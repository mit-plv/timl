structure TiML = struct
structure E = NamefulExpr
open Expr
open Util
open Parser
open Elaborate
structure NR = NameResolve
open NR
structure TC = TypeCheck
open TC

infixr 0 $

exception Error of string
                     
open SMT2Printer
open SMTSolver

fun process_top_bind show_result filename gctx bind =
    let
      fun print_result show_region filename old_gctxn gctx =
          let 
            val header =
                (* sprintf "Typechecked $" [filename] :: *)
                sprintf "Typechecking results (as module signatures) for $:" [filename] ::
                [""]
            val typing_lines = str_gctx old_gctxn gctx
            val lines = 
                header @
                (* ["Types: ", ""] @ *)
                typing_lines @
                [""]
          in
            lines
          end
      (* typechecking context to name-resolving context *)      
      fun TCctx2NRctx (ctx : TC.context) : NR.context =
          let
            val (sctx, kctx, cctx, tctx) = ctx
            val cctx = map (fn (name, (_, _, core)) => (name, get_constr_inames core)) cctx
          in
            (sctx_names sctx, names kctx, cctx, names tctx)
          end
      (* typechecking signature to name-resolving signature *)      
      fun TCsgntr2NRsgntr (sg : TC.sgntr) : NR.sgntr =
          case sg of
              Sig ctx => NR.Sig $ TCctx2NRctx ctx
            | FunctorBind ((name, arg), body) => NR.FunctorBind ((name, TCctx2NRctx arg), TCctx2NRctx body)
      (* typechecking global context to name-resolving global context *)      
      fun TCgctx2NRgctx gctx = map (mapSnd TCsgntr2NRsgntr) gctx
      val old_gctx = gctx
      val prog = [bind]
      val (prog, _, _) = resolve_prog (TCgctx2NRgctx gctx) prog
      val result as ((gctxd, (* gctx *)_), (vcs, admits)) = typecheck_prog gctx prog
      (* val () = write_file (filename ^ ".smt2", to_smt2 vcs) *)
      (* val () = app println $ print_result false filename (gctx_names old_gctx) gctxd *)
      val () = println $ sprintf "Typechecker generated $ proof obligations." [str_int $ length vcs]
      (* val () = app println $ concatMap (fn vc => VC.str_vc false filename vc @ [""]) vcs *)
      fun print_unsat show_region filename (vc, counter) =
          VC.str_vc show_region filename vc @
          (* [""] @ *)
          (case counter of
               SOME assigns =>
               if length assigns > 0 then
                 indent ["Counter-example:"] @
                 (self_compose 2 indent) (map (fn (name, value) => sprintf "$ = $" [name, value]) assigns) @
                 []        
               else []
             (* | NONE => ["SMT solver reported 'unknown': can't prove and can't find counter example\n"] *)
             | NONE => []
          ) @
          [""]
      fun print_unsats show_region filename unsats =
          if length unsats > 0 then
            app println $ concatMap (print_unsat show_region filename) unsats
          else
            println "All conditions proved."
      fun bigO_solver vcs =
          if length vcs = 0 then vcs
          else
            let
              val () = println "-------------------------------------------"
              val () = println "Applying BigO solver ..."
              val vcs = BigOSolver.solve_vcs vcs
              val () = println (sprintf "BigO solver generated or left $ proof obligations unproved." [str_int $ length vcs])
              val () = println ""
              (* val () = print_unsats false filename $ map (fn vc => (vc, SOME [])) vcs *)
            in
              vcs
            end
      fun smt_solver vcs =
          if length vcs = 0 then
            (* vcs *)
            map (fn vc => (vc, NONE)) vcs
          else
            let
              val () = println "-------------------------------------------"
              val () = println "Applying SMT solver ..."
              val unsats = List.mapPartial id $ SMTSolver.smt_solver filename true (SOME Z3) vcs
              (* re-check individually to get counter-example *)
              (* ToDo: don't need this when SMT batch response parser is made smarter *)
              val unsats = List.mapPartial id $ map (SMTSolver.smt_solver_single filename true (SOME Z3)) $ map fst $ unsats
                                           
              (* val unsats = List.mapPartial id $ SMTSolver.smt_solver filename false (SOME CVC4) vcs *)
              (* re-check individually to get counter-example *)
              (* val unsats = List.mapPartial id $ map (SMTSolver.smt_solver_single filename true (SOME CVC4)) $ map fst $ unsats *)
              (* val unsats = List.mapPartial id $ map (SMTSolver.smt_solver_single filename true (SOME Z3)) $ map fst $ unsats *)
                                           
              val () = println (sprintf "SMT solver generated or left $ proof obligations unproved." [str_int $ length unsats])
              val () = println ""
                               (* val () = print_unsats false filename unsats *)
            in
              (* map fst unsats *)
              unsats
            end
      val vcs = bigO_solver vcs
      val vcs = concatMap VC.simp_vc_vcs vcs
      val vcs = smt_solver vcs
      (* val vcs = map (mapFst VC.simp_vc) vcs *)
      val () = if null vcs then
                 if show_result then println $ "Typechecking succeeded.\n" else ()
               else
                 raise Error $ (* str_error "Error" filename dummy *) join_lines $ [sprintf "Typecheck Error: $ Unproved obligations:" [str_int $ length vcs], ""] @ (
                 (* concatMap (fn vc => str_vc true filename vc @ [""]) $ map fst vcs *)
                 concatMap (print_unsat true filename) vcs
               )
      val () = if show_result then
                 app println $ print_result false filename (gctx_names old_gctx) gctxd
               else ()
      val admits = map (fn admit => (filename, admit)) admits
      val gctxd = update_gctx gctxd
                              (* val gctx = gctxd @ old_gctx *)
    in
      (prog, gctxd, (* gctx,  *)admits)
    end

fun typecheck_file show_result gctx filename =
    let
      val () = if show_result then println $ sprintf "Typechecking file $ ..." [filename] else ()
      val prog = parse_file filename
      val prog = elaborate_prog prog
      (* val () = (app println o map (suffix "\n") o fst o E.str_decls ctxn) decls *)
      (* val () = (app println o map (suffix "\n") o fst o UnderscoredExpr.str_decls ctxn) decls *)
      (* apply solvers after each top bind *)
      fun iter (bind, (prog, gctx, acc)) =
          let
            (* val mod_names = mod_names_top_bind bind *)
            (* val (gctx', mapping) = select_modules gctx mod_names *)
            val gctx' = gctx
            val (progd, gctxd, admits) = process_top_bind show_result filename gctx' bind
            (* val gctxd = remap_modules gctxd mapping *)
            val gctx = gctxd @ gctx
          in
            (progd @ prog, gctx, acc @ admits)
          end
      val (prog, gctx, admits) = foldl iter ([], gctx, []) prog
    in
      (prog, gctx, admits)
    end
    handle
    Elaborate.Error (r, msg) => raise Error $ str_error "Error" filename r ["Elaborate error: " ^ msg]
    | NameResolve.Error (r, msg) => raise Error $ str_error "Error" filename r ["Resolve error: " ^ msg]
    | TypeCheck.Error (r, msg) => raise Error $ str_error "Error" filename r ((* "Type error: " :: *) msg)
    | BigOSolver.MasterTheoremCheckFail (r, msg) => raise Error $ str_error "Error" filename r ((* "Type error: " :: *) msg)
    | Parser.Error => raise Error "Unknown parse error"
    | SMTError msg => raise Error $ "SMT error: " ^ msg
    | IO.Io e => raise Error $ sprintf "IO error in function $ on file $" [#function e, #name e]
    | OS.SysErr (msg, err) => raise Error $ sprintf "System error$: $" [(default "" o Option.map (prefix " " o OS.errorName)) err, msg]
                                    
fun process_file is_library filename gctx =
    let
      open OS.Path
      fun splitDirFileExt filename =
          let
            val dir_file = splitDirFile filename
            val base_ext = splitBaseExt (#file dir_file)
          in
            (#dir dir_file, #base base_ext, #ext base_ext)
          end
      fun joinDirFileCurried dir file = joinDirFile {dir = dir, file = file}
      val (dir, base, ext) = splitDirFileExt filename
      val gctx =
          if ext = SOME "pkg" then
            let
              val () = if is_library then
                         TypeCheck.turn_on_builtin ()
                       else ()
              (* val split_lines = String.tokens (fn c => c = #"\n") *)
              (* val read_lines = split_lines o read_file *)
              val filenames = read_lines filename
              val filenames = map trim filenames
              (* val () = app println filenames *)
              val filenames = List.filter (fn s => not (String.isPrefix "(*" s andalso String.isSuffix "*)" s)) filenames
              (* val () = app println filenames *)
              val filenames = List.filter (fn s => s <> "") filenames
              val filenames = map (joinDirFileCurried dir) filenames
              val gctx = process_files is_library gctx filenames
              val () = TypeCheck.turn_off_builtin ()
            in
              gctx
            end
          else if ext = SOME "timl" then
            typecheck_file (not is_library) gctx filename
          else raise Error $ sprintf "Unknown filename extension $ of $" [default "<EMPTY>" ext, filename]
    in
      gctx
    end
      
and process_files is_library gctx filenames =
    let
      fun iter (filename, (prog, gctx, acc)) =
          let
            val (progd, gctx, admits) = process_file is_library filename gctx
          in
            (progd @ prog, gctx, acc @ admits)
          end
    in
      foldl iter ([], gctx, []) filenames
    end
      
fun main libraries filenames =
    let
      (* val () = app println $ ["Input file(s):"] @ indent filenames *)
      val (_, gctx, _) = process_files true [] libraries
      val (prog, gctx, admits) = process_files false gctx filenames
      fun str_admit show_region (filename, p) =
          let
            open Expr
            val vc = prop2vc p
            (* val r = get_region_p p *)
            val r = get_region_p $ snd vc
            val region_lines = if show_region then
                                 [str_region "" filename r]
                               else []
          in
            region_lines @ 
            [str_p [] [] p] @ [""]
          end
      val () =
          if null admits then
            ()
          else
            (* app println $ "Admitted axioms: \n" :: concatMap (str_admit true) admits *)
            app println $ "Admitted axioms: \n" :: (concatMap (str_admit false) $ dedup (fn ((_, p), (_, p')) => Expr.eq_p p p') admits)
    in
      (prog, gctx, admits)
    end
      
end

structure Main = struct
open Util
open OS.Process
open String
open List

exception ParseArgsError of string
            
fun usage () =
    let
      val () = println "Usage: THIS [--help] [-l <library1:library2:...>] [--annoless] <filename1> <filename2> ..."
      val () = println "  --help: print this message"
      val () = println "  -l <library1:library2:...>: paths to libraries, separated by ':'"
      val () = println "  --annoless: less annotations on case-of"
    in
      ()
    end
            
fun parse_arguments args =
    let
      val annoless = ref false
      val positionals = ref []
      val libraries = ref []
      fun parse_libraries arg = libraries := tokens (curry op= #":") arg
      (* fun do_A arg = print ("Argument of -A is " ^ arg ^ "\n") *)
      (* fun do_B ()  = if !switch then print "switch is on\n" else print "switch is off\n" *)
      fun parseArgs args =
          case args of
              [] => ()
	    | "--help" :: ts => (usage (); parseArgs ts)
	    | "--annoless" :: ts => (annoless := true; parseArgs ts)
	    | "-l" :: arg :: ts => (parse_libraries arg; parseArgs ts)
	    (* | parseArgs ("-A" :: arg :: ts) = (do_A arg;       parseArgs ts) *)
	    (* | parseArgs ("-B"        :: ts) = (do_B();         parseArgs ts) *)
	    | s :: ts =>
              if isPrefix "-" s then
	        raise ParseArgsError ("Unrecognized option: " ^ s)
              else
                (push_ref positionals s; parseArgs ts)
      val () = parseArgs args
    in
      (!annoless, !libraries, rev (!positionals))
    end
                   
fun main (prog_name, args : string list) : int = 
    let
      val (opt, libraries, filenames) = parse_arguments args
      val () = if null filenames then
                 (usage ();
                  exit failure)
               else ()
      val () = PreTypeCheck.anno_less := opt
      val _ = TiML.main libraries filenames
    in	
      0
    end
    handle
    TiML.Error msg => (println msg; 1)
    | IO.Io e => (println (sprintf "IO Error doing $ on $" [#function e, #name e]); 1)
    | Impossible msg => (println ("Impossible: " ^ msg); 1)
    | Expr.ModuleUVar msg => (println ("ModuleUVar: " ^ msg); 1)
    | ParseArgsError msg => (println msg; usage (); 1)
                               (* | _ => (println ("Internal error"); 1) *)

end

