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
structure SU = SetUtilFn (StringBinarySet)
structure MU = MapUtilFn (Gctx.Map)
open SMT2Printer
open SMTSolver

infixr 0 $
infix 0 !!

exception Error of string
                     
structure UnderscoredCollectMod = CollectModFn (structure Expr = UnderscoredExpr
                                     val on_var = collect_mod_long_id
                                     val on_mod_id = collect_mod_mod_id
                                    )
                                    
fun process_prog show_result filename gctx prog =
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
            fun on_constr (name, (_, tbinds)) =
              let
                val (_, core) = unfold_binds tbinds
              in
                (name, TC.get_constr_inames core)
              end
            val cctx = map on_constr cctx
          in
            (sctx_names sctx, names kctx, cctx, names tctx)
          end
      (* typechecking signature to name-resolving signature *)      
      fun TCsgntr2NRsgntr (sg : TC.sgntr) : NR.sgntr =
          case sg of
              Sig ctx => NR.Sig $ TCctx2NRctx ctx
            | FunctorBind ((name, arg), body) => NR.FunctorBind ((name, TCctx2NRctx arg), TCctx2NRctx body)
      (* typechecking global context to name-resolving global context *)      
      fun TCgctx2NRgctx gctx = Gctx.map TCsgntr2NRsgntr gctx
      (* trim [gctx] to retain only those that are relevant in typechecking [prog] *)
      fun trim_gctx prog gctx =
        let
          open SU.Set
          open SU
          open List
          fun trans_closure graph nodes =
            let
              fun loop (working, done) =
                case pop working of
                    NONE => done
                  | SOME (node, working) =>
                    if member node done then
                      loop (working, done)
                    else
                      let
                        val outs = default empty $ Gctx.find (graph, node)
                        val working = union (working, outs)
                        val done = add (done, node)
                      in
                        loop (working, done)
                      end
              val nodes = loop (nodes, empty)
            in
              nodes
            end
              
          val ms = dedup $ UnderscoredCollectMod.collect_mod_prog prog
          val ms = to_list $ trans_closure (get_dependency_graph gctx) $ to_set ms
          (* val () = println $ "before restrict: " ^ str_int (Gctx.length gctx) *)
          val gctx = MU.restrict ms gctx
          (* val () = println $ "after restrict: " ^ str_int (Gctx.length gctx) *)
        in
          gctx
        end
      val old_gctx = gctx
      (* val prog = [bind] *)
      val (prog, _, _) = resolve_prog (TCgctx2NRgctx gctx) prog
      val result as ((_, gctxd, (* gctx *)_), (vcs, admits)) = typecheck_prog (trim_gctx prog gctx) prog
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
      fun smt_solver use_batch vcs =
          if length vcs = 0 then
            (* vcs *)
            map (fn vc => (vc, NONE)) vcs
          else
            let
              val () = println "-------------------------------------------"
              val () = println "Applying SMT solver ..."
              val unsats = map (fn vc => (vc, NONE)) vcs
              val unsats =
                  if use_batch then
                    List.mapPartial id $ SMTSolver.smt_solver filename true (SOME Z3) $ map fst unsats
                  else unsats
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
      val vcs = map Normalize.normalize_vc vcs
      val vcs = concatMap VC.simp_vc_vcs vcs
      val vcs = map fst $ smt_solver false(*true*) vcs
      val vcs = bigO_solver vcs
      val vcs = map Normalize.normalize_vc vcs
      val vcs = concatMap VC.simp_vc_vcs vcs
      val vcs = smt_solver true vcs
      val vcs = map (mapFst Normalize.normalize_vc) vcs
      val vcs = map (mapFst VC.simp_vc) vcs
      (* val vcs = BigOSolver.infer_numbers vcs *)
      val () = if null vcs then
                 if show_result then println $ sprintf "Typechecking $ succeeded.\n" [filename] else ()
               else
                 raise Error $ (* str_error "Error" filename dummy *) join_lines $ [sprintf "Typecheck Error: $ Unproved obligations:" [str_int $ length vcs], ""] @ (
                 (* concatMap (fn vc => str_vc true filename vc @ [""]) $ map fst vcs *)
                 concatMap (print_unsat true filename) vcs
               )
      val gctxd = normalize_sgntr_list old_gctx gctxd
      val gctxd = update_sgntr_list gctxd
      (* val gctxd = SimpCtx.simp_sgntr_list gctxd *)
      val () = if show_result then
                 app println $ print_result false filename (gctx_names old_gctx) gctxd
               else ()
      val admits = map (attach_fst filename) admits
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
      (* fun iter (bind, (prog, gctx, admits_acc)) = *)
      (*     let *)
      (*       (* val mod_names = mod_names_top_bind bind *) *)
      (*       (* val (gctx', mapping) = select_modules gctx mod_names *) *)
      (*       val gctx' = gctx *)
      (*       val (progd, gctxd, admits) = process_prog show_result filename gctx' [bind] *)
      (*       (* val gctxd = remap_modules gctxd mapping *) *)
      (*       val gctx = addList (gctx, gctxd) *)
      (*     in *)
      (*       (progd @ prog, gctx, admits_acc @ admits) *)
      (*     end *)
      (* val (prog, gctx, admits) = foldl iter ([], gctx, []) prog *)
      val (prog, gctxd, admits) = process_prog show_result filename gctx prog
      val gctx = addList (gctx, gctxd)
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
    | Gctx.KeyAlreadyExists (name, gctx) => raise Error $ sprintf "module name '$' already exists in module context $" [name, str_ls id gctx]

fun process_file is_library filename gctx =
    let
      val (dir, base, ext) = split_dir_file_ext filename
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
              val filenames = map (curry join_dir_file dir) filenames
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
      val (_, gctx, _) = process_files true empty libraries
      val (prog, gctx, admits) = process_files false gctx filenames
      fun str_admit show_region (filename, p) =
          let
            open Expr
            fun prop2vc p =
              let
              in
                case p of
                    Quan (Forall, bs, Bind ((name, r), p), r_all) =>
                    let
                      val vc = prop2vc p
                      val vc = add_hyp_vc (VarH (name, (bs, r_all))) vc
                    in
                      vc
                    end
                  | BinConn (Imply, p1, p) =>
                    let
                      val vc = prop2vc p
                      val vc = add_hyp_vc (PropH p1) vc
                    in
                      vc
                    end
                  | _ => ([], p)
              end
            val vc = prop2vc p
            (* val r = get_region_p p *)
            val r = get_region_p $ snd vc
            val region_lines = if show_region then
                                 [str_region "" filename r]
                               else []
          in
            region_lines @ 
            [str_p empty [] p] @ [""]
          end
      val () =
          if null admits then
            ()
          else
            (* app println $ "Admitted axioms: \n" :: concatMap (str_admit true) admits *)
            app println $ "Admitted axioms: \n" :: (concatMap (str_admit false) $ dedup (fn ((_, p), (_, p')) => Equal.eq_p p p') admits)
    in
      (prog, gctx, admits)
    end
      
end

structure Main = struct
open Util
open OS.Process
open List

infixr 0 $
infix 0 !!
        
exception ParseArgsError of string
            
fun usage () =
    let
      val () = println "Usage: THIS [--help] [-l <library1:library2:...>] [--annoless] <filename1> <filename2> ..."
      val () = println "  --help: print this message"
      val () = println "  -l <library1:library2:...>: paths to libraries, separated by ':'"
      val () = println "  --annoless: less annotations on case-of"
      val () = println "  --repeat n: repeat the whole thing for [n] times (for profiling purpose)"
      val () = println "  --unit-test <dir-name>: do unit test under directory dir-name"
    in
      ()
    end

type options =
     {
       AnnoLess : bool ref,
       Repeat : int ref,
       Libraries : string list ref,
       UnitTest : string option ref
     }

fun create_default_options () : options =
  {
    AnnoLess = ref false,
    Repeat = ref 1,
    Libraries = ref [],
    UnitTest = ref NONE
  }
    
fun parse_arguments (opts : options, args) =
    let
      val positionals = ref []
      fun parse_libraries arg =
        String.tokens (curry op= #":") arg
      (* fun do_A arg = print ("Argument of -A is " ^ arg ^ "\n") *)
      (* fun do_B ()  = if !switch then print "switch is on\n" else print "switch is off\n" *)
      fun parse_repeat s =
        let
          val n = Int.fromString s !! (fn () => raise ParseArgsError $ sprintf "$ is not a number" [s])
          val () = if n < 0 then raise ParseArgsError $ sprintf "$ is negative" [str_int n]
                   else ()
        in
          n
        end
      fun parseArgs args =
          case args of
              [] => ()
	    | "--help" :: ts => (usage (); parseArgs ts)
	    | "--annoless" :: ts => (#AnnoLess opts := true; parseArgs ts)
	    | "--repeat" :: arg :: ts => (#Repeat opts := parse_repeat arg; parseArgs ts)
	    | "-l" :: arg :: ts => (app (push_ref (#Libraries opts)) $ parse_libraries arg; parseArgs ts)
	    | "--unit-test" :: arg :: ts => (#UnitTest opts := SOME arg; parseArgs ts)
	    (* | parseArgs ("-A" :: arg :: ts) = (do_A arg;       parseArgs ts) *)
	    (* | parseArgs ("-B"        :: ts) = (do_B();         parseArgs ts) *)
	    | s :: ts =>
              if String.isPrefix "-" s then
	        raise ParseArgsError ("Unrecognized option: " ^ s)
              else
                (push_ref positionals s; parseArgs ts)
      val () = parseArgs args
    in
      (rev (!positionals))
    end

val success = OS.Process.success
val failure = OS.Process.failure

fun usage_and_fail () = (usage (); exit failure)
                          
fun main (prog_name, args : string list) = 
    let
      val opts = create_default_options ()
      val filenames = rev $ parse_arguments (opts, args)
      val () = case !(#UnitTest opts) of
                   NONE => ()
                 | SOME dirname => (UnitTest.test_suites dirname; exit success)
      val libraries = rev $ !(#Libraries opts)
      val () = if null filenames then
                 usage_and_fail ()
               else ()
      val () = TypeCheck.anno_less := !(#AnnoLess opts)
      val _ = repeat_app (fn () => TiML.main libraries filenames) (!(#Repeat opts))
    in	
      success
    end
    handle
    TiML.Error msg => (println msg; failure)
    | IO.Io e => (println (sprintf "IO Error doing $ on $" [#function e, #name e]); failure)
    | Impossible msg => (println ("Impossible: " ^ msg); failure)
    | Unimpl msg => (println ("Unimpl: " ^ msg); failure)
    | ParseArgsError msg => (println msg; usage_and_fail ())
                               (* | _ => (println ("Internal error"); failure) *)

end
