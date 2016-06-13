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

fun print_result show_region filename old_gctxn gctx =
    let 
      val header =
          (* sprintf "Typechecked $" [filename] :: *)
          sprintf "Typechecking results for $:" [filename] ::
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
      
fun TCctx2NRctx (ctx : TC.context) : NR.context =
    let
      val (sctx, kctx, cctx, tctx) = ctx
      val cctx = map (fn (name, (_, _, core)) => (name, get_constr_inames core)) cctx
    in
      (sctx_names sctx, names kctx, cctx, names tctx)
    end
fun TCsgntr2NRsgntr (sg : TC.sgntr) : NR.sgntr =
    case sg of
        Sig ctx => NR.Sig $ TCctx2NRctx ctx
      | FunctorBind ((name, arg), body) => NR.FunctorBind ((name, TCctx2NRctx arg), TCctx2NRctx body)
fun TCgctx2NRgctx gctx = map (mapSnd TCsgntr2NRsgntr) gctx
                             
fun process_top_bind filename gctx bind =
    let
      val old_gctx = gctx
      val prog = [bind]
      val (prog, _, _) = resolve_prog (TCgctx2NRgctx gctx) prog
      val result as ((gctxd, (* gctx *)_), (vcs, admits)) = typecheck_prog gctx prog
      (* val () = write_file (filename ^ ".smt2", to_smt2 vcs) *)
      (* val () = app println $ print_result false filename (gctx_names old_gctx) gctxd *)
      val () = println $ sprintf "Type checker generated $ proof obligations." [str_int $ length vcs]
      (* val () = app println $ concatMap (fn vc => VC.str_vc false filename vc @ [""]) vcs *)
      fun print_unsat show_region filename (vc, counter) =
          VC.str_vc show_region filename vc @
          [""] @
          (case counter of
               SOME assigns =>
               if length assigns > 0 then
                 ["Counter-example:"] @
                 map (fn (name, value) => sprintf "$ = $" [name, value]) assigns @
                 [""]        
               else []
             (* | NONE => ["SMT solver reported 'unknown': can't prove and can't find counter example\n"] *)
             | NONE => []
          ) 
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
                               (* val () = println "" *)
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
      val () = app println $ print_result false filename (gctx_names old_gctx) gctxd
      val () = if null vcs then
                 println $ "Typechecked.\n"
               else
                 raise Error $ (* str_error "Error" filename dummy *) join_lines $ [sprintf "Typecheck Error: $ Unproved obligations:" [str_int $ length vcs], ""] @ (
                 (* concatMap (fn vc => str_vc true filename vc @ [""]) $ map fst vcs *)
                 concatMap (print_unsat true filename) vcs
               )
      val admits = map (fn admit => (filename, admit)) admits
      val gctxd = update_gctx gctxd
                              (* val gctx = gctxd @ old_gctx *)
    in
      (gctxd, (* gctx,  *)admits)
    end

  (*
local
  open E
  fun mod_names_i x n b = on_m_i mod_names_v x n b
  fun mod_names_p x n b = on_m_p mod_names_i x n b
  fun mod_names_s x n b = on_m_s mod_names_p x n b
  fun mod_names_mt x n b = on_m_mt mod_names_v mod_names_i mod_names_s x n b
  fun mod_names_t x n b = on_m_t mod_names_mt x n b
                                 
  fun on_e_e on_v =
      let
        fun f b =
	    case b of
	        Var (y, b) => Var (on_m_long_id on_v y, b)
	      | Abs (pn, e) =>
                Abs (on_pn pn, f e)
	      | App (e1, e2) => App (f e1, f e2)
	      | TT r => TT r
	      | Pair (e1, e2) => Pair (f e1, f e2)
	      | Fst e => Fst (f e)
	      | Snd e => Snd (f e)
	      | AbsI (s, name, e, r) => AbsI (on_s f x s, name, f e, r)
	      | AppI (e, i) => AppI (f e, on_i f x i)
	      | Let (return, decs, e, r) =>
	        let
                  val return = on_return return
		  val decs = map on_decl decs
                  val e = f e
	        in
		  Let (return, decs, e, r)
	        end
	      | Ascription (e, t) => Ascription (f e, t)
	      | AscriptionTime (e, d) => AscriptionTime (f e, d)
	      | ConstInt n => ConstInt n
	      | BinOp (opr, e1, e2) => BinOp (opr, f e1, f e2)
	      | AppConstr (cx, is, e) => AppConstr (cx, is, f e)
	      | Case (e, return, rules, r) => Case (f e, return, map (f_rule) rules, r)
	      | Never t => Never t

        and f_dec dec =
	    case dec of
	        Val (tnames, pn, e, r) => 
	        let 
                  val (_, enames) = ptrn_names pn 
	        in
                  (Val (tnames, pn, f e, r), length enames)
                end
              | Rec (tnames, name, (binds, ((t, d), e)), r) => 
                let
                  fun g (bind, m) =
                      case bind of
                          SortingST _ => m
                        | TypingST pn =>
	                  let 
                            val (_, enames) = ptrn_names pn 
	                  in
                            m + length enames
                          end
                  val m = foldl g 0 binds
                  val e = f (x + 1 + m) n e
                in
                  (Rec (tnames, name, (binds, ((t, d), e)), r), 1)
                end
              | Datatype a => (Datatype a, 0)
              | IdxDef a => (IdxDef a, 0)
              | AbsIdx2 a => (AbsIdx2 a, 0)
              | AbsIdx (a, decls, r) => 
                let
                  val (decls, m) = f_decls decls
                in
                  (AbsIdx (a, decls, r), m)
                end
              | TypeDef (name, t) => (TypeDef (name, t), 0)
              | Open m => (Open m, 0)

        and f_rule (pn, e) =
	    let 
              val (_, enames) = ptrn_names pn 
	    in
	      (pn, f (x + length enames) n e)
	    end
      in
        f
      end
in
fun mod_names_top_bind bind = []
fun select_modules gctx mod_names = (gctx, ())
fun remap_modules gctx mapping = gctx
end
*)

fun typecheck_file gctx filename =
    let
      val () = println $ sprintf "Typechecking file $ ..." [filename]
      val prog = parse_file filename
      val prog = elaborate_prog prog
      (* val () = (app println o map (suffix "\n") o fst o E.str_decls ctxn) decls *)
      (* val () = (app println o map (suffix "\n") o fst o UnderscoredExpr.str_decls ctxn) decls *)
      (* apply solvers after each top bind *)
      fun iter (bind, (gctx, acc)) =
          let
            (* val mod_names = mod_names_top_bind bind *)
            (* val (gctx', mapping) = select_modules gctx mod_names *)
            val gctx' = gctx
            val (gctxd, admits) = process_top_bind filename gctx' bind
            (* val gctxd = remap_modules gctxd mapping *)
            val gctx = gctxd @ gctx
          in
            (gctx, acc @ admits)
          end
      val (gctx, admits) = foldl iter (gctx, []) prog
    in
      (gctx, admits)
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
                                    
fun process_file (filename, gctx) =
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
      val (dir, _, ext) = splitDirFileExt filename
      val gctx =
          if ext = SOME "pkg" then
            let
              val split_lines = String.tokens (fn c => c = #"\n")
              val read_lines = split_lines o read_file
              val filenames = read_lines filename
              val filenames = map trim filenames
              (* val () = app println filenames *)
              val filenames = List.filter (fn s => not (String.isPrefix "(*" s andalso String.isSuffix "*)" s)) filenames
              (* val () = app println filenames *)
              val filenames = List.filter (fn s => s <> "") filenames
              val filenames = map (joinDirFileCurried dir) filenames
              val gctx = process_files gctx filenames
            in
              gctx
            end
          else if ext = SOME "timl" then
            typecheck_file gctx filename
          else raise Error $ sprintf "Unknown filename extension $ of $" [default "<EMPTY>" ext, filename]
    in
      gctx
    end
      
and process_files gctx filenames =
    let
      fun iter (filename, (gctx, acc)) =
          let
            val (gctx, admits) = process_file (filename, gctx)
          in
            (gctx, acc @ admits)
          end
    in
      foldl iter (gctx, []) filenames
    end
      
fun main filenames =
    let
      val () = app println $ ["Input file(s):"] @ indent filenames
      val (gctx, admits) = process_files [] filenames
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
      gctx
    end
      
end

structure Main = struct
open Util
open OS.Process
       
fun main (prog_name, args : string list) : int = 
    let
      val _ =
	  case args of
	      [] => (println "Usage: THIS filename1 filename2 ..."; exit(failure))
	    | filenames =>
              TiML.main filenames
    in	
      0
    end
    handle
    TiML.Error msg => (println msg; 1)
    | IO.Io e => (println (sprintf "IO Error doing $ on $" [#function e, #name e]); 1)
    | Impossible msg => (println ("Impossible: " ^ msg); 1)
    | Expr.ModuleUVar msg => (println ("ModuleUVar: " ^ msg); 1)
                               (* | _ => (println ("Internal error"); 1) *)

end

