structure TiML = struct
structure E = NamefulExpr
open Expr
open Util
open Parser
open Elaborate
open NameResolve
open TypeCheck

infixr 0 $

fun print_result show_region filename old_ctx decls ((typing, vcs) : tc_result) =
    let 
      val header =
          (* sprintf "Typechecked $" [filename] :: *)
          sprintf "Typechecking results for $:" [filename] ::
          [""]
      open Expr
        fun str_decls (ctx as (sctx, kctx, cctx, tctx)) decls =
            let fun f (decl, (acc, ctx)) =
                    let val (s, ctx) = str_decl ctx decl
                    in
                        (s :: acc, ctx)
                    end
                val (decls, ctx) = foldl f ([], ctx) decls
                val decls = rev decls
            in
                (decls, ctx)
            end
                
        and str_decl (ctx as (sctx, kctx, cctx, tctx)) decl =
            case decl of
                Val (tnames, pn, e, _) =>
                let 
                    val ctx' as (sctx', kctx', cctx', _) = (sctx, (rev o map fst) tnames @ kctx, cctx, tctx)
                    val tnames = (join "" o map (fn nm => sprintf " [$]" [nm]) o map fst) tnames
                    val (inames, enames) = ptrn_names pn
                    val pn = str_pn (sctx', kctx', cctx') pn
                    val e = str_e ctx' e
	            val ctx = (inames @ sctx, kctx, cctx, enames @ tctx)
                in
                    ("", ctx)
                end
              | Rec (tnames, (name, _), (binds, ((t, d), e)), _) =>
                let 
	            val ctx as (sctx, kctx, cctx, tctx) = (sctx, kctx, cctx, name :: tctx)
                    val ctx_ret = ctx
                    val ctx as (sctx, kctx, cctx, tctx) = (sctx, (rev o map fst) tnames @ kctx, cctx, tctx)
                    val tnames = (join "" o map (fn nm => sprintf " [$]" [nm]) o map fst) tnames
                    fun f (bind, (binds, ctx as (sctx, kctx, cctx, tctx))) =
                        case bind of
                            SortingST ((name, _), s) => 
                            (sprintf "{$ : $}" [name, str_s sctx s] :: binds, (name :: sctx, kctx, cctx, tctx))
                          | TypingST pn =>
                            let
                                val (inames, enames) = ptrn_names pn
                            in
                                (str_pn (sctx, kctx, cctx) pn :: binds, (inames @ sctx, kctx, cctx, enames @ tctx))
                            end
                    val (binds, ctx as (sctx, kctx, cctx, tctx)) = foldl f ([], ctx) binds
                    val binds = rev binds
                    val binds = (join "" o map (prefix " ")) binds
                    val t = str_mt (sctx, kctx) t
                    val d = str_i sctx d
                    val e = str_e ctx e
                in
                    ("", ctx_ret)
                end
              | Datatype (name, tnames, sorts, constrs, _) =>
                let val str_tnames = (join_prefix " " o rev) tnames
                    fun str_constr_decl (cname, ibinds, _) =
                        let 
                            val (name_sorts, (t, idxs)) = unfold_ibinds ibinds
                            val (name_sorts, sctx') = str_sortings sctx name_sorts
                            val name_sorts = map (fn (nm, s) => sprintf "$ : $" [nm, s]) name_sorts
                        in
                            sprintf "$ of$ $ ->$$ $" [cname, (join_prefix " " o map (surround "{" "}")) name_sorts, str_mt (sctx', rev tnames @ name :: kctx) t, (join_prefix " " o map (surround "{" "}" o str_i sctx') o rev) idxs, str_tnames, name]
                        end
                    val s = sprintf "datatype$$ $ = $" [(join_prefix " " o map (surround "{" "}" o str_s sctx) o rev) sorts, str_tnames, name, join " | " (map str_constr_decl constrs)]
                    val cnames = map #1 constrs
                    val ctx = (sctx, name :: kctx, rev cnames @ cctx, tctx)
                in
                    (* (s, ctx) *)
                    ("", ctx)
                end
              | IdxDef ((name, r), s, i) =>
                (sprintf "$ : $ = $" [name, str_s sctx s, str_i sctx i], (name :: sctx, kctx, cctx, tctx))
              | AbsIdx (((name, r1), s, i), decls, _) =>
                let
                    val ctx' = (name :: sctx, kctx, cctx, tctx)
                    val (decls, ctx') = str_decls ctx' decls
                in
                    ("", ctx')
                end
      val decl_lines = map (suffix "\n") $ List.filter (fn s => s <> "") $ fst $ str_decls (ctx_names old_ctx) decls
      val typing_lines = [str_typing_info old_ctx typing]
      (* val vc_lines = *)
      (*     sprintf "Verification Conditions: [count=$]" [str_int (length vcs)] :: *)
      (*     "" :: *)
      (*     concatMap (fn vc => VC.str_vc show_region filename vc @ [""]) vcs *)
      val s = join_lines 
                (
                  header
                  @ ["Definitions: ", ""]
                  @ decl_lines
                  @ ["Types: ", ""]
                  @ typing_lines 
                (* @ vc_lines *)
                )
    in
      s
    end

exception Error of string
                     
open SMT2Printer
open SMTSolver

fun typecheck_file (filename, ctx) =
    let
      val ctxn =
          let
            val (sctx, kctx, cctx, tctx) = ctx
            val cctx = map (fn (name, (_, _, core)) => (name, get_constr_inames core)) cctx
          in
            (sctx_names sctx, names kctx, cctx, names tctx)
          end
      val () = println $ sprintf "Typechecking file $ ..." [filename]
      val decls = parse_file filename
      val decls = map elaborate_decl decls
      (* val () = (app println o map (suffix "\n") o fst o E.str_decls ctxn) decls *)
      val decls = resolve_decls ctxn decls
      (* val () = (app println o map (suffix "\n") o fst o UnderscoredExpr.str_decls ctxn) decls *)
      val old_ctx = ctx
      val result as ((decls, ctxd, ds, ctx), (vcs, admits)) = typecheck_decls ctx decls
      (* val () = write_file (filename ^ ".smt2", to_smt2 vcs) *)
      (* val () = println $ print_result false filename result *)
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
      val () = print $ print_result false filename old_ctx decls result
      fun str_admit show_region p =
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
            [str_p (#1 ctxn) p] @ [""]
          end
      val () =
          if null admits then
            ()
          else
            app println $ "Admitted axioms: \n" :: concatMap (str_admit (* true *)false) admits
      val () = if null vcs then
                 println $ "Typechecked.\n"
               else
                 raise Error $ (* str_error "Error" filename dummy *) join_lines $ [sprintf "Typecheck Error: $ Unproved obligations:" [str_int $ length vcs], ""] @ (
                 (* concatMap (fn vc => str_vc true filename vc @ [""]) $ map fst vcs *)
                 concatMap (print_unsat true filename) vcs
               )
    in
      ctx
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
                                    
fun process_file (filename, ctx) =
    let
      open OS.Path
      val typecheck_files = foldl typecheck_file
      fun splitDirFileExt filename =
          let
            val dir_file = splitDirFile filename
            val base_ext = splitBaseExt (#file dir_file)
          in
            (#dir dir_file, #base base_ext, #ext base_ext)
          end
      fun joinDirFileCurried dir file = joinDirFile {dir = dir, file = file}
      val (dir, _, ext) = splitDirFileExt filename
      val ctx =
          if ext = SOME "pkg" then
            let
              val split_lines = String.tokens (fn c => c = #"\n")
              val read_lines = split_lines o read_file
              fun read_lines filename =
                  let
                    open TextIO
                    val ins = openIn filename
                    fun loop lines =
                        case inputLine ins of
                            SOME ln => loop (String.substring (ln, 0, String.size ln - 1) :: lines)
                          | NONE => lines
                    val lines = rev $ loop []
                    val () = closeIn ins
                  in
                    lines
                  end
              fun trim s =
                  let
                    fun first_non_space s =
                        let
                          val len = String.size s
                          fun loop n =
                              if n >= len then
                                NONE
                              else
                                if Char.isSpace $ String.sub (s, n)  then
                                  loop (n + 1)
                                else
                                  SOME n
                        in
                          loop 0
                        end
                    fun last_non_space s =
                        let
                          val len = String.size s
                          fun loop n =
                              if n < 0 then
                                NONE
                              else
                                if Char.isSpace $ String.sub (s, n)  then
                                  loop (n - 1)
                                else
                                  SOME n
                        in
                          loop (len - 1)
                        end
                    val first = first_non_space s
                    val last = last_non_space s
                  in
                    case (first, last) of
                        (SOME first, SOME last) =>
                        if first <= last then
                          String.substring (s, first, last - first + 1)
                        else
                          ""
                      | _ => ""
                  end
              val filenames = read_lines filename
              val filenames = map trim filenames
              (* val () = app println filenames *)
              val filenames = List.filter (fn s => not (String.isPrefix "(*" s andalso String.isSuffix "*)" s)) filenames
              (* val () = app println filenames *)
              val filenames = List.filter (fn s => s <> "") filenames
              val filenames = map (joinDirFileCurried dir) filenames
              val ctx = process_files ctx filenames
            in
              ctx
            end
          else if ext = SOME "timl" then
            typecheck_file (filename, ctx)
          else raise Error $ sprintf "Unknown filename extension $ of $" [default "<EMPTY>" ext, filename]
    in
      ctx
    end
      
and process_files ctx filenames = foldl process_file ctx filenames
          
fun main filenames =
    let
      val () = app println $ ["Input file(s):"] @ indent filenames
      val ctx = process_files empty_ctx filenames
    in
      ctx
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
    | Impossible msg => (println ("Impossible: " ^ msg); 1)
    | IO.Io e => (println (sprintf "IO Error doing $ on $" [#function e, #name e]); 1)
    | _ => (println ("Internal error"); 1)

end

