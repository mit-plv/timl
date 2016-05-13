structure TiML = struct
structure E = NamefulExpr
open Expr
open Util
open Parser
open Elaborate
open NameResolve
open TypeCheck

infixr 0 $

fun print_result show_region filename ((typing, vcs) : tc_result) =
    let 
      val header =
          (* sprintf "Typechecked $" [filename] :: *)
          sprintf "Typechecking results for $:" [filename] ::
          [""]
      val typing_lines = [str_typing_info typing]
      val vc_lines =
          sprintf "Verification Conditions: [count=$]" [str_int (length vcs)] ::
          "" ::
	  concatMap (fn vc => VC.str_vc show_region filename vc @ [""]) vcs
      val s = join_lines 
                (
                  header
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
      val decls = parse_file filename
      val decls = map elaborate_decl decls
      (* val () = (app println o map (suffix "\n") o fst o E.str_decls ctxn) decls *)
      val decls = resolve_decls ctxn decls
      (* val () = (app println o map (suffix "\n") o fst o UnderscoredExpr.str_decls ctxn) decls *)
      val result as ((decls, ctxd, ds, ctx), vcs) = typecheck_decls ctx decls
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
              val unsats = List.mapPartial id $ map (SMTSolver.smt_solver_single filename) vcs
              val () = println (sprintf "SMT solver generated or left $ proof obligations unproved." [str_int $ length unsats])
              val () = println ""
              (* val () = print_unsats false filename unsats *)
            in
              (* map fst unsats *)
              unsats
            end
      val vcs = (smt_solver o bigO_solver) vcs
      val () = print $ print_result false filename result
      val () = if null vcs then
                 println $ "Typechecked."
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
              val filenames = read_lines filename
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

