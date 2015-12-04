structure TiML = struct
structure E = NamefulExpr
open Expr
open Util
open Parser
open Elaborate
open NameResolve
open TypeCheck

infixr 0 $

fun print_result show_region filename (((decls, ctxd, ds, ctx), vcs) : tc_result) =
  let 
      val ctxn as (sctxn, kctxn, cctxn, tctxn) = ctx_names ctx
      val header =
          sprintf "Typechecked $" [filename] ::
          [""]
      val idx_lines =
          (List.concat o map (fn (name, s) => [sprintf "$ : $" [name, str_s sctxn s], ""]) o rev o #1) ctxd
      val type_lines =
          (List.concat o map (fn (name, t) => [sprintf "$ : $" [name, str_t (sctxn, kctxn) t], ""]) o rev o #4) ctxd
      val time_lines =
          "Times:" :: "" ::
          (List.concat o map (fn d => [sprintf "|> $" [str_i sctxn d], ""])) ds
      val vc_lines =
          sprintf "Verification Conditions: [count=$]" [str_int (length vcs)] ::
          "" ::
	  concatMap (fn vc => VC.str_vc show_region filename vc @ [""]) vcs
      val s = join_lines 
                  (
                    header
                    @ idx_lines 
                    @ type_lines 
                    @ time_lines 
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
      val ctxn = ctx_names ctx
      val decls = parse_file filename
      val decls = map elaborate_decl decls
      (* val () = (print o join_lines o map (suffix "\n") o fst o E.str_decls ctxn) decls *)
      val decls = resolve_decls ctxn decls
      (* val () = (print o join_lines o map (suffix "\n") o fst o str_decls ctxn) decls *)
      val result as ((decls, ctxd, ds, ctx), vcs) = typecheck_decls ctx decls
      (* val () = write_file (filename ^ ".smt2", to_smt2 vcs) *)
      val () = println $ print_result false filename result
      val () = println $ sprintf "Generated $ proof obligations." [str_int $ length vcs]
      val (_, unsats) = mapSnd (smt_solver filename) result
      (* val unsats = map (fn vc => (vc, NONE)) vcs *)
      fun print_unsat filename (vc, counter) =
        VC.str_vc false filename vc @
        [""] @
        (case counter of
             SOME assigns =>
             if length assigns > 0 then
                 ["Counter-example:"] @
                 map (fn (name, value) => sprintf "$ = $" [name, value]) assigns @
                 [""]        
             else []
           | NONE => ["SMT solver reported 'unknown': can't prove and can't find counter example\n"]
        ) 
      val () =
          if length unsats > 0 then
              let
                  val () = println (sprintf "SMT solver can't prove the following $ proof obligations:\n" [str_int $ length unsats])
                  val () = (app println o concatMap (print_unsat filename)) unsats
                  val () = println "Applying BigO solver ..."
                  val vcs = BigOSolver.solve_vcs $ map fst unsats
                  val () = 
                      if length vcs > 0 then
                          let
                              val () = println $ sprintf "BigO solver can't prove the following $ proof obligations:\n" [str_int $ length vcs]
                              val () = app println $ concatMap (fn vc => VC.str_vc true filename vc @ [""]) vcs
                          in
                              ()
                          end
                      else
                          println "All conditions proved."
              in
                  ()
              end
          else
              println "All conditions proved."
  in
      ctx
  end
  handle 
  Elaborate.Error (r, msg) => raise Error $ str_error "Error" filename r ["Elaborate error: " ^ msg]
  | NameResolve.Error (r, msg) => raise Error $ str_error "Error" filename r ["Resolve error: " ^ msg]
  | TypeCheck.Error (r, msg) => raise Error $ str_error "Error" filename r ((* "Type error: " :: *) msg)
  | Parser.Error => raise Error "Unknown parse error"
  | SMTError msg => raise Error $ "SMT error: " ^ msg
  | IO.Io e => raise Error $ sprintf "IO error in function $ on file $" [#function e, #name e]
  | OS.SysErr (msg, err) => raise Error $ sprintf "System error$: $" [(default "" o Option.map (prefix " " o OS.errorName)) err, msg]
                                                         
fun main filenames =
  let
      val ctx = foldl typecheck_file empty_ctx filenames
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

end

