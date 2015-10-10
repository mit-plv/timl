structure TiML = struct
structure T = NamefulType
structure E = NamefulExpr
open Type
open Expr
open Util
open Parser
open Elaborate
open NameResolve
open TypeCheck
open SMT2Printer
open SMTSolver

infixr 0 $

fun print_result show_region filename (((ctxd, ds, ctx), vcs) : tc_result) =
  let 
      val ctxn as (sctxn, kctxn, cctxn, tctxn) = ctx_names ctx
      val type_lines =
          "OK: Typechecked" :: "" ::
          (List.concat o map (fn (name, t) => [sprintf "$ : $" [name, str_t (sctxn, kctxn) t], ""]) o rev o #4) ctxd
      val time_lines =
          "Times:" :: "" ::
          (List.concat o map (fn d => [sprintf "|> $" [str_i sctxn d], ""])) ds
      val vc_lines =
          sprintf "Verification Conditions: [count=$]" [str_int (length vcs)] :: "" ::
	  concatMap (str_vc show_region filename) vcs
      val s = join_lines (type_lines @ time_lines @ vc_lines)
  in
      s
  end

fun main filename =
  let
      val empty_ctx = (([], []), [], [], [])
      val ctx = empty_ctx
      val ctxn = ctx_names ctx
      val decls = parse_file filename
      val decls = map elaborate_decl decls
      (* val () = (print o join_lines o map (suffix "\n") o fst o E.str_decls ctxn) decls *)
      val decls = resolve_decls ctxn decls
      (* val () = (print o join_lines o map (suffix "\n") o fst o str_decls ctxn) decls *)
      val result as ((ctxd, ds, ctx), vcs) = typecheck_decls ctx decls
      (* val smt2 = to_smt2 vcs *)
      (* val () = write_file (filename ^ ".smt2", smt2) *)
      val () = println $ print_result false filename result
      val () = println "Solving by Z3 SMT solver ..."
      val result as (_, unsats) = mapSnd (smt_solver filename) result
      fun print_unsat filename (vc, counter) =
        str_vc true filename vc @
        [""] @
        (case counter of
             SOME assigns =>
             ["Counter example:"] @
             map (fn (name, value) => sprintf "$ = $" [name, value]) assigns @
             [""]
           | NONE => ["Can't prove and can't find counter example"]) 
      val () =
          if length (snd result) <> 0 then
              (println (sprintf "Can't prove the following $ condition(s):\n" [str_int $ length unsats]);
               (app println o concatMap (print_unsat filename)) unsats)
          else
              println "All conditions proved."
  in
      OK result
  end
  handle 
  IO.Io e => Failed $ sprintf "Error in $ on file $\n" [#function e, #name e]
  | Parser.Error => Failed $ "Unknown parse error"
  | Elaborate.Error (r, msg) => Failed $ str_error "Error" filename r ["Elaborate error: " ^ msg]
  | NameResolve.Error (r, msg) => Failed $ str_error "Error" filename r ["Resolve error: " ^ msg]
  | TypeCheck.Error (r, msg) => Failed $ str_error "Error" filename r ((* "Type error: " :: *) msg)
  | OS.SysErr (msg, _) => Failed $ "SysErr: " ^ msg
                                            
end

structure Main = struct
open Util
open OS.Process
         
fun main (prog_name, args : string list) : int = 
    let
        val _ =
	    case args of
	        filename :: _ =>
                (case TiML.main filename of
                     OK _ => ()
                   | Failed msg => println msg
                )
	      | _ => (println "Usage: THIS filename"; exit(failure));
    in	
        0
    end

end

