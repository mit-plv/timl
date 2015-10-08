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
	 
fun typecheck_decls_print filename (ctx as (sctx, kctx, cctx, tctx)) decls =
  let 
      val ((ctxd, ds, ctx as (sctx, kctx, cctx, tctx)), vcs) = typecheck_decls ctx decls
      val ctxn as (sctxn, kctxn, cctxn, tctxn) = (sctx_names sctx, names kctx, names cctx, names tctx)
      val type_lines =
          "OK: Typechecked" :: "" ::
          (List.concat o map (fn (name, t) => [sprintf "$ : $" [name, str_t (sctxn, kctxn) t], ""]) o rev o #4) ctxd
      val time_lines =
          "Times:" :: "" ::
          (List.concat o map (fn d => [sprintf "|> $" [str_i sctxn d], ""])) ds
      val vc_lines =
          sprintf "VCs: [count=$]" [str_int (length vcs)] :: "" ::
	  map (str_vc filename) vcs
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
      val s = typecheck_decls_print filename ctx decls
  in
      s
  end
  handle 
  IO.Io e => sprintf "Error in $ on file $\n" [#function e, #name e]
  | Parser.Error => "Unknown parse error"
  | Elaborate.Error (r, msg) => str_error "Error" filename r ["Elaborate error: " ^ msg]
  | NameResolve.Error (r, msg) => str_error "Error" filename r ["Resolve error: " ^ msg]
  | TypeCheck.Error (r, msg) => str_error "Error" filename r ((* "Type error: " :: *) msg)
                                            
end

structure Main = struct
fun main (prog_name, args : string list) : int = 
  let
      val output = ""
      val output =
	  case args of
	      filename :: _ => TiML.main filename
	    | _ => "Usage: THIS filename"
  in	
      print (output ^ "\n");
      0
  end
end

