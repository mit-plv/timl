structure TypeCheckPrint = struct
open TypeCheck

fun typecheck_decls_file filename (ctx as (sctx, kctx, cctx, tctx)) decls =
  let 
      val ctxn as (sctxn, kctxn, cctxn, tctxn) = (sctx_names sctx, names kctx, names cctx, names tctx)
      val ((ctxd, ctx), vcs) = typecheck_decls ctx decls
      val type_lines =
          "OK:" :: "" ::
          (List.concat o map (fn (name, (t, d)) => [sprintf "$ : $" [name, str_t (sctxn, kctxn) t], sprintf "|> $" [str_i sctxn d]]) o #4) ctxd
      val vc_lines =
          sprintf "VCs: [count=$]" [str_int (length vcs)] :: "" ::
	  map str_vc vcs
      val s = join_lines (type_lines @ [""] @ vc_lines)
  in
      s
  end
  handle
  TypeCheck.Error (r, msg) => str_error "Error" filename r msg

end

structure TestParser = struct
open Util
open Region
open Parser

fun parse_file filename =
  let
      val inStream =  TextIO.openIn filename
      fun input n =
	if TextIO.endOfStream inStream
	then ""
	else TextIO.inputN (inStream,n);

      fun on_error (msg, left, right) = print (str_error "Error" filename (left, right) [msg])
      val s = parse (input, on_error, on_error)
      val _ = TextIO.closeIn inStream
  in
      s
  end

structure T = NamefulType
structure E = NamefulExpr
(* open T *)
(* open E *)
open Type
open Expr
open Elaborate
open NameResolve
open TypeCheckPrint
	 
fun main filename =
  let
      val empty_ctx = (([], []), [], [], [])
      val ctx = empty_ctx
      val ctxn = ctx_names ctx
      val decls = parse_file filename
      val decls = map elaborate_decl decls
      val () = app (fn decl => println (fst (E.str_decl ctxn decl))) decls
      val decls = resolve_decls ctxn decls
      val s = typecheck_decls_file filename ctx decls
  in
      s
  end
  handle 
  IO.Io e => sprintf "Error in $ on file $\n" [#function e, #name e]
  | Parser.Error => "Unknown parse error"
  | Elaborate.Error (r, msg) => str_error "Error" filename r [msg]
  | NameResolve.Error (r, msg) => str_error "Error" filename r [msg]
                                            
end

structure Main = struct
fun main (prog_name, args : string list) : int = 
  let
      val output = ""
      val output =
	  case args of
	      filename :: _ => TestParser.main filename
	    | _ => "Usage: filename"
  in	
      print (output ^ "\n");
      0
  end
end

