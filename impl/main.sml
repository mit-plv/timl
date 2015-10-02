structure TypeCheckPrint = struct
open TypeCheck

fun check_file filename (ctx as (sctx, kctx, cctx, tctx)) e =
    let 
	val ctxn as (sctxn, kctxn, cctxn, tctxn) = (sctx_names sctx, names kctx, names cctx, names tctx)
    in
	case typecheck_opt ctx e of
	    OK ((t, d), vcs) =>
	    let
	    in
		sprintf
		    "OK: \nType: $\nTime: $\nVCs: [count=$]\n$\n"
		    [str_t (sctxn, kctxn) t,
		     str_i sctxn d,
		     str_int (length vcs),
		     join "\n" (map str_vc vcs)]
	    end
	  | Failed (r, msg) => str_error "Error" filename r ((join "" o map (fn s => s ^ "\n")) msg)
    end

val check = check_file "string"

end

structure Ilist = struct

structure T = NamefulType
structure E = NamefulExpr
open T
open E

infix 7 $
infix 6 %+
infix 6 %*
infix 4 %<=
infix 3 /\
infix 1 -->
infix 1 <->

open Region
val dummy = dummy_region
fun VarI' x =  VarI (x, dummy)
fun Var' x =  Var (x, dummy)
fun VarT' x =  VarT (x, dummy)
fun AppV' (x, ts, is) =  AppV ((x, dummy), ts, is, dummy)
fun AppConstr' (x, ts, is, e) =  AppConstr ((x, dummy), ts, is, e)
fun Constr' (x, inames, ename) =  Constr ((x, dummy), inames, ename)
val T0' = T0 dummy
val T1' = T1 dummy

val ilist = ArrowK (1, [STime])
fun NilI family : constr = (family, ["a"], [], Unit dummy, [T0'])
fun ConsI family : constr = (family, ["a"], [("n", STime)], Prod (VarT' "a", AppV' (family, [VarT' "a"], [VarI' "n"])), [VarI' "n" %+ T1'])
val NilI_int = AppConstr' ("NilI", [Int dummy], [], TT dummy)
val ConsI_int = AppConstr' ("ConsI", [Int dummy], [T0'], Pair (Const (77, dummy), NilI_int))

open Type
open Expr
open NameResolve
open TypeCheck

val sctx = ([], [])
val sctxn = sctx_names sctx
val ilist = resolve_kind sctxn ilist
val skctx as (_, kctx) = (sctx, [("ilist", ilist)])
val skctxn as (_, kctxn) = (sctxn, names kctx)
val NilI = resolve_constr skctxn (NilI "ilist")
val ConsI = resolve_constr skctxn (ConsI "ilist")
val ctx as (_, _, cctx, tctx) : context = (sctx, kctx, [("ConsI", ConsI), ("NilI", NilI)], [])
val ctxn = (sctxn, kctxn, names cctx, names tctx)

end

structure TestParser = struct
open Util
open Parser
open Elaborate
structure T = NamefulType
structure E = NamefulExpr
open T
open E

fun do_parse filename =
  let
      val src = ref (
	      "      map = fn [a] [b] {m : Time} (f : a -- m -> b) =>  " ^
	      "        fix (map : forall {n : Time}, list a {n} -- (m + 2) * n -> list b {n}) {n : Time} (ls : list a {n}) => " ^
	      "          case ls return list b {n} |> (m + 2) * n of  " ^
	      "              NilI _ => NilI [b] ()  " ^
	      "            | ConsI {n'} x_xs => ConsI [b] {n'} (f (fst x_xs), map {n'} (snd x_xs))  "
	  )

      val src = ref ")"
	      
      fun input _ = let val s = !src in src := ""; s end
      (* val filename = "string" *)

      (* val filename = "test.timl" *)
      val inStream =  TextIO.openIn filename
      fun input n =
	if TextIO.endOfStream inStream
	then ""
	else TextIO.inputN (inStream,n);

      fun on_error (msg, left, right) = print (str_error "Error" filename (left, right) msg)
      val s = parse (input, on_error, on_error)
      val _ = TextIO.closeIn inStream
  in
      s
  end

open Ilist
open TypeCheckPrint
					      
fun main filename =
    let
	val e = do_parse filename
	val e = elaborate e
	(* val () = println (E.str_e ([], [], [], []) e) *)
	val e = resolve_expr ctxn e
    in
	check_file filename ctx e
    end
    handle 
    IO.Io e => sprintf "Error calling $ on file $\n" [#function e, #name e]
    | Parser.Error => "Parse error"
    | Elaborate.Error (r, msg) => str_error "Error" filename r msg
    | NameResolve.Error (r, msg) => str_error "Error" filename r msg
end

structure Main = struct
fun main (prog_name, args : string list) : int = 
    let
	val output = ""
	(* val output = RecurExamples.main () *)
	(* val output = DatatypeExamples.main () *)
	(* val output = NamefulDatatypeExamples.main () *)
	val output =
	    case args of
		filename :: _ => TestParser.main filename
	      | _ => "Usage: filename"
    in	
	print (output ^ "\n");
	0
    end
end

