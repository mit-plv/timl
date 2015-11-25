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

