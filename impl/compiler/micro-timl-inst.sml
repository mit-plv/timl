structure MicroTiMLInst =
struct
open List
open Util
infixr 0 $

type pos = {abs : int, line : int, col : int}
type region = pos * pos
type reporter = string * pos * pos -> unit

fun str_region header filename ((left, right) : region) = sprintf "File $, line $-$, characters $-$:" [filename, str_int (#line left), str_int (#line right), str_int (#col left), str_int (max (#col right) 0)]

fun str_error header filename region msg = join_lines $ str_region header filename region :: indent msg

fun combine_region (r1 : region) (r2 : region) : region = (#1 r1, #2 r2)

structure StringTime =
struct
open Util

type time_type = string

val Time0 = "0.0"
val Time1 = "1.0"

fun from_string s = s
fun str_time r = r
end

structure IntNat =
struct
open Util

type nat_type = int

fun from_int i = i
val str_nat = prefix "@" o str_int
end

structure MicroTiMLDef = MicroTiMLDefFun(
    structure Time = StringTime
    structure Nat = IntNat)

open MicroTiMLDef
structure MicroTiMLUtil = MicroTiMLUtilFun(MicroTiMLDef)
open MicroTiMLUtil
structure AstTransformers = AstTransformersFun(MicroTiMLDef)
open AstTransformers
structure DerivAssembler = DerivAssemblerFun(MicroTiMLDef)
open DerivAssembler
structure DerivTransformers = DerivTransformersFun(MicroTiMLDef)
open DerivTransformers
structure CPSPass = CPSPassFun(MicroTiMLDef)
open CPSPass
structure WrapAbsPass = WrapAbsPassFun(MicroTiMLDef)
open WrapAbsPass
end
