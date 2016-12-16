structure MicroTiMLInst =
struct
open List
open Util
infixr 0 $

type pos = unit
type reporter = string * pos * pos -> unit

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
end
