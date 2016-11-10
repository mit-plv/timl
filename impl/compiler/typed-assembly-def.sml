functor TypedAssemblyDefFun(MicroTiMLHoistedDef : SIG_MICRO_TIML_HOISTED_DEF) =
struct
open List
open Util
infixr 0 $

structure MicroTiMLHoistedDef = MicroTiMLHoistedDef
open MicroTiMLHoistedDef
end
