signature SUBSTABLE_VAR = sig
  include SHIFTABLE_VAR
  val substx_var : (var -> 'a) -> int -> (unit -> 'a) -> var -> 'a
end
                           
functor SubstFn (structure IdxType : IDX_TYPE
                 structure SubstableVar : SUBSTABLE_VAR
                 sharing type IdxType.Idx.var = SubstableVar.var
                ) = struct

open IdxType
open SubstableVar
open Util
open ShiftUtil
       
infixr 0 $

structure IdxShift = IdxShiftFn (structure Idx = Idx
                                 structure ShiftableVar = SubstableVar)
open IdxShift
                                        
structure TypeShift = TypeShiftFn (structure Type = Type
                                  structure ShiftableVar = SubstableVar
                                  structure ShiftableIdx = IdxShift
                                 )
open TypeShift
                                        
(* ToDo: just a hack now *)
fun forget_above_i_i x b = forget_i_i x 100000000 b

(* subst *)

exception Error of string

fun visit_VarI (d, x, v) env y =
  let
    val x = x + env
    val d = d + env
  in
    substx_var VarI x (fn () => shiftx_i_i 0 d v) y
  end

structure IdxSubst = IdxSubstFn (structure Idx = Idx
                                 val visit_VarI = visit_VarI
                                )
open IdxSubst
                                        
fun visit_MtVar (d, x, v) env y =
  let
    fun add_depth (di, dt) (di', dt') = (idepth_add (di, di'), tdepth_add (dt, dt'))
    fun get_di (di, dt) = di
    fun get_dt (di, dt) = dt
    val x = x + unTDepth (get_dt env)
    val (di, dt) = add_depth d env
  in
    substx_var MtVar x (fn () => shiftx_i_mt 0 (unIDepth di) $ shiftx_t_mt 0 (unTDepth dt) v) y
  end
    
structure TypeSubst = TypeSubstFn (structure Type = Type
                                   val visit_MtVar = visit_MtVar
                                   val substx_i_i = substx_i_i
                                   val substx_i_s = substx_i_s
                                  )
open TypeSubst

end
