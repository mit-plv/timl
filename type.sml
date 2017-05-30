signature TYPE_PARAMS = sig
  structure Idx : IDX
  structure UVarT : UVAR_T
  type base_type
  type var
  type name
  type region
end         

functor TypeFn (Params : TYPE_PARAMS) =
struct

open Params
open UVarT
open Idx
open Bind
                        
type kind = int (*number of type arguments*) * bsort list

structure Datatype = DatatypeFn (structure Idx = Idx
                                 type var = var)
open Datatype

(* monotypes *)
datatype mtype = 
	 Arrow of mtype * idx * mtype
         | TyNat of idx * region
         | TyArray of mtype * idx
	 | BaseType of base_type * region
         | Unit of region
	 | Prod of mtype * mtype
	 | UniI of sort * (name * mtype) ibind * region
         | MtVar of var
         | MtAbs of kind * (name * mtype) tbind * region
         | MtApp of mtype * mtype
         | MtAbsI of bsort * (name * mtype) ibind  * region
         | MtAppI of mtype * idx
         | UVar of (bsort, kind, mtype) uvar_mt * region
         | TDatatype of mtype datatype_def * region

datatype ty = 
	 Mono of mtype
	 | Uni of (name * ty) tbind * region

end

functor TestTypeFnSignatures (Params : TYPE_PARAMS) = struct
structure M : TYPE = TypeFn (Params)
end
  
functor TypeSubstFn (structure Type : TYPE
                    structure ShiftableVar : SHIFTABLE_VAR
                    sharing type Type.var = ShiftableVar.var
                   ) = struct

open Type
open ShiftableVar
open ShiftUtil

infixr 0 $
         
fun on_i_mt on_i on_s x n b =
  let
    fun f x n b =
      case b of
	  Arrow (t1, d, t2) => Arrow (f x n t1, on_i x n d, f x n t2)
        | TyNat (i, r) => TyNat (on_i x n i, r)
        | TyArray (t, i) => TyArray (f x n t, on_i x n i)
        | Unit r => Unit r
	| Prod (t1, t2) => Prod (f x n t1, f x n t2)
	| UniI (s, bind, r) => UniI (on_s x n s, on_i_ibind f x n bind, r)
        | MtVar y => MtVar y
        | MtApp (t1, t2) => MtApp (f x n t1, f x n t2)
        | MtAbs (k, bind, r) => MtAbs (k, on_i_tbind f x n bind, r)
        | MtAppI (t, i) => MtAppI (f x n t, on_i x n i)
        | MtAbsI (b, bind, r) => MtAbsI (b, on_i_ibind f x n bind, r)
	| BaseType a => BaseType a
        | UVar a => b
        | TDatatype (dt, r) =>
          let
            fun on_constr_decl x n (name, c, r) = (name, on_i_constr_core on_i on_s f x n c, r)
            val dt = on_i_tbind (on_i_tbinds return3 (on_pair (return3, on_list on_constr_decl))) x n dt
          in
            TDatatype (dt, r)
          end
  in
    f x n b
  end

and on_i_constr_core on_i on_s on_i_mt x n b = on_i_ibinds on_s (on_pair (on_i_mt, on_list on_i)) x n b
                                    
fun on_i_t on_i_mt x n b =
  let
    fun f x n b =
      case b of
	  Mono t => Mono (on_i_mt x n t)
	| Uni (bind, r) => Uni (on_i_tbind f x n bind, r)
  in
    f x n b
  end

fun on_t_mt on_v x n b =
  let
    fun f x n b =
      case b of
	  Arrow (t1, d, t2) => Arrow (f x n t1, d, f x n t2)
        | TyNat (i, r) => TyNat (i, r)
        | TyArray (t, i) => TyArray (f x n t, i)
        | Unit r => Unit r
	| Prod (t1, t2) => Prod (f x n t1, f x n t2)
	| UniI (s, bind, r) => UniI (s, on_t_ibind f x n bind, r)
        | MtVar y => MtVar $ on_v x n y
        | MtApp (t1, t2) => MtApp (f x n t1, f x n t2)
        | MtAbs (k, bind, r) => MtAbs (k, on_t_tbind f x n bind, r)
        | MtAppI (t, i) => MtAppI (f x n t, i)
        | MtAbsI (s, bind, r) => MtAbsI (s, on_t_ibind f x n bind, r)
	| BaseType a => BaseType a
        | UVar a => b
        | TDatatype (dt, r) =>
          let
            fun on_constr_decl x n (name, c, r) = (name, on_t_constr_core f x n c, r)
            val dt = on_t_tbind (on_t_tbinds return3 (on_pair (return3, on_list on_constr_decl))) x n dt
          in
            TDatatype (dt, r)
          end
  in
    f x n b
  end
    
and on_t_constr_core on_mt x n b = on_t_ibinds return3 (on_pair (on_mt, return3)) x n b
                                         
fun on_t_t on_t_mt x n b =
  let
    fun f x n b =
      case b of
	  Mono t => Mono (on_t_mt x n t)
	| Uni (bind, r) => Uni (on_t_tbind f x n bind, r)
  in
    f x n b
  end

fun shiftx_i_mt x n b = on_i_mt shiftx_i_i shiftx_i_s x n b
and shiftx_t_mt x n b = on_t_mt shiftx_v x n b
fun shift_i_mt b = shiftx_i_mt 0 1 b
fun shift_t_mt b = shiftx_t_mt 0 1 b

fun shiftx_i_t x n b = on_i_t shiftx_i_mt x n b
fun shift_i_t b = shiftx_i_t 0 1 b

fun shiftx_t_t x n b = on_t_t shiftx_t_mt x n b
fun shift_t_t b = shiftx_t_t 0 1 b

fun forget_i_mt x n b = on_i_mt forget_i_i forget_i_s x n b
fun forget_t_mt x n b = on_t_mt forget_v x n b
fun forget_i_t x n b = on_i_t forget_i_mt x n b
fun forget_t_t x n b = on_t_t forget_t_mt x n b

end
