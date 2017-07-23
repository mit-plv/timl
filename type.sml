signature TYPE_PARAMS = sig
  structure Idx : IDX
  structure UVarT : UVAR_T
  type base_type
end         

functor TypeFn (Params : TYPE_PARAMS) =
struct

open Params
open UVarT
open Idx
open Bind
                        
type kind = int (*number of type arguments*) * bsort list

type 'mtype constr_core = (sort, name, 'mtype * idx list) ibinds
type 'mtype constr_decl = name * 'mtype constr_core * region
(* to be used in typing context *)                                                          
type 'mtype constr_info = var(*family*) * (unit, name, 'mtype constr_core) tbinds

type 'mtype datatype_def = (name(*for datatype self-reference*) * (unit, name, Idx.bsort list * 'mtype constr_decl list) Bind.tbinds) Bind.tbind

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
