signature TYPE_PARAMS = sig
  structure Idx : IDX
  structure UVarT : UVAR_T
  type base_type
  type var
  type 'mtype datatype_def
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
  
