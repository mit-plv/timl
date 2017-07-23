signature IDX_PARAMS = sig
  structure UVarI : UVAR_I
  type base_sort
  type var
  type name
  type region
  type 'idx exists_anno
end         

functor IdxFn (Params : IDX_PARAMS) =
struct

open Params
open UVarI
open Bind
open Operators
                        
(* basic index sort with arrow and uvar *)
datatype bsort = 
         Base of base_sort 
         | BSArrow of bsort * bsort
         | UVarBS of bsort uvar_bs
                           
datatype idx =
	 VarI of var
         | IConst of idx_const * region
         | UnOpI of idx_un_op * idx * region
         | BinOpI of idx_bin_op * idx * idx
         | Ite of idx * idx * idx * region
         | IAbs of bsort * (name * idx) ibind * region
         | UVarI of (bsort, idx) uvar_i * region

datatype prop =
	 PTrueFalse of bool * region
         | BinConn of bin_conn * prop * prop
         | Not of prop * region
	 | BinPred of bin_pred * idx * idx
         | Quan of idx exists_anno (*for linking idx inferer with types*) quan * bsort * (name * prop) ibind * region

datatype sort =
	 Basic of bsort * region
	 | Subset of (bsort * region) * (name * prop) ibind * region
         | UVarS of (bsort, sort) uvar_s * region
         (* [SAbs] and [SApp] are just for higher-order unification *)
         | SAbs of bsort * (name * sort) ibind * region
         | SApp of sort * idx
                            
end

functor TestIdxFnSignatures (Params : IDX_PARAMS) = struct
structure M : IDX = IdxFn (Params)
end

