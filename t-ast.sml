(* signature VAR2 = sig *)
(*   type var *)
(* end *)

(* type-annotated AST *)
functor TAst (Idx : IDX) = struct

open Idx
open Operators
open UVar
open Bind
open BaseTypes
       
type kind = int (*number of type arguments*) * bsort list

datatype mtype = 
	 Arrow of mtype * idx * mtype
         | TyNat of idx * region
         | TyArray of mtype * idx
	 | BaseType of base_type
         | Unit of region
	 | Prod of mtype * mtype
	 | UniI of sort * (name * mtype) ibind * region
         | MtVar of var
         (* type-level computations *)
         | MtAbs of kind * (name * mtype) tbind * region
         | MtApp of mtype * mtype
         | MtAbsI of bsort * (name * mtype) ibind  * region
         | MtAppI of mtype * idx
         | UVar of (bsort, kind, mtype) uvar_mt * region

datatype expr =
	 Var of var 
         | EConst of expr_const
         | EUnOp of expr_un_op * expr
         | BinOp of bin_op * expr * expr
	 | TriOp of tri_op * expr * expr * expr
         | EEI of expr_EI * expr * idx
         | ET of expr_T * mtype * region
	 (* | Abs of ptrn * expr *)
	 (* | AbsI of sort * (name * expr) ibind * region *)
	 (* | AppConstr of (long_id * bool) * idx list * expr *)
	 (* | Case of expr * return * (ptrn * expr) list * region *)
	 (* | Let of return * decl list * expr * region *)
	 (* | Ascription of expr * mtype *)


end
