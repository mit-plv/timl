(* signature VAR2 = sig *)
(*   type var *)
(* end *)

(* type-annotated AST *)
functor TAst (structure Idx : IDX
              structure Type : TYPE
              structure UVarT : UVAR_T
             ) = struct

open Idx
open Type
open UVarT
open Operators
open Bind
       
structure Datatype = DatatypeFn (structure Idx = Idx
                                 type var = var)
open Datatype
       
structure Pattern = PatternFn (structure Idx = Idx
                               type var = var)
open Pattern

type kind = int (*number of type arguments*) * bsort list

(* (* monotypes *) *)
(* datatype mtype =  *)
(* 	 Arrow of mtype * idx * mtype *)
(*          | TyNat of idx * region *)
(*          | TyArray of mtype * idx *)
(* 	 | BaseType of base_type * region *)
(*          | Unit of region *)
(* 	 | Prod of mtype * mtype *)
(* 	 | UniI of sort * (name * mtype) ibind * region *)
(*          | MtVar of var *)
(*          | MtAbs of kind * (name * mtype) tbind * region *)
(*          | MtApp of mtype * mtype *)
(*          | MtAbsI of bsort * (name * mtype) ibind  * region *)
(*          | MtAppI of mtype * bsort * idx *)
(*          | UVar of (bsort, kind, mtype) uvar_mt * region *)
(*          | TDatatype of mtype datatype_def *)

type return = mtype option * idx option
                                 
datatype expr =
	 Var of var * bool
         | EConst of expr_const * region
         | EUnOp of expr_un_op * expr * region
         | BinOp of bin_op * expr * expr
	 | TriOp of tri_op * expr * expr * expr
         | EEI of expr_EI * expr * idx
         | ET of expr_T * mtype * region
	 (* | Abs of mtype ptrn * expr *)
	 | AbsI of sort * (name * expr) ibind * region
	 (* | AppConstr of (long_id * bool) * idx list * expr *)
	 (* | Case of expr * return * (mtype ptrn * expr) list * region *)
	 (* | Let of return * decl list * expr * region *)
	 | Ascription of expr * mtype

end
