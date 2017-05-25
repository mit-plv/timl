(* signature VAR2 = sig *)
(*   type var *)
(* end *)

(* type-annotated AST *)
functor TAst (structure Idx : IDX structure Type : TYPE) = struct

open Idx
open Type
open Operators
open UVar
open Bind
open BaseTypes
       
datatype expr =
	 Var of var * bool
         | EConst of expr_const * region
         | EUnOp of expr_un_op * expr * region
         | BinOp of bin_op * expr * expr
	 | TriOp of tri_op * expr * expr * expr
         | EEI of expr_EI * expr * idx
         | ET of expr_T * mtype * region
	 (* | Abs of ptrn * expr *)
	 | AbsI of sort * (name * expr) ibind * region
	 (* | AppConstr of (long_id * bool) * idx list * expr *)
	 (* | Case of expr * return * (ptrn * expr) list * region *)
	 (* | Let of return * decl list * expr * region *)
	 | Ascription of expr * mtype

end
