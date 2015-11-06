structure Ast = struct
open Region
open Operators
         
type id = string * region

datatype idx = 
	 VarI of string * region
	 | ConstIN of int * region
	 | ConstIT of string * region
         | UnOpI of idx_un_op * idx * region
	 | BinOpI of idx_bin_op * idx * idx * region
	 | TTI of region

datatype prop =
	 ConstP of string * region
         | Not of prop * region
	 | BinConn of bin_conn * prop * prop * region
	 | BinPred of bin_pred * idx * idx * region

type bsort = id

datatype sort =
	 Basic of bsort
	 | Subset of bsort * id * prop * region

datatype quan =
	 Forall
	 | Exists

datatype abs = 
	 Fn
	 | Rec

and tbind =
    Kinding of id
    | Sorting of id * sort * region

datatype ty =
	 VarT of string * region
	 | Arrow of ty * idx * ty * region
	 | Prod of ty * ty * region
	 | Quan of quan * tbind list * ty * region
	 | AppTT of ty * ty * region
	 | AppTI of ty * idx * region

fun get_region_t t =
  case t of
      VarT (_, r) => r
    | Arrow (_, _, _, r) => r
    | Prod (_, _, r) => r
    | Quan (_, _, _, r) => r
    | AppTT (_, _, r) => r
    | AppTI (_, _, r) => r

type constr_core = tbind list * ty * ty option
type constr_decl = id * constr_core option * region

datatype ptrn =
	 ConstrP of id * string list * ptrn option * region
         | TupleP of ptrn list * region
         | AliasP of id * ptrn * region
         | AnnoP of ptrn * ty * region

fun get_region_pn pn =
  case pn of
      ConstrP (_, _, _, r) => r
    | TupleP (_, r) => r
    | AliasP (_, _, r) => r
    | AnnoP (_, _, r) => r

datatype bind =
	 Typing of ptrn
	 | TBind of tbind

datatype case_type =
         HCase
       | HUnpack
             
datatype exp = 
	 Var of string * region
       | Tuple of exp list * region
       | Abs of bind list * exp * region
       | App of exp * exp * region
       | AppT of exp * ty * region
       | AppI of exp * idx * region
       | Case of case_type * exp * (ty option * idx option) * (ptrn * exp) list * region
       | Ascription of exp * ty * region
       | AscriptionTime of exp * idx * region
       | Let of decl list * exp * region
       | Const of int * region
       | BinOp of bin_op * exp * exp * region

and decl =
    Val of ptrn * exp * region
    | Rec of id * bind list * (ty option * idx option) * exp * region
    | Datatype of string * string list * sort list * constr_decl list * region

type reporter = string * pos * pos -> unit

end

