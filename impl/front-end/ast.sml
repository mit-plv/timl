structure Ast = struct
open Region

type id = string * region

datatype idx = 
	 VarI of string * region
	 | Tint of int * region
	 | Tadd of idx * idx * region
	 | Tmult of idx * idx * region
	 | Tmax of idx * idx * region
	 | Tmin of idx * idx * region
	 | TTI of region

datatype prop =
	 Pconst of string * region
	 | And of prop * prop * region
	 | Or of prop * prop * region
	 | Imply of prop * prop * region
	 | Iff of prop * prop * region
	 | Eq of idx * idx * region
	 | TimeLe of idx * idx * region

type bsort = id

datatype sort =
	 Basic of bsort
	 | Subset of bsort * id * prop * region

datatype quan =
	 Forall
	 | Exists

datatype abs = 
	 Fn
	 | Fix

datatype ty =
	 VarT of string * region
	 | Arrow of ty * idx * ty * region
	 | Prod of ty * ty * region
	 | Sum of ty * ty * region
	 | Quan of quan * bind list * ty * region
	 | Recur of string * bind list * ty * region
	 | AppTT of ty * ty * region
	 | AppTI of ty * idx * region

and bind =
	 Typing of id * ty * region
	 | Kinding of id
	 | Sorting of id * sort * region

fun get_region_t t =
  case t of
      VarT (_, r) => r
    | Arrow (_, _, _, r) => r
    | Prod (_, _, r) => r
    | Sum (_, _, r) => r
    | Quan (_, _, _, r) => r
    | Recur (_, _, _, r) => r
    | AppTT (_, _, r) => r
    | AppTI (_, _, r) => r

datatype ptrn =
	 ConstrP of id * string list * ptrn option * region
         | TupleP of ptrn list * region
         | AliasP of id * ptrn * region

type constr_decl = id * bind list * ty * ty * region

datatype case_type =
         HSumCase
       | HUnpack
       | HCase
             
datatype exp = 
	 Var of string * region
       | Tuple of exp list * region
       | Abs of abs * bind list * exp * region
       | App of exp * exp * region
       | AppT of exp * ty * region
       | AppI of exp * idx * region
       | Case of case_type * exp * (ty option * idx option) * (ptrn * exp) list * region
       | Ascription of exp * ty * region
       | AscriptionTime of exp * idx * region
       | Let of decl list * exp * region
       | Const of int * region

and decl =
    Val of id * exp * region
  | Datatype of string * string list * sort list * constr_decl list * region

type reporter = string * pos * pos -> unit

end

