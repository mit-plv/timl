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

datatype ptrn =
	 Constr of id * string list * id * region

datatype exp = 
	 Var of string * region
       | Tuple of exp list * region
       | Abs of abs * bind list * exp * region
       | App of exp * exp * region
       | AppT of exp * ty * region
       | AppI of exp * idx * region
       | Case of exp * (ty * idx) option * (ptrn * exp) list * region
       | Ascription of exp * ty * region
       | AscriptionTime of exp * idx * region
       | Let of dec list * exp * region
       | Const of int * region

and dec =
    Val of id * exp * region

type reporter = string * pos * pos -> unit

end

