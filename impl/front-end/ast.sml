structure Ast = struct

(* the line and col fields of right position are not used *)
type pos = {abs : int, line : int, col : int}
type region = pos * pos

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

datatype bsort =
	 Bsort of string * region

datatype sort =
	 Basic of bsort * region
	 | Subset of bsort * string * prop * region

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
	 | Quan of quan * binding list * ty * region
	 | Recur of string * binding list * ty * region
	 | AppTT of ty * ty * region
	 | AppTI of ty * idx * region

and binding =
	 Typing of string * ty * region
	 | Kinding of string * region
	 | Sorting of string * sort * region

datatype ptrn =
	 Constr of string * string list * string * region

datatype exp = 
	 Var of string * region
       | Tuple of exp list * region
       | Abs of abs * binding list * exp * region
       | App of exp * exp * region
       | AppT of exp * ty * region
       | AppI of exp * idx * region
       | Case of exp * (ty * idx) option * (ptrn * exp) list * region
       | Ascription of exp * ty * region
       | AscriptionTime of exp * idx * region
       | Let of def list * exp * region

and def =
    Val of string * exp * region

type reporter = string * pos * pos -> unit

end

