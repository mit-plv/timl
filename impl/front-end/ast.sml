structure Ast = struct

(* the line and col fields of right position are not used *)
type pos = {abs : int, line : int, col : int}

datatype idx = 
	 VarI of string * pos * pos
	 | Tint of int * pos * pos
	 | Tadd of idx * idx * pos * pos
	 | Tmult of idx * idx * pos * pos
	 | Tmax of idx * idx * pos * pos
	 | Tmin of idx * idx * pos * pos

datatype prop =
	 Pconst of string * pos * pos
	 | And of prop * prop * pos * pos
	 | Or of prop * prop * pos * pos
	 | Imply of prop * prop * pos * pos
	 | Iff of prop * prop * pos * pos
	 | Eq of idx * idx * pos * pos
	 | TimeLe of idx * idx * pos * pos

datatype bsort =
	 Bsort of string

datatype sort =
	 Basic of bsort * pos * pos
	 | Subset of bsort * string * prop * pos * pos

datatype quan =
	 Forall
	 | Exists

datatype abs = 
	 Fn
	 | Fix

datatype ty =
	 VarT of string * pos * pos
	 | Arrow of ty * idx * ty * pos * pos
	 | Prod of ty * ty * pos * pos
	 | Sum of ty * ty * pos * pos
	 | Quan of quan * binding list * ty * pos * pos
	 | Recur of string * binding list * ty * pos * pos
	 | AppTT of ty * ty * pos * pos
	 | AppTI of ty * idx * pos * pos

and binding =
	 Typing of string * ty * pos * pos
	 | Kinding of string * pos * pos
	 | Sorting of string * sort * pos * pos

datatype ptrn =
	 Constr of string * string list * string * pos * pos

datatype exp = 
	 Var of string * pos * pos
       | Tuple of exp list * pos * pos
       | Abs of abs * binding list * exp * pos * pos
       | App of exp * exp * pos * pos
       | AppT of exp * ty * pos * pos
       | AppI of exp * idx * pos * pos
       | Case of exp * (ty * idx) option * (ptrn * exp) list * pos * pos
       | Ascription of exp * ty * pos * pos
       | AscriptionTime of exp * idx * pos * pos
       | Let of def list * exp * pos * pos

and def =
    Val of string * exp * pos * pos

type reporter = string * pos * pos -> unit

end

