type var = int

signature THEORY = sig
    type kind
    type constr
end

structure Theory : THEORY = struct
type prop = unit
datatype kind =
	 Unit
	 | Prod of kind * kind
	 | Subset of kind * prop
datatype constr =
	 TT
	 | Pair of constr * constr
end

signature KIND = sig
    type kind
end

functor Constr (structure Theory : THEORY) : KIND = struct
	datatype simplekind = 
		 Type
		 | Other of Theory.kind
	datatype kind = 
		 Simple of simplekind
		 | Arrow of simplekind * kind
	end

(* constructors *)
signature CONSTR = sig
    type kind
    type constr
end

functor Constr (structure Theory : THEORY structure Kind : KIND) : CONSTR = struct
	type kind = Kind.kind
	datatype constr = 
		 Var of var
	       | Arrow of constr * constr * constr
	       | Abs of kind * string * constr
	       | Unit
	       | Prod of constr * constr
	       | Sum of constr * constr
	       | App of constr * constr
	       | Uni of kind * string * constr
	       | Ex of kind * string * constr
	       | Recur of kind * string * constr
	       | Other of Theory.constr

end

(* expressions *)
functor Expr (structure Constr : CONSTR) = struct
	open Constr
	datatype expr =
		 Var of var
		 | Abs of constr * string * expr (* string is the variable name only for debug purpose *)
		 | App of expr * expr
		 | Fix of constr * string * expr
		 | Let of string * expr * expr
		 | Ascript of expr * constr
		 | AscriptTime of expr * constr
		 (* unit type *)
		 | TT
		 (* product type *)
		 | Pair of expr * expr
		 | Fst of expr
		 | Snd of expr
		 (* sum type *)
		 | Inl of constr * expr
		 | Inr of constr * expr
		 | Match of expr * expr * expr
		 (* universal *)
		 | Tabs of kind * string * expr
		 | Tapp of expr * constr
		 (* existential *)
		 | Pack of constr * constr * expr
		 | Unpack of expr * string * string * expr

end			       
	 
val _ = print "hello\n"
