type var = int

signature THEORY = sig
    type kind
    type constr
    type prop
end

structure Theory : THEORY = struct
type kind = unit
type constr = unit
type prop = unit
end

signature TIME_THEORY = sig
    type kind
    type constr
    val Time : kind
end

functor MakeTimeTheory (structure Theory : THEORY) : TIME_THEORY = struct
datatype prop =
	 True
	 | False
	 | And of prop * prop
	 | Or of prop * prop
	 | TimeEq of Theory.constr * Theory.constr
	 | Other of Theory.prop
datatype kind =
	 Unit
	 | Prod of kind * kind
	 | Subset of kind * string * prop
	 | Time
	 | Other of Theory.kind
datatype constr =
	 TT
	 | Pair of constr * constr
end

(* constructors *)
signature CONSTR = sig
    type kind
    type constr
    val T0 : constr
    val T1 : constr
    val Tadd : constr * constr -> constr
    val Tmax : constr * constr -> constr
end

functor MakeConstr (structure Theory : TIME_THEORY) = struct
(* simple kind without arrows *)
	datatype skind = 
		 Type
		 | Other of Theory.kind
	datatype kind = 
		 Simple of skind
		 | Arrow of skind * kind
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
	       | T0
	       | T1
	       | Tadd of constr * constr
	       | Tmax of constr * constr
	       | Other of Theory.constr

end

(* expressions *)
functor MakeExpr (structure Constr : CONSTR) = struct
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

structure TimeTheory = MakeTimeTheory (structure Theory = Theory)
structure Constr = MakeConstr (structure Theory = TimeTheory)
structure Expr = MakeExpr (structure Constr = Constr)
open Theory
open TimeTheory
open Constr
open Expr

datatype 'a error =
	 OK of 'a
	 | Error of string

(* kinding context *)
type kcontext = (string * kind) list

(* typing context *)
type tcontext = (string * constr) list
fun lookup (x : var) (tctx : tcontext) : constr option = NONE

fun toString (x : var) : string = Int.toString x

fun vcgen (kctx : kcontext) (tctx : tcontext) (e : expr) : (constr * constr * prop list) error =
  case e of
      Var x =>
      (case lookup x tctx of
      	   SOME t =>
	   OK (t, T0, [])
      	 | NONE => Error ("Unbound variable " ^ toString x))
    | App _ =>
      Error "Umimplemented"
	    
    | _  => Error "Umimplemented"

val result = vcgen [] [] TT
val _ =
    case result of
	OK _ => print "OK\n"
      | Error msg => print ("Error " ^ msg ^ "\n")
