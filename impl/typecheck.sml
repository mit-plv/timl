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
    type hkind
    type constr
    val T0 : constr
    val T1 : constr
    val Tadd : constr * constr -> constr
    val Tmax : constr * constr -> constr
end

functor MakeConstr (structure Theory : TIME_THEORY) = struct
(* simple kind without arrows *)
datatype kind = 
	 Type
	 | Other of Theory.kind
(* higher kinds with arrows *)
datatype hkind = 
	 Simple of kind
	 | Arrow of kind * hkind
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
	 | Recur of hkind * string * constr
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

exception Unimpl

fun lookup (x : var) (tctx : tcontext) : constr option = NONE

fun var_toString (x : var) : string = Int.toString x
fun expr_toString (e : expr) : string =
  case e of
      Var x => var_toString x
    | App (e1, e2) => "(" ^ expr_toString e1 ^ " " ^ expr_toString e2 ^ ")"
    | _ => raise Unimpl

fun constr_toString (c : constr) : string =
  case c of
      Arrow (c1, d, c2) => "(" ^ constr_toString c1 ^ " time " ^ constr_toString d ^ " -> " ^ constr_toString c2 ^ ")"
    | _ => raise Unimpl

fun a + b = Tadd (a, b)

fun subst (v : constr) (b : constr) : constr = raise Unimpl
						     
fun whnf (c : constr) : constr =
  case c of
      Constr.App (c1, c2) =>
      (case whnf c1 of
	   Constr.Abs (_, _, c1') => whnf (subst c2 c1')
	 | c1' => Constr.App (c1', c2))
    | _ => raise Unimpl 

fun vcgen_le (c : constr) (c' : constr) : (prop list) error = raise Unimpl
								    
fun vcgen_subtype (c : constr) (c' : constr) : (prop list) error =
  case (whnf c, whnf c') of
      (Arrow (c1, d, c2), Arrow (c1', d', c2')) =>
      (case vcgen_subtype c1' c1 of
	   OK vc1 =>
	   (case vcgen_le d d' of
		OK vcd =>
		(case vcgen_subtype c2 c2' of
		     OK vc2 => OK (vc1 @ vcd @ vc2)
		   | Error msg => Error msg)
	      | Error msg => Error msg)
	 | Error msg => Error msg)
   | _ => 
     Error "Unimplement"
								     
fun vcgen (kctx : kcontext) (tctx : tcontext) (e : expr) : (constr * constr * prop list) error =
  case e of
      Var x =>
      (case lookup x tctx of
      	   SOME t =>
	   OK (t, T0, [])
      	 | NONE => Error ("Unbound variable " ^ var_toString x))
    | App (e1, e2) =>
      (case vcgen kctx tctx e1 of
    	   OK (t1, d1, vc1) =>
    	   (case whnf t1 of
    		Arrow (t2, d, t) =>
    		(case vcgen kctx tctx e2 of
    		     OK (t2', d2, vc2) =>
    		     (case vcgen_subtype t2' t2 of
    			  OK vc3 => OK (t, d1 + d2 + T1 + d,  vc1 @ vc2 @ vc3)
			| Error msg => Error msg)
    		   | Error msg => Error msg)
    	      | t1' =>  Error ("Type of " ^ expr_toString e ^ " should have type pattern (_ time _ -> _) but is " ^ constr_toString t1'))
	 | Error msg  => Error msg)
    | _  => Error "Unimplemented"

val result = vcgen [] [] (Var 0)
val _ =
    case result of
	OK _ => print "OK\n"
      | Error msg => print ("Error: " ^ msg ^ "\n")
