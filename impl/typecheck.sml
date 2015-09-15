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

datatype 'a result =
	 OK of 'a
	 | Failed of string

(* use exception and cell to mimic the Error and Writer monads *)
local								    

    exception Fail of string

    fun runError m _ =
	OK (m ())
	handle
	Fail msg => Failed msg

    val acc = ref ([] : prop list)

    fun tell a = acc := !acc @ a

    fun runWriter m _ =
	(acc := []; let val r = m () in (r, !acc) end)

    fun time_le (c : constr) (c' : constr) = raise Unimpl

    fun subtyping (c : constr) (c' : constr) =
	case (whnf c, whnf c') of
	    (Arrow (c1, d, c2), Arrow (c1', d', c2')) =>
	    (subtyping c1' c1;
	     time_le d d';
	     subtyping c2 c2')
	  | _ => 
	    raise Unimpl

    fun typing (kctx : kcontext) (tctx : tcontext) (e : expr) : constr * constr =
	case e of
	    Var x =>
	    (case lookup x tctx of
      		 SOME t =>
		 (t, T0)
      	       | NONE => raise Fail ("Unbound variable " ^ var_toString x))
	  | App (e1, e2) =>
	    let val (t1, d1) = typing kctx tctx e1 
	    in
    		case whnf t1 of
    		    Arrow (t2, d, t) =>
    		    let val (t2', d2) = typing kctx tctx e2 
		    in
			subtyping t2' t2;
    			(t, d1 + d2 + T1 + d) 
		    end
    		  | t1' =>  raise Fail ("Type of " ^ expr_toString e ^ " should have type pattern (_ time _ -> _) but is " ^ constr_toString t1')
	    end
	  | _  => raise Unimpl

in								     

    fun vcgen (kctx : kcontext) (tctx : tcontext) (e : expr) : ((constr * constr) * prop list) result =
	runError (runWriter (fn _ => typing kctx tctx e)) ()

end

val result = vcgen [] [] (Var 0)
val _ =
    case result of
	OK _ => print "OK\n"
      | Failed msg => print ("Failed: " ^ msg ^ "\n")
