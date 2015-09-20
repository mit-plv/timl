type var = int

datatype 'a result =
	 OK of 'a
	 | Failed of string

exception Unimpl
exception Impossible of string

(* types *)
structure Type = struct

(* basic index sort *)
datatype bsort =
	 Time
	 | Bool
	 | BSUnit

datatype idx =
	 T0
	 | T1
	 | Tadd of idx * idx
	 | Tmax of idx * idx
	 | Tmin of idx * idx
	 | Btrue
	 | Bfalse
	 | TT

datatype prop =
	 True
	 | False
	 | And of prop * prop
	 | Or of prop * prop
	 | TimeEq of idx * idx
	 | TimeLe of idx * idx
	 | BoolEq of idx * idx

(* index sort *)
datatype sort =
	 Basic of bsort
	 | Subset of bsort * string * prop
					  
datatype ty = 
	 Var of var
	 | Arrow of ty * idx * ty
	 | Unit
	 | Prod of ty * ty
	 | Sum of ty * ty
	 | UniI of sort * string * ty
	 | ExI of sort * string * ty
	 | Uni of string * ty
	 (* the kind of Recur is sort => Type, to allow for change of index *)
	 | AppRecur of string * (string * sort) list * ty * idx list
	 (* the first operant of App can only be a recursive type*)
	 | AppVar of var * idx list

end

signature TYPE = sig
    type sort
    type idx
    type ty
end

(* expressions *)
functor MakeExpr (structure Type : TYPE) = struct
open Type
datatype expr =
	 Var of var
	 | App of expr * expr
	 | Abs of ty * string * expr (* string is the variable name only for debug purpose *)
	 (* convenience facilities *)
	 | Fix of ty * string * expr
	 | Let of expr * string * expr
	 | Ascription of expr * ty
	 | AscriptionTime of expr * idx
	 (* unit type *)
	 | TT
	 (* product type *)
	 | Pair of expr * expr
	 | Fst of expr
	 | Snd of expr
	 (* sum type *)
	 | Inl of ty * expr
	 | Inr of ty * expr
	 | Match of expr * string * expr * string * expr
	 (* universal *)
	 | Tabs of string * expr
	 | Tapp of expr * ty
	 (* universal index *)
	 | TabsI of sort * string * expr
	 | TappI of expr * idx
	 (* existential index *)
	 | Pack of ty * idx * expr
	 | Unpack of expr * ty * idx * string * string * expr
	 (* recursive type *)
	 | Fold of ty * expr
	 | Unfold of expr
end			       

structure Expr = MakeExpr (structure Type = Type)
open Type
open Expr

(* sorting context *)
type scontext = (string * sort) list
(* kinding context *)
datatype kind = 
	 Type
	 (* will only be used by recursive types in a restricted form *)
	 | KArrow of sort list
type kcontext = (string * kind) list
(* typing context *)
type tcontext = (string * ty) list

type context = scontext * kcontext * tcontext

fun add_sorting (name, s) sctx = (name, s) :: sctx
fun add_sorting_k (name, s) skctx = raise Unimpl
fun add_sortings_k ns skctx = raise Unimpl
fun add_sorting_kt (name, s) ctx = raise Unimpl
fun lookup_sort (x : var) (sctx : scontext) : sort option = NONE

fun add_kinding (name, k) kctx = (name, k) :: kctx
fun add_kinding_t (name, k) ktctx = raise Unimpl
fun add_kinding_s (name, k) (sctx, kctx) = (sctx, add_kinding (name, k) kctx)
fun lookup_kind (x : var) (kctx : kcontext) : kind option = NONE

fun add_typing (name, c) tctx = (name, c) :: tctx
fun add_typing_sk (name, c) (sctx, (kctx, tctx)) = (sctx, (kctx, add_typing (name, c) tctx))
fun lookup (x : var) (tctx : tcontext) : ty option = NONE

fun var_toString (x : var) : string = Int.toString x
fun bsort_toString (s : bsort) : string = raise Unimpl
fun sort_toString (s : sort) : string = raise Unimpl
fun idx_toString (i : idx) : string = raise Unimpl
fun kind_toString (k : kind) : string = raise Unimpl
fun type_toString (c : ty) : string =
  case c of
      Arrow (c1, d, c2) => "(" ^ type_toString c1 ^ " time " ^ idx_toString d ^ " -> " ^ type_toString c2 ^ ")"
    | _ => raise Unimpl

fun expr_toString (e : expr) : string =
  case e of
      Var x => var_toString x
    | App (e1, e2) => "(" ^ expr_toString e1 ^ " " ^ expr_toString e2 ^ ")"
    | _ => raise Unimpl

val STime = Basic Time
val SBool = Basic Bool
val SUnit = Basic BSUnit
		  
fun a + b = Tadd (a, b)
infix 3 $
fun a $ b = Tmax (a, b)

fun subst (v : ty) (b : ty) : ty = raise Unimpl
fun subst_i_t (v : idx) (b : ty) : ty = raise Unimpl
fun subst_i_p (v : idx) (b : prop) : prop = raise Unimpl
						  
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

    fun check_length (a, b) =
      if length a = length b then
	  ()
      else
	  raise Fail "List length mismatch"
		
    fun is_le (arg : scontext * idx * idx) = raise Unimpl
    fun is_eq (arg : scontext * idx * idx * sort) = raise Unimpl
    fun is_eqs (ctx, i, i', s) =
      (check_length (i, i');
       check_length (i, s);
       app (fn ((i, i'), s) => is_eq (ctx, i, i', s)) (ListPair.zip ((ListPair.zip (i, i')), s)))
    fun is_iff (arg : scontext * prop * prop) = raise Unimpl
    fun is_imply (arg : scontext * prop * prop) = raise Unimpl
    fun is_true (arg : scontext * prop) = raise Unimpl

    (*       	| Type.Fst s' => *)
    (*   (case flatten s' of *)
    (*        SProd (s1, s2) => s1 *)
    (*     | s'' => Type.Fst s'') *)
    (* | Type.Snd s' => *)
    (*   (case flatten s' of *)
    (*        SProd (s1, s2) => s2 *)
    (*      | s'' => Type.Snd s'') *)

    fun is_eqvbsort_b s s' =
      case (s, s') of
	  (Time, Time) => true
	| (Bool, Bool) => true
	| (BSUnit, BSUnit) => true
	| _ => false

    fun is_eqvbsort (s, s') =
      if is_eqvbsort_b s s' then
	  ()
      else
	  raise Fail ("Basic sort mismatch: " ^ bsort_toString s ^ " and " ^ bsort_toString s')
		
    fun is_eqvsort (ctx, s, s') =
      case (s, s') of
	  (Basic s1, Basic s1') =>
	  is_eqvbsort (s1, s1')
	| (Subset (s1, name, p), Subset (s1', _, p')) =>
	  (is_eqvbsort (s1, s1');
	   is_iff (add_sorting (name, Basic s1) ctx, p, p'))
	| (Subset (s1, name, p), Basic s1') =>
	  (is_eqvbsort (s1, s1');
	   is_true (add_sorting (name, Basic s1) ctx, p))
	| (Basic s1, Subset (s1', name, p)) =>
	  (is_eqvbsort (s1, s1');
	   is_true (add_sorting (name, Basic s1) ctx, p))

    fun is_eqvsorts (ctx, s, s') =
      (check_length (s, s');
       ListPair.app (fn (s, s') => is_eqvsort (ctx, s, s')) (s, s'))
		    
    fun sort_mismatch i expect have =  "Sort mismatch for " ^ idx_toString i ^ ": expect " ^ expect ^ " have " ^ sort_toString have

    fun is_wfsort (ctx : scontext, s : sort) =
      case s of
	  Basic _ => ()
	| Subset (s, name, p) =>
	  is_wfprop (add_sorting (name, Basic s) ctx, p)

    and is_wfprop (ctx : scontext, p : prop) =
	case p of
	    True => ()
	  | False => ()
	  | And (p1, p2) =>
	    (is_wfprop (ctx, p1);
	     is_wfprop (ctx, p2))
	  | Or (p1, p2) =>
	    (is_wfprop (ctx, p1);
	     is_wfprop (ctx, p2))
	  | TimeEq (d1, d2) =>
	    (check_sort (ctx, d1, STime);
	     check_sort (ctx, d2, STime))
	  | TimeLe (d1, d2) =>
	    (check_sort (ctx, d1, STime);
	     check_sort (ctx, d2, STime))
	  | BoolEq (d1, d2) =>
	    (check_sort (ctx, d1, SBool);
	     check_sort (ctx, d2, SBool))

    and check_sort (ctx, i, s) : unit =
	let val s' = get_sort (ctx, i) in
	    case (s', s) of
		(Subset (s1', _, p'), Subset (s1, _, p)) =>
		(is_eqvbsort (s1', s1);
		 is_imply (ctx, subst_i_p i p', subst_i_p i p))
	      | (Basic s1', Subset (s1, _, p)) =>
		(is_eqvbsort (s1', s1);
		 is_true (ctx, subst_i_p i p))
	      | (Subset (s1', _, _), Basic s1) => 
		is_eqvbsort (s1', s1)
	      | (Basic s1', Basic s1) => 
		is_eqvbsort (s1', s1)
	end

    and get_sort (ctx, i) =
	case i of
      	    T0 => STime
	  | T1 => STime
	  | Tadd (d1, d2) => 
	    (check_sort (ctx, d1, STime);
	     check_sort (ctx, d2, STime);
	     STime)
	  | Tmax (d1, d2) => 
	    (check_sort (ctx, d1, STime);
	     check_sort (ctx, d2, STime);
	     STime)
	  | Tmin (d1, d2) => 
	    (check_sort (ctx, d1, STime);
	     check_sort (ctx, d2, STime);
	     STime)
	  | Btrue => SBool
	  | Bfalse => SBool
	  | Type.TT => SUnit

    fun is_wfsorts (ctx, s) = List.app (fn s => is_wfsort (ctx, s)) s
    fun check_sorts (ctx, i, s) =
      (check_length (i, s);
      ListPair.app (fn (i, s) => check_sort (ctx, i, s)) (i, s))

    (* k => Type *)
    fun recur_kind k = KArrow k

    fun kind_mismatch c expect have =  "Kind mismatch for " ^ type_toString c ^ ": expect " ^ expect ^ " have " ^ kind_toString have

    fun is_wftype (ctx as (sctx : scontext, kctx : kcontext), c : ty) : unit = 
      case c of
	  Type.Var a =>
	  (case lookup_kind a kctx of
      	       SOME k =>
	       (case k of
		    Type => ()
		  | KArrow _ => raise Fail (kind_mismatch c "Type" k))
      	     | NONE => raise Fail ("Unbound type variable " ^ var_toString a))
	| Arrow (c1, d, c2) => 
	  (is_wftype (ctx, c1);
	   check_sort (sctx, d, STime);
	   is_wftype (ctx, c2))
	| Unit => ()
	| Prod (c1, c2) => 
	  (is_wftype (ctx, c1);
	   is_wftype (ctx, c2))
	| Sum (c1, c2) => 
	  (is_wftype (ctx, c1);
	   is_wftype (ctx, c2))
	| Uni (name, c) => 
	  is_wftype (add_kinding_s (name, Type) ctx, c)
	| UniI (s, name, c) => 
	  (is_wfsort (sctx, s);
	   is_wftype (add_sorting_k (name, s) ctx, c))
	| ExI (s, name, c) => 
	  (is_wfsort (sctx, s);
	   is_wftype (add_sorting_k (name, s) ctx, c))
	| AppRecur (nameself, ns, t, i) =>
	  let val s = List.map #2 ns in
	      is_wfsorts (sctx, s);
	      is_wftype (add_sortings_k ns (add_kinding_s (nameself, recur_kind s) ctx), t);
	      check_sorts (sctx, i, s)
	  end
	| AppVar (a, i) => 
	  (case lookup_kind a kctx of
      	       SOME k =>
	       (case k of
		    KArrow s => 
		    check_sorts (sctx, i, s)
		  | _ => raise Fail (kind_mismatch c "(_ => _)" k))
      	     | NONE => raise Fail ("Unbound type variable " ^ var_toString a))

    fun not_subtype c c' = type_toString c ^ " is not subtype of " ^ type_toString c'

    (* is_subtype assumes that the types are already checked against the given kind, so it doesn't need to worry about their well-formedness *)
    fun is_subtype (ctx as (sctx : scontext, kctx : kcontext), c : ty, c' : ty) =
      case (c, c') of
	  (Arrow (c1, d, c2), Arrow (c1', d', c2')) =>
	  (is_subtype (ctx, c1', c1);
	   is_le (sctx, d, d');
	   is_subtype (ctx, c2, c2'))
	| (Type.Var a, Type.Var a') => 
	  if a = a' then
	      ()
	  else
	      raise Fail (not_subtype c c')
	| (Unit, Unit) => ()
	| (Prod (c1, c2), Prod (c1', c2')) =>
	  (is_subtype (ctx, c1, c1');
	   is_subtype (ctx, c2, c2'))
	| (Sum (c1, c2), Sum (c1', c2')) => 
	  (is_subtype (ctx, c1, c1');
	   is_subtype (ctx, c2, c2'))
	| (Uni (name, c), Uni (_, c')) => 
	  is_subtype (add_kinding_s (name, Type) ctx, c, c')
	| (UniI (s, name, c), UniI (s', _, c')) => 
	  (is_eqvsort (sctx, s, s');
	   is_subtype (add_sorting_k (name, s) ctx, c, c'))
	| (ExI (s, name, c), ExI (s', _, c')) => 
	  (is_eqvsort (sctx, s, s');
	   is_subtype (add_sorting_k (name, s) ctx, c, c'))
	(* currently don't support subtyping for recursive types, so they must be equivalent *)
	| (AppRecur (nameself, ns, t, i), AppRecur (_, ns', t', i')) => 
	  let val s = List.map #2 ns
	      val s' = List.map #2 ns'
	      val () = is_eqvsorts (sctx, s, s')
	      val () = is_eqs (sctx, i, i', s)
	      val ctx' = add_sortings_k ns (add_kinding_s (nameself, recur_kind s) ctx) in
	      is_eqvtype (ctx', t, t')
	  end
	| (AppVar (a, i), AppVar (a', i')) => 
	  if a = a' then
	      case lookup_kind a kctx of
      		  SOME k =>
		  (case k of
		       KArrow s => 
		       is_eqs (sctx, i, i', s)
		     | Type =>
		       raise Impossible "is_subtype: x in (x c) should have an arrow kind")
      		| NONE => raise Fail ("Unbound type variable " ^ var_toString a)
	  else
	      raise Fail (not_subtype c c')
	| _ => raise Fail (not_subtype c c')

    and is_eqvtype (kctx, c, c') =
	(is_subtype (kctx, c, c');
	 is_subtype (kctx, c', c))

    fun no_join c c' = "Cannot find a join (minimal supertype) of " ^ type_toString c ^ " and " ^ type_toString c'
    fun no_meet c c' = "Cannot find a meet (maximal subtype) of " ^ type_toString c ^ " and " ^ type_toString c'

    (* c and c' are already checked for wellformedness *)
    fun join (ctx as (sctx : scontext, kctx : kcontext), c : ty, c' : ty) : ty = 
      case (c, c') of
	  (Arrow (c1, d, c2), Arrow (c1', d', c2')) => 
	  let val c1'' = meet (ctx, c1, c1') 
	      val d'' = d $ d' 
	      val c2'' = join (ctx, c2, c2') in
	      Arrow (c1'', d'', c2'')
	  end
	| (Type.Var a, Type.Var a') => 
	  if a = a' then
	      c
	  else
	      raise Fail (no_join c c')
	| (Unit, Unit) => Unit
	| (Prod (c1, c2), Prod (c1', c2')) => 
	  let val c1'' = join (ctx, c1, c1') 
	      val c2'' = join (ctx, c2, c2') in
	      Prod (c1'', c2'')
	  end
	| (Sum (c1, c2), Sum (c1', c2')) => 
	  let val c1'' = join (ctx, c1, c1') 
	      val c2'' = join (ctx, c2, c2') in
	      Sum (c1'', c2'')
	  end
	| (Uni (name, t), Uni (_, t')) => 
	  let val t'' = join (add_kinding_s (name, Type) ctx, t, t') in
	      Uni (name, t'')
	  end
	| (UniI (s, name, t), UniI (s', _, t')) => 
	  let val () = is_eqvsort (sctx, s, s')
	      val t'' = join (add_sorting_k (name, s) ctx, t, t') in
	      UniI (s, name, t'')
	  end
	| (ExI (s, name, t), ExI (s', _, t')) => 
	  let val () = is_eqvsort (#1 ctx, s, s')
	      val t'' = join (add_sorting_k (name, s) ctx, t, t') in
	      ExI (s, name, t'')
	  end
	(* currently don't support join for recursive types, so they must be equivalent *)
	| (AppRecur _, AppRecur _) => 
	  (is_eqvtype (ctx, c, c');
	   c)
	| (AppVar _, AppVar _) => 
	  (is_eqvtype (ctx, c, c');
	   c)
	| _ => raise Fail (no_join c c')

    and meet (ctx as (sctx : scontext, kctx : kcontext), c : ty, c' : ty) : ty = 
	case (c, c') of
	    (Arrow (c1, d, c2), Arrow (c1', d', c2')) => 
	    let val c1'' = join (ctx, c1, c1') 
		val d'' = Tmin (d, d')
		val c2'' = meet (ctx, c2, c2') in
		Arrow (c1'', d'', c2'')
	    end
	  | (Type.Var a, Type.Var a') => 
	    if a = a' then
		c
	    else
		raise Fail (no_meet c c')
	  | (Unit, Unit) => Unit
	  | (Prod (c1, c2), Prod (c1', c2')) => 
	    let val c1'' = meet (ctx, c1, c1') 
		val c2'' = meet (ctx, c2, c2') in
		Prod (c1'', c2'')
	    end
	  | (Sum (c1, c2), Sum (c1', c2')) => 
	    let val c1'' = meet (ctx, c1, c1') 
		val c2'' = meet (ctx, c2, c2') in
		Sum (c1'', c2'')
	    end
	  | (Uni (name, t), Uni (_, t')) => 
	    let val t'' = meet (add_kinding_s (name, Type) ctx, t, t') in
		Uni (name, t'')
	    end
	  | (UniI (s, name, t), UniI (s', _, t')) => 
	    let val () = is_eqvsort (sctx, s, s')
		val t'' = meet (add_sorting_k (name, s) ctx, t, t') in
		UniI (s, name, t'')
	    end
	  | (ExI (s, name, t), ExI (s', _, t')) => 
	    let val () = is_eqvsort (#1 ctx, s, s')
		val t'' = meet (add_sorting_k (name, s) ctx, t, t') in
		ExI (s, name, t'')
	    end
	  (* currently don't support meet for recursive types, so they must be equivalent *)
	  | (AppRecur _, AppRecur _) => 
	    (is_eqvtype (ctx, c, c');
	     c)
	  | (AppVar _, AppVar _) => 
	    (is_eqvtype (ctx, c, c');
	     c)
	  | _ => raise Fail (no_meet c c')

    fun is_value (e : expr) : bool = raise Unimpl

    fun mismatch e expect have =  "Type mismatch for " ^ expr_toString e ^ ": expect " ^ expect ^ " have " ^ type_toString have
    fun mismatch_anno expect have =  "Type annotation mismatch: expect " ^ expect ^ " have " ^ type_toString have

    fun check_fix_body e =
      case e of
	  Tabs (_, e') => check_fix_body e'
	| Abs _ => ()
	| _ => raise Fail "The body of fixpoint must have the form (fn [(_ :: _) ... (_ :: _)] (_ : _) => _)"
    fun unfold t =
      raise Unimpl
    (* (subst t1 (subst_i_t i t2)) *)
	    
    fun get_type (ctx as (sctx : scontext, ktctx as (kctx : kcontext, tctx : tcontext)), e : expr) : ty * idx =
      let val skctx = (sctx, kctx) in
	  case e of
	      Var x =>
	      (case lookup x tctx of
      		   SOME t => (t, T0)
      		 | NONE => raise Fail ("Unbound variable " ^ var_toString x))
	    | App (e1, e2) =>
	      let val (t1, d1) = get_type (ctx, e1) in
    		  case t1 of
    		      Arrow (t2, d, t) =>
    		      let val (t2', d2) = get_type (ctx, e2) 
			  val () = is_subtype (skctx, t2', t2) in
    			  (t, d1 + d2 + T1 + d) 
		      end
    		    | t1' =>  raise Fail (mismatch e1 "(_ time _ -> _)" t1')
	      end
	    | Abs (t, varname, e) => 
	      let val () = is_wftype (skctx, t)
		  val (t1, d) = get_type (add_typing_sk (varname, t) ctx, e) in
		  (Arrow (t, d, t1), T0)
	      end
	    | TT => (Unit, T0)
	    | Pair (e1, e2) => 
	      let val (t1, d1) = get_type (ctx, e1) 
		  val (t2, d2) = get_type (ctx, e2) in
		  (Prod (t1, t2), d1 + d2)
	      end
	    | Fst e => 
	      let val (t, d) = get_type (ctx, e) in 
		  case t of
		      Prod (t1, t2) => (t1, d + T1)
		    | t' => raise Fail (mismatch e "(_ * _)" t')
	      end
	    | Snd e => 
	      let val (t, d) = get_type (ctx, e) in 
		  case t of
		      Prod (t1, t2) => (t2, d + T1)
		    | t' => raise Fail (mismatch e "(_ * _)" t')
	      end
	    | Inl (t2, e) => 
	      let val (t1, d) = get_type (ctx, e)
		  val () = is_wftype (skctx, t2) in
		  (Sum (t1, t2), d)
	      end
	    | Inr (t1, e) => 
	      let val (t2, d) = get_type (ctx, e)
		  val () = is_wftype (skctx, t1) in
		  (Sum (t1, t2), d)
	      end
	    | Match (e, name1, e1, name2, e2) => 
	      let val (t, d) = get_type (ctx, e) in
		  case t of
		      Sum (t1, t2) => 
		      let val (tr1, d1) = get_type (add_typing_sk (name1, t1) ctx, e1)
			  val (tr2, d2) = get_type (add_typing_sk (name2, t2) ctx, e2)
			  val tr = join (skctx, tr1, tr2) in
			  (tr, d + T1 + d1 $ d2)
		      end
		    | t' => raise Fail (mismatch e "(_ + _)" t')
	      end
	    | Tabs (name, e) => 
	      if is_value e then
		  let val (t, _) = get_type ((sctx, add_kinding_t (name, Type) ktctx), e) in
		      (Uni (name, t), T0)
		  end 
	      else
		  raise Fail ("The body of a universal abstraction must be a value")
	    | Tapp (e, c) =>
	      let val (t, d) = get_type (ctx, e) in
		  case t of
		      Uni (_, t1) => 
		      let val () = is_wftype (skctx, c) in
			  (subst c t1, d + T1)
		      end
		    | t' => raise Fail (mismatch e "(forall _ : _, _)" t')
	      end
	    | TabsI (s, name, e) => 
	      if is_value e then
		  let val () = is_wfsort (sctx, s)
		      val (t, _) = get_type ((add_sorting_kt (name, s) ctx), e) in
		      (UniI (s, name, t), T0)
		  end 
	      else
		  raise Fail ("The body of a universal abstraction must be a value")
	    | TappI (e, i) =>
	      let val (t, d) = get_type (ctx, e) in
		  case t of
		      UniI (s, _, t1) => 
		      let val () = check_sort (sctx, i, s) in
			  (subst_i_t i t1, d + T1)
		      end
		    | t' => raise Fail (mismatch e "(forallI _ : _, _)" t')
	      end
	    | Fold (t, e) => 
	      (case t of
		   AppRecur t1 =>
		   let val () = is_wftype (skctx, t)
		       val (t', d) = get_type (ctx, e)
		       val () = is_subtype (skctx, t', unfold t1) in
		       (t, d)
		   end
		 | t' => raise Fail (mismatch_anno "((recur (_ :: _) (_ : _), _) _)" t'))
	    | Unfold e =>
	      let val (t, d) = get_type (ctx, e) in
		  case t of
	      	      AppRecur t1 =>
		      (unfold t1, d + T1)
		    | t' => raise Fail (mismatch e "((recur (_ :: _) (_ : _), _) _)" t')
	      end
	    | Pack (t, i, e) =>
	      (case t of
		   ExI (s, _, t1) =>
		   let val () = is_wftype (skctx, t)
		       val () = check_sort (sctx, i, s)
		       val (t2, d) = get_type (ctx, e)
		       val () = is_subtype (skctx, t2, (subst_i_t i t1)) in
		       (t, d)
		   end
		 | t' => raise Fail (mismatch_anno "(ex _ : _, _)" t'))
	    | Unpack (e1, t, d, idx_var, expr_var, e2) => 
	      let val () = is_wftype (skctx, t)
		  val () = check_sort (sctx, d, STime)
		  val (t1, d1) = get_type (ctx, e1) in
		  case t1 of
		      ExI (s, _, t1') => 
		      let val ctx' = add_typing_sk (expr_var, t1') (add_sorting_kt (idx_var, s) ctx)
			  val (t2, d2) = get_type (ctx', e2)
			  val () = is_subtype (skctx, t2, t)
			  val () = is_le (sctx, d2, d) in
			  (t, d1 + T1 + d)
		      end
		    | t1' => raise Fail (mismatch e1 "(ex _ : _, _)" t1')
	      end
	    | Let (e1, name, e2) => 
	      let val (t1, d1) = get_type (ctx, e1)
		  val (t2, d2) = get_type (add_typing_sk (name, t1) ctx, e2) in
		  (t2, d1 + T1 + d2)
	      end
	    | Fix (t, name, e) => 
	      let val () = check_fix_body e
		  val () = is_wftype (skctx, t)
		  val (t1, _) = get_type (add_typing_sk (name, t) ctx, e)
		  val () = is_subtype (skctx, t1, t) in
		  (t, T0)
	      end
	    | Ascription (e, t) => 
	      let val () = is_wftype (skctx, t)
		  val (t1, d) = get_type (ctx, e)
		  val () = is_subtype (skctx, t1, t) in
		  (t, d)
	      end
	    | AscriptionTime (e, d) => 
	      let val () = check_sort (sctx, d, STime)
		  val (t, d1) = get_type (ctx, e)
		  val () = is_le (sctx, d1, d) in
		  (t, d)
	      end
      end
in								     

fun vcgen (sctx : scontext) (kctx : kcontext) (tctx : tcontext) (e : expr) : ((ty * idx) * prop list) result =
  runError (runWriter (fn () => get_type ((sctx, (kctx, tctx)), e))) ()
	   
end

val result = vcgen [] [] [] (Var 0)
val _ =
    case result of
	OK ((t, d), vc) => print ("OK: type=" ^ type_toString t ^ " d=" ^ idx_toString d)
      | Failed msg => print ("Failed: " ^ msg ^ "\n")
