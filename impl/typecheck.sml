type var = int

datatype 'a result =
	 OK of 'a
	 | Failed of string

exception Unimpl
exception Impossible of string

(* constructors *)
structure Constr = struct

datatype idx =
	 T0
	 | T1
	 | Tadd of idx * idx
	 | Tmax of idx * idx
	 | Tmin of idx * idx
	 | Btrue
	 | Bfalse
	 | TT
	 | Pair of idx * idx
	 | Fst of idx
	 | Snd of idx

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
	 Time
	 | Bool
	 | SUnit
	 | SProd of sort * sort
	 | Subset of sort * string * prop
					 

datatype kind = 
	 Type
	 (* will only be used by recursive types in a restricted form *)
	 | KArrow of sort

datatype constr = 
	 Var of var
	 | Arrow of constr * idx * constr
	 | Unit
	 | Prod of constr * constr
	 | Sum of constr * constr
	 | UniI of sort * string * constr
	 | ExI of sort * string * constr
	 | Uni of string * constr
	 (* the kind of Recur is sort => Type, to allow for change of index *)
	 | Recur of string * sort * string * constr
	 (* the first operant of App can only be a recursive type*)
	 | AppI of constr * idx

end

signature CONSTR = sig
    type sort
    type idx
    type constr
end

(* expressions *)
functor MakeExpr (structure Constr : CONSTR) = struct
open Constr
datatype expr =
	 Var of var
	 | App of expr * expr
	 | Abs of constr * string * expr (* string is the variable name only for debug purpose *)
	 (* convenience facilities *)
	 | Fix of constr * string * expr
	 | Let of expr * string * expr
	 | Ascription of expr * constr
	 | AscriptionTime of expr * idx
	 (* unit type *)
	 | TT
	 (* product type *)
	 | Pair of expr * expr
	 | Fst of expr
	 | Snd of expr
	 (* sum type *)
	 | Inl of constr * expr
	 | Inr of constr * expr
	 | Match of expr * string * expr * string * expr
	 (* universal *)
	 | Tabs of string * expr
	 | Tapp of expr * constr
	 (* universal index *)
	 | TabsI of sort * string * expr
	 | TappI of expr * idx
	 (* existential index *)
	 | Pack of constr * idx * expr
	 | Unpack of expr * constr * idx * string * string * expr
	 (* recursive type *)
	 | Fold of constr * expr
	 | Unfold of expr
end			       

structure Expr = MakeExpr (structure Constr = Constr)
open Constr
open Expr

(* sorting context *)
type scontext = (string * sort) list
(* kinding context *)
type kcontext = (string * kind) list
(* typing context *)
type tcontext = (string * constr) list

type context = scontext * kcontext * tcontext

fun add_sorting (name, s) sctx = (name, s) :: sctx
fun add_sorting_k (name, s) skctx = raise Unimpl
fun add_sorting_kt (name, s) ctx = raise Unimpl
fun lookup_sort (x : var) (sctx : scontext) : sort option = NONE

fun add_kinding (name, k) kctx = (name, k) :: kctx
fun add_kinding_t (name, k) ktctx = raise Unimpl
fun add_kinding_s (name, k) (sctx, kctx) = (sctx, add_kinding (name, k) kctx)
fun lookup_kind (x : var) (kctx : kcontext) : kind option = NONE

fun add_typing (name, c) tctx = (name, c) :: tctx
fun add_typing_sk (name, c) (sctx, (kctx, tctx)) = (sctx, (kctx, add_typing (name, c) tctx))
fun lookup (x : var) (tctx : tcontext) : constr option = NONE

fun var_toString (x : var) : string = Int.toString x
fun sort_toString (s : sort) : string = raise Unimpl
fun idx_toString (i : idx) : string = raise Unimpl
fun kind_toString (k : kind) : string = raise Unimpl
fun constr_toString (c : constr) : string =
  case c of
      Arrow (c1, d, c2) => "(" ^ constr_toString c1 ^ " time " ^ idx_toString d ^ " -> " ^ constr_toString c2 ^ ")"
    | _ => raise Unimpl

fun expr_toString (e : expr) : string =
  case e of
      Var x => var_toString x
    | App (e1, e2) => "(" ^ expr_toString e1 ^ " " ^ expr_toString e2 ^ ")"
    | _ => raise Unimpl

fun a + b = Tadd (a, b)
infix 3 $
fun a $ b = Tmax (a, b)

fun subst (v : constr) (b : constr) : constr = raise Unimpl
fun subst_idx (v : idx) (b : constr) : constr = raise Unimpl
						     
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

    fun is_le (arg : scontext * idx * idx) = raise Unimpl
    fun is_eq (arg : scontext * idx * idx * sort) = raise Unimpl
    fun is_iff (arg : scontext * prop * prop) = raise Unimpl

    fun is_eqvsort (ctx, s, s') =
      case (s, s') of
	  (Time, Time) => ()
	| (Bool, Bool) => ()
	| (SUnit, SUnit) => ()
	| (SProd (s1, s2), SProd (s1', s2')) =>
	  (is_eqvsort (ctx, s1, s1');
	   is_eqvsort (ctx, s2, s2'))
	| (Subset (s1, name, p), Subset (s1', _, p')) =>
	  raise Unimpl
	  (* (is_eqvsort (ctx, s1, s1'); *)
	  (*  is_iff (add_kinding (name, NonType k1) kctx, p, p')) *)
	| _ => raise Fail ("Sort mismatch: " ^ sort_toString s ^ " and " ^ sort_toString s')

    (* k => Type *)
    fun recur_kind k = KArrow k

    fun sort_mismatch i expect have =  "Sort mismatch for " ^ idx_toString i ^ ": expect " ^ expect ^ " have " ^ sort_toString have

    fun kind_mismatch c expect have =  "Kind mismatch for " ^ constr_toString c ^ ": expect " ^ expect ^ " have " ^ kind_toString have

    fun is_wfsort (ctx : scontext, k : sort) =
	case k of
	    Time => ()
	  | Bool => ()
	  | SUnit => ()
	  | SProd (s1, s2) =>
	    (is_wfsort (ctx, s1);
	     is_wfsort (ctx, s2))
	  | Subset (s, name, p) =>
	    (is_wfsort (ctx, s);
	     is_wfprop (add_sorting (name, s) ctx, p))

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
	    (check_sort (ctx, d1, Time);
	     check_sort (ctx, d2, Time))
	  | TimeLe (d1, d2) =>
	    (check_sort (ctx, d1, Time);
	     check_sort (ctx, d2, Time))
	  | BoolEq (d1, d2) =>
	    (check_sort (ctx, d1, Bool);
	     check_sort (ctx, d2, Bool))

    and get_sort (ctx, i) =
      case i of
      	  T0 => Time
	| T1 => Time
	| Tadd (d1, d2) => 
	  (check_sort (ctx, d1, Time);
	   check_sort (ctx, d2, Time);
	   Time)
	| Tmax (d1, d2) => 
	  (check_sort (ctx, d1, Time);
	   check_sort (ctx, d2, Time);
	   Time)
	| Tmin (d1, d2) => 
	  (check_sort (ctx, d1, Time);
	   check_sort (ctx, d2, Time);
	   Time)
	| Btrue => Bool
	| Bfalse => Bool
	| Constr.TT => SUnit
	| Constr.Pair (i1, i2) =>
	  SProd (get_sort (ctx, i1), get_sort (ctx, i2))
	| Constr.Fst i1 =>
	  let val s = get_sort (ctx, i1) in
	      case s of
		  SProd (s1, s2) => s1
		| _ => raise Fail (sort_mismatch i1 "(_ * _)" s)
	  end
	| Constr.Snd i1 =>
	  let val s = get_sort (ctx, i1) in
	      case s of
		  SProd (s1, s2) => s2
		| _ => raise Fail (sort_mismatch i1 "(_ * _)" s)
	  end

    and check_sort (ctx, i, s) : unit =
	let val s' = get_sort (ctx, i) in
	    raise Unimpl
	end

    fun is_eqvkind (ctx, k, k') =
      case (k, k') of
	  (Type, Type) => ()
	| (KArrow s, KArrow s') =>
	  is_eqvsort (ctx, s, s')
	| _ => raise Fail ("Kind mismatch: " ^ kind_toString k ^ " and " ^ kind_toString k')
		     
    fun get_kind (ctx as (sctx : scontext, kctx : kcontext), c : constr) : kind = 
	case c of
	    Constr.Var a =>
	    (case lookup_kind a kctx of
      		 SOME k => k
      	       | NONE => raise Fail ("Unbound type variable " ^ var_toString a))
	  | Arrow (c1, d, c2) => 
	    (check_kind (ctx, c1, Type);
	     check_sort (sctx, d, Time);
	     check_kind (ctx, c2, Type);
	     Type)
	  | Unit => Type
	  | Prod (c1, c2) => 
	    (check_kind (ctx, c1, Type);
	     check_kind (ctx, c2, Type);
	     Type)
	  | Sum (c1, c2) => 
	    (check_kind (ctx, c1, Type);
	     check_kind (ctx, c2, Type);
	     Type)
	  | Uni (name, c) => 
	    (check_kind (add_kinding_s (name, Type) ctx, c, Type);
	     Type)
	  | UniI (s, name, c) => 
	    (is_wfsort (sctx, s);
	     check_kind (add_sorting_k (name, s) ctx, c, Type);
	     Type)
	  | ExI (s, name, c) => 
	    (is_wfsort (sctx, s);
	     check_kind (add_sorting_k (name, s) ctx, c, Type);
	     Type)
	  | Recur (nameself, s, namearg, t) =>
	    (is_wfsort (sctx, s);
	     check_kind (add_sorting_k (namearg, s) (add_kinding_s (nameself, recur_kind s) ctx), t, Type);
	     recur_kind s)
	  | Constr.AppI (c1, i) => 
	    let val k1 = get_kind (ctx, c1) in
		case k1 of
		    KArrow s => 
		    (check_sort (sctx, i, s);
		     Type)
		  | _ => raise Fail (kind_mismatch c1 "(_ => _)" k1)
	    end

    and check_kind (ctx, c : constr, k : kind) : unit = 
	is_eqvkind (#1 ctx, get_kind (ctx, c), k)

    local
	fun not_subtype c c' = constr_toString c ^ " is not subtype of " ^ constr_toString c'
	(* is_subconstr assumes that the constructors are already checked against the given kind, so it doesn't need to worry about their well-formedness *)
	fun is_subconstr (ctx as (sctx : scontext, kctx : kcontext), c : constr, c' : constr, k : kind) =
	  case k of
	      Type =>
	      (case (c, c') of
		   (Arrow (c1, d, c2), Arrow (c1', d', c2')) =>
		   (is_subconstr (ctx, c1', c1, Type);
		    is_le (sctx, d, d');
		    is_subconstr (ctx, c2, c2', Type))
		 | (Constr.Var a, Constr.Var a') => 
		   if a = a' then
		       ()
		   else
		       raise Fail (not_subtype c c')
		 | (Unit, Unit) => ()
		 | (Prod (c1, c2), Prod (c1', c2')) =>
		   (is_subconstr (ctx, c1, c1', Type);
		    is_subconstr (ctx, c2, c2', Type))
		 | (Sum (c1, c2), Sum (c1', c2')) => 
		   (is_subconstr (ctx, c1, c1', Type);
		    is_subconstr (ctx, c2, c2', Type))
		 | (Uni (name, c), Uni (_, c')) => 
		   is_subconstr (add_kinding_s (name, Type) ctx, c, c', Type)
		 | (UniI (s, name, c), UniI (s', _, c')) => 
		   (is_eqvsort (sctx, s, s');
		    is_subconstr (add_sorting_k (name, s) ctx, c, c', Type))
		 | (ExI (s, name, c), ExI (s', _, c')) => 
		   (is_eqvsort (sctx, s, s');
		    is_subconstr (add_sorting_k (name, s) ctx, c, c', Type))
		 (* currently don't support subtyping for recursive types, so they must be equivalent *)
		 | (Constr.AppI (Recur (nameself, s, namearg, t), i), Constr.AppI (Recur (_, s', _, t'), i')) => 
		   let val () = is_eqvsort (sctx, s, s')
		       val () = is_eq (sctx, i, i', s)
		       val ctx' = add_sorting_k (namearg, s) (add_kinding_s (nameself, recur_kind s) ctx) in
		       is_eqvconstr (ctx', t, t', Type)
		   end
		 | (Constr.AppI (c1 as Constr.Var a, i), Constr.AppI (Constr.Var a', i')) => 
		   if a = a' then
		       let val k = get_kind (ctx, c1) in
			   case k of
			       KArrow s => 
			       is_eq (sctx, i, i', s)
			     | _ => raise Impossible "is_subconstr: x in (x c) should have an arrow kind"
		       end
		   else
		       raise Fail (not_subtype c c')
		 | _ => raise Fail (not_subtype c c'))
	    | KArrow _ => raise Impossible "is_subconstr: should never test subconstr in higher-order kinds"

	and is_eqvconstr (kctx, c, c', k) =
	    (is_subconstr (kctx, c, c', k);
	     is_subconstr (kctx, c', c, k))

    in

    fun is_subtype (kctx, t, t') = is_subconstr (kctx, t, t', Type)

    fun no_join c c' = "Cannot find a join (minimal supertype) of " ^ constr_toString c ^ " and " ^ constr_toString c'
    fun no_meet c c' = "Cannot find a meet (maximal subtype) of " ^ constr_toString c ^ " and " ^ constr_toString c'

    (* c and c' are already checked against k *)
    fun join (ctx as (sctx : scontext, kctx : kcontext), c : constr, c' : constr, k : kind) : constr = 
      case k of
	  Type =>
	  (case (c, c') of
	       (Arrow (c1, d, c2), Arrow (c1', d', c2')) => 
	       let val c1'' = meet (ctx, c1, c1', Type) 
		   val d'' = d $ d' 
		   val c2'' = join (ctx, c2, c2', Type) in
		   Arrow (c1'', d'', c2'')
	       end
	     | (Constr.Var a, Constr.Var a') => 
	       if a = a' then
		   c
	       else
		   raise Fail (no_join c c')
	     | (Unit, Unit) => Unit
	     | (Prod (c1, c2), Prod (c1', c2')) => 
	       let val c1'' = join (ctx, c1, c1', Type) 
		   val c2'' = join (ctx, c2, c2', Type) in
		   Prod (c1'', c2'')
	       end
	     | (Sum (c1, c2), Sum (c1', c2')) => 
	       let val c1'' = join (ctx, c1, c1', Type) 
		   val c2'' = join (ctx, c2, c2', Type) in
		   Sum (c1'', c2'')
	       end
	     | (Uni (name, t), Uni (_, t')) => 
	       let val t'' = join (add_kinding_s (name, Type) ctx, t, t', Type) in
		   Uni (name, t'')
	       end
	     | (UniI (s, name, t), UniI (s', _, t')) => 
	       let val () = is_eqvsort (sctx, s, s')
		   val t'' = join (add_sorting_k (name, s) ctx, t, t', Type) in
		   UniI (s, name, t'')
	       end
	     | (ExI (s, name, t), ExI (s', _, t')) => 
	       let val () = is_eqvsort (ctx, s, s')
		   val t'' = join (add_sorting_k (name, s) ctx, t, t', Type) in
		   ExI (s, name, t'')
	       end
	     (* currently don't support join for recursive types, so they must be equivalent *)
	     | (Constr.AppI (Recur _, _), Constr.AppI (Recur _, _)) => 
	       (is_eqvconstr (ctx, c, c', Type);
		c)
	     | (Constr.AppI (Constr.Var _, _), Constr.AppI (Constr.Var _, _)) => 
	       (is_eqvconstr (ctx, c, c', Type);
		c)
	     | _ => raise Fail (no_join c c'))
	| KArrow _ => raise Impossible "join: should never try join in higher-order kinds"

    and meet (ctx as (sctx : scontext, kctx : kcontext), c : constr, c' : constr, k : kind) : constr = 
	case k of
	    Type =>
	    (case (c, c') of
		 (Arrow (c1, d, c2), Arrow (c1', d', c2')) => 
		 let val c1'' = join (ctx, c1, c1', Type) 
		     val d'' = d $ d' 
		     val c2'' = meet (ctx, c2, c2', Type) in
		     Arrow (c1'', d'', c2'')
		 end
	       | (Constr.Var a, Constr.Var a') => 
		 if a = a' then
		     c
		 else
		     raise Fail (no_meet c c')
	       | (Unit, Unit) => Unit
	       | (Prod (c1, c2), Prod (c1', c2')) => 
		 let val c1'' = meet (ctx, c1, c1', Type) 
		     val c2'' = meet (ctx, c2, c2', Type) in
		     Prod (c1'', c2'')
		 end
	       | (Sum (c1, c2), Sum (c1', c2')) => 
		 let val c1'' = meet (ctx, c1, c1', Type) 
		     val c2'' = meet (ctx, c2, c2', Type) in
		     Sum (c1'', c2'')
		 end
	       | (Uni (name, t), Uni (_, t')) => 
		 let val t'' = meet (add_kinding_s (name, Type) ctx, t, t', Type) in
		     Uni (name, t'')
		 end
	       | (UniI (s, name, t), UniI (s', _, t')) => 
		 let val () = is_eqvsort (sctx, s, s')
		     val t'' = meet (add_sorting_k (name, s) ctx, t, t', Type) in
		     UniI (s, name, t'')
		 end
	       | (ExI (s, name, t), ExI (s', _, t')) => 
		 let val () = is_eqvsort (ctx, s, s')
		     val t'' = meet (add_sorting_k (name, s) ctx, t, t', Type) in
		     ExI (s, name, t'')
		 end
	       (* currently don't support meet for recursive types, so they must be equivalent *)
	       | (Constr.AppI (Recur _, _), Constr.AppI (Recur _, _)) => 
		 (is_eqvconstr (ctx, c, c', Type);
		  c)
	       | (Constr.AppI (Constr.Var _, _), Constr.AppI (Constr.Var _, _)) => 
		 (is_eqvconstr (ctx, c, c', Type);
		  c)
	       | _ => raise Fail (no_meet c c'))
	  | KArrow _ => raise Impossible "meet: should never try meet in higher-order kinds"

    end

    fun is_value (e : expr) : bool = raise Unimpl

    fun mismatch e expect have =  "Type mismatch for " ^ expr_toString e ^ ": expect " ^ expect ^ " have " ^ constr_toString have
    fun mismatch_anno expect have =  "Type annotation mismatch: expect " ^ expect ^ " have " ^ constr_toString have

    fun check_fix_body e =
      case e of
	  Tabs (_, e') => check_fix_body e'
	| Abs _ => ()
	| _ => raise Fail "The body of fixpoint must have the form (fn [(_ :: _) ... (_ :: _)] (_ : _) => _)"

    fun get_type (ctx as (sctx : scontext, ktctx as (kctx : kcontext, tctx : tcontext)), e : expr) : constr * idx =
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
	      let val () = check_kind (skctx, t, Type)
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
		  val () = check_kind (skctx, t2, Type) in
		  (Sum (t1, t2), d)
	      end
	    | Inr (t1, e) => 
	      let val (t2, d) = get_type (ctx, e)
		  val () = check_kind (skctx, t1, Type) in
		  (Sum (t1, t2), d)
	      end
	    | Match (e, name1, e1, name2, e2) => 
	      let val (t, d) = get_type (ctx, e) in
		  case t of
		      Sum (t1, t2) => 
		      let val (tr1, d1) = get_type (add_typing_sk (name1, t1) ctx, e1)
			  val (tr2, d2) = get_type (add_typing_sk (name2, t2) ctx, e2)
			  val tr = join (skctx, tr1, tr2, Type) in
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
		      let val () = check_kind (skctx, c, Type) in
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
			  (subst_idx i t1, d + T1)
		      end
		    | t' => raise Fail (mismatch e "(forallI _ : _, _)" t')
	      end
	    | Fold (t, e) => 
	      (case t of
		   Constr.AppI (t1 as Recur (_, _, _, t2), i) =>
		   let val () = check_kind (skctx, t, Type)
		       val (t3, d) = get_type (ctx, e)
		       val () = is_subtype (skctx, t3, (subst t1 (subst_idx i t2))) in
		       (t, d)
		   end
		 | t' => raise Fail (mismatch_anno "((recur (_ :: _) (_ : _), _) _)" t'))
	    | Unfold e =>
	      let val (t, d) = get_type (ctx, e) in
		  case t of
	      	      Constr.AppI (t1 as Recur (_, _, _, t2), i) =>
		      (subst t1 (subst_idx i t2), d + T1)
		    | t' => raise Fail (mismatch e "((recur (_ :: _) (_ : _), _) _)" t')
	      end
	    | Pack (t, i, e) =>
	      (case t of
		   ExI (s, _, t1) =>
		   let val () = check_kind (skctx, t, Type)
		       val () = check_sort (sctx, i, s)
		       val (t2, d) = get_type (ctx, e)
		       val () = is_subtype (skctx, t2, (subst_idx i t1)) in
		       (t, d)
		   end
		 | t' => raise Fail (mismatch_anno "(ex _ : _, _)" t'))
	    | Unpack (e1, t, d, idx_var, expr_var, e2) => 
	      let val () = check_kind (skctx, t, Type)
		  val () = check_sort (sctx, d, Time)
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
		  val () = check_kind (skctx, t, Type)
		  val (t1, _) = get_type (add_typing_sk (name, t) ctx, e)
		  val () = is_subtype (skctx, t1, t) in
		  (t, T0)
	      end
	    | Ascription (e, t) => 
	      let val () = check_kind (skctx, t, Type)
		  val (t1, d) = get_type (ctx, e)
		  val () = is_subtype (skctx, t1, t) in
		  (t, d)
	      end
	    | AscriptionTime (e, d) => 
	      let val () = check_sort (sctx, d, Time)
		  val (t, d1) = get_type (ctx, e)
		  val () = is_le (sctx, d1, d) in
		  (t, d)
	      end
      end
in								     

fun vcgen (sctx : scontext) (kctx : kcontext) (tctx : tcontext) (e : expr) : ((constr * idx) * prop list) result =
  runError (runWriter (fn () => get_type ((sctx, (kctx, tctx)), e))) ()
      
end

val result = vcgen [] [] [] (Var 0)
val _ =
    case result of
	OK ((t, d), vc) => print ("OK: type=" ^ constr_toString t ^ " d=" ^ idx_toString d)
      | Failed msg => print ("Failed: " ^ msg ^ "\n")
