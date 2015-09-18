type var = int

datatype 'a result =
	 OK of 'a
	 | Failed of string

exception Unimpl
exception Impossible of string

(* constructors *)
signature CONSTR = sig
    type kind
    type constr
end

structure Constr = struct

datatype kind = 
	 Type
	 | NonType of ntkind
	 (* will only be used by recursive types in a restricted form *)
	 | KArrow of ntkind

     (* non-type kind *)
     and ntkind =
	 Time
	 | Bool
	 | KUnit
	 | KProd of ntkind * ntkind
	 | Subset of ntkind * string * prop
					   
     and prop =
	 True
	 | False
	 | And of prop * prop
	 | Or of prop * prop
	 | TimeEq of constr * constr
	 | TimeLe of constr * constr
	 | BoolEq of constr * constr

     and constr = 
	 Var of var
	 | Arrow of constr * constr * constr
	 | Unit
	 | Prod of constr * constr
	 | Sum of constr * constr
	 | Uni of kind * string * constr
	 | Ex of kind * string * constr
	 (* the kind of Recur is kind => Type (where kind is not Type or Arrow), to allow for change of index *)
	 | Recur of string * ntkind * string * constr
	 (* the first operant of App can only be a recursive type*)
	 | App of constr * constr
	 | T0
	 | T1
	 | Tadd of constr * constr
	 | Tmax of constr * constr
	 | Tmin of constr * constr
	 | Btrue
	 | Bfalse
	 | TT
	 | Pair of constr * constr
	 | Fst of constr
	 | Snd of constr

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
	 | AscriptionTime of expr * constr
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
	 | Tabs of kind * string * expr
	 | Tapp of expr * constr
	 (* existential *)
	 | Pack of constr * constr * expr
	 | Unpack of expr * constr * constr * string * string * expr
	 (* recursive type *)
	 | Fold of constr * expr
	 | Unfold of expr
end			       

structure Expr = MakeExpr (structure Constr = Constr)
open Constr
open Expr

(* kinding context *)
type kcontext = (string * kind) list
fun add_kinding (name, k) kctx = (name, k) :: kctx
fun lookup_type (x : var) (kctx : kcontext) : kind option = NONE

(* typing context *)
type tcontext = (string * constr) list
fun add_typing (name, c) tctx = (name, c) :: tctx
fun lookup (x : var) (tctx : tcontext) : constr option = NONE

fun var_toString (x : var) : string = Int.toString x

fun kind_toString (k : kind) : string = raise Unimpl

fun constr_toString (c : constr) : string =
  case c of
      Arrow (c1, d, c2) => "(" ^ constr_toString c1 ^ " time " ^ constr_toString d ^ " -> " ^ constr_toString c2 ^ ")"
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

    fun is_le (arg : kcontext * constr * constr) = raise Unimpl
    fun is_eq (arg : kcontext * constr * constr * ntkind) = raise Unimpl
    fun is_iff (arg : kcontext * prop * prop) = raise Unimpl

    fun is_eqvntkind (kctx, k, k') =
      case (k, k') of
	  (Time, Time) => ()
	| (Bool, Bool) => ()
	| (KUnit, KUnit) => ()
	| (KProd (k1, k2), KProd (k1', k2')) =>
	  (is_eqvntkind (kctx, k1, k1');
	   is_eqvntkind (kctx, k2, k2'))
	| (Subset (k1, name, p), Subset (k1', _, p')) =>
	  (is_eqvntkind (kctx, k1, k1');
	   is_iff (add_kinding (name, NonType k1) kctx, p, p'))
	| _ => raise Fail ("Kind mismatch: " ^ kind_toString (NonType k) ^ " and " ^ kind_toString (NonType k'))

    fun is_eqvkind (kctx, k, k') =
      case (k, k') of
	  (Type, Type) => ()
	| (KArrow k1, KArrow k1') =>
	  is_eqvntkind (kctx, k1, k1')
	| (NonType k1, NonType k1') => 
	  is_eqvntkind (kctx, k1, k1')
	| _ => raise Fail ("Kind mismatch: " ^ kind_toString k ^ " and " ^ kind_toString k')
			      
    (* k => Type *)
    fun recur_kind k = KArrow k

    val KTime = NonType Time
    val KBool = NonType Bool
			
    local

	fun kind_mismatch c expect have =  "Kind mismatch for " ^ constr_toString c ^ ": expect " ^ expect ^ " have " ^ kind_toString have
    in

    fun is_wfkind (kctx : kcontext, k : kind) =
      case k of
	  Type => ()
	| NonType k1 =>
	  is_wfntkind (kctx, k1)
	| KArrow k1 =>
	  is_wfntkind (kctx, k1)

    and is_wfntkind (kctx : kcontext, k : ntkind) =
	case k of
	    Time => ()
	  | Bool => ()
	  | KUnit => ()
	  | KProd (k1, k2) =>
	    (is_wfntkind (kctx, k1);
	     is_wfntkind (kctx, k2))
	  | Subset (k, name, p) =>
	    (is_wfntkind (kctx, k);
	     is_wfprop (add_kinding (name, NonType k) kctx, p))

    and is_wfprop (kctx : kcontext, p : prop) =
	case p of
	    True => ()
	  | False => ()
	  | And (p1, p2) =>
	    (is_wfprop (kctx, p1);
	     is_wfprop (kctx, p2))
	  | Or (p1, p2) =>
	    (is_wfprop (kctx, p1);
	     is_wfprop (kctx, p2))
	  | TimeEq (d1, d2) =>
	    (check_kind (kctx, d1, KTime);
	     check_kind (kctx, d2, KTime))
	  | TimeLe (d1, d2) =>
	    (check_kind (kctx, d1, KTime);
	     check_kind (kctx, d2, KTime))
	  | BoolEq (d1, d2) =>
	    (check_kind (kctx, d1, KBool);
	     check_kind (kctx, d2, KBool))

    and get_kind (kctx : kcontext, c : constr) : kind = 
	case c of
	    Constr.Var a =>
	    (case lookup_type a kctx of
      		 SOME k => k
      	       | NONE => raise Fail ("Unbound type variable " ^ var_toString a))
	  | Arrow (c1, d, c2) => 
	    (check_kind (kctx, c1, Type);
	     check_kind (kctx, d, KTime);
	     check_kind (kctx, c2, Type);
	     Type)
	  | Unit => Type
	  | Prod (c1, c2) => 
	    (check_kind (kctx, c1, Type);
	     check_kind (kctx, c2, Type);
	     Type)
	  | Sum (c1, c2) => 
	    (check_kind (kctx, c1, Type);
	     check_kind (kctx, c2, Type);
	     Type)
	  | Uni (k, name, c) => 
	    (is_wfkind (kctx, k);
	     check_kind (add_kinding (name, k) kctx, c, Type);
	     Type)
	  | Ex (k, name, c) => 
	    (is_wfkind (kctx, k);
	     check_kind (add_kinding (name, k) kctx, c, Type);
	     Type)
	  | Recur (nameself, k, namearg, t) =>
	    (is_wfkind (kctx, NonType k);
	     check_kind (add_kinding (namearg, NonType k) (add_kinding (nameself, recur_kind k) kctx), t, Type);
	     recur_kind k)
	  | Constr.App (c1, c2) => 
	    let val k1 = get_kind (kctx, c1) in
		case k1 of
		    KArrow k2 => 
		    (check_kind (kctx, c2, NonType k2);
		     Type)
		  | _ => raise Fail (kind_mismatch c1 "(_ => _)" k1)
	    end
	  | T0 => KTime
	  | T1 => KTime
	  | Tadd (d1, d2) => 
	    (check_kind (kctx, d1, KTime);
	     check_kind (kctx, d2, KTime);
	     KTime)
	  | Tmax (d1, d2) => 
	    (check_kind (kctx, d1, KTime);
	     check_kind (kctx, d2, KTime);
	     KTime)
	  | Tmin (d1, d2) => 
	    (check_kind (kctx, d1, KTime);
	     check_kind (kctx, d2, KTime);
	     KTime)
	  | Btrue => KBool
	  | Bfalse => KBool
	  | Constr.TT => NonType KUnit
	  | Constr.Pair (c1, c2) =>
	    (case (get_kind (kctx, c1), get_kind (kctx, c2)) of
		 (NonType k1, NonType k2) => NonType (KProd (k1, k2))
	       | (NonType _, k2) => raise Fail (kind_mismatch c2 "(NonType _)" k2)
	       | (k1, _) => raise Fail (kind_mismatch c1 "(NonType _)" k1))
	  | Constr.Fst c1 =>
	    let val k = get_kind (kctx, c1) in
		case k of
		    NonType (KProd (k1, k2)) => NonType k1
		  | _ => raise Fail (kind_mismatch c1 "(_ * _)" k)
	    end
	  | Constr.Snd c1 =>
	    let val k = get_kind (kctx, c1) in
		case k of
		    NonType (KProd (k1, k2)) => NonType k2
		  | _ => raise Fail (kind_mismatch c1 "(_ * _)" k)
	    end

    and check_kind (kctx : kcontext, c : constr, k : kind) : unit = is_eqvkind (kctx, get_kind (kctx, c), k)

    end

    local
	fun not_subtype c c' = constr_toString c ^ " is not subtype of " ^ constr_toString c'
	(* is_subconstr assumes that the constructors are already checked against the given kind, so it doesn't need to worry about their well-formedness *)
	fun is_subconstr (kctx : kcontext, c : constr, c' : constr, k : kind) =
	  case k of
	      Type =>
	      (case (c, c') of
		   (Arrow (c1, d, c2), Arrow (c1', d', c2')) =>
		   (is_subconstr (kctx, c1', c1, Type);
		    is_le (kctx, d, d');
		    is_subconstr (kctx, c2, c2', Type))
		 | (Constr.Var a, Constr.Var a') => 
		   if a = a' then
		       ()
		   else
		       raise Fail (not_subtype c c')
		 | (Unit, Unit) => ()
		 | (Prod (c1, c2), Prod (c1', c2')) =>
		   (is_subconstr (kctx, c1, c1', Type);
		    is_subconstr (kctx, c2, c2', Type))
		 | (Sum (c1, c2), Sum (c1', c2')) => 
		   (is_subconstr (kctx, c1, c1', Type);
		    is_subconstr (kctx, c2, c2', Type))
		 | (Uni (k, name, c), Uni (k', _, c')) => 
		   (is_eqvkind (kctx, k, k');
		    is_subconstr (add_kinding (name, k) kctx, c, c', Type))
		 | (Ex (k, name, c), Ex (k', _, c')) => 
		   (is_eqvkind (kctx, k, k');
		    is_subconstr (add_kinding (name, k) kctx, c, c', Type))
		 (* currently don't support subtyping for recursive types, so they must be equivalent *)
		 | (Constr.App (Recur (nameself, k, namearg, c1), c2), Constr.App (Recur (_, k', _, c1'), c2')) => 
		   let val () = is_eqvkind (kctx, NonType k, NonType k')
		       val () = is_eqvconstr (kctx, c2, c2', NonType k)
		       val kctx' = add_kinding (namearg, NonType k) (add_kinding (nameself, recur_kind k) kctx) in
		       is_eqvconstr (kctx', c1, c1', Type)
		   end
		 | (Constr.App (c1 as Constr.Var a, c2), Constr.App (Constr.Var a', c2')) => 
		   if a = a' then
		       let val k = get_kind (kctx, c1) in
			   case k of
			       KArrow k1 => 
			       is_eqvconstr (kctx, c2, c2', NonType k1)
			     | _ => raise Impossible "is_subconstr: x in (x c) should have an arrow kind"
		       end
		   else
		       raise Fail (not_subtype c c')
		 | _ => raise Fail (not_subtype c c'))
	    | KArrow _ => raise Impossible "is_subconstr: should never test subconstr in higher-order kinds"
	    | NonType k1 => is_eq (kctx, c, c', k1)

	and is_eqvconstr (kctx, c, c', k) = (is_subconstr (kctx, c, c', k); is_subconstr (kctx, c', c, k))

    in

    fun is_subtype (kctx, t, t') = is_subconstr (kctx, t, t', Type)

    fun no_join c c' = "Cannot find a join (minimal supertype) of " ^ constr_toString c ^ " and " ^ constr_toString c'
    fun no_meet c c' = "Cannot find a meet (maximal subtype) of " ^ constr_toString c ^ " and " ^ constr_toString c'

    (* c and c' are already checked against k *)
    fun join (kctx : kcontext, c : constr, c' : constr, k : kind) : constr = 
      case k of
	  Type =>
	  (case (c, c') of
	       (Arrow (c1, d, c2), Arrow (c1', d', c2')) => 
	       let val c1'' = meet (kctx, c1, c1', Type) 
		   val d'' = d $ d' 
		   val c2'' = join (kctx, c2, c2', Type) in
		   Arrow (c1'', d'', c2'')
	       end
	     | (Constr.Var a, Constr.Var a') => 
	       if a = a' then
		   c
	       else
		   raise Fail (no_join c c')
	     | (Unit, Unit) => Unit
	     | (Prod (c1, c2), Prod (c1', c2')) => 
	       let val c1'' = join (kctx, c1, c1', Type) 
		   val c2'' = join (kctx, c2, c2', Type) in
		   Prod (c1'', c2'')
	       end
	     | (Sum (c1, c2), Sum (c1', c2')) => 
	       let val c1'' = join (kctx, c1, c1', Type) 
		   val c2'' = join (kctx, c2, c2', Type) in
		   Sum (c1'', c2'')
	       end
	     | (Uni (k, name, t), Uni (k', name', t')) => 
	       let val () = is_eqvkind (kctx, k, k')
		   val t'' = join (add_kinding (name, k) kctx, t, t', k) in
		   Uni (k, name, t'')
	       end
	     | (Ex (k, name, t), Ex (k', name', t')) => 
	       let val () = is_eqvkind (kctx, k, k')
		   val t'' = join (add_kinding (name, k) kctx, t, t', k) in
		   Ex (k, name, t'')
	       end
	     (* currently don't support join for recursive types, so they must be equivalent *)
	     | (Constr.App (Recur _, _), Constr.App (Recur _, _)) => 
	       (is_eqvconstr (kctx, c, c', Type);
		c)
	     | (Constr.App (Constr.Var _, _), Constr.App (Constr.Var _, _)) => 
	       (is_eqvconstr (kctx, c, c', Type);
		c)
	     | _ => raise Fail (no_join c c'))
	| KArrow _ => raise Impossible "join: should never try join in higher-order kinds"
	| NonType k1 =>
	  (is_eq (kctx, c, c', k1);
	   c)

    and meet (kctx, c, c', k) = 
	case k of
	    Type =>
	    (case (c, c') of
		 (Arrow (c1, d, c2), Arrow (c1', d', c2')) => 
		 let val c1'' = join (kctx, c1, c1', Type) 
		     val d'' = Tmin (d, d')
		     val c2'' = meet (kctx, c2, c2', Type) in
		     Arrow (c1'', d'', c2'')
		 end
	       | (Constr.Var a, Constr.Var a') => 
		 if a = a' then
		     c
		 else
		     raise Fail (no_meet c c')
	       | (Unit, Unit) => Unit
	       | (Prod (c1, c2), Prod (c1', c2')) => 
		 let val c1'' = meet (kctx, c1, c1', Type) 
		     val c2'' = meet (kctx, c2, c2', Type) in
		     Prod (c1'', c2'')
		 end
	       | (Sum (c1, c2), Sum (c1', c2')) => 
		 let val c1'' = meet (kctx, c1, c1', Type) 
		     val c2'' = meet (kctx, c2, c2', Type) in
		     Sum (c1'', c2'')
		 end
	       | (Uni (k, name, t), Uni (k', name', t')) => 
		 let val () = is_eqvkind (kctx, k, k')
		     val t'' = meet (add_kinding (name, k) kctx, t, t', k) in
		     Uni (k, name, t'')
		 end
	       | (Ex (k, name, t), Ex (k', name', t')) => 
		 let val () = is_eqvkind (kctx, k, k')
		     val t'' = meet (add_kinding (name, k) kctx, t, t', k) in
		     Ex (k, name, t'')
		 end
	       (* currently don't support meet for recursive types, so they must be equivalent *)
	       | (Constr.App (Recur _, _), Constr.App (Recur _, _)) => 
		 (is_eqvconstr (kctx, c, c', Type);
		  c)
	       | (Constr.App (Constr.Var _, _), Constr.App (Constr.Var _, _)) => 
		 (is_eqvconstr (kctx, c, c', Type);
		  c)
	       | _ => raise Fail (no_meet c c'))
	  | KArrow _ => raise Impossible "meet: should never try meet in higher-order kinds"
	  | NonType k1 =>
	    (is_eq (kctx, c, c', k1);
	     c)

    end

    fun is_value (e : expr) : bool = raise Unimpl

    fun mismatch e expect have =  "Type mismatch for " ^ expr_toString e ^ ": expect " ^ expect ^ " have " ^ constr_toString have
    fun mismatch_anno expect have =  "Type annotation mismatch: expect " ^ expect ^ " have " ^ constr_toString have

    fun check_fix_body e =
      case e of
	  Tabs (_, _, e') => check_fix_body e'
	| Abs _ => ()
	| _ => raise Fail "The body of fixpoint must have the form (fn [(_ :: _) ... (_ :: _)] (_ : _) => _)"

    fun get_type (ctx as (kctx : kcontext, tctx : tcontext), e : expr) : constr * constr =
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
		      val () = is_subtype (kctx, t2', t2) in
    		      (t, d1 + d2 + T1 + d) 
		  end
    		| t1' =>  raise Fail (mismatch e1 "(_ time _ -> _)" t1')
	  end
	| Abs (t, varname, e) => 
	  let val () = check_kind (kctx, t, Type)
	      val (t1, d) = get_type ((kctx, (add_typing (varname, t) tctx)), e) in
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
	      val () = check_kind (kctx, t2, Type) in
	      (Sum (t1, t2), d)
	  end
	| Inr (t1, e) => 
	  let val (t2, d) = get_type (ctx, e)
	      val () = check_kind (kctx, t1, Type) in
	      (Sum (t1, t2), d)
	  end
	| Match (e, name1, e1, name2, e2) => 
	  let val (t, d) = get_type (ctx, e) in
	      case t of
		  Sum (t1, t2) => 
		  let val (tr1, d1) = get_type ((kctx, add_typing (name1, t1) tctx), e1)
		      val (tr2, d2) = get_type ((kctx, add_typing (name2, t2) tctx), e2)
		      val tr = join (kctx, tr1, tr2, Type) in
		      (tr, d + T1 + d1 $ d2)
		  end
		| t' => raise Fail (mismatch e "(_ + _)" t')
	  end
	| Tabs (k, name, e) => 
	  if is_value e then
	      let val () = is_wfkind (kctx, k)
		  val (t, _) = get_type ((add_kinding (name, k) kctx, tctx), e) in
		  (Uni (k, name, t), T0)
	      end 
	  else
	      raise Fail ("The body of a universal abstraction must be a value")
	| Tapp (e, c) =>
	  let val (t, d) = get_type (ctx, e) in
	      case t of
		  Uni (k, name, t1) => 
		  let val () = check_kind (kctx, c, k) in
		      (subst c t1, d + T1)
		  end
		| t' => raise Fail (mismatch e "(forall _ : _, _)" t')
	  end
	| Fold (t, e) => 
	  (case t of
	       Constr.App (t1 as Recur (_, k, _, t2), c) =>
	       let val (t3, d) = get_type (ctx, e)
		   val () = check_kind (kctx, t, Type)
		   val () = is_subtype (kctx, t3, (subst c (subst t1 t2))) in
		   (t, d)
	       end
	     | t' => raise Fail (mismatch_anno "((recur (_ :: _) (_ : _), _) _)" t'))
	| Unfold e =>
	  let val (t, d) = get_type (ctx, e) in
	      case t of
	      	  Constr.App (t1 as Recur (_, _, _, t2), c) =>
		  (subst c (subst t1 t2), d + T1)
		| t' => raise Fail (mismatch e "((recur (_ :: _) (_ : _), _) _)" t')
	  end
	| Pack (t, c, e) =>
	  (case t of
	       Ex (k, _, t1) =>
	       let val () = check_kind (kctx, t, Type)
		   val () = check_kind (kctx, c, k)
		   val (t2, d) = get_type (ctx, e)
		   val () = is_subtype (kctx, t2, (subst c t1)) in
		   (t, d)
	       end
	     | t' => raise Fail (mismatch_anno "(ex _ : _, _)" t'))
	| Unpack (e1, t, d, type_var, expr_var, e2) => 
	  let val () = check_kind (kctx, t, Type)
	      val () = check_kind (kctx, d, KTime)
	      val (t1, d1) = get_type (ctx, e1) in
	      case t1 of
		  Ex (k, _, t1') => 
		  let val (t2, d2) = get_type ((add_kinding (type_var, k) kctx, add_typing (expr_var, t1') tctx), e2)
		      val () = is_subtype (kctx, t2, t)
		      val () = is_le (kctx, d2, d) in
		      (t, d1 + T1 + d)
		  end
		| t1' => raise Fail (mismatch e1 "(ex _ : _, _)" t1')
	  end
	| Let (e1, name, e2) => 
	  let val (t1, d1) = get_type (ctx, e1)
	      val (t2, d2) = get_type ((kctx, add_typing (name, t1) tctx), e2) in
	      (t2, d1 + T1 + d2)
	  end
	| Fix (t, name, e) => 
	  let val () = check_fix_body e
	      val () = check_kind (kctx, t, Type)
	      val (t1, _) = get_type ((kctx, add_typing (name, t) tctx), e)
	      val () = is_subtype (kctx, t1, t) in
	      (t, T0)
	  end
	| Ascription (e, t) => 
	  let val () = check_kind (kctx, t, Type)
	      val (t1, d) = get_type (ctx, e)
	      val () = is_subtype (kctx, t1, t) in
	      (t, d)
	  end
	| AscriptionTime (e, d) => 
	  let val () = check_kind (kctx, d, KTime)
	      val (t, d1) = get_type (ctx, e)
	      val () = is_le (kctx, d1, d) in
	      (t, d)
	  end

in								     

fun vcgen (ctx : kcontext * tcontext) (e : expr) : ((constr * constr) * prop list) result =
  runError (runWriter (fn _ => get_type (ctx, e))) ()

end

val result = vcgen ([], []) (Var 0)
val _ =
    case result of
	OK _ => print "OK\n"
      | Failed msg => print ("Failed: " ^ msg ^ "\n")
