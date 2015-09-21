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
	 VarI of var
	 | T0
	 | T1
	 | Tadd of idx * idx
	 | Tmax of idx * idx
	 | Tmin of idx * idx
	 | TrueI
	 | FalseI
	 | TT

datatype prop =
	 True
	 | False
	 | And of prop * prop
	 | Or of prop * prop
	 | Imply of prop * prop
	 | TimeLe of idx * idx
	 | Eq of bsort * idx * idx

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
		 | Fix of ty * idx * ty * string * string * expr
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

fun is_value (e : expr) : bool =
    case e of
	Var _ => true
      | App _ => false
      | Abs _ => true
      | TT => true
      | Pair (e1, e2) => is_value e1 andalso is_value e2
      | Fst _ => false
      | Snd _ => false
      | Inl (_, e) => is_value e
      | Inr (_, e) => is_value e
      | Match _ => false
      | Fold (_, e) => is_value e
      | Unfold _ => false
      | Tabs _ => true
      | Tapp _ => false
      | TabsI _ => true
      | TappI _ => false
      | Pack (_, _, e) => is_value e
      | Unpack _ => false
      | Fix _ => true
      | Let _ => false
      | Ascription _ => false
      | AscriptionTime _ => false

fun var_toString (x : var) : string = Int.toString x
fun bsort_toString (s : bsort) : string = raise Unimpl
fun sort_toString (s : sort) : string = raise Unimpl
fun idx_toString (i : idx) : string = raise Unimpl
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

local
    fun f x n b =
	case b of
	    VarI y =>
	    if y >= x then
		VarI (y + n)
	    else
		VarI y
	  | T0 => T0
	  | T1 => T1
	  | Tadd (d1, d2) => Tadd (f x n d1, f x n d2)
	  | Tmax (d1, d2) => Tmax (f x n d1, f x n d2)
	  | Tmin (d1, d2) => Tmin (f x n d1, f x n d2)
	  | Type.TT => Type.TT
	  | TrueI => TrueI
	  | FalseI => FalseI
in
fun shiftx_i_i x n b = f x n b
fun shift_i_i b = shiftx_i_i 0 1 b
end

local
    fun f x n b =
	case b of
	    True => True
	  | False => False
	  | And (p1, p2) => And (f x n p1, f x n p2)
	  | Or (p1, p2) => Or (f x n p1, f x n p2)
	  | Imply (p1, p2) => Imply (f x n p1, f x n p2)
	  | TimeLe (d1, d2) => TimeLe (shiftx_i_i x n d1, shiftx_i_i x n d2)
	  | Eq (s, i1, i2) => Eq (s, shiftx_i_i x n i1, shiftx_i_i x n i2)
in
fun shiftx_i_p x n b = f x n b
fun shift_i_p b = shiftx_i_p 0 1 b
end

local
    fun f x n b =
	case b of
	    Basic s => Basic s
	  | Subset (s, name, p) => Subset (s, name, shiftx_i_p (x + 1) n p)
in
fun shiftx_i_s x n b = f x n b
fun shift_i_s b = shiftx_i_s 0 1 b
end

local
    fun f x n b =
	case b of
	    Type.Var y => Type.Var y
	  | Arrow (t1, d, t2) => Arrow (f x n t1, shiftx_i_i x n d, f x n t2)
	  | Unit => Unit
	  | Prod (t1, t2) => Prod (f x n t1, f x n t2)
	  | Sum (t1, t2) => Sum (f x n t1, f x n t2)
	  | Uni (name, t) => Uni (name, f x n t)
	  | UniI (s, name, t) => UniI (shiftx_i_s x n s, name, f (x + 1) n t)
	  | ExI (s, name, t) => ExI (shiftx_i_s x n s, name, f (x + 1) n t)
	  | AppRecur (name, ns, t, i) => AppRecur (name, map (fn (name, s) => (name, shiftx_i_s x n s)) ns, f (x + length ns) n t, map (shiftx_i_i x n) i)
	  | AppVar (y, i) =>  AppVar (y, map (shiftx_i_i x n) i)
in
fun shiftx_i_t x n b = f x n b
fun shift_i_t b = shiftx_i_t 0 1 b
end

local
    fun f x n b =
	case b of
	    Type.Var y =>
	    if y >= x then
		Type.Var (y + n)
	    else
		Type.Var y
	  | Arrow (t1, d, t2) => Arrow (f x n t1, d, f x n t2)
	  | Unit => Unit
	  | Prod (t1, t2) => Prod (f x n t1, f x n t2)
	  | Sum (t1, t2) => Sum (f x n t1, f x n t2)
	  | Uni (name, t) => Uni (name, f (x + 1) n t)
	  | AppRecur (name, ns, t, i) => AppRecur (name, ns, f (x + 1) n t, i)
	  | AppVar (y, i) => 
	    if y >= x then
		AppVar (y + n, i)
	    else
		AppVar (y, i)
	  | UniI (s, name, t) => UniI (s, name, f x n t)
	  | ExI (s, name, t) => ExI (s, name, f x n t)
in
fun shiftx_t_t x n b = f x n b
fun shift_t_t b = shiftx_t_t 0 1 b
end

exception Subst of string

local
    fun f x v b =
	case b of
	    VarI y =>
	    if y = x then
		v
	    else if y > x then
		VarI (y - 1)
	    else
		VarI y
	  | Tadd (d1, d2) => Tadd (f x v d1, f x v d2)
	  | Tmax (d1, d2) => Tmax (f x v d1, f x v d2)
	  | Tmin (d1, d2) => Tmin (f x v d1, f x v d2)
	  | T0 => T0
	  | T1 => T1
	  | TrueI => TrueI
	  | FalseI => FalseI
	  | Type.TT => Type.TT
in
fun substx_i_i x (v : idx) (b : idx) : idx = f x v b
fun subst_i_i v b = substx_i_i 0 v b
end

local
    fun f x v b =
	case b of
	    True => True
	  | False => False
	  | And (p1, p2) => And (f x v p1, f x v p2)
	  | Or (p1, p2) => Or (f x v p1, f x v p2)
	  | Imply (p1, p2) => Imply (f x v p1, f x v p2)
	  | TimeLe (d1, d2) => TimeLe (substx_i_i x v d1, substx_i_i x v d2)
	  | Eq (s, i1, i2) => Eq (s, substx_i_i x v i1, substx_i_i x v i2)
in
fun substx_i_p x (v : idx) b = f x v b
fun subst_i_p (v : idx) (b : prop) : prop = substx_i_p 0 v b
end

local
    fun f x v b =
	case b of
	    Basic s => Basic s
	  | Subset (s, name, p) => Subset (s, name, substx_i_p (x + 1) (shift_i_i v) p)
in
fun substx_i_s x (v : idx) (b : sort) : sort = f x v b
fun subst_i_s (v : idx) (b : sort) : sort = substx_i_s 0 v b
end

local
    fun f x v b =
	case b of
	    Type.Var y => Type.Var y
	  | Arrow (t1, d, t2) => Arrow (f x v t1, substx_i_i x v d, f x v t2)
	  | Unit => Unit
	  | Prod (t1, t2) => Prod (f x v t1, f x v t2)
	  | Sum (t1, t2) => Sum (f x v t1, f x v t2)
	  | Uni (name, t) => Uni (name, f x v t)
	  | UniI (s, name, t) => UniI (substx_i_s x v s, name, f x v t)
	  | ExI (s, name, t) => ExI (substx_i_s x v s, name, f x v t)
	  | AppRecur (name, ns, t, i) =>
	    let val n = length ns in
		AppRecur (name, map (fn (name, s) => (name, substx_i_s x v s)) ns, f (x + n) (shiftx_i_i 0 n v) t, map (substx_i_i x v) i)
	    end
	  | AppVar (y, i) => AppVar (y, map (substx_i_i x v) i)
in
fun substx_i_t x (v : idx) (b : ty) : ty = f x v b
fun subst_i_t (v : idx) (b : ty) : ty = substx_i_t 0 v b
end

local
    fun f x (v : ty) (b : ty) : ty =
	case b of
	    Type.Var y =>
	    if y = x then
		v
	    else if y > x then
		Type.Var (y - 1)
	    else
		Type.Var y
	  | Arrow (t1, d, t2) => Arrow (f x v t1, d, f x v t2)
	  | Unit => Unit
	  | Prod (t1, t2) => Prod (f x v t1, f x v t2)
	  | Sum (t1, t2) => Sum (f x v t1, f x v t2)
	  | Uni (name, t) => Uni (name, f (x + 1) (shift_t_t v) t)
	  | UniI (s, name, t) => UniI (s, name, f x (shift_i_t v) t)
	  | ExI (s, name, t) => ExI (s, name, f x (shift_i_t v) t)
	  | AppRecur (name, ns, t, i) => AppRecur (name, ns, f (x + 1) (shiftx_i_t 0 (length ns) (shift_t_t v)) t, i)
	  | AppVar (y, i) => 
	    if y = x then
		raise Subst "self-reference variable should only be subtitute for via unrolling"
	    else if y > x then
		AppVar (y - 1, i)
	    else
		AppVar (y, i)
in
fun substx_t_t x (v : ty) (b : ty) : ty = f x v b
fun subst (v : ty) (b : ty) : ty = substx_t_t 0 v b
end

local
    fun shift_i n (name, ns, t) = (name, map (fn (name, s) => (name, shiftx_i_s 0 n s)) ns, shiftx_i_t 0 n t)
    fun shift_t (name, ns, t) = (name, ns, shiftx_t_t 0 1 t)
    fun f x v (b : ty) : ty =
	case b of
	    Type.Var y =>
	    if y = x then
		raise Subst "unroll should only do subtitution on self-reference variable"
	    else if y > x then
		Type.Var (y - 1)
	    else
		Type.Var y
	  | Arrow (t1, d, t2) => Arrow (f x v t1, d, f x v t2)
	  | Unit => Unit
	  | Prod (t1, t2) => Prod (f x v t1, f x v t2)
	  | Sum (t1, t2) => Sum (f x v t1, f x v t2)
	  | Uni (name, t) => Uni (name, f (x + 1) (shift_t v) t)
	  | UniI (s, name, t) => UniI (s, name, f x (shift_i 1 v) t)
	  | ExI (s, name, t) => ExI (s, name, f x (shift_i 1 v) t)
	  | AppRecur (name, ns, t, i) => AppRecur (name, ns, f (x + 1) (shift_i (length ns) (shift_t v)) t, i)
	  | AppVar (y, i) => 
	    if y = x then
		let val (name, ns, t) = v in
		    AppRecur (name, ns, t, i)
		end
	    else if y > x then
		AppVar (y - 1, i)
	    else
		AppVar (y, i)
in
fun unroll (name, ns, t, i) =
    let val n = length ns 
	val t = f 0 (shift_i n (name, ns, t)) t 
	val (t, _) = foldl (fn (i, (t, x)) => (substx_i_t x i t, x - 1)) (t, n - 1) i in
	t
    end
end

datatype kind = 
	 Type
	 (* will only be used by recursive types in a restricted form *)
	 | KArrow of sort list

local
    fun f x n b =
	case b of
	    Type => Type
	  | KArrow s => KArrow (map (shiftx_i_s x n) s)
in
fun shiftx_i_k x n b = f x n b
fun shift_i_k b = shiftx_i_k 0 1 b
end

fun kind_toString (k : kind) : string = raise Unimpl

(* sorting context *)
type scontext = (string * sort) list
(* kinding context *)
type kcontext = (string * kind) list
(* typing context *)
type tcontext = (string * ty) list
type context = scontext * kcontext * tcontext

fun shiftx_i_ks n ctx = map (fn (name, k) => (name, shiftx_i_k 0 n k)) ctx
fun shiftx_i_ts n ctx = map (fn (name, t) => (name, shiftx_i_t 0 n t)) ctx
fun shiftx_t_ts n ctx = map (fn (name, t) => (name, shiftx_t_t 0 n t)) ctx
fun add_sorting ns sctx = ns :: sctx
fun add_sorting_k ns (sctx, kctx) = 
    (add_sorting ns sctx, shiftx_i_ks 1 kctx)
fun add_sortings_k ns (sctx, kctx) = 
    let val (sctx', _) = foldl (fn ((name, s), (ctx, n)) => (add_sorting (name, (shiftx_i_s 0 n s)) ctx, n + 1)) (sctx, 0) ns
	val kctx' = shiftx_i_ks (length ns) kctx in
	(sctx', kctx')
    end
fun add_sorting_kt ns (sctx, (kctx, tctx)) = 
    (add_sorting ns sctx, 
     (shiftx_i_ks 1 kctx, 
      shiftx_i_ts 1 tctx))

fun nth_error ls n =
    if n < 0 orelse n >= length ls then
	NONE
    else
	SOME (List.nth (ls, n))

fun lookup_sort (n : int) (ctx : scontext) : sort option = 
    case nth_error ctx n of
	NONE => NONE
      | SOME (_, s) => 
	SOME (shiftx_i_s 0 (n + 1) s)

fun add_kinding (name, k) kctx = (name, k) :: kctx
fun add_kinding_t nk (kctx, tctx) = 
    (add_kinding nk kctx,
     shiftx_t_ts 1 tctx)
fun add_kinding_s nk (sctx, kctx) = (sctx, add_kinding nk kctx)
fun lookup_kind (n : int) (ctx : kcontext) : kind option = 
    case nth_error ctx n of
	NONE => NONE
      | SOME (_, k) => SOME k

fun add_typing nt tctx = nt :: tctx
fun add_typing_sk nt (sctx, (kctx, tctx)) = (sctx, (kctx, add_typing nt tctx))
fun lookup (n : int) (ctx : tcontext) : ty option = 
    case nth_error ctx n of
	NONE => NONE
      | SOME (_, t) => SOME t

fun get_base s =
    case s of
	Basic s => s
      | Subset (s, _, _) => s

type bscontext = (string * bsort) list

fun collect ctx : bscontext * prop list = 
    let fun get_p s n ps =
	    case s of
		Basic _ => ps
	      | Subset (_, _, p) => shiftx_i_p 0 n p :: ps
	val (ps, _) = foldl (fn ((name, s), (ps, n)) => (get_p s n ps, n + 1)) ([], 0) ctx
	val bctx = map (fn (name, s) => (name, get_base s)) ctx in
	(bctx, ps)
    end

type vc = bscontext * prop list * prop

(* level 7 *)
infix 7 $
fun a $ b = Tmax (a, b)
(* level 6 *)
infix 6 %+
fun a %+ b = Tadd (a, b)
(* level 4 *)
infix 4 %<=
fun a %<= b = TimeLe (a, b)
(* level 3 *)
infix 3 /\
fun a /\ b = And (a, b)
(* level 1 *)
infix 1 -->
fun a --> b = Imply (a, b)

(* use exception and cell to mimic the Error and Writer monads *)
local								    

    exception Fail of string

    fun runError m _ =
	OK (m ())
	handle
	Fail msg => Failed msg

    val acc = ref ([] : vc list)

    fun tell a =
	acc := a :: !acc

    fun runWriter m _ =
	(acc := []; let val r = m () in (r, !acc) end)

    fun check_length (a, b) =
	if length a = length b then
	    ()
	else
	    raise Fail "List length mismatch"

    fun is_le (ctx : scontext, d : idx, d' : idx) =
	let val (bctx, ps) = collect ctx in
	    tell (bctx, ps, d %<= d')
	end
	    
    fun is_eq (ctx : scontext, i : idx, i' : idx, s : sort) = 
	let val (bctx, ps) = collect ctx in
	    tell (bctx, ps, Eq (get_base s, i, i'))
	end

    fun is_eqs (ctx, i, i', s) =
	(check_length (i, i');
	 check_length (i, s);
	 app (fn ((i, i'), s) => is_eq (ctx, i, i', s)) (ListPair.zip ((ListPair.zip (i, i')), s)))
	    
    fun is_true (ctx : scontext, p : prop) = 
	let val (bctx, ps) = collect ctx in
	    tell (bctx, ps, p)
	end

    fun is_iff (ctx : scontext, p1 : prop, p2 : prop) = 
	let val (bctx, ps) = collect ctx in
	    tell (bctx, ps, (p1 --> p2) /\ (p2 --> p1))
	end

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
	  | Imply (p1, p2) =>
	    (is_wfprop (ctx, p1);
	     is_wfprop (ctx, p2))
	  | TimeLe (d1, d2) =>
	    (check_sort (ctx, d1, STime);
	     check_sort (ctx, d2, STime))
	  | Eq (s, i1, i2) =>
	    (check_sort (ctx, i1, Basic s);
	     check_sort (ctx, i2, Basic s))

    and check_sort (ctx, i, s) : unit =
	let val s' = get_bsort (ctx, i) in
	    case s of
		Subset (s1, _, p) =>
		(is_eqvbsort (s', s1);
		 is_true (ctx, subst_i_p i p))
	      | Basic s1 => 
		is_eqvbsort (s', s1)
	end

    and check_bsort (ctx, i, s) : unit =
	is_eqvbsort (get_bsort (ctx, i), s)

    and get_bsort (ctx, i) =
	case i of
	    VarI x =>
	    (case lookup_sort x ctx of
      		 SOME s => get_base s
      	       | NONE => raise Fail ("Unbound index variable " ^ var_toString x))
      	  | T0 => Time
	  | T1 => Time
	  | Tadd (d1, d2) => 
	    (check_bsort (ctx, d1, Time);
	     check_bsort (ctx, d2, Time);
	     Time)
	  | Tmax (d1, d2) => 
	    (check_bsort (ctx, d1, Time);
	     check_bsort (ctx, d2, Time);
	     Time)
	  | Tmin (d1, d2) => 
	    (check_bsort (ctx, d1, Time);
	     check_bsort (ctx, d2, Time);
	     Time)
	  | TrueI => Bool
	  | FalseI => Bool
	  | Type.TT => BSUnit

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

    fun mismatch e expect have =  "Type mismatch for " ^ expr_toString e ^ ": expect " ^ expect ^ " have " ^ type_toString have
    fun mismatch_anno expect have =  "Type annotation mismatch: expect " ^ expect ^ " have " ^ type_toString have

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
    			    (t, d1 %+ d2 %+ T1 %+ d) 
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
		    (Prod (t1, t2), d1 %+ d2)
		end
	      | Fst e => 
		let val (t, d) = get_type (ctx, e) in 
		    case t of
			Prod (t1, t2) => (t1, d %+ T1)
		      | t' => raise Fail (mismatch e "(_ * _)" t')
		end
	      | Snd e => 
		let val (t, d) = get_type (ctx, e) in 
		    case t of
			Prod (t1, t2) => (t2, d %+ T1)
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
			    (tr, d %+ T1 %+ d1 $ d2)
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
			    (subst c t1, d %+ T1)
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
			    (subst_i_t i t1, d %+ T1)
			end
		      | t' => raise Fail (mismatch e "(forallI _ : _, _)" t')
		end
	      | Fold (t, e) => 
		(case t of
		     AppRecur t1 =>
		     let val () = is_wftype (skctx, t)
			 val (t', d) = get_type (ctx, e)
			 val () = is_subtype (skctx, t', unroll t1) in
			 (t, d)
		     end
		   | t' => raise Fail (mismatch_anno "((recur (_ :: _) (_ : _), _) _)" t'))
	      | Unfold e =>
		let val (t, d) = get_type (ctx, e) in
		    case t of
	      		AppRecur t1 =>
			(unroll t1, d %+ T1)
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
			let val ctx' as (sctx', (kctx', _)) = add_typing_sk (expr_var, t1') (add_sorting_kt (idx_var, s) ctx)
			    val (t2, d2) = get_type (ctx', e2)
			    val () = is_subtype ((sctx', kctx'), t2, shift_i_t t)
			    val () = is_le (sctx', d2, shift_i_i d) in
			    (t, d1 %+ T1 %+ d)
			end
		      | t1' => raise Fail (mismatch e1 "(ex _ : _, _)" t1')
		end
	      | Let (e1, name, e2) => 
		let val (t1, d1) = get_type (ctx, e1)
		    val (t2, d2) = get_type (add_typing_sk (name, t1) ctx, e2) in
		    (t2, d1 %+ T1 %+ d2)
		end
	      | Fix (t1, d, t2, name, argname, e1) => 
		let val t = Arrow (t1, d, t2)
		    val e = Abs (t1, argname, e1)
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

fun vcgen (sctx : scontext) (kctx : kcontext) (tctx : tcontext) (e : expr) : ((ty * idx) * vc list) result =
    runError (runWriter (fn () => get_type ((sctx, (kctx, tctx)), e))) ()
	     
end

val result = vcgen [] [] [] (Var 0)
val _ =
    case result of
	OK ((t, d), vc) => print ("OK: type=" ^ type_toString t ^ " d=" ^ idx_toString d)
      | Failed msg => print ("Failed: " ^ msg ^ "\n")
