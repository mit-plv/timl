structure TypeCheck = struct
open Region
open Type
open Expr

infix 7 $
infix 6 %+
infix 6 %*
infix 4 %<=
infix 3 /\
infix 1 -->
infix 1 <->

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
      | SumCase _ => false
      | Fold (_, e) => is_value e
      | Unfold _ => false
      | AbsT _ => true
      | AppT _ => false
      | AbsI _ => true
      | AppI _ => false
      | Pack (_, _, e) => is_value e
      | Unpack _ => false
      | Fix _ => false
      | Let _ => false
      | Ascription _ => false
      | AscriptionTime _ => false
      | Plus _ => false
      | Const _ => true
      | AppConstr (_, _, _, e) => is_value e
      | Case _ => false
      | Never _ => false

fun shiftx_v x n y = 
    if y >= x then
	y + n
    else
	y

local
    fun f x n b =
	case b of
	    VarI (y, r) => VarI (shiftx_v x n y, r)
	  | T0 => T0
	  | T1 => T1
	  | Tadd (d1, d2) => Tadd (f x n d1, f x n d2)
	  | Tmult (d1, d2) => Tmult (f x n d1, f x n d2)
	  | Tmax (d1, d2) => Tmax (f x n d1, f x n d2)
	  | Tmin (d1, d2) => Tmin (f x n d1, f x n d2)
	  | TTI => TTI
	  | TrueI => TrueI
	  | FalseI => FalseI
	  | Tconst n => Tconst n
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
	  | Iff (p1, p2) => Iff (f x n p1, f x n p2)
	  | TimeLe (d1, d2) => TimeLe (shiftx_i_i x n d1, shiftx_i_i x n d2)
	  | Eq (i1, i2) => Eq (shiftx_i_i x n i1, shiftx_i_i x n i2)
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
	    Arrow (t1, d, t2) => Arrow (f x n t1, shiftx_i_i x n d, f x n t2)
	  | Unit => Unit
	  | Prod (t1, t2) => Prod (f x n t1, f x n t2)
	  | Sum (t1, t2) => Sum (f x n t1, f x n t2)
	  | Uni (name, t) => Uni (name, f x n t)
	  | UniI (s, name, t) => UniI (shiftx_i_s x n s, name, f (x + 1) n t)
	  | ExI (s, name, t) => ExI (shiftx_i_s x n s, name, f (x + 1) n t)
	  | AppRecur (name, ns, t, i) => AppRecur (name, map (mapSnd (shiftx_i_s x n)) ns, f (x + length ns) n t, map (shiftx_i_i x n) i)
	  | AppV (y, ts, is) => AppV (y, map (f x n) ts, map (shiftx_i_i x n) is)
	  | Int => Int
in
fun shiftx_i_t x n b = f x n b
fun shift_i_t b = shiftx_i_t 0 1 b
end

local
    fun f x n b =
	case b of
	    Arrow (t1, d, t2) => Arrow (f x n t1, d, f x n t2)
	  | Unit => Unit
	  | Prod (t1, t2) => Prod (f x n t1, f x n t2)
	  | Sum (t1, t2) => Sum (f x n t1, f x n t2)
	  | Uni (name, t) => Uni (name, f (x + 1) n t)
	  | UniI (s, name, t) => UniI (s, name, f x n t)
	  | ExI (s, name, t) => ExI (s, name, f x n t)
	  | AppRecur (name, ns, t, i) => AppRecur (name, ns, f (x + 1) n t, i)
	  | AppV ((y, r), ts, is) => AppV ((shiftx_v x n y, r), map (f x n) ts, is)
	  | Int => Int

in
fun shiftx_t_t x n b = f x n b
fun shift_t_t b = shiftx_t_t 0 1 b
end

fun shift_pn_i pn i =
    let val (inames, _) = ptrn_names pn
    in
	shiftx_i_i 0 (length inames) i
    end

fun shift_pn_t pn t =
    let val (inames, _) = ptrn_names pn
    in
	shiftx_i_t 0 (length inames) t
    end

local
    fun f x n b =
	case b of
	    Var (y, r) => Var (shiftx_v x n y, r)
	  | Abs (t, name, e) => Abs (t, name, f (x + 1) n e)
	  | App (e1, e2) => App (f x n e1, f x n e2)
	  | TT => TT
	  | Pair (e1, e2) => Pair (f x n e1, f x n e2)
	  | Fst e => Fst (f x n e)
	  | Snd e => Snd (f x n e)
	  | Inl (t, e) => Inl (t, f x n e)
	  | Inr (t, e) => Inr (t, f x n e)
	  | SumCase (e, name1, e1, name2, e2) => 
	    SumCase (f x n e, name1, f (x + 1) n e1, name2, f (x + 1) n e2)
	  | Fold (t, e) => Fold (t, f x n e)
	  | Unfold e => Unfold (f x n e)
	  | AbsT (name, e) => AbsT (name, f x n e)
	  | AppT (e, t) => AppT (f x n e, t)
	  | AbsI (s, name, e) => AbsI (s, name, f x n e)
	  | AppI (e, i) => AppI (f x n e, i)
	  | Pack (t, i, e) => Pack (t, i, f x n e)
	  | Unpack (e1, t, d, iname, ename, e2) => 
	    Unpack (f x n e1, t, d, iname, ename, f (x + 1) n e2)
	  | Fix (t, name, e) => 
	    Fix (t, name, f (x + 1) n e)
	  | Let (e1, name, e2) => Let (f x n e1, name, f (x + 1) n e2)
	  | Ascription (e, t) => Ascription (f x n e, t)
	  | AscriptionTime (e, d) => AscriptionTime (f x n e, d)
	  | Const n => Const n
	  | Plus (e1, e2) => Plus (f x n e1, f x n e2)
	  | AppConstr (cx, ts, is, e) => AppConstr (cx, ts, is, f x n e)
	  | Case (e, t, d, rules) => Case (f x n e, t, d, map (f_rule x n) rules)
	  | Never t => Never t

    and f_rule x n (pn, e) =
	let val (_, enames) = ptrn_names pn 
	in
	    (pn, f (x + length enames) n e)
	end
in
fun shiftx_e_e x n b = f x n b
fun shift_e_e b = shiftx_e_e 0 1 b
end

exception Subst of string

local
    fun f x v b =
	case b of
	    VarI (y, r) =>
	    if y = x then
		v
	    else if y > x then
		VarI (y - 1, r)
	    else
		VarI (y, r)
	  | Tadd (d1, d2) => Tadd (f x v d1, f x v d2)
	  | Tmult (d1, d2) => Tmult (f x v d1, f x v d2)
	  | Tmax (d1, d2) => Tmax (f x v d1, f x v d2)
	  | Tmin (d1, d2) => Tmin (f x v d1, f x v d2)
	  | T0 => T0
	  | T1 => T1
	  | TrueI => TrueI
	  | FalseI => FalseI
	  | TTI => TTI
	  | Tconst n => Tconst n
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
	  | Iff (p1, p2) => Iff (f x v p1, f x v p2)
	  | TimeLe (d1, d2) => TimeLe (substx_i_i x v d1, substx_i_i x v d2)
	  | Eq (i1, i2) => Eq (substx_i_i x v i1, substx_i_i x v i2)
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
	    Arrow (t1, d, t2) => Arrow (f x v t1, substx_i_i x v d, f x v t2)
	  | Unit => Unit
	  | Prod (t1, t2) => Prod (f x v t1, f x v t2)
	  | Sum (t1, t2) => Sum (f x v t1, f x v t2)
	  | Uni (name, t) => Uni (name, f x v t)
	  | UniI (s, name, t) => UniI (substx_i_s x v s, name, f (x + 1) (shift_i_i v) t)
	  | ExI (s, name, t) => ExI (substx_i_s x v s, name, f (x + 1) (shift_i_i v) t)
	  | AppRecur (name, ns, t, i) =>
	    let val n = length ns in
		AppRecur (name, map (mapSnd (substx_i_s x v)) ns, f (x + n) (shiftx_i_i 0 n v) t, map (substx_i_i x v) i)
	    end
	  | AppV (y, ts, is) => AppV (y, map (f x v) ts, map (substx_i_i x v) is)
	  | Int => Int
in
fun substx_i_t x (v : idx) (b : ty) : ty = f x v b
fun subst_i_t (v : idx) (b : ty) : ty = substx_i_t 0 v b
end

local
    (* the substitute can be a type or a recursive type definition *)
    datatype value = 
	     Type of ty
	     | Recur of string * (string * sort) list * ty
    fun f x v (b : ty) : ty =
	case b of
	    Arrow (t1, d, t2) => Arrow (f x v t1, d, f x v t2)
	  | Unit => Unit
	  | Prod (t1, t2) => Prod (f x v t1, f x v t2)
	  | Sum (t1, t2) => Sum (f x v t1, f x v t2)
	  | Uni (name, t) => Uni (name, f (x + 1) (shift_t v) t)
	  | UniI (s, name, t) => UniI (s, name, f x (shift_i 1 v) t)
	  | ExI (s, name, t) => ExI (s, name, f x (shift_i 1 v) t)
	  | AppRecur (name, ns, t, i) => AppRecur (name, ns, f (x + 1) (shift_i (length ns) (shift_t v)) t, i)
	  | AppV ((y, r), ts, is) => 
	    if y = x then
		case v of
		    Type t =>
		    if null ts andalso null is then
			t
		    else
			raise Subst "can't be substituted type for this higher-kind type variable"
		  | Recur (name, ns, t) =>
		    if null ts then
			AppRecur (name, ns, t, is)
		    else
			raise Subst "can't substitute recursive type definition for this type variable because this application has type arguments"
	    else if y > x then
		AppV ((y - 1, r), map (f x v) ts, is)
	    else
		AppV ((y, r), map (f x v) ts, is)
	  | Int => Int

    and shift_i n v =
	case v of
	    Type t => Type (shiftx_i_t 0 n t)
	  | Recur (name, ns, t) => Recur (name, map (mapSnd (shiftx_i_s 0 n)) ns, shiftx_i_t (length ns) n t)
    and shift_t v =
	case v of
	    Type t => Type (shiftx_t_t 1 1 t)
	  | Recur (name, ns, t) => Recur (name, ns, shiftx_t_t 1 1 t)
in

fun substx_t_t x (v : ty) (b : ty) : ty = f x (Type v) b
fun subst_t_t (v : ty) (b : ty) : ty = substx_t_t 0 v b
fun subst_is_t is t = 
    #1 (foldl (fn (i, (t, x)) => (substx_i_t x (shiftx_i_i 0 x i) t, x - 1)) (t, length is - 1) is)
fun subst_ts_t vs b = 
    #1 (foldl (fn (v, (b, x)) => (substx_t_t x (shiftx_t_t 0 x v) b, x - 1)) (b, length vs - 1) vs)
fun unroll (name, ns, t, i) =
    subst_is_t i (f 0 (shift_i (length ns) (Recur (name, ns, t))) t)
end

(*
local
    fun f x (v : ty) (b : ty) : ty =
	case b of
	    Arrow (t1, d, t2) => Arrow (f x v t1, d, f x v t2)
	  | Unit => Unit
	  | Prod (t1, t2) => Prod (f x v t1, f x v t2)
	  | Sum (t1, t2) => Sum (f x v t1, f x v t2)
	  | Uni (name, t) => Uni (name, f (x + 1) (shift_t_t v) t)
	  | UniI (s, name, t) => UniI (s, name, f x (shift_i_t v) t)
	  | ExI (s, name, t) => ExI (s, name, f x (shift_i_t v) t)
	  | AppRecur (name, ns, t, i) => AppRecur (name, ns, f (x + 1) (shiftx_i_t 0 (length ns) (shift_t_t v)) t, i)
	  | AppV (y, ts, is) => 
	    if y = x then
		if null ts andalso null is then
		    v
		else
		    raise Subst "can't be substituted for this higher-kind type variable"
	    else if y > x then
		AppV (y - 1, map (f x v) ts, is)
	    else
		AppV (y, map (f x v) ts, is)
	  | Int => Int
in
fun substx_t_t x (v : ty) (b : ty) : ty = f x v b
fun subst_t_t (v : ty) (b : ty) : ty = substx_t_t 0 v b
end

fun subst_is_t is t = 
    #1 (foldl (fn (i, (t, x)) => (substx_i_t x (shiftx_i_i 0 x i) t, x - 1)) (t, length is - 1) is)

fun subst_ts_t vs b = 
    #1 (foldl (fn (v, (b, x)) => (substx_t_t x (shiftx_t_t 0 x v) b, x - 1)) (b, length vs - 1) vs)

local
    datatype recur = Recur of string * (string * sort) list * ty
    fun shift_i_r n (Recur (name, ns, t)) = Recur (name, map (mapSnd (shiftx_i_s 0 n)) ns, shiftx_i_t (length ns) n t)
    fun shift_t_r (Recur (name, ns, t)) = Recur (name, ns, shiftx_t_t 1 1 t)
    fun f x v (b : ty) : ty =
	case b of
	    Arrow (t1, d, t2) => Arrow (f x v t1, d, f x v t2)
	  | Unit => Unit
	  | Prod (t1, t2) => Prod (f x v t1, f x v t2)
	  | Sum (t1, t2) => Sum (f x v t1, f x v t2)
	  | Uni (name, t) => Uni (name, f (x + 1) (shift_t_r v) t)
	  | UniI (s, name, t) => UniI (s, name, f x (shift_i_r 1 v) t)
	  | ExI (s, name, t) => ExI (s, name, f x (shift_i_r 1 v) t)
	  | AppRecur (name, ns, t, i) => AppRecur (name, ns, f (x + 1) (shift_i_r (length ns) (shift_t_r v)) t, i)
	  | AppV (y, ts, is) => 
	    if y = x then
		if null ts then
		    let val Recur (name, ns, t) = v in
			AppRecur (name, ns, t, is)
		    end
		else
		    raise Subst "can't substitute recursive type for this type variable"
	    else if y > x then
		AppV (y - 1, map (f x v) ts, is)
	    else
		AppV (y, map (f x v) ts, is)
	  | Int => Int

in
fun unroll (name, ns, t, i) =
    subst_is_t i (f 0 (shift_i_r (length ns) (Recur (name, ns, t))) t)
end
*)

fun shiftx_i_c x n (family, tnames, name_sorts, t, is) =
    let val m = length name_sorts 
    in
	(family, tnames, 
	 #1 (foldr (fn ((name, s), (acc, m)) => ((name, shiftx_i_s (x + m) n s) :: acc, m - 1)) ([], m - 1) name_sorts), 
	 shiftx_i_t (x + m) n t, 
	 map (shiftx_i_i (x + m) n) is)
    end
fun shift_i_c b = shiftx_i_c 0 1 b

fun shiftx_t_c x n (family, tnames, name_sorts, t, is) =
    (shiftx_v x n family, tnames, name_sorts, shiftx_t_t (x + length tnames) n t, is)
fun shift_t_c b = shiftx_t_c 0 1 b

local
    fun f x n b =
	case b of
	    ArrowK (n, sorts) => ArrowK (n, map (shiftx_i_s x n) sorts)
in
fun shiftx_i_k x n b = f x n b
fun shift_i_k b = shiftx_i_k 0 1 b
end

(* sorting context *)
type scontext = (string * sort) list * prop list
(* kinding context *)
type kcontext = (string * kind) list 
(* constructor context *)
type ccontext = (string * constr) list
(* typing context *)
type tcontext = (string * ty) list
type context = scontext * kcontext * ccontext * tcontext

fun names (ctx : ('a * 'b) list) = map #1 ctx

fun shiftx_i_ps n ps = 
    map (shiftx_i_p 0 n) ps
fun shiftx_i_ks n ctx = 
    map (mapSnd (shiftx_i_k 0 n)) ctx
fun shiftx_i_cs n ctx = 
    map (mapSnd (shiftx_i_c 0 n)) ctx
fun shiftx_t_cs n ctx = 
    map (mapSnd (shiftx_t_c 0 n)) ctx
fun shiftx_i_ts n ctx = 
    map (mapSnd (shiftx_i_t 0 n)) ctx
fun shiftx_t_ts n ctx = 
    map (mapSnd (shiftx_t_t 0 n)) ctx

fun add_sorting pair (pairs, ps) = (pair :: pairs, shiftx_i_ps 1 ps)
fun add_sorting_sk pair (sctx, kctx) = 
    (add_sorting pair sctx, 
     shiftx_i_ks 1 kctx)
fun add_sorting_skc pair (sctx, kctx, cctx) = 
    (add_sorting pair sctx, 
     shiftx_i_ks 1 kctx,
     shiftx_i_cs 1 cctx)
fun add_sorting_skct pair (sctx, kctx, cctx, tctx) = 
    (add_sorting pair sctx, 
     shiftx_i_ks 1 kctx, 
     shiftx_i_cs 1 cctx, 
     shiftx_i_ts 1 tctx)
(* Within 'pairs', sort depends on previous sort *)
fun add_dep_sortings_skct (pairs', ps') ((pairs, ps), kctx, cctx, tctx) = 
    let val n = length pairs' 
    in
	((pairs' @ pairs, ps' @ shiftx_i_ps n ps), 
	 shiftx_i_ks n kctx, 
	 shiftx_i_cs n cctx, 
	 shiftx_i_ts n tctx)
    end
(* Within 'pairs', sort doesn't depend on previous sort. All of them point to 'sctx'. So the front elements of 'pairs' must be shifted to skip 'pairs' and point to 'sctx' *)
fun add_nondep_sortings pairs sctx = 
    #1 (foldr (fn ((name, s), (ctx, n)) => (add_sorting (name, (shiftx_i_s 0 n s)) ctx, n + 1)) (sctx, 0) pairs)
fun add_nondep_sortings_sk pairs (sctx, kctx) = 
    let val n = length pairs
    in
	(add_nondep_sortings pairs sctx,
	 shiftx_i_ks n kctx)
    end
fun add_nondep_sortings_skc pairs (sctx, kctx, cctx) = 
    let val n = length pairs
    in
	(add_nondep_sortings pairs sctx,
	 shiftx_i_ks n kctx,
	 shiftx_i_ks n cctx)
    end

fun sctx_length (pairs, _) = length pairs
fun sctx_names ((pairs, _) : scontext) = map #1 pairs

fun lookup_sort (n : int) (pairs, _) : sort option = 
    case nth_error pairs n of
	NONE => NONE
      | SOME (_, s) => 
	SOME (shiftx_i_s 0 (n + 1) s)

fun add_kinding pair (kctx : kcontext) = pair :: kctx
fun add_kinding_kc pair (kctx, cctx) = 
    (add_kinding pair kctx, 
     shiftx_t_cs 1 cctx)
fun add_kinding_kct pair (kctx, cctx, tctx) = 
    (add_kinding pair kctx,
     shiftx_t_cs 1 cctx,
     shiftx_t_ts 1 tctx)
fun add_kinding_skct pair (sctx, kctx, cctx, tctx) = 
    (sctx,
     add_kinding pair kctx,
     shiftx_t_cs 1 cctx,
     shiftx_t_ts 1 tctx)
fun add_kinding_sk pair (sctx, kctx) = 
    (sctx, 
     add_kinding pair kctx)

fun lookup_kind (n : int) kctx : kind option = 
    case nth_error kctx n of
	NONE => NONE
      | SOME (_, k) => SOME k

fun add_typing pair tctx = pair :: tctx
fun add_typing_skct pair (sctx, kctx, cctx, tctx) = 
    (sctx, 
     kctx, 
     cctx,
     add_typing pair tctx)

fun lookup (n : int) (ctx : tcontext) : ty option = 
    case nth_error ctx n of
	NONE => NONE
      | SOME (_, t) => SOME t

fun get_base s =
    case s of
	Basic s => s
      | Subset (s, _, _) => s

type bscontext = (string * bsort) list

fun collect (pairs, ps) : bscontext * prop list = 
    let fun get_p s n ps =
	    case s of
		Basic _ => ps
	      | Subset (_, _, p) => shiftx_i_p 0 n p :: ps
	val bctx = map (mapSnd get_base) pairs
	val (ps', _) = foldl (fn ((name, s), (ps, n)) => (get_p s n ps, n + 1)) ([], 0) pairs
    in
	(bctx, ps @ ps')
    end

type vc = bscontext * prop list * prop

fun mem eq x ls = List.exists (fn y => eq (y, x)) ls
fun subset eq a b =
    List.all (fn x => mem eq x b) a
fun diff eq a b = List.filter (fn x => not (mem eq x b)) a

local
    fun find_unique name ls =
	if not (mem op= name ls) then
	    name
	else
	    let fun loop n =
		    let val name' = name ^ str_int n in
			if not (mem op= name' ls) then name' else loop (n + 1)
		    end in
		loop 0
	    end
in
fun unique names = foldr (fn (name, acc) => find_unique name acc :: acc) [] names
end

fun str_vc (ctx : bscontext, ps, p) =
    let val ctx = ListPair.zip (mapFst unique (ListPair.unzip ctx))
	val ctxn = map #1 ctx in
	sprintf "$$===============\n$\n" 
		[join "" (map (fn (name, s) => sprintf "$ : $\n" [name, str_b s]) (rev ctx)), 
		 join "" (map (fn p => str_p ctxn p ^ "\n") ps), 
		 str_p ctxn p]
    end 

(* exception Unimpl *)
exception Impossible of string

exception Error of string

fun runError m _ =
    OK (m ())
    handle
    Error msg => Failed msg

(* use cell to mimic the Writer monad *)
local								    

    val acc = ref ([] : vc list)

    fun tell vc =
	(
	  (* print (sprintf "Output VC:\n$" [str_vc vc]); *)
	  acc := vc :: !acc)

    fun runWriter m _ =
	(acc := []; let val r = m () in (r, !acc) end)

    fun check_length_n (n, ls) =
	if length ls = n then
	    ()
	else
	    raise Error "List length mismatch"

    fun check_length (a, b) =
	if length a = length b then
	    ()
	else
	    raise Error "List length mismatch"

    fun is_le (ctx : scontext, d : idx, d' : idx) =
	let val (bctx, ps) = collect ctx in
	    tell (bctx, ps, d %<= d')
	end
	    
    fun is_eq (ctx : scontext, i : idx, i' : idx, s : sort) = 
	let val (bctx, ps) = collect ctx in
	    tell (bctx, ps, Eq (i, i'))
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
	    tell (bctx, ps, p1 <-> p2)
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
	    raise Error ("Basic sort mismatch: " ^ str_b s ^ " and " ^ str_b s')
		  
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
	    
    fun sort_mismatch ctx i expect have =  "Sort mismatch for " ^ str_i ctx i ^ ": expect " ^ expect ^ " have " ^ str_s ctx have

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
	  | Iff (p1, p2) =>
	    (is_wfprop (ctx, p1);
	     is_wfprop (ctx, p2))
	  | TimeLe (d1, d2) =>
	    (check_sort (ctx, d1, STime);
	     check_sort (ctx, d2, STime))
	  | Eq (i1, i2) =>
	    let val s1 = get_bsort (ctx, i1)
		val s2 = get_bsort (ctx, i2)
	    in
		if s1 = s2 then ()
		else raise Error (sprintf "Base-sorts not equal: $ and $" [str_b s1, str_b s2])
	    end


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
	    VarI (x, _) =>
	    (case lookup_sort x ctx of
      		 SOME s => get_base s
      	       | NONE => raise Error ("Unbound index variable " ^ str_v (sctx_names ctx) x))
      	  | T0 => Time
	  | T1 => Time
	  | Tadd (d1, d2) => 
	    (check_bsort (ctx, d1, Time);
	     check_bsort (ctx, d2, Time);
	     Time)
	  | Tmult (d1, d2) => 
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
	  | TTI => BSUnit
	  | Tconst n => 
	    if n >= 0 then
		Time
	    else
		raise Error ("Time constant must be non-negative")

    fun is_wfsorts (ctx, s) = List.app (fn s => is_wfsort (ctx, s)) s
    fun check_sorts (ctx, i, s) =
	(check_length (i, s);
	 ListPair.app (fn (i, s) => check_sort (ctx, i, s)) (i, s))

    (* k => Type *)
    fun recur_kind k = ArrowK (0, k)

    fun kind_mismatch (ctx as (sctx, kctx)) c expect have =  "Kind mismatch for " ^ str_t ctx c ^ ": expect " ^ expect ^ " have " ^ str_k sctx have

    fun fetch_kind (kctx, a) =
	case lookup_kind a kctx of
      	    SOME k => k
      	  | NONE => raise Error ("Unbound type variable " ^ str_v (names kctx) a)

    fun is_wftype (ctx as (sctx : scontext, kctx : kcontext), c : ty) : unit = 
	let val ctxn as (sctxn, kctxn) = (sctx_names sctx, names kctx)
	(* val () = print (sprintf "Type wellformedness checking: $\n" [str_t ctxn c]) *)
	in
	    case c of
		Arrow (c1, d, c2) => 
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
		is_wftype (add_kinding_sk (name, Type) ctx, c)
	      | UniI (s, name, c) => 
		(is_wfsort (sctx, s);
		 is_wftype (add_sorting_sk (name, s) ctx, c))
	      | ExI (s, name, c) => 
		(is_wfsort (sctx, s);
		 is_wftype (add_sorting_sk (name, s) ctx, c))
	      | AppRecur (nameself, ns, t, i) =>
		let val s = List.map #2 ns in
		    is_wfsorts (sctx, s);
		    is_wftype (add_nondep_sortings_sk (rev ns) (add_kinding_sk (nameself, recur_kind s) ctx), t);
		    check_sorts (sctx, i, s)
		end
	      | AppV ((x, _), ts, is) => 
		(case fetch_kind (kctx, x) of
		     ArrowK (n, sorts) => 
		     (check_length_n (n, ts);
		      check_sorts (sctx, is, sorts)))
	      | Int => ()
	end

    fun not_subtype ctx c c' = str_t ctx c ^ " is not subtype of " ^ str_t ctx c'

    (* is_subtype assumes that the types are already checked against the given kind, so it doesn't need to worry about their well-formedness *)
    fun is_subtype (ctx as (sctx : scontext, kctx : kcontext), c : ty, c' : ty) =
	let val ctxn as (sctxn, kctxn) = (sctx_names sctx, names kctx)
	(* val () = print (sprintf "Subtyping checking: \n$\n<:\n$\n" [str_t ctxn c, str_t ctxn c'])  *)
	in
	    case (c, c') of
		(Arrow (c1, d, c2), Arrow (c1', d', c2')) =>
		(is_subtype (ctx, c1', c1);
		 is_le (sctx, d, d');
		 is_subtype (ctx, c2, c2'))
	      | (Unit, Unit) => ()
	      | (Prod (c1, c2), Prod (c1', c2')) =>
		(is_subtype (ctx, c1, c1');
		 is_subtype (ctx, c2, c2'))
	      | (Sum (c1, c2), Sum (c1', c2')) => 
		(is_subtype (ctx, c1, c1');
		 is_subtype (ctx, c2, c2'))
	      | (Uni (name, c), Uni (_, c')) => 
		is_subtype (add_kinding_sk (name, Type) ctx, c, c')
	      | (UniI (s, name, c), UniI (s', _, c')) => 
		(is_eqvsort (sctx, s, s');
		 is_subtype (add_sorting_sk (name, s) ctx, c, c'))
	      | (ExI (s, name, c), ExI (s', _, c')) => 
		(is_eqvsort (sctx, s, s');
		 is_subtype (add_sorting_sk (name, s) ctx, c, c'))
	      (* currently don't support subtyping for recursive types, so they must be equivalent *)
	      | (AppRecur (nameself, ns, t, i), AppRecur (_, ns', t', i')) => 
		let val s = List.map #2 ns
		    val s' = List.map #2 ns'
		    val () = is_eqvsorts (sctx, s, s')
		    val () = is_eqs (sctx, i, i', s)
		    val ctx' = add_nondep_sortings_sk (rev ns) (add_kinding_sk (nameself, recur_kind s) ctx) in
		    is_eqvtype (ctx', t, t')
		end
	      | (AppV ((a, _), ts, is), AppV ((a', _), ts', is')) => 
		if a = a' then
		    (app (fn (t, t') => is_eqvtype (ctx, t, t')) (ListPair.zip (ts, ts'));
		     case fetch_kind (kctx, a) of
			 ArrowK (_, sorts) =>
			 is_eqs (sctx, is, is', sorts))
		else
		    raise Error (not_subtype ctxn c c')
	      | (Int, Int) => ()
	      | _ => raise Error (not_subtype ctxn c c')
	end

    and is_eqvtype (kctx, c, c') =
	(is_subtype (kctx, c, c');
	 is_subtype (kctx, c', c))

    fun no_join ctx c c' = "Cannot find a join (minimal supertype) of " ^ str_t ctx c ^ " and " ^ str_t ctx c'
    fun no_meet ctx c c' = "Cannot find a meet (maximal subtype) of " ^ str_t ctx c ^ " and " ^ str_t ctx c'

    (* c and c' are already checked for wellformedness *)
    fun join_type (ctx as (sctx : scontext, kctx : kcontext), c : ty, c' : ty) : ty = 
	let val ctxn as (sctxn, kctxn) = (sctx_names sctx, names kctx)
	in
	    case (c, c') of
		(Arrow (c1, d, c2), Arrow (c1', d', c2')) => 
		let val c1'' = meet (ctx, c1, c1') 
		    val d'' = d $ d' 
		    val c2'' = join_type (ctx, c2, c2') in
		    Arrow (c1'', d'', c2'')
		end
	      | (Unit, Unit) => Unit
	      | (Prod (c1, c2), Prod (c1', c2')) => 
		let val c1'' = join_type (ctx, c1, c1') 
		    val c2'' = join_type (ctx, c2, c2') in
		    Prod (c1'', c2'')
		end
	      | (Sum (c1, c2), Sum (c1', c2')) => 
		let val c1'' = join_type (ctx, c1, c1') 
		    val c2'' = join_type (ctx, c2, c2') in
		    Sum (c1'', c2'')
		end
	      | (Uni (name, t), Uni (_, t')) => 
		let val t'' = join_type (add_kinding_sk (name, Type) ctx, t, t') in
		    Uni (name, t'')
		end
	      | (UniI (s, name, t), UniI (s', _, t')) => 
		let val () = is_eqvsort (sctx, s, s')
		    val t'' = join_type (add_sorting_sk (name, s) ctx, t, t') in
		    UniI (s, name, t'')
		end
	      | (ExI (s, name, t), ExI (s', _, t')) => 
		let val () = is_eqvsort (#1 ctx, s, s')
		    val t'' = join_type (add_sorting_sk (name, s) ctx, t, t') in
		    ExI (s, name, t'')
		end
	      (* currently don't support join for recursive types, so they must be equivalent *)
	      | (AppRecur _, AppRecur _) => 
		(is_eqvtype (ctx, c, c');
		 c)
	      | (AppV _, AppV _) => 
		(is_eqvtype (ctx, c, c');
		 c)
	      | (Int, Int) => Int
	      | _ => raise Error (no_join ctxn c c')
	end

    and meet (ctx as (sctx : scontext, kctx : kcontext), c : ty, c' : ty) : ty = 
	let val ctxn as (sctxn, kctxn) = (sctx_names sctx, names kctx)
	in
	    case (c, c') of
		(Arrow (c1, d, c2), Arrow (c1', d', c2')) => 
		let val c1'' = join_type (ctx, c1, c1') 
		    val d'' = Tmin (d, d')
		    val c2'' = meet (ctx, c2, c2') in
		    Arrow (c1'', d'', c2'')
		end
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
		let val t'' = meet (add_kinding_sk (name, Type) ctx, t, t') in
		    Uni (name, t'')
		end
	      | (UniI (s, name, t), UniI (s', _, t')) => 
		let val () = is_eqvsort (sctx, s, s')
		    val t'' = meet (add_sorting_sk (name, s) ctx, t, t') in
		    UniI (s, name, t'')
		end
	      | (ExI (s, name, t), ExI (s', _, t')) => 
		let val () = is_eqvsort (#1 ctx, s, s')
		    val t'' = meet (add_sorting_sk (name, s) ctx, t, t') in
		    ExI (s, name, t'')
		end
	      (* currently don't support meet for recursive types, so they must be equivalent *)
	      | (AppRecur _, AppRecur _) => 
		(is_eqvtype (ctx, c, c');
		 c)
	      | (AppV _, AppV _) => 
		(is_eqvtype (ctx, c, c');
		 c)
	      | (Int, Int) => Int
	      | _ => raise Error (no_meet ctxn c c')
	end

    val Cover_False = []
    fun Cover_Or (a, b) = a @ b
    fun Cover_Constr e = [e]

    fun get_family ((x, _, _, _, _) : constr) = x

    fun get_family_members cctx x =
	List.mapPartial (fn (n, (_, c)) => if get_family c = x then SOME n else NONE) (add_idx cctx)

    (* covers should already have type t *)
    fun check_redundancy ((_, _, cctx), t, prev, this) =
	if not (subset op= this prev) then ()
	else raise Error (sprintf "Redundant pattern $ after [$]" [join ", " (map (str_v (names cctx)) this), join ", " (map (str_v (names cctx)) prev)])

    fun check_exhaustive ((_, _, cctx), t, cover) =
	case t of
	    AppV ((family, _), _, _) =>
	    let val all = get_family_members cctx family
		val missed = diff op= all cover
	    in
		if missed = [] then ()
		else raise Error (sprintf "Not exhaustive, missing these constructors: $" [join ", " (map (str_v (names cctx)) missed)])
	    end
	  | _ => raise Impossible "shouldn't check exhaustiveness under this type"

    fun fetch_constr (ctx, x) =
	case nth_error ctx x of
	    SOME (name, c) => (name, c)
	  | NONE => raise Error (sprintf "Unbound constructor $" [str_v (names ctx) x])

    fun fetch_constr_type (ctx, cx) =
	let val (cname, (family, tnames, ns, t, is)) = fetch_constr (ctx, cx)
	    val ts = (map (fn x => VarT (x, dummy_region)) o rev o range o length) tnames
	    val t = Arrow (t, T0, AppV ((shiftx_v 0 (length tnames) family, dummy_region), ts, is))
	    val t = foldr (fn ((name, s), t) => UniI (s, name, t)) t ns
	    val t = foldr Uni t tnames
	in
	    (cname, t)
	end

    (* t is already checked for wellformedness *)
    fun match_ptrn (ctx as (sctx : scontext, kctx : kcontext, cctx : ccontext), pn : ptrn, t) =
	let val skctxn as (sctxn, kctxn) = (sctx_names sctx, names kctx)
	in
	    case (pn, t) of
		(Constr ((cx, _), inames, ename), AppV ((x, _), ts, is)) =>
		let val (_, c as (x', tnames, ns, t1, is')) = fetch_constr (cctx, cx)
		in
		    if x' = x then
			let val () = check_length (tnames, ts)
			    val t1 = subst_ts_t ts t1
			    val is = map (shiftx_i_i 0 (length ns)) is
			    val () = check_length (is', is)
			    val ps = map Eq (ListPair.zip (is', is))
			    val () = check_length (inames, ns)
			in
			    ((rev (ListPair.zip (inames, #2 (ListPair.unzip ns))), ps), (ename, t1), Cover_Constr cx)
			end
		    else
			raise Error (sprintf "Type of constructor $ doesn't match datatype:\n  expect: $\n  got: $\n" [str_v (names cctx) cx, str_v kctxn x, str_v kctxn x'])
		end
	      | _ => raise Error (sprintf "Pattern $ doesn't match type $" [str_pn (names cctx) pn, str_t skctxn t])
	end

    fun mismatch (ctx as (sctx, kctx, _, _)) e expect have =  
	sprintf "Type mismatch for $:\n  expect: $\n  got: $\n" [str_e ctx e, expect, str_t (sctx, kctx) have]
    fun mismatch_anno ctx expect have =  "Type annotation mismatch: expect " ^ expect ^ " have " ^ str_t ctx have

    fun check_fix_body e =
	case e of
    	    AbsI (_, _, e') => check_fix_body e'
    	  | Abs _ => ()
    	  | _ => raise Error "The body of fixpoint must have the form (fn [(_ :: _) ... (_ :: _)] (_ : _) => _)"

    fun get_type (ctx as (sctx : scontext, kctx : kcontext, cctx : ccontext, tctx : tcontext), e : expr) : ty * idx =
	let val skctx = (sctx, kctx) 
	    val ctxn as (sctxn, kctxn, cctxn, tctxn) = (sctx_names sctx, names kctx, names cctx, names tctx) 
	    val skctxn = (sctxn, kctxn)
	    (* val () = print (sprintf "Typing $\n" [str_e ctxn e]) *)
	    val (t, d) =
		case e of
		    Var (x, _) =>
		    (case lookup x tctx of
      			 SOME t => (t, T0)
      		       | NONE => raise Error ("Unbound variable " ^ str_v tctxn x))
		  | App (e1, e2) =>
		    let val (t1, d1) = get_type (ctx, e1) in
    			case t1 of
    			    Arrow (t2, d, t) =>
    			    let val (t2', d2) = get_type (ctx, e2) 
				val () = is_subtype (skctx, t2', t2) in
    				(t, d1 %+ d2 %+ T1 %+ d) 
			    end
    			  | t1' =>  raise Error (mismatch ctxn e1 "(_ -- _ -> _)" t1')
		    end
		  | Abs (t, varname, e) => 
		    let val () = is_wftype (skctx, t)
			val (t1, d) = get_type (add_typing_skct (varname, t) ctx, e) in
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
			    Prod (t1, t2) => (t1, d)
			  | t' => raise Error (mismatch ctxn e "(_ * _)" t')
		    end
		  | Snd e => 
		    let val (t, d) = get_type (ctx, e) in 
			case t of
			    Prod (t1, t2) => (t2, d)
			  | t' => raise Error (mismatch ctxn e "(_ * _)" t')
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
		  | SumCase (e, name1, e1, name2, e2) => 
		    let val (t, d) = get_type (ctx, e) in
			case t of
			    Sum (t1, t2) => 
			    let val (tr1, d1) = get_type (add_typing_skct (name1, t1) ctx, e1)
				val (tr2, d2) = get_type (add_typing_skct (name2, t2) ctx, e2)
				val tr = join_type (skctx, tr1, tr2) in
				(tr, d %+ d1 $ d2)
			    end
			  | t' => raise Error (mismatch ctxn e "(_ + _)" t')
		    end
		  | AbsT (name, e) => 
		    if is_value e then
			let val (t, _) = get_type (add_kinding_skct (name, Type) ctx, e) in
			    (Uni (name, t), T0)
			end 
		    else
			raise Error ("The body of a universal abstraction must be a value")
		  | AppT (e, c) =>
		    let val (t, d) = get_type (ctx, e) in
			case t of
			    Uni (_, t1) => 
			    let val () = is_wftype (skctx, c) in
				(subst_t_t c t1, d)
			    end
			  | t' => raise Error (mismatch ctxn e "(forall _ : _, _)" t')
		    end
		  | AbsI (s, name, e) => 
		    if is_value e then
			let val () = is_wfsort (sctx, s)
			    val (t, _) = get_type ((add_sorting_skct (name, s) ctx), e) in
			    (UniI (s, name, t), T0)
			end 
		    else
			raise Error ("The body of a universal abstraction must be a value")
		  | AppI (e, i) =>
		    let val (t, d) = get_type (ctx, e) in
			case t of
			    UniI (s, _, t1) => 
			    let val () = check_sort (sctx, i, s) in
				(subst_i_t i t1, d)
			    end
			  | t' => raise Error (mismatch ctxn e "(forallI _ : _, _)" t')
		    end
		  | Fold (t, e) => 
		    (case t of
			 AppRecur t1 =>
			 let val () = is_wftype (skctx, t)
			     val (t', d) = get_type (ctx, e)
			     val () = is_subtype (skctx, t', unroll t1) in
			     (t, d)
			 end
		       | t' => raise Error (mismatch_anno skctxn "((recur (_ :: _) (_ : _), _) _)" t'))
		  | Unfold e =>
		    let val (t, d) = get_type (ctx, e) in
			case t of
	      		    AppRecur t1 =>
			    (unroll t1, d)
			  | t' => raise Error (mismatch ctxn e "((recur (_ :: _) (_ : _), _) _)" t')
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
		       | t' => raise Error (mismatch_anno skctxn "(ex _ : _, _)" t'))
		  | Unpack (e1, t, d, idx_var, expr_var, e2) => 
		    let val () = is_wftype (skctx, t)
			val () = check_sort (sctx, d, STime)
			val (t1, d1) = get_type (ctx, e1) in
			case t1 of
			    ExI (s, _, t1') => 
			    let val ctx' = add_typing_skct (expr_var, t1') (add_sorting_skct (idx_var, s) ctx)
				val () = check_type (ctx', e2, shift_i_t t, shift_i_i d)
			    in
				(t, d1 %+ d)
			    end
			  | t1' => raise Error (mismatch ctxn e1 "(ex _ : _, _)" t1')
		    end
		  | Let (e1, name, e2) => 
		    let val (t1, d1) = get_type (ctx, e1)
			val (t2, d2) = get_type (add_typing_skct (name, t1) ctx, e2) in
			(t2, d1 %+ d2)
		    end
		  | Fix (t, name, e) => 
		    let val () = check_fix_body e
			val () = is_wftype (skctx, t)
			val (t1, _) = get_type (add_typing_skct (name, t) ctx, e)
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
		  | Plus (e1, e2) =>
		    let val (t1, d1) = get_type (ctx, e1)
			val (t2, d2) = get_type (ctx, e2) in
			is_subtype (skctx, t1, Int);
			is_subtype (skctx, t2, Int);
			(Int, d1 %+ d2 %+ T1)
		    end
		  | Const _ => 
		    (Int, T0)
		  | AppConstr ((cx, _), ts, is, e) => 
		    let val (cname, tc) = fetch_constr_type (cctx, cx)
			val () = is_wftype (skctx, tc)
			val (_, d) = get_type (ctx, e)
			(* delegate to checking e' *)
			val f = Var (0, dummy_region)
			val f = foldl (fn (t, e) => AppT (e, t)) f ts
			val f = foldl (fn (i, e) => AppI (e, i)) f is
			val e' = App (f, shift_e_e e)
			val (t, _) = get_type (add_typing_skct (cname, tc) ctx, e') 
		    in
			(* constructor application doesn't incur count *)
			(t, d)
		    end
		  | Case (e, t, d, rules) => 
		    let val () = is_wftype (skctx, t)
			val () = check_sort (sctx, d, STime)
			val (t1, d1) = get_type (ctx, e)
		    in
			check_rules (ctx, rules, (t1, d, t));
			(t, d1 %+ d)
		    end
		  | Never t => 
		    (is_wftype (skctx, t);
		     is_true (sctx, False);
		     (t, T0))
	(* val () = print (sprintf "  type: $ [for $]\n  time: $\n" [str_t skctxn t, str_e ctxn e, str_i sctxn d]) *)
	in
	    (t, d)
	end

    and check_type (ctx as (sctx, kctx, cctx, tctx), e, t, d) =
	let 
	    val ctxn as (sctxn, kctxn, cctxn, tctxn) = (sctx_names sctx, names kctx, names cctx, names tctx) 
	    (* val () = print (sprintf "Type checking $ against $ and $\n" [str_e ctxn e, str_t (sctxn, kctxn) t, str_i sctxn d]) *)
	    val (t', d') = get_type (ctx, e)
	in
	    is_subtype ((sctx, kctx), t', t);
	    is_le (sctx, d', d)
	end

    and check_rules (ctx as (sctx, kctx, cctx, tctx), rules, t as (t1, _, _)) =
	let val skcctx = (sctx, kctx, cctx) 
	    fun f (rule, acc) =
		let val cover = check_rule (ctx, rule, t)
		    val () = check_redundancy (skcctx, t1, acc, cover)
		in
		    Cover_Or (cover, acc)
		end 
	    val cover = foldl f Cover_False rules
	in
	    check_exhaustive (skcctx, t1, cover)
	end

    and check_rule (ctx as (sctx, kctx, cctx, tctx), (pn, e), t as (t1, d, t2)) =
	let val skcctx = (sctx, kctx, cctx) 
	    val (sctx', nt, cover) = match_ptrn (skcctx, pn, t1)
	    val ctx' = add_typing_skct nt (add_dep_sortings_skct sctx' ctx)
	in
	    check_type (ctx', e, shift_pn_t pn t2, shift_pn_i pn d);
	    cover
	end

in								     

fun vcgen ctx e : (ty * idx) * vc list =
    runWriter (fn () => get_type (ctx, e)) ()
	     
fun vcgen_opt ctx e : ((ty * idx) * vc list, string) result =
    runError (fn () => vcgen ctx e) ()
	     
end

fun eq_i i i' =
    case (i, i') of
        (VarI (x, _), VarI (x', _)) => x = x'
      | (T0, T0) => true
      | (T1, T1) => true
      | (Tconst n, Tconst n') => n = n'
      | (Tadd (i1, i2), Tadd (i1', i2')) => eq_i i1 i1' andalso eq_i i2 i2'
      | (Tmult (i1, i2), Tmult (i1', i2')) => eq_i i1 i1' andalso eq_i i2 i2'
      | (Tmax (i1, i2), Tmax (i1', i2')) => eq_i i1 i1' andalso eq_i i2 i2'
      | (Tmin (i1, i2), Tmin (i1', i2')) => eq_i i1 i1' andalso eq_i i2 i2'
      | (TrueI, TrueI) => true
      | (FalseI, FalseI) => true
      | (TTI, TTI) => true
      | _ => false

fun eq_p p p' =
    case (p, p') of
        (True, True) => true
      | (False, False) => true
      | (And (p1, p2), And (p1', p2')) => eq_p p1 p1' andalso eq_p p2 p2'
      | (Or (p1, p2), Or (p1', p2')) => eq_p p1 p1' andalso eq_p p2 p2'
      | (Imply (p1, p2), Imply (p1', p2')) => eq_p p1 p1' andalso eq_p p2 p2'
      | (Iff (p1, p2), Iff (p1', p2')) => eq_p p1 p1' andalso eq_p p2 p2'
      | (Eq (i1, i2), Eq (i1', i2')) => eq_i i1 i1' andalso eq_i i2 i2'
      | (TimeLe (i1, i2), TimeLe (i1', i2')) => eq_i i1 i1' andalso eq_i i2 i2'
      | _ => false

local
    fun solver (ctx, ps, p) =
	isSome (List.find (eq_p p) ps) orelse
	case p of
	    Imply (p1, p2) => solver (ctx, p1 :: ps, p2)
	  | Iff (p1, p2) => solver (ctx, p1 :: ps, p2) andalso solver (ctx, p2 :: ps, p1)
	  | And (p1, p2) => solver (ctx, ps, p1) andalso solver (ctx, ps, p1)
	  | Or (p1, p2) => solver (ctx, ps, p1) orelse solver (ctx, ps, p1)
	  | True => true
	  | Eq (i1, i2) => eq_i i1 i2
	  | TimeLe (i1, i2) => eq_i i1 i2
	  | _ => false

in
fun trivial_solver vcs = List.filter (fn vc => solver vc = false) vcs
end

local
    fun passi i =
	case i of
	    Tmax (i1, i2) =>
	    if eq_i i1 i2 then
		(true, i1)
	    else
		let val (b1, i1) = passi i1
		    val (b2, i2) = passi i2 in
		    (b1 orelse b2, Tmax (i1, i2))
		end
	  | Tmin (i1, i2) =>
	    if eq_i i1 i2 then
		(true, i1)
	    else
		let val (b1, i1) = passi i1
		    val (b2, i2) = passi i2 in
		    (b1 orelse b2, Tmin (i1, i2))
		end
	  | Tadd (i1, i2) => 
	    if eq_i i1 T0 then (true, i2)
	    else if eq_i i2 T0 then (true, i1)
	    else
		let val (b1, i1) = passi i1
		    val (b2, i2) = passi i2 in
		    (b1 orelse b2, Tadd (i1, i2))
		end
	  | Tmult (i1, i2) => 
	    if eq_i i1 T0 then (true, T0)
	    else if eq_i i2 T0 then (true, T0)
	    else if eq_i i1 T1 then (true, i2)
	    else if eq_i i2 T1 then (true, i1)
	    else
		let val (b1, i1) = passi i1
		    val (b2, i2) = passi i2 in
		    (b1 orelse b2, Tmult (i1, i2))
		end
	  | _ => (false, i)
		     
    fun passp p = 
	case p of
	    And (p1, p2) => 
	    let val (b1, p1) = passp p1
		val (b2, p2) = passp p2 in
		(b1 orelse b2, And (p1, p2))
	    end
	  | Or (p1, p2) => 
	    let val (b1, p1) = passp p1
		val (b2, p2) = passp p2 in
		(b1 orelse b2, Or (p1, p2))
	    end
	  | Imply (p1, p2) => 
	    let val (b1, p1) = passp p1
		val (b2, p2) = passp p2 in
		(b1 orelse b2, Imply (p1, p2))
	    end
	  | Iff (p1, p2) => 
	    let val (b1, p1) = passp p1
		val (b2, p2) = passp p2 in
		(b1 orelse b2, Iff (p1, p2))
	    end
	  | Eq (i1, i2) => 
	    let val (b1, i1) = passi i1
		val (b2, i2) = passi i2 in
		(b1 orelse b2, Eq (i1, i2))
	    end
	  | TimeLe (i1, i2) => 
	    let val (b1, i1) = passi i1
		val (b2, i2) = passi i2 in
		(b1 orelse b2, TimeLe (i1, i2))
	    end
	  | _ => (false, p)
    fun until_unchanged f a = 
	let fun loop a =
		let val (changed, a') = f a in
		    if changed then loop a'
		    else a
		end in
	    loop a
	end
in
val simp_p = until_unchanged passp
val simp_i = until_unchanged passi
fun simplify (ctx, ps, p) = (ctx, map simp_p ps, simp_p p)
end

fun simp_s s =
    case s of
	Basic b => Basic b
      | Subset (b, name, p) => Subset (b, name, simp_p p)

local
    fun f t =
	case t of
	    Arrow (t1, d, t2) => Arrow (f t1, simp_i d, f t2)
	  | Prod (t1, t2) => Prod (f t1, f t2)
	  | Sum (t1, t2) => Sum (f t1, f t2)
	  | Unit => Unit
	  | AppRecur (name, ns, t, is) => AppRecur (name, map (mapSnd simp_s) ns, f t, map simp_i is)
	  | AppV (x, ts, is) => AppV (x, map f ts, map simp_i is)
	  | Uni (name, t) => Uni (name, f t)
	  | UniI (s, name, t) => UniI (simp_s s, name, f t)
	  | ExI (s, name, t) => ExI (simp_s s, name, f t)
	  | Int => Int

in
val simp_t = f
end

fun typecheck (ctx as (sctx, kctx, cctx, tctx) : context) e : (ty * idx) * vc list =
    let 
	val ctxn as (sctxn, kctxn, cctxn, tctxn) = (sctx_names sctx, names kctx, names cctx, names tctx)
	val ((t, d), vcs) = vcgen ctx e
	(* val () = print "Simplifying and applying trivial solver ...\n" *)
	val vcs = trivial_solver vcs
	val vcs = map simplify vcs
	val vcs = trivial_solver vcs
	val t = simp_t t
	val d = simp_i d
    in
        ((t, d), vcs)
    end

fun typecheck_opt ctx e =
    runError (fn () => typecheck ctx e) ()

end
			  
