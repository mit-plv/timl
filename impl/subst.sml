structure Subst = struct
open Type
open Expr

(* generic traversers for both 'shift' and 'forget' *)
         
fun on_i_i on_v x n b =
  let
      fun f x n b =
	case b of
	    VarI (y, r) => VarI (on_v x n y, r)
	  | ConstIN n => ConstIN n
	  | ConstIT x => ConstIT x
          | ToReal (i, r) => ToReal (f x n i, r)
	  | BinOpI (opr, d1, d2) => BinOpI (opr, f x n d1, f x n d2)
	  | TTI r => TTI r
	  | TrueI r => TrueI r
	  | FalseI r => FalseI r
  in
      f x n b
  end

fun on_i_p on_i_i x n b =
  let
      fun f x n b =
        case b of
	    True r => True r
	  | False r => False r
          | Not (p, r) => Not (f x n p, r)
	  | BinConn (opr, p1, p2) => BinConn (opr, f x n p1, f x n p2)
	  | BinPred (opr, d1, d2) => BinPred (opr, on_i_i x n d1, on_i_i x n d2)
  in
      f x n b
  end

fun on_i_s on_i_p x n b =
  let
      fun f x n b =
	case b of
	    Basic s => Basic s
	  | Subset (s, name, p) => Subset (s, name, on_i_p (x + 1) n p)
  in
      f x n b
  end

fun on_i_t on_i_i on_i_s x n b =
  let
      fun f x n b =
	case b of
	    Arrow (t1, d, t2) => Arrow (f x n t1, on_i_i x n d, f x n t2)
	  | Unit r => Unit r
	  | Prod (t1, t2) => Prod (f x n t1, f x n t2)
	  | Sum (t1, t2) => Sum (f x n t1, f x n t2)
	  | Uni (name, t) => Uni (name, f x n t)
	  | UniI (s, name, t) => UniI (on_i_s x n s, name, f (x + 1) n t)
	  | ExI (s, name, t) => ExI (on_i_s x n s, name, f (x + 1) n t)
	  | AppRecur (name, ns, t, i, r) => AppRecur (name, map (mapSnd (on_i_s x n)) ns, f (x + length ns) n t, map (on_i_i x n) i, r)
	  | AppV (y, ts, is, r) => AppV (y, map (f x n) ts, map (on_i_i x n) is, r)
	  | Int r => Int r
  in
      f x n b
  end

fun on_t_t on_v x n b =
  let
      fun f x n b =
	case b of
	    Arrow (t1, d, t2) => Arrow (f x n t1, d, f x n t2)
	  | Unit r => Unit r
	  | Prod (t1, t2) => Prod (f x n t1, f x n t2)
	  | Sum (t1, t2) => Sum (f x n t1, f x n t2)
	  | Uni (name, t) => Uni (name, f (x + 1) n t)
	  | UniI (s, name, t) => UniI (s, name, f x n t)
	  | ExI (s, name, t) => ExI (s, name, f x n t)
	  | AppRecur (name, ns, t, i, r) => AppRecur (name, ns, f (x + 1) n t, i, r)
	  | AppV ((y, r1), ts, is, r) => AppV ((on_v x n y, r1), map (f x n) ts, is, r)
	  | Int r => Int r

  in
      f x n b
  end

(* shift *)
	 
fun shiftx_v x n y = 
    if y >= x then
	y + n
    else
	y

fun shiftx_i_i x n b = on_i_i shiftx_v x n b
fun shift_i_i b = shiftx_i_i 0 1 b

fun shiftx_i_p x n b = on_i_p shiftx_i_i x n b
fun shift_i_p b = shiftx_i_p 0 1 b

fun shiftx_i_s x n b = on_i_s shiftx_i_p x n b
fun shift_i_s b = shiftx_i_s 0 1 b

fun shiftx_i_t x n b = on_i_t shiftx_i_i shiftx_i_s x n b
fun shift_i_t b = shiftx_i_t 0 1 b

fun shiftx_t_t x n b = on_t_t shiftx_v x n b
fun shift_t_t b = shiftx_t_t 0 1 b

local
    fun f x n b =
	case b of
	    Var (y, r) => Var (shiftx_v x n y, r)
	  | Abs (t, name, e) => Abs (t, name, f (x + 1) n e)
	  | App (e1, e2) => App (f x n e1, f x n e2)
	  | TT r => TT r
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
	  | Unpack (e1, return, iname, ename, e2) => 
	    Unpack (f x n e1, return, iname, ename, f (x + 1) n e2)
	  | Fix (t, name, e) => 
	    Fix (t, name, f (x + 1) n e)
	  | Let (decs, e, r) =>
	    let fun g (dec, (acc, m)) =
		  let
		      val (dec, m') = f_dec (x + m) n dec
		  in
		      (dec :: acc, m' + m)
		  end
		val (decs, m) = foldl g ([], 0) decs
		val decs = rev decs
	    in
		Let (decs, f (x + m) n e, r)
	    end
	  | Ascription (e, t) => Ascription (f x n e, t)
	  | AscriptionTime (e, d) => AscriptionTime (f x n e, d)
	  | Const n => Const n
	  | BinOp (opr, e1, e2) => BinOp (opr, f x n e1, f x n e2)
	  | AppConstr (cx, ts, is, e) => AppConstr (cx, ts, is, f x n e)
	  | Case (e, return, rules, r) => Case (f x n e, return, map (f_rule x n) rules, r)
	  | Never t => Never t

    and f_dec x n dec =
	case dec of
	    Val (name, e) => (Val (name, f x n e), 1)
          | Datatype a => (Datatype a, 0)

    and f_rule x n (pn, e) =
	let val (_, enames) = ptrn_names pn 
	in
	    (pn, f (x + length enames) n e)
	end
in
fun shiftx_e_e x n b = f x n b
fun shift_e_e b = shiftx_e_e 0 1 b
end

(* forget *)

exception ForgetError of var
(* exception Unimpl *)

fun forget_v x n y = 
    if y >= x + n then
	y - n
    else if y < x then
	y
    else
        raise ForgetError y

fun forget_i_i x n b = on_i_i forget_v x n b
fun forget_i_p x n b = on_i_p forget_i_i x n b
fun forget_i_s x n b = on_i_s forget_i_p x n b
fun forget_i_t x n b = on_i_t forget_i_i forget_i_s x n b
fun forget_t_t x n b = on_t_t forget_v x n b

(* subst *)

exception Error of string

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
	  | ConstIN n => ConstIN n
	  | ConstIT x => ConstIT x
          | ToReal (i, r) => ToReal (f x v i, r)
	  | BinOpI (opr, d1, d2) => BinOpI (opr, f x v d1, f x v d2)
	  | TrueI r => TrueI r
	  | FalseI r => FalseI r
	  | TTI r => TTI r
in
fun substx_i_i x (v : idx) (b : idx) : idx = f x v b
fun subst_i_i v b = substx_i_i 0 v b
end

local
    fun f x v b =
	case b of
	    True r => True r
	  | False r => False r
          | Not (p, r) => Not (f x v p, r)
	  | BinConn (opr,p1, p2) => BinConn (opr, f x v p1, f x v p2)
	  | BinPred (opr, d1, d2) => BinPred (opr, substx_i_i x v d1, substx_i_i x v d2)
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
	  | Unit r => Unit r
	  | Prod (t1, t2) => Prod (f x v t1, f x v t2)
	  | Sum (t1, t2) => Sum (f x v t1, f x v t2)
	  | Uni (name, t) => Uni (name, f x v t)
	  | UniI (s, name, t) => UniI (substx_i_s x v s, name, f (x + 1) (shift_i_i v) t)
	  | ExI (s, name, t) => ExI (substx_i_s x v s, name, f (x + 1) (shift_i_i v) t)
	  | AppRecur (name, ns, t, i, r) =>
	    let val n = length ns in
		AppRecur (name, map (mapSnd (substx_i_s x v)) ns, f (x + n) (shiftx_i_i 0 n v) t, map (substx_i_i x v) i, r)
	    end
	  | AppV (y, ts, is, r) => AppV (y, map (f x v) ts, map (substx_i_i x v) is, r)
	  | Int r => Int r
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
	  | Unit r => Unit r
	  | Prod (t1, t2) => Prod (f x v t1, f x v t2)
	  | Sum (t1, t2) => Sum (f x v t1, f x v t2)
	  | Uni (name, t) => Uni (name, f (x + 1) (shift_t v) t)
	  | UniI (s, name, t) => UniI (s, name, f x (shift_i 1 v) t)
	  | ExI (s, name, t) => ExI (s, name, f x (shift_i 1 v) t)
	  | AppRecur (name, ns, t, i, r) => AppRecur (name, ns, f (x + 1) (shift_i (length ns) (shift_t v)) t, i, r)
	  | AppV ((y, r), ts, is, r2) => 
	    if y = x then
		case v of
		    Type t =>
		    if null ts andalso null is then
			t
		    else
			raise Error "can't be substituted type for this higher-kind type variable"
		  | Recur (name, ns, t) =>
		    if null ts then
			AppRecur (name, ns, t, is, r2)
		    else
			raise Error "can't substitute recursive type definition for this type variable because this application has type arguments"
	    else if y > x then
		AppV ((y - 1, r), map (f x v) ts, is, r2)
	    else
		AppV ((y, r), map (f x v) ts, is, r2)
	  | Int r => Int r

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
fun unroll (name, ns, t, i, _) =
    subst_is_t i (f 0 (shift_i (length ns) (Recur (name, ns, t))) t)
end

fun shiftx_i_c x n ((family, tnames, (name_sorts, t, is)) : constr) : constr =
  let val m = length name_sorts 
  in
      (family,
       tnames, 
       (#1 (foldr (fn ((name, s), (acc, m)) => ((name, shiftx_i_s (x + m) n s) :: acc, m - 1)) ([], m - 1) name_sorts), 
	shiftx_i_t (x + m) n t, 
	map (shiftx_i_i (x + m) n) is))
  end

fun shift_i_c b = shiftx_i_c 0 1 b

fun shiftx_t_c x n ((family, tnames, (name_sorts, t, is)) : constr) : constr =
    (shiftx_v x n family, tnames, (name_sorts, shiftx_t_t (x + length tnames) n t, is))
fun shift_t_c b = shiftx_t_c 0 1 b

local
    fun f x n b =
	case b of
	    ArrowK (is_datatype, n, sorts) => ArrowK (is_datatype, n, map (shiftx_i_s x n) sorts)
in
fun shiftx_i_k x n b = f x n b
fun shift_i_k b = shiftx_i_k 0 1 b
end

end
