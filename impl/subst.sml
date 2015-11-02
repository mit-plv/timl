structure Subst = struct
open Expr

(* generic traversers for both 'shift' and 'forget' *)
         
fun on_i_i on_v on_invis expand_i x n b =
  let
      fun f x n b =
	case b of
	    VarI (y, r) => VarI (on_v x n y, r)
	  | ConstIN n => ConstIN n
	  | ConstIT x => ConstIT x
          | UnOpI (opr, i, r) => UnOpI (opr, f x n i, r)
	  | BinOpI (opr, i1, i2) => BinOpI (opr, f x n i1, f x n i2)
	  | TTI r => TTI r
	  | TrueI r => TrueI r
	  | FalseI r => FalseI r
          | UVarI (invis, uvar) =>
            (case !uvar of
                 Refined i => 
                 f x n (expand_i invis i)
               | Fresh _ => 
                 UVarI (on_invis x n invis, uvar)
            )
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

fun on_i_ibind f x n bind =
    case bind of
        BindI (name, inner) => BindI (name, f (x + 1) n inner)

fun on_t_ibind f x n bind =
    case bind of
        BindI (name, inner) => BindI (name, f x n inner)

fun on_i_s on_i_p x n b =
  let
      fun f x n b =
	case b of
	    Basic s => Basic s
	  | Subset (s, bind) => Subset (s, on_i_ibind on_i_p x n bind)
  in
      f x n b
  end

fun on_i_s_ref on_invis expand_s x n (invis, uvar) =
    case !uvar of
        Refined i => 
        f x n (expand_s invis i)
      | Fresh _ => 
        UVarI (on_invis x n invis, uvar)

fun on_i_mt on_i_i on_i_s on_i_s_ref on_invis expand_mt x n b =
  let
      fun f x n b =
	case b of
	    Arrow (t1, d, t2) => Arrow (f x n t1, on_i_i x n d, f x n t2)
	  | Unit r => Unit r
	  | Prod (t1, t2) => Prod (f x n t1, f x n t2)
	  | Sum (t1, t2) => Sum (f x n t1, f x n t2)
	  | UniI (s, bind) => UniI (on_i_s_ref x n s, on_i_ibind f x n bind)
	  | ExI (s, bind) => ExI (on_i_s_ref x n s, on_i_ibind f x n bind)
	  | AppV (y, ts, is, r) => AppV (y, map (f x n) ts, map (on_i_i x n) is, r)
	  | Int r => Int r
          | UVar (invis as (invisi invist), uvar) =>
            (case !uvar of
                 Refined t => 
                 f x n (expand_mt invis t)
               | Fresh _ => 
                 UVar ((on_invis x n invisi, invist), uvar)
            )
  in
      f x n b
  end

fun on_i_t on_i_mt x n b =
  let
      fun f x n b =
	case b of
	    Mono t => Mono (on_i_mt x n t)
	  | Uni (name, t) => Uni (name, f x n t)
  in
      f x n b
  end

fun on_t_ibind f x n bind =
    case bind of
        BindI (name, inner) => BindI (name, f x n inner)

fun on_t_mt on_v x n b =
  let
      fun f x n b =
	case b of
	    Arrow (t1, d, t2) => Arrow (f x n t1, d, f x n t2)
	  | Unit r => Unit r
	  | Prod (t1, t2) => Prod (f x n t1, f x n t2)
	  | Sum (t1, t2) => Sum (f x n t1, f x n t2)
	  | UniI (s, bind) => UniI (s, on_t_ibind f x n bind)
	  | ExI (s, bind) => ExI (s, on_t_ibind f x n bind)
	  | AppRecur (name, ns, t, i, r) => AppRecur (name, ns, f (x + 1) n t, i, r)
	  | AppV ((y, r1), ts, is, r) => AppV ((on_v x n y, r1), map (f x n) ts, is, r)
	  | Int r => Int r
          | UVar (invis as (invisi invist), uvar) =>
            (case !uvar of
                 Refined t => 
                 f x n (expand_mt invis t)
               | Fresh _ => 
                 UVar ((invisi, on_invis x n invist), uvar)
            )
  in
      f x n b
  end

fun on_t_t on_t_mt x n b =
  let
      fun f x n b =
	case b of
	    Mono t => Mono (on_t_mt x n t)
	  | Uni (name, t) => Uni (name, f (x + 1) n t)
  in
      f x n b
  end

(* shift *)
	 
fun shiftx_v x n y = 
    if y >= x then
	y + n
    else
	y

fun shiftx_invis x n invis = 
    let 
        fun f ((off, len), (acc, (x, n))) =
            if n = 0 then
                ((off, len) :: acc, (0, 0))
            else if x < off then
                ((off - x, len) :: (x, n) :: acc, (0, 0))
            else if x <= off + len then
                ((off, len + n) :: acc, (0, 0))
            else 
                ((off, len) :: acc, (x - off - len, n))
    in
        (rev o fst o fold f ([], (x, n))) invis
    end

fun expand shift invis b = (fst o foldl (fn ((off, len), (b, base)) => (shift (base + off) len b, base + off + len)) (b, 0)) invis

fun expand_i invis b = expand shiftx_i_i invis b
and shiftx_i_i x n b = on_i_i shiftx_v shiftx_invis expand_i x n b
fun shift_i_i b = shiftx_i_i 0 1 b

fun shiftx_i_p x n b = on_i_p shiftx_i_i x n b
fun shift_i_p b = shiftx_i_p 0 1 b

fun shiftx_i_s x n b = on_i_s shiftx_i_p x n b
fun shift_i_s b = shiftx_i_s 0 1 b

fun expand_s invis b = expand shiftx_i_s invis b
and shiftx_i_s_ref x n b = on_i_s_ref shiftx_invis expand_s x n b

fun expand_mt (invisi, invist) b = (expand shiftx_i_mt invisi o expand shiftx_t_mt invist) b
and shiftx_i_mt x n b = on_i_mt shiftx_i_i shiftx_i_s shiftx_i_s_ref shiftx_invis expand_mt x n b
and shiftx_t_mt x n b = on_t_mt shiftx_v shiftx_invis expand_mt x n b
fun shift_i_mt b = shiftx_i_mt 0 1 b
fun shift_t_mt b = shiftx_t_mt 0 1 b

fun shiftx_i_t x n b = on_i_t shiftx_i_mt x n b
fun shift_i_t b = shiftx_i_t 0 1 b

fun shiftx_t_t x n b = on_t_t shiftx_t_mt x n b
fun shift_t_t b = shiftx_t_t 0 1 b

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

fun forget_invis x n invis = 
    let 
        fun f ((off, len), (acc, (x, n))) =
            if n = 0 then
                ((off, len) :: acc, (0, 0))
            else if x < off then
                raise ForgetError x
            else if x <= off + len then
                if x + n <= off + len then
                    ((off, len - n) :: acc, (0, 0))
                else
                    raise ForgetError (off + len)
            else 
                ((off, len) :: acc, (x - off - len, n))
    in
        (rev o fst o fold f ([], (x, n))) invis
    end

fun forget_i_i x n b = on_i_i forget_v forget_invis expand_i x n b
fun forget_i_p x n b = on_i_p forget_i_i x n b
fun forget_i_s x n b = on_i_s forget_i_p x n b
and forget_i_s_ref x n b = on_i_s_ref forget_invis expand_s x n b
fun forget_i_mt x n b = on_i_mt forget_i_i forget_i_s forget_i_s_ref forget_invis expand_mt x n b
fun forget_t_mt x n b = on_t_mt forget_v forget_invis expand_mt x n b
fun forget_i_t x n b = on_i_t forget_i_mt x n b
fun forget_t_t x n b = on_t_t forget_t_mt x n b

fun shrink forget invis b = (fst o foldl (fn ((off, len), (b, base)) => (forget (base + off) len b, base + off)) (b, 0)) invis

fun shrink_i invis b = shrink forget_i_i invis b
fun shrink_s invis b = shrink forget_i_s invis b
fun shrink_mt (invisi, invist) b = (shrink forget_i_mt invisi o shrink forget_t_mt invist) b

(* shift_e_e *)

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
          | UnOpI (opr, i, r) => UnOpI (opr, f x v i, r)
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

(* mimic type class *)
type 'a shiftable = {
    shift_i : int -> 'a -> 'a,
    shift_t : int -> 'a -> 'a
}

fun shift_id n v = v

val idx_shiftable : idx shiftable = {
    shift_i = shiftx_i_i 0,
    shift_t = shift_id
}

fun substx_i_ibind f x (s : 'a shiftable) v bind =
    case bind of
        BindI (name, inner) => BindI (name, f (x + 1) (#shift_i s 1 v) inner)

fun substx_t_ibind f x (s : 'a shiftable) v bind =
    case bind of
        BindI (name, inner) => BindI (name, f x (#shift_i s 1 v) inner)

local
    fun f x v b =
	case b of
	    Basic s => Basic s
	  | Subset (s, bind) => Subset (s, substx_i_ibind substx_i_p x idx_shiftable v bind)
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
	  | UniI (s, bind) => UniI (substx_i_s x v s, substx_i_ibind f x idx_shiftable v bind)
	  | ExI (s, bind) => ExI (substx_i_s x v s, substx_i_ibind f x idx_shiftable v bind)
	  | AppRecur (name, ns, t, i, r) =>
	    let val n = length ns in
		AppRecur (name, map (mapSnd (substx_i_s x v)) ns, f (x + n) (shiftx_i_i 0 n v) t, map (substx_i_i x v) i, r)
	    end
	  | AppV (y, ts, is, r) => AppV (y, map (f x v) ts, map (substx_i_i x v) is, r)
	  | Int r => Int r
in
fun substx_i_mt x (v : idx) (b : mty) : mty = f x v b
fun subst_i_mt (v : idx) (b : mty) : mty = substx_i_mt 0 v b
end

local
    fun f x v b =
	case b of
	    Mono t => Mono (substx_i_mt x v t)
	  | Uni (name, t) => Uni (name, f x v t)
in
fun substx_i_t x (v : idx) (b : ty) : ty = f x v b
fun subst_i_t (v : idx) (b : ty) : ty = substx_i_t 0 v b
end

local
    (* the substitute can be a type or a recursive type definition *)
    datatype value = 
	     Type of mty
	     | Recur of string * (string * sort) list * mty

    fun shift_i n v =
	case v of
	    Type t => Type (shiftx_i_mt 0 n t)
	  | Recur (name, ns, t) => Recur (name, map (mapSnd (shiftx_i_s 0 n)) ns, shiftx_i_mt (length ns) n t)

    fun shift_t n v =
	case v of
	    Type t => Type (shiftx_t_mt 0 n t)
	  | Recur (name, ns, t) => Recur (name, ns, shiftx_t_mt 1 n t)

    val value_shiftable : value shiftable = {
        shift_i = shift_i,
        shift_t = shift_t
    }

    fun f x v (b : mty) : mty =
	case b of
	    Arrow (t1, d, t2) => Arrow (f x v t1, d, f x v t2)
	  | Unit r => Unit r
	  | Prod (t1, t2) => Prod (f x v t1, f x v t2)
	  | Sum (t1, t2) => Sum (f x v t1, f x v t2)
	  | UniI (s, bind) => UniI (s, substx_t_ibind f x value_shiftable v bind)
	  | ExI (s, bind) => ExI (s, substx_t_ibind f x value_shiftable v bind)
	  | AppRecur (name, ns, t, i, r) => AppRecur (name, ns, f (x + 1) (shift_i (length ns) (shift_t 1 v)) t, i, r)
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

in

fun substx_t_mt x (v : mty) (b : mty) : mty = f x (Type v) b
fun subst_t_mt (v : mty) (b : mty) : mty = substx_t_mt 0 v b
fun subst_is_mt is t = 
    #1 (foldl (fn (i, (t, x)) => (substx_i_mt x (shiftx_i_i 0 x i) t, x - 1)) (t, length is - 1) is)
fun subst_ts_mt vs b = 
    #1 (foldl (fn (v, (b, x)) => (substx_t_mt x (shiftx_t_mt 0 x v) b, x - 1)) (b, length vs - 1) vs)
fun unroll (name, ns, t, i, _) =
    subst_is_mt i (f 0 (shift_i (length ns) (Recur (name, ns, t))) t)
end

fun substx_t_t x (v : mty) (b : ty) : ty =
  case b of
      Mono t => Mono (substx_t_mt x v t)
    | Uni (name, t) => Uni (name, substx_t_t (x + 1) (shift_t_mt v) t)
fun subst_t_t v b =
  substx_t_t 0 v b

fun on_i_ibinds on_anno on_inner x n ibinds =
    case ibinds of
        NilIB inner => 
        NilIB (on_inner x n inner)
      | ConsIB (anno, bind) =>
        ConsIB (on_anno x n anno, on_i_ibind (on_i_ibinds on_anno on_inner) x n bind)

fun on_t_ibinds on_anno on_inner x n ibinds =
    case ibinds of
        NilIB inner => 
        NilIB (on_inner x n inner)
      | ConsIB (anno, bind) =>
        ConsIB (on_anno x n anno, on_t_ibind (on_t_ibinds on_anno on_inner) x n bind)

fun shiftx_pair (f, g) x n (a, b) = (f x n a, g x n b)
fun shiftx_list f x n ls = map (f x n) ls

fun shiftx_i_c x n ((family, tnames, ibinds) : constr) : constr =
    (family,
     tnames, 
     on_i_ibinds shiftx_i_s (shiftx_pair (shiftx_i_mt, shiftx_list shiftx_i_i)) x n ibinds)

fun shift_i_c b = shiftx_i_c 0 1 b

fun shiftx_id x n b = b

fun shiftx_t_c x n ((family, tnames, ibinds) : constr) : constr =
    (shiftx_v x n family, 
     tnames, 
     on_t_ibinds shiftx_id (shiftx_pair (shiftx_t_mt, shiftx_id)) (x + length tnames) n ibinds)
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
