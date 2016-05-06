structure UnderscoredSubst = struct
open Util
open UnderscoredExpr
infixr 0 $
         
fun on_i_i on_v on_invis x n b =
  let
      fun f x n b =
	case b of
	    VarI (y, r) => VarI (on_v x n y, r)
	  | ConstIN n => ConstIN n
	  | ConstIT x => ConstIT x
          | UnOpI (opr, i, r) => UnOpI (opr, f x n i, r)
          | DivI (i1, n2) => DivI (f x n i1, n2)
          | ExpI (i1, n2) => ExpI (f x n i1, n2)
	  | BinOpI (opr, i1, i2) => BinOpI (opr, f x n i1, f x n i2)
	  | TTI r => TTI r
	  | TrueI r => TrueI r
	  | FalseI r => FalseI r
          | TimeAbs (name, i, r) => TimeAbs (name, f (x + 1) n i, r)
          | UVarI a => UVarI a
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
          | Quan (q, bs, name, p) => Quan (q, bs, name, f (x + 1) n p)
  in
      f x n b
  end

fun on_i_ibind f x n bind =
    case bind of
        BindI (name, inner) => BindI (name, f (x + 1) n inner)

fun on_t_ibind f x n bind =
    case bind of
        BindI (name, inner) => BindI (name, f x n inner)

fun on_i_s on_i_p on_invis x n b =
  let
      fun f x n b =
	case b of
	    Basic s => Basic s
	  | Subset (s, bind) => Subset (s, on_i_ibind on_i_p x n bind)
          | UVarS a => UVarS a
  in
      f x n b
  end

fun on_i_mt on_i_i on_i_s on_invis x n b =
  let
      fun f x n b =
	case b of
	    Arrow (t1, d, t2) => Arrow (f x n t1, on_i_i x n d, f x n t2)
          | Unit r => Unit r
	  | Prod (t1, t2) => Prod (f x n t1, f x n t2)
	  | UniI (s, bind) => UniI (on_i_s x n s, on_i_ibind f x n bind)
	  | AppV (y, ts, is, r) => AppV (y, map (f x n) ts, map (on_i_i x n) is, r)
	  | BaseType a => BaseType a
          | UVar a => UVar a
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

fun on_t_mt on_v on_invis x n b =
  let
      fun f x n b =
	case b of
	    Arrow (t1, d, t2) => Arrow (f x n t1, d, f x n t2)
          | Unit r => Unit r
	  | Prod (t1, t2) => Prod (f x n t1, f x n t2)
	  | UniI (s, bind) => UniI (s, on_t_ibind f x n bind)
	  | AppV ((y, r1), ts, is, r) => AppV ((on_v x n y, r1), map (f x n) ts, is, r)
	  | BaseType a => BaseType a
          | UVar a => UVar a
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

fun shiftx_invis _ x n invis = 
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
        val (invis, (x, n)) = foldl f ([], (x, n)) invis
        val residue = if n = 0 then [] else [(x, n)]
        val invis = residue @ invis
        val invis = rev invis
    in
        invis
    end

and shiftx_i_i x n b = on_i_i shiftx_v shiftx_invis x n b
fun shift_i_i b = shiftx_i_i 0 1 b

fun shiftx_i_p x n b = on_i_p shiftx_i_i x n b
fun shift_i_p b = shiftx_i_p 0 1 b

and shiftx_i_s x n b = on_i_s shiftx_i_p shiftx_invis x n b
fun shift_i_s b = shiftx_i_s 0 1 b

and shiftx_i_mt x n b = on_i_mt shiftx_i_i shiftx_i_s shiftx_invis x n b
and shiftx_t_mt x n b = on_t_mt shiftx_v shiftx_invis x n b
fun shift_i_mt b = shiftx_i_mt 0 1 b
fun shift_t_mt b = shiftx_t_mt 0 1 b

fun shiftx_i_t x n b = on_i_t shiftx_i_mt x n b
fun shift_i_t b = shiftx_i_t 0 1 b

fun shiftx_t_t x n b = on_t_t shiftx_t_mt x n b
fun shift_t_t b = shiftx_t_t 0 1 b

end
