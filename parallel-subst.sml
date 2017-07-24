(* parallel substitution *)
structure ParaSubst = struct
open Expr
open Subst
open Bind
       
fun psubst_aux_is_ibind f d x v (Bind (name, b) : ('a * 'b) ibind) =
  Bind (name, f (d + 1) x v b)
       
fun apply_depth d (id : long_id) : long_id =
  case id of
      QID _ => id
    | ID (x, r) => ID (x + d, r)
                
fun psubst_long_id d x get_v default y =
  case findi (curry eq_var y) (map (apply_depth d) x) of
      SOME (n, _) => get_v n
    | NONE => default
          
local
  fun f d x v b =
    case b of
	VarI y => psubst_long_id d x (fn n => shiftx_i_i 0 d (List.nth (v, n))) b y
      | IConst _ => b
      | UnOpI (opr, i, r) => UnOpI (opr, f d x v i, r)
      | BinOpI (opr, d1, d2) => BinOpI (opr, f d x v d1, f d x v d2)
      | Ite (i1, i2, i3, r) => Ite (f d x v i1, f d x v i2, f d x v i3, r)
      | IAbs (b, bind, r) => IAbs (b, psubst_aux_is_ibind f d x v bind, r)
      | UVarI a => b
in
val psubst_aux_is_i = f 
fun psubst_is_i x v b = f 0 x v b
end
        
local
  fun f d x v b =
    case b of
	PTrueFalse _ => b
      | Not (p, r) => Not (f d x v p, r)
      | BinConn (opr,p1, p2) => BinConn (opr, f d x v p1, f d x v p2)
      | BinPred (opr, i1, i2) => BinPred (opr, psubst_aux_is_i d x v i1, psubst_aux_is_i d x v i2)
      | Quan (q, bs, bind, r) => Quan (q, bs, psubst_aux_is_ibind f d x v bind, r)
in
val psubst_aux_is_p = f
fun psubst_is_p x v b = f 0 x v b
end

local
  fun f d x v b =
    case b of
	Basic s => Basic s
      | Subset (b, bind, r) => Subset (b, psubst_aux_is_ibind psubst_aux_is_p d x v bind, r)
      | UVarS a => b
      | SAbs (b, bind, r) => SAbs (b, psubst_aux_is_ibind f d x v bind, r)
      | SApp (s, i) => SApp (f d x v s, psubst_aux_is_i d x v i)
in
val psubst_aux_is_s = f
fun psubst_is_s x v b = f 0 x v b
end

fun psubst_aux_is_k d x v b = mapSnd (map (psubst_aux_is_s d x v)) b
        
fun psubst_aux_is_tbind f d x v (Bind (name, b) : ('a * 'b) tbind) =
  Bind (name, f d x v b)
local
  fun f d x v b =
    case b of
	Arrow (t1, i, t2) => Arrow (f d x v t1, psubst_aux_is_i d x v i, f d x v t2)
      | TyNat (i, r) => TyNat (psubst_aux_is_i d x v i, r)
      | TyArray (t, i) => TyArray (f d x v t, psubst_aux_is_i d x v i)
      | Unit r => Unit r
      | Prod (t1, t2) => Prod (f d x v t1, f d x v t2)
      | UniI (s, bind, r) => UniI (psubst_aux_is_s d x v s, psubst_aux_is_ibind f d x v bind, r)
      | MtVar y => MtVar y
      | MtApp (t1, t2) => MtApp (f d x v t1, f d x v t2)
      | MtAbs (k, bind, r) => MtAbs (k, psubst_aux_is_tbind f d x v bind, r)
      | MtAppI (t, i) => MtAppI (f d x v t, psubst_aux_is_i d x v i)
      | MtAbsI (b, bind, r) => MtAbsI (b, psubst_aux_is_ibind f d x v bind, r)
      | BaseType a => BaseType a
      | UVar a => b
      | TDatatype _ => raise Unimpl "psubst_aux_is_mt()/TDatatype"
in
val psubst_aux_is_mt = f
fun psubst_is_mt x v b = f 0 x v b
end

fun psubst_aux_ts_ibind f (di, dt) x v (Bind (name, b) : ('a * 'b) ibind) =
  Bind (name, f (di + 1, dt) x v b)
fun psubst_aux_ts_tbind f (di, dt) x v (Bind (name, b) : ('a * 'b) tbind) =
  Bind (name, f (di, dt + 1) x v b)
local
  fun f d x v b =
    case b of
	Arrow (t1, i, t2) => Arrow (f d x v t1, i, f d x v t2)
      | TyNat (i, r) => TyNat (i, r)
      | TyArray (t, i) => TyArray (f d x v t, i)
      | Unit r => Unit r
      | Prod (t1, t2) => Prod (f d x v t1, f d x v t2)
      | UniI (s, bind, r) => UniI (s, psubst_aux_ts_ibind f d x v bind, r)
      | MtVar y => psubst_long_id (snd d) x (fn n => shiftx_i_mt 0 (fst d) (shiftx_t_mt 0 (snd d) (List.nth (v, n)))) b y
      | MtAbs (k, bind, r) => MtAbs (k, psubst_aux_ts_tbind f d x v bind, r)
      | MtApp (t1, t2) => MtApp (f d x v t1, f d x v t2)
      | MtAbsI (s, bind, r) => MtAbsI (s, psubst_aux_ts_ibind f d x v bind, r)
      | MtAppI (t, i) => MtAppI (f d x v t, i)
      | BaseType a => BaseType a
      | UVar a => b
      | TDatatype _ => raise Unimpl "psubst_aux_ts_mt()/TDatatype"
in
val psubst_aux_ts_mt = f
fun psubst_ts_mt x v b = f (0, 0) x v b
end

end
