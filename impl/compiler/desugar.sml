structure Desugar =
struct
  open UnderscoredExpr
  structure O = Option

  fun long_id_map (on_mod_proj : id -> id) (on_var : id -> id) ((mp, x) : long_id) : long_id =
    case mp of
      SOME mp => (SOME (on_mod_proj mp), x)
    | NONE => (NONE, on_var x)

  fun idx_map (on_mod_proj : int -> id -> id) (on_var : int -> id -> id) (gctx_dep : int) (sctx_dep : int) (i : idx) : idx =
    let
      fun walk (sctx_dep : int) (i : idx) : idx =
        case i of
          VarI longid => VarI (long_id_map (on_mod_proj gctx_dep) (on_var sctx_dep) longid)
        | ConstIT _ => i
        | ConstIN _ => i
        | UnOpI (uop, i1, r) => UnOpI (uop, walk sctx_dep i1, r)
        | DivI (i1, a) => DivI (walk sctx_dep i1, a)
        | ExpI (i1, a) => ExpI (walk sctx_dep i1, a)
        | BinOpI (bop, i1, i2) => BinOpI (bop, walk sctx_dep i1, walk sctx_dep i2)
        | Ite (i1, i2, i3, r) => Ite (walk sctx_dep i1, walk sctx_dep i2, walk sctx_dep i3, r)
        | TrueI _ => i
        | FalseI _ => i
        | TTI _ => i
        | TimeAbs (name, i1, r) => TimeAbs (name, walk (sctx_dep + 1) i1, r)
        | AdmitI _ => i
        | UVarI _ => i
    in
      walk sctx_dep i
    end

  fun prop_map (on_idx : int -> int -> idx -> idx) (gctx_dep : int) (sctx_dep : int) (p : prop) : prop =
    let
      fun walk (sctx_dep : int) (p : prop) : prop =
        case p of
          True _ => p
        | False _ => p
        | BinConn (bconn, p1, p2) => BinConn (bconn, walk sctx_dep p1, walk sctx_dep p2)
        | Not (p1, r) => Not (walk sctx_dep p1, r)
        | BinPred (bpred, i1, i2) => BinPred (bpred, on_idx gctx_dep sctx_dep i1, on_idx gctx_dep sctx_dep i2)
        | Quan (op_quan, bs, Bind (name1, p1), r) => Quan (op_quan, bs, Bind (name1, walk (sctx_dep + 1) p1), r)
    in
      walk sctx_dep p
    end

  fun sort_map (on_prop : int -> int -> prop -> prop) (gctx_dep : int) (sctx_dep : int) (s : sort) : sort =
    let
      fun walk (s : sort) : sort =
        case s of
          Basic _ => s
        | Subset (a, Bind (name, p), r) => Subset (a, Bind (name, on_prop gctx_dep (sctx_dep + 1) p), r)
        | UVarS _ => s
    in
      walk s
    end

  fun kind_map (on_sort : int -> int -> sort -> sort) (gctx_dep : int) (sctx_dep : int) (k : kind) : kind =
    let
      fun walk (k : kind) : kind =
        case k of
          ArrowK (is_d, cnt, slist) => ArrowK (is_d, cnt, map (on_sort gctx_dep sctx_dep) slist)
    in
      walk k
    end

  fun mtype_map (on_mod_proj : int -> id -> id) (on_idx : int -> int -> idx -> idx) (on_sort : int -> int -> sort -> sort)
    (on_var : int -> id -> id) (gctx_dep : int) (sctx_dep : int) (cctx_dep : int) (mt : mtype) : mtype =
    let
      fun walk (sctx_dep : int) (mt : mtype) : mtype =
        case mt of
          Arrow (mt1, i, mt2) => Arrow (walk sctx_dep mt1, on_idx gctx_dep sctx_dep i, walk sctx_dep mt2)
        | TyNat (i, r) => TyNat (on_idx gctx_dep sctx_dep i, r)
        | TyArray (mt1, i) => TyArray (walk sctx_dep mt1, on_idx gctx_dep sctx_dep i)
        | BaseType _ => mt
        | UVar _ => mt
        | Unit _ => mt
        | Prod (mt1, mt2) => Prod (walk sctx_dep mt1, walk sctx_dep mt2)
        | UniI (s, Bind (name, mt1), r) => UniI (on_sort gctx_dep sctx_dep s, Bind (name, walk (sctx_dep + 1) mt1), r)
        | AppV (longid, mtlist, ilist, r) =>
            AppV (long_id_map (on_mod_proj gctx_dep) (on_var cctx_dep) longid, map (walk sctx_dep) mtlist, map (on_idx gctx_dep sctx_dep) ilist, r)
    in
      walk sctx_dep mt
    end

  fun ty_map (on_mtype : int -> int -> int -> mtype -> mtype) (gctx_dep : int) (sctx_dep : int) (cctx_dep : int) (t : ty) : ty =
    let
      fun walk (cctx_dep : int) (t : ty) : ty =
        case t of
          Mono mt => Mono (on_mtype gctx_dep sctx_dep cctx_dep mt)
        | Uni (Bind (name, t1), r) => Uni (Bind (name, walk (cctx_dep + 1) t1), r)
    in
      walk cctx_dep t
    end
end
