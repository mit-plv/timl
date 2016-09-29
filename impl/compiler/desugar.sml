structure Desugar =
struct
  open UnderscoredExpr
  structure O = Option

  exception TODO

  type sigcontext = (int * int * int * int) list

  fun long_id_map (on_mod_proj : id -> id) (on_var : id -> id) ((mp, x) : long_id) : long_id =
    case mp of
      SOME mp => (SOME (on_mod_proj mp), x)
    | NONE => (NONE, on_var x)

  fun idx_map (on_mod_proj : sigcontext -> id -> id) (on_vars : int -> id -> id) (gctx : sigcontext) (sctx : int) (i : idx) : idx =
    let
      fun walk (sctx : int) (i : idx) : idx =
        case i of
          VarI longid => VarI (long_id_map (on_mod_proj gctx) (on_vars sctx) longid)
        | ConstIT _ => i
        | ConstIN _ => i
        | UnOpI (uop, i1, r) => UnOpI (uop, walk sctx i1, r)
        | DivI (i1, a) => DivI (walk sctx i1, a)
        | ExpI (i1, a) => ExpI (walk sctx i1, a)
        | BinOpI (bop, i1, i2) => BinOpI (bop, walk sctx i1, walk sctx i2)
        | Ite (i1, i2, i3, r) => Ite (walk sctx i1, walk sctx i2, walk sctx i3, r)
        | TrueI _ => i
        | FalseI _ => i
        | TTI _ => i
        | TimeAbs (name, i1, r) => TimeAbs (name, walk (sctx + 1) i1, r)
        | AdmitI _ => i
        | UVarI _ => i
    in
      walk sctx i
    end

  fun prop_map (on_idx : sigcontext -> int -> idx -> idx) (gctx : sigcontext) (sctx : int) (p : prop) : prop =
    let
      fun walk (sctx : int) (p : prop) : prop =
        case p of
          True _ => p
        | False _ => p
        | BinConn (bconn, p1, p2) => BinConn (bconn, walk sctx p1, walk sctx p2)
        | Not (p1, r) => Not (walk sctx p1, r)
        | BinPred (bpred, i1, i2) => BinPred (bpred, on_idx gctx sctx i1, on_idx gctx sctx i2)
        | Quan (op_quan, bs, Bind (name1, p1), r) => Quan (op_quan, bs, Bind (name1, walk (sctx + 1) p1), r)
    in
      walk sctx p
    end

  fun sort_map (on_prop : sigcontext -> int -> prop -> prop) (gctx : sigcontext) (sctx : int) (s : sort) : sort =
    let
      fun walk (s : sort) : sort =
        case s of
          Basic _ => s
        | Subset (a, Bind (name, p), r) => Subset (a, Bind (name, on_prop gctx (sctx + 1) p), r)
        | UVarS _ => s
    in
      walk s
    end

  fun kind_map (on_sort : sigcontext -> int -> sort -> sort) (gctx : sigcontext) (sctx : int) (k : kind) : kind =
    let
      fun walk (k : kind) : kind =
        case k of
          ArrowK (is_d, cnt, sorts) => ArrowK (is_d, cnt, map (on_sort gctx sctx) sorts)
    in
      walk k
    end

  fun mtype_map (on_mod_proj : sigcontext -> id -> id) (on_idx : sigcontext -> int -> idx -> idx) (on_sort : sigcontext -> int -> sort -> sort)
    (on_vark : int -> id -> id) (gctx : sigcontext) (sctx : int) (kctx : int) (mt : mtype) : mtype =
    let
      fun walk (sctx : int) (mt : mtype) : mtype =
        case mt of
          Arrow (mt1, i, mt2) => Arrow (walk sctx mt1, on_idx gctx sctx i, walk sctx mt2)
        | TyNat (i, r) => TyNat (on_idx gctx sctx i, r)
        | TyArray (mt1, i) => TyArray (walk sctx mt1, on_idx gctx sctx i)
        | BaseType _ => mt
        | UVar _ => mt
        | Unit _ => mt
        | Prod (mt1, mt2) => Prod (walk sctx mt1, walk sctx mt2)
        | UniI (s, Bind (name, mt1), r) => UniI (on_sort gctx sctx s, Bind (name, walk (sctx + 1) mt1), r)
        | AppV (longid, mtypes, indices, r) =>
            AppV (long_id_map (on_mod_proj gctx) (on_vark kctx) longid, map (walk sctx) mtypes, map (on_idx gctx sctx) indices, r)
    in
      walk sctx mt
    end

  fun ty_map (on_mtype : sigcontext -> int -> int -> mtype -> mtype) (gctx : sigcontext) (sctx : int) (kctx : int) (t : ty) : ty =
    let
      fun walk (kctx : int) (t : ty) : ty =
        case t of
          Mono mt => Mono (on_mtype gctx sctx kctx mt)
        | Uni (Bind (name, t1), r) => Uni (Bind (name, walk (kctx + 1) t1), r)
    in
      walk kctx t
    end

  fun ptrn_map (on_mod_proj : sigcontext -> id -> id) (on_mtype : sigcontext -> int -> int -> mtype -> mtype) (on_varc : int -> id -> id)
    (gctx : sigcontext) (sctx : int) (kctx : int) (cctx : int) (p : ptrn) : ptrn =
    let
      fun walk (p : ptrn) : ptrn =
        case p of
          ConstrP ((longid, eia), inames, op1, r) =>
            ConstrP ((long_id_map (on_mod_proj gctx) (on_varc cctx) longid, eia), inames, O.map walk op1, r)
        | VarP _ => p
        | PairP (p1, p2) => PairP (walk p1, walk p2)
        | TTP _ => p
        | AliasP (name, p1, r) => AliasP (name, walk p1, r)
        | AnnoP (p1, mt) => AnnoP (walk p1, on_mtype gctx sctx kctx mt)
    in
      walk p
    end

  fun expr_map (on_mod_proj : sigcontext -> id -> id) (on_idx : sigcontext -> int -> idx -> idx)
    (on_sort : sigcontext -> int -> sort -> sort) (on_mtype : sigcontext -> int -> int -> mtype -> mtype)
    (on_ptrn : sigcontext -> int -> int -> int -> ptrn -> ptrn)
    (on_decl : sigcontext -> int -> int -> int -> int -> decl -> decl)
    (on_varc : int -> id -> id) (on_vart : int -> id -> id)
    (gctx : sigcontext) (sctx : int) (kctx : int) (cctx : int) (tctx : int) (e : expr) : expr =
    let
      fun walk (sctx : int) (kctx : int) (cctx : int) (tctx : int) (e : expr) : expr =
        case e of
          Var (longid, eia) => Var (long_id_map (on_mod_proj gctx) (on_vart tctx) longid, eia)
        | App (e1, e2) => App (walk sctx kctx cctx tctx e1, walk sctx kctx cctx tctx e2)
        | Abs (p, e1) =>
            let
              val (inames, enames) = ptrn_names p
            in
              Abs
                (on_ptrn gctx sctx kctx cctx p,
                  walk (sctx + length inames) kctx cctx (tctx + length enames) e1)
            end
        | TT _ => e
        | Pair (e1, e2) => Pair (walk sctx kctx cctx tctx e1, walk sctx kctx cctx tctx e2)
        | Fst e1 => Fst (walk sctx kctx cctx tctx e1)
        | Snd e1 => Fst (walk sctx kctx cctx tctx e1)
        | AbsI (s, name, e1, r) => AbsI (on_sort gctx sctx s, name, walk (sctx + 1) kctx cctx tctx e1, r)
        | AppI (e1, i) => AppI (walk sctx kctx cctx tctx e1, on_idx gctx sctx i)
        | BinOp (bop, e1, e2) => BinOp (bop, walk sctx kctx cctx tctx e1, walk sctx kctx cctx tctx e2)
        | TriOp (top, e1, e2, e3) =>
            TriOp (top,
              walk sctx kctx cctx tctx e1,
              walk sctx kctx cctx tctx e2,
              walk sctx kctx cctx tctx e3)
        | ConstNat _ => e
        | ConstInt _ => e
        | AppConstr ((longid, eia), indices, e1) =>
            let
              val indices' = map (on_idx gctx sctx) indices
            in
              AppConstr
                ((long_id_map (on_mod_proj gctx) (on_varc cctx) longid, eia), indices', walk sctx kctx cctx tctx e1)
            end
        | Case (e1, (omt, oi), rules, r) =>
            let
              val e1' = walk sctx kctx cctx tctx e1
              val omt' = O.map (on_mtype gctx sctx kctx) omt
              val oi' = O.map (on_idx gctx sctx) oi
              fun walk_rule (rp, re) =
                let
                  val rp' = on_ptrn gctx sctx kctx cctx rp
                  val (inames, enames) = ptrn_names rp
                  val re' = walk (sctx + length inames) kctx cctx (tctx + length enames) re
                in
                  (rp', re')
                end
              val rules' = map walk_rule rules
            in
              Case (e1', (omt', oi'), rules', r)
            end
        | Let ((omt, oi), decls, e1, r) =>
            let
              val omt' = O.map (on_mtype gctx sctx kctx) omt
              val oi' = O.map (on_idx gctx sctx) oi
              fun iter (decl, (acc, sctx, kctx, cctx, tctx)) =
                let
                  val decl' = on_decl gctx sctx kctx cctx tctx decl
                  val (sctx', kctx', cctx', tctx') =
                    case decl' of
                      Val (tnames, p, _, _) =>
                        let
                          val (inames, enames) = ptrn_names p
                        in
                          (sctx + length inames, kctx + length tnames, cctx, tctx + length enames)
                        end
                    | Rec _ => (sctx, kctx, cctx, tctx + 1)
                    | Datatype (_, _, _, constrs, _) => (sctx, kctx + 1, cctx + length constrs, tctx)
                    | IdxDef _ => (sctx + 1, kctx, cctx, tctx)
                    | AbsIdx2 _ => (sctx + 1, kctx, cctx, tctx)
                    | AbsIdx _ => (sctx + 1, kctx, cctx, tctx)
                    | TypeDef _ => (sctx, kctx + 1, cctx, tctx)
                    | Open (mp, x) => (case List.nth (gctx, mp) of (a, b, c, d) => (sctx + a, kctx + b, cctx + c, tctx + d))
                in
                  (decl' :: acc, sctx', kctx', cctx', tctx')
                end
              val (decls', sctx', kctx', cctx', tctx') = foldl iter ([], sctx, kctx, cctx, tctx) decls
            in
              Let ((omt', oi'), rev decls', walk sctx' kctx' cctx' tctx' e1, r)
            end
        | Ascription (e1, mt) => Ascription (walk sctx kctx cctx tctx e1, on_mtype gctx sctx kctx mt)
        | AscriptionTime (e1, i) => AscriptionTime (walk sctx kctx cctx tctx e1, on_idx gctx sctx i)
        | Never (mt, r) => Never (on_mtype gctx sctx kctx mt, r)
        | Builtin (mt, r) => Builtin (on_mtype gctx sctx kctx mt, r)
    in
      walk sctx kctx cctx tctx e
    end

  fun decl_map (on_mod_proj : sigcontext -> id -> id) (on_idx : sigcontext -> int -> idx -> idx)
    (on_sort : sigcontext -> int -> sort -> sort)
    (on_mtype : sigcontext -> int -> int -> mtype -> mtype)
    (on_ptrn : sigcontext -> int -> int -> int -> ptrn -> ptrn)
    (on_expr : sigcontext -> int -> int -> int -> int -> expr -> expr)
    (gctx : sigcontext) (sctx : int) (kctx : int) (cctx : int) (tctx : int)
    (d : decl) : decl =
    let
      fun walk (sctx : int) (kctx : int) (cctx : int) (tctx : int) (d : decl) : decl =
        case d of
          Val (tnames, p, e, r) => Val (tnames, on_ptrn gctx sctx kctx cctx p, on_expr gctx sctx kctx cctx tctx e, r)
        | Rec (tnames, fname, (stbinds, ((return, using), e)), r) =>
            let
              val kctx' = kctx + length tnames
              val tctx' = tctx + 1
              fun iter (stb, (acc, sctx, kctx, cctx, tctx)) =
                let
                  val (stb', sctx', kctx', cctx', tctx') =
                    case stb of
                      SortingST (name, s) => (SortingST (name, on_sort gctx sctx s), sctx + 1, kctx, cctx, tctx)
                    | TypingST p =>
                        let
                          val (inames, enames) = ptrn_names p
                        in
                          (TypingST (on_ptrn gctx sctx kctx cctx p), sctx + length inames, kctx, cctx, tctx + length enames)
                        end
                in
                  (stb' :: acc, sctx', kctx', cctx', tctx')
                end
              val (stbinds', sctx', kctx'', cctx', tctx'') = foldl iter ([], sctx, kctx', cctx, tctx') stbinds
              val stbinds'' = rev stbinds'
              val return' = on_mtype gctx sctx' kctx'' return
              val using' = on_idx gctx sctx' using
              val e' = on_expr gctx sctx' kctx'' cctx' tctx'' e
            in
              Rec (tnames, fname, (stbinds'', ((return', using'), e')), r)
            end
        | Datatype (name, tnames, sorts, constrs, r) =>
            let
              val sorts' = map (on_sort gctx sctx) sorts
              val kctx' = kctx + 1 + length tnames
              fun walk_constr ((cname, ibinds, r) : constr_decl) =
                let
                  val (name_sorts, (t, indices)) = unfold_ibinds ibinds
                  fun iter ((name, s), (acc, sctx)) =
                    let
                      val s' = on_sort gctx sctx s
                      val sctx' = sctx + 1
                    in
                     ((name, s') :: acc, sctx')
                    end
                  val (name_sorts', sctx') = foldl iter ([], sctx) name_sorts
                  val name_sorts'' = rev name_sorts
                  val t' = on_mtype gctx sctx' kctx' t
                  val indices' = map (on_idx gctx sctx') indices
                  val ibinds' = fold_ibinds (name_sorts'', (t', indices'))
                in
                  (cname, ibinds', r)
                end
              val constrs' = map walk_constr constrs
            in
              Datatype (name, tnames, sorts', constrs', r)
            end
        | IdxDef (name, s, i) => IdxDef (name, on_sort gctx sctx s, on_idx gctx sctx i)
        | AbsIdx2 (name, s, i) => AbsIdx2 (name, on_sort gctx sctx s, on_idx gctx sctx i)
        | AbsIdx ((name, s, i), decls, r) =>
            let
              val s' = on_sort gctx sctx s
              val i' = on_idx gctx sctx i
              fun iter (decl, (acc, sctx, kctx, cctx, tctx)) =
                let
                  val decl' = walk sctx kctx cctx tctx decl
                  val (sctx', kctx', cctx', tctx') =
                    case decl' of
                      Val (tnames, p, _, _) =>
                        let
                          val (inames, enames) = ptrn_names p
                        in
                          (sctx + length inames, kctx + length tnames, cctx, tctx + length enames)
                        end
                    | Rec _ => (sctx, kctx, cctx, tctx + 1)
                    | Datatype (_, _, _, constrs, _) => (sctx, kctx + 1, cctx + length constrs, tctx)
                    | IdxDef _ => (sctx + 1, kctx, cctx, tctx)
                    | AbsIdx2 _ => (sctx + 1, kctx, cctx, tctx)
                    | AbsIdx _ => (sctx + 1, kctx, cctx, tctx)
                    | TypeDef _ => (sctx, kctx + 1, cctx, tctx)
                    | Open (mp, x) => (case List.nth (gctx, mp) of (a, b, c, d) => (sctx + a, kctx + b, cctx + c, tctx + d))
                in
                  (decl' :: acc, sctx', kctx', cctx', tctx')
                end
              val decls' = #1 (foldl iter ([], sctx + 1, kctx, cctx, tctx) decls)
              val decls'' = rev decls'
            in
              AbsIdx ((name, s', i'), decls'', r)
            end
        | TypeDef (name, mt) => TypeDef (name, on_mtype gctx sctx kctx mt)
        | Open mp => Open (on_mod_proj gctx mp)
    in
      walk sctx kctx cctx tctx d
    end
end
