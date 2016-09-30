structure Desugar =
struct
  open UnderscoredExpr
  structure O = Option

  type scontext = int
  type kcontext = int
  type ccontext = int
  type tcontext = int
  type context = scontext * kcontext * ccontext * tcontext
  type sigcontext = context list

  fun long_id_map (on_mod_proj : id -> id) (on_var : id -> id) ((mp, x) : long_id) : long_id =
    case mp of
      SOME mp => (SOME (on_mod_proj mp), x)
    | NONE => (NONE, on_var x)

  fun idx_map (on_mod_proj : sigcontext -> id -> id) (on_vars : scontext -> id -> id) (gctx : sigcontext) (sctx : scontext) (i : idx) : idx =
    let
      fun walk (sctx : scontext) (i : idx) : idx =
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

  fun prop_map (on_idx : sigcontext -> scontext -> idx -> idx) (gctx : sigcontext) (sctx : scontext) (p : prop) : prop =
    let
      fun walk (sctx : scontext) (p : prop) : prop =
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

  fun sort_map (on_prop : sigcontext -> scontext -> prop -> prop) (gctx : sigcontext) (sctx : scontext) (s : sort) : sort =
    let
      fun walk (s : sort) : sort =
        case s of
          Basic _ => s
        | Subset (a, Bind (name, p), r) => Subset (a, Bind (name, on_prop gctx (sctx + 1) p), r)
        | UVarS _ => s
    in
      walk s
    end

  fun kind_map (on_sort : sigcontext -> scontext -> sort -> sort) (gctx : sigcontext) (sctx : scontext) (k : kind) : kind =
    let
      fun walk (k : kind) : kind =
        case k of
          ArrowK (is_d, cnt, sorts) => ArrowK (is_d, cnt, map (on_sort gctx sctx) sorts)
    in
      walk k
    end

  fun mtype_map (on_mod_proj : sigcontext -> id -> id) (on_idx : sigcontext -> scontext -> idx -> idx)
    (on_sort : sigcontext -> scontext -> sort -> sort)
    (on_vark : kcontext -> id -> id) (gctx : sigcontext) (sctx : scontext) (kctx : kcontext) (mt : mtype) : mtype =
    let
      fun walk (sctx : scontext) (mt : mtype) : mtype =
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

  fun ty_map (on_mtype : sigcontext -> scontext -> kcontext -> mtype -> mtype) (gctx : sigcontext)
    (sctx : scontext) (kctx : kcontext) (t : ty) : ty =
    let
      fun walk (kctx : kcontext) (t : ty) : ty =
        case t of
          Mono mt => Mono (on_mtype gctx sctx kctx mt)
        | Uni (Bind (name, t1), r) => Uni (Bind (name, walk (kctx + 1) t1), r)
    in
      walk kctx t
    end

  fun ptrn_map (on_mod_proj : sigcontext -> id -> id) (on_mtype : sigcontext -> scontext -> kcontext -> mtype -> mtype)
    (on_varc : ccontext -> id -> id)
    (gctx : sigcontext) (sctx : scontext) (kctx : kcontext) (cctx : ccontext) (p : ptrn) : ptrn =
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

  fun expr_map (on_mod_proj : sigcontext -> id -> id) (on_idx : sigcontext -> scontext -> idx -> idx)
    (on_sort : sigcontext -> scontext -> sort -> sort) (on_mtype : sigcontext -> scontext -> kcontext -> mtype -> mtype)
    (on_ptrn : sigcontext -> scontext -> kcontext -> ccontext -> ptrn -> ptrn)
    (on_decl : sigcontext -> scontext -> kcontext -> ccontext -> tcontext -> decl -> (decl * context))
    (on_varc : ccontext -> id -> id) (on_vart : tcontext -> id -> id)
    (gctx : sigcontext) (sctx : scontext) (kctx : kcontext) (cctx : ccontext) (tctx : tcontext) (e : expr) : expr =
    let
      fun walk (sctx : scontext) (kctx : kcontext) (cctx : ccontext) (tctx : tcontext) (e : expr) : expr =
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
              fun iter (decl, (acc, (sctx, kctx, cctx, tctx))) =
                let
                  val (decl', (sctx', kctx', cctx', tctx')) = on_decl gctx sctx kctx cctx tctx decl
                in
                  (decl' :: acc, (sctx', kctx', cctx', tctx'))
                end
              val (decls', (sctx', kctx', cctx', tctx')) = foldl iter ([], (sctx, kctx, cctx, tctx)) decls
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

  fun decl_map (on_mod_proj : sigcontext -> id -> id) (on_idx : sigcontext -> scontext -> idx -> idx)
    (on_sort : sigcontext -> scontext -> sort -> sort)
    (on_mtype : sigcontext -> scontext -> kcontext -> mtype -> mtype)
    (on_ptrn : sigcontext -> scontext -> kcontext -> ccontext -> ptrn -> ptrn)
    (on_expr : sigcontext -> scontext -> kcontext -> ccontext -> tcontext -> expr -> expr)
    (gctx : sigcontext) (sctx : scontext) (kctx : kcontext) (cctx : ccontext) (tctx : tcontext)
    (d : decl) : (decl * context) =
    let
      fun walk (sctx : scontext) (kctx : kcontext) (cctx : ccontext) (tctx : tcontext) (d : decl) : (decl * context) =
        case d of
          Val (tnames, p, e, r) =>
            let
              val d' = Val (tnames, on_ptrn gctx sctx kctx cctx p, on_expr gctx sctx kctx cctx tctx e, r)
              val (inames, enames) = ptrn_names p
            in
              (d', (sctx + length inames, kctx + length tnames, cctx, tctx + length enames))
            end
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
              (Rec (tnames, fname, (stbinds'', ((return', using'), e')), r), (sctx, kctx, cctx, tctx + 1))
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
              (Datatype (name, tnames, sorts', constrs', r), (sctx, kctx + 1, cctx + length constrs, tctx))
            end
        | IdxDef (name, s, i) => (IdxDef (name, on_sort gctx sctx s, on_idx gctx sctx i), (sctx + 1, kctx, cctx, tctx))
        | AbsIdx2 (name, s, i) => (AbsIdx2 (name, on_sort gctx sctx s, on_idx gctx sctx i), (sctx + 1, kctx, cctx, tctx))
        | AbsIdx ((name, s, i), decls, r) =>
            let
              val s' = on_sort gctx sctx s
              val i' = on_idx gctx sctx i
              fun iter (decl, (acc, sctx, kctx, cctx, tctx)) =
                let
                  val (decl', (sctx', kctx', cctx', tctx')) = walk sctx kctx cctx tctx decl
                in
                  (decl' :: acc, sctx', kctx', cctx', tctx')
                end
              val decls' = #1 (foldl iter ([], sctx + 1, kctx, cctx, tctx) decls)
              val decls'' = rev decls'
            in
              (AbsIdx ((name, s', i'), decls'', r), (sctx + 1, kctx, cctx, tctx))
            end
        | TypeDef (name, mt) => (TypeDef (name, on_mtype gctx sctx kctx mt), (sctx, kctx + 1, cctx, tctx))
        | Open (mp, x) =>
            case List.nth (gctx, mp) of
              (s, k, c, t) => (Open (on_mod_proj gctx (mp, x)), (sctx + s, kctx + k, cctx + c, tctx + t))
    in
      walk sctx kctx cctx tctx d
    end

  fun spec_map (on_idx : sigcontext -> scontext -> idx -> idx)
    (on_sort : sigcontext -> scontext -> sort -> sort) (on_kind : sigcontext -> scontext -> kind -> kind)
    (on_mtype : sigcontext -> scontext -> kcontext -> mtype -> mtype) (on_ty : sigcontext -> scontext -> kcontext -> ty -> ty)
    (gctx : sigcontext) (sctx : scontext) (kctx : kcontext) (cctx : ccontext) (tctx : tcontext) (s : spec) : spec * context =
    let
      fun walk (s : spec) : spec * context =
        case s of
          SpecVal (name, t) => (SpecVal (name, on_ty gctx sctx kctx t), (sctx, kctx, cctx, tctx + 1))
        | SpecDatatype (name, tnames, sorts, constrs, r) =>
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
              (SpecDatatype (name, tnames, sorts', constrs', r), (sctx, kctx + 1, cctx + length constrs, tctx))
            end
        | SpecIdx (name, s) => (SpecIdx (name, on_sort gctx sctx s), (sctx + 1, kctx, cctx, tctx))
        | SpecType (name, k) => (SpecType (name, on_kind gctx sctx k), (sctx, kctx + 1, cctx, tctx))
        | SpecTypeDef (name, mt) => (SpecTypeDef (name, on_mtype gctx sctx kctx mt), (sctx, kctx + 1, cctx, tctx))
    in
      walk s
    end

  fun sgn_map (on_spec : sigcontext -> scontext -> kcontext -> ccontext -> tcontext -> spec -> spec * context)
    (gctx : sigcontext) (s : sgn) : sgn * context =
    case s of
      SigComponents (specs, r) =>
        let
          fun iter (spec, (acc, s, k, c, t)) =
            let
              val (spec', (s', k', c', t')) = on_spec gctx s k c t spec
            in
              (spec' :: acc, s', k', c', t')
            end
          val (specs', s, k, c, t) = foldl iter ([], 0, 0, 0, 0) specs
          val specs'' = rev specs'
        in
          (SigComponents (specs'', r), (s, k, c, t))
        end

  fun modu_map (on_mod_proj : sigcontext -> id -> id)
    (on_decl : sigcontext -> scontext -> kcontext -> ccontext -> tcontext -> decl -> decl * context)
    (on_sgn : sigcontext -> sgn -> sgn * context)
    (gctx : sigcontext) (modu : mod) : mod * context =
    let
      fun walk (modu : mod) : mod * context =
        case modu of
          ModComponents (decls, r) =>
            let
              fun iter (decl, (acc, sctx, kctx, cctx, tctx)) =
                let
                  val (decl', (sctx', kctx', cctx', tctx')) = on_decl gctx sctx kctx cctx tctx decl
                in
                  (decl' :: acc, sctx', kctx', cctx', tctx')
                end
              val (decls', sctx', kctx', cctx', tctx') = foldl iter ([], 0, 0, 0, 0) decls
              val decls'' = rev decls'
            in
              (ModComponents (decls'', r), (sctx', kctx', cctx', tctx'))
            end
        | ModSeal (modu1, sgn) => (case walk modu1 of (modu1', ctx) => (ModSeal (modu1', #1 (on_sgn gctx sgn)), ctx))
        | ModTransparentAscription (modu1, sgn) =>
            (case walk modu1 of (modu1', ctx) => (ModTransparentAscription (modu1', #1 (on_sgn gctx sgn)), ctx))
    in
      walk modu
    end

  fun top_bind_map (on_modu : sigcontext -> mod -> mod * context)
    (on_sgn : sigcontext -> sgn -> sgn * context)
    (gctx : sigcontext) (fctx : sigcontext) (tb : top_bind) : top_bind * sigcontext * sigcontext =
    let
      fun walk (tb : top_bind) : top_bind * sigcontext * sigcontext =
        case tb of
          TopModBind (name, modu) =>
            let
              val (modu', ctx) = on_modu gctx modu
            in
              (TopModBind (name, modu'), ctx :: gctx, fctx)
            end
        | TopFunctorApp (name, (f, fr), (m, mr)) =>
            let
              val ctx = List.nth (fctx, f)
            in
              (TopFunctorApp (name, (f, fr), (m, mr)), ctx :: gctx, fctx)
            end
        | TopFunctorBind (name1, (name2, sgn), modu) =>
            let
              val (sgn', ctx) = on_sgn gctx sgn
              val (modu', ctx) = on_modu (ctx :: gctx) modu
            in
              (TopFunctorBind (name1, (name2, sgn'), modu'), gctx, ctx :: fctx)
            end
    in
      walk tb
    end

  fun prog_map (on_top_bind : sigcontext -> sigcontext -> top_bind -> top_bind * sigcontext * sigcontext)
    (p : prog) : prog * sigcontext * sigcontext =
    let
      fun iter (tb, (acc, gctx, fctx)) =
        let
          val (tb', gctx', fctx') = on_top_bind gctx fctx tb
        in
          (tb :: acc, gctx', fctx')
        end
      val (p', gctx', fctx') = foldl iter ([], [], []) p
      val p'' = rev p'
    in
     (p'', gctx', fctx')
    end
end
