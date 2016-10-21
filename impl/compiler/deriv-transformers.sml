functor DerivTransformers(Time : SIG_TIME) =
struct
  structure AstTransformers = AstTransformers(Time)
  open AstTransformers

  open Util

  infixr 0 $

  structure ShiftCtx =
  struct
    structure Helper = DerivGenericOnlyDownTransformer(
    struct
      open ShiftCstr
      open ShiftExpr
      open List

      val subst_c_c = SubstCstr.subst_c_c

      type down = ctx * (int * int)

      fun add_kind (_, ((kctxd, tctxd), (kdep, tdep))) = ((kctxd, map shift0_c_c tctxd), (kdep + 1, tdep))
      fun add_type (_, ((kctxd, tctxd), (kdep, tdep))) = ((kctxd, tctxd), (kdep, tdep + 1))

      fun insert_k a b c = (mapi (fn (i, k) => shift_c_k (length c) (b - 1 - i) k) $ take (a, b)) @ c @ drop (a, b)
      fun insert_t a b c = take (a, b) @ c @ drop (a, b)

      fun on_pr_leaf ((kctx, p), ((kctxd, tctxd), (kdep, tdep))) =
        (insert_k kctx kdep kctxd, shift_c_p (length kctxd) kdep p)
      fun on_ke_leaf ((kctx, k1, k2), ((kctxd, tctxd), (kdep, tdep))) =
        (insert_k kctx kdep kctxd, shift_c_k (length kctxd) kdep k1, shift_c_k (length kctxd) kdep k2)
      fun on_kd_leaf ((kctx, c, k), ((kctxd, tctxd), (kdep, tdep))) =
        (insert_k kctx kdep kctxd, shift_c_c (length kctxd) kdep c, shift_c_k (length kctxd) kdep k)
      fun on_wk_leaf ((kctx, k), ((kctxd, tctxd), (kdep, tdep))) =
        (insert_k kctx kdep kctxd, shift_c_k (length kctxd) kdep k)
      fun on_wp_leaf ((kctx, p), ((kctxd, tctxd), (kdep, tdep))) =
        (insert_k kctx kdep kctxd, shift_c_p (length kctxd) kdep p)
      fun on_te_leaf ((kctx, t1, t2), ((kctxd, tctxd), (kdep, tdep))) =
        (insert_k kctx kdep kctxd, shift_c_c (length kctxd) kdep t1, shift_c_c (length kctxd) kdep t2)
      fun on_ty_leaf (((kctx, tctx), e, t, i), ((kctxd, tctxd), (kdep, tdep))) =
        let
          val kctx = insert_k kctx kdep kctxd
          val tctx = insert_t (map (shift_c_c (length kctxd) kdep) tctx) tdep tctxd
        in
          ((kctx, tctx), shift_e_e (length tctxd) tdep (shift_c_e (length kctxd) kdep e),
             shift_c_c (length kctxd) kdep t, shift_c_c (length kctxd) kdep i)
        end

      fun transformer_typing (on_typing, on_kinding, on_wfkind, on_tyeq, on_proping) (ty, down) =
        case ty of
          TyFix (j, kd, ty) => SOME (TyFix (on_ty_leaf (j, down), kd, ty))
        | _ => NONE

      fun transformer_proping _ = NONE
      fun transformer_kdeq _ _ = NONE
      fun transformer_kinding _ _ = NONE
      fun transformer_wfkind _ _ = NONE
      fun transformer_wfprop _ _ = NONE
      fun transformer_tyeq _ _ = NONE
    end)

    fun shift_ctx_ty ctxd dep ty = Helper.transform_typing (ty, (ctxd, dep))
    fun shift_ctx_kd ctxd dep kd = Helper.transform_kinding (kd, (ctxd, dep))
    fun shift_ctx_te ctxd dep te = Helper.transform_tyeq (te, (ctxd, dep))
    fun shift_ctx_pr ctxd dep pr = Helper.transform_proping (pr, (ctxd, dep))
    fun shift_ctx_wk ctxd dep wk = Helper.transform_wfkind (wk, (ctxd, dep))

    fun shift0_ctx_ty ctxd = shift_ctx_ty ctxd (0, 0)
    fun shift0_ctx_kd ctxd = shift_ctx_kd ctxd (0, 0)
    fun shift0_ctx_te ctxd = shift_ctx_te ctxd (0, 0)
    fun shift0_ctx_pr ctxd = shift_ctx_pr ctxd (0, 0)
    fun shift0_ctx_wk ctxd = shift_ctx_wk ctxd (0, 0)
  end

  structure DerivAssembler = DerivAssembler(
  struct
    val shift_c_k = ShiftCstr.shift_c_k
    val shift_c_c = ShiftCstr.shift_c_c

    val subst_c_c = SubstCstr.subst_c_c
  end)

  structure DerivFVCstr =
  struct
    structure Helper = DerivGenericTransformer(
    struct
      open List
      open FVUtil

      type down = int
      type up = int list

      val upward_base = []
      val combiner = unique_merge

      val shift_c_c = ShiftCstr.shift_c_c
      val shift_c_k = ShiftCstr.shift_c_k

      val subst_c_c = SubstCstr.subst_c_c

      fun add_kind (_, dep) = dep + 1
      fun add_type (_, dep) = dep

      fun on_pr_leaf (pr as (kctx, p), dep) = (pr, FVCstr.free_vars_c_p dep p)
      fun on_ke_leaf (ke as (kctx, k1, k2), dep) = (ke, combiner (FVCstr.free_vars_c_k dep k1, FVCstr.free_vars_c_k dep k2))
      fun on_kd_leaf (kd as (kctx, c, k), dep) = (kd, combiner (FVCstr.free_vars_c_c dep c, FVCstr.free_vars_c_k dep k))
      fun on_wk_leaf (wk as (kctx, k), dep) = (wk, FVCstr.free_vars_c_k dep k)
      fun on_wp_leaf (wp as (kctx, p), dep) = (wp, FVCstr.free_vars_c_p dep p)
      fun on_te_leaf (te as (kctx, t1, t2), dep) = (te, combiner (FVCstr.free_vars_c_c dep t1, FVCstr.free_vars_c_c dep t2))
      fun on_ty_leaf (ty as (ctx, e, t, i), dep) =
        (ty, combiner (combiner (FVCstr.free_vars_c_e dep e, FVCstr.free_vars_c_c dep t), FVCstr.free_vars_c_c dep i))

      fun transformer_typing (on_typing, on_kinding, on_wfkind, on_tyeq, on_proping) (ty, dep) =
        case ty of
          TyFix _ => SOME (ty, [])
        | _ => NONE

      fun transformer_proping _ = NONE
      fun transformer_kdeq _ _ = NONE
      fun transformer_kinding _ _ = NONE
      fun transformer_wfkind _ _ = NONE
      fun transformer_wfprop _ _ = NONE
      fun transformer_tyeq _ _ = NONE
    end)

    fun free_vars_c_ty d ty = #2 (Helper.transform_typing (ty, d))

    val free_vars0_c_ty = free_vars_c_ty 0
  end

  structure DerivFVExpr =
  struct
    structure Helper = DerivGenericTransformer(
    struct
      open List
      open FVUtil

      type down = int
      type up = int list

      val upward_base = []
      val combiner = unique_merge

      val shift_c_c = ShiftCstr.shift_c_c
      val shift_c_k = ShiftCstr.shift_c_k

      val subst_c_c = SubstCstr.subst_c_c

      fun add_kind (_, dep) = dep
      fun add_type (_, dep) = dep + 1

      fun on_pr_leaf (pr as (kctx, p), dep) = (pr, [])
      fun on_ke_leaf (ke as (kctx, k1, k2), dep) = (ke, [])
      fun on_kd_leaf (kd as (kctx, c, k), dep) = (kd, [])
      fun on_wk_leaf (wk as (kctx, k), dep) = (wk, [])
      fun on_wp_leaf (wp as (kctx, p), dep) = (wp, [])
      fun on_te_leaf (te as (kctx, t1, t2), dep) = (te, [])
      fun on_ty_leaf (ty as (ctx, e, t, i), dep) =
        (ty, FVExpr.free_vars_e_e dep e)

      fun transformer_typing (on_typing, on_kinding, on_wfkind, on_tyeq, on_proping) (ty, dep) =
        case ty of
          TyFix _ => SOME (ty, [])
        | _ => NONE

      fun transformer_proping _ = NONE
      fun transformer_kdeq _ _ = NONE
      fun transformer_kinding _ _ = NONE
      fun transformer_wfkind _ _ = NONE
      fun transformer_wfprop _ _ = NONE
      fun transformer_tyeq _ _ = NONE
    end)

    fun free_vars_e_ty d ty = #2 (Helper.transform_typing (ty, d))

    val free_vars0_e_ty = free_vars_e_ty 0
  end

  structure DerivDirectSubstCstr =
  struct
    structure Helper = DerivGenericOnlyDownTransformer(
    struct
      type down = cstr * int

      open ShiftCstr

      fun add_kind (_, (to, who)) = (shift0_c_c to, who + 1)
      fun add_type (_, (to, who)) = (to, who)

      val subst_c_c = SubstCstr.subst_c_c

      open DirectSubstCstr

      fun on_pr_leaf ((kctx, p), (to, who)) = (kctx, dsubst_c_p to who p)
      fun on_ke_leaf ((kctx, k1, k2), (to, who)) = (kctx, dsubst_c_k to who k1, dsubst_c_k to who k2)
      fun on_kd_leaf ((kctx, c, k), (to, who)) = (kctx, dsubst_c_c to who c, dsubst_c_k to who k)
      fun on_wk_leaf ((kctx, k), (to, who)) = (kctx, dsubst_c_k to who k)
      fun on_wp_leaf ((kctx, p), (to, who)) = (kctx, dsubst_c_p to who p)
      fun on_te_leaf ((kctx, t1, t2), (to, who)) = (kctx, dsubst_c_c to who t1, dsubst_c_c to who t2)
      fun on_ty_leaf ((ctx, e, t, i), (to, who)) = (ctx, dsubst_c_e to who e, dsubst_c_c to who t, dsubst_c_c to who i)

      fun transformer_typing (on_typing, on_kinding, on_wfkind, on_tyeq, on_proping) (ty, (to, who)) =
        case ty of
          TyFix _ => SOME ty
        | _ => NONE

      fun transformer_proping _ = NONE
      fun transformer_kdeq _ _ = NONE
      fun transformer_kinding _ _ = NONE
      fun transformer_wfkind _ _ = NONE
      fun transformer_wfprop _ _ = NONE
      fun transformer_tyeq _ _ = NONE
    end)

    fun dsubst_c_ty to who ty = Helper.transform_typing (ty, (to, who))
    fun dsubst_c_kd to who kd = Helper.transform_kinding (kd, (to, who))
    fun dsubst_c_wk to who wk = Helper.transform_wfkind (wk, (to, who))

    fun dsubst0_c_ty to = dsubst_c_ty to 0
    fun dsubst0_c_kd to = dsubst_c_kd to 0
    fun dsubst0_c_wk to = dsubst_c_wk to 0
  end

  structure DerivDirectSubstExpr =
  struct
    structure Helper = DerivGenericOnlyDownTransformer(
    struct
      type down = expr * int

      open ShiftCstr
      open ShiftExpr

      fun add_kind (_, (to, who)) = (shift0_c_e to, who)
      fun add_type (_, (to, who)) = (shift0_e_e to, who + 1)

      val subst_c_c = SubstCstr.subst_c_c

      open DirectSubstExpr

      fun on_pr_leaf (pr, _) = pr
      fun on_ke_leaf (ke, _) = ke
      fun on_kd_leaf (kd, _) = kd
      fun on_wk_leaf (wk, _) = wk
      fun on_wp_leaf (wp, _) = wp
      fun on_te_leaf (te, _) = te
      fun on_ty_leaf ((ctx, e, t, i), (to, who)) = (ctx, dsubst_e_e to who e, t, i)

      fun transformer_typing (on_typing, on_kinding, on_wfkind, on_tyeq, on_proping) (ty, (to, who)) =
        case ty of
          TyFix _ => SOME ty
        | _ => NONE

      fun transformer_proping _ = NONE
      fun transformer_kdeq _ _ = NONE
      fun transformer_kinding _ _ = NONE
      fun transformer_wfkind _ _ = NONE
      fun transformer_wfprop _ _ = NONE
      fun transformer_tyeq _ _ = NONE
    end)

    fun dsubst_e_ty to who ty = Helper.transform_typing (ty, (to, who))

    fun dsubst0_e_ty to = dsubst_e_ty to 0
  end

  structure DerivChangeContext =
  struct
    structure Helper = DerivGenericOnlyDownTransformer(
    struct
      type down = ctx

      open ShiftCstr

      fun add_kind (k, (kctx, tctx)) = (k :: kctx, map shift0_c_c tctx)
      fun add_type (t, (kctx, tctx)) = (kctx, t :: tctx)

      val subst_c_c = SubstCstr.subst_c_c

      fun on_pr_leaf ((_ , p), (kctx, tctx)) = (kctx, p)
      fun on_ke_leaf ((_, k1, k2), (kctx, tctx)) = (kctx, k1, k2)
      fun on_kd_leaf ((_, c, k), (kctx, tctx)) = (kctx, c, k)
      fun on_wk_leaf ((_, k), (kctx, tctx)) = (kctx, k)
      fun on_wp_leaf ((_, p), (kctx, tctx)) = (kctx, p)
      fun on_te_leaf ((_, t1, t2), (kctx, tctx)) = (kctx, t1, t2)
      fun on_ty_leaf ((_, e, t, i), ctx) = (ctx, e, t, i)

      fun transformer_typing (on_typing, on_kinding, on_wfkind, on_tyeq, on_proping) (ty, ctx) =
        case ty of
          TyFix (j, kd, ty) => SOME (TyFix (on_ty_leaf (j, ctx), kd, ty))
        | _ => NONE

      fun transformer_proping _ = NONE
      fun transformer_kdeq _ _ = NONE
      fun transformer_kinding _ _ = NONE
      fun transformer_wfkind _ _ = NONE
      fun transformer_wfprop _ _ = NONE
      fun transformer_tyeq _ _ = NONE
    end)

    fun change_ctx_ty ctx ty = Helper.transform_typing (ty, ctx)
    fun change_ctx_kd ctx kd = Helper.transform_kinding (kd, ctx)
    fun change_ctx_wk ctx wk = Helper.transform_wfkind (wk, ctx)
    fun change_ctx_te ctx te = Helper.transform_tyeq (te, ctx)
    fun change_ctx_pr ctx pr = Helper.transform_proping (pr, ctx)

    val change0_ctx_ty = change_ctx_ty ([], [])
    val change0_ctx_kd = change_ctx_kd ([], [])
    val change0_ctx_wk = change_ctx_wk ([], [])
    val change0_ctx_te = change_ctx_te ([], [])
    val change0_ctx_pr = change_ctx_pr ([], [])
  end

  structure ANF =
  struct
    open DerivAssembler

    open ShiftCstr
    open ShiftCtx
    open List

    fun gen_kdeq_refl kctx k =
      case k of
        KType => KdEqKType (kctx, k, k)
      | KArrow (k1, k2) =>
          let
            val ke1 = gen_kdeq_refl kctx k1
            val ke2 = gen_kdeq_refl kctx k2
          in
            KdEqKArrow (as_KdEqKArrow ke1 ke2, ke1, ke2)
          end
      | KBaseSort s => KdEqBaseSort (kctx, k, k)
      | KSubset (k, p) =>
          let
            val ke = gen_kdeq_refl kctx k
            val pr = PrAdmit (k :: kctx, PIff (p, p))
          in
            KdEqSubset (as_KdEqKSubset ke pr, ke, pr)
          end

    fun gen_tyeq_refl kctx t =
      case t of
        CVar x => TyEqVar (kctx, t, t)
      | CConst cn => TyEqConst (kctx, t, t)
      | CBinOp (opr, t1, t2) =>
          let
            val te1 = gen_tyeq_refl kctx t1
            val te2 = gen_tyeq_refl kctx t2
          in
            TyEqBinOp (as_TyEqBinOp opr te1 te2, te1, te2)
          end
      | CIte (i1, i2, i3) =>
          let
            val te1 = gen_tyeq_refl kctx i1
            val te2 = gen_tyeq_refl kctx i2
            val te3 = gen_tyeq_refl kctx i3
          in
            TyEqIte (as_TyEqIte te1 te2 te3, te1, te2, te3)
          end
      | CTimeAbs c => TyEqTimeAbs (kctx, t, t)
      | CTimeApp (arity, c1, c2) =>
          let
            val te1 = gen_tyeq_refl kctx c1
            val te2 = gen_tyeq_refl kctx c2
          in
            TyEqTimeApp (as_TyEqTimeApp arity te1 te2, te1, te2)
          end
      | CArrow (t1, i, t2) =>
          let
            val te1 = gen_tyeq_refl kctx t1
            val pr = PrAdmit (kctx, TEq (i, i))
            val te2 = gen_tyeq_refl kctx t2
          in
            TyEqArrow (as_TyEqArrow te1 pr te2, te1, pr, te2)
          end
      | CAbs c => TyEqAbs (kctx, t, t)
      | CApp (c1, c2) =>
          let
            val te1 = gen_tyeq_refl kctx c1
            val te2 = gen_tyeq_refl kctx c2
          in
            TyEqApp (as_TyEqApp te1 te2, te1, te2)
          end
      | CQuan (q, k, c) =>
          let
            val ke = gen_kdeq_refl kctx k
            val te = gen_tyeq_refl (k :: kctx) c
          in
            TyEqQuan (as_TyEqQuan q ke te, ke, te)
          end
      | CRec (k, c) =>
          let
            val ke = gen_kdeq_refl kctx k
            val te = gen_tyeq_refl (k :: kctx) c
          in
            TyEqRec (as_TyEqRec ke te, ke, te)
          end
      | CRef c =>
          let
            val te = gen_tyeq_refl kctx c
          in
            TyEqRef (as_TyEqRef te, te)
          end
      | CUnOp (opr, c) =>
          let
            val te = gen_tyeq_refl kctx c
          in
            TyEqUnOp (as_TyEqUnOp opr te, te)
          end

    fun add_kind (k, (kctx, tctx)) = (k :: kctx, map shift0_c_c tctx)
    fun add_type (t, (kctx, tctx)) = (kctx, t :: tctx)

    fun concat_ctx ((kctx1, tctx1), (kctx2, tctx2)) =
      (kctx1 @ kctx2, tctx1 @ map (shift_c_c (length kctx1) 0) tctx2)

    fun normalize_deriv ty = normalize ty (fn (ty, (kctxd, tctxd), ti) => (ty, ti))

    and normalize ty (cont : typing * ctx * cstr -> typing * cstr) =
      case ty of
        TyVar j => cont (ty, ([], []), T0)
      | TyApp (j, ty1, ty2) =>
          normalize_name ty1
            (fn (ty1, d1 as (kctxd1, tctxd1), ti1) =>
               normalize_name (shift0_ctx_ty d1 ty2)
                 (fn (ty2, d2 as (kctxd2, tctxd2), ti2) =>
                    let
                      val ty1 = shift0_ctx_ty d2 ty1
                      val jty1 = extract_judge_typing ty1
                      val (_, i, _) = extract_c_arrow (#3 jty1)
                      val ti1 = shift_c_c (length kctxd2) 0 ti1
                    in
                      cont (TyApp (as_TyApp ty1 ty2, ty1, ty2), concat_ctx (d2, d1), Tadd (Tadd (ti1, ti2), Tadd (T1, i)))
                    end))
      | TyAppC (j, ty, kd) =>
          normalize_name ty
            (fn (ty, d as (kctxd, tctxd), ti) =>
               let
                 val kd = shift0_ctx_kd d kd
               in
                 cont (TyAppC (as_TyAppC ty kd, ty, kd), d, ti)
               end)
      | TyFold (j, kd, ty) =>
          normalize_name ty
            (fn (ty, d as (kctxd, tctxd), ti) =>
               let
                 val kd = shift0_ctx_kd d kd
               in
                 cont (TyFold (as_TyFold kd ty, kd, ty), d, ti)
               end)
      | TyUnfold (j, ty) =>
          normalize_name ty
            (fn (ty, d as (kctxd, tctxd), ti) => cont (TyUnfold (as_TyUnfold ty, ty), d, ti))
      | TyPack (j, kd1, kd2, ty) =>
          normalize_name ty
            (fn (ty, d as (kctxd, tctxd), ti) =>
               let
                 val kd1 = shift0_ctx_kd d kd1
                 val kd2 = shift0_ctx_kd d kd2
               in
                 cont (TyPack (as_TyPack kd1 kd2 ty, kd1, kd2, ty), d, ti)
               end)
      | TyUnpack (j, ty1, ty2) =>
          normalize ty1
            (fn (ty1, d1 as (kctxd1, tctxd1), ti1) =>
               let
                 val jty1 = extract_judge_typing ty1
                 val (_, k, t) = extract_c_quan (#3 jty1)
                 val ty2 = shift_ctx_ty (kctxd1, map shift0_c_c tctxd1) (1, 1) ty2
                 val (ty2, ti2) = normalize ty2
                   (fn (ty2, d2 as (kctxd2, tctxd2), ti2) =>
                      cont (ty2, concat_ctx (d2, concat_ctx (([k], [t]), d1)), ti2))
                 val jty2 = extract_judge_typing ty2
                 val ty2 = TySub ((#1 jty2, #2 jty2, #3 jty2, ti2), ty2, gen_tyeq_refl (fst $ #1 jty2) (#3 jty2), PrAdmit (fst $ #1 jty2, TLe (#4 jty2, ti2)))
               in
                 (TyUnpack (as_TyUnpack ty1 ty2, ty1, ty2), Tadd (ti1, shift_c_c ~1 0 ti2))
               end)
      | TyConst j => cont (ty, ([], []), T0)
      | TyPair (j, ty1, ty2) =>
          normalize_name ty1
            (fn (ty1, d1 as (kctxd1, tctxd1), ti1) =>
               normalize_name (shift0_ctx_ty d1 ty2)
                 (fn (ty2, d2 as (kctxd2, tctxd2), ti2) =>
                    let
                      val ty1 = shift0_ctx_ty d2 ty1
                      val ti1 = shift_c_c (length kctxd2) 0 ti1
                    in
                      cont (TyPair (as_TyPair ty1 ty2, ty1, ty2), concat_ctx (d2, d1), Tadd (ti1, ti2))
                    end))
      | TyProj (j, ty) =>
          normalize_name ty
            (fn (ty, d as (kctxd, tctxd), ti) =>
               let
                 val (p, _) = extract_e_proj (#2 j)
               in
                 cont (TyProj (as_TyProj p ty, ty), d, ti)
               end)
      | TyInj (j, ty, kd) =>
          normalize_name ty
            (fn (ty, d as (kctxd, tctxd), ti) =>
               let
                 val (inj, _) = extract_e_inj (#2 j)
                 val kd = shift0_ctx_kd d kd
               in
                 cont (TyInj (as_TyInj inj ty kd, ty, kd), d, ti)
               end)
      | TyCase (j, ty1, ty2, ty3) =>
          normalize_name ty1
            (fn (ty1, d1 as (kctxd, tctxd), ti) =>
               let
                 val ty2 = shift_ctx_ty d1 (0, 1) ty2
                 val ty3 = shift_ctx_ty d1 (0, 1) ty3
                 val (ty2, ti2) = normalize_deriv ty2
                 val (ty3, ti3) = normalize_deriv ty3
                 val jty2 = extract_judge_typing ty2
                 val jty3 = extract_judge_typing ty3
               in
                 cont (TyCase (as_TyCase ty1 ty2 ty3, ty1, ty2, ty3), d1, Tadd (ti, Tmax (ti2, ti3)))
               end)
      | TyNew (j, ty) =>
          normalize_name ty
            (fn (ty, d as (kctxd, tctxd), ti) => cont (TyNew (as_TyNew ty, ty), d, ti))
      | TyRead (j, ty) =>
          normalize_name ty
            (fn (ty, d as (kctxd, tctxd), ti) => cont (TyRead (as_TyRead ty, ty), d, ti))
      | TyWrite (j, ty1, ty2) =>
          normalize_name ty1
            (fn (ty1, d1 as (kctxd1, tctxd1), ti1) =>
               normalize_name (shift0_ctx_ty d1 ty2)
                 (fn (ty2, d2 as (kctxd2, tctxd2), ti2) =>
                    let
                      val ty1 = shift0_ctx_ty d2 ty1
                      val jty1 = extract_judge_typing ty1
                      val tylet1 = TyConst (#1 jty1, EConst ECTT, CTypeUnit, T0)
                      val (tylet2, ti3) = cont (TyVar ((fst $ #1 jty1, CTypeUnit :: (snd $ #1 jty1)), EVar 0, CTypeUnit, T0), concat_ctx (([], [CTypeUnit]), concat_ctx (d2, d1)), Tadd (shift_c_c (length kctxd2) 0 ti1, ti2))
                    in
                      (TyLet (as_TyLet tylet1 tylet2, tylet1, tylet2), ti3)
                    end))
      | TyLet (j, ty1, ty2) =>
          normalize ty1
            (fn (ty1, d1 as (kctxd1, tctxd1), ti1) =>
               let
                 val jty1 = extract_judge_typing ty1
                 val ty2 = shift_ctx_ty d1 (0, 1) ty2
                 val (ty2, ti2) =
                   normalize ty2 (fn (ty2, d2 as (kctxd2, tctxd2), ti2) => cont (ty2, concat_ctx (d2, concat_ctx (([], [#3 jty1]), d1)), Tadd (shift_c_c (length kctxd2) 0 ti1, ti2)))
               in
                 (TyLet (as_TyLet ty1 ty2, ty1, ty2), ti2)
               end)
      | TySub (j, ty, te, pr) =>
          normalize ty
            (fn (ty, d as (kctxd, tctxd), _) =>
               let
                 val te = shift0_ctx_te d te
                 val pr = shift0_ctx_pr d pr
                 val jpr = extract_judge_proping pr
                 val (_, _, i2) = extract_p_bin_pred $ #2 jpr
                 val jty = extract_judge_typing ty
                 val pr = PrAdmit (fst $ #1 jty, TLe (#4 jty, #4 jty))
               in
                 cont (TySub (as_TySub ty te pr, ty, te, pr), d, i2)
               end)
      | TyFix (j, kd, ty) =>
          let
            val (ty, _) = normalize_deriv ty
            val jkd = extract_judge_kinding kd
            val jty = extract_judge_typing ty
            fun unfold_CForalls t ks =
              case t of
                CQuan (QuanForall, k, t) => unfold_CForalls t (k :: ks)
              | _ => (t, ks)
            val (t, ks) = unfold_CForalls (#2 jkd) []
            val (t1, i, t2) = extract_c_arrow t
            val te = gen_tyeq_refl (fst $ #1 jty) (#3 jty)
            val pr = PrAdmit (fst $ #1 jty, TLe (#4 jty, i))
            val ty = TySub (as_TySub ty te pr, ty, te, pr)
          in
            cont (TyFix (as_TyFix (#1 j) kd ty, kd, ty), ([], []), T0)
          end
      | _ => raise (Impossible "normalize")

    and normalize_name ty cont =
      normalize ty
        (fn (ty, d as (kctxd, tctxd), ti1) =>
           let
             val jty = extract_judge_typing ty
           in
             if is_atomic (#2 jty) then
               cont (ty, d, ti1)
             else
               let
                 val t = #3 jty
                 val tylet1 = ty
                 val (tylet2, ti2) = cont (TyVar ((fst $ #1 jty, t :: (snd $ #1 jty)), EVar 0, t, T0), concat_ctx (([], [t]), d), ti1)
               in
                 (TyLet (as_TyLet tylet1 tylet2, tylet1, tylet2), ti2)
               end
           end)

    and is_atomic e =
      case e of
        EVar _ => true
      | EConst _ => true
      | EAbs _ => true
      | ERec _ => true
      | EAbsC _ => true
      | EFix _ => true
      | _ => false
  end

  structure CPS =
  struct
    open DerivAssembler

    open ShiftCstr
    open ShiftCtx
    open List

    (* TODO: optimization: do a beta-reduction if possible *)
    fun send_to_cont cont ty =
      let
        val res = TyAppK (as_TyAppK cont ty, cont, ty)
      in
        res
      end

    fun transform_type t =
      case t of
        CVar x => CVar x
      | CConst cn => CConst cn
      | CBinOp (opr, t1, t2) => CBinOp (opr, transform_type t1, transform_type t2)
      | CIte (i1, i2, i3) => CIte (transform_type i1, transform_type i2, transform_type i3)
      | CTimeAbs c => CTimeAbs (transform_type c)
      | CTimeApp (arity, c1, c2) => CTimeApp (arity, transform_type c1, transform_type c2)
      | CArrow (t1, i, t2) =>
          let
            val t1 = shift0_c_c $ transform_type t1
            val i = shift0_c_c $ transform_type i
            val t2 = shift0_c_c $ transform_type t2
            val t2 = CArrow (t2, CVar 0, CTypeUnit)
            val t = CForall (KTime, CArrow (CProd (t1, t2), Tadd (i, CVar 0), CTypeUnit))
          in
            t
          end
      | CAbs c => CAbs (transform_type c)
      | CApp (c1, c2) => CApp (transform_type c1, transform_type c2)
      | CQuan (quan, k, t) => CQuan (quan, k, transform_type t)
      | CRec (k, c) => CRec (k, transform_type c)
      | CRef c => CRef (transform_type c)
      | CUnOp (opr, c) => CUnOp (opr, transform_type c)

    fun transform_kinding kd =
      case kd of
        KdVar (kctx, CVar x, k) => KdVar (kctx, CVar x, shift_c_k (1 + x) 0 $ nth (kctx, x))
      | KdConst (kctx, CConst cn, k) => KdConst (kctx, CConst cn, const_kind cn)
      | KdBinOp ((kctx, CBinOp (opr, t1, t2), k), kd1, kd2) =>
          let
            val kd1 = transform_kinding kd1
            val kd2 = transform_kinding kd2
          in
            KdBinOp (as_KdBinOp opr kd1 kd2, kd1, kd2)
          end
      | KdIte ((kctx, CIte (i1, i2, i3), k), kd1, kd2, kd3) =>
          let
            val kd1 = transform_kinding kd1
            val kd2 = transform_kinding kd2
            val kd3 = transform_kinding kd3
          in
            KdIte (as_KdIte kd1 kd2 kd3, kd1, kd2, kd3)
          end
      | KdArrow ((kctx, CArrow (t1, i, t2), k), kd1, kd2, kd3) =>
          let
            val kd1 = shift0_ctx_kd ([KTime], []) $ transform_kinding kd1
            val kd2 = shift0_ctx_kd ([KTime], []) $ transform_kinding kd2
            val kd3 = shift0_ctx_kd ([KTime], []) $ transform_kinding kd3
            val jkd3 = extract_judge_kinding kd3
            val kd3 = KdArrow (as_KdArrow kd3 (KdVar (#1 jkd3, CVar 0, KTime)) (KdConst (#1 jkd3, CTypeUnit, KType)), kd3, KdVar (#1 jkd3, CVar 0, KTime), KdConst (#1 jkd3, CTypeUnit, KType))
            val kdi = KdVar (#1 jkd3, CVar 0, KTime)
            val kd2 = KdBinOp (as_KdBinOp CBTimeAdd kd2 kdi, kd2, kdi)
            val kd = KdArrow (as_KdArrow (KdBinOp (as_KdBinOp CBTypeProd kd1 kd3, kd1, kd3)) kd2 (KdConst (#1 jkd3, CTypeUnit, KType)), KdBinOp (as_KdBinOp CBTypeProd kd1 kd3, kd1, kd3), kd2, KdConst (#1 jkd3, CTypeUnit, KType))
          in
            KdQuan (as_KdQuan QuanForall (WfKdBaseSort (kctx, KTime)) kd, WfKdBaseSort (kctx, KTime), kd)
          end
      | KdAbs ((kctx, CAbs c, k), wk, kd) =>
          let
            val kd = transform_kinding kd
          in
            KdAbs (as_KdAbs wk kd, wk, kd)
          end
      | KdApp ((kctx, CApp (c1, c2), k), kd1, kd2) =>
          let
            val kd1 = transform_kinding kd1
            val kd2 = transform_kinding kd2
          in
            KdApp (as_KdApp kd1 kd2, kd1, kd2)
          end
      | KdTimeAbs ((kctx, CTimeAbs c, k), kd) =>
          let
            val kd = transform_kinding kd
          in
            KdTimeAbs (as_KdTimeAbs kd, kd)
          end
      | KdTimeApp ((kctx, CTimeApp (arity, c1, c2), k), kd1, kd2) =>
          let
            val kd1 = transform_kinding kd1
            val kd2 = transform_kinding kd2
          in
            KdTimeApp (as_KdTimeApp kd1 kd2, kd1, kd2)
          end
      | KdQuan ((kctx, CQuan (quan, k, t), _), wk, kd) =>
          let
            val kd = transform_kinding kd
          in
            KdQuan (as_KdQuan quan wk kd, wk, kd)
          end
      | KdRec ((kctx, CRec (k, c), _), wk, kd) =>
          let
            val kd = transform_kinding kd
          in
            KdRec (as_KdRec wk kd, wk, kd)
          end
      | KdRef ((kctx, CRef c, k), kd) =>
          let
            val kd = transform_kinding kd
          in
            KdRef (as_KdRef kd, kd)
          end
      | KdEq (j, kd, ke) =>
          let
            val kd = transform_kinding kd
          in
            KdEq (as_KdEq kd ke, kd, ke)
          end
      | KdUnOp ((kctx, CUnOp (opr, c), k), kd) =>
          let
            val kd = transform_kinding kd
          in
            KdUnOp (as_KdUnOp opr kd, kd)
          end
      | KdAdmit (kctx, c, k) => KdAdmit (kctx, transform_type c, k)
      | _ => raise (Impossible "transform_kinding")

    fun transform_tyeq te =
      case te of
        TyEqVar j => TyEqVar j
      | TyEqConst j => TyEqConst j
      | TyEqBinOp ((_, CBinOp (opr, _, _), _), te1, te2) =>
          let
            val te1 = transform_tyeq te1
            val te2 = transform_tyeq te2
          in
            TyEqBinOp (as_TyEqBinOp opr te1 te2, te1, te2)
          end
      | TyEqIte (j, te1, te2, te3) =>
          let
            val te1 = transform_tyeq te1
            val te2 = transform_tyeq te2
            val te3 = transform_tyeq te3
          in
            TyEqIte (as_TyEqIte te1 te2 te3, te1, te2, te3)
          end
      | TyEqArrow (j, te1, pr, te2) =>
          let
            val te1 = shift0_ctx_te ([KTime], []) $ transform_tyeq te1
            val pr = shift0_ctx_pr ([KTime], []) pr
            val te2 = shift0_ctx_te ([KTime], []) $ transform_tyeq te2
            val jte2 = extract_judge_tyeq te2
            val te2 = TyEqArrow (as_TyEqArrow te2 (PrAdmit (#1 jte2, TEq (CVar 0, CVar 0))) (TyEqConst (#1 jte2, CTypeUnit, CTypeUnit)), te2, PrAdmit (#1 jte2, TEq (CVar 0, CVar 0)), TyEqConst (#1 jte2, CTypeUnit, CTypeUnit))
            val jpr = extract_judge_proping pr
            val (_, i1, i2) = extract_p_bin_pred (#2 jpr)
            val pr = PrAdmit (#1 jte2, TEq (Tadd (i1, CVar 0) , Tadd (i2, CVar 0)))
            val te = TyEqArrow (as_TyEqArrow (TyEqBinOp (as_TyEqBinOp CBTypeProd te1 te2, te1, te2)) pr (TyEqConst (#1 jte2, CTypeUnit, CTypeUnit)), TyEqBinOp (as_TyEqBinOp CBTypeProd te1 te2, te1, te2), pr, TyEqConst (#1 jte2, CTypeUnit, CTypeUnit))
          in
            TyEqQuan (as_TyEqQuan QuanForall (KdEqBaseSort (#1 j, KTime, KTime)) te, KdEqBaseSort (#1 j, KTime, KTime), te)
          end
      | TyEqApp (j, te1, te2) =>
          let
            val te1 = transform_tyeq te1
            val te2 = transform_tyeq te2
          in
            TyEqApp (as_TyEqApp te1 te2, te1, te2)
          end
      | TyEqTimeApp ((kctx, CTimeApp (arity, _, _), _), te1, te2) =>
          let
            val te1 = transform_tyeq te1
            val te2 = transform_tyeq te2
          in
            TyEqTimeApp (as_TyEqTimeApp arity te1 te2, te1, te2)
          end
      | TyEqBeta (j, te1, te2, te3) =>
          let
            val te1 = transform_tyeq te1
            val te2 = transform_tyeq te2
            val te3 = transform_tyeq te3
          in
            TyEqBeta (as_TyEqBeta te1 te2 te3, te1, te2, te3)
          end
      | TyEqBetaRev (j, te1, te2, te3) =>
          let
            val te1 = transform_tyeq te1
            val te2 = transform_tyeq te2
            val te3 = transform_tyeq te3
          in
            TyEqBetaRev (as_TyEqBetaRev te1 te2 te3, te1, te2, te3)
          end
      | TyEqQuan ((kctx, CQuan (quan, _, _), _), ke, te) =>
          let
            val te = transform_tyeq te
          in
            TyEqQuan (as_TyEqQuan quan ke te, ke, te)
          end
      | TyEqRec (j, ke, te) =>
          let
            val te = transform_tyeq te
          in
            TyEqRec (as_TyEqRec ke te, ke, te)
          end
      | TyEqRef (j, te) =>
          let
            val te = transform_tyeq te
          in
            TyEqRef (as_TyEqRef te, te)
          end
      | TyEqAbs (kctx, t1, t2) => TyEqAbs (kctx, transform_type t1, transform_type t2)
      | TyEqTimeAbs (kctx, t1, t2) => TyEqTimeAbs (kctx, transform_type t1, transform_type t2)
      | TyEqUnOp ((kctx, CUnOp (opr, _), _), te) =>
          let
            val te = transform_tyeq te
          in
            TyEqUnOp (as_TyEqUnOp opr te, te)
          end
      | TyEqNatEq (j, pr) => TyEqNatEq (j, pr)
      | _ => raise (Impossible "transform_tyeq")

    fun debug str = ()

    fun cps_deriv ty =
      let
        val jty = extract_judge_typing ty
        val kd_arg = KdAdmit (fst $ #1 jty, #3 jty, KType)
        val kd_arg = transform_kinding kd_arg
        val jkd_arg = extract_judge_kinding kd_arg
        val ty_var = TyVar ((fst $ #1 jty, (#2 jkd_arg) :: (snd $ #1 jty)), EVar 0, #2 jkd_arg, T0)
        val ty_body = TyHalt (as_TyHalt ty_var, ty_var)
        val cont = TyAbs (as_TyAbs kd_arg ty_body, kd_arg, ty_body)
      in
        cps ty cont
      end

    and cps ty cont =
      case ty of
        TyVar (_, EVar x, t, T0) =>
          let
            val () = debug "TyVar in"
            val res = send_to_cont cont (TyVar (#1 (extract_judge_typing cont), EVar x, nth (snd $ #1 (extract_judge_typing cont), x), T0))
            val () = debug "TyVar out"
          in
            res
          end
      | TyApp (j, ty1, ty2) =>
          let
            val () = debug "TyApp in"
            val jty1 = extract_judge_typing ty1
            val jty2 = extract_judge_typing ty2
            val kd1 = KdAdmit (fst $ #1 jty1, #3 jty1, KType)
            val kd2 = KdAdmit (fst $ #1 jty2, #3 jty2, KType)
            val kd1 = transform_kinding kd1
            val kd2 = transform_kinding kd2
            val jkd1 = extract_judge_kinding kd1
            val jkd2 = extract_judge_kinding kd2
            val t1 = #2 jkd1
            val t2 = #2 jkd2
            val in2_cont = shift0_ctx_ty ([], [t2, t1]) cont
            val in2_jcont = extract_judge_typing in2_cont
            val in1_cont =
              let
                val t_tmp = SubstCstr.subst0_c_c (#2 (extract_c_arrow (#3 in2_jcont))) (#3 (extract_c_quan t1))
                val d1 = TyVar ((fst $ #1 in2_jcont, CProd (t2, #3 in2_jcont) :: t_tmp :: (snd $ #1 in2_jcont)), EVar 1, t_tmp, T0)
                val d2 = TyVar ((fst $ #1 in2_jcont, CProd (t2, #3 in2_jcont) :: t_tmp :: (snd $ #1 in2_jcont)), EVar 0, CProd (t2, #3 in2_jcont), T0)
                val d3 = TyApp (as_TyApp d1 d2, d1, d2)
                val d4 = TyVar ((fst $ #1 in2_jcont, t_tmp :: (snd $ #1 in2_jcont)), EVar 1, t2, T0)
                val d5 = shift0_ctx_ty ([], [t_tmp]) in2_cont
                val d6 = TyPair (as_TyPair d4 d5, d4, d5)
                val d7 = TyLet (as_TyLet d6 d3, d6, d3)
                val d8 = TyVar (#1 in2_jcont, EVar 1, t1, T0)
                val d9 = KdAdmit (fst $ #1 in2_jcont, #2 (extract_c_arrow (#3 in2_jcont)), KTime) (* TODO: extract time kinding *)
                val d10 = TyAppC (as_TyAppC d8 d9, d8, d9)
                val d11 = TyLet (as_TyLet d10 d7, d10, d7)
                val d12 = kd2
              in
                TyAbs (as_TyAbs d12 d11, d12, d11)
              end
            val in1_jcont = extract_judge_typing in1_cont
            val in0_cont =
              let
                val d1 = cps (shift0_ctx_ty ([], [t1]) ty2) in1_cont
                val d2 = kd1
              in
                TyAbs (as_TyAbs d2 d1, d2, d1)
              end
            val res = cps ty1 in0_cont
            val () = debug "TyApp out"
          in
            res
          end
      | TyAbs (j, kd, ty) =>
          let
            val () = debug "TyAbs in"
            val kd = shift0_ctx_kd ([KTime], []) kd
            val kd = transform_kinding kd
            val jkd = extract_judge_kinding kd
            val (t1, i, t2) = extract_c_arrow (#3 j)
            val t2 = shift0_c_c t2
            val kd2 = KdAdmit (#1 jkd, t2, KType)
            val kd2 = transform_kinding kd2
            val jkd2 = extract_judge_kinding kd2
            val t2 = #2 jkd2
            val kd2 = KdArrow (as_KdArrow kd2 (KdVar (#1 jkd, CVar 0, KTime)) (KdConst (#1 jkd, CTypeUnit, KType)), kd2, KdVar (#1 jkd, CVar 0, KTime), KdConst (#1 jkd, CTypeUnit, KType))
            val kd = KdBinOp (as_KdBinOp CBTypeProd kd kd2, kd, kd2)
            val jkd = extract_judge_kinding kd
            val (_, t_arg, t_cont) = extract_c_bin_op (#2 jkd)
            val ty = shift_ctx_ty ([KTime], [t_cont, #2 jkd]) (0, 1) ty
            val jty_old = extract_judge_typing ty
            val old_ctx = #1 (extract_judge_typing cont)
            val new_ctx = (KTime :: fst old_ctx, t_arg :: t_cont :: (#2 jkd) :: map shift0_c_c (snd old_ctx))
            val ty = cps ty (TyVar (new_ctx, EVar 1, t_cont, T0))
            val jty = extract_judge_typing ty
            val ty_get_arg = TyProj (as_TyProj ProjFst (TyVar ((fst $ #1 jty, tl $ snd $ #1 jty), EVar 1, #2 jkd, T0)), TyVar ((fst $ #1 jty, tl $ snd $ #1 jty), EVar 1, #2 jkd, T0))
            val ty = TyLet (as_TyLet ty_get_arg ty, ty_get_arg, ty)
            val ty_get_cont = TyProj (as_TyProj ProjSnd (TyVar ((fst $ #1 jty, tl $ tl $ snd $ #1 jty), EVar 0, #2 jkd, T0)), TyVar ((fst $ #1 jty, tl $ tl $ snd $ #1 jty), EVar 0, #2 jkd, T0))
            val ty = TyLet (as_TyLet ty_get_cont ty, ty_get_cont, ty)
            val jty_new = extract_judge_typing ty
            val new_i = Tadd (#4 jty_old, CVar 0)
            val ty = TySub ((#1 jty_new, #2 jty_new, #3 jty, new_i), ty, ANF.gen_tyeq_refl (fst $ #1 jty_new) (#3 jty), PrAdmit (fst $ #1 jty_new, TLe (#4 jty_new, new_i)))
            val ty = TyAbs (as_TyAbs kd ty, kd, ty)
            val ty = TyAbsC (as_TyAbsC (WfKdBaseSort (tl $ fst $ #1 jty, KTime)) ty, WfKdBaseSort (tl $ fst $ #1 jty, KTime), ty)
            val res = send_to_cont cont ty
            val () = debug "TyAbs out"
          in
            res
          end
      | TyAppC (j, ty, kd) =>
          let
            val () = debug "TyAppC in"
            val jty = extract_judge_typing ty
            val kdt = KdAdmit (fst $ #1 jty, #3 jty, KType)
            val kdt = transform_kinding kdt
            val jkdt = extract_judge_kinding kdt
            val t = #2 jkdt
            val in1_cont = shift0_ctx_ty ([], [t]) cont
            val kd = transform_kinding kd
            val jkd = extract_judge_kinding kd
            val in1_jcont = extract_judge_typing in1_cont
            val in0_cont =
              let
                val t_tmp = SubstCstr.subst0_c_c (#2 jkd) (#3 (extract_c_quan t))
                val d1 = shift0_ctx_ty ([], [t_tmp]) in1_cont
                val d2 = TyVar ((fst $ #1 in1_jcont, t_tmp :: (snd $ #1 in1_jcont)), EVar 0, t_tmp, T0)
                val d3 = send_to_cont d1 d2
                val d4 = TyVar (#1 in1_jcont, EVar 0, t, T0)
                val d5 = TyAppC (as_TyAppC d4 kd, d4, kd)
                val d6 = TyLet (as_TyLet d5 d3, d5, d3)
                val d7 = kdt
              in
                TyAbs (as_TyAbs d7 d6, d7, d6)
              end
            val res = cps ty in0_cont
            val () = debug "TyAppC out"
          in
            res
          end
      | TyAbsC (j, wk, ty) =>
          let
            val () = debug "TyAbsC in"
            val jwk = extract_judge_wfkind wk
            val jty = extract_judge_typing ty
            val kd = KdAdmit (fst $ #1 jty, #3 jty, KType)
            val kd = transform_kinding kd
            val jkd = extract_judge_kinding kd
            val old_ctx = #1 (extract_judge_typing cont)
            val new_ctx = (#2 jwk :: fst old_ctx, map shift0_c_c $ snd old_ctx)
            val ty = cps ty (TyAbs (as_TyAbs kd (TyVar ((fst new_ctx, #2 jkd :: snd new_ctx), EVar 0, #2 jkd, T0)), kd, TyVar ((fst new_ctx, #2 jkd :: snd new_ctx), EVar 0, #2 jkd, T0)))
            val ty = case ty of
                       TyAppK (j, ty1, ty2) => ty2
                     | _ => raise (Impossible "cps")
            val ty = TyAbsC (as_TyAbsC wk ty, wk, ty)
            val res = send_to_cont cont ty
            val () = debug "TyAbsC out"
          in
            res
          end
      | TyRec (j, kd, ty) =>
          let
            val () = debug "TyRec in"
            val kd = transform_kinding kd
            val jkd = extract_judge_kinding kd
            val jty = extract_judge_typing ty
            val old_ctx = #1 (extract_judge_typing cont)
            val new_ctx = (fst old_ctx, (#2 jkd) :: snd old_ctx)
            val ty = cps ty (TyAbs (as_TyAbs kd (TyVar ((fst new_ctx, #2 jkd :: snd new_ctx), EVar 0, #2 jkd, T0)), kd, TyVar ((fst new_ctx, #2 jkd :: snd new_ctx), EVar 0, #2 jkd, T0)))
            val ty = case ty of
                      TyAppK (j, ty1, ty2) => ty2
                    | _ => raise (Impossible "cps")
            val ty = TyRec (as_TyRec kd ty, kd, ty)
            val res = send_to_cont cont ty
            val () = debug "TyRec out"
          in
            res
          end
      | TyFold (j, kd, ty) =>
          let
            val () = debug "TyFold in"
            val jty = extract_judge_typing ty
            val kdt = KdAdmit (fst $ #1 jty, #3 jty, KType)
            val kdt = transform_kinding kdt
            val jkdt = extract_judge_kinding kdt
            val t = #2 jkdt
            val in1_cont = shift0_ctx_ty ([], [t]) cont
            val in1_jcont = extract_judge_typing in1_cont
            val in0_cont =
              let
                val t_tmp = transform_type (#3 j)
                val d1 = shift0_ctx_ty ([], [t_tmp]) in1_cont
                val d2 = TyVar ((fst $ #1 in1_jcont, t_tmp :: (snd $ #1 in1_jcont)), EVar 0, t_tmp, T0)
                val d3 = send_to_cont d1 d2
                val d4 = TyVar (#1 in1_jcont, EVar 0, t, T0)
                val d5 = transform_kinding kd
                val d6 = TyFold (as_TyFold d5 d4, d5, d4)
                val d7 = TyLet (as_TyLet d6 d3, d6, d3)
                val d8 = kdt
              in
                TyAbs (as_TyAbs d8 d7, d8, d7)
              end
            val res = cps ty in0_cont
            val () = debug "TyFold out"
          in
            res
          end
      | TyUnfold (j, ty) =>
          let
            val () = debug "TyUnfold in"
            val jty = extract_judge_typing ty
            val kdt = KdAdmit (fst $ #1 jty, #3 jty, KType)
            val kdt = transform_kinding kdt
            val jkdt = extract_judge_kinding kdt
            val t = #2 jkdt
            val in1_cont = shift0_ctx_ty ([], [t]) cont
            val in1_jcont = extract_judge_typing in1_cont
            val in0_cont =
              let
                val t_tmp = transform_type (#3 j)
                val d1 = shift0_ctx_ty ([], [t_tmp]) in1_cont
                val d2 = TyVar ((fst $ #1 in1_jcont, t_tmp :: (snd $ #1 in1_jcont)), EVar 0, t_tmp, T0)
                val d3 = send_to_cont d1 d2
                val d4 = TyVar (#1 in1_jcont, EVar 0, t, T0)
                val d5 = TyUnfold (as_TyUnfold d4, d4)
                val d6 = TyLet (as_TyLet d5 d3, d5, d3)
                val d7 = kdt
              in
                TyAbs (as_TyAbs d7 d6, d7, d6)
              end
            val res = cps ty in0_cont
            val () = debug "TyUnfold out"
          in
            res
          end
      | TyPack (j, kd1, kd2, ty) =>
          let
            val () = debug "TyPack in"
            val kd1 = transform_kinding kd1
            val kd2 = transform_kinding kd2
            val jty = extract_judge_typing ty
            val kdt = KdAdmit (fst $ #1 jty, #3 jty, KType)
            val kdt = transform_kinding kdt
            val jkdt = extract_judge_kinding kdt
            val t = #2 jkdt
            val in1_cont = shift0_ctx_ty ([], [t]) cont
            val in1_jcont = extract_judge_typing in1_cont
            val in0_cont =
              let
                val t_tmp = transform_type (#3 j)
                val d1 = shift0_ctx_ty ([], [t_tmp]) in1_cont
                val d2 = TyVar ((fst $ #1 in1_jcont, t_tmp :: (snd $ #1 in1_jcont)), EVar 0, t_tmp, T0)
                val d3 = send_to_cont d1 d2
                val d4 = TyVar (#1 in1_jcont, EVar 0, t, T0)
                val d5 = TyPack (as_TyPack kd1 kd2 d4, kd1, kd2, d4)
                val d6 = TyLet (as_TyLet d5 d3, d5, d3)
                val d7 = kdt
              in
                TyAbs (as_TyAbs d7 d6, d7, d6)
              end
            val res = cps ty in0_cont
            val () = debug "TyPack out"
          in
            res
          end
      | TyUnpack (j, ty1, ty2) =>
          let
            val () = debug "TyUnpack in"
            val jty1 = extract_judge_typing ty1
            val kdt = KdAdmit (fst $ #1 jty1, #3 jty1, KType)
            val kdt = transform_kinding kdt
            val jkdt = extract_judge_kinding kdt
            val t = #2 jkdt
            val (_, k, t_body) = extract_c_quan t
            val in1_cont = shift0_ctx_ty ([], [t]) cont
            val in1_jcont = extract_judge_typing in1_cont
            val in0_cont =
              let
                val d1 = shift0_ctx_ty ([k], [t_body]) in1_cont
                val d2 = shift_ctx_ty ([], [shift0_c_c t]) (1, 1) ty2
                val jd2 = extract_judge_typing d2
                val d2 = cps d2 d1
                val d3 = TyVar (#1 in1_jcont, EVar 0, t, T0)
                val d4 = TyUnpack (as_TyUnpack d3 d2, d3, d2)
                val d5 = kdt
              in
                TyAbs (as_TyAbs d5 d4, d5, d4)
              end
            val res = cps ty1 in0_cont
            val () = debug "TyUnpack out"
          in
            res
          end
      | TyConst (_, EConst cn, t, T0) =>
          let
            val () = debug "TyConst in"
            val res = send_to_cont cont (TyConst (#1 (extract_judge_typing cont), EConst cn, const_type cn, T0))
            val () = debug "TyConst out"
          in
            res
          end
      | TyPair (j, ty1, ty2) =>
          let
            val () = debug "TyPair in"
            val jty1 = extract_judge_typing ty1
            val jty2 = extract_judge_typing ty2
            val kd1 = KdAdmit (fst $ #1 jty1, #3 jty1, KType)
            val kd2 = KdAdmit (fst $ #1 jty2, #3 jty2, KType)
            val kd1 = transform_kinding kd1
            val kd2 = transform_kinding kd2
            val jkd1 = extract_judge_kinding kd1
            val jkd2 = extract_judge_kinding kd2
            val t1 = #2 jkd1
            val t2 = #2 jkd2
            val in2_cont = shift0_ctx_ty ([], [t2, t1]) cont
            val in2_jcont = extract_judge_typing in2_cont
            val in1_cont =
              let
                val d1 = shift0_ctx_ty ([], [CProd (t1, t2)]) in2_cont
                val d2 = TyVar ((fst $ #1 in2_jcont, CProd (t1, t2) :: (snd $ #1 in2_jcont)), EVar 0, CProd (t1, t2), T0)
                val d3 = send_to_cont d1 d2
                val d4 = TyVar (#1 in2_jcont, EVar 1, t1, T0)
                val d5 = TyVar (#1 in2_jcont, EVar 0, t2, T0)
                val d6 = TyPair (as_TyPair d4 d5, d4, d5)
                val d7 = TyLet (as_TyLet d6 d3, d6, d3)
                val d8 = kd2
              in
                TyAbs (as_TyAbs d8 d7, d8, d7)
              end
            val in1_jcont = extract_judge_typing in1_cont
            val in0_cont =
              let
                val d1 = cps (shift0_ctx_ty ([], [t1]) ty2) in1_cont
                val d2 = kd1
              in
                TyAbs (as_TyAbs d2 d1, d2, d1)
              end
            val res = cps ty1 in0_cont
            val () = debug "TyPair out"
          in
            res
          end
      | TyProj (j as (_, EUnOp (EUProj p, _), _, _), ty) =>
          let
            val () = debug "TyProj in"
            val jty = extract_judge_typing ty
            val kdt = KdAdmit (fst $ #1 jty, #3 jty, KType)
            val kdt = transform_kinding kdt
            val jkdt = extract_judge_kinding kdt
            val t = #2 jkdt
            val in1_cont = shift0_ctx_ty ([], [t]) cont
            val in1_jcont = extract_judge_typing in1_cont
            val in0_cont =
              let
                val t_tmp = transform_type (#3 j)
                val d1 = shift0_ctx_ty ([], [t_tmp]) in1_cont
                val d2 = TyVar ((fst $ #1 in1_jcont, t_tmp :: (snd $ #1 in1_jcont)), EVar 0, t_tmp, T0)
                val d3 = send_to_cont d1 d2
                val d4 = TyVar (#1 in1_jcont, EVar 0, t, T0)
                val d5 = TyProj (as_TyProj p d4, d4)
                val d6 = TyLet (as_TyLet d5 d3, d5, d3)
                val d7 = kdt
              in
                TyAbs (as_TyAbs d7 d6, d7, d6)
              end
            val res = cps ty in0_cont
            val () = debug "TyProj out"
          in
            res
          end
      | TyInj (j as (_, EUnOp (EUInj inj, _), _, _), ty, kd) =>
          let
            val () = debug "TyInj in"
            val jty = extract_judge_typing ty
            val kdt = KdAdmit (fst $ #1 jty, #3 jty, KType)
            val kdt = transform_kinding kdt
            val jkdt = extract_judge_kinding kdt
            val t = #2 jkdt
            val kd = transform_kinding kd
            val in1_cont = shift0_ctx_ty ([], [t]) cont
            val in1_jcont = extract_judge_typing in1_cont
            val in0_cont =
              let
                val t_tmp = transform_type (#3 j)
                val d1 = shift0_ctx_ty ([], [t_tmp]) in1_cont
                val d2 = TyVar ((fst $ #1 in1_jcont, t_tmp :: (snd $ #1 in1_jcont)), EVar 0, t_tmp, T0)
                val d3 = send_to_cont d1 d2
                val d4 = TyVar (#1 in1_jcont, EVar 0, t, T0)
                val d5 = TyInj (as_TyInj inj d4 kd, d4, kd)
                val d6 = TyLet (as_TyLet d5 d3, d5, d3)
                val d7 = kdt
              in
                TyAbs (as_TyAbs d7 d6, d7, d6)
              end
            val res = cps ty in0_cont
            val () = debug "TyInj out"
          in
            res
          end
      | TyCase (j, ty, ty1, ty2) =>
          let
            val () = debug "TyCase in"
            val jty1 = extract_judge_typing ty1
            val jty2 = extract_judge_typing ty2
            val jty = extract_judge_typing ty
            val kdt = KdAdmit (fst $ #1 jty, #3 jty, KType)
            val kdt = transform_kinding kdt
            val jkdt = extract_judge_kinding kdt
            val t = #2 jkdt
            val in1_cont = shift0_ctx_ty ([], [t]) cont
            val in1_jcont = extract_judge_typing in1_cont
            val in0_cont =
              let
                val (t1_tmp, t2_tmp) = extract_c_sum t
                val d1 = TyVar ((fst $ #1 in1_jcont, t1_tmp :: (#3 in1_jcont) :: (snd $ #1 in1_jcont)), EVar 1, #3 in1_jcont, T0)
                val d2 = cps (shift_ctx_ty ([], [#3 in1_jcont, t]) (0, 1) ty1) d1
                val d3 = TyVar ((fst $ #1 in1_jcont, t2_tmp :: (#3 in1_jcont) :: (snd $ #1 in1_jcont)), EVar 1, #3 in1_jcont, T0)
                val d4 = cps (shift_ctx_ty ([], [#3 in1_jcont, t]) (0, 1) ty2) d3
                val d5 = TyVar ((fst $ #1 in1_jcont, (#3 in1_jcont) :: (snd $ #1 in1_jcont)), EVar 1, t, T0)
                val d6 = TyCase (as_TyCase d5 d2 d4, d5, d2, d4)
                val d7 = TyLet (as_TyLet in1_cont d6, in1_cont, d6)
                val d8 = kdt
              in
                TyAbs (as_TyAbs d8 d7, d8, d7)
              end
            val res = cps ty in0_cont
            val () = debug "TyCase out"
          in
            res
          end
      | TyNew (j, ty) =>
          let
            val jty = extract_judge_typing ty
            val kdt = KdAdmit (fst $ #1 jty, #3 jty, KType)
            val kdt = transform_kinding kdt
            val jkdt = extract_judge_kinding kdt
            val t = #2 jkdt
            val in1_cont = shift0_ctx_ty ([], [t]) cont
            val in1_jcont = extract_judge_typing in1_cont
            val in0_cont =
              let
                val t_tmp = transform_type (#3 j)
                val d1 = shift0_ctx_ty ([], [t_tmp]) in1_cont
                val d2 = TyVar ((fst $ #1 in1_jcont, t_tmp :: (snd $ #1 in1_jcont)), EVar 0, t_tmp, T0)
                val d3 = send_to_cont d1 d2
                val d4 = TyVar (#1 in1_jcont, EVar 0, t, T0)
                val d5 = TyNew (as_TyNew d4, d4)
                val d6 = TyLet (as_TyLet d5 d3, d5, d3)
                val d7 = kdt
              in
                TyAbs (as_TyAbs d7 d6, d7, d6)
              end
          in
            cps ty in0_cont
          end
      | TyRead (j, ty) =>
          let
            val jty = extract_judge_typing ty
            val kdt = KdAdmit (fst $ #1 jty, #3 jty, KType)
            val kdt = transform_kinding kdt
            val jkdt = extract_judge_kinding kdt
            val t = #2 jkdt
            val in1_cont = shift0_ctx_ty ([], [t]) cont
            val in1_jcont = extract_judge_typing in1_cont
            val in0_cont =
              let
                val t_tmp = transform_type (#3 j)
                val d1 = shift0_ctx_ty ([], [t_tmp]) in1_cont
                val d2 = TyVar ((fst $ #1 in1_jcont, t_tmp :: (snd $ #1 in1_jcont)), EVar 0, t_tmp, T0)
                val d3 = send_to_cont d1 d2
                val d4 = TyVar (#1 in1_jcont, EVar 0, t, T0)
                val d5 = TyRead (as_TyRead d4, d4)
                val d6 = TyLet (as_TyLet d5 d3, d5, d3)
                val d7 = kdt
              in
                TyAbs (as_TyAbs d7 d6, d7, d6)
              end
          in
            cps ty in0_cont
          end
      | TyWrite (j, ty1, ty2) =>
          let
            val jty1 = extract_judge_typing ty1
            val jty2 = extract_judge_typing ty2
            val kd1 = KdAdmit (fst $ #1 jty1, #3 jty1, KType)
            val kd2 = KdAdmit (fst $ #1 jty2, #3 jty2, KType)
            val kd1 = transform_kinding kd1
            val kd2 = transform_kinding kd2
            val jkd1 = extract_judge_kinding kd1
            val jkd2 = extract_judge_kinding kd2
            val t1 = #2 jkd1
            val t2 = #2 jkd2
            val in2_cont = shift0_ctx_ty ([], [t2, t1]) cont
            val in2_jcont = extract_judge_typing in2_cont
            val in1_cont =
              let
                val d1 = shift0_ctx_ty ([], [CTypeUnit]) in2_cont
                val d2 = TyConst ((fst $ #1 in2_jcont, CTypeUnit :: (snd $ #1 in2_jcont)), EConst ECTT, CTypeUnit, T0)
                val d3 = send_to_cont d1 d2
                val d4 = TyVar (#1 in2_jcont, EVar 1, t1, T0)
                val d5 = TyVar (#1 in2_jcont, EVar 0, t2, T0)
                val d6 = TyWrite (as_TyWrite d4 d5, d4, d5)
                val d7 = TyLet (as_TyLet d6 d3, d6, d3)
                val d8 = kd2
              in
                TyAbs (as_TyAbs d8 d7, d8, d7)
              end
            val in1_jcont = extract_judge_typing in1_cont
            val in0_cont =
              let
                val d1 = cps (shift0_ctx_ty ([], [t1]) ty2) in1_cont
                val d2 = kd1
              in
                TyAbs (as_TyAbs d2 d1, d2, d1)
              end
          in
            cps ty1 in0_cont
          end
      | TySub (j, ty, te, pr) =>
          let
            val () = debug "TySub in"
            val jty = extract_judge_typing ty
            val kdt = KdAdmit (fst $ #1 jty, #3 jty, KType)
            val kdt = transform_kinding kdt
            val jkdt = extract_judge_kinding kdt
            val t = #2 jkdt
            val in1_cont = shift0_ctx_ty ([], [t]) cont
            val in1_jcont = extract_judge_typing in1_cont
            val in0_cont =
              let
                val t_tmp = transform_type (#3 j)
                val d1 = in1_cont
                val d2 = TyVar (#1 in1_jcont, EVar 0, t, T0)
                val d3 = TySub ((#1 in1_jcont, EVar 0, t_tmp, T0), d2, transform_tyeq te, PrAdmit (fst $ #1 in1_jcont, TLe (T0, T0)))
                val d4 = send_to_cont d1 d3
                val d5 = kdt
              in
                TyAbs (as_TyAbs d5 d4, d5, d4)
              end
            val res = cps ty in0_cont
            val in0_jcont = extract_judge_typing in0_cont
            val ti = Tadd (#4 j, #2 (extract_c_arrow $ #3 in0_jcont))
            val jres = extract_judge_typing res
            val res = TySub ((#1 jres, #2 jres, #3 jres, ti), res, ANF.gen_tyeq_refl (fst $ #1 jres) (#3 jres), PrAdmit (fst $ #1 jres, TLe (#4 jres, ti)))
            val () = debug "TySub out"
          in
            res
          end
      | _ => raise (Impossible "cps")
  end

  structure CloConv =
  struct
    structure Helper = DerivGenericOnlyDownTransformer(
    struct
      type down = ctx

      val shift_c_k = ShiftCstr.shift_c_k
      val shift_c_c = ShiftCstr.shift_c_c

      val subst_c_c = SubstCstr.subst_c_c

      fun add_kind (k, (kctx, tctx)) = (k :: kctx, map (shift_c_c 1 0) tctx)
      fun add_type (t, (kctx, tctx)) = (kctx, t :: tctx)

      open DerivFVCstr
      open DerivFVExpr
      open List

      open DerivDirectSubstCstr
      open DerivDirectSubstExpr
      open DirectSubstCstr
      open DirectSubstExpr

      open DerivChangeContext
      open DerivAssembler

      fun transform_type t =
        case t of
          CVar x => CVar x
        | CConst cn => CConst cn
        | CBinOp (opr, t1, t2) =>
            let
              val t1 = transform_type t1
              val t2 = transform_type t2
            in
              CBinOp (opr, t1, t2)
            end
        | CIte (i1, i2, i3) =>
            let
              val i1 = transform_type i1
              val i2 = transform_type i2
              val i3 = transform_type i3
            in
              CIte (i1, i2, i3)
            end
        | CTimeAbs c => CTimeAbs (transform_type c)
        | CTimeApp (arity, c1, c2) =>
            let
              val c1 = transform_type c1
              val c2 = transform_type c2
            in
              CTimeApp (arity, c1, c2)
            end
        | CArrow (t1, i, t2) =>
            let
              val t1 = transform_type t1
              val i = transform_type i
              val t2 = transform_type t2
            in
              CExists (KType, CProd (CArrow (CProd (CVar 0, ShiftCstr.shift0_c_c t1), ShiftCstr.shift0_c_c i, ShiftCstr.shift0_c_c t2), CVar 0))
            end
        | CAbs c => CAbs (transform_type c)
        | CApp (c1, c2) =>
            let
              val c1 = transform_type c1
              val c2 = transform_type c2
            in
              CApp (c1, c2)
            end
        | CQuan (q, k, c) =>
            let
              val c = transform_type c
            in
              CQuan (q, k, c)
            end
        | CRec (k, c) =>
            let
              val c = transform_type c
            in
              CRec (k, c)
            end
        | CRef c => CRef (transform_type c)
        | CUnOp (opr, c) => CUnOp (opr, transform_type c)

      fun on_pr_leaf ((_, p), (kctx, _)) = (kctx, p)
      fun on_ke_leaf ((_, k1, k2), (kctx, tctx)) = (kctx, k1, k2)
      fun on_kd_leaf ((_, c, k), (kctx, tctx)) = (kctx, transform_type c, k)
      fun on_wk_leaf ((_, k), (kctx, tctx)) = (kctx, k)
      fun on_wp_leaf ((_, p), (kctx, tctx)) = (kctx, p)
      fun on_te_leaf ((_, t1, t2), (kctx, tctx)) = (kctx, transform_type t1, transform_type t2)
      fun on_ty_leaf (ty as ((_, _), e, t, i), (kctx, tctx)) =
        case e of
          EVar x => ((kctx, tctx), e, List.nth (tctx, x), T0)
        | EConst cn => ((kctx, tctx), e, const_type cn, T0)
        | _ => raise (Impossible "CloConv")

      fun transformer_typing (on_typing, on_kinding, on_wfkind, on_tyeq, on_proping) (ty, (kctx, tctx)) =
        case ty of
          TyRec (_, kd, _) =>
            let
              val fcv = free_vars0_c_ty ty
              val fev = free_vars0_e_ty ty
              val kinds = map (fn x => shift_c_k (1 + x) 0 (nth (kctx, x))) fcv
              val new_kinds = snd $ ListPair.unzip $
                foldri (fn (i, (x, k), kctx) =>
                          (x, foldli (fn (j, (x, _), k) =>
                                        dsubst_c_k (CVar j) x k) k kctx) :: kctx) [] $ ListPair.zip (fcv, kinds)
              val types = map (fn x => nth (tctx, x)) fev
              val new_types = map (fn t => foldli (fn (j, x, t) => dsubst_c_c (CVar j) x t) t fcv) types

              fun unfold_kd kd wks =
                case kd of
                  KdQuan (j, wk, kd) => unfold_kd kd (wk :: wks)
                | _ => (kd, wks)
              val (_, ori_wks) = unfold_kd kd []

              val ty = foldli (fn (j, x, ty) => dsubst_c_ty (CVar j) x ty) ty fcv
              val ty = foldli (fn (j, x, ty) => dsubst_e_ty (EVar j) x ty) ty fev
              val ty = change_ctx_ty (new_kinds, new_types) ty
              val (_, kd, ty_inner) =
                case ty of
                  TyRec (j, kd, ty_inner) => (j, kd, ty_inner)
                | _ => raise (Impossible "CloConv")

              val kd_arrow = fst $ unfold_kd kd []

              fun unfold_ty ty wks =
                case ty of
                  TyAbsC (j, wk, ty) => unfold_ty ty (wk :: wks)
                | _ => (ty, wks)
              val (ty_abs, wks) = unfold_ty ty_inner []
              val (_, kd_abs, ty_body) =
                case ty_abs of
                  TyAbs a => a
                | _ => raise (Impossible "closure conversion")

              val ori_kinds = map (snd o extract_judge_wfkind) wks
              val new_types = map (shift_c_c (length ori_kinds) 0) new_types

              val kctx_fix = ori_kinds @ new_kinds

              val t_env =
                case length new_types of
                  0 => CTypeUnit
                | 1 => hd new_types
                | _ => foldl (fn (a, b) => CProd (a, b)) (CProd (hd $ tl new_types, hd new_types)) (tl $ tl new_types)
              val kd_t_env =
                case length new_types of
                  0 => KdConst (kctx_fix, CTypeUnit, KType)
                | 1 => KdAdmit (kctx_fix, t_env, KType)
                | _ => foldl (fn (t, ty) =>
                    let
                      val tmp = KdAdmit (kctx_fix, t, KType)
                    in
                      KdBinOp (as_KdBinOp CBTypeProd tmp ty, tmp, ty)
                    end) (KdBinOp ((kctx_fix, CProd (hd $ tl new_types, hd new_types), KType), KdAdmit (kctx_fix, hd $ tl new_types, KType), KdAdmit (kctx_fix, hd new_types, KType))) (tl $ tl new_types)

              val kd_t_abs =
                case kd_arrow of
                  KdArrow (jkd, kd1, kd2, kd3) =>
                    let
                      val kd1 = on_kinding (kd1, (kctx_fix, []))
                      val kd2 = on_kinding (kd2, (kctx_fix, []))
                      val kd3 = on_kinding (kd3, (kctx_fix, []))
                      val kd1 = KdBinOp (as_KdBinOp CBTypeProd kd_t_env kd1, kd_t_env, kd1)
                    in
                      KdArrow (as_KdArrow kd1 kd2 kd3, kd1, kd2, kd3)
                    end
                | _ => raise (Impossible "CloConv")
              val jkd_t_abs = extract_judge_kinding kd_t_abs
              val t_abs = #2 jkd_t_abs
              val (t_abs_1, t_abs_i, t_abs_2) = extract_c_arrow t_abs
              val t_arg = #2 (extract_c_prod t_abs_1)

              val t_partial_fix = foldl (fn (a, b) => CForall (a, b)) t_abs ori_kinds
              val t_fix = foldl (fn (a, b) => CForall (a, b)) t_partial_fix new_kinds
              val kd_partial_fix = foldl (fn (wk, kd) => KdQuan (as_KdQuan QuanForall wk kd, wk, kd)) kd_t_abs wks
              val kd_fix = foldl (fn (k, kd) =>
                                     let
                                       val jkd = extract_judge_kinding kd
                                       val wk = WfKdAdmit (tl $ #1 jkd, k)
                                     in
                                       KdQuan (as_KdQuan QuanForall wk kd, wk, kd)
                                     end) kd_partial_fix new_kinds

              val t_abs_exi = CArrow (CProd (CVar 0, ShiftCstr.shift0_c_c t_arg), ShiftCstr.shift0_c_c t_abs_i, ShiftCstr.shift0_c_c t_abs_2)

              val t_param = t_abs_1

              val tctx_fix = [t_param, t_fix]

              val tctx_unwrap_env =
                case length new_types of
                  0 => tctx_fix
                | 1 => t_env :: tctx_fix
                | _ =>
                    let
                      fun inner tctx d t =
                        if d = 0 then
                          let
                            val (t1, t2) = extract_c_prod t
                          in
                            t2 :: t1 :: tctx
                          end
                        else
                          let
                            val (t1, t2) = extract_c_prod t
                          in
                            inner (t2 :: t1 :: tctx) (d - 1) t2
                          end
                    in
                      inner (t_env :: tctx_fix) (length new_types - 2) t_env
                    end

              val tctx_unwrap_self = (shift_c_c (length ori_kinds) 0 $ foldl (fn (t, k) => CForall (t, k)) (CExists (KType, CProd (t_abs_exi, CVar 0))) ori_kinds) :: tctx_unwrap_env
              val tctx_unwrap_arg = t_arg :: tctx_unwrap_self

              val ty_body = foldli (fn (j, x, ty) => dsubst_e_ty (EVar (if j = 0 then 2 else 2 * j + 1)) (j + 2) ty) ty_body fev
              val ty_body = change_ctx_ty (kctx_fix, tctx_unwrap_arg) ty_body
              val new_ty_body = on_typing (ty_body, (kctx_fix, tctx_unwrap_arg))

              val new_ty_body_wrap_arg =
                let
                  val param_idx = length tctx_unwrap_self - 2
                  val tmp_ty = TyProj (((kctx_fix, tctx_unwrap_self), EProj (ProjSnd, EVar param_idx), t_arg, T0), TyVar ((kctx_fix, tctx_unwrap_self), EVar param_idx, t_param, T0))
                in
                  TyLet (as_TyLet tmp_ty new_ty_body, tmp_ty, new_ty_body)
                end

              val new_ty_body_wrap_self =
                let
                  val param_idx = length tctx_unwrap_env - 2
                  val ty1 = TyProj (((kctx_fix, tctx_unwrap_env), EProj (ProjFst, EVar param_idx), t_env, T0), TyVar ((kctx_fix, tctx_unwrap_env), EVar param_idx, t_param, T0))
                  val ty2 = TyVar ((kctx_fix, tctx_unwrap_env), EVar (param_idx + 1), t_fix, T0)
                  val ty3 = foldri (fn (j, _, ty) =>
                                      let
                                        val jty = extract_judge_typing ty
                                        val e = EAppC (#2 jty, CVar (j + length ori_kinds))
                                        val i = #4 jty
                                        val (_, k, body) = extract_c_quan (#3 jty)
                                        val t = SubstCstr.subst0_c_c (CVar (j + length ori_kinds)) body
                                      in
                                        TyAppC ((#1 jty, e, t, i), ty, KdVar (fst $ #1 jty, CVar (j + length ori_kinds), k))
                                      end) ty2 new_kinds
                  val tmp_kinds = mapi (fn (i, k) => shift_c_k (length ori_kinds) (length ori_kinds - i - 1) k) ori_kinds
                  val ty3 = ShiftCtx.shift_ctx_ty (tmp_kinds, []) (0, 0) ty3
                  val ty3 = foldri (fn (j, _, ty) =>
                                      let
                                        val jty = extract_judge_typing ty
                                        val e = EAppC (#2 jty, CVar j)
                                        val i = #4 jty
                                        val (_, k, body) = extract_c_quan (#3 jty)
                                        val t = SubstCstr.subst0_c_c (CVar j) body
                                      in
                                        TyAppC ((#1 jty, e, t, i), ty, KdVar (fst $ #1 jty, CVar j, k))
                                      end) ty3 ori_kinds
                  val ty1 = ShiftCtx.shift_ctx_ty (tmp_kinds, []) (0, 0) ty1
                  val ty4 = TyPair (as_TyPair ty3 ty1, ty3, ty1)
                  val jty4 = extract_judge_typing ty4
                  val ty4 = TySub ((#1 jty4, #2 jty4, #3 jty4, T0), ty4, ANF.gen_tyeq_refl (fst $ #1 jty4) (#3 jty4), PrAdmit (fst $ #1 jty4, TLe (#4 jty4, T0)))
                  val jty3 = extract_judge_typing ty3
                  val (tmp_t_1, tmp_t_i, tmp_t_2) = extract_c_arrow (#3 jty3)
                  val (_, tmp_t_arg) = extract_c_prod tmp_t_1
                  val kd2 = KdAdmit (fst $ #1 jty3, CExists (KType, CProd (CArrow (CProd (CVar 0, shift_c_c 1 0 tmp_t_arg), shift_c_c 1 0 tmp_t_i, shift_c_c 1 0 tmp_t_2), CVar 0)), KType)
                  val kd_t_env = ShiftCtx.shift_ctx_kd (tmp_kinds, []) (0, 0) kd_t_env
                  val ty5 = TyPack (as_TyPack kd2 kd_t_env ty4, kd2, kd_t_env, ty4)
                  val ty6 = foldli (fn (j, wk, ty) =>
                                     let
                                       val jty = extract_judge_typing ty
                                       val wk = WfKdAdmit (tl $ fst $ #1 jty, hd $ fst $ #1 jty)
                                     in
                                       TyAbsC (as_TyAbsC wk ty, wk, ty)
                                     end) ty5 wks
                in
                  TyLet (as_TyLet ty6 new_ty_body_wrap_arg, ty6, new_ty_body_wrap_arg)
                end

              val new_ty_body_wrap_env =
                case length new_types of
                  0 => new_ty_body_wrap_self
                | 1 =>
                    let
                      val tmp_ty = TyProj (((kctx_fix, tctx_fix), EProj (ProjFst, EVar 0), t_env, T0), TyVar ((kctx_fix, tctx_fix), EVar 0, t_param, T0))
                    in
                      TyLet (as_TyLet tmp_ty new_ty_body_wrap_self, tmp_ty, new_ty_body_wrap_self)
                    end
                | _ =>
                    let
                      val tylet2 =
                        foldli (fn (i, _, ty) =>
                                  if i mod 2 = 0 then
                                    let
                                      val jty = extract_judge_typing ty
                                      val (kctx, tctx') = #1 jty
                                      val tctx = tl tctx'
                                      val tmp_ty = TyProj (((kctx, tctx), EProj (ProjSnd, EVar 1), hd tctx', T0), TyVar ((kctx, tctx), EVar 1, nth (tctx, 1), T0))
                                    in
                                      TyLet (as_TyLet tmp_ty ty, tmp_ty, ty)
                                    end
                                  else
                                    let
                                      val jty = extract_judge_typing ty
                                      val (kctx, tctx') = #1 jty
                                      val tctx = tl tctx'
                                      val tmp_ty = TyProj (((kctx, tctx), EProj (ProjFst, EVar 0), hd tctx', T0), TyVar ((kctx, tctx), EVar 0, hd tctx, T0))
                                    in
                                      TyLet (as_TyLet tmp_ty ty, tmp_ty, ty)
                                    end) new_ty_body_wrap_self (take (tctx_unwrap_env, length tctx_unwrap_env - 3))
                      val tylet1 = TyProj (((kctx_fix, tctx_fix), EProj (ProjFst, EVar 0), t_env, T0), TyVar ((kctx_fix, tctx_fix), EVar 0, t_param, T0))
                    in
                      TyLet (as_TyLet tylet1 tylet2, tylet1, tylet2)
                    end

              val jnew_ty_body_wrap_env = extract_judge_typing new_ty_body_wrap_env
              val jnew_ty_body = extract_judge_typing new_ty_body
              val new_ty_body_wrap_env_sub =
                TySub ((#1 jnew_ty_body_wrap_env, #2 jnew_ty_body_wrap_env, #3 jnew_ty_body, #4 jnew_ty_body), new_ty_body_wrap_env, ANF.gen_tyeq_refl kctx_fix (#3 jnew_ty_body), PrAdmit (kctx_fix, TLe (#4 jnew_ty_body_wrap_env, #4 jnew_ty_body)))

              val ty_fix = TyFix (as_TyFix (kctx, tctx) kd_fix new_ty_body_wrap_env_sub, kd_fix, new_ty_body_wrap_env_sub)

              val ty_construct =
                case length types of
                  0 => TyConst ((kctx, tctx), EConst ECTT, CTypeUnit, T0)
                | 1 => TyVar ((kctx, tctx), EVar (hd fev), hd types, T0)
                | _ => foldli (fn (j, x, ty) =>
                                let
                                  val jty = extract_judge_typing ty
                                  val e = EPair (EVar x, #2 jty)
                                  val t = CProd (nth (types, j), #3 jty)
                                  val i = Tadd (T0, #4 jty)
                                in
                                  TyPair ((#1 jty, e, t, i), TyVar (#1 jty, EVar j, nth (types, j), T0), ty)
                                end) (TyPair (((kctx, tctx), EPair (EVar (hd $ tl fev), EVar (hd fev)), CProd (hd $ tl types, hd types), Tadd (T0, T0)), TyVar ((kctx, tctx), EVar (hd $ tl fev), hd $ tl types, T0), TyVar ((kctx, tctx), EVar (hd fev), hd types, T0))) (tl $ tl fev)
              val kd_construct =
                case length types of
                  0 => KdConst (kctx, CTypeUnit, KType)
                | 1 => KdAdmit (kctx, hd types, KType)
                | _ => foldli (fn (j, _, kd) =>
                                let
                                  val jkd = extract_judge_kinding kd
                                in
                                  KdBinOp ((#1 jkd, CProd (nth (types, j), #2 jkd), KType), KdAdmit (#1 jkd, nth (types, j), KType), kd)
                                end) (KdBinOp ((kctx, CProd (hd $ tl types, hd types), KType), KdAdmit (kctx, hd $ tl types, KType), KdAdmit (kctx, hd types, KType))) (tl $ tl fev)

              val ty_app_c =
                foldr (fn (j, ty) =>
                         let
                           val jty = extract_judge_typing ty
                           val e = EAppC (#2 jty, CVar j)
                           val (_, k, body) = extract_c_quan (#3 jty)
                           val t = SubstCstr.subst0_c_c (CVar j) body
                           val i = #4 jty
                         in
                           TyAppC ((#1 jty, e, t, i), ty, KdVar (fst $ #1 jty, CVar j, k))
                         end) ty_fix fcv
              val ty_app_c = ShiftCtx.shift0_ctx_ty (map (snd o extract_judge_wfkind) ori_wks, []) ty_app_c
              val ty_app_c =
                foldri (fn (j, _, ty) =>
                          let
                            val jty = extract_judge_typing ty
                            val e = EAppC (#2 jty, CVar j)
                            val (_, k, body) = extract_c_quan (#3 jty)
                            val t = SubstCstr.subst0_c_c (CVar j) body
                            val i = #4 jty
                          in
                            TyAppC ((#1 jty, e, t, i), ty, KdVar (fst $ #1 jty, CVar j, k))
                          end) ty_app_c ori_wks

              val ty_construct = ShiftCtx.shift0_ctx_ty (map (snd o extract_judge_wfkind) ori_wks, []) ty_construct
              val kd_construct = ShiftCtx.shift0_ctx_kd (map (snd o extract_judge_wfkind) ori_wks, []) kd_construct

              val ty_clo = TyPair (as_TyPair ty_app_c ty_construct, ty_app_c, ty_construct)
              val jty_clo = extract_judge_typing ty_clo
              val ty_clo_sub = TySub ((#1 jty_clo, #2 jty_clo, #3 jty_clo, T0), ty_clo, ANF.gen_tyeq_refl (fst $ #1 jty_clo) (#3 jty_clo), PrAdmit (fst $ #1 jty_clo, TLe (#4 jty_clo, T0)))

              val jty_app_c = extract_judge_typing ty_app_c
              val (t_app_c_1, t_app_c_i, t_app_c_2) = extract_c_arrow (#3 jty_app_c)
              val (_, t_app_c_arg) = extract_c_prod t_app_c_1
              val t_app_c = CArrow (CProd (CVar 0, shift_c_c 1 0 t_app_c_arg), shift_c_c 1 0 t_app_c_i, shift_c_c 1 0 t_app_c_2)
              val t_pack = CExists (KType, CProd (t_app_c, CVar 0))
              val kd_t_pack = KdQuan ((fst $ #1 jty_app_c, t_pack, KType), WfKdType (fst $ #1 jty_app_c, KType), KdBinOp ((KType :: (fst $ #1 jty_app_c), CProd (t_app_c, CVar 0), KType), KdAdmit (KType :: (fst $ #1 jty_app_c), t_app_c, KType), KdVar (KType :: (fst $ #1 jty_app_c), CVar 0, KType)))
              val ty_pack = TyPack (as_TyPack kd_t_pack kd_construct ty_clo_sub, kd_t_pack, kd_construct, ty_clo_sub)

              val ty_abs_c = foldli (fn (j, wk, ty) =>
                                      let
                                        val jty = extract_judge_typing ty
                                        val wk = WfKdAdmit (tl $ fst $ #1 jty, hd $ fst $ #1 jty)
                                      in
                                        TyAbsC (as_TyAbsC wk ty, wk, ty)
                                      end) ty_pack ori_wks
            in
              SOME ty_abs_c
            end
        | TyAbs ((ctx, e, t, _), kd, ty_inner) =>
            let
              val (t1, i, t2) = extract_c_arrow t
              val kd = KdArrow ((fst ctx, t, KType), kd, KdAdmit (fst ctx, i, KTime), KdAdmit (fst ctx, t2, KType))
              val ty = ShiftCtx.shift0_ctx_ty ([], [t]) ty
            in
              SOME (on_typing (TyRec (as_TyRec kd ty, kd, ty), (kctx, tctx)))
            end
        | TyApp ((_, _, _, ti), ty1, ty2) =>
            let
              val ty1 = on_typing (ty1, (kctx, tctx))
              val ty2 = on_typing (ty2, (kctx, tctx))
              val jty1 = extract_judge_typing ty1
              val jty2 = extract_judge_typing ty2
              val (_, _, t_clo) = extract_c_quan (#3 jty1)
              val (t_func, t_env) = extract_c_prod t_clo
              val (t1, i, t2) = extract_c_arrow t_func
              val ty3 =
                let
                  val e = EProj (ProjFst, EVar 0)
                  val t = t_func
                  val ctx = (KType :: kctx, t_clo :: map ShiftCstr.shift0_c_c tctx)
                in
                  TyProj ((ctx, e, t, T0), TyVar (ctx, EVar 0, t_clo, T0))
                end
              val ty4 =
                let
                  val jty3 = extract_judge_typing ty3
                  val e = EProj (ProjSnd, EVar 0)
                  val t = t_env
                  val ctx = #1 jty3
                in
                  TyProj ((ctx, e, t, T0), TyVar (ctx, EVar 0, t_clo, T0))
                end
              val ty5 = ShiftCtx.shift0_ctx_ty ([KType], [t_clo]) ty2
              val ty6 = TyPair (as_TyPair ty4 ty5, ty4, ty5)
              val ty7 = TyApp (as_TyApp ty3 ty6, ty3, ty6)
              val ty8 = TyUnpack (as_TyUnpack ty1 ty7, ty1, ty7)
              val jty8 = extract_judge_typing ty8
              val ty9 = TySub ((#1 jty8, #2 jty8, #3 jty8, ti), ty8, ANF.gen_tyeq_refl (fst $ #1 jty8) (#3 jty8), PrAdmit (fst $ #1 jty8, TLe (#4 jty8, ti)))
            in
              SOME ty9
            end
        | TyAppK ((_, _, _, ti), ty1, ty2) =>
            let
              val ty1 = on_typing (ty1, (kctx, tctx))
              val ty2 = on_typing (ty2, (kctx, tctx))
              val jty1 = extract_judge_typing ty1
              val jty2 = extract_judge_typing ty2
              val (_, _, t_clo) = extract_c_quan (#3 jty1)
              val (t_func, t_env) = extract_c_prod t_clo
              val (t1, i, t2) = extract_c_arrow t_func
              val ty3 =
                let
                  val e = EProj (ProjFst, EVar 0)
                  val t = t_func
                  val ctx = (KType :: kctx, t_clo :: map ShiftCstr.shift0_c_c tctx)
                in
                  TyProj ((ctx, e, t, T0), TyVar (ctx, EVar 0, t_clo, T0))
                end
              val ty4 =
                let
                  val jty3 = extract_judge_typing ty3
                  val e = EProj (ProjSnd, EVar 0)
                  val t = t_env
                  val ctx = #1 jty3
                in
                  TyProj ((ctx, e, t, T0), TyVar (ctx, EVar 0, t_clo, T0))
                end
              val ty5 = ShiftCtx.shift0_ctx_ty ([KType], [t_clo]) ty2
              val ty6 = TyPair (as_TyPair ty4 ty5, ty4, ty5)
              val ty7 = TyAppK (as_TyAppK ty3 ty6, ty3, ty6)
              val ty8 = TyUnpack (as_TyUnpack ty1 ty7, ty1, ty7)
              val jty8 = extract_judge_typing ty8
              val ty9 = TySub ((#1 jty8, #2 jty8, #3 jty8, ti), ty8, ANF.gen_tyeq_refl (fst $ #1 jty8) (#3 jty8), PrAdmit (fst $ #1 jty8, TLe (#4 jty8, ti)))
            in
              SOME ty9
            end
        | TyFix _ => raise (Impossible "CloConv")
        | _ => NONE

      fun transformer_tyeq (on_tyeq, on_proping, on_kdeq) (te, (kctx, tctx)) =
        case te of
          TyEqArrow (_, te1, pr, te2) =>
            let
              val te1 = ShiftCtx.shift0_ctx_te ([KType], []) $ on_tyeq (te1, (kctx, tctx))
              val pr = ShiftCtx.shift0_ctx_pr ([KType], []) $ on_proping (pr, (kctx, tctx))
              val te2 = ShiftCtx.shift0_ctx_te ([KType], []) $ on_tyeq (te2, (kctx, tctx))
              val te1 = TyEqBinOp (as_TyEqBinOp CBTypeProd (TyEqVar (KType :: kctx, CVar 0, CVar 0)) te1, TyEqVar (KType :: kctx, CVar 0, CVar 0), te1)
              val te = TyEqArrow (as_TyEqArrow te1 pr te2, te1, pr, te2)
              val ke = KdEqKType (kctx, KType, KType)
              val te = ShiftCtx.shift0_ctx_te ([KType], []) te
              val te = TyEqBinOp (as_TyEqBinOp CBTypeProd te (TyEqVar (KType :: kctx, CVar 0, CVar 0)), te, TyEqVar (KType :: kctx, CVar 0, CVar 0))
            in
              SOME (TyEqQuan (as_TyEqQuan QuanExists ke te, ke, te))
            end
        | TyEqAbs (_, t1, t2) => SOME (TyEqAbs (kctx, transform_type t1, transform_type t2))
        | TyEqTimeAbs (_, t1, t2) => SOME (TyEqTimeAbs (kctx, transform_type t1, transform_type t2))
        | _ => NONE

      fun transformer_kinding (on_kinding, on_wfkind, on_kdeq) (kd, (kctx, tctx)) =
        case kd of
          KdArrow (_, kd1, kd2, kd3) =>
            let
              val kd1 = ShiftCtx.shift0_ctx_kd ([KType], []) $ on_kinding (kd1, (kctx, tctx))
              val kd2 = ShiftCtx.shift0_ctx_kd ([KType], []) $ on_kinding (kd2, (kctx, tctx))
              val kd3 = ShiftCtx.shift0_ctx_kd ([KType], []) $ on_kinding (kd3, (kctx, tctx))
              val kd1 = KdBinOp (as_KdBinOp CBTypeProd (KdVar (KType :: kctx, CVar 0, KType)) kd1, KdVar (KType :: kctx, CVar 0, KType), kd1)
              val kd = KdArrow (as_KdArrow kd1 kd2 kd3, kd1, kd2, kd3)
              val wk = WfKdType (kctx, KType)
              val kd = KdBinOp (as_KdBinOp CBTypeProd kd (KdVar (KType :: kctx, CVar 0, KType)), kd, KdVar (KType :: kctx, CVar 0, KType))
            in
              SOME (KdQuan (as_KdQuan QuanExists wk kd, wk, kd))
            end
        | _ => NONE

      fun transformer_proping _ = NONE
      fun transformer_kdeq _ _ = NONE
      fun transformer_wfkind _ _ = NONE
      fun transformer_wfprop _ _ = NONE
    end)

    fun clo_conv_ty ty = Helper.transform_typing (ty, ([], []))
  end
end
