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

    fun shift0_ctx_ty ctxd = shift_ctx_ty ctxd (0, 0)
    fun shift0_ctx_kd ctxd = shift_ctx_kd ctxd (0, 0)
    fun shift0_ctx_te ctxd = shift_ctx_te ctxd (0, 0)
    fun shift0_ctx_pr ctxd = shift_ctx_pr ctxd (0, 0)
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

    fun dsubst0_c_ty to = dsubst_c_ty to 0
    fun dsubst0_c_kd to = dsubst_c_kd to 0
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

    val change0_ctx_ty = change_ctx_ty ([], [])
    val change0_ctx_kd = change_ctx_kd ([], [])
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

  structure CloConv =
  struct
    structure Helper = DerivGenericOnlyDownTransformer(
    struct
      type down = unit

      val shift_c_k = ShiftCstr.shift_c_k
      val shift_c_c = ShiftCstr.shift_c_c

      val subst_c_c = SubstCstr.subst_c_c

      fun add_kind (_, ()) = ()
      fun add_type (_, ()) = ()

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
              CExists (KType, CProd (CArrow (ShiftCstr.shift0_c_c t1, ShiftCstr.shift0_c_c i, ShiftCstr.shift0_c_c t2), CVar 0))
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

      fun on_pr_leaf (pr, ()) = pr
      fun on_ke_leaf (ke, ()) = ke
      fun on_kd_leaf ((kctx, c, k), ()) = (kctx, transform_type c, k)
      fun on_wk_leaf (wk, ()) = wk
      fun on_wp_leaf (wp, ()) = wp
      fun on_te_leaf (te, ()) = te
      fun on_ty_leaf (ty as ((kctx, tctx), e, t, i), ()) =
        case e of
          EVar x => ((kctx, tctx), e, List.nth (tctx, x), T0)
        | EConst cn => ((kctx, tctx), e, const_type cn, T0)
        | _ => raise (Impossible "CloConv")

      fun transformer_typing (on_typing, on_kinding, on_wfkind, on_tyeq, on_proping) (ty, ()) =
        case ty of
          TyRec (j, kd, ty_inner) =>
            let
              val fcv = free_vars0_c_ty ty
              val fev = free_vars0_e_ty ty
              val jty = extract_judge_typing ty
              val kinds = map (fn x => shift_c_k (1 + x) 0 (nth (fst $ #1 jty, x))) fcv
              val new_kinds = snd $ ListPair.unzip $
                foldri (fn (i, (x, k), kctx) =>
                          (x, foldli (fn (j, (x, _), k) =>
                                        dsubst_c_k (CVar j) x k) k kctx) :: kctx) [] $ ListPair.zip (fcv, kinds)
              val types = map (fn x => nth (snd $ #1 jty, x)) fev
              val new_types = map (fn t => foldli (fn (j, x, t) => dsubst_c_c (CVar j) x t) t fcv) types

              fun unfold ty wks =
                case ty of
                  TyAbsC (j, wk, ty) => unfold ty (wk :: wks)
                | _ => (ty, wks)
              val (ty_abs, wks) = unfold ty_inner []
              val (j_abs, kd_abs, ty_abs_body) =
                case ty_abs of
                  TyAbs a => a
                | _ => raise (Impossible "closure conversion")

              val ori_kinds = map (snd o extract_judge_wfkind) wks
              val new_ori_kinds = mapi (fn (i, k) => foldli (fn (j, x, k) => dsubst_c_k (CVar (j + length wks - 1 - i)) (x + length wks - 1 - i) k) k fcv) ori_kinds
              val new_types = map (shift_c_c (length wks) 0) new_types

              val kctx_rec = new_ori_kinds @ new_kinds

              val t_env =
                case length new_types of
                  0 => CTypeUnit
                | 1 => hd new_types
                | _ => foldl (fn (a, b) => CProd (a, b)) (CProd (hd $ tl new_types, hd new_types)) (tl $ tl new_types)

              val t_arrow_self = foldli (fn (j, x, t) => dsubst_c_c (CVar (j + length wks)) (x + length wks) t) (#3 j_abs) fcv
              val (t_arrow_1, t_arrow_i, t_arrow_2) = extract_c_arrow t_arrow_self
              val t_arrow_1 = transform_type t_arrow_1
              val t_arrow_i = transform_type t_arrow_i
              val t_arrow_2 = transform_type t_arrow_2
              val t_arrow_self = CArrow (CProd (t_env, t_arrow_1), t_arrow_i, t_arrow_2)
              val t_partial_self = foldl (fn (a, b) => CForall (a, b)) t_arrow_self new_ori_kinds
              val t_self = foldl (fn (a, b) => CForall (a, b)) t_partial_self new_kinds

              val t_arrow_self_exi = CArrow (CProd (CVar (length wks), t_arrow_1), t_arrow_i, t_arrow_2)
              val t_partial_self_exi = foldl (fn (a, b) => CForall (a, b)) t_arrow_self_exi new_ori_kinds

              val jkd_abs = extract_judge_kinding kd_abs
              val t_arg = foldli (fn (j, x, t) => dsubst_c_c (CVar (j + length wks + 1)) (x + length wks) t) (#2 jkd_abs) fcv
              val t_param = CProd (t_env, t_arg)

              val tctx_rec = [t_param, t_self]

              val tctx_unwrap_env =
                case length new_types of
                  0 => tctx_rec
                | 1 => t_env :: tctx_rec
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
                            inner (t1 :: tctx) (d - 1) t2
                          end
                    in
                      inner (t_env :: tctx_rec) (length new_types - 2) t_env
                    end
              val tctx_get_self = CExists (KType, CProd (shift_c_c (length wks + 1) 1 t_partial_self_exi, CVar 0)) :: tctx_unwrap_env
              val tctx_unwrap_arg = t_arg :: tctx_get_self

              val new_ty_abs_body = ty_abs_body
              val new_ty_abs_body = foldli (fn (j, x, ty) => dsubst_c_ty (CVar (j + length wks)) (x + length wks) ty) new_ty_abs_body fcv
              val new_ty_abs_body = foldli (fn (j, x, ty) => dsubst_e_ty (EVar (if j = 0 then 2 else 2 * j + 1)) (x + 2) ty) new_ty_abs_body fev
              val new_ty_abs_body = change_ctx_ty (kctx_rec, tctx_unwrap_arg) new_ty_abs_body
              val new_ty_abs_body = on_typing (new_ty_abs_body, ())

              val new_ty_abs_body_wrap_arg =
                let
                  val param_idx = length tctx_get_self - 2
                  val tmp_ty = TyProj (((kctx_rec, tctx_get_self), EProj (ProjSnd, EVar param_idx), t_arg, T0), TyVar ((kctx_rec, tctx_get_self), EVar param_idx, t_param, T0))
                in
                  TyLet (as_TyLet tmp_ty new_ty_abs_body, tmp_ty, new_ty_abs_body)
                end
              val new_ty_abs_body_unget_self =
                let
                  val param_idx = length tctx_unwrap_env - 2
                  val ty1 = TyProj (((kctx_rec, tctx_unwrap_env), EProj (ProjFst, EVar param_idx), t_env, T0), TyVar ((kctx_rec, tctx_unwrap_env), EVar param_idx, t_param, T0))
                  val ty2 = TyVar ((kctx_rec, tctx_unwrap_env), EVar (param_idx + 1), t_self, T0)
                  val ty3 = foldri (fn (j, _, ty) =>
                                      let
                                        val jty = extract_judge_typing ty
                                        val e = EAppC (#2 jty, CVar (j + length wks))
                                        val i = #4 jty
                                        val (_, k, body) = extract_c_quan (#3 jty)
                                        val t = SubstCstr.subst0_c_c (CVar (j + length wks)) body
                                      in
                                        TyAppC ((#1 jty, e, t, i), ty, KdVar (fst $ #1 jty, CVar (j + length wks), k))
                                      end) ty2 new_kinds
                  val ty4 = TyPair (as_TyPair ty3 ty1, ty3, ty1)
                  val kd1 = KdAdmit (kctx_rec, t_env, KType)
                  val kd2 = KdAdmit (kctx_rec, CExists (KType, CProd (shift_c_c (length wks + 1) 1 t_partial_self_exi ,CVar 0)), KType)
                  val ty5 = TyPack (as_TyPack kd2 kd1 ty4, kd2, kd1, ty4)
                in
                  TyLet (as_TyLet ty5 new_ty_abs_body_wrap_arg, ty5, new_ty_abs_body_wrap_arg)
                end
              val new_ty_abs_body_wrap_env =
                case length new_types of
                  0 => new_ty_abs_body_unget_self
                | 1 =>
                    let
                      val tmp_ty = TyProj (((kctx_rec, tctx_rec), EProj (ProjFst, EVar 0), t_env, T0), TyVar ((kctx_rec, tctx_rec), EVar 0, t_param, T0))
                    in
                      TyLet (as_TyLet tmp_ty new_ty_abs_body_unget_self, tmp_ty, new_ty_abs_body_unget_self)
                    end
                | _ =>
                    let
                      val tylet2 =
                        foldli (fn (i, t, ty) =>
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
                                    end) new_ty_abs_body_unget_self (take (tctx_unwrap_env, length tctx_unwrap_env - 3))
                      val tylet1 = TyProj (((kctx_rec, tctx_rec), EProj (ProjFst, EVar 0), t_env, T0), TyVar ((kctx_rec, tctx_rec), EVar 0, t_param, T0))
                    in
                      TyLet (as_TyLet tylet1 tylet2, tylet1, tylet2)
                    end

              val jnew_ty_abs_body_wrap_env = extract_judge_typing new_ty_abs_body_wrap_env
              val jnew_ty_abs_body = extract_judge_typing new_ty_abs_body
              val new_ty_abs_body_wrap_env_sub =
                TySub ((#1 jnew_ty_abs_body_wrap_env, #2 jnew_ty_abs_body_wrap_env, #3 jnew_ty_abs_body, #4 jnew_ty_abs_body), new_ty_abs_body_wrap_env, ANF.gen_tyeq_refl kctx_rec (#3 jnew_ty_abs_body), PrAdmit (kctx_rec, TLe (#4 jnew_ty_abs_body_wrap_env, #4 jnew_ty_abs_body)))

              val kd_self = KdAdmit ([], t_self, KType)
              val ty_fix = TyFix (as_TyFix (#1 j) kd_self new_ty_abs_body_wrap_env_sub, kd_self, new_ty_abs_body_wrap_env_sub)

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
              val ty_construct =
                case length types of
                  0 => TyConst (#1 j, EConst ECTT, CTypeUnit, T0)
                | 1 => TyVar (#1 j, EVar (hd fev), hd types, T0)
                | _ => foldl (fn (j, ty) =>
                                let
                                  val jty = extract_judge_typing ty
                                  val e = EPair (EVar j, #2 jty)
                                  val t = CProd (nth (types, j), #3 jty)
                                  val i = Tadd (T0, #4 jty)
                                in
                                  TyPair ((#1 jty, e, t, i), TyVar (#1 jty, EVar j, nth (types, j), T0), ty)
                                end) (TyPair ((#1 j, EPair (EVar (hd $ tl fev), EVar (hd fev)), CProd (hd $ tl types, hd types), Tadd (T0, T0)), TyVar (#1 j, EVar (hd $ tl fev), hd $ tl types, T0), TyVar (#1 j, EVar (hd fev), hd types, T0))) (tl $ tl fev)
              val ty_clo = TyPair (as_TyPair ty_app_c ty_construct, ty_app_c, ty_construct)
              val jty_clo = extract_judge_typing ty_clo
              val ty_clo_sub = TySub ((#1 jty_clo, #2 jty_clo, #3 jty_clo, T0), ty_clo, ANF.gen_tyeq_refl (fst $ #1 jty_clo) (#3 jty_clo), PrAdmit (fst $ #1 jty_clo, TLe (#4 jty_clo, T0)))
              val jty_construct = extract_judge_typing ty_construct
              val jty_app_c = extract_judge_typing ty_app_c
              val pack_kd2 = KdAdmit (fst $ #1 j, #3 jty_construct, KType)
              val t_pack = CExists (KType, CProd (shift_c_c 1 1 t_partial_self_exi, CVar 0))
              val pack_kd1 = KdAdmit (fst $ #1 j, t_pack, KType)
              val ty_pack = TyPack (as_TyPack pack_kd1 pack_kd2 ty_clo_sub, pack_kd1, pack_kd2, ty_clo_sub)
            in
              SOME ty_pack
            end
        | TyAbs (j, kd, ty_inner) =>
            let
              val body = extract_e_abs (#2 j)
              val kd = KdAdmit (fst $ #1 j, #3 j, KType)
              val ty = ShiftCtx.shift0_ctx_ty ([], [#3 j]) ty
            in
              SOME (on_typing (TyRec (as_TyRec kd ty, kd, ty), ()))
            end
        | TyAbsC (j, wk, ty_inner) =>
            let
              val body = extract_e_abs_c (#2 j)
              val kd = KdAdmit (fst $ #1 j, #3 j, KType)
              val ty = ShiftCtx.shift0_ctx_ty ([], [#3 j]) ty
            in
              SOME (on_typing (TyRec (as_TyRec kd ty, kd, ty), ()))
            end
        | TyApp (j, ty1, ty2) =>
            let
              val ty1 = on_typing (ty1, ())
              val ty2 = on_typing (ty2, ())
              val jty1 = extract_judge_typing ty1
              val jty2 = extract_judge_typing ty2
              val (_, _, t_clo) = extract_c_quan (#3 jty1)
              val (t_func, t_env) = extract_c_prod t_clo
              val (t1, i, t2) = extract_c_arrow t_func
              val ty3 =
                let
                  val e = EProj (ProjFst, EVar 0)
                  val t = t_func
                  val ctx = (KType :: fst (#1 j), t_clo :: map ShiftCstr.shift0_c_c (snd (#1 j)))
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
              val ty9 = TySub ((#1 jty8, #2 jty8, #3 jty8, #4 j), ty8, ANF.gen_tyeq_refl (fst $ #1 jty8) (#3 jty8), PrAdmit (fst $ #1 jty8, TLe (#4 jty8, #4 j)))
            in
              SOME ty9
            end
        | TyAppC (j, ty, kd) =>
            let
              val ty = on_typing (ty, ())
              val jkd = extract_judge_kinding kd
              val jty = extract_judge_typing ty
              val (_, _, t_clo) = extract_c_quan (#3 jty)
              val (t_func, t_env) = extract_c_prod t_clo
              val (_, _, t_body) = extract_c_quan t_func
              val ty1 =
                let
                  val e = EProj (ProjFst, EVar 0)
                  val t = t_func
                  val ctx = (KType :: fst (#1 j), t_clo :: map ShiftCstr.shift0_c_c (snd (#1 j)))
                in
                  TyProj ((ctx, e, t, T0), TyVar (ctx, EVar 0, t_clo, T0))
                end
              val ty2 =
                let
                  val jty1 = extract_judge_typing ty1
                  val e = EAppC (#2 jty1, ShiftCstr.shift0_c_c (#2 jkd))
                  val t = SubstCstr.subst0_c_c (ShiftCstr.shift0_c_c (#2 jkd)) t_body
                  val ctx = #1 jty1
                in
                  TyAppC ((ctx, e, t, T0), ty1, ShiftCtx.shift0_ctx_kd ([KType], [t_clo]) kd)
                end
              val ty3 =
                let
                  val jty2 = extract_judge_typing ty2
                  val e = EProj (ProjSnd, EVar 0)
                  val t = t_env
                  val ctx = #1 jty2
                in
                  TyProj ((ctx, e, t, T0), TyVar (ctx, EVar 0, t_clo, T0))
                end
              val ty4 = TyPair (as_TyPair ty2 ty3, ty2, ty3)
              val kd2 = KdVar (KType :: fst (#1 j), CVar 0, KType)
              val t_pack = CExists (KType, CProd (shift_c_c 1 1 $ #3 (extract_judge_typing ty2), CVar 0))
              val kd1 = KdAdmit (KType :: fst (#1 j), t_pack, KType)
              val ty5 = TyPack (as_TyPack kd1 kd2 ty4, kd1, kd2, ty4)
              val ty6 = TyUnpack (as_TyUnpack ty ty5, ty, ty5)
              val jty6 = extract_judge_typing ty6
              val ty7 = TySub ((#1 jty6, #2 jty6, #3 jty6, #4 jty), ty6, ANF.gen_tyeq_refl (fst $ #1 jty6) (#3 jty6), PrAdmit (fst $ #1 jty6, TLe (#4 jty6, #4 jty)))
            in
              SOME ty7
            end
        | TyFix _ => raise (Impossible "CloConv")
        | _ => NONE


      fun transformer_tyeq (on_tyeq, on_proping, on_kdeq) (te, ()) =
        case te of
          TyEqArrow (j, te1, pr, te2) =>
            let
              val te1 = on_tyeq (te1, ())
              val pr = on_proping (pr, ())
              val te2 = on_tyeq (te2, ())
              val te = TyEqArrow (as_TyEqArrow te1 pr te2, te1, pr, te2)
              val jte = extract_judge_tyeq te
              val ke = KdEqKType (#1 jte, KType, KType)
              val te = ShiftCtx.shift0_ctx_te ([KType], []) te
            in
              SOME (TyEqQuan (as_TyEqQuan QuanExists ke te, ke, te))
            end
        | TyEqAbs j => SOME (TyEqAbs (#1 j, transform_type (#2 j), transform_type (#3 j)))
        | TyEqTimeAbs j => SOME (TyEqTimeAbs (#1 j, transform_type (#2 j), transform_type (#3 j)))
        | _ => NONE

      fun transformer_kinding (on_kinding, on_wfkind, on_kdeq) (kd, ()) =
        case kd of
          KdArrow (j, kd1, kd2, kd3) =>
            let
              val kd1 = on_kinding (kd1, ())
              val kd2 = on_kinding (kd2, ())
              val kd3 = on_kinding (kd3, ())
              val kd = KdArrow (as_KdArrow kd1 kd2 kd3, kd1, kd2, kd3)
              val jkd = extract_judge_kinding kd
              val wk = WfKdType (#1 jkd, KType)
              val kd = ShiftCtx.shift0_ctx_kd ([KType], []) kd
            in
              SOME (KdQuan (as_KdQuan QuanExists wk kd, wk, kd))
            end
        | _ => NONE

      fun transformer_proping _ = NONE
      fun transformer_kdeq _ _ = NONE
      fun transformer_wfkind _ _ = NONE
      fun transformer_wfprop _ _ = NONE
    end)

    fun clo_conv_ty ty = Helper.transform_typing (ty, ())
  end
end
