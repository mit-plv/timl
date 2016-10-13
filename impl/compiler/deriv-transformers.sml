functor DerivTransformers(Time : SIG_TIME) =
struct
  structure MicroTiML = MicroTiML(Time)
  open MicroTiML

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

      fun insert a b c = take (a, b) @ c @ drop (a, b)

      fun on_pr_leaf ((kctx, p), ((kctxd, tctxd), (kdep, tdep))) =
        (insert kctx kdep kctxd, shift_c_p (length kctxd) kdep p)
      fun on_ke_leaf ((kctx, k1, k2), ((kctxd, tctxd), (kdep, tdep))) =
        (insert kctx kdep kctxd, shift_c_k (length kctxd) kdep k1, shift_c_k (length kctxd) kdep k2)
      fun on_kd_leaf ((kctx, c, k), ((kctxd, tctxd), (kdep, tdep))) =
        (insert kctx kdep kctxd, shift_c_c (length kctxd) kdep c, shift_c_k (length kctxd) kdep k)
      fun on_wk_leaf ((kctx, k), ((kctxd, tctxd), (kdep, tdep))) =
        (insert kctx kdep kctxd, shift_c_k (length kctxd) kdep k)
      fun on_wp_leaf ((kctx, p), ((kctxd, tctxd), (kdep, tdep))) =
        (insert kctx kdep kctxd, shift_c_p (length kctxd) kdep p)
      fun on_te_leaf ((kctx, t1, t2), ((kctxd, tctxd), (kdep, tdep))) =
        (insert kctx kdep kctxd, shift_c_c (length kctxd) kdep t1, shift_c_c (length kctxd) kdep t2)
      fun on_ty_leaf (((kctx, tctx), e, t, i), ((kctxd, tctxd), (kdep, tdep))) =
        let
          val kctx = insert kctx kdep kctxd
          val tctx = insert (map (shift_c_c (length kctxd) kdep) tctx) tdep tctxd
        in
          ((kctx, tctx), shift_e_e (length tctxd) tdep (shift_c_e (length kctxd) kdep e),
             shift_c_c (length kctxd) kdep t, shift_c_c (length kctxd) kdep i)
        end

      fun transformer_proping _ = NONE
      fun transformer_kdeq _ _ = NONE
      fun transformer_kinding _ _ = NONE
      fun transformer_wfkind _ _ = NONE
      fun transformer_wfprop _ _ = NONE
      fun transformer_tyeq _ _ = NONE
      fun transformer_typing _ _ = NONE
    end)

    fun shift_ctx_ty ctxd dep ty = Helper.transform_typing (ty, (ctxd, dep))
    fun shift_ctx_kd ctxd dep kd = Helper.transform_kinding (kd, (ctxd, dep))

    fun shift0_ctx_ty ctxd = shift_ctx_ty ctxd (0, 0)
    fun shift0_ctx_kd ctxd = shift_ctx_kd ctxd (0, 0)
  end

  structure ANF =
  struct
    structure DerivAssembler = DerivAssembler(
    struct
      val shift_c_k = ShiftCstr.shift_c_k
      val shift_c_c = ShiftCstr.shift_c_c

      val subst_c_c = SubstCstr.subst_c_c
    end)
    open DerivAssembler

    open ShiftCstr
    open ShiftCtx
    open List

    fun add_kind (k, (kctx, tctx)) = (k :: kctx, map shift0_c_c tctx)
    fun add_type (t, (kctx, tctx)) = (kctx, t :: tctx)

    fun concat_ctx ((kctx1, tctx1), (kctx2, tctx2)) =
      (kctx1 @ kctx2, tctx1 @ map (shift_c_c (length kctx1) 0) tctx2)

    fun normalize_deriv ty = normalize ty (fn (ty, (kctxd, tctxd)) => ty)

    and normalize ty cont =
      case ty of
        TyVar j => cont (ty, ([], []))
      | TyApp (j, ty1, ty2) =>
          normalize_name ty1
            (fn (ty1, d1 as (kctxd1, tctxd1)) =>
               normalize_name (shift0_ctx_ty d1 ty2)
                 (fn (ty2, d2 as (kctxd2, tctxd2)) =>
                    let
                      val ty1 = shift0_ctx_ty d2 ty1
                    in
                      cont (TyApp (as_TyApp ty1 ty2, ty1, ty2), concat_ctx (d2, d1))
                    end))
      | TyAbs (j, kd, ty) =>
          let
            val ty = normalize_deriv ty
          in
            cont (TyAbs (as_TyAbs kd ty, kd, ty), ([], []))
          end
      | TyAppC (j, ty, kd) =>
          normalize_name ty
            (fn (ty, d as (kctxd, tctxd)) =>
               let
                 val kd = shift0_ctx_kd d kd
               in
                 cont (TyAppC (as_TyAppC ty kd, ty, kd), d)
               end)
      | TyAbsC (j, wk, ty) =>
          let
            val ty = normalize_deriv ty
          in
            cont (TyAbsC (as_TyAbsC wk ty, wk, ty), ([], []))
          end
      | TyRec (j, kd, ty) =>
          let
            val ty = normalize_deriv ty
          in
            cont (TyRec (as_TyRec kd ty, kd, ty), ([], []))
          end
      | TyFold (j, kd, ty) =>
          normalize_name ty
            (fn (ty, d as (kctxd, tctxd)) =>
               let
                 val kd = shift0_ctx_kd d kd
               in
                 cont (TyFold (as_TyFold kd ty, kd, ty), d)
               end)
      | TyUnfold (j, ty) =>
          normalize_name ty
            (fn (ty, d as (kctxd, tctxd)) => cont (TyUnfold (as_TyUnfold ty, ty), d))
      | TyPack (j, kd1, kd2, ty) =>
          normalize_name ty
            (fn (ty, d as (kctxd, tctxd)) =>
               let
                 val kd1 = shift0_ctx_kd d kd1
                 val kd2 = shift0_ctx_kd d kd2
               in
                 cont (TyPack (as_TyPack kd1 kd2 ty, kd1, kd2, ty), d)
               end)
      | TyUnpack (j, ty1, ty2) =>
          normalize ty1
            (fn (ty1, d1 as (kctxd1, tctxd1)) =>
            let
                 val jty1 = extract_judge_typing ty1
                 val (_, k, t) = extract_c_quan (#3 jty1)
                 val ty2 = shift_ctx_ty d1 (1, 1) ty2
                 val ty2 = normalize ty2 (fn (ty2, d2 as (kctxd2, tctxd2)) => cont (ty2, concat_ctx (d2, concat_ctx (([k], [t]), d1))))
               in
                 TyUnpack (as_TyUnpack ty1 ty2, ty1, ty2)
               end)
      | _ => raise (Impossible "normalize")

    and normalize_name ty cont =
      normalize ty (fn (ty, d as (kctxd, tctxd)) => cont (ty, d))
  end
end
