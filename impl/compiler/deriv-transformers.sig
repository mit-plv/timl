signature SIG_DERIV_ASSEMBLER =
sig
    structure MicroTiMLDef : SIG_MICRO_TIML_DEF

    val as_KdEqKType : MicroTiMLDef.kctx -> MicroTiMLDef.kdeq
    val as_KdEqKArrow : MicroTiMLDef.kdeq -> MicroTiMLDef.kdeq -> MicroTiMLDef.kdeq
    val as_KdEqBaseSort : MicroTiMLDef.kctx -> MicroTiMLDef.sort -> MicroTiMLDef.kdeq
    val as_KdEqSubset : MicroTiMLDef.kdeq -> MicroTiMLDef.proping -> MicroTiMLDef.kdeq
    val as_KdEqSubsetElimLeft : MicroTiMLDef.proping -> MicroTiMLDef.kdeq
    val as_KdEqSubsetElimRight : MicroTiMLDef.proping -> MicroTiMLDef.kdeq
    val as_WfPropTrue : MicroTiMLDef.kctx -> MicroTiMLDef.wfprop
    val as_WfPropFalse : MicroTiMLDef.kctx -> MicroTiMLDef.wfprop
    val as_WfPropQuan : MicroTiMLDef.quan -> MicroTiMLDef.sort -> MicroTiMLDef.wfprop -> MicroTiMLDef.wfprop
    val as_WfPropBinPred : MicroTiMLDef.prop_bin_pred -> MicroTiMLDef.kinding -> MicroTiMLDef.kinding -> MicroTiMLDef.wfprop
    val as_WfPropNot : MicroTiMLDef.wfprop -> MicroTiMLDef.wfprop
    val as_WfPropBinConn : MicroTiMLDef.prop_bin_conn -> MicroTiMLDef.wfprop -> MicroTiMLDef.wfprop -> MicroTiMLDef.wfprop
    val as_WfKdType : MicroTiMLDef.kctx -> MicroTiMLDef.wfkind
    val as_WfKdBaseSort : MicroTiMLDef.kctx -> MicroTiMLDef.sort -> MicroTiMLDef.wfkind
    val as_WfKdSubset : MicroTiMLDef.wfkind -> MicroTiMLDef.wfprop -> MicroTiMLDef.wfkind
    val as_WfKdArrow : MicroTiMLDef.wfkind -> MicroTiMLDef.wfkind -> MicroTiMLDef.wfkind
    val as_KdVar : MicroTiMLDef.kctx -> MicroTiMLDef.var -> MicroTiMLDef.kinding
    val as_KdConst : MicroTiMLDef.kctx -> MicroTiMLDef.cstr_const -> MicroTiMLDef.kinding
    val as_KdEq : MicroTiMLDef.kinding -> MicroTiMLDef.kdeq -> MicroTiMLDef.kinding
    val as_KdRec : MicroTiMLDef.wfkind -> MicroTiMLDef.kinding -> MicroTiMLDef.kinding
    val as_KdQuan : MicroTiMLDef.quan -> MicroTiMLDef.wfkind -> MicroTiMLDef.kinding -> MicroTiMLDef.kinding
    val as_KdTimeApp : MicroTiMLDef.kinding -> MicroTiMLDef.kinding -> MicroTiMLDef.kinding
    val as_KdTimeAbs : MicroTiMLDef.kinding -> MicroTiMLDef.kinding
    val as_KdApp : MicroTiMLDef.kinding -> MicroTiMLDef.kinding -> MicroTiMLDef.kinding
    val as_KdAbs : MicroTiMLDef.wfkind -> MicroTiMLDef.kinding -> MicroTiMLDef.kinding
    val as_KdArrow : MicroTiMLDef.kinding -> MicroTiMLDef.kinding -> MicroTiMLDef.kinding -> MicroTiMLDef.kinding
    val as_KdIte : MicroTiMLDef.kinding -> MicroTiMLDef.kinding -> MicroTiMLDef.kinding -> MicroTiMLDef.kinding
    val as_KdBinOp : MicroTiMLDef.cstr_bin_op -> MicroTiMLDef.kinding -> MicroTiMLDef.kinding -> MicroTiMLDef.kinding
    val as_KdUnOp : MicroTiMLDef.cstr_un_op -> MicroTiMLDef.kinding -> MicroTiMLDef.kinding
    val as_KdTypeNat : MicroTiMLDef.kinding -> MicroTiMLDef.kinding
    val as_KdTypeArr : MicroTiMLDef.kinding -> MicroTiMLDef.kinding -> MicroTiMLDef.kinding
    val as_TyEqVar : MicroTiMLDef.kctx -> MicroTiMLDef.var -> MicroTiMLDef.tyeq
    val as_TyEqConst : MicroTiMLDef.kctx -> MicroTiMLDef.cstr_const -> MicroTiMLDef.tyeq
    val as_TyEqRec : MicroTiMLDef.kdeq -> MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq
    val as_TyEqBetaRev : MicroTiMLDef.kctx -> MicroTiMLDef.cstr -> MicroTiMLDef.cstr -> MicroTiMLDef.tyeq
    val as_TyEqBeta : MicroTiMLDef.kctx -> MicroTiMLDef.cstr -> MicroTiMLDef.cstr -> MicroTiMLDef.tyeq
    val as_TyEqTimeApp : MicroTiMLDef.kctx -> int -> MicroTiMLDef.cstr -> MicroTiMLDef.cstr -> MicroTiMLDef.tyeq
    val as_TyEqQuan : MicroTiMLDef.quan -> MicroTiMLDef.kdeq -> MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq
    val as_TyEqApp : MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq
    val as_TyEqArrow : MicroTiMLDef.tyeq -> MicroTiMLDef.proping -> MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq
    val as_TyEqIte : MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq
    val as_TyEqUnOp : MicroTiMLDef.cstr_un_op -> MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq
    val as_TyEqBinOp : MicroTiMLDef.cstr_bin_op -> MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq
    val as_TyEqAbs : MicroTiMLDef.kctx -> MicroTiMLDef.cstr -> MicroTiMLDef.tyeq
    val as_TyEqTimeAbs : MicroTiMLDef.kctx -> MicroTiMLDef.cstr -> MicroTiMLDef.tyeq
    val as_TyEqTrans : MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq
    val as_TyEqTypeNat : MicroTiMLDef.proping -> MicroTiMLDef.tyeq
    val as_TyEqTypeArr : MicroTiMLDef.tyeq -> MicroTiMLDef.proping -> MicroTiMLDef.tyeq
    val as_TyEqNat : MicroTiMLDef.proping -> MicroTiMLDef.tyeq
    val as_TyEqTime : MicroTiMLDef.proping -> MicroTiMLDef.tyeq
    val as_TyVar : MicroTiMLDef.ctx -> MicroTiMLDef.var -> MicroTiMLDef.typing
    val as_TyConst : MicroTiMLDef.ctx -> MicroTiMLDef.expr_const -> MicroTiMLDef.typing
    val as_TyApp : MicroTiMLDef.typing -> MicroTiMLDef.typing -> MicroTiMLDef.typing
    val as_TyAbs : MicroTiMLDef.kinding -> MicroTiMLDef.typing -> MicroTiMLDef.typing
    val as_TySubTy : MicroTiMLDef.typing -> MicroTiMLDef.tyeq -> MicroTiMLDef.typing
    val as_TySubTi : MicroTiMLDef.typing -> MicroTiMLDef.proping -> MicroTiMLDef.typing
    val as_TyWrite : MicroTiMLDef.typing -> MicroTiMLDef.typing -> MicroTiMLDef.proping -> MicroTiMLDef.typing -> MicroTiMLDef.typing
    val as_TyRead : MicroTiMLDef.typing -> MicroTiMLDef.typing -> MicroTiMLDef.proping -> MicroTiMLDef.typing
    val as_TyNew : MicroTiMLDef.typing -> MicroTiMLDef.typing -> MicroTiMLDef.typing
    val as_TyCase : MicroTiMLDef.typing -> MicroTiMLDef.typing -> MicroTiMLDef.typing -> MicroTiMLDef.typing
    val as_TyInj : MicroTiMLDef.injector -> MicroTiMLDef.typing -> MicroTiMLDef.kinding -> MicroTiMLDef.typing
    val as_TyProj : MicroTiMLDef.projector -> MicroTiMLDef.typing -> MicroTiMLDef.typing
    val as_TyPair : MicroTiMLDef.typing -> MicroTiMLDef.typing -> MicroTiMLDef.typing
    val as_TyUnpack : MicroTiMLDef.typing -> MicroTiMLDef.typing -> MicroTiMLDef.typing
    val as_TyPack : MicroTiMLDef.kinding -> MicroTiMLDef.kinding -> MicroTiMLDef.typing -> MicroTiMLDef.typing
    val as_TyUnfold : MicroTiMLDef.typing -> MicroTiMLDef.typing
    val as_TyFold : MicroTiMLDef.kinding -> MicroTiMLDef.typing -> MicroTiMLDef.typing
    val as_TyHalt : MicroTiMLDef.typing -> MicroTiMLDef.typing
    val as_TyRec : MicroTiMLDef.kinding -> MicroTiMLDef.typing -> MicroTiMLDef.typing
    val as_TyFix : MicroTiMLDef.ctx -> MicroTiMLDef.kinding -> MicroTiMLDef.typing -> MicroTiMLDef.typing
    val as_TyAbsC : MicroTiMLDef.wfkind -> MicroTiMLDef.typing -> MicroTiMLDef.typing
    val as_TyAppC : MicroTiMLDef.typing -> MicroTiMLDef.kinding -> MicroTiMLDef.typing
    val as_TyLet : MicroTiMLDef.typing -> MicroTiMLDef.typing -> MicroTiMLDef.typing
    val as_TyPrimBinOp : MicroTiMLDef.prim_expr_bin_op -> MicroTiMLDef.typing -> MicroTiMLDef.typing -> MicroTiMLDef.typing
end

signature SIG_CSTR_DERIV_GENERIC_TRANSFORMER =
sig
    structure MicroTiMLDef : SIG_MICRO_TIML_DEF

    type down
    type up

    val transform_proping : MicroTiMLDef.proping * down -> MicroTiMLDef.proping * up
    val transform_kdeq : MicroTiMLDef.kdeq * down -> MicroTiMLDef.kdeq * up
    val transform_kinding : MicroTiMLDef.kinding * down -> MicroTiMLDef.kinding * up
    val transform_wfkind : MicroTiMLDef.wfkind * down -> MicroTiMLDef.wfkind * up
    val transform_wfprop : MicroTiMLDef.wfprop * down -> MicroTiMLDef.wfprop * up
    val transform_tyeq : MicroTiMLDef.tyeq * down -> MicroTiMLDef.tyeq * up
end

signature SIG_EXPR_DERIV_GENERIC_TRANSFORMER =
sig
    structure MicroTiMLDef : SIG_MICRO_TIML_DEF

    type down
    type up

    val transform_typing : MicroTiMLDef.typing * down -> MicroTiMLDef.typing * up
end

signature SIG_CSTR_DERIV_GENERIC_ONLY_DOWN_TRANSFORMER =
sig
    structure MicroTiMLDef : SIG_MICRO_TIML_DEF

    type down

    val transform_proping : MicroTiMLDef.proping * down -> MicroTiMLDef.proping
    val transform_kdeq : MicroTiMLDef.kdeq * down -> MicroTiMLDef.kdeq
    val transform_kinding : MicroTiMLDef.kinding * down -> MicroTiMLDef.kinding
    val transform_wfkind : MicroTiMLDef.wfkind * down -> MicroTiMLDef.wfkind
    val transform_wfprop : MicroTiMLDef.wfprop * down -> MicroTiMLDef.wfprop
    val transform_tyeq : MicroTiMLDef.tyeq * down -> MicroTiMLDef.tyeq
end

signature SIG_EXPR_DERIV_GENERIC_ONLY_DOWN_TRANSFORMER =
sig
    structure MicroTiMLDef : SIG_MICRO_TIML_DEF

    type down

    val transform_typing : MicroTiMLDef.typing * down -> MicroTiMLDef.typing
end

signature SIG_DERIV_TRANSFOMRERS =
sig
    structure MicroTiMLDef : SIG_MICRO_TIML_DEF

    structure ShiftCtx :
              sig
                  val shift_ctx_ty : ((MicroTiMLDef.kctx * int) * (MicroTiMLDef.tctx * int)) -> MicroTiMLDef.typing -> MicroTiMLDef.typing
                  val shift_ctx_kd : (MicroTiMLDef.kctx * int) -> MicroTiMLDef.kinding -> MicroTiMLDef.kinding
                  val shift_ctx_te : (MicroTiMLDef.kctx * int) -> MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq
                  val shift_ctx_pr : (MicroTiMLDef.kctx * int) -> MicroTiMLDef.proping -> MicroTiMLDef.proping
                  val shift_ctx_wk : (MicroTiMLDef.kctx * int) -> MicroTiMLDef.wfkind -> MicroTiMLDef.wfkind
                  val shift_ctx_ke : (MicroTiMLDef.kctx * int) -> MicroTiMLDef.kdeq -> MicroTiMLDef.kdeq
                  val shift_ctx_wp : (MicroTiMLDef.kctx * int) -> MicroTiMLDef.wfprop -> MicroTiMLDef.wfprop

                  val shift0_ctx_ty : (MicroTiMLDef.kctx * MicroTiMLDef.tctx) -> MicroTiMLDef.typing -> MicroTiMLDef.typing
                  val shift0_ctx_kd : MicroTiMLDef.kctx -> MicroTiMLDef.kinding -> MicroTiMLDef.kinding
                  val shift0_ctx_te : MicroTiMLDef.kctx -> MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq
                  val shift0_ctx_pr : MicroTiMLDef.kctx -> MicroTiMLDef.proping -> MicroTiMLDef.proping
                  val shift0_ctx_wk : MicroTiMLDef.kctx -> MicroTiMLDef.wfkind -> MicroTiMLDef.wfkind
                  val shift0_ctx_ke : MicroTiMLDef.kctx -> MicroTiMLDef.kdeq -> MicroTiMLDef.kdeq
                  val shift0_ctx_wp : MicroTiMLDef.kctx -> MicroTiMLDef.wfprop -> MicroTiMLDef.wfprop
              end

    structure DropCtx :
              sig
                  val drop_ctx_ty : ((MicroTiMLDef.kctx * (int * int) list) * (MicroTiMLDef.tctx * (int * int) list)) -> MicroTiMLDef.typing -> MicroTiMLDef.typing
                  val drop_ctx_kd : (MicroTiMLDef.kctx * (int * int) list) -> MicroTiMLDef.kinding -> MicroTiMLDef.kinding
                  val drop_ctx_ke : (MicroTiMLDef.kctx * (int * int) list) -> MicroTiMLDef.kdeq -> MicroTiMLDef.kdeq
                  val drop_ctx_wk : (MicroTiMLDef.kctx * (int * int) list) -> MicroTiMLDef.wfkind -> MicroTiMLDef.wfkind
                  val drop_ctx_wp : (MicroTiMLDef.kctx * (int * int) list) -> MicroTiMLDef.wfprop -> MicroTiMLDef.wfprop
                  val drop_ctx_te : (MicroTiMLDef.kctx * (int * int) list) -> MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq
                  val drop_ctx_pr : (MicroTiMLDef.kctx * (int * int) list) -> MicroTiMLDef.proping -> MicroTiMLDef.proping
              end

    structure DerivFVCstr :
              sig
                  val free_vars_c_ty : int -> MicroTiMLDef.typing -> int list
                  val free_vars0_c_ty : MicroTiMLDef.typing -> int list
              end

    structure DerivFVExpr :
              sig
                  val free_vars_e_ty : int -> MicroTiMLDef.typing -> int list
                  val free_vars0_e_ty : MicroTiMLDef.typing -> int list
              end

    structure DerivSubstKinding :
              sig
                  val subst_kd_kd : MicroTiMLDef.kinding -> int -> MicroTiMLDef.kinding -> MicroTiMLDef.kinding
                  val subst0_kd_kd : MicroTiMLDef.kinding -> MicroTiMLDef.kinding -> MicroTiMLDef.kinding
              end

    structure DerivSubstTyping :
              sig
                  val subst_ty_ty : MicroTiMLDef.typing -> int -> MicroTiMLDef.typing -> MicroTiMLDef.typing
                  val subst0_ty_ty : MicroTiMLDef.typing -> MicroTiMLDef.typing -> MicroTiMLDef.typing
              end
end
