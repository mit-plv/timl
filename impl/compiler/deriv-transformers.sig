signature SIG_DERIV_TRANSFOMRERS =
sig
    structure MicroTiMLDef : SIG_MICRO_TIML_DEF

    functor ExprDerivGenericTransformer(
        Action:
        sig
            type kdown
            type tdown
            type down = kdown * tdown
            type up

            val upward_base : up
            val combiner : up * up -> up

            val add_kind : MicroTiMLDef.kind * down -> down
            val add_type : MicroTiMLDef.cstr * tdown -> tdown

            val on_ty_leaf : MicroTiMLDef.typing_judgement * down -> MicroTiMLDef.typing_judgement * up

            val transform_proping : MicroTiMLDef.proping * kdown -> MicroTiMLDef.proping * up
            val transform_kinding : MicroTiMLDef.kinding * kdown -> MicroTiMLDef.kinding * up
            val transform_wfkind : MicroTiMLDef.wfkind * kdown -> MicroTiMLDef.wfkind * up
            val transform_tyeq : MicroTiMLDef.tyeq * kdown -> MicroTiMLDef.tyeq * up

            val transformer_typing : (MicroTiMLDef.typing * down -> MicroTiMLDef.typing * up) -> MicroTiMLDef.typing * down -> (MicroTiMLDef.typing * up) option
                                                                                                                                                  end) :
            sig
                val transform_typing : MicroTiMLDef.typing * Action.down -> MicroTiMLDef.typing * Action.up
            end

    functor CstrDerivGenericOnlyDownTransformer(
    Action:
    sig
        type down

        val add_kind : MicroTiMLDef.kind * down -> down

        val on_pr_leaf : MicroTiMLDef.proping_judgement * down -> MicroTiMLDef.proping_judgement
        val on_ke_leaf : MicroTiMLDef.kdeq_judgement * down -> MicroTiMLDef.kdeq_judgement
        val on_kd_leaf : MicroTiMLDef.kinding_judgement * down -> MicroTiMLDef.kinding_judgement
        val on_wk_leaf : MicroTiMLDef.wfkind_judgement * down -> MicroTiMLDef.wfkind_judgement
        val on_wp_leaf : MicroTiMLDef.wfprop_judgement * down -> MicroTiMLDef.wfprop_judgement
        val on_te_leaf : MicroTiMLDef.tyeq_judgement * down -> MicroTiMLDef.tyeq_judgement

        val transformer_proping : MicroTiMLDef.proping * down -> MicroTiMLDef.proping option
        val transformer_kdeq : (MicroTiMLDef.kdeq * down -> MicroTiMLDef.kdeq) * (MicroTiMLDef.proping * down -> MicroTiMLDef.proping) -> MicroTiMLDef.kdeq * down -> MicroTiMLDef.kdeq option
        val transformer_kinding : (MicroTiMLDef.kinding * down -> MicroTiMLDef.kinding) * (MicroTiMLDef.wfkind * down -> MicroTiMLDef.wfkind) * (MicroTiMLDef.kdeq * down -> MicroTiMLDef.kdeq) -> MicroTiMLDef.kinding * down -> MicroTiMLDef.kinding option
        val transformer_wfkind : (MicroTiMLDef.wfkind * down -> MicroTiMLDef.wfkind) * (MicroTiMLDef.wfprop * down -> MicroTiMLDef.wfprop) -> MicroTiMLDef.wfkind * down -> MicroTiMLDef.wfkind option
        val transformer_wfprop : (MicroTiMLDef.wfprop * down -> MicroTiMLDef.wfprop) * (MicroTiMLDef.kinding * down -> MicroTiMLDef.kinding) -> MicroTiMLDef.wfprop * down -> MicroTiMLDef.wfprop option
        val transformer_tyeq : (MicroTiMLDef.tyeq * down -> MicroTiMLDef.tyeq) * (MicroTiMLDef.proping * down -> MicroTiMLDef.proping) * (MicroTiMLDef.kdeq * down -> MicroTiMLDef.kdeq) * (MicroTiMLDef.kinding * down -> MicroTiMLDef.kinding) -> MicroTiMLDef.tyeq * down -> MicroTiMLDef.tyeq option
    end) :
            sig
                val transform_proping : MicroTiMLDef.proping * Action.down -> MicroTiMLDef.proping
                val transform_kdeq : MicroTiMLDef.kdeq * Action.down -> MicroTiMLDef.kdeq
                val transform_kinding : MicroTiMLDef.kinding * Action.down -> MicroTiMLDef.kinding
                val transform_wfkind : MicroTiMLDef.wfkind * Action.down -> MicroTiMLDef.wfkind
                val transform_wfprop : MicroTiMLDef.wfprop * Action.down -> MicroTiMLDef.wfprop
                val transform_tyeq : MicroTiMLDef.tyeq * Action.down -> MicroTiMLDef.tyeq
            end

    functor ExprDerivGenericOnlyDownTransformer(
        Action:
        sig
            type kdown
            type tdown
            type down = kdown * tdown

            val add_kind : MicroTiMLDef.kind * down -> down
            val add_type : MicroTiMLDef.cstr * tdown -> tdown

            val on_ty_leaf : MicroTiMLDef.typing_judgement * down -> MicroTiMLDef.typing_judgement

            val transform_proping : MicroTiMLDef.proping * kdown -> MicroTiMLDef.proping
            val transform_kinding : MicroTiMLDef.kinding * kdown -> MicroTiMLDef.kinding
            val transform_wfkind : MicroTiMLDef.wfkind * kdown -> MicroTiMLDef.wfkind
            val transform_tyeq : MicroTiMLDef.tyeq * kdown -> MicroTiMLDef.tyeq

            val transformer_typing : (MicroTiMLDef.typing * down -> MicroTiMLDef.typing) -> MicroTiMLDef.typing * down -> MicroTiMLDef.typing option
        end) :
            sig
                val transform_typing : MicroTiMLDef.typing * Action.down -> MicroTiMLDef.typing
            end

    structure DerivAssembler :
              sig
                  val as_KdEqKArrow : MicroTiMLDef.kdeq -> MicroTiMLDef.kdeq -> MicroTiMLDef.kdeq_judgement
                  val as_KdEqKSubset : MicroTiMLDef.kdeq -> MicroTiMLDef.proping -> MicroTiMLDef.kdeq_judgement
                  val as_WfPropQuan : MicroTiMLDef.quan -> MicroTiMLDef.sort -> MicroTiMLDef.wfprop -> MicroTiMLDef.wfprop_judgement
                  val as_WfPropBinPred : MicroTiMLDef.prop_bin_pred -> MicroTiMLDef.kinding -> MicroTiMLDef.kinding -> MicroTiMLDef.wfprop_judgement
                  val as_WfPropNot : MicroTiMLDef.wfprop -> MicroTiMLDef.wfprop_judgement
                  val as_WfPropBinConn : MicroTiMLDef.prop_bin_conn -> MicroTiMLDef.wfprop -> MicroTiMLDef.wfprop -> MicroTiMLDef.wfprop_judgement
                  val as_WfKdSubset : MicroTiMLDef.wfkind -> MicroTiMLDef.wfprop -> MicroTiMLDef.wfkind_judgement
                  val as_WfKdArrow : MicroTiMLDef.wfkind -> MicroTiMLDef.wfkind -> MicroTiMLDef.wfkind_judgement
                  val as_KdEq : MicroTiMLDef.kinding -> MicroTiMLDef.kdeq -> MicroTiMLDef.kinding_judgement
                  val as_KdRef : MicroTiMLDef.kinding -> MicroTiMLDef.kinding_judgement
                  val as_KdRec : string -> MicroTiMLDef.wfkind -> MicroTiMLDef.kinding -> MicroTiMLDef.kinding_judgement
                  val as_KdQuan : MicroTiMLDef.quan -> MicroTiMLDef.wfkind -> MicroTiMLDef.kinding -> MicroTiMLDef.kinding_judgement
                  val as_KdTimeApp : MicroTiMLDef.kinding -> MicroTiMLDef.kinding -> MicroTiMLDef.kinding_judgement
                  val as_KdTimeAbs : MicroTiMLDef.kinding -> MicroTiMLDef.kinding_judgement
                  val as_KdApp : MicroTiMLDef.kinding -> MicroTiMLDef.kinding -> MicroTiMLDef.kinding_judgement
                  val as_KdAbs : MicroTiMLDef.wfkind -> MicroTiMLDef.kinding -> MicroTiMLDef.kinding_judgement
                  val as_KdArrow : MicroTiMLDef.kinding -> MicroTiMLDef.kinding -> MicroTiMLDef.kinding -> MicroTiMLDef.kinding_judgement
                  val as_KdIte : MicroTiMLDef.kinding -> MicroTiMLDef.kinding -> MicroTiMLDef.kinding -> MicroTiMLDef.kinding_judgement
                  val as_KdBinOp : MicroTiMLDef.cstr_bin_op -> MicroTiMLDef.kinding -> MicroTiMLDef.kinding -> MicroTiMLDef.kinding_judgement
                  val as_KdUnOp : MicroTiMLDef.cstr_un_op -> MicroTiMLDef.kinding -> MicroTiMLDef.kinding_judgement
                  val as_TyEqRef : MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq_judgement
                  val as_TyEqRec : string -> string -> MicroTiMLDef.kdeq -> MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq_judgement
                  val as_TyEqBetaRev : MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq_judgement
                  val as_TyEqBeta : MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq_judgement
                  val as_TyEqNat : MicroTiMLDef.kinding -> MicroTiMLDef.kinding -> MicroTiMLDef.proping -> MicroTiMLDef.tyeq_judgement
                  val as_TyEqTimeApp : int -> MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq_judgement
                  val as_TyEqQuan : MicroTiMLDef.quan -> MicroTiMLDef.kdeq -> MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq_judgement
                  val as_TyEqApp : MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq_judgement
                  val as_TyEqArrow : MicroTiMLDef.tyeq -> MicroTiMLDef.proping -> MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq_judgement
                  val as_TyEqIte : MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq_judgement
                  val as_TyEqUnOp : MicroTiMLDef.cstr_un_op -> MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq_judgement
                  val as_TyEqBinOp : MicroTiMLDef.cstr_bin_op -> MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq_judgement
                  val as_TyApp : MicroTiMLDef.typing -> MicroTiMLDef.typing -> MicroTiMLDef.typing_judgement
                  val as_TyAppK : MicroTiMLDef.typing -> MicroTiMLDef.typing -> MicroTiMLDef.typing_judgement
                  val as_TyAbs : MicroTiMLDef.kinding -> MicroTiMLDef.typing -> MicroTiMLDef.typing_judgement
                  val as_TySubTy : MicroTiMLDef.typing -> MicroTiMLDef.tyeq -> MicroTiMLDef.typing_judgement
                  val as_TySubTi : MicroTiMLDef.typing -> MicroTiMLDef.proping -> MicroTiMLDef.typing_judgement
                  val as_TyWrite : MicroTiMLDef.typing -> MicroTiMLDef.typing -> MicroTiMLDef.typing_judgement
                  val as_TyRead : MicroTiMLDef.typing -> MicroTiMLDef.typing_judgement
                  val as_TyNew : MicroTiMLDef.typing -> MicroTiMLDef.typing_judgement
                  val as_TyCase : MicroTiMLDef.typing -> MicroTiMLDef.typing -> MicroTiMLDef.typing -> MicroTiMLDef.typing_judgement
                  val as_TyInj : MicroTiMLDef.injector -> MicroTiMLDef.typing -> MicroTiMLDef.kinding -> MicroTiMLDef.typing_judgement
                  val as_TyProj : MicroTiMLDef.projector -> MicroTiMLDef.typing -> MicroTiMLDef.typing_judgement
                  val as_TyPair : MicroTiMLDef.typing -> MicroTiMLDef.typing -> MicroTiMLDef.typing_judgement
                  val as_TyUnpack : MicroTiMLDef.typing -> MicroTiMLDef.typing -> MicroTiMLDef.typing_judgement
                  val as_TyPack : MicroTiMLDef.kinding -> MicroTiMLDef.kinding -> MicroTiMLDef.typing -> MicroTiMLDef.typing_judgement
                  val as_TyUnfold : MicroTiMLDef.typing -> MicroTiMLDef.typing_judgement
                  val as_TyFold : MicroTiMLDef.kinding -> MicroTiMLDef.typing -> MicroTiMLDef.typing_judgement
                  val as_TyHalt : MicroTiMLDef.typing -> MicroTiMLDef.typing_judgement
                  val as_TyRec : MicroTiMLDef.kinding -> MicroTiMLDef.typing -> MicroTiMLDef.typing_judgement
                  val as_TyFix : MicroTiMLDef.ctx -> MicroTiMLDef.kinding -> MicroTiMLDef.typing -> MicroTiMLDef.typing_judgement
                  val as_TyAbsC : MicroTiMLDef.wfkind -> MicroTiMLDef.typing -> MicroTiMLDef.typing_judgement
                  val as_TyAppC : MicroTiMLDef.typing -> MicroTiMLDef.kinding -> MicroTiMLDef.typing_judgement
                  val as_TyLet : MicroTiMLDef.typing -> MicroTiMLDef.typing -> MicroTiMLDef.typing_judgement
              end

    structure ShiftCtx :
              sig
                  val shift_ctx_ty : ((MicroTiMLDef.kctx * int) * (MicroTiMLDef.tctx * int)) -> MicroTiMLDef.typing -> MicroTiMLDef.typing
                  val shift_ctx_kd : (MicroTiMLDef.kctx * int) -> MicroTiMLDef.kinding -> MicroTiMLDef.kinding
                  val shift_ctx_te : (MicroTiMLDef.kctx * int) -> MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq
                  val shift_ctx_pr : (MicroTiMLDef.kctx * int) -> MicroTiMLDef.proping -> MicroTiMLDef.proping
                  val shift_ctx_wk : (MicroTiMLDef.kctx * int) -> MicroTiMLDef.wfkind -> MicroTiMLDef.wfkind
                  val shift_ctx_ke : (MicroTiMLDef.kctx * int) -> MicroTiMLDef.kdeq -> MicroTiMLDef.kdeq

                  val shift0_ctx_ty : (MicroTiMLDef.kctx * MicroTiMLDef.tctx) -> MicroTiMLDef.typing -> MicroTiMLDef.typing
                  val shift0_ctx_kd : MicroTiMLDef.kctx -> MicroTiMLDef.kinding -> MicroTiMLDef.kinding
                  val shift0_ctx_te : MicroTiMLDef.kctx -> MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq
                  val shift0_ctx_pr : MicroTiMLDef.kctx -> MicroTiMLDef.proping -> MicroTiMLDef.proping
                  val shift0_ctx_wk : MicroTiMLDef.kctx -> MicroTiMLDef.wfkind -> MicroTiMLDef.wfkind
                  val shift0_ctx_ke : MicroTiMLDef.kctx -> MicroTiMLDef.kdeq -> MicroTiMLDef.kdeq
              end

    structure ChangeCtx :
              sig
                  val change_ctx_wk : MicroTiMLDef.kctx -> MicroTiMLDef.wfkind -> MicroTiMLDef.wfkind
                  val change_ctx_kd : MicroTiMLDef.kctx -> MicroTiMLDef.kinding -> MicroTiMLDef.kinding
                  val change_ctx_ty : MicroTiMLDef.ctx -> MicroTiMLDef.typing -> MicroTiMLDef.typing
              end

    structure DerivSubstTyping :
              sig
                  val subst_ty_ty : MicroTiMLDef.typing -> int -> MicroTiMLDef.typing -> MicroTiMLDef.typing
                  val subst0_ty_ty : MicroTiMLDef.typing -> MicroTiMLDef.typing -> MicroTiMLDef.typing
              end

    structure CloConv :
              sig
                  val clo_conv_deriv : MicroTiMLDef.typing -> MicroTiMLDef.typing
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

    structure DerivDirectSubstCstr :
              sig
                  val dsubst_c_ty : MicroTiMLDef.cstr -> int -> MicroTiMLDef.typing -> MicroTiMLDef.typing
                  val dsubst_c_kd : MicroTiMLDef.cstr -> int -> MicroTiMLDef.kinding -> MicroTiMLDef.kinding
                  val dsubst_c_wk : MicroTiMLDef.cstr -> int -> MicroTiMLDef.wfkind -> MicroTiMLDef.wfkind

                  val dsubst0_c_ty : MicroTiMLDef.cstr -> MicroTiMLDef.typing -> MicroTiMLDef.typing
                  val dsubst0_c_kd : MicroTiMLDef.cstr -> MicroTiMLDef.kinding -> MicroTiMLDef.kinding
                  val dsubst0_c_wk : MicroTiMLDef.cstr -> MicroTiMLDef.wfkind -> MicroTiMLDef.wfkind
              end

    structure DerivDirectSubstExpr :
              sig
                  val dsubst_e_ty : MicroTiMLDef.expr -> int -> MicroTiMLDef.typing -> MicroTiMLDef.typing
                  val dsubst0_e_ty : MicroTiMLDef.expr -> MicroTiMLDef.typing -> MicroTiMLDef.typing
              end
end
