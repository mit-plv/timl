functor SimplifyLetPassFun(MicroTiMLDef : SIG_MICRO_TIML_DEF) =
struct
open Util
infixr 0 $

structure MicroTiMLDef = MicroTiMLDef
open MicroTiMLDef
structure MicroTiMLUtil = MicroTiMLUtilFun(MicroTiMLDef)
open MicroTiMLUtil
structure AstTransformers = AstTransformersFun(MicroTiMLDef)
open AstTransformers
structure DerivTransformers = DerivTransformersFun(MicroTiMLDef)
open DerivTransformers

structure DerivAssembler = DerivAssemblerFun(MicroTiMLDef)
open DerivAssembler

open DerivSubstTyping

structure ExprDerivHelper = ExprDerivGenericOnlyDownTransformerFun(
    structure MicroTiMLDef = MicroTiMLDef
    structure Action =
    struct
    type kdown = unit
    type tdown = unit
    type down = kdown * tdown

    fun add_kind (_, ((), ())) = ((), ())
    fun add_type (_, ()) = ()

    fun on_ty_leaf (ty, ((), ())) = ty

    fun transform_proping (pr, ()) = pr
    fun transform_kinding (kd, ()) = kd
    fun transform_wfkind (wk, ()) = wk
    fun transform_tyeq (te, ()) = te

    fun transformer_typing on_typing (ty, ((), ())) =
      case ty of
          TyLet ((_, _, _, i), ty1, ty2) =>
          (case (#2 (extract_judge_typing ty1)) of
               EVar _ =>
               let
                   val ty = on_typing (subst0_ty_ty ty1 ty2, ((), ()))
                   val ((kctx, _), _, _, i') = extract_judge_typing ty
               in
                   SOME (as_TySubTi ty (PrAdmit (kctx, TLe (i', i))))
               end
             | EConst _ =>
               let
                   val ty = on_typing (subst0_ty_ty ty1 ty2, ((), ()))
                   val ((kctx, _), _, _, i') = extract_judge_typing ty
               in
                   SOME (as_TySubTi ty (PrAdmit (kctx, TLe (i', i))))
               end
             | _ => NONE)
        | TyFix ((ctx, _, _, _), kd, ty) => SOME (as_TyFix ctx kd (on_typing (ty, ((), ()))))
        |_ => NONE
    end)

fun simplify_let_deriv ty = ExprDerivHelper.transform_typing (ty, ((), ()))
end
