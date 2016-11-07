functor CloConvPassFun(MicroTiMLDef : SIG_MICRO_TIML_DEF) =
struct
open List
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

open ShiftCstr
open ShiftExpr
open SubstCstr
open SubstExpr

open DerivAssembler
open ShiftCtx
open DirectSubstCstr
open DirectSubstExpr
open DerivFVCstr
open DerivFVExpr
open DerivDirectSubstCstr
open DerivDirectSubstExpr

structure CstrHelper = CstrGenericOnlyDownTransformer(
    struct
    type down = unit

    fun add_kind (_, ()) = ()

    fun transformer_cstr (on_cstr, on_kind) (c, ()) =
      case c of
          CArrow (t1, i, t2) =>
          let
              val t1 = shift0_c_c $ on_cstr (t1, ())
              val i = shift0_c_c i
              val t2 = shift0_c_c $ on_cstr (t2, ())
          in
              SOME (CExists (KType, CProd (CArrow (CProd (CVar 0, t1), i, t2), CVar 0)))
          end
        | CQuan (QuanForall, _, _) =>
          let
              fun unfold_CForalls t ks =
                case t of
                    CQuan (QuanForall, k, t) => unfold_CForalls t (k :: ks)
                  | _ => (t, ks)
              val (t, ks) = unfold_CForalls c []
              val cnt_ks = length ks
              val (t1, i, t2) = extract_c_arrow t
              val t1 = shift_c_c 1 cnt_ks $ on_cstr (t1, ())
              val i = shift_c_c 1 cnt_ks i
              val t2 = shift_c_c 1 cnt_ks $ on_cstr (t2, ())
              val t_inner = CArrow (CProd (CVar cnt_ks, t1), i, t2)
              val t_wrap_CForalls = foldli (fn (i, k, t) => CForall (shift_c_k 1 (cnt_ks - 1 - i) k, t)) t ks
          in
              SOME (CExists (KType, CProd (t_wrap_CForalls, CVar 0)))
          end
        | _ => NONE

    fun transformer_kind _ (k, ()) = SOME k
    fun transformer_prop _ (p, ()) = SOME p
    end)

structure CstrDerivHelper = CstrDerivGenericOnlyDownTransformer(
    struct
    type down = kctx

    fun add_kind (k, kctx) = k :: kctx

    fun on_pr_leaf ((_, p), kctx) = (kctx, p)
    fun on_ke_leaf ((_, k1, k2), kctx) = (kctx, k1, k2)
    fun on_kd_leaf ((_, c, k), kctx) = (kctx, CstrHelper.transform_cstr (c, ()), k)
    fun on_wk_leaf ((_, k), kctx) = (kctx, k)
    fun on_wp_leaf ((_, p), kctx) = (kctx, p)
    fun on_te_leaf ((_, t1, t2), kctx) = (kctx, CstrHelper.transform_cstr (t1, ()), CstrHelper.transform_cstr (t2, ()))

    fun transformer_tyeq (on_tyeq, on_proping, on_kdeq, on_kinding) (te, kctx) =
      case te of
          TyEqQuan ((_, CQuan (QuanForall, _, _), _), _, _) =>
          let
              fun unfold_TyEqQuan te kes =
                case te of
                    TyEqQuan ((_, CQuan (QuanForall, _, _), _), ke, te) => unfold_TyEqQuan te (ke :: kes)
                  | _ => (te, kes)
              val (te, kes) = unfold_TyEqQuan te []
              val (te1, pr, te2) =
                  case te of
                      TyEqArrow (_, te1, pr, te2) => (te1, pr, te2)
                    | _ => raise (Impossible "CloConv")
              val cnt_kes = length kes
              val cur_kctx = (map (fn ke => #2 (extract_judge_kdeq ke)) kes) @ kctx
              val te1 = shift_ctx_te ([KType], cnt_kes) $ on_tyeq (te1, cur_kctx)
              val pr = shift_ctx_pr ([KType], cnt_kes) $ on_proping (pr, cur_kctx)
              val te2 = shift_ctx_te ([KType], cnt_kes) $ on_tyeq (te2, cur_kctx)
              val new_kctx = #1 (extract_judge_tyeq te1)
              val te1 = TyEqBinOp (as_TyEqBinOp CBTypeProd (TyEqVar (new_kctx, CVar cnt_kes, CVar cnt_kes)) te1, TyEqVar (new_kctx, CVar cnt_kes, CVar cnt_kes), te1)
              val te = TyEqArrow (as_TyEqArrow te1 pr te2, te1, pr, te2)
              val te = foldli (fn (j, ke, te) =>
                                  let
                                      val ke = shift_ctx_ke ([KType], cnt_kes - 1 - j) ke
                                  in
                                      TyEqQuan (as_TyEqQuan QuanForall ke te, ke, te)
                                  end) te kes
              val ke = KdEqKType (kctx, KType, KType)
              val te = TyEqBinOp (as_TyEqBinOp CBTypeProd te (TyEqVar (KType :: kctx, CVar 0, CVar 0)), te, TyEqVar (KType :: kctx, CVar 0, CVar 0))
          in
              SOME (TyEqQuan (as_TyEqQuan QuanExists ke te, ke, te))
          end
        | TyEqArrow (_, te1, pr, te2) =>
          let
              val te1 = shift0_ctx_te [KType] $ on_tyeq (te1, kctx)
              val pr = shift0_ctx_pr [KType] $ on_proping (pr, kctx)
              val te2 = shift0_ctx_te [KType] $ on_tyeq (te2, kctx)
              val te1 = TyEqBinOp (as_TyEqBinOp CBTypeProd (TyEqVar (KType :: kctx, CVar 0, CVar 0)) te1, TyEqVar (KType :: kctx, CVar 0, CVar 0), te1)
              val te = TyEqArrow (as_TyEqArrow te1 pr te2, te1, pr, te2)
              val ke = KdEqKType (kctx, KType, KType)
              val te = shift0_ctx_te [KType] te
              val te = TyEqBinOp (as_TyEqBinOp CBTypeProd te (TyEqVar (KType :: kctx, CVar 0, CVar 0)), te, TyEqVar (KType :: kctx, CVar 0, CVar 0))
          in
              SOME (TyEqQuan (as_TyEqQuan QuanExists ke te, ke, te))
          end
        | _ => NONE

    fun transformer_kinding (on_kinding, on_wfkind, on_kdeq) (kd, kctx) =
      case kd of
          KdQuan ((_, CQuan (QuanForall, _, _), _), _, _) =>
          let
              fun unfold_KdQuan kd wks =
                case kd of
                    KdQuan ((_, CQuan (QuanForall, _, _), _), wk, kd) => unfold_KdQuan kd (wk :: wks)
                  | _ => (kd, wks)
              val (kd, wks) = unfold_KdQuan kd []
              val (kd1, kd2, kd3) =
                  case kd of
                      KdArrow (_, kd1, kd2, kd3) => (kd1, kd2, kd3)
                    | _ => raise (Impossible "CloConv")
              val cnt_wks = length wks
              val cur_kctx = (map (snd o extract_judge_wfkind) wks) @ kctx
              val kd1 = shift_ctx_kd ([KType], cnt_wks) $ on_kinding (kd1, cur_kctx)
              val kd2 = shift_ctx_kd ([KType], cnt_wks) $ on_kinding (kd2, cur_kctx)
              val kd3 = shift_ctx_kd ([KType], cnt_wks) $ on_kinding (kd3, cur_kctx)
              val new_kctx = #1 (extract_judge_kinding kd1)
              val kd1 = KdBinOp (as_KdBinOp CBTypeProd (KdVar (new_kctx, CVar cnt_wks, KType)) kd1, KdVar (new_kctx, CVar cnt_wks, KType), kd1)
              val kd = KdArrow (as_KdArrow kd1 kd2 kd3, kd1, kd2, kd3)
              val kd = foldli (fn (i, wk, kd) =>
                                  let
                                      val wk = shift_ctx_wk ([KType], cnt_wks - 1 - i) wk
                                  in
                                      KdQuan (as_KdQuan QuanForall wk kd, wk, kd)
                                  end) kd wks
              val wk = WfKdType (kctx, KType)
              val kd = KdBinOp (as_KdBinOp CBTypeProd kd (KdVar (KType :: kctx, CVar 0, KType)), kd, KdVar (KType :: kctx, CVar 0, KType))
          in
              SOME (KdQuan (as_KdQuan QuanExists wk kd, wk, kd))
          end
        | KdArrow (_, kd1, kd2, kd3) =>
          let
              val kd1 = shift0_ctx_kd [KType] $ on_kinding (kd1, kctx)
              val kd2 = shift0_ctx_kd [KType] $ on_kinding (kd2, kctx)
              val kd3 = shift0_ctx_kd [KType] $ on_kinding (kd3, kctx)
              val kd1 = KdBinOp (as_KdBinOp CBTypeProd (KdVar (KType :: kctx, CVar 0, KType)) kd1, KdVar (KType :: kctx, CVar 0, KType), kd1)
              val kd = KdArrow (as_KdArrow kd1 kd2 kd3, kd1, kd2, kd3)
              val wk = WfKdType (kctx, KType)
              val kd = KdBinOp (as_KdBinOp CBTypeProd kd (KdVar (KType :: kctx, CVar 0, KType)), kd, KdVar (KType :: kctx, CVar 0, KType))
          in
              SOME (KdQuan (as_KdQuan QuanExists wk kd, wk, kd))
          end
        | _ => NONE

    (* need to change the context, so simply use the default transformer *)
    fun transformer_proping _ = NONE
    fun transformer_kdeq _ _ = NONE
    fun transformer_wfkind _ _ = NONE
    fun transformer_wfprop _ _ = NONE
    end)
end
