functor CloConvPassFun(MicroTiMLDef : SIG_MICRO_TIML_DEF) : SIG_CLO_CONV_PASS =
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
open ChangeCtx
open DirectSubstCstr
open DirectSubstExpr
open DerivFVCstr
open DerivFVExpr
open DerivDirectSubstCstr
open DerivDirectSubstExpr
open DerivSubstKinding

fun meta_lemma1 ty =
  let
      val ((kctx, _), _, t, i) = extract_judge_typing ty
  in
      (KdAdmit (kctx, t, KType), KdAdmit (kctx, i, KTime))
  end

fun meta_lemma2 kd =
  let
      val (kctx, _, k) = extract_judge_kinding kd
  in
      WfKdAdmit (kctx, k)
  end

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
              val t_wrap_CForalls = foldli (fn (i, k, t) => CForall (shift_c_k 1 (cnt_ks - 1 - i) k, t)) t_inner ks
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

structure ExprDerivHelper = ExprDerivGenericOnlyDownTransformer(
    struct
    type kdown = kctx
    type tdown = tctx
    type down = kdown * tdown

    fun add_kind (k, (kctx, tctx)) = (k :: kctx, map (shift_c_c 1 0) tctx)
    fun add_type (t, tctx) = t :: tctx

    fun on_ty_leaf ((_, e, _, _), (kctx, tctx)) =
      case e of
          EVar x => ((kctx, tctx), e, List.nth (tctx, x), T0)
        | EConst cn  => ((kctx, tctx), e, const_type cn, T0)
        | _ => raise (Impossible "CloConv")

    val transform_proping = CstrDerivHelper.transform_proping
    val transform_kinding = CstrDerivHelper.transform_kinding
    val transform_wfkind = CstrDerivHelper.transform_wfkind
    val transform_tyeq = CstrDerivHelper.transform_tyeq

    fun transformer_typing on_typing (ty, (kctx, tctx)) =
      case ty of
          TyLet (_, TyRec (_, _, ty_inner), ty_after) =>
          let
              fun unfold_ty ty wks =
                case ty of
                    TyAbsC (j, wk, ty) => unfold_ty ty (wk :: wks)
                  | TySubTi _ => raise (Impossible "not supported")
                  | TySubTy _ => raise (Impossible "not supported")
                  | _ => (ty, wks)
              val (ty_abs, ori_wks) = unfold_ty ty_inner []
              val (kd_arg, ty_body) =
                  case ty_abs of
                      TyAbs (_, kd_arg, ty_body) => (kd_arg, ty_body)
                    | TySubTi _ => raise (Impossible "not supported")
                    | TySubTy _ => raise (Impossible "not supported")
                    | _ => raise (Impossible "CloConv")
              val fcv = free_vars0_c_ty ty
              val fev = free_vars0_e_ty ty
              val free_kinds = map (fn x => shift_c_k (1 + x) 0 $ nth (kctx, x)) fcv
              val new_free_kinds = snd $ ListPair.unzip $
                                  foldri (fn (i, (x, k), pairs) =>
                                             (x, foldli (fn (j, (y, _), k) => dsubst_c_k (CVar j) y k) k pairs) :: pairs)
                                  [] (ListPair.zip (fcv, free_kinds))
              val free_wks = map (fn x => meta_lemma2 (KdVar (kctx, CVar x, shift_c_k (1 + x) 0 $ nth (kctx, x)))) fcv
              val new_free_wks = snd $ ListPair.unzip $
                                     foldri (fn (i, (x, wk), pairs) =>
                                                let
                                                    val wk = foldli (fn (j, (y, _), wk) => dsubst_c_wk (CVar j) y wk) wk pairs
                                                    val wk = change_ctx_wk (map (snd o extract_judge_wfkind o snd) pairs) wk
                                                in
                                                    (x, wk) :: pairs
                                                end)
                                     [] (ListPair.zip (fcv, free_wks))
              val free_types = map (fn x => nth (tctx, x)) fev
              val free_kds = map (fn x => fst $ meta_lemma1 (TyVar ((kctx, tctx), EVar x, nth (tctx, x), T0))) fev
              val new_free_types = map (fn t => foldli (fn (j, x, t) => dsubst_c_c (CVar j) x t) t fcv) free_types
              val new_free_kds = map (fn kd =>
                                         let
                                             val kd = foldli (fn (j, x, kd) => dsubst_c_kd (CVar j) x kd) kd fcv
                                             val kd = change_ctx_kd new_free_kinds kd
                                         in
                                             kd
                                         end) free_kds
              val cnt_ori_kinds = length ori_wks

              val new_ori_wks = mapi (fn (i, wk) => foldli (fn (j, x, wk) => dsubst_c_wk (CVar (j + cnt_ori_kinds - 1 - i)) (x + cnt_ori_kinds - 1 - i) wk) wk fcv) ori_wks
              val (new_all_kinds, new_ori_wks) = foldr
                                                     (fn (wk, (kinds, wks)) =>
                                                         let
                                                             val (_, k) = extract_judge_wfkind wk
                                                             val wk = transform_wfkind (wk, kinds)
                                                         in
                                                             (k :: kinds, wk :: wks)
                                                         end) (new_free_kinds, []) new_ori_wks
              val new_ori_kinds = List.take (new_all_kinds, cnt_ori_kinds)
              val new_free_types = map (shift_c_c cnt_ori_kinds 0) new_free_types
              val new_free_kds = map (shift0_ctx_kd new_ori_kinds) new_free_kds

              val new_kd_arg = foldli (fn (j, x, kd) => dsubst_c_kd (CVar (j + cnt_ori_kinds)) (x + cnt_ori_kinds) kd) kd_arg fcv
              val new_kd_arg = transform_kinding (new_kd_arg, new_all_kinds)
              val (_, new_t_arg, _) = extract_judge_kinding new_kd_arg
              val (kd_res, kd_time) = meta_lemma1 ty_body
              val new_kd_time = foldli (fn (j, x, kd) => dsubst_c_kd (CVar (j + cnt_ori_kinds)) (x + cnt_ori_kinds) kd) kd_time fcv
              val new_kd_time = transform_kinding (new_kd_time, new_all_kinds)
              val (_, new_i_abs, _) = extract_judge_kinding new_kd_time
              val new_kd_res = foldli (fn (j, x, kd) => dsubst_c_kd (CVar (j + cnt_ori_kinds)) (x + cnt_ori_kinds) kd) kd_res fcv
              val new_kd_res = transform_kinding (new_kd_res, new_all_kinds)
              val (_, new_t_res, _) = extract_judge_kinding new_kd_res

              val new_kd_env = foldl (fn (kd, kd_env) =>
                                         KdBinOp (as_KdBinOp CBTypeProd kd kd_env, kd, kd_env))
                                     (KdConst (new_all_kinds, CTypeUnit, KType)) new_free_kds
              val (_, new_t_env, _) = extract_judge_kinding new_kd_env
              val new_kd_param = KdBinOp (as_KdBinOp CBTypeProd new_kd_env new_kd_arg, new_kd_env, new_kd_arg)
              val (_, new_t_param, _) = extract_judge_kinding new_kd_param

              val new_kd_arrow = KdArrow (as_KdArrow new_kd_param new_kd_time new_kd_res, new_kd_param, new_kd_time, new_kd_res)
              val (_, new_t_arrow, _) = extract_judge_kinding new_kd_arrow
              val new_kd_self = foldl (fn (wk, kd) => KdQuan (as_KdQuan QuanForall wk kd, wk, kd)) new_kd_arrow (new_ori_wks @ new_free_wks)
              val (_, new_t_self, _) = extract_judge_kinding new_kd_self

              val new_kctx_base = new_all_kinds
              val new_tctx_base = [new_t_param, new_t_self]

              val new_tctx_env =
                  let
                      fun inner t tctx =
                        case t of
                            CBinOp (CBTypeProd, t1, t2) =>
                            inner t2 (t2 :: t1 :: tctx)
                          | _ => tctx
                  in
                      inner new_t_env (new_t_env :: new_tctx_base)
                  end

              val new_kd_self_partial_unpacked =
                  let
                      val kd1 = shift0_ctx_kd new_kctx_base new_kd_self
                      val kd2 = foldri (fn (i, _, kd) =>
                                           let
                                               val (wk, kd_body) = case kd of
                                                                       KdQuan (_, wk, kd_body) => (wk, kd_body)
                                                                     | KdEq _ => raise (Impossible "not supported")
                                                                     | _ => raise (Impossible "CloConv")
                                               val to = KdVar (new_kctx_base, CVar (i + cnt_ori_kinds), shift_c_k (1 + i + cnt_ori_kinds) 0 $ nth (new_kctx_base, i + cnt_ori_kinds))
                                           in
                                               subst0_kd_kd to kd_body
                                           end) kd1 new_free_wks
                      val kd3 = KdBinOp (as_KdBinOp CBTypeProd kd2 new_kd_env, kd2, new_kd_env)
                  in
                      kd3
                  end

              val new_kd_self_partial =
                  let
                      val kd1 = shift0_ctx_kd new_kctx_base new_kd_self
                      val kd2 = foldri (fn (i, _, kd) =>
                                           let
                                               val (wk, kd_body) = case kd of
                                                                       KdQuan (_, wk, kd_body) => (wk, kd_body)
                                                                     | KdEq _ => raise (Impossible "not supported")
                                                                     | _ => raise (Impossible "CloConv")
                                               val to = KdVar (new_kctx_base, CVar (i + cnt_ori_kinds), shift_c_k (1 + i + cnt_ori_kinds) 0 $ nth (new_kctx_base, i + cnt_ori_kinds))
                                           in
                                               subst0_kd_kd to kd_body
                                           end) kd1 new_free_wks
                      fun iter kd wks =
                        case kd of
                            KdQuan ((_, CQuan (QuanForall, _, _), _), wk, kd) => iter kd (wk :: wks)
                          | KdEq _ => raise (Impossible "not supported")
                          | _ => (kd, wks)
                      val (kd3, wks) = iter kd2 []
                      val (kd31, kd3i, kd32) =
                          case kd3 of
                              KdArrow (_, kd1, kdi, kd2) => (kd1, kdi, kd2)
                            | KdEq _ => raise (Impossible "not supported")
                            | _ => raise (Impossible "CloConv")
                      val (_, kd312) =
                          case kd31 of
                              KdBinOp ((_, CBinOp (CBTypeProd, _, _), _), kd1, kd2) => (kd1, kd2)
                            | KdEq _ => raise (Impossible "not supported")
                            | _ => raise (Impossible "CloConv")
                      val kd4 = shift_ctx_kd ([KType], cnt_ori_kinds) kd312
                      val kd5 = shift_ctx_kd ([KType], cnt_ori_kinds) kd3i
                      val kd6 = shift_ctx_kd ([KType], cnt_ori_kinds) kd32
                      val kd7 =
                          let
                              val (kctx, _, _) = extract_judge_kinding kd4
                          in
                              KdVar (kctx, CVar cnt_ori_kinds, KType)
                          end
                      val kd8 = KdBinOp (as_KdBinOp CBTypeProd kd7 kd4, kd7, kd4)
                      val kd9 = KdArrow (as_KdArrow kd8 kd5 kd6, kd8, kd5, kd6)
                      val kd10 = foldli (fn (i, wk, kd) =>
                                            let
                                                val wk = shift_ctx_wk ([KType], cnt_ori_kinds - 1 - i) wk
                                            in
                                                KdQuan (as_KdQuan QuanForall wk kd, wk, kd)
                                            end) kd9 wks
                      val kd11 =
                          let
                              val (kctx, _, _) = extract_judge_kinding kd10
                          in
                              KdVar (kctx, CVar 0, KType)
                          end
                      val kd12 = KdBinOp (as_KdBinOp CBTypeProd kd10 kd11, kd10, kd11)
                      val kd13 = KdQuan (as_KdQuan QuanExists (WfKdType (new_kctx_base, KType)) kd12, WfKdType (new_kctx_base, KType), kd12)
                  in
                      kd13
                  end

              val (_, new_t_self_partial_unpacked, _) = extract_judge_kinding new_kd_self_partial_unpacked
              val (_, new_t_self_partial, _) = extract_judge_kinding new_kd_self_partial

              val new_tctx_self = new_t_self_partial :: new_t_self_partial_unpacked :: new_tctx_env

              val new_tctx_arg = new_t_arg :: new_tctx_self

              val new_ty_body = foldli (fn (j, x, ty) => dsubst_c_ty (CVar (j + cnt_ori_kinds)) (x + cnt_ori_kinds) ty) ty_body fcv
              val new_ty_body = foldli (fn (j, x, ty) => dsubst_e_ty (EVar (j + 2)) (x + 2) ty) new_ty_body fev
              val new_ty_body = foldri (fn (j, x, ty) => dsubst_e_ty (EVar (2 * j + 4)) (j + 2) ty) new_ty_body fev
              val new_ty_body = on_typing (new_ty_body, (new_kctx_base, new_tctx_arg))

              val new_ty_wrap_arg =
                  let
                      val ctx = (new_kctx_base, new_tctx_self)
                      val param_idx = length new_tctx_self - 2
                      val ty = TyProj (as_TyProj ProjSnd (TyVar (ctx, EVar param_idx, new_t_param, T0)), TyVar (ctx, EVar param_idx, new_t_param, T0))
                  in
                      TyLet (as_TyLet ty new_ty_body, ty, new_ty_body)
                  end

              val new_ty_wrap_self_unpacked =
                  let
                      val ctx = (new_kctx_base, new_t_self_partial_unpacked :: new_tctx_env)
                      val ty1 = TyVar (ctx, EVar 0, new_t_self_partial_unpacked, T0)
                      val ty2 = TyPack (as_TyPack new_kd_self_partial new_kd_env ty1, new_kd_self_partial, new_kd_env, ty1)
                  in
                      TyLet (as_TyLet ty2 new_ty_wrap_arg, ty2, new_ty_wrap_arg)
                  end

              val new_ty_wrap_self =
                  let
                      val ctx = (new_kctx_base, new_tctx_env)
                      val self_idx = length new_tctx_env - 1
                      val param_idx = self_idx - 1
                      val env_idx = param_idx - 1
                      val ty1 = TyVar (ctx, EVar env_idx, new_t_env, T0)
                      val ty2 = TyVar (ctx, EVar self_idx, new_t_self, T0)
                      val ty3 = foldri (fn (i, _, ty) =>
                                           let
                                               val jty = extract_judge_typing ty
                                               val (_, k, t_body) = extract_c_quan (#3 jty)
                                               val kd = KdVar (fst $ #1 jty, CVar (i + cnt_ori_kinds), k)
                                           in
                                               TyAppC (as_TyAppC ty kd, ty, kd)
                                           end) ty2 new_free_kinds
                      val ty4 = TyPair (as_TyPair ty3 ty1, ty3, ty1)
                      (* val ty6 = TyPack (as_TyPack new_kd_self_partial new_kd_env ty4, new_kd_self_partial, new_kd_env, ty4) *)
                  in
                      TyLet (as_TyLet ty4 new_ty_wrap_self_unpacked, ty4, new_ty_wrap_self_unpacked)
                  end

              val new_ty_wrap_env =
                  let
                      fun inner t ty =
                        case t of
                            CBinOp (CBTypeProd, t1, t2) =>
                            let
                                val ty = inner t2 ty
                                val jty = extract_judge_typing ty
                                val (kctx, tctx) = #1 jty
                                val tctx = tl tctx
                                val ty1 = TyVar ((kctx, tctx), EVar 1, nth (tctx, 1), T0)
                                val ty2 = TyProj (as_TyProj ProjSnd ty1, ty1)
                                val ty3 = TyLet (as_TyLet ty2 ty, ty2, ty)
                                val tctx = tl tctx
                                val ty4 = TyVar ((kctx, tctx), EVar 0, nth (tctx, 0), T0)
                                val ty5 = TyProj (as_TyProj ProjFst ty4 ,ty4)
                                val ty6 = TyLet (as_TyLet ty5 ty3, ty5, ty3)
                            in
                                ty6
                            end
                          | _ => ty
                  in
                      let
                          val ty = inner new_t_env new_ty_wrap_self
                          val jty = extract_judge_typing ty
                          val (kctx, tctx) = #1 jty
                          val tctx = tl tctx
                          val ty1 = TyVar ((kctx, tctx), EVar 0, nth (tctx, 0), T0)
                          val ty2 = TyProj (as_TyProj ProjFst ty1, ty1)
                      in
                          TyLet (as_TyLet ty2 ty, ty2, ty)
                      end
                  end

              val new_ty_sub =
                  let
                      val jty_wrap_env = extract_judge_typing new_ty_wrap_env
                  in
                      TySubTi ((#1 jty_wrap_env, #2 jty_wrap_env, #3 jty_wrap_env, new_i_abs), new_ty_wrap_env, PrAdmit (fst $ #1 jty_wrap_env, TLe (#4 jty_wrap_env, new_i_abs)))
                  end

              val new_ty_fix = TyFix (as_TyFix (kctx, tctx) new_kd_self new_ty_sub, new_kd_self, new_ty_sub)

              val kctx_add_env = kctx
              val tctx_add_env_d = foldl (fn (x, tctx_cur) => CProd (nth (tctx, x), hd tctx_cur) :: tctx_cur) [CTypeUnit] fev
              val tctx_add_env = tctx_add_env_d @ tctx

              val new_ty_fix_add_env = shift0_ctx_ty ([], tctx_add_env_d) new_ty_fix

              val ty_env = TyVar ((kctx_add_env, tctx_add_env), EVar 0, hd tctx_add_env, T0)
              val kd_env =
                  foldl (fn (kd, kd_env) => KdBinOp (as_KdBinOp CBTypeProd kd kd_env, kd, kd_env)) (KdConst (kctx, CTypeUnit, KType)) free_kds

              val ty_app_c =
                  foldr (fn (x, ty) =>
                            let
                                val jty = extract_judge_typing ty
                                val (_, k, t_body) = extract_c_quan (#3 jty)
                                val kd = KdVar (kctx, CVar x, k)
                            in
                                TyAppC (as_TyAppC ty kd, ty, kd)
                            end) new_ty_fix_add_env fcv

              val (ty_clo_sub, kd_tmp) =
                  let
                      val kd_tmp =
                          let
                              val kd1 = fst $ meta_lemma1 ty_app_c
                              fun iter kd wks step =
                                if step = 0 then (kd, wks) else
                                case kd of
                                    KdQuan ((_, CQuan (QuanForall, _, _), _), wk, kd) => iter kd (wk :: wks) (step - 1)
                                  | KdAdmit (kctx, CQuan (QuanForall, k, t), _) => iter (KdAdmit (k :: kctx, t, KType)) (WfKdAdmit (kctx, k) :: wks) (step - 1) (* needed since meta lemmas are not implemented *)
                                  | KdEq _ => raise (Impossible "not supported")
                                  | _ => raise (Impossible "CloConv")
                              val (kd2, wks) = iter kd1 [] cnt_ori_kinds
                              val (kd21, kd2i, kd22) =
                                  case kd2 of
                                      KdArrow (_, kd1, kdi, kd2) => (kd1, kdi, kd2)
                                    | KdAdmit (kctx, CArrow (t1, i, t2), _) => (KdAdmit (kctx, t1, KType), KdAdmit (kctx, i, KTime), KdAdmit (kctx, t2, KType)) (* needed since meta lemmas are not implemented *)
                                    | KdEq _ => raise (Impossible "not supported")
                                    | _ => raise (Impossible "CloConv")
                              val (_, kd212) =
                                  case kd21 of
                                      KdBinOp ((_, CBinOp (CBTypeProd, _, _), _), kd1, kd2) => (kd1, kd2)
                                    | KdAdmit (kctx, CBinOp (CBTypeProd, t1, t2), _) => (KdAdmit (kctx, t1, KType), KdAdmit (kctx, t2, KType)) (* needed since meta lemmas are not implemented *)
                                    | KdEq _ => raise (Impossible "not supported")
                                    | _ => raise (Impossible "CloConv")
                              val kd3 = shift_ctx_kd ([KType], cnt_ori_kinds) kd212
                              val kd4 = shift_ctx_kd ([KType], cnt_ori_kinds) kd2i
                              val kd5 = shift_ctx_kd ([KType], cnt_ori_kinds) kd22
                              val kd6 =
                                  let
                                      val (kctx, _, _) = extract_judge_kinding kd3
                                  in
                                      KdVar (kctx, CVar cnt_ori_kinds, KType)
                                  end
                              val kd7 = KdBinOp (as_KdBinOp CBTypeProd kd6 kd3, kd6, kd3)
                              val kd8 = KdArrow (as_KdArrow kd7 kd4 kd5, kd7, kd4, kd5)
                              val kd9 = foldli (fn (i, wk, kd) =>
                                                   let
                                                       val wk = shift_ctx_wk ([KType], cnt_ori_kinds - 1 - i) wk
                                                   in
                                                       KdQuan (as_KdQuan QuanForall wk kd, wk, kd)
                                                   end) kd8 wks
                              val kd10 =
                                  let
                                      val (kctx, _, _) = extract_judge_kinding kd9
                                  in
                                      KdVar (kctx, CVar 0, KType)
                                  end
                              val kd11 = KdBinOp (as_KdBinOp CBTypeProd kd9 kd10, kd9, kd10)
                              val kd12 = KdQuan (as_KdQuan QuanExists (WfKdType (kctx, KType)) kd11, WfKdType (kctx, KType), kd11)
                          in
                              kd12
                          end

                      val ty_clo = TyPair (as_TyPair ty_app_c ty_env, ty_app_c, ty_env)
                      val jty_clo = extract_judge_typing ty_clo
                      val ty_clo_sub = TySubTi ((#1 jty_clo, #2 jty_clo, #3 jty_clo, T0), ty_clo, PrAdmit (fst $ #1 jty_clo, TLe (#4 jty_clo, T0)))
                  in
                      (ty_clo_sub, kd_tmp)
                  end

              val (_, _, t_clo_sub, _) = extract_judge_typing ty_clo_sub

              val ty_res =
                  let
                      val ty_var = TyVar ((kctx_add_env, t_clo_sub :: tctx_add_env), EVar 0, t_clo_sub, T0)
                  in
                      TyPack (as_TyPack kd_tmp kd_env ty_var, kd_tmp, kd_env, ty_var)
                  end

              val (_, _, t_res, _) = extract_judge_typing ty_res
              val ty_after = on_typing (shift_ctx_ty (([], 0), (t_clo_sub :: tctx_add_env_d, 1)) ty_after, (kctx, t_res :: t_clo_sub :: tctx_add_env))
              val ty_let = TyLet (as_TyLet ty_res ty_after, ty_res, ty_after)
              val ty_let_2 = TyLet (as_TyLet ty_clo_sub ty_let, ty_clo_sub, ty_let)

              val ty_add_env =
                  foldri (fn (i, x, ty) =>
                             let
                                 val ((kctx, tctx), _, _, _) = extract_judge_typing ty
                                 val ty_fst = TyVar ((kctx, tl tctx), EVar (x + i + 1), nth (tl tctx, x + i + 1), T0)
                                 val ty_snd = TyVar ((kctx, tl tctx), EVar 0, hd (tl tctx), T0)
                                 val ty_p = TyPair (as_TyPair ty_fst ty_snd, ty_fst, ty_snd)
                             in
                                 TyLet (as_TyLet ty_p ty, ty_p, ty)
                             end) ty_let_2 fev
              val ty_add_env =
                  let
                      val ((kctx, tctx), _, _, _) = extract_judge_typing ty_add_env
                      val ty_unit = TyConst ((kctx, tl tctx), EConst ECTT, CTypeUnit, T0)
                  in
                      TyLet (as_TyLet ty_unit ty_add_env, ty_unit, ty_add_env)
                  end

              val (_, _, _, i_let) = extract_judge_typing ty_let
              val (_, _, _, i_add_env) = extract_judge_typing ty_add_env

              val ty_add_env_sub =
                  let
                      val pr = PrAdmit (kctx, TLe (i_add_env, i_let))
                  in
                      TySubTi (as_TySubTi ty_add_env pr, ty_add_env, pr)
                  end
          in
              SOME ty_add_env_sub
          end
        | TyApp ((_, _, _, ti), ty1, ty2) =>
          let
              fun unfold_TyAppC ty kds =
                case ty of
                    TyAppC (_, ty, kd) => unfold_TyAppC ty (kd :: kds)
                  | TySubTi _ => raise (Impossible "not supported")
                  | TySubTy _ => raise (Impossible "not supported")
                  | _ => (ty, kds)
              val (ty1, kds) = unfold_TyAppC ty1 []

              val ty1 = on_typing (ty1, (kctx, tctx))
              val ty2 = on_typing (ty2, (kctx, tctx))
              val jty1 = extract_judge_typing ty1
              val jty2 = extract_judge_typing ty2
              val (_, _, t_clo) = extract_c_quan (#3 jty1)
              val (t_func, t_env) = extract_c_prod t_clo

              val ty3 = TyVar ((KType :: kctx, CProd (t_env, shift0_c_c (#3 jty2)) :: t_env :: t_func :: t_clo :: map shift0_c_c tctx), EVar 2, t_func, T0)
              val ty3 = foldl (fn (kd, ty) => TyAppC (as_TyAppC ty kd, ty, kd)) ty3 (map (fn kd => shift0_ctx_kd [KType] (transform_kinding (kd, kctx))) kds)
              val ty4 =
                  let
                      val jty3 = extract_judge_typing ty3
                  in
                      TyVar (#1 jty3, EVar 0, hd (snd $ #1 jty3), T0)
                  end
              val ty5 = TyApp (as_TyApp ty3 ty4, ty3, ty4)
              val ty6 =
                  let
                      val jty5 = extract_judge_typing ty5
                  in
                      TyVar ((fst $ #1 jty5, tl $ snd $ #1 jty5), EVar 0, t_env, T0)
                  end
              val ty7 = ShiftCtx.shift0_ctx_ty ([KType], [t_env, t_func, t_clo]) ty2
              val ty8 = TyPair (as_TyPair ty6 ty7, ty6, ty7)
              val ty9 = TyLet (as_TyLet ty8 ty5, ty8, ty5)
              val ty10 =
                  let
                      val jty9 = extract_judge_typing ty9
                  in
                      TyVar ((fst $ #1 jty9, tl $ snd $ #1 jty9), EVar 1, t_clo, T0)
                  end
              val ty11 = TyProj (as_TyProj ProjSnd ty10, ty10)
              val ty12 = TyLet (as_TyLet ty11 ty9, ty11, ty9)
              val ty13 =
                  let
                      val jty12 = extract_judge_typing ty12
                  in
                      TyVar ((fst $ #1 jty12, tl $ snd $ #1 jty12), EVar 0, t_clo, T0)
                  end
              val ty14 = TyProj (as_TyProj ProjFst ty13, ty13)
              val ty15 = TyLet (as_TyLet ty14 ty12, ty14, ty12)
              val ty16 = TyUnpack (as_TyUnpack ty1 ty15, ty1, ty15)
              val ty17 =
                  let
                      val jty16 = extract_judge_typing ty16
                  in
                      TySubTi ((#1 jty16, #2 jty16, #3 jty16, ti), ty16, PrAdmit (fst $ #1 jty16, TLe (#4 jty16, ti)))
                  end
          in
              SOME ty17
          end
        | TyFix _ => raise (Impossible "CloConv")
        | TyAbs _ => raise (Impossible "CloConv")
        | TyAbsC _ => raise (Impossible "CloConv")
        | TyRec _ => raise (Impossible "CloConv")
        | TyAppC _ => raise (Impossible "CloConv")
        | _ => NONE
    end)

fun clo_conv_deriv ty = ExprDerivHelper.transform_typing (ty, ([], []))
end
