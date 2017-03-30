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
open DropCstr
open DropExpr

structure DerivAssembler = DerivAssemblerFun(MicroTiMLDef)
open DerivAssembler

open ShiftCtx
open DropCtx
open DerivFVCstr
open DerivFVExpr
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

structure CstrHelper = CstrGenericOnlyDownTransformerFun(
    structure MicroTiMLDef = MicroTiMLDef
    structure Action =
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

structure CstrDerivHelper = CstrDerivGenericOnlyDownTransformerFun(
    structure MicroTiMLDef = MicroTiMLDef
    structure Action =
    struct
    type down = kctx

    fun add_kind (k, kctx) = k :: kctx

    fun on_pr_leaf (pr, _) = pr
    fun on_ke_leaf (ke, _) = ke
    fun on_kd_leaf (KdAdmit (_, c, k), kctx) = KdAdmit (kctx, CstrHelper.transform_cstr (c, ()), k)
      | on_kd_leaf (kd, _) = kd
    fun on_wk_leaf (wk, _) = wk
    fun on_wp_leaf (wp, _) = wp
    fun on_te_leaf (TyEqAbs (_, CAbs t, _), kctx) = as_TyEqAbs kctx (CstrHelper.transform_cstr (t, ()))
      | on_te_leaf (TyEqBeta (_, CApp (CAbs t1, t2), _), kctx) = as_TyEqBeta kctx (CstrHelper.transform_cstr (t1, ())) (CstrHelper.transform_cstr (t2, ()))
      | on_te_leaf (TyEqBetaRev (_, _, CApp (CAbs t1, t2)), kctx) = as_TyEqBetaRev kctx (CstrHelper.transform_cstr (t1, ())) (CstrHelper.transform_cstr (t2, ()))
      | on_te_leaf (TyEqTimeAbs (_, CTimeAbs i, _), kctx) = as_TyEqTimeAbs kctx (CstrHelper.transform_cstr (i, ()))
      | on_te_leaf (TyEqTimeApp (_, CTimeApp (arity, c1, c2), _), kctx) = as_TyEqTimeApp kctx arity (CstrHelper.transform_cstr (c1, ())) (CstrHelper.transform_cstr (c2, ()))
      | on_te_leaf (te, _) = te

    fun transformer_tyeq (on_tyeq, on_proping, on_kdeq) (te, kctx) =
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
              val te1 = as_TyEqBinOp CBTypeProd (as_TyEqVar new_kctx cnt_kes) te1
              val te = as_TyEqArrow te1 pr te2
              val te = foldli (fn (j, ke, te) =>
                                  let
                                      val ke = shift_ctx_ke ([KType], cnt_kes - 1 - j) ke
                                  in
                                      as_TyEqQuan QuanForall ke te
                                  end) te kes
              val ke = as_KdEqKType kctx
              val te = as_TyEqBinOp CBTypeProd te (as_TyEqVar (KType :: kctx) 0)
          in
              SOME (as_TyEqQuan QuanExists ke te)
          end
        | TyEqArrow (_, te1, pr, te2) =>
          let
              val te1 = shift0_ctx_te [KType] $ on_tyeq (te1, kctx)
              val pr = shift0_ctx_pr [KType] $ on_proping (pr, kctx)
              val te2 = shift0_ctx_te [KType] $ on_tyeq (te2, kctx)
              val te1 = as_TyEqBinOp CBTypeProd (as_TyEqVar (KType :: kctx) 0) te1
              val te = as_TyEqArrow te1 pr te2
              val ke = as_KdEqKType kctx
              val te = shift0_ctx_te [KType] te
              val te = as_TyEqBinOp CBTypeProd te (as_TyEqVar (KType :: kctx) 0)
          in
              SOME (as_TyEqQuan QuanExists ke te)
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
              val kd1 = as_KdBinOp CBTypeProd (as_KdVar new_kctx cnt_wks) kd1
              val kd = as_KdArrow kd1 kd2 kd3
              val kd = foldli (fn (i, wk, kd) =>
                                  let
                                      val wk = shift_ctx_wk ([KType], cnt_wks - 1 - i) wk
                                  in
                                      as_KdQuan QuanForall wk kd
                                  end) kd wks
              val wk = as_WfKdType kctx
              val kd = as_KdBinOp CBTypeProd kd (as_KdVar (KType :: kctx) 0)
          in
              SOME (as_KdQuan QuanExists wk kd)
          end
        | KdArrow (_, kd1, kd2, kd3) =>
          let
              val kd1 = shift0_ctx_kd [KType] $ on_kinding (kd1, kctx)
              val kd2 = shift0_ctx_kd [KType] $ on_kinding (kd2, kctx)
              val kd3 = shift0_ctx_kd [KType] $ on_kinding (kd3, kctx)
              val kd1 = as_KdBinOp CBTypeProd (as_KdVar (KType :: kctx) 0) kd1
              val kd = as_KdArrow kd1 kd2 kd3
              val wk = as_WfKdType kctx
              val kd = as_KdBinOp CBTypeProd kd (as_KdVar (KType :: kctx) 0)
          in
              SOME (as_KdQuan QuanExists wk kd)
          end
        | _ => NONE

    (* need to change the context, so simply use the default transformer *)
    fun transformer_proping _ = NONE
    fun transformer_kdeq _ _ = NONE
    fun transformer_wfkind _ _ = NONE
    fun transformer_wfprop _ _ = NONE
    end)

structure ExprDerivHelper = ExprDerivGenericOnlyDownTransformerFun(
    structure MicroTiMLDef = MicroTiMLDef
    structure Action =
    struct
    type kdown = kctx * (int * int) list
    type tdown = tctx * (int * int) list
    type down = kdown * tdown

    fun add_kind (k, ((kctx, kmap), (tctx, tmap))) = ((k :: kctx, add_assoc 0 0 (map (fn (from, to) => (from + 1, to + 1)) kmap)), (map shift0_c_c tctx, tmap))
    fun add_type (t, (tctx, tmap)) = (t :: tctx, add_assoc 0 0 (map (fn (from, to) => (from + 1, to + 1)) tmap))

    fun on_ty_leaf (TyVar (_, EVar x, _, _), ((kctx, kmap), (tctx, tmap))) = as_TyVar (kctx, tctx) (assoc x tmap)
      | on_ty_leaf (TyConst (_, EConst cn, _, _), ((kctx, kmap), (tctx, tmap))) = as_TyConst (kctx, tctx) cn
      | on_ty_leaf _ = raise (Impossible "as_ty_leaf")

    fun transform_proping (pr, (kctx, kmap)) = CstrDerivHelper.transform_proping (drop_ctx_pr (kctx, kmap) pr, kctx)
    fun transform_kinding (kd, (kctx, kmap)) = CstrDerivHelper.transform_kinding (drop_ctx_kd (kctx, kmap) kd, kctx)
    fun transform_wfkind (wk, (kctx, kmap)) = CstrDerivHelper.transform_wfkind (drop_ctx_wk (kctx, kmap) wk, kctx)
    fun transform_tyeq (te, (kctx, kmap)) = CstrDerivHelper.transform_tyeq (drop_ctx_te (kctx, kmap) te, kctx)

    fun transformer_typing on_typing (ty, ((kctx, kmap), (tctx, tmap))) =
      case ty of
          TyLet (_, ty_rec as TyRec (_, _, ty_inner), ty_after) =>
          let
              fun unfold_ty ty wks =
                case ty of
                    TyAbsC (j, wk, _, ty) => unfold_ty ty (wk :: wks)
                  | _ => (ty, wks)
              val (ty_abs, ori_wks) = unfold_ty ty_inner []
              val (kd_arg, ty_body) =
                  case ty_abs of
                      TyAbs (_, kd_arg, ty_body) => (kd_arg, ty_body)
                    | _ => raise (Impossible "CloConv")
              val fcv = free_vars0_c_ty ty_rec
              val fev = free_vars0_e_ty ty_rec
              val free_kinds = map (fn x => shift_c_k (1 + (assoc x kmap)) 0 $ nth (kctx, assoc x kmap)) fcv
              val new_free_kinds = snd $
                                       foldri (fn (i, (x, k), (mapping, kinds)) =>
                                                  (add_assoc (assoc x kmap) 0 (map_assoc (fn to => to + 1) mapping), drop_c_k mapping k :: kinds))
                                       ([], []) (ListPair.zip (fcv, free_kinds))
              val free_wks = map (fn x => meta_lemma2 (as_KdVar kctx (assoc x kmap))) fcv
              val new_free_wks = snd $
                                     foldri (fn (i, (x, wk), ((kctx, mapping), wks)) =>
                                                let
                                                    val wk = drop_ctx_wk (kctx, mapping) wk
                                                    val jwk = extract_judge_wfkind wk
                                                in
                                                    ((#2 jwk :: kctx, add_assoc (assoc x kmap) 0 (map_assoc (fn to => to + 1) mapping)), wk :: wks)
                                                end)
                                     (([], []), []) (ListPair.zip (fcv, free_wks))
              val free_types = map (fn x => nth (tctx, assoc x tmap)) fev
              val free_kds = map (fn x => fst $ meta_lemma1 (as_TyVar (kctx, tctx) (assoc x tmap))) fev
              val new_free_types =
                  let
                      val mapping = mapi (fn (i, x) => (assoc x kmap, i)) fcv
                  in
                      map (drop_c_c mapping) free_types
                  end
              val new_free_kds =
                  let
                      val mapping = mapi (fn (i, x) => (assoc x kmap, i)) fcv
                  in
                      map (drop_ctx_kd (new_free_kinds, mapping)) free_kds
                  end
              val cnt_ori_kinds = length ori_wks

              val new_ori_wks = snd $
                                    foldri (fn (i, wk, ((kctx, mapping), wks)) =>
                                               let
                                                   val wk = drop_ctx_wk (kctx, mapping) wk
                                                   val jwk = extract_judge_wfkind wk
                                               in
                                                   ((#2 jwk :: kctx, add_assoc 0 0 (map (fn (from, to) => (from + 1, to + 1)) mapping)), wk :: wks)
                                               end)
                                    ((new_free_kinds, mapi (fn (i, x) => (x, i)) fcv), []) ori_wks
              val new_ori_kinds = map (snd o extract_judge_wfkind) new_ori_wks
              val new_all_kinds = new_ori_kinds @ new_free_kinds
              val new_free_types = map (shift_c_c cnt_ori_kinds 0) new_free_types
              val new_free_kds = map (shift0_ctx_kd new_ori_kinds) new_free_kds

              val new_kd_arg = transform_kinding (kd_arg, (new_all_kinds, mapi (fn (i, _) => (i, i)) new_ori_kinds @ mapi (fn (i, x) => (x + cnt_ori_kinds, i + cnt_ori_kinds)) fcv))
              val (_, new_t_arg, _) = extract_judge_kinding new_kd_arg
              val (kd_res, kd_time) = meta_lemma1 ty_body
              val new_kd_time = transform_kinding (kd_time, (new_all_kinds, mapi (fn (i, _) => (i, i)) new_ori_kinds @ mapi (fn (i, x) => (x + cnt_ori_kinds, i + cnt_ori_kinds)) fcv))
              val (_, new_i_abs, _) = extract_judge_kinding new_kd_time
              val new_kd_res = transform_kinding (kd_res, (new_all_kinds, mapi (fn (i, _) => (i, i)) new_ori_kinds @ mapi (fn (i, x) => (x + cnt_ori_kinds, i + cnt_ori_kinds)) fcv))
              val (_, new_t_res, _) = extract_judge_kinding new_kd_res

              val new_kd_env = foldl (fn (kd, kd_env) =>
                                         as_KdBinOp CBTypeProd kd kd_env)
                                     (as_KdConst new_all_kinds CCTypeUnit) new_free_kds
              val (_, new_t_env, _) = extract_judge_kinding new_kd_env
              val new_kd_param = as_KdBinOp CBTypeProd new_kd_env new_kd_arg
              val (_, new_t_param, _) = extract_judge_kinding new_kd_param

              val new_kd_arrow = as_KdArrow new_kd_param new_kd_time new_kd_res
              val (_, new_t_arrow, _) = extract_judge_kinding new_kd_arrow
              val new_kd_self = foldl (fn (wk, kd) => as_KdQuan QuanForall wk kd) new_kd_arrow (new_ori_wks @ new_free_wks)
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
                                                                     | _ => raise (Impossible "CloConv")
                                               val to = as_KdVar new_kctx_base (i + cnt_ori_kinds)
                                           in
                                               subst0_kd_kd to kd_body
                                           end) kd1 new_free_wks
                      val kd3 = as_KdBinOp CBTypeProd kd2 new_kd_env
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
                                                                     | _ => raise (Impossible "CloConv")
                                               val to = as_KdVar new_kctx_base (i + cnt_ori_kinds)
                                           in
                                               subst0_kd_kd to kd_body
                                           end) kd1 new_free_wks
                      fun iter kd wks =
                        case kd of
                            KdQuan ((_, CQuan (QuanForall, _, _), _), wk, kd) => iter kd (wk :: wks)
                          | _ => (kd, wks)
                      val (kd3, wks) = iter kd2 []
                      val (kd31, kd3i, kd32) =
                          case kd3 of
                              KdArrow (_, kd1, kdi, kd2) => (kd1, kdi, kd2)
                            | _ => raise (Impossible "CloConv")
                      val (_, kd312) =
                          case kd31 of
                              KdBinOp ((_, CBinOp (CBTypeProd, _, _), _), kd1, kd2) => (kd1, kd2)
                            | _ => raise (Impossible "CloConv")
                      val kd4 = shift_ctx_kd ([KType], cnt_ori_kinds) kd312
                      val kd5 = shift_ctx_kd ([KType], cnt_ori_kinds) kd3i
                      val kd6 = shift_ctx_kd ([KType], cnt_ori_kinds) kd32
                      val kd7 =
                          let
                              val (kctx, _, _) = extract_judge_kinding kd4
                          in
                              as_KdVar kctx cnt_ori_kinds
                          end
                      val kd8 = as_KdBinOp CBTypeProd kd7 kd4
                      val kd9 = as_KdArrow kd8 kd5 kd6
                      val kd10 = foldli (fn (i, wk, kd) =>
                                            let
                                                val wk = shift_ctx_wk ([KType], cnt_ori_kinds - 1 - i) wk
                                            in
                                                as_KdQuan QuanForall wk kd
                                            end) kd9 wks
                      val kd11 =
                          let
                              val (kctx, _, _) = extract_judge_kinding kd10
                          in
                              as_KdVar kctx 0
                          end
                      val kd12 = as_KdBinOp CBTypeProd kd10 kd11
                      val kd13 = as_KdQuan QuanExists (as_WfKdType new_kctx_base) kd12
                  in
                      kd13
                  end

              val (_, new_t_self_partial_unpacked, _) = extract_judge_kinding new_kd_self_partial_unpacked
              val (_, new_t_self_partial, _) = extract_judge_kinding new_kd_self_partial

              val new_tctx_self = new_t_self_partial :: new_t_self_partial_unpacked :: new_tctx_env

              val new_tctx_arg = new_t_arg :: new_tctx_self

              val new_ty_body = on_typing (ty_body, ((new_kctx_base, mapi (fn (i, _) => (i, i)) new_ori_kinds @ mapi (fn (i, x) => (x + cnt_ori_kinds, i + cnt_ori_kinds)) fcv), (new_tctx_arg, [(0, 0), (1, 1)] @ mapi (fn (i, x) => (x + 2, 2 * i + 4)) fev)))

              val new_ty_wrap_arg =
                  let
                      val ctx = (new_kctx_base, new_tctx_self)
                      val param_idx = length new_tctx_self - 2
                      val ty = as_TyProj ProjSnd (as_TyVar ctx param_idx)
                  in
                      as_TyLet ty new_ty_body
                  end

              val new_ty_wrap_self_unpacked =
                  let
                      val ctx = (new_kctx_base, new_t_self_partial_unpacked :: new_tctx_env)
                      val ty1 = as_TyVar ctx 0
                      val ty2 = as_TyPack new_kd_self_partial new_kd_env ty1
                  in
                      as_TyLet ty2 new_ty_wrap_arg
                  end

              val new_ty_wrap_self =
                  let
                      val ctx = (new_kctx_base, new_tctx_env)
                      val self_idx = length new_tctx_env - 1
                      val param_idx = self_idx - 1
                      val env_idx = param_idx - 1
                      val ty1 = as_TyVar ctx env_idx
                      val ty2 = as_TyVar ctx self_idx
                      val ty3 = foldri (fn (i, _, ty) =>
                                           let
                                               val jty = extract_judge_typing ty
                                               val (_, k, t_body) = extract_c_quan (#3 jty)
                                               val kd = as_KdVar (fst $ #1 jty) (i + cnt_ori_kinds)
                                           in
                                               as_TyAppC ty kd
                                           end) ty2 new_free_kinds
                      val ty4 = as_TyPair ty3 ty1
                  in
                      as_TyLet ty4 new_ty_wrap_self_unpacked
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
                                val ty1 = as_TyVar (kctx, tctx) 1
                                val ty2 = as_TyProj ProjSnd ty1
                                val ty3 = as_TyLet ty2 ty
                                val tctx = tl tctx
                                val ty4 = as_TyVar (kctx, tctx) 0
                                val ty5 = as_TyProj ProjFst ty4
                                val ty6 = as_TyLet ty5 ty3
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
                          val ty1 = as_TyVar (kctx, tctx) 0
                          val ty2 = as_TyProj ProjFst ty1
                      in
                          as_TyLet ty2 ty
                      end
                  end

              val new_ty_sub =
                  let
                      val jty_wrap_env = extract_judge_typing new_ty_wrap_env
                  in
                      as_TySubTi new_ty_wrap_env (PrAdmit (fst $ #1 jty_wrap_env, TLe (#4 jty_wrap_env, new_i_abs)))
                  end

              val new_ty_fix = as_TyFix (kctx, tctx) new_kd_self new_ty_sub

              val kctx_add_env = kctx
              val tctx_add_env_d = foldl (fn (x, tctx_cur) => CProd (nth (tctx, assoc x tmap), hd tctx_cur) :: tctx_cur) [CTypeUnit] fev
              val tctx_add_env = tctx_add_env_d @ tctx

              val new_ty_fix_add_env = shift0_ctx_ty ([], tctx_add_env_d) new_ty_fix

              val ty_env = as_TyVar (kctx_add_env, tctx_add_env) 0
              val kd_env =
                  foldl (fn (kd, kd_env) => as_KdBinOp CBTypeProd kd kd_env) (as_KdConst kctx CCTypeUnit) free_kds

              val ty_app_c =
                  foldr (fn (x, ty) =>
                            let
                                val jty = extract_judge_typing ty
                                val (_, k, t_body) = extract_c_quan (#3 jty)
                                val kd = as_KdVar kctx (assoc x kmap)
                            in
                                as_TyAppC ty kd
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
                                  | _ => raise (Impossible "CloConv")
                              val (kd2, wks) = iter kd1 [] cnt_ori_kinds
                              val (kd21, kd2i, kd22) =
                                  case kd2 of
                                      KdArrow (_, kd1, kdi, kd2) => (kd1, kdi, kd2)
                                    | KdAdmit (kctx, CArrow (t1, i, t2), _) => (KdAdmit (kctx, t1, KType), KdAdmit (kctx, i, KTime), KdAdmit (kctx, t2, KType)) (* needed since meta lemmas are not implemented *)
                                    | _ => raise (Impossible "CloConv")
                              val (_, kd212) =
                                  case kd21 of
                                      KdBinOp ((_, CBinOp (CBTypeProd, _, _), _), kd1, kd2) => (kd1, kd2)
                                    | KdAdmit (kctx, CBinOp (CBTypeProd, t1, t2), _) => (KdAdmit (kctx, t1, KType), KdAdmit (kctx, t2, KType)) (* needed since meta lemmas are not implemented *)
                                    | _ => raise (Impossible "CloConv")
                              val kd3 = shift_ctx_kd ([KType], cnt_ori_kinds) kd212
                              val kd4 = shift_ctx_kd ([KType], cnt_ori_kinds) kd2i
                              val kd5 = shift_ctx_kd ([KType], cnt_ori_kinds) kd22
                              val kd6 =
                                  let
                                      val (kctx, _, _) = extract_judge_kinding kd3
                                  in
                                      as_KdVar kctx cnt_ori_kinds
                                  end
                              val kd7 = as_KdBinOp CBTypeProd kd6 kd3
                              val kd8 = as_KdArrow kd7 kd4 kd5
                              val kd9 = foldli (fn (i, wk, kd) =>
                                                   let
                                                       val wk = shift_ctx_wk ([KType], cnt_ori_kinds - 1 - i) wk
                                                   in
                                                       as_KdQuan QuanForall wk kd
                                                   end) kd8 wks
                              val kd10 =
                                  let
                                      val (kctx, _, _) = extract_judge_kinding kd9
                                  in
                                      as_KdVar kctx 0
                                  end
                              val kd11 = as_KdBinOp CBTypeProd kd9 kd10
                              val kd12 = as_KdQuan QuanExists (as_WfKdType kctx) kd11
                          in
                              kd12
                          end

                      val ty_clo = as_TyPair ty_app_c ty_env
                      val jty_clo = extract_judge_typing ty_clo
                      val ty_clo_sub = as_TySubTi ty_clo (PrAdmit (fst $ #1 jty_clo, TLe (#4 jty_clo, T0)))
                  in
                      (ty_clo_sub, kd_tmp)
                  end

              val (_, _, t_clo_sub, _) = extract_judge_typing ty_clo_sub

              val ty_res =
                  let
                      val ty_var = as_TyVar (kctx_add_env, t_clo_sub :: tctx_add_env) 0
                  in
                      as_TyPack kd_tmp kd_env ty_var
                  end

              val (_, _, t_res, _) = extract_judge_typing ty_res
              val ty_after = on_typing (shift_ctx_ty (([], 0), (t_clo_sub :: tctx_add_env_d, 1)) ty_after, ((kctx, kmap), (t_res :: t_clo_sub :: tctx_add_env, [(0, 0)] @ map (fn (from, to) => (from + 1 + 1 + length tctx_add_env_d, to + 1 + 1 + length tctx_add_env_d)) tmap)))
              val ty_let = as_TyLet ty_res ty_after
              val ty_let_2 = as_TyLet ty_clo_sub ty_let

              val ty_add_env =
                  foldri (fn (i, x, ty) =>
                             let
                                 val ((kctx, tctx), _, _, _) = extract_judge_typing ty
                                 val ty_fst = as_TyVar (kctx, tl tctx) ((assoc x tmap) + i + 1)
                                 val ty_snd = as_TyVar (kctx, tl tctx) 0
                                 val ty_p = as_TyPair ty_fst ty_snd
                             in
                                 as_TyLet ty_p ty
                             end) ty_let_2 fev
              val ty_add_env =
                  let
                      val ((kctx, tctx), _, _, _) = extract_judge_typing ty_add_env
                      val ty_unit = as_TyConst (kctx, tl tctx) ECTT
                  in
                      as_TyLet ty_unit ty_add_env
                  end

              val (_, _, _, i_let) = extract_judge_typing ty_let
              val (_, _, _, i_add_env) = extract_judge_typing ty_add_env

              val ty_add_env_sub =
                  let
                      val pr = PrAdmit (kctx, TLe (i_add_env, i_let))
                  in
                      as_TySubTi ty_add_env pr
                  end
          in
              SOME ty_add_env_sub
          end
        | TyApp ((_, _, _, ti), ty1, ty2) =>
          let
              fun unfold_TyAppC ty kds =
                case ty of
                    TyAppC (_, ty, kd) => unfold_TyAppC ty (kd :: kds)
                  | _ => (ty, kds)
              val (ty1, kds) = unfold_TyAppC ty1 []

              val ty1 = on_typing (ty1, ((kctx, kmap), (tctx, tmap)))
              val ty2 = on_typing (ty2, ((kctx, kmap), (tctx, tmap)))
              val jty1 = extract_judge_typing ty1
              val jty2 = extract_judge_typing ty2
              val (_, _, t_clo) = extract_c_quan (#3 jty1)
              val (t_func, t_env) = extract_c_prod t_clo

              val ty3 = as_TyVar ((KType :: kctx, CProd (t_env, shift0_c_c (#3 jty2)) :: t_env :: t_func :: t_clo :: map shift0_c_c tctx)) 2
              val ty3 = foldl (fn (kd, ty) => as_TyAppC ty kd) ty3 (map (fn kd => shift0_ctx_kd [KType] (transform_kinding (kd, (kctx, kmap)))) kds)
              val ty4 =
                  let
                      val jty3 = extract_judge_typing ty3
                  in
                      as_TyVar (#1 jty3) 0
                  end
              val ty5 = as_TyApp ty3 ty4
              val ty6 =
                  let
                      val jty5 = extract_judge_typing ty5
                  in
                      as_TyVar ((fst $ #1 jty5, tl $ snd $ #1 jty5)) 0
                  end
              val ty7 = ShiftCtx.shift0_ctx_ty ([KType], [t_env, t_func, t_clo]) ty2
              val ty8 = as_TyPair ty6 ty7
              val ty9 = as_TyLet ty8 ty5
              val ty10 =
                  let
                      val jty9 = extract_judge_typing ty9
                  in
                      as_TyVar ((fst $ #1 jty9, tl $ snd $ #1 jty9)) 1
                  end
              val ty11 = as_TyProj ProjSnd ty10
              val ty12 = as_TyLet ty11 ty9
              val ty13 =
                  let
                      val jty12 = extract_judge_typing ty12
                  in
                      as_TyVar ((fst $ #1 jty12, tl $ snd $ #1 jty12)) 0
                  end
              val ty14 = as_TyProj ProjFst ty13
              val ty15 = as_TyLet ty14 ty12
              val ty16 = as_TyUnpack ty1 ty15
              val ty17 =
                  let
                      val jty16 = extract_judge_typing ty16
                  in
                      as_TySubTi ty16 (PrAdmit (fst $ #1 jty16, TLe (#4 jty16, drop_c_c kmap ti)))
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

fun clo_conv_deriv ty = ExprDerivHelper.transform_typing (ty, (([], []), ([], [])))
end
