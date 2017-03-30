functor CPSPassFun(MicroTiMLDef : SIG_MICRO_TIML_DEF) : SIG_CPS_PASS =
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

structure DerivAssembler = DerivAssemblerFun(MicroTiMLDef)
open DerivAssembler

open ShiftCtx
open DerivSubstTyping

structure CountNodes =
struct
structure ExprHelper = ExprGenericTransformerFun(
    structure MicroTiMLDef = MicroTiMLDef
    structure Action =
    struct
    type kdown = unit
    type tdown = unit
    type down = kdown * tdown
    type up = int

    val upward_base = 0
    fun combiner (a, b) = a + b + 1

    fun add_kind (_, ((), ())) = ((), ())
    fun add_type (_, ()) = ()

    fun transform_cstr (c, ()) = (c, 0)

    fun transformer_expr on_expr (e, ((), ())) =
      case e of
          EFix _ => raise (Impossible "CPS")
        | EHalt _ => raise (Impossible "CPS")
        | _ => NONE
    end)

fun count_nodes e = ExprHelper.transform_expr (e, ((), ()))
end

fun send_to_cont ty_cont ty =
  let
      val add_let =
          case (#2 (extract_judge_typing ty)) of
              EAbs _ => true
            | EAbsC _ => true
            | ERec _ => true
            | _ => false
  in
      case ty_cont of
          TyAbs (_, _, ty_body) =>
          if add_let then
              as_TyLet ty ty_body
          else
              subst0_ty_ty ty ty_body
        | _ =>
          if add_let then
              let
                  val ((kctx, tctx), _, t, _) = extract_judge_typing ty
                  val ty_tmp1 = shift0_ctx_ty ([], [t]) ty_cont
                  val ty_tmp2 = as_TyVar (kctx, t :: tctx) 0
                  val ty_tmp3 = as_TyApp ty_tmp1 ty_tmp2
              in
                  as_TyLet ty ty_tmp3
              end
          else
              as_TyApp ty_cont ty
  end

fun meta_lemma ty =
  let
      val ((kctx, _), _, t, i) = extract_judge_typing ty
  in
      (KdAdmit (kctx, t, KType), KdAdmit (kctx, i, KTime))
  end

fun inverse_kd_arrow kd =
  case kd of
      KdArrow (_, kd_t1, kd_i, kd_t2) => (kd_t1, kd_i, kd_t2)
    | KdAdmit (kctx, CArrow (t1, i, t2), KType) =>
      (KdAdmit (kctx, t1, KType), KdAdmit (kctx, i, KTime), KdAdmit (kctx, t2, KType))
    | KdEq (_, kd, _) => inverse_kd_arrow kd
    | _ => raise (Impossible "inverse_kd_arrow")

structure CstrHelper = CstrGenericOnlyDownTransformerFun(
    structure MicroTiMLDef = MicroTiMLDef
    structure Action =
    struct
    type down = cstr (* blowup *)

    fun add_kind (_, blowup) = blowup

    fun transformer_cstr (on_cstr, on_kind) (c, blowup) =
      case c of
          CArrow (t1, i, t2) =>
          let
              (* t1 -- i --> t2 => forall j, ([t1], [t2] -- j --> unit) -- k * (i + 1) + 2 * i + 1 + j --> unit  *)
              val t1 = shift0_c_c $ on_cstr (t1, blowup)
              val i = shift0_c_c $ on_cstr (i, blowup)
              val t2 = shift0_c_c $ on_cstr (t2, blowup)
              val t2_cont = CArrow (t2, CVar 0, CTypeUnit)
          in
              SOME (CForall (KTime, CArrow (CProd (t1, t2_cont), Tadd (Tadd (Tadd (Tmult (blowup, Tadd (i, T1)), Tmult (TfromNat $ CNat $ Nat.from_int 2, i)), T1), CVar 0), CTypeUnit)))
          end
        | CQuan (QuanForall, k, t) =>
          let
              (* forall a, t => forall a, forall j, ([t] -- j --> unit) -- 1 + j --> unit *)
              val t = shift0_c_c $ on_cstr (t, blowup)
              val t_cont = CArrow (t, CVar 0, CTypeUnit)
              val t_quan_j = CForall (KTime, CArrow (t_cont, Tadd (T1, CVar 0), CTypeUnit))
          in
              SOME (CForall (k, t_quan_j))
          end
        | _ => NONE

    fun transformer_kind _ (k, _) = SOME k
    fun transformer_prop _ (p, _) = SOME p
    end)

structure CstrDerivHelper = CstrDerivGenericOnlyDownTransformerFun(
    structure MicroTiMLDef = MicroTiMLDef
    structure Action =
    struct
    type down = cstr (* blowup *)

    fun add_kind (_, blowup) = blowup

    fun on_pr_leaf (pr, _) = pr
    fun on_ke_leaf (ke, _) = ke
    fun on_kd_leaf (KdAdmit (kctx, c, k), blowup) = KdAdmit (kctx, CstrHelper.transform_cstr (c, blowup), k)
      | on_kd_leaf (kd, _) = kd
    fun on_wk_leaf (wk, _) = wk
    fun on_wp_leaf (wp, _) = wp
    fun on_te_leaf (TyEqAbs (kctx, CAbs t, _), blowup) = as_TyEqAbs kctx (CstrHelper.transform_cstr (t, blowup))
      | on_te_leaf (TyEqBeta (kctx, CApp (CAbs t1, t2), _), blowup) = as_TyEqBeta kctx (CstrHelper.transform_cstr (t1, blowup)) (CstrHelper.transform_cstr (t2, blowup))
      | on_te_leaf (TyEqBetaRev (kctx, _, CApp (CAbs t1, t2)), blowup) = as_TyEqBetaRev kctx (CstrHelper.transform_cstr (t1, blowup)) (CstrHelper.transform_cstr (t2, blowup))
      | on_te_leaf (TyEqTimeAbs (kctx, CTimeAbs i, _), blowup) = as_TyEqTimeAbs kctx (CstrHelper.transform_cstr (i, blowup))
      | on_te_leaf (TyEqTimeApp (kctx, CTimeApp (arity, c1, c2), _), blowup) = as_TyEqTimeApp kctx arity (CstrHelper.transform_cstr (c1, blowup)) (CstrHelper.transform_cstr (c2, blowup))
      | on_te_leaf (te, _) = te

    fun transformer_kinding (on_kinding, on_wfkind, on_kdeq) (kd, blowup) =
      case kd of
          KdArrow (_, kd_t1, kd_i, kd_t2) =>
          let
              val kd_t1 = shift0_ctx_kd [KTime] $ on_kinding (kd_t1, blowup)
              val kd_i = shift0_ctx_kd [KTime] $ on_kinding (kd_i, blowup)
              val kd_t2 = shift0_ctx_kd [KTime] $ on_kinding (kd_t2, blowup)
              val (kctx, _, _) = extract_judge_kinding kd_t2
              val kd_j = KdVar (kctx, CVar 0, KTime)
              val kd_t2_cont =
                  let
                      val kd_tmp1 = as_KdConst kctx CCTypeUnit
                  in
                      as_KdArrow kd_t2 kd_j kd_tmp1
                  end
              val kd_t_param = as_KdBinOp CBTypeProd kd_t1 kd_t2_cont
              val kd_arrow =
                  let
                      val kd_tmp1 = as_KdConst kctx (CCTime Time.Time1)
                      val (_, coef) = extract_c_un_op blowup
                      val kd_tmp2 = as_KdUnOp CUNat2Time (as_KdConst kctx (extract_c_const coef))
                      val kd_tmp3 = as_KdBinOp CBTimeAdd kd_i kd_tmp1
                      val kd_tmp4 =  as_KdBinOp CBTimeMult kd_tmp2 kd_tmp3
                      val kd_tmp5 = as_KdUnOp CUNat2Time (as_KdConst kctx (CCIdxNat (Nat.from_int 2)))
                      val kd_tmp6 = as_KdBinOp CBTimeMult kd_tmp5 kd_i
                      val kd_tmp7 = as_KdBinOp CBTimeAdd kd_tmp4 kd_tmp6
                      val kd_tmp8 = as_KdBinOp CBTimeAdd kd_tmp7 kd_tmp1
                      val kd_tmp9 = as_KdBinOp CBTimeAdd kd_tmp8 kd_j
                      val kd_tmp10 = as_KdConst kctx CCTypeUnit
                  in
                      as_KdArrow kd_t_param kd_tmp9 kd_tmp10
                  end
              val wk = as_WfKdBaseSort (tl kctx) BSTime
          in
              SOME (as_KdQuan QuanForall wk kd_arrow)
          end
        | KdQuan ((_, CQuan (QuanForall, _, _), _), wk, kd) =>
          let
              val kd = shift0_ctx_kd [KTime] $ on_kinding (kd, blowup)
              val (kctx, _, _) = extract_judge_kinding kd
              val kd_j = KdVar (kctx, CVar 0, KTime)
              val kd_cont =
                  let
                      val kd_tmp1 = as_KdConst kctx CCTypeUnit
                  in
                      as_KdArrow kd kd_j kd_tmp1
                  end
              val kd_arrow =
                  let
                      val kd_tmp1 = as_KdConst kctx CCTypeUnit
                      val kd_tmp2 = as_KdConst kctx (CCTime Time.Time1)
                      val kd_tmp3 = as_KdBinOp CBTimeAdd kd_tmp2 kd_j
                  in
                      as_KdArrow kd_cont kd_tmp3 kd_tmp1
                  end
              val wk_j = as_WfKdBaseSort (tl kctx) BSTime
              val kd_quan_j = as_KdQuan QuanForall wk_j kd_arrow
          in
              SOME (as_KdQuan QuanForall wk kd_quan_j)
          end
        | _ => NONE

    fun transformer_tyeq (on_tyeq, on_proping, on_kdeq) (te, blowup) =
      case te of
          TyEqArrow (_, te_t1, pr_i, te_t2) =>
          let
              val te_t1 = shift0_ctx_te [KTime] $ on_tyeq (te_t1, blowup)
              val pr_i = shift0_ctx_pr [KTime] pr_i
              val te_t2 = shift0_ctx_te [KTime] $ on_tyeq (te_t2, blowup)
              val (kctx, _, _) = extract_judge_tyeq te_t2
              val pr_j = PrAdmit (kctx, TEq (CVar 0, CVar 0))
              val te_t2_cont =
                  let
                      val te_tmp1 = as_TyEqConst kctx CCTypeUnit
                  in
                      as_TyEqArrow te_t2 pr_j te_tmp1
                  end
              val te_t_param = as_TyEqBinOp CBTypeProd te_t1 te_t2_cont
              val te_t_arrow =
                  let
                      val (_, i_lhs, i_rhs) = extract_p_bin_pred $ snd $ extract_judge_proping pr_i
                      val pr_tmp1 = PrAdmit (kctx, TEq (Tadd (Tadd (Tadd (Tmult (blowup, Tadd (i_lhs, T1)), Tmult (TfromNat $ CNat $ Nat.from_int 2, i_lhs)), T1), CVar 0), Tadd (Tadd (Tadd (Tmult (blowup, Tadd (i_rhs, T1)), Tmult (TfromNat $ CNat $ Nat.from_int 2, i_rhs)), T1), CVar 0)))
                      val te_tmp2 = as_TyEqConst kctx CCTypeUnit
                  in
                      as_TyEqArrow te_t_param pr_tmp1 te_tmp2
                  end
              val ke = as_KdEqBaseSort (tl kctx) BSTime
          in
              SOME (as_TyEqQuan QuanForall ke te_t_arrow)
          end
        | TyEqQuan ((_, CQuan (QuanForall, _, _), _), ke, te) =>
          let
              val te = shift0_ctx_te [KTime] $ on_tyeq (te, blowup)
              val (kctx, _, _) = extract_judge_tyeq te
              val pr_j = PrAdmit (kctx, TEq (CVar 0, CVar 0))
              val te_cont =
                  let
                      val te_tmp1 = as_TyEqConst kctx CCTypeUnit
                  in
                      as_TyEqArrow te pr_j te_tmp1
                  end
              val te_arrow =
                  let
                      val te_tmp1 = as_TyEqConst kctx CCTypeUnit
                      val pr_tmp2 = PrAdmit (kctx, TEq (Tadd (T1, CVar 0), Tadd (T1, CVar 0)))
                  in
                      as_TyEqArrow te_cont pr_tmp2 te_tmp1
                  end
              val ke_j = as_KdEqBaseSort (tl kctx) BSTime
              val te_quan_j = as_TyEqQuan QuanForall ke_j te_arrow
          in
              SOME (as_TyEqQuan QuanForall ke te_quan_j)
          end
        | _ => NONE

    (* be confident! *)
    fun transformer_proping (pr, _) = SOME pr
    fun transformer_kdeq _ (ke, _) = SOME ke
    fun transformer_wfkind _ (wk, _) = SOME wk
    fun transformer_wfprop _ (wp, _) = SOME wp
    end)

val blowup = ref (CConst CCIdxTT)

(* the size of ty's and ty_cont's context should be the same *)
(* but in ty_cont's context the types are correctly cpsed *)
fun cps ty ty_cont =
  case ty of
      TyVar (_, EVar x, _, _) =>
      let
          val ((kctx, tctx), _, _, _) = extract_judge_typing ty_cont
          val ty_res = send_to_cont ty_cont (as_TyVar (kctx, tctx) x)
      in
          ty_res
      end
    | TyConst (_, EConst cn, _, _) =>
      let
          val (ctx, _, _, _) = extract_judge_typing ty_cont
          val ty_res = send_to_cont ty_cont (as_TyConst ctx cn)
      in
          ty_res
      end
    | TyApp (_, ty1, ty2) =>
      let
          val kd_t1 = cps_kinding $ fst $ meta_lemma ty1
          val kd_t2 = cps_kinding $ fst $ meta_lemma ty2
          val (_, t1, _) = extract_judge_kinding kd_t1
          val (_, t2, _) = extract_judge_kinding kd_t2
          val in2_ty_cont = shift0_ctx_ty ([], [t2, t1]) ty_cont
          val in1_ty_cont =
              let
                  val ((kctx, tctx), _, t_cont, _) = extract_judge_typing in2_ty_cont
                  val ty_tmp1 = as_TyVar (kctx, CProd (t2, t_cont) :: t_cont :: tctx) 3
                  val (_, kd_tmp2, _) = inverse_kd_arrow $ fst $ meta_lemma in2_ty_cont (* kind context is just correct *)
                  val ty_tmp3 = as_TyAppC ty_tmp1 kd_tmp2
                  val ty_tmp4 = as_TyVar (kctx, CProd (t2, t_cont) :: t_cont :: tctx) 0
                  val ty_tmp5 = as_TyApp ty_tmp3 ty_tmp4
                  val ty_tmp6 = as_TyVar (kctx, t_cont :: tctx) 1
                  val ty_tmp7 = as_TyVar (kctx, t_cont :: tctx) 0
                  val ty_tmp8 = as_TyPair ty_tmp6 ty_tmp7
                  val ty_tmp9 = as_TyLet ty_tmp8 ty_tmp5
                  val ty_tmp10 = as_TyLet in2_ty_cont ty_tmp9
              in
                  as_TyAbs kd_t2 ty_tmp10
              end
          val in0_ty_cont =
              let
                  val ty_tmp1 = cps (shift0_ctx_ty ([], [t1]) ty2) in1_ty_cont
              in
                  as_TyAbs kd_t1 ty_tmp1
              end
          val ty_res = cps ty1 in0_ty_cont
      in
          ty_res
      end
    | TyAppC (_, ty, kd_c) =>
      let
          val kd_t = cps_kinding $ fst $ meta_lemma ty
          val (_, t, _) = extract_judge_kinding kd_t
          val kd_c = cps_kinding kd_c
          val in1_ty_cont = shift0_ctx_ty ([], [t]) ty_cont
          val in0_ty_cont =
              let
                  val ((kctx, tctx), _, t_cont, _) = extract_judge_typing in1_ty_cont
                  val ty_tmp1 = as_TyVar (kctx, t_cont :: tctx) 1
                  val ty_tmp2 = as_TyAppC ty_tmp1 kd_c
                  val (_, kd_tmp3, _) = inverse_kd_arrow $ fst $ meta_lemma in1_ty_cont (* kind context is just correct *)
                  val ty_tmp4 = as_TyAppC ty_tmp2 kd_tmp3
                  val ty_tmp5 = as_TyVar (kctx, t_cont :: tctx) 0
                  val ty_tmp6 = as_TyApp ty_tmp4 ty_tmp5
                  val ty_tmp7 = as_TyLet in1_ty_cont ty_tmp6
              in
                  as_TyAbs kd_t ty_tmp7
              end
          val ty_res = cps ty in0_ty_cont
      in
          ty_res
      end
    | TyAbs (_, kd_t_arg, ty_body) =>
      let
          val kd_t_arg = cps_kinding $ shift0_ctx_kd [KTime] kd_t_arg
          val (kd_t_body, _) = meta_lemma ty_body
          val kd_t_body = cps_kinding $ shift0_ctx_kd [KTime] kd_t_body
          (* t1 -- i --> t2 => forall j, ([t1], [t2] -- j --> unit) -- k * (i + 1) + 2 * i + 1 + j --> unit *)
          val kd_t_body_cont =
              let
                  val (kctx, _, _) = extract_judge_kinding kd_t_body
                  val kd_tmp1 = as_KdVar kctx 0
                  val kd_tmp2 = as_KdConst kctx CCTypeUnit
              in
                  as_KdArrow kd_t_body kd_tmp1 kd_tmp2
              end
          val kd_t_param = as_KdBinOp CBTypeProd kd_t_arg kd_t_body_cont
          val (_, t_arg, _) = extract_judge_kinding kd_t_arg
          val (_, t_body_cont, _) = extract_judge_kinding kd_t_body_cont
          val (_, t_param, _) = extract_judge_kinding kd_t_param
          (* fn (x) body => forall j, fn (x, k) let k = k in let x = x in [body, k] *)
          val ty_body = shift_ctx_ty (([KTime], 0), ([t_body_cont, t_param], 1)) ty_body
          val (_, _, _, i_body) = extract_judge_typing ty_body
          val ty_body =
              let
                  val ((kctx, tctx), _, _, _) = extract_judge_typing ty_cont
              in
                  cps ty_body (as_TyVar (KTime :: kctx, t_arg :: t_body_cont :: t_param :: map shift0_c_c tctx) 1)
              end
          val ty_wrap_arg =
              let
                  val ((kctx, tctx), _, _, _) = extract_judge_typing ty_body
                  val ty_tmp1 = as_TyVar (kctx, tl tctx) 1
                  val ty_tmp2 = as_TyProj ProjFst ty_tmp1
              in
                  as_TyLet ty_tmp2 ty_body
              end
          val ty_wrap_body_cont =
              let
                  val ((kctx, tctx), _, _, _) = extract_judge_typing ty_wrap_arg
                  val ty_tmp1 = as_TyVar (kctx, tl tctx) 0
                  val ty_tmp2 = as_TyProj ProjSnd ty_tmp1
              in
                  as_TyLet ty_tmp2 ty_wrap_arg
              end
          val ty_sub_ti =
              let
                  val ((kctx, tctx), e, t, i) = extract_judge_typing ty_wrap_body_cont
                  val as_i = Tadd (Tadd (Tadd (Tmult (!blowup, Tadd (i_body, T1)), Tmult (TfromNat $ CNat $ Nat.from_int 2, i_body)), T1), CVar 0)
              in
                  as_TySubTi ty_wrap_body_cont (PrAdmit (kctx, TLe (i, as_i)))
              end
          val ty_abs = as_TyAbs kd_t_param ty_sub_ti
          val ty_abs_c =
              let
                  val ((kctx, _), e_abs, _, _) = extract_judge_typing ty_abs
                  val wk = as_WfKdBaseSort (tl kctx) BSTime
              in
                  as_TyAbsC wk ty_abs
              end
          (* abstraction is value, send to continuation *)
          val ty_res = send_to_cont ty_cont ty_abs_c
      in
          ty_res
      end
    | TyAbsC (_, wk_arg, _, ty_body) =>
      let
          val (_, k_arg) = extract_judge_wfkind wk_arg
          val (kd_t_body, _) = meta_lemma ty_body
          val kd_t_body = cps_kinding $ shift0_ctx_kd [KTime] kd_t_body
          (* forall a, t => forall a, forall j, ([t] -- j --> unit) -- 1 + j --> unit  *)
          val kd_t_body_cont =
              let
                  val (kctx, _, _) = extract_judge_kinding kd_t_body
                  val kd_tmp1 = as_KdVar kctx 0
                  val kd_tmp2 = as_KdConst kctx CCTypeUnit
              in
                  as_KdArrow kd_t_body kd_tmp1 kd_tmp2
              end
          val (_, t_body_cont, _) = extract_judge_kinding kd_t_body_cont
            (* forall a, body => forall a, forall j, fn (k) [body, k]  *)
          val ty_body = shift0_ctx_ty ([KTime], [t_body_cont]) ty_body
          val ty_body =
              let
                  val ((kctx, tctx), _, _, _) = extract_judge_typing ty_cont
              in
                  cps ty_body (as_TyVar (KTime :: k_arg :: kctx, t_body_cont :: map (shift_c_c 2 0) tctx) 0)
              end
          val ty_sub_ti =
              let
                  val ((kctx, tctx), e, t, i) = extract_judge_typing ty_body
                  val as_i = Tadd (T1, CVar 0)
              in
                  as_TySubTi ty_body (PrAdmit (kctx, TLe (i, as_i)))
              end
          val ty_abs = as_TyAbs kd_t_body_cont ty_sub_ti
          val ty_abs_c =
              let
                  val ((kctx, _), e_abs, _, _) = extract_judge_typing ty_abs
                  val wk = as_WfKdBaseSort (tl kctx) BSTime
              in
                  as_TyAbsC wk ty_abs
              end
          val ty_abs_arg =
              let
                  val (_, e_abs_c, _, _) = extract_judge_typing ty_abs_c
              in
                  as_TyAbsC wk_arg ty_abs_c
              end
          (* abstraction is value, send to continuation *)
          val ty_res = send_to_cont ty_cont ty_abs_arg
      in
          ty_res
      end
    | TyRec (_, kd_t_self, ty_self) =>
      let
          val kd_t_self = cps_kinding kd_t_self
          val (_, t_self, _) = extract_judge_kinding kd_t_self
          (* rec x. e, e must be abstraction, so [e, fn (x) => x] will return abstraction *)
          val ty_self =
              let
                  val ((kctx, tctx), _, _, _) = extract_judge_typing ty_cont
                  val ty_tmp1 = as_TyVar (kctx, t_self :: t_self :: tctx) 0
              in
                  cps ty_self (as_TyAbs kd_t_self ty_tmp1)
              end
          val ty_self =
              case ty_self of
                  TyAbs _ => ty_self
                | TyAbsC _ => ty_self
                | TyLet (_, ty, _) => ty
                | _ => raise (Impossible "CPS")
          val ty_rec = as_TyRec kd_t_self ty_self
          (* abstraction is value, send to continuation *)
          val ty_res = send_to_cont ty_cont ty_rec
      in
          ty_res
      end
    | TyFold (_, kd_t_folded, ty_body) =>
      let
          val kd_t_folded = cps_kinding kd_t_folded
          val (kd_t_body, t_body, ty_body_as_var) = cps_body_as_var_in1 ty_body ty_cont
          val ty_fold_var = as_TyFold kd_t_folded ty_body_as_var
          val ty_res = cps_finisher_in1 ty_body kd_t_body t_body ty_fold_var ty_cont
      in
          ty_res
      end
    | TyUnfold (_, ty_body) =>
      let
          val (kd_t_body, t_body, ty_body_as_var) = cps_body_as_var_in1 ty_body ty_cont
          val ty_unfold_var = as_TyUnfold ty_body_as_var
          val ty_res = cps_finisher_in1 ty_body kd_t_body t_body ty_unfold_var ty_cont
      in
          ty_res
      end
    | TyPack (_, kd_t_packed, kd_c, ty_body) =>
      let
          val kd_t_packed = cps_kinding kd_t_packed
          val kd_c = cps_kinding kd_c
          val (kd_t_body, t_body, ty_body_as_var) = cps_body_as_var_in1 ty_body ty_cont
          val ty_pack_var = as_TyPack kd_t_packed kd_c ty_body_as_var
          val ty_res = cps_finisher_in1 ty_body kd_t_body t_body ty_pack_var ty_cont
      in
          ty_res
      end
    | TyProj ((_, EUnOp (EUProj p, _), _, _ ), ty_body) =>
      let
          val (kd_t_body, t_body, ty_body_as_var) = cps_body_as_var_in1 ty_body ty_cont
          val ty_proj_var = as_TyProj p ty_body_as_var
          val ty_res = cps_finisher_in1 ty_body kd_t_body t_body ty_proj_var ty_cont
      in
          ty_res
      end
    | TyInj ((_, EUnOp (EUInj inj, _), _, _), ty_body, kd_t_other) =>
      let
          val kd_t_other = cps_kinding kd_t_other
          val (kd_t_body, t_body, ty_body_as_var) = cps_body_as_var_in1 ty_body ty_cont
          val ty_inj_var = as_TyInj inj ty_body_as_var kd_t_other
          val ty_res = cps_finisher_in1 ty_body kd_t_body t_body ty_inj_var ty_cont
      in
          ty_res
      end
    | TyNew (_, ty1, ty2) =>
      let
          val (kd_t1, kd_t2, t1, t2, ty1_as_var, ty2_as_var) = cps_body_as_var_in2 ty1 ty2 ty_cont
          val ty_new_var = as_TyNew ty1_as_var ty2_as_var
          val ty_res = cps_finisher_in2 ty1 ty2 kd_t1 kd_t2 t1 t2 ty_new_var ty_cont
      in
          ty_res
      end
    | TyRead (_, ty1, ty2, pr) =>
      let
          val (kd_t1, kd_t2, t1, t2, ty1_as_var, ty2_as_var) = cps_body_as_var_in2 ty1 ty2 ty_cont
          val ty_read_var = as_TyRead ty1_as_var ty2_as_var pr
          val ty_res = cps_finisher_in2 ty1 ty2 kd_t1 kd_t2 t1 t2 ty_read_var ty_cont
      in
          ty_res
      end
    | TyPair (_, ty1, ty2) =>
      let
          val (kd_t1, kd_t2, t1, t2, ty1_as_var, ty2_as_var) = cps_body_as_var_in2 ty1 ty2 ty_cont
          val ty_pair_var = as_TyPair ty1_as_var ty2_as_var
          val ty_res = cps_finisher_in2 ty1 ty2 kd_t1 kd_t2 t1 t2 ty_pair_var ty_cont
      in
          ty_res
      end
    | TyWrite (_, ty1, ty2, pr, ty3) =>
      let
          val (kd_t1, kd_t2, kd_t3, t1, t2, t3, ty1_as_var, ty2_as_var, ty3_as_var) = cps_body_as_var_in3 ty1 ty2 ty3 ty_cont
          val ty_write_var = as_TyWrite ty1_as_var ty2_as_var pr ty3_as_var
          val ty_res = cps_finisher_in3 ty1 ty2 ty3 kd_t1 kd_t2 kd_t3 t1 t2 t3 ty_write_var ty_cont
      in
          ty_res
      end
    | TyPrimBinOp ((_, EBinOp (EBPrim opr, _, _), _, _), ty1, ty2) =>
      let
          val (kd_t1, kd_t2, t1, t2, ty1_as_var, ty2_as_var) = cps_body_as_var_in2 ty1 ty2 ty_cont
          val ty_prim_var = as_TyPrimBinOp opr ty1_as_var ty2_as_var
          val ty_res = cps_finisher_in2 ty1 ty2 kd_t1 kd_t2 t1 t2 ty_prim_var ty_cont
      in
          ty_res
      end
    | TyUnpack (_, ty1, ty2) =>
      let
          val kd_t1 = cps_kinding $ fst $ meta_lemma ty1
          val (_, t1, _) = extract_judge_kinding kd_t1
          val (_, k, t_body) = extract_c_quan t1
          val in0_ty_cont =
              let
                  val ((kctx, tctx), _, _, _) = extract_judge_typing ty_cont
                  val shifted_t1 = shift0_c_c t1
                  val ty_tmp1 = shift0_ctx_ty ([k], [t_body, shifted_t1]) ty_cont
                  val ty_tmp2 = shift_ctx_ty (([], 0), ([shifted_t1], 1)) ty2
                  val ty_tmp3 = cps ty_tmp2 ty_tmp1
                  val ty_tmp4 = TyVar ((kctx, t1 :: tctx), EVar 0, t1, T0)
                  val ty_tmp5 = as_TyUnpack ty_tmp4 ty_tmp3
              in
                  as_TyAbs kd_t1 ty_tmp5
              end
          val ty_res = cps ty1 in0_ty_cont
      in
          ty_res
      end
    | TyCase (_, ty_disp, ty1, ty2) =>
      let
          val kd_t_disp = cps_kinding $ fst $ meta_lemma ty_disp
          val (_, t_disp, _) = extract_judge_kinding kd_t_disp
          val (t_inl, t_inr) = extract_c_sum t_disp
          val in0_ty_cont =
              let
                  val ((kctx, tctx), _, t_cont, _) = extract_judge_typing ty_cont
                  val ty_tmp1 = as_TyVar (kctx, t_inl :: t_cont :: t_disp :: tctx) 1
                  val ty_tmp2 = cps (shift_ctx_ty (([], 0), ([t_cont, t_disp], 1)) ty1) ty_tmp1
                  val ty_tmp3 = as_TyVar (kctx, t_inr :: t_cont :: t_disp :: tctx) 1
                  val ty_tmp4 = cps (shift_ctx_ty (([], 0), ([t_cont, t_disp], 1)) ty2) ty_tmp3
                  val ty_tmp5 = as_TyVar (kctx, t_cont :: t_disp :: tctx) 1
                  val ty_tmp6 = as_TyCase ty_tmp5 ty_tmp2 ty_tmp4
                  val ty_tmp7 = shift0_ctx_ty ([], [t_disp]) ty_cont
                  val ty_tmp8 = as_TyLet ty_tmp7 ty_tmp6
              in
                  as_TyAbs kd_t_disp ty_tmp8
              end
          val ty_res = cps ty_disp in0_ty_cont
      in
          ty_res
      end
    | TyLet (_, ty1, ty2) =>
      let
          val kd_t1 = cps_kinding $ fst $ meta_lemma ty1
          val (_, t1, _) = extract_judge_kinding kd_t1
          val in0_ty_cont =
              let
                  val ((kctx, tctx), _, t_cont, _) = extract_judge_typing ty_cont
                  val ty_tmp1 = shift0_ctx_ty ([], [t1]) ty_cont
                  val ty_tmp2 = cps ty2 ty_tmp1
              in
                  as_TyAbs kd_t1 ty_tmp2
              end
          val ty_res = cps ty1 in0_ty_cont
      in
          ty_res
      end
    | TySubTy (_, ty_body, te) =>
      let
          val te = cps_tyeq te
          val (kd_t_body, t_body, ty_body_as_var) = cps_body_as_var_in1 ty_body ty_cont
          val ty_sub_var = as_TySubTy ty_body_as_var te
          val ty_res = cps_finisher_in1 ty_body kd_t_body t_body ty_sub_var ty_cont
      in
          ty_res
      end
    | TySubTi ((_, e, _, _), ty_body, pr) =>
      let
          val (kd_t_body, t_body, ty_body_as_var) = cps_body_as_var_in1 ty_body ty_cont
          val ty_bare_res = cps_finisher_in1 ty_body kd_t_body t_body ty_body_as_var ty_cont
          val ((kctx, _), _, _, i_bare_res) = extract_judge_typing ty_bare_res
          val (_, _, i_body) =  extract_p_bin_pred $ snd $ extract_judge_proping pr
          val (_, _, t_cont, _) = extract_judge_typing ty_cont
          val (_, i_cont, _) = extract_c_arrow t_cont
          val pr = PrAdmit (kctx, TLe (i_bare_res, Tadd (Tadd (TfromNat $ CNat $ Nat.from_int ((snd $ CountNodes.count_nodes e) * 2), Tmult (!blowup, i_body)), Tadd (Tmult (TfromNat $ CNat $ Nat.from_int 2, i_body), Tadd (case ty_cont of TyAbs _ => T0 | _ => T1, i_cont)))))
          val ty_res = as_TySubTi ty_bare_res pr
      in
          ty_res
      end
    | _ => raise (Impossible "CPS")

(* since cps doesn't change kinds, it is okay to retain kinding's context *)
and cps_kinding kd = CstrDerivHelper.transform_kinding (kd, !blowup)

and cps_tyeq te = CstrDerivHelper.transform_tyeq (te, !blowup)

and cps_body_as_var_in1 ty_body ty_cont =
    let
        val kd_t_body = cps_kinding $ fst $ meta_lemma ty_body
        val (_, t_body, _) = extract_judge_kinding kd_t_body
        val ((kctx, tctx), _, _, _) = extract_judge_typing ty_cont
    in
        (kd_t_body, t_body, as_TyVar (kctx, t_body :: tctx) 0)
    end

and cps_body_as_var_in2 ty1 ty2 ty_cont =
    let
        val kd_t1 = cps_kinding $ fst $ meta_lemma ty1
        val kd_t2 = cps_kinding $ fst $ meta_lemma ty2
        val (_, t1, _) = extract_judge_kinding kd_t1
        val (_, t2, _) = extract_judge_kinding kd_t2
        val ((kctx, tctx), _, _, _) = extract_judge_typing ty_cont
    in
        (kd_t1, kd_t2, t1, t2, as_TyVar (kctx, t2 :: t1 :: tctx) 1, as_TyVar (kctx, t2 :: t1 :: tctx) 0)
    end

and cps_body_as_var_in3 ty1 ty2 ty3 ty_cont =
    let
        val kd_t1 = cps_kinding $ fst $ meta_lemma ty1
        val kd_t2 = cps_kinding $ fst $ meta_lemma ty2
        val kd_t3 = cps_kinding $ fst $ meta_lemma ty3
        val (_, t1, _) = extract_judge_kinding kd_t1
        val (_, t2, _) = extract_judge_kinding kd_t2
        val (_, t3, _) = extract_judge_kinding kd_t3
        val ((kctx, tctx), _, _, _) = extract_judge_typing ty_cont
    in
        (kd_t1, kd_t2, kd_t3, t1, t2, t3, as_TyVar (kctx, t3 :: t2 :: t1 :: tctx) 2, as_TyVar (kctx, t3 :: t2 :: t1 :: tctx) 1, as_TyVar (kctx, t3 :: t2 :: t1 :: tctx) 0)
    end

and cps_finisher_in1 ty_body kd_t_body t_body ty_post ty_cont =
    let
        val ((kctx, tctx), _, t_post, _) = extract_judge_typing ty_post
        val ty_tmp1 = shift0_ctx_ty ([], [t_post, t_body]) ty_cont
        val ty_tmp2 =
            if t_post = CTypeUnit then
                as_TyConst (kctx, t_post :: tctx) ECTT
            else
                as_TyVar (kctx, t_post :: tctx) 0
        val ty_tmp3 = send_to_cont ty_tmp1 ty_tmp2
        val ty_tmp4 = as_TyLet ty_post ty_tmp3
        val in0_ty_cont = as_TyAbs kd_t_body ty_tmp4
        val ty_res = cps ty_body in0_ty_cont
    in
        ty_res
    end

and cps_finisher_in2 ty1 ty2 kd_t1 kd_t2 t1 t2 ty_post ty_cont =
    let
        val ((kctx, tctx), _, t_post, _) = extract_judge_typing ty_post
        val ty_tmp1 = shift0_ctx_ty ([], [t_post, t2, t1]) ty_cont
        val ty_tmp2 =
            if t_post = CTypeUnit then
                as_TyConst (kctx, t_post :: tctx) ECTT
            else
                as_TyVar (kctx, t_post :: tctx) 0
        val ty_tmp3 = send_to_cont ty_tmp1 ty_tmp2
        val ty_tmp4 = as_TyLet ty_post ty_tmp3
        val in1_ty_cont = as_TyAbs kd_t2 ty_tmp4
        val ty_partial_res = cps (shift0_ctx_ty ([], [t1]) ty2) in1_ty_cont
        val in0_ty_cont = as_TyAbs kd_t1 ty_partial_res
        val ty_res = cps ty1 in0_ty_cont
    in
        ty_res
    end

and cps_finisher_in3 ty1 ty2 ty3 kd_t1 kd_t2 kd_t3 t1 t2 t3 ty_post ty_cont =
    let
        val ((kctx, tctx), _, t_post, _) = extract_judge_typing ty_post
        val ty_tmp1 = shift0_ctx_ty ([], [t_post, t3, t2, t1]) ty_cont
        val ty_tmp2 =
            if t_post = CTypeUnit then
                as_TyConst (kctx, t_post :: tctx) ECTT
            else
                as_TyVar (kctx, t_post :: tctx) 0
        val ty_tmp3 = send_to_cont ty_tmp1 ty_tmp2
        val ty_tmp4 = as_TyLet ty_post ty_tmp3
        val in2_ty_cont = as_TyAbs kd_t3 ty_tmp4
        val ty_partial_res = cps (shift0_ctx_ty ([], [t2, t1]) ty3) in2_ty_cont
        val in1_ty_cont = as_TyAbs kd_t2 ty_partial_res
        val ty_partial_res = cps (shift0_ctx_ty ([], [t1]) ty2) in1_ty_cont
        val in0_ty_cont = as_TyAbs kd_t1 ty_partial_res
        val ty_res = cps ty1 in0_ty_cont
    in
        ty_res
    end

fun cps_deriv ty =
  let
      val (_, e, _, _) = extract_judge_typing ty
      val () = blowup := (TfromNat $ CNat $ Nat.from_int $ (snd $ CountNodes.count_nodes e) * 2)
      val kd_t = cps_kinding $ fst $ meta_lemma ty
      val (_, t, _) = extract_judge_kinding kd_t
      val ((kctx, tctx), _, _, _) = extract_judge_typing ty
      val ty_cont =
          let
              val ty_tmp1 = as_TyVar (kctx, t :: tctx) 0
              val ty_tmp2 = as_TyHalt ty_tmp1
          in
              as_TyAbs kd_t ty_tmp2
          end
      val ty_res = cps ty ty_cont
  in
      ty_res
  end
end
