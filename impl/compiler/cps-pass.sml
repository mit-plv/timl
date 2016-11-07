functor CPSPass(MicroTiMLDef : SIG_MICRO_TIML_DEF) =
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

open ShiftCtx
open DerivAssembler

structure CPS =
struct
open DerivSubstTyping

fun send_to_cont ty_cont ty =
  case ty_cont of
      TyAbs (_, _, ty_body) => subst0_ty_ty ty ty_body
    | _ => TyAppK (as_TyAppK ty_cont ty, ty_cont, ty)

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

(* the size of ty's and ty_cont's context should be the same
but in ty_cont's context the types are correctly cpsed *)
fun cps ty ty_cont =
  case ty of
      TyVar (_, EVar x, _, _) =>
      let
          val ((kctx, tctx), _, _, _) = extract_judge_typing ty_cont
          val ty_res = send_to_cont ty_cont (TyVar ((kctx, tctx), EVar x, nth (tctx, x), T0))
      in
          ty_res
      end
    | TyApp (_, ty1, ty2) =>
      let
          val (kd_t1, kd_i1) = meta_lemma ty1
          val (kd_t2, kd_i2) = meta_lemma ty2
          val kd_t1 = cps_kinding kd_t1
          val kd_t2 = cps_kinding kd_t2
          val (_, t1, _) = extract_judge_kinding kd_t1
          val (_, t2, _) = extract_judge_kinding kd_t2
          val in2_ty_cont = shift0_ctx_ty ([], [t2, t1]) ty_cont
          val in1_ty_cont =
              let
                  val ((kctx, tctx), _, t_cont, _) = extract_judge_typing in2_ty_cont
                  val ty_tmp1 = TyVar ((kctx, CProd (t2, t_cont) :: tctx), EVar 2, t1, T0)
                  val (_, kd_tmp2, _) = inverse_kd_arrow $ fst $ meta_lemma in2_ty_cont
                  val ty_tmp3 = TyAppC (as_TyAppC ty_tmp1 kd_tmp2, ty_tmp1, kd_tmp2)
                  val ty_tmp4 = TyVar ((kctx, CProd (t2, t_cont) :: tctx), EVar 0, CProd (t2, t_cont), T0)
                  val ty_tmp5 = TyApp (as_TyApp ty_tmp3 ty_tmp4, ty_tmp3, ty_tmp4)
                  val ty_tmp6 = TyVar ((kctx, tctx), EVar 0, t2, T0)
                  val ty_tmp7 = TyPair (as_TyPair ty_tmp6 in2_ty_cont, ty_tmp6, in2_ty_cont)
                  val ty_tmp8 = TyLet (as_TyLet ty_tmp7 ty_tmp5, ty_tmp7, ty_tmp5)
              in
                  TyAbs (as_TyAbs kd_t2 ty_tmp8, kd_t2, ty_tmp8)
              end
          val in0_ty_cont =
              let
                  val ty_tmp1 = cps (shift0_ctx_ty ([], [t1]) ty2) in1_ty_cont
              in
                  TyAbs (as_TyAbs kd_t1 ty_tmp1, kd_t1, ty_tmp1)
              end
          val ty_res = cps ty1 in0_ty_cont
      in
          ty_res
      end
    | TyAppC (_, ty, kd_c) =>
      let
          val (kd_t, _) = meta_lemma ty
          val kd_t = cps_kinding kd_t
          val (_, t, _) = extract_judge_kinding kd_t
          val kd_c = cps_kinding kd_c
          val in1_ty_cont = shift0_ctx_ty ([], [t]) ty_cont
          val in0_ty_cont =
              let
                  val ((kctx, tctx), _, t_cont, _) = extract_judge_typing in1_ty_cont
                  val ty_tmp1 = TyVar ((kctx, tctx), EVar 0, t, T0)
                  val ty_tmp2 = TyAppC (as_TyAppC ty_tmp1 kd_c, ty_tmp1, kd_c)
                  val (_, kd_tmp3, _) = inverse_kd_arrow $ fst $ meta_lemma in1_ty_cont
                  val ty_tmp4 = TyAppC (as_TyAppC ty_tmp2 kd_tmp3, ty_tmp2, kd_tmp3)
                  val ty_tmp5 = TyAppK (as_TyAppK ty_tmp4 in1_ty_cont, ty_tmp4, in1_ty_cont)
              in
                  TyAbs (as_TyAbs kd_t ty_tmp5, kd_t, ty_tmp5)
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
          (* t1 -- i --> t2 => forall j, ([t1], [t2] -- j --> unit) -- i + j --> unit *)
          val kd_t_body_cont =
              let
                  val (kctx, _, _) = extract_judge_kinding kd_t_body
                  val kd_tmp1 = KdVar (kctx, CVar 0, KTime)
                  val kd_tmp2 = KdConst (kctx, CTypeUnit, KType)
              in
                  KdArrow (as_KdArrow kd_t_body kd_tmp1 kd_tmp2, kd_t_body, kd_tmp1, kd_tmp2)
              end
          val kd_t_param = KdBinOp (as_KdBinOp CBTypeProd kd_t_arg kd_t_body_cont, kd_t_arg, kd_t_body_cont)
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
                  cps ty_body (TyVar ((KTime :: kctx, t_arg :: t_body_cont :: t_param :: map shift0_c_c tctx), EVar 1, t_body_cont, T0))
              end
          val ty_wrap_arg =
              let
                  val ((kctx, tctx), _, _, _) = extract_judge_typing ty_body
                  val ty_tmp1 = TyVar ((kctx, tl tctx), EVar 1, t_param, T0)
                  val ty_tmp2 = TyProj (as_TyProj ProjFst ty_tmp1, ty_tmp1)
              in
                  TyLet (as_TyLet ty_tmp2 ty_body, ty_tmp2, ty_body)
              end
          val ty_wrap_body_cont =
              let
                  val ((kctx, tctx), _, _, _) = extract_judge_typing ty_wrap_arg
                  val ty_tmp1 = TyVar ((kctx, tl tctx), EVar 0, t_param, T0)
                  val ty_tmp2 = TyProj (as_TyProj ProjSnd ty_tmp1, ty_tmp1)
              in
                  TyLet (as_TyLet ty_tmp2 ty_wrap_arg, ty_tmp2, ty_wrap_arg)
              end
          val ty_sub_ti =
              let
                  val ((kctx, tctx), e, t, i) = extract_judge_typing ty_wrap_body_cont
                  val as_i = Tadd (i_body, CVar 0)
              in
                  TySubTi (((kctx, tctx), e, t, as_i), ty_wrap_body_cont, PrAdmit (kctx, TLe (i, as_i)))
              end
          val ty_abs = TyAbs (as_TyAbs kd_t_param ty_sub_ti, kd_t_param, ty_sub_ti)
          val ty_abs_c =
              let
                  val ((kctx, _), _, _, _) = extract_judge_typing ty_abs
                  val wk = WfKdBaseSort (tl kctx, KTime)
              in
                  TyAbsC (as_TyAbsC wk ty_abs, wk, ty_abs)
              end
          (* abstraction is value, send to continuation *)
          val ty_res = send_to_cont ty_cont ty_abs_c
      in
          ty_res
      end
    | TyAbsC (_, wk_arg, ty_body) =>
      let
          val (_, k_arg) = extract_judge_wfkind wk_arg
          val (kd_t_body, _) = meta_lemma ty_body
          val kd_t_body = cps_kinding $ shift0_ctx_kd [KTime] kd_t_body
          (* forall a, t => forall a, forall j, ([t] -- j --> unit) -- j --> unit  *)
          val kd_t_body_cont =
              let
                  val (kctx, _, _) = extract_judge_kinding kd_t_body
                  val kd_tmp1 = KdVar (kctx, CVar 0, KTime)
                  val kd_tmp2 = KdConst (kctx, CTypeUnit, KType)
              in
                  KdArrow (as_KdArrow kd_t_body kd_tmp1 kd_tmp2, kd_t_body, kd_tmp1, kd_tmp2)
              end
          val (_, t_body_cont, _) = extract_judge_kinding kd_t_body_cont
            (* forall a, body => forall a, forall j, fn (k) [body, k]  *)
          val ty_body = shift0_ctx_ty ([KTime], [t_body_cont]) ty_body
          val ty_body =
              let
                  val ((kctx, tctx), _, _, _) = extract_judge_typing ty_cont
              in
                  cps ty_body (TyVar ((KTime :: k_arg :: kctx, t_body_cont :: map (shift_c_c 2 0) tctx), EVar 0, t_body_cont, T0))
              end
          val ty_sub_ti =
              let
                  val ((kctx, tctx), e, t, i) = extract_judge_typing ty_body
                  val as_i = CVar 0
              in
                  TySubTi (((kctx, tctx), e, t, as_i), ty_body, PrAdmit (kctx, TLe (i, as_i)))
              end
          val ty_abs = TyAbs (as_TyAbs kd_t_body_cont ty_sub_ti, kd_t_body_cont, ty_sub_ti)
          val ty_abs_c =
              let
                  val ((kctx, _), _, _, _) = extract_judge_typing ty_abs
                  val wk = WfKdBaseSort (tl kctx, KTime)
              in
                  TyAbsC (as_TyAbsC wk ty_abs, wk, ty_abs)
              end
          val ty_abs_arg = TyAbsC (as_TyAbsC wk_arg ty_abs_c, wk_arg, ty_abs_c)
          (* abstraction is value, send to continuation *)
          val ty_res = send_to_cont ty_cont ty_abs_arg
      in
          ty_res
      end
    | _ => raise (Impossible "CPS")

(* since cps doesn't change kinds, it is okay to retain kinding's context *)
and cps_kinding kd = kd

end

end
