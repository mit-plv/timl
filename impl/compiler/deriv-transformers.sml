functor DerivAssemblerFun(MicroTiMLDef : SIG_MICRO_TIML_DEF) : SIG_DERIV_ASSEMBLER =
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

open ShiftCstr
open SubstCstr

exception AssembleFail of string

fun assert b msg =
  if b then () else (println $ "AssembleFail: " ^ msg; raise AssembleFail msg)

fun as_KdEqKType kctx = KdEqKType (kctx, KType, KType)

fun as_KdEqKArrow ke1 ke2 =
  let
      val jke1 = extract_judge_kdeq ke1
      val jke2 = extract_judge_kdeq ke2
      val () = assert (#1 jke1 = #1 jke2) "KdEqKArrow 1"
  in
      KdEqKArrow ((#1 jke1, KArrow (#2 jke1, #2 jke2), KArrow (#3 jke1, #3 jke2)), ke1, ke2)
  end

fun as_KdEqBaseSort kctx b = KdEqBaseSort (kctx, KBaseSort b, KBaseSort b)

fun as_KdEqSubset ke pr =
  let
      val jke = extract_judge_kdeq ke
      val jpr = extract_judge_proping pr
      val () = assert (#2 jke :: #1 jke = #1 jpr) "KdEqKSubset 1"
      val (opr, p1, p2) = extract_p_bin_conn (#2 jpr)
      val () = assert (opr = PBCIff) "KdEqKSubset 2"
  in
      KdEqSubset ((#1 jke, KSubset (#2 jke, p1), KSubset (#3 jke, p2)), ke, pr)
  end

fun as_KdEqSubsetElimLeft pr =
  let
      val jpr = extract_judge_proping pr
  in
      KdEqSubsetElimLeft ((tl $ #1 jpr, KSubset (hd $ #1 jpr, #2 jpr), hd $ #1 jpr), pr)
  end

fun as_KdEqSubsetElimRight pr =
  let
      val jpr = extract_judge_proping pr
  in
      KdEqSubsetElimRight ((tl $ #1 jpr, hd $ #1 jpr, KSubset (hd $ #1 jpr, #2 jpr)), pr)
  end

fun as_WfPropTrue kctx = WfPropTrue (kctx, PTrue)

fun as_WfPropFalse kctx = WfPropFalse (kctx, PFalse)

fun as_WfPropBinConn opr wp1 wp2 =
  let
      val jwp1 = extract_judge_wfprop wp1
      val jwp2 = extract_judge_wfprop wp2
      val () = assert (#1 jwp1 = #1 jwp2) "WfPropBinConn 1"
  in
      WfPropBinConn ((#1 jwp1, PBinConn (opr, #2 jwp1, #2 jwp2)), wp1, wp2)
  end

fun as_WfPropNot wp =
  let
      val jwp = extract_judge_wfprop wp
  in
      WfPropNot ((#1 jwp, PNot (#2 jwp)), wp)
  end

fun as_WfPropBinPred opr kd1 kd2 =
  let
      val jkd1 = extract_judge_kinding kd1
      val jkd2 = extract_judge_kinding kd2
      val () = assert (#1 jkd1 = #1 jkd2) "WfPropBinPred 1"
      val () = assert (#3 jkd1 = binpred_arg1_kind opr) "WfPropBinPred 2"
      val () = assert (#3 jkd2 = binpred_arg2_kind opr) "WfPropBinPred 3"
  in
      WfPropBinPred ((#1 jkd1, PBinPred (opr, #2 jkd1, #2 jkd2)), kd1, kd2)
  end

fun as_WfPropQuan q b wp =
  let
      val jwp = extract_judge_wfprop wp
  in
      WfPropQuan ((tl $ #1 jwp, PQuan (q, b, #2 jwp)), wp)
  end

fun as_WfKdType kctx = WfKdType (kctx, KType)

fun as_WfKdArrow wk1 wk2 =
  let
      val jwk1 = extract_judge_wfkind wk1
      val jwk2 = extract_judge_wfkind wk2
      val () = assert (#1 jwk1 = #1 jwk2) "WfKdArrow 1"
  in
      WfKdArrow ((#1 jwk1, KArrow (#2 jwk1, #2 jwk2)), wk1, wk2)
  end

fun as_WfKdBaseSort kctx b = WfKdBaseSort (kctx, KBaseSort b)

fun as_WfKdSubset wk wp =
  let
      val jwk = extract_judge_wfkind wk
      val jwp = extract_judge_wfprop wp
      val () = assert (#2 jwk :: #1 jwk = #1 jwp) "WfKdSubset 1"
  in
      WfKdSubset ((#1 jwk, KSubset (#2 jwk, #2 jwp)), wk, wp)
  end

fun as_KdVar kctx x = KdVar (kctx, CVar x, shift_c_k (1 + x) 0 $ nth (kctx, x))

fun as_KdConst kctx cn = KdConst (kctx, CConst cn, const_kind cn)

fun as_KdBinOp opr kd1 kd2 =
  let
      val jkd1 = extract_judge_kinding kd1
      val jkd2 = extract_judge_kinding kd2
      val () = assert (#1 jkd1 = #1 jkd2) "KdBinOp 1"
      val () = assert (#3 jkd1 = cbinop_arg1_kind opr) "KdBinOp 2"
      val () = assert (#3 jkd2 = cbinop_arg2_kind opr) "KdBinOp 3"
  in
      KdBinOp ((#1 jkd1, CBinOp (opr, #2 jkd1, #2 jkd2), cbinop_result_kind opr), kd1, kd2)
  end

fun as_KdIte kd1 kd2 kd3 =
  let
      val jkd1 = extract_judge_kinding kd1
      val jkd2 = extract_judge_kinding kd2
      val jkd3 = extract_judge_kinding kd3
      val () = assert (#1 jkd1 = #1 jkd2) "KdIte 1"
      val () = assert (#1 jkd1 = #1 jkd3) "KdIte 2"
      val () = assert (#3 jkd1 = KBaseSort BSBool) "KdIte 3"
      val () = assert (#3 jkd2 = #3 jkd3) "KdIte 4"
  in
      KdIte ((#1 jkd1, CIte (#2 jkd1, #2 jkd2, #2 jkd3), #3 jkd2), kd1, kd2, kd3)
  end

fun as_KdArrow kd1 kd2 kd3 =
  let
      val jkd1 = extract_judge_kinding kd1
      val jkd2 = extract_judge_kinding kd2
      val jkd3 = extract_judge_kinding kd3
      val () = assert (#1 jkd1 = #1 jkd2) "KdArrow 1"
      val () = assert (#1 jkd1 = #1 jkd3) "KdArrow 2"
      val () = assert (#3 jkd1 = KType) "KdArrow 3"
      val () = assert (#3 jkd2 = KTime) "KdArrow 4"
      val () = assert (#3 jkd3 = KType) "KdArrow 5"
  in
      KdArrow ((#1 jkd1, CArrow (#2 jkd1, #2 jkd2, #2 jkd3), KType), kd1, kd2, kd3)
  end

fun as_KdAbs wk kd =
  let
      val jwk = extract_judge_wfkind wk
      val jkd = extract_judge_kinding kd
      val () = assert (#2 jwk :: #1 jwk = #1 jkd) "KdAbs 1"
  in
      KdAbs ((#1 jwk, CAbs (#2 jkd), KArrow (#2 jwk, shift_c_k ~1 0 (#3 jkd))), wk, kd) (* TODO *)
  end

fun as_KdApp kd1 kd2 =
  let
      val jkd1 = extract_judge_kinding kd1
      val jkd2 = extract_judge_kinding kd2
      val () = assert (#1 jkd1 = #1 jkd2) "KdApp 1"
      val (k1, k2) = extract_k_arrow (#3 jkd1)
      val () = assert (k1 = #3 jkd2) "KdApp 2"
  in
      KdApp ((#1 jkd1, CApp (#2 jkd1, #2 jkd2), k2), kd1, kd2)
  end

fun as_KdTimeAbs kd =
  let
      val jkd = extract_judge_kinding kd
      val () = assert ((hd $ #1 jkd) = KNat) "KdTimeAbs 1"
      val arity = extract_k_time_fun (#3 jkd)
  in
      KdTimeAbs ((tl $ #1 jkd, CTimeAbs (#2 jkd), KTimeFun (arity + 1)), kd)
  end

fun as_KdTimeApp kd1 kd2 =
  let
      val jkd1 = extract_judge_kinding kd1
      val arity = extract_k_time_fun (#3 jkd1)
      val jkd2 = extract_judge_kinding kd2
      val () = assert (#1 jkd1 = #1 jkd2) "KdTimeApp 1"
      val () = assert (arity > 0) "KdTimeApp 2"
      val () = assert (#3 jkd2 = KNat) "KdTimeApp 3"
  in
      KdTimeApp ((#1 jkd1, CTimeApp (arity - 1, #2 jkd1, #2 jkd2), KTimeFun (arity - 1)), kd1, kd2)
  end

fun as_KdQuan q wk kd =
  let
      val jwk = extract_judge_wfkind wk
      val jkd = extract_judge_kinding kd
      val () = assert (#2 jwk :: #1 jwk = #1 jkd) "KdQuan 1"
      val () = assert (#3 jkd = KType) "KdQuan 2"
  in
      KdQuan ((#1 jwk, CQuan (q, #2 jwk, #2 jkd), KType), wk, kd)
  end

fun as_KdRec wk kd =
  let
      val jwk = extract_judge_wfkind wk
      val jkd = extract_judge_kinding kd
      val () = assert (#2 jwk :: #1 jwk = #1 jkd) "KdRec 1"
      val () = assert (#3 jkd = shift0_c_k (#2 jwk)) "KdRec 2"
  in
      KdRec ((#1 jwk, CRec (#2 jwk, #2 jkd), #2 jwk), wk, kd)
  end

fun as_KdTypeNat kd =
  let
      val jkd = extract_judge_kinding kd
      val () = assert (#3 jkd = KNat) "KdTypeNat 1"
  in
      KdTypeNat ((#1 jkd, CTypeNat (#2 jkd), KType), kd)
  end

fun as_KdTypeArr kd1 kd2 =
  let
      val jkd1 = extract_judge_kinding kd1
      val jkd2 = extract_judge_kinding kd2
      val () = assert (#1 jkd1 = #1 jkd2) "KdTypeArr 1"
      val () = assert (#3 jkd1 = KType) "KdTypeArr 1"
      val () = assert (#3 jkd2 = KNat) "KdTypeArr 2"
  in
      KdTypeArr ((#1 jkd1, CTypeArr (#2 jkd1, #2 jkd2), KType), kd1, kd2)
  end

fun as_KdEq kd ke =
  let
      val jkd = extract_judge_kinding kd
      val jke = extract_judge_kdeq ke
      val () = assert (#1 jkd = #1 jke) "KdEq 1"
      val () = assert (#3 jkd = #2 jke) "KdEq 2"
  in
      KdEq ((#1 jkd, #2 jkd, #3 jke), kd, ke)
  end

fun as_KdUnOp opr kd =
  let
      val jkd = extract_judge_kinding kd
      val () = assert (#3 jkd = cunop_arg_kind opr) "KdUnOp 1"
  in
      KdUnOp ((#1 jkd, CUnOp (opr, #2 jkd), cunop_result_kind opr), kd)
  end

fun as_TyEqVar kctx x = TyEqVar (kctx, CVar x, CVar x)

fun as_TyEqConst kctx cn = TyEqConst (kctx, CConst cn, CConst cn)

fun as_TyEqBinOp opr te1 te2 =
  let
      val jte1 = extract_judge_tyeq te1
      val jte2 = extract_judge_tyeq te2
      val () = assert (#1 jte1 = #1 jte2) "TyEqBinOp 1"
  in
      TyEqBinOp ((#1 jte1, CBinOp (opr, #2 jte1, #2 jte2), CBinOp (opr, #3 jte1, #3 jte2)), te1, te2)
  end

fun as_TyEqIte te1 te2 te3 =
  let
      val jte1 = extract_judge_tyeq te1
      val jte2 = extract_judge_tyeq te2
      val jte3 = extract_judge_tyeq te3
      val () = assert (#1 jte1 = #1 jte2) "TyEqIte 1"
      val () = assert (#1 jte1 = #1 jte3) "TyEqIte 2"
  in
      TyEqIte ((#1 jte1, CIte (#2 jte1, #2 jte2, #2 jte3), CIte (#3 jte1, #3 jte2, #3 jte3)), te1, te2, te3)
  end

fun as_TyEqArrow te1 pr te2 =
  let
      val jte1 = extract_judge_tyeq te1
      val jpr = extract_judge_proping pr
      val jte2 = extract_judge_tyeq te2
      val () = assert (#1 jte1 = #1 jpr) "TyEqArrow 1"
      val () = assert (#1 jte1 = #1 jte2) "TyEqArrow 2"
      val (opr, i1, i2) = extract_p_bin_pred (#2 jpr)
      val () = assert (opr = PBTimeEq) "TyEqArrow 3"
  in
      TyEqArrow ((#1 jte1, CArrow (#2 jte1, i1, #2 jte2), CArrow (#3 jte1, i2, #3 jte2)), te1, pr, te2)
  end

fun as_TyEqApp te1 te2 =
  let
      val jte1 = extract_judge_tyeq te1
      val jte2 = extract_judge_tyeq te2
      val () = assert (#1 jte1 = #1 jte2) "TyEqApp 1"
  in
      TyEqApp ((#1 jte1, CApp (#2 jte1, #2 jte2), CApp (#3 jte1, #3 jte2)), te1, te2)
  end

fun as_TyEqBeta kctx t1 t2 = TyEqBeta (kctx, CApp (CAbs t1, t2), subst0_c_c t2 t1)

fun as_TyEqBetaRev kctx t1 t2 = TyEqBetaRev (kctx, subst0_c_c t2 t1, CApp (CAbs t1, t2))

fun as_TyEqQuan q ke te =
  let
      val jke = extract_judge_kdeq ke
      val jte = extract_judge_tyeq te
      val () = assert (#2 jke :: #1 jke = #1 jte) "TyEqQuan 1"
  in
      TyEqQuan ((#1 jke, CQuan (q, #2 jke, #2 jte), CQuan (q, #3 jke, #3 jte)), ke, te)
  end

fun as_TyEqRec ke te =
  let
      val jke = extract_judge_kdeq ke
      val jte = extract_judge_tyeq te
      val () = assert (#2 jke :: #1 jke = #1 jte) "TyEqRec 1"
  in
      TyEqRec ((#1 jke, CRec (#2 jke, #2 jte), CRec (#3 jke, #3 jte)), ke, te)
  end

fun as_TyEqTypeNat pr =
  let
      val jpr = extract_judge_proping pr
      val (opr, i1, i2) = extract_p_bin_pred (#2 jpr)
      val () = assert (opr = PBNatEq) "TyEqTypeNat 1"
  in
      TyEqTypeNat ((#1 jpr, CTypeNat i1, CTypeNat i2), pr)
  end

fun as_TyEqTypeArr te pr =
  let
      val jte = extract_judge_tyeq te
      val jpr = extract_judge_proping pr
      val () = assert (#1 jte = #1 jpr) "TyEqTypeArr 1"
      val (opr, i1, i2) = extract_p_bin_pred (#2 jpr)
      val () = assert (opr = PBNatEq) "TyEqTypeArr 2"
  in
      TyEqTypeArr ((#1 jte, CTypeArr (#2 jte, i1), CTypeArr (#3 jte, i2)), te, pr)
  end

fun as_TyEqAbs kctx t = TyEqAbs (kctx, CAbs t, CAbs t)

fun as_TyEqTimeAbs kctx i = TyEqTimeAbs (kctx, CTimeAbs i, CTimeAbs i)

fun as_TyEqTimeApp kctx arity c1 c2 = TyEqTimeApp (kctx, CTimeApp (arity, c1, c2), CTimeApp (arity, c1, c2))

fun as_TyEqTrans te1 te2 =
  let
      val jte1 = extract_judge_tyeq te1
      val jte2 = extract_judge_tyeq te2
      val () = assert (#1 jte1 = #1 jte2) "TyEqTrans 1"
      val () = assert (#3 jte1 = #2 jte2) "TyEqTrans 2"
  in
      TyEqTrans ((#1 jte1, #2 jte1, #3 jte2), te1, te2)
  end

fun as_TyEqUnOp opr te =
  let
      val jte = extract_judge_tyeq te
  in
      TyEqUnOp ((#1 jte, CUnOp (opr, #2 jte), CUnOp (opr, #3 jte)), te)
  end

fun as_TyEqNat pr =
  let
      val jpr = extract_judge_proping pr
      val (opr, n1, n2) = extract_p_bin_pred (#2 jpr)
      val () = assert (opr = PBNatEq) "TyEqNat 1"
  in
      TyEqNat ((#1 jpr, n1, n2), pr)
  end

fun as_TyEqTime pr =
  let
      val jpr = extract_judge_proping pr
      val (opr, r1, r2) = extract_p_bin_pred (#2 jpr)
      val () = assert (opr = PBTimeEq) "TyEqTime 1"
  in
      TyEqTime ((#1 jpr, r1, r2), pr)
  end

fun as_VConst cn = VConst (EConst cn)

fun as_VPair v1 v2 =
  let
      val ev1 = extract_expr_value v1
      val ev2 = extract_expr_value v2
  in
      VPair (EPair (ev1, ev2), v1, v2)
  end

fun as_VInj c v =
  let
      val ev = extract_expr_value v
  in
      VInj (EInj (c, ev), v)
  end

fun as_VAbs e = VAbs (EAbs e)

fun as_VAbsC e = VAbsC (EAbsC e)

fun as_VPack c v =
  let
      val ev = extract_expr_value v
  in
      VPack (EPack (c, ev), v)
  end

fun as_VFold v =
  let
      val ev = extract_expr_value v
  in
      VFold (EFold ev, v)
  end

fun add_kind k (kctx, tctx) = (k :: kctx, map shift0_c_c tctx)

fun add_type t (kctx, tctx) = (kctx, t :: tctx)

fun get_kctx (kctx, _) = kctx

fun get_tctx (_, tctx) = tctx

fun as_TyVar ctx x = TyVar (ctx, EVar x, nth (#2 ctx, x), T0)

fun as_TyApp ty1 ty2 =
  let
      val jty1 = extract_judge_typing ty1
      val jty2 = extract_judge_typing ty2
      val () = assert (#1 jty1 = #1 jty2) "TyApp 1"
      val (t1, i, t2) = extract_c_arrow (#3 jty1)
      val () = assert (t1 = #3 jty2) "TyApp 2"
  in
      TyApp ((#1 jty1, EApp (#2 jty1, #2 jty2), t2, Tadd (Tadd (Tadd (#4 jty1, #4 jty2), T1), i)), ty1, ty2)
  end

fun as_TyAbs kd ty =
  let
      val jkd = extract_judge_kinding kd
      val jty = extract_judge_typing ty
      val () = assert (#3 jkd = KType) "TyAbs 1"
      val () = assert (#1 jkd = (get_kctx $ #1 jty)) "TyAbs 2"
      val () = assert (#2 jkd = (hd $ get_tctx $ #1 jty)) "TyAbs 3"
  in
      TyAbs (((get_kctx $ #1 jty, tl $ get_tctx $ #1 jty), EAbs (#2 jty), CArrow (#2 jkd, #4 jty, #3 jty), T0), kd, ty)
  end

fun as_TyAppC ty kd =
  let
      val jty = extract_judge_typing ty
      val jkd = extract_judge_kinding kd
      val () = assert (#1 jkd = (get_kctx $ #1 jty)) "TyAppC 1"
      val (q, k, t) = extract_c_quan (#3 jty)
      val () = assert (q = QuanForall) "TyAppC 2"
      val () = assert (k = #3 jkd) "TyAppC 3"
  in
      TyAppC ((#1 jty, EAppC (#2 jty, #2 jkd), subst_c_c (#2 jkd) 0 t, #4 jty), ty, kd)
  end

fun as_TyAbsC wk va ty =
  let
      val jwk = extract_judge_wfkind wk
      val eva = extract_expr_value va
      val jty = extract_judge_typing ty
      val () = assert (#2 jwk :: #1 jwk = (get_kctx $ #1 jty)) "TyAbsC 1"
      val () = assert (#4 jty = T0) "TyAbsC 2"
      val () = assert (eva = #2 jty) "TyAbsC 3"
  in
      TyAbsC (((tl $ get_kctx $ #1 jty, map (shift_c_c ~1 0) $ get_tctx $ #1 jty), EAbsC (#2 jty), CForall (#2 jwk, #3 jty), T0), wk, va, ty) (* TODO *)
  end

fun unfold_EAbsCs e =
  case e of
      EAbsC e => unfold_EAbsCs e
    | _ => e

fun as_TyRec kd ty =
  let
      val jkd = extract_judge_kinding kd
      val jty = extract_judge_typing ty
      val () = assert (#3 jkd = KType) "TyRec 1"
      val () = assert (#1 jkd = (get_kctx $ #1 jty)) "TyRec 2"
      val () = assert (#2 jkd = (hd $ get_tctx $ #1 jty)) "TyRec 3"
      val () = assert (#2 jkd = #3 jty) "TyRec 4"
      val () = assert (#4 jty = T0) "TyRec 5"
      val e = unfold_EAbsCs (#2 jty)
      val _ = extract_e_abs e
  in
      TyRec (((get_kctx $ #1 jty, tl $ get_tctx $ #1 jty), ERec (#2 jty), #3 jty, T0), kd, ty)
  end

fun unfold_CApps t cs =
  case t of
      CApp (t, c) => unfold_CApps t (c :: cs)
    | _ => (t, cs)

fun as_TyFold kd ty =
  let
      val jkd = extract_judge_kinding kd
      val jty = extract_judge_typing ty
      val () = assert (#3 jkd = KType) "TyFold 1"
      val () = assert (#1 jkd = (get_kctx $ #1 jty)) "TyFold 2"
      val (t, cs) = unfold_CApps (#2 jkd) []
      val (_, t1) = extract_c_rec t
      val () = assert (#3 jty = CApps (subst0_c_c t t1) cs) "TyFold 3"
  in
      TyFold ((#1 jty, EFold (#2 jty), #2 jkd, #4 jty), kd, ty)
  end

fun as_TyUnfold ty =
  let
      val jty = extract_judge_typing ty
      val (t, cs) = unfold_CApps (#3 jty) []
      val (_, t1) = extract_c_rec t
  in
      TyUnfold ((#1 jty, EUnfold (#2 jty), CApps (subst0_c_c t t1) cs, #4 jty), ty)
  end

fun as_TyPack kd1 kd2 ty =
  let
      val jkd1 = extract_judge_kinding kd1
      val jkd2 = extract_judge_kinding kd2
      val jty = extract_judge_typing ty
      val () = assert (#1 jkd1 = #1 jkd2) "TyPack 1"
      val () = assert (#1 jkd1 = (get_kctx $ #1 jty)) "TyPack 2"
      val () = assert (#3 jkd1 = KType) "TyPack 3"
      val (q, k, t) = extract_c_quan (#2 jkd1)
      val () = assert (q = QuanExists) "TyPack 4"
      val () = assert (k = #3 jkd2) "TyPack 5"
      val () = assert (#3 jty = subst0_c_c (#2 jkd2) t) "TyPack 6"
  in
      TyPack ((#1 jty, EPack (#2 jkd2, #2 jty), #2 jkd1, #4 jty), kd1, kd2, ty)
  end

fun as_TyUnpack ty1 ty2 =
  let
      val jty1 = extract_judge_typing ty1
      val jty2 = extract_judge_typing ty2
      val (q, k, t) = extract_c_quan (#3 jty1)
      val () = assert (q = QuanExists) "TyUnpack 1"
      val () = assert (#1 jty2 = add_type t (add_kind k $ #1 jty1)) "TyUnpack 2"
  in
      TyUnpack ((#1 jty1, EUnpack (#2 jty1, #2 jty2), shift_c_c ~1 0 (#3 jty2), Tadd (#4 jty1, shift_c_c ~1 0 (#4 jty2))), ty1, ty2) (* TODO *)
  end

fun as_TyConst ctx cn = TyConst (ctx, EConst cn, const_type cn, T0)

fun as_TyPair ty1 ty2 =
  let
      val jty1 = extract_judge_typing ty1
      val jty2 = extract_judge_typing ty2
      val () = assert (#1 jty1 = #1 jty2) "TyPair 1"
  in
      TyPair ((#1 jty1, EPair (#2 jty1, #2 jty2), CProd (#3 jty1, #3 jty2), Tadd (#4 jty1, #4 jty2)), ty1, ty2)
  end

fun as_TyProj p ty =
  let
      val jty = extract_judge_typing ty
      val (t1, t2) = extract_c_prod (#3 jty)
  in
      TyProj ((#1 jty, EProj (p, #2 jty), case p of ProjFst => t1 | ProjSnd => t2, #4 jty), ty)
  end

fun as_TyInj inj ty kd =
  let
      val jty = extract_judge_typing ty
      val jkd = extract_judge_kinding kd
      val () = assert (#1 jkd = (get_kctx $ #1 jty)) "TyInj 1"
      val () = assert (#3 jkd = KType) "TyInj 2"
  in
      TyInj ((#1 jty, EInj (inj, #2 jty), case inj of InjInl => CSum (#3 jty, #2 jkd) | InjInr => CSum (#2 jkd, #3 jty), #4 jty), ty, kd)
  end

fun as_TyCase ty1 ty2 ty3 =
  let
      val jty1 = extract_judge_typing ty1
      val jty2 = extract_judge_typing ty2
      val jty3 = extract_judge_typing ty3
      val (t1, t2) = extract_c_sum (#3 jty1)
      val () = assert (#1 jty2 = add_type t1 (#1 jty1)) "TyCase 1"
      val () = assert (#1 jty3 = add_type t2 (#1 jty1)) "TyCase 2"
      val () = assert (#3 jty2 = #3 jty3) "TyCase 3"
  in
      TyCase ((#1 jty1, ECase (#2 jty1, #2 jty2, #2 jty3), #3 jty2, Tadd (#4 jty1, Tmax (#4 jty2, #4 jty3))), ty1, ty2, ty3)
  end

fun as_TyNew ty1 ty2 =
  let
      val jty1 = extract_judge_typing ty1
      val jty2 = extract_judge_typing ty2
      val () = assert (#1 jty1 = #1 jty2) "TyNew 1"
      val j = extract_c_type_nat (#3 jty2)
  in
      TyNew ((#1 jty1, ENew (#2 jty1, #2 jty2), CTypeArr (#3 jty1, j), Tadd (#4 jty1, #4 jty2)), ty1, ty2)
  end

fun as_TyRead ty1 ty2 pr =
  let
      val jty1 = extract_judge_typing ty1
      val jty2 = extract_judge_typing ty2
      val jpr = extract_judge_proping pr
      val () = assert (#1 jty1 = #1 jty2) "TyRead 1"
      val () = assert (get_kctx (#1 jty1) = #1 jpr) "TyRead 2"
      val (t, j1) = extract_c_type_arr (#3 jty1)
      val j2 = extract_c_type_nat (#3 jty2)
      val () = assert (#2 jpr = NLt (j2, j1)) "TyRead 3"
  in
      TyRead ((#1 jty1, ERead (#2 jty1, #2 jty2), t, Tadd (#4 jty1, #4 jty2)), ty1, ty2, pr)
  end

fun as_TyWrite ty1 ty2 pr ty3 =
  let
      val jty1 = extract_judge_typing ty1
      val jty2 = extract_judge_typing ty2
      val jpr = extract_judge_proping pr
      val jty3 = extract_judge_typing ty3
      val () = assert (#1 jty1 = #1 jty2) "TyWrite 1"
      val () = assert (#1 jty1 = #1 jty3) "TyWrite 2"
      val () = assert (get_kctx (#1 jty1) = #1 jpr) "TyWrite 3"
      val (t, j1) = extract_c_type_arr (#3 jty1)
      val j2 = extract_c_type_nat (#3 jty2)
      val () = assert (#2 jpr = NLt (j2, j1)) "TyWrite 4"
      val () = assert (#3 jty3 = t) "TyWrite 5"
  in
      TyWrite ((#1 jty1, EWrite (#2 jty1, #2 jty2, #2 jty3), CTypeUnit, Tadd (Tadd (#4 jty1, #4 jty2), #4 jty3)), ty1, ty2, pr, ty3)
  end

fun as_TySubTy ty te =
  let
      val jty = extract_judge_typing ty
      val jte = extract_judge_tyeq te
      val () = assert (#1 jte = (get_kctx $ #1 jty)) "TySubTy 1"
      val () = assert (#2 jte = #3 jty) "TySubTy 2"
  in
      TySubTy ((#1 jty, #2 jty, #3 jte, #4 jty), ty, te)
  end

fun as_TySubTi ty pr =
  let
      val jty = extract_judge_typing ty
      val jpr = extract_judge_proping pr
      val (opr, i1, i2) = extract_p_bin_pred (#2 jpr)
      val () = assert (opr = PBTimeLe) "TySubTi 1"
      val () = assert (#1 jpr = (get_kctx $ #1 jty)) "TySubTi 2"
      val () = assert (i1 = #4 jty) "TySubTi 3"
  in
      TySubTi ((#1 jty, #2 jty, #3 jty, i2), ty, pr)
  end

fun as_TyHalt ty =
  let
      val jty = extract_judge_typing ty
  in
      TyHalt ((#1 jty, EHalt (#2 jty), CTypeUnit, #4 jty), ty)
  end

fun as_TyLet ty1 ty2 =
  let
      val jty1 = extract_judge_typing ty1
      val jty2 = extract_judge_typing ty2
      val () = assert (#1 jty2 = add_type (#3 jty1) (#1 jty1)) "TyLet 1"
  in
      TyLet ((#1 jty1, ELet (#2 jty1, #2 jty2), #3 jty2, Tadd (#4 jty1, #4 jty2)), ty1, ty2)
  end

fun unfold_CForalls t ks =
  case t of
      CQuan (QuanForall, k, t) => unfold_CForalls t (k :: ks)
    | _ => (t, ks)

fun as_TyFix ctx kd ty =
  let
      val jkd = extract_judge_kinding kd
      val jty = extract_judge_typing ty
      val () = assert (#1 jkd = []) "TyFix 1"
      val () = assert (#3 jkd = KType) "TyFix 2"
      val (t, ks) = unfold_CForalls (#2 jkd) []
      val (t1, i, t2) = extract_c_arrow t
      val () = assert (#1 jty = (ks, [t1, #2 jkd])) "TyFix 3"
      val () = assert (#3 jty = t2) "TyFix 4"
      val () = assert (#4 jty = i) "TyFix 5"
  in
      TyFix ((ctx, EFix (length ks, #2 jty), #2 jkd, T0), kd, ty)
  end

fun as_TyPrimBinOp opr ty1 ty2 =
  let
      val jty1 = extract_judge_typing ty1
      val jty2 = extract_judge_typing ty2
      val () = assert (#1 jty1 = #1 jty2) "TyPrimBinOp 1"
      val () = assert (#3 jty1 = pebinop_arg1_type opr) "TyPrimBinOp 2"
      val () = assert (#3 jty2 = pebinop_arg2_type opr) "TyPrimBinOp 3"
  in
      TyPrimBinOp ((#1 jty1, EBinOp (EBPrim opr, #2 jty1, #2 jty2), pebinop_result_type opr, Tadd (#4 jty1, #4 jty2)), ty1, ty2)
  end
end

functor CstrDerivGenericTransformerFun(
    structure MicroTiMLDef : SIG_MICRO_TIML_DEF
    structure Action :
              sig
                  type down
                  type up

                  val upward_base : up
                  val combiner : up * up -> up

                  val add_kind : MicroTiMLDef.kind * down -> down

                  val on_pr_leaf : MicroTiMLDef.proping * down -> MicroTiMLDef.proping * up
                  val on_ke_leaf : MicroTiMLDef.kdeq * down -> MicroTiMLDef.kdeq * up
                  val on_kd_leaf : MicroTiMLDef.kinding * down -> MicroTiMLDef.kinding * up
                  val on_wk_leaf : MicroTiMLDef.wfkind * down -> MicroTiMLDef.wfkind * up
                  val on_wp_leaf : MicroTiMLDef.wfprop * down -> MicroTiMLDef.wfprop * up
                  val on_te_leaf : MicroTiMLDef.tyeq * down -> MicroTiMLDef.tyeq * up

                  val transformer_proping : MicroTiMLDef.proping * down -> (MicroTiMLDef.proping * up) option
                  val transformer_kdeq : (MicroTiMLDef.kdeq * down -> MicroTiMLDef.kdeq * up) * (MicroTiMLDef.proping * down -> MicroTiMLDef.proping * up) -> MicroTiMLDef.kdeq * down -> (MicroTiMLDef.kdeq * up) option
                  val transformer_kinding : (MicroTiMLDef.kinding * down -> MicroTiMLDef.kinding * up) * (MicroTiMLDef.wfkind * down -> MicroTiMLDef.wfkind * up) * (MicroTiMLDef.kdeq * down -> MicroTiMLDef.kdeq * up) -> MicroTiMLDef.kinding * down -> (MicroTiMLDef.kinding * up) option
                  val transformer_wfkind : (MicroTiMLDef.wfkind * down -> MicroTiMLDef.wfkind * up) * (MicroTiMLDef.wfprop * down -> MicroTiMLDef.wfprop * up) -> MicroTiMLDef.wfkind * down -> (MicroTiMLDef.wfkind * up) option
                  val transformer_wfprop : (MicroTiMLDef.wfprop * down -> MicroTiMLDef.wfprop * up) * (MicroTiMLDef.kinding * down -> MicroTiMLDef.kinding * up) -> MicroTiMLDef.wfprop * down -> (MicroTiMLDef.wfprop * up) option
                  val transformer_tyeq : (MicroTiMLDef.tyeq * down -> MicroTiMLDef.tyeq * up) * (MicroTiMLDef.proping * down -> MicroTiMLDef.proping * up) * (MicroTiMLDef.kdeq * down -> MicroTiMLDef.kdeq * up) -> MicroTiMLDef.tyeq * down -> (MicroTiMLDef.tyeq * up) option
              end) : SIG_CSTR_DERIV_GENERIC_TRANSFORMER =
struct
open List
open Util
infixr 0 $

structure MicroTiMLDef = MicroTiMLDef
open MicroTiMLDef
structure MicroTiMLUtil = MicroTiMLUtilFun(MicroTiMLDef)
open MicroTiMLUtil

structure DerivAssembler = DerivAssemblerFun(MicroTiMLDef)
open DerivAssembler

open Action

val combine = foldl combiner upward_base

fun default_transform_proping (pr, down) = on_pr_leaf (pr, down)

and transform_proping (pr, down) =
    case transformer_proping (pr, down) of
        SOME res => res
      | NONE => default_transform_proping (pr, down)

fun default_transform_kdeq (ke, down) =
    case ke of
        KdEqKType _ => on_ke_leaf (ke, down)
      | KdEqKArrow (_, ke1, ke2) =>
        let
            val (ke1, up1) = transform_kdeq (ke1, down)
            val (ke2, up2) = transform_kdeq (ke2, down)
        in
            (as_KdEqKArrow ke1 ke2, combine [up1, up2])
        end
      | KdEqBaseSort _ => on_ke_leaf (ke, down)
      | KdEqSubset (_, ke, pr) =>
        let
            val (ke, up1) = transform_kdeq (ke, down)
            val jke = extract_judge_kdeq ke
            val (pr, up2) = transform_proping (pr, add_kind (#2 jke, down))
        in
            (as_KdEqSubset ke pr, combine [up1, up2])
        end
      | KdEqSubsetElimLeft (_, pr) =>
        let
            val jpr = extract_judge_proping pr
            val (pr, up1) = transform_proping (pr, add_kind (hd $ #1 jpr, down))
        in
            (as_KdEqSubsetElimLeft pr, combine [up1])
        end
      | KdEqSubsetElimRight (_, pr) =>
        let
            val jpr = extract_judge_proping pr
            val (pr, up1) = transform_proping (pr, add_kind (hd $ #1 jpr, down))
        in
            (as_KdEqSubsetElimRight pr, combine [up1])
        end

and transform_kdeq (ke, down) =
    case transformer_kdeq (transform_kdeq, transform_proping) (ke, down) of
        SOME res => res
      | NONE => default_transform_kdeq (ke, down)

fun default_transform_kinding (kd, down) =
    case kd of
        KdVar _ => on_kd_leaf (kd, down)
      | KdConst _ => on_kd_leaf (kd, down)
      | KdBinOp (judge, kd1, kd2) =>
        let
            val (kd1, up1) = transform_kinding (kd1, down)
            val (kd2, up2) = transform_kinding (kd2, down)
            val (opr, _, _) = extract_c_bin_op (#2 judge)
        in
            (as_KdBinOp opr kd1 kd2, combine [up1, up2])
        end
      | KdIte (_, kd1, kd2, kd3) =>
        let
            val (kd1, up1) = transform_kinding (kd1, down)
            val (kd2, up2) = transform_kinding (kd2, down)
            val (kd3, up3) = transform_kinding (kd3, down)
        in
            (as_KdIte kd1 kd2 kd3, combine [up1, up2, up3])
        end
      | KdArrow (_, kd1, kd2, kd3) =>
        let
            val (kd1, up1) = transform_kinding (kd1, down)
            val (kd2, up2) = transform_kinding (kd2, down)
            val (kd3, up3) = transform_kinding (kd3, down)
        in
            (as_KdArrow kd1 kd2 kd3, combine [up1, up2, up3])
        end
      | KdAbs (_, wk, kd) =>
        let
            val (wk, up1) = transform_wfkind (wk, down)
            val jwk = extract_judge_wfkind wk
            val (kd, up2) = transform_kinding (kd, add_kind (#2 jwk, down))
        in
            (as_KdAbs wk kd, combine [up1, up2])
        end
      | KdApp (_, kd1, kd2) =>
        let
            val (kd1, up1) = transform_kinding (kd1, down)
            val (kd2, up2) = transform_kinding (kd2, down)
        in
            (as_KdApp kd1 kd2, combine [up1, up2])
        end
      | KdTimeAbs (_, kd) =>
        let
            val (kd, up1) = transform_kinding (kd, add_kind (KNat, down))
        in
            (as_KdTimeAbs kd, combine [up1])
        end
      | KdTimeApp (_, kd1, kd2) =>
        let
            val (kd1, up1) = transform_kinding (kd1, down)
            val (kd2, up2) = transform_kinding (kd2, down)
        in
            (as_KdTimeApp kd1 kd2, combine [up1, up2])
        end
      | KdQuan (judge, wk, kd) =>
        let
            val (wk, up1) = transform_wfkind (wk, down)
            val jwk = extract_judge_wfkind wk
            val (kd, up2) = transform_kinding (kd, add_kind (#2 jwk, down))
            val (q, _, _) = extract_c_quan (#2 judge)
        in
            (as_KdQuan q wk kd, combine [up1, up2])
        end
      | KdRec (_, wk, kd) =>
        let
            val (wk, up1) = transform_wfkind (wk, down)
            val jwk = extract_judge_wfkind wk
            val (kd, up2) = transform_kinding (kd, add_kind (#2 jwk, down))
        in
            (as_KdRec wk kd, combine [up1, up2])
        end
      | KdEq (_, kd, ke) =>
        let
            val (kd, up1) = transform_kinding (kd, down)
            val (ke, up2) = transform_kdeq (ke, down)
        in
            (as_KdEq kd ke, combine [up1, up2])
        end
      | KdUnOp (judge, kd) =>
        let
            val (kd, up1) = transform_kinding (kd, down)
            val (opr, _) = extract_c_un_op (#2 judge)
        in
            (as_KdUnOp opr kd, combine [up1])
        end
      | KdTypeNat (_, kd) =>
        let
            val (kd, up1) = transform_kinding (kd, down)
        in
            (as_KdTypeNat kd, combine [up1])
        end
      | KdTypeArr (_, kd1, kd2) =>
        let
            val (kd1, up1) = transform_kinding (kd1, down)
            val (kd2, up2) = transform_kinding (kd2, down)
        in
            (as_KdTypeArr kd1 kd2, combine [up1, up2])
                end
   | KdAdmit _ => on_kd_leaf (kd, down)

and transform_kinding (kd, down) =
 case transformer_kinding (transform_kinding, transform_wfkind, transform_kdeq) (kd, down) of
     SOME res => res
   | NONE => default_transform_kinding (kd, down)

and default_transform_wfkind (wk, down) =
 case wk of
     WfKdType _ => on_wk_leaf (wk, down)
   | WfKdArrow (_, wk1, wk2) =>
     let
         val (wk1, up1) = transform_wfkind (wk1, down)
         val (wk2, up2) = transform_wfkind (wk2, down)
     in
         (as_WfKdArrow wk1 wk2, combine [up1, up2])
     end
   | WfKdBaseSort _ => on_wk_leaf (wk, down)
   | WfKdSubset (_, wk, wp) =>
     let
         val (wk, up1) = transform_wfkind (wk, down)
         val jwk = extract_judge_wfkind wk
         val (wp, up2) = transform_wfprop (wp, add_kind (#2 jwk, down))
     in
         (as_WfKdSubset wk wp, combine [up1, up2])
     end
   | WfKdAdmit _ => on_wk_leaf (wk, down)

and transform_wfkind (wk, down) =
 case transformer_wfkind (transform_wfkind, transform_wfprop) (wk, down) of
     SOME res => res
   | NONE => default_transform_wfkind (wk, down)

and default_transform_wfprop (wp, down) =
 case wp of
     WfPropTrue judge => on_wp_leaf (wp, down)
   | WfPropFalse judge => on_wp_leaf (wp, down)
   | WfPropBinConn (judge, wp1, wp2) =>
     let
         val (wp1, up1) = transform_wfprop (wp1, down)
         val (wp2, up2) = transform_wfprop (wp2, down)
         val (opr, _, _) = extract_p_bin_conn (#2 judge)
     in
         (as_WfPropBinConn opr wp1 wp2, combine [up1, up2])
     end
   | WfPropNot (_, wp) =>
     let
         val (wp, up1) = transform_wfprop (wp, down)
     in
         (as_WfPropNot wp, combine [up1])
     end
   | WfPropBinPred (judge, kd1, kd2) =>
     let
         val (kd1, up1) = transform_kinding (kd1, down)
         val (kd2, up2) = transform_kinding (kd2, down)
         val (opr, _, _) = extract_p_bin_pred (#2 judge)
     in
         (as_WfPropBinPred opr kd1 kd2, combine [up1, up2])
     end
   | WfPropQuan (judge, wp) =>
     let
         val (q, b, _) = extract_p_quan (#2 judge)
         val (wp, up1) = transform_wfprop (wp, add_kind (KBaseSort b, down))
     in
         (as_WfPropQuan q b wp, combine [up1])
     end

and transform_wfprop (wp, down) =
 case transformer_wfprop (transform_wfprop, transform_kinding) (wp, down) of
     SOME res => res
   | NONE => default_transform_wfprop (wp, down)

fun default_transform_tyeq (te, down) =
 case te of
     TyEqVar judge => on_te_leaf (te, down)
   | TyEqConst judge => on_te_leaf (te, down)
   | TyEqBinOp (judge, te1, te2) =>
     let
         val (te1, up1) = transform_tyeq (te1, down)
         val (te2, up2) = transform_tyeq (te2, down)
         val (opr, _, _) = extract_c_bin_op (#2 judge)
     in
         (as_TyEqBinOp opr te1 te2, combine [up1, up2])
     end
   | TyEqIte (_, te1, te2, te3) =>
     let
         val (te1, up1) = transform_tyeq (te1, down)
         val (te2, up2) = transform_tyeq (te2, down)
         val (te3, up3) = transform_tyeq (te3, down)
     in
         (as_TyEqIte te1 te2 te3, combine [up1, up2, up3])
     end
   | TyEqArrow (_, te1, pr, te2) =>
     let
         val (te1, up1) = transform_tyeq (te1, down)
         val (pr, up2) = transform_proping (pr, down)
         val (te2, up3) = transform_tyeq (te2, down)
     in
         (as_TyEqArrow te1 pr te2, combine [up1, up2, up3])
     end
   | TyEqApp (_, te1, te2) =>
     let
         val (te1, up1) = transform_tyeq (te1, down)
         val (te2, up2) = transform_tyeq (te2, down)
     in
         (as_TyEqApp te1 te2, combine [up1, up2])
     end
   | TyEqTimeApp _ => on_te_leaf (te, down)
   | TyEqBeta _ => on_te_leaf (te, down)
   | TyEqBetaRev _ => on_te_leaf (te, down)
   | TyEqQuan (judge, ke, te) =>
     let
         val (ke, up1) = transform_kdeq (ke, down)
         val jke = extract_judge_kdeq ke
         val (te, up2) = transform_tyeq (te, add_kind (#2 jke, down))
         val (q, _, _) = extract_c_quan (#2 judge)
     in
         (as_TyEqQuan q ke te, combine [up1, up2])
     end
   | TyEqRec (_, ke, te) =>
     let
         val (ke, up1) = transform_kdeq (ke, down)
         val jke = extract_judge_kdeq ke
         val (te, up2) = transform_tyeq (te, add_kind (#2 jke, down))
     in
         (as_TyEqRec ke te, combine [up1, up2])
     end
   | TyEqAbs _ => on_te_leaf (te, down)
   | TyEqTimeAbs _ => on_te_leaf (te, down)
   | TyEqUnOp (judge, te) =>
     let
         val (te, up1) = transform_tyeq (te, down)
         val (opr, _) = extract_c_un_op (#2 judge)
     in
         (as_TyEqUnOp opr te, combine [up1])
     end
   | TyEqTrans (_, te1, te2) =>
     let
         val (te1, up1) = transform_tyeq (te1, down)
         val (te2, up2) = transform_tyeq (te2, down)
     in
         (as_TyEqTrans te1 te2, combine [up1, up2])
     end
   | TyEqTypeNat (_, pr) =>
     let
         val (pr, up1) = transform_proping (pr, down)
     in
         (as_TyEqTypeNat pr, combine [up1])
     end
   | TyEqTypeArr (_, te, pr) =>
     let
         val (te, up1) = transform_tyeq (te, down)
         val (pr, up2) = transform_proping (pr, down)
     in
         (as_TyEqTypeArr te pr, combine [up1, up2])
     end
   | TyEqNat (_, pr) =>
     let
         val (pr, up1) = transform_proping (pr, down)
     in
         (as_TyEqNat pr, combine [up1])
     end
   | TyEqTime (_, pr) =>
     let
         val (pr, up1) = transform_proping (pr, down)
     in
         (as_TyEqTime pr, combine [up1])
     end

and transform_tyeq (te, down) =
 case transformer_tyeq (transform_tyeq, transform_proping, transform_kdeq) (te, down) of
     SOME res => res
   | NONE => default_transform_tyeq (te, down)
end

functor ExprDerivGenericTransformerFun(
 structure MicroTiMLDef : SIG_MICRO_TIML_DEF
 structure Action :
           sig
               type kdown
               type tdown
               type down = kdown * tdown
               type up

               val upward_base : up
               val combiner : up * up -> up

               val add_kind : MicroTiMLDef.kind * down -> down
               val add_type : MicroTiMLDef.cstr * tdown -> tdown

               val on_va_leaf : MicroTiMLDef.value * down -> MicroTiMLDef.value * up
               val on_ty_leaf : MicroTiMLDef.typing * down -> MicroTiMLDef.typing * up

               val transform_proping : MicroTiMLDef.proping * kdown -> MicroTiMLDef.proping * up
               val transform_kinding : MicroTiMLDef.kinding * kdown -> MicroTiMLDef.kinding * up
               val transform_wfkind : MicroTiMLDef.wfkind * kdown -> MicroTiMLDef.wfkind * up
               val transform_tyeq : MicroTiMLDef.tyeq * kdown -> MicroTiMLDef.tyeq * up

               val transformer_value : (MicroTiMLDef.value * down -> MicroTiMLDef.value * up) -> MicroTiMLDef.value * down -> (MicroTiMLDef.value * up) option
               val transformer_typing : (MicroTiMLDef.typing * down -> MicroTiMLDef.typing * up) * (MicroTiMLDef.value * down -> MicroTiMLDef.value * up) -> MicroTiMLDef.typing * down -> (MicroTiMLDef.typing * up) option
           end) : SIG_EXPR_DERIV_GENERIC_TRANSFORMER =
struct
open List
open Util
infixr 0 $

structure MicroTiMLDef = MicroTiMLDef
open MicroTiMLDef
structure MicroTiMLUtil = MicroTiMLUtilFun(MicroTiMLDef)
open MicroTiMLUtil

structure DerivAssembler = DerivAssemblerFun(MicroTiMLDef)
open DerivAssembler

open Action

val combine = foldl combiner upward_base

fun default_transform_value (va, down) =
case va of
   VConst _ => on_va_leaf (va, down)
 | VPair (_, va1, va2) =>
   let
       val (va1, up1) = transform_value (va1, down)
       val (va2, up2) = transform_value (va2, down)
   in
       (as_VPair va1 va2, combine [up1, up2])
   end
 | VInj (e, va1) =>
   let
       val (inj, _) = extract_e_inj e
       val (va1, up1) = transform_value (va1, down)
   in
       (as_VInj inj va1, combine [up1])
   end
 | VAbs _ => on_va_leaf (va, down)
 | VAbsC _ => on_va_leaf (va, down)
 | VPack (e, va1) =>
   let
       val (c, _) = extract_e_pack e
       val (va1, up1) = transform_value (va1, down)
   in
       (as_VPack c va1, combine [up1])
   end
 | VFold (_, va1) =>
   let
       val (va1, up1) = transform_value (va1, down)
   in
       (as_VFold va1, combine [up1])
   end

and transform_value (va, down) =
 case transformer_value transform_value (va, down) of
     SOME res => res
   | NONE => default_transform_value (va, down)

fun default_transform_typing (ty, down as (kdown, tdown)) =
 case ty of
     TyVar judge => on_ty_leaf (ty, down)
   | TyApp (_, ty1, ty2) =>
     let
         val (ty1, up1) = transform_typing (ty1, down)
         val (ty2, up2) = transform_typing (ty2, down)
     in
         (as_TyApp ty1 ty2, combine [up1, up2])
     end
   | TyAbs (_, kd, ty) =>
     let
         val (kd, up1) = transform_kinding (kd, kdown)
         val jkd = extract_judge_kinding kd
         val (ty, up2) = transform_typing (ty, (kdown, add_type (#2 jkd, tdown)))
     in
         (as_TyAbs kd ty, combine [up1, up2])
     end
   | TyAppC (_, ty, kd) =>
     let
         val (ty, up1) = transform_typing (ty, down)
         val (kd, up2) = transform_kinding (kd, kdown)
     in
         (as_TyAppC ty kd, combine [up1, up2])
     end
   | TyAbsC (_, wk, va, ty) =>
     let
         val (wk, up1) = transform_wfkind (wk, kdown)
         val jwk = extract_judge_wfkind wk
         val (va, up2) = transform_value (va, add_kind (#2 jwk, down))
         val (ty, up3) = transform_typing (ty, add_kind (#2 jwk, down))
     in
         (as_TyAbsC wk va ty, combine [up1, up2, up3])
     end
   | TyRec (_, kd, ty) =>
     let
         val (kd, up1) = transform_kinding (kd, kdown)
         val jkd = extract_judge_kinding kd
         val (ty, up2) = transform_typing (ty, (kdown, add_type (#2 jkd, tdown)))
     in
         (as_TyRec kd ty, combine [up1, up2])
     end
   | TyFold (_, kd, ty) =>
     let
         val (kd, up1) = transform_kinding (kd, kdown)
         val (ty, up2) = transform_typing (ty, down)
     in
         (as_TyFold kd ty, combine [up1, up2])
     end
   | TyUnfold (_, ty) =>
     let
         val (ty, up1) = transform_typing (ty, down)
     in
         (as_TyUnfold ty, combine [up1])
     end
   | TyPack (_, kd1, kd2, ty) =>
     let
         val (kd1, up1) = transform_kinding (kd1, kdown)
         val (kd2, up2) = transform_kinding (kd2, kdown)
         val (ty, up3) = transform_typing (ty, down)
     in
         (as_TyPack kd1 kd2 ty, combine [up1, up2, up3])
     end
   | TyUnpack (_, ty1, ty2) =>
     let
         val (ty1, up1) = transform_typing (ty1, down)
         val jty1 = extract_judge_typing ty1
         val (_, k, t) = extract_c_quan (#3 jty1)
         val (ty2, up2) = transform_typing (ty2, let val (kdown, tdown) = add_kind (k, down) in (kdown, add_type (t, tdown)) end)
     in
         (as_TyUnpack ty1 ty2, combine [up1, up2])
     end
   | TyConst _ => on_ty_leaf (ty, down)
   | TyPair (_, ty1, ty2) =>
     let
         val (ty1, up1) = transform_typing (ty1, down)
         val (ty2, up2) = transform_typing (ty2, down)
     in
         (as_TyPair ty1 ty2, combine [up1, up2])
     end
   | TyProj (judge, ty) =>
     let
         val (ty, up1) = transform_typing (ty, down)
         val (p, _) = extract_e_proj (#2 judge)
     in
         (as_TyProj p ty, combine [up1])
     end
   | TyInj (judge, ty, kd) =>
     let
         val (ty, up1) = transform_typing (ty, down)
         val (kd, up2) = transform_kinding (kd, kdown)
         val (inj, _) = extract_e_inj (#2 judge)
     in
         (as_TyInj inj ty kd, combine [up1, up2])
     end
   | TyCase (_, ty1, ty2, ty3) =>
     let
         val (ty1, up1) = transform_typing (ty1, down)
         val jty1 = extract_judge_typing ty1
         val (t1, t2) = extract_c_sum (#3 jty1)
         val (ty2, up2) = transform_typing (ty2, (kdown, add_type (t1, tdown)))
         val (ty3, up3) = transform_typing (ty3, (kdown, add_type (t2, tdown)))
     in
         (as_TyCase ty1 ty2 ty3, combine [up1, up2, up3])
     end
   | TyNew (_, ty1, ty2) =>
     let
         val (ty1, up1) = transform_typing (ty1, down)
         val (ty2, up2) = transform_typing (ty2, down)
     in
         (as_TyNew ty1 ty2, combine [up1, up2])
     end
   | TyRead (_, ty1, ty2, pr) =>
     let
         val (ty1, up1) = transform_typing (ty1, down)
         val (ty2, up2) = transform_typing (ty2, down)
         val (pr, up3) = transform_proping (pr, kdown)
     in
         (as_TyRead ty1 ty2 pr, combine [up1, up2, up3])
     end
   | TyWrite (_, ty1, ty2, pr, ty3) =>
     let
         val (ty1, up1) = transform_typing (ty1, down)
         val (ty2, up2) = transform_typing (ty2, down)
         val (pr, up3) = transform_proping (pr, kdown)
         val (ty3, up4) = transform_typing (ty3, down)
     in
         (as_TyWrite ty1 ty2 pr ty3, combine [up1, up2, up3, up4])
     end
   | TySubTy (_, ty, te) =>
     let
         val (ty, up1) = transform_typing (ty, down)
         val (te, up2) = transform_tyeq (te, kdown)
     in
         (as_TySubTy ty te, combine [up1, up2])
     end
   | TySubTi (_, ty, pr) =>
     let
         val (ty, up1) = transform_typing (ty, down)
         val (pr, up2) = transform_proping (pr, kdown)
     in
         (as_TySubTi ty pr, combine [up1, up2])
     end
   | TyHalt (_, ty) =>
     let
         val (ty, up1) = transform_typing (ty, down)
     in
         (as_TyHalt ty, combine [up1])
     end
   | TyLet (_, ty1, ty2) =>
     let
         val (ty1, up1) = transform_typing (ty1, down)
         val jty1 = extract_judge_typing ty1
         val (ty2, up2) = transform_typing (ty2, (kdown, add_type (#3 jty1, tdown)))
     in
         (as_TyLet ty1 ty2, combine [up1, up2])
     end
   | TyFix _ => on_ty_leaf (ty, down)
   | TyPrimBinOp (judge, ty1, ty2) =>
     let
         val (ty1, up1) = transform_typing (ty1, down)
         val (ty2, up2) = transform_typing (ty2, down)
         val (opr, _, _) = extract_e_prim_bin_op (#2 judge)
     in
         (as_TyPrimBinOp opr ty1 ty2, combine [up1, up2])
     end

and transform_typing (ty, down) =
    case transformer_typing (transform_typing, transform_value) (ty, down) of
        SOME res => res
      | NONE => default_transform_typing (ty, down)
end

functor CstrDerivGenericOnlyDownTransformerFun(
    structure MicroTiMLDef : SIG_MICRO_TIML_DEF
    structure Action :
              sig
                  type down

                  val add_kind : MicroTiMLDef.kind * down -> down

                  val on_pr_leaf : MicroTiMLDef.proping * down -> MicroTiMLDef.proping
                  val on_ke_leaf : MicroTiMLDef.kdeq * down -> MicroTiMLDef.kdeq
                  val on_kd_leaf : MicroTiMLDef.kinding * down -> MicroTiMLDef.kinding
                  val on_wk_leaf : MicroTiMLDef.wfkind * down -> MicroTiMLDef.wfkind
                  val on_wp_leaf : MicroTiMLDef.wfprop * down -> MicroTiMLDef.wfprop
                  val on_te_leaf : MicroTiMLDef.tyeq * down -> MicroTiMLDef.tyeq

                  val transformer_proping : MicroTiMLDef.proping * down -> MicroTiMLDef.proping option
                  val transformer_kdeq : (MicroTiMLDef.kdeq * down -> MicroTiMLDef.kdeq) * (MicroTiMLDef.proping * down -> MicroTiMLDef.proping) -> MicroTiMLDef.kdeq * down -> MicroTiMLDef.kdeq option
                  val transformer_kinding : (MicroTiMLDef.kinding * down -> MicroTiMLDef.kinding) * (MicroTiMLDef.wfkind * down -> MicroTiMLDef.wfkind) * (MicroTiMLDef.kdeq * down -> MicroTiMLDef.kdeq) -> MicroTiMLDef.kinding * down -> MicroTiMLDef.kinding option
                  val transformer_wfkind : (MicroTiMLDef.wfkind * down -> MicroTiMLDef.wfkind) * (MicroTiMLDef.wfprop * down -> MicroTiMLDef.wfprop) -> MicroTiMLDef.wfkind * down -> MicroTiMLDef.wfkind option
                  val transformer_wfprop : (MicroTiMLDef.wfprop * down -> MicroTiMLDef.wfprop) * (MicroTiMLDef.kinding * down -> MicroTiMLDef.kinding) -> MicroTiMLDef.wfprop * down -> MicroTiMLDef.wfprop option
                  val transformer_tyeq : (MicroTiMLDef.tyeq * down -> MicroTiMLDef.tyeq) * (MicroTiMLDef.proping * down -> MicroTiMLDef.proping) * (MicroTiMLDef.kdeq * down -> MicroTiMLDef.kdeq) -> MicroTiMLDef.tyeq * down -> MicroTiMLDef.tyeq option
              end) : SIG_CSTR_DERIV_GENERIC_ONLY_DOWN_TRANSFORMER =
struct
open List
open Util
infixr 0 $

structure MicroTiMLDef =  MicroTiMLDef
open MicroTiMLDef

open Action

structure Transformer = CstrDerivGenericTransformerFun(
    structure MicroTiMLDef = MicroTiMLDef
    structure Action =
    struct
    type down = down
    type up = unit

    val upward_base = ()
    fun combiner ((), ()) = ()

    val add_kind = add_kind

    val on_pr_leaf = (fn j => (j, ())) o on_pr_leaf
    val on_ke_leaf = (fn j => (j, ())) o on_ke_leaf
    val on_kd_leaf = (fn j => (j, ())) o on_kd_leaf
    val on_wk_leaf = (fn j => (j, ())) o on_wk_leaf
    val on_wp_leaf = (fn j => (j, ())) o on_wp_leaf
    val on_te_leaf = (fn j => (j, ())) o on_te_leaf

    val transformer_proping = Option.map (fn pr => (pr, ())) o transformer_proping

    fun transformer_kdeq (on_kdeq, on_proping) =
      let
          val on_kdeq_no_up = fst o on_kdeq
          val on_proping_no_up = fst o on_proping
      in
          Option.map (fn ke => (ke, ())) o Action.transformer_kdeq (on_kdeq_no_up, on_proping_no_up)
      end

    fun transformer_kinding (on_kinding, on_wfkind, on_kdeq) =
      let
          val on_kinding_no_up = fst o on_kinding
          val on_wfkind_no_up = fst o on_wfkind
          val on_kdeq_no_up = fst o on_kdeq
      in
          Option.map (fn kd => (kd, ())) o Action.transformer_kinding (on_kinding_no_up, on_wfkind_no_up, on_kdeq_no_up)
      end

    fun transformer_wfkind (on_wfkind, on_wfprop) =
      let
          val on_wfkind_no_up = fst o on_wfkind
          val on_wfprop_no_up = fst o on_wfprop
      in
          Option.map (fn wk => (wk, ())) o Action.transformer_wfkind (on_wfkind_no_up, on_wfprop_no_up)
      end

    fun transformer_wfprop (on_wfprop, on_kinding) =
      let
          val on_wfprop_no_up = fst o on_wfprop
          val on_kinding_no_up = fst o on_kinding
      in
          Option.map (fn wp => (wp, ())) o Action.transformer_wfprop (on_wfprop_no_up, on_kinding_no_up)
      end

    fun transformer_tyeq (on_tyeq, on_proping, on_kdeq) =
      let
          val on_tyeq_no_up = fst o on_tyeq
          val on_proping_no_up = fst o on_proping
          val on_kdeq_no_up = fst o on_kdeq
      in
          Option.map (fn te => (te, ())) o Action.transformer_tyeq (on_tyeq_no_up, on_proping_no_up, on_kdeq_no_up)
      end
    end)

val transform_proping = fst o Transformer.transform_proping
val transform_kdeq = fst o Transformer.transform_kdeq
val transform_kinding = fst o Transformer.transform_kinding
val transform_wfkind = fst o Transformer.transform_wfkind
val transform_wfprop = fst o Transformer.transform_wfprop
val transform_tyeq = fst o Transformer.transform_tyeq
end

functor ExprDerivGenericOnlyDownTransformerFun(
    structure MicroTiMLDef : SIG_MICRO_TIML_DEF
    structure Action :
              sig
                  type kdown
                  type tdown
                  type down = kdown * tdown

                  val add_kind : MicroTiMLDef.kind * down -> down
                  val add_type : MicroTiMLDef.cstr * tdown -> tdown

                  val on_va_leaf : MicroTiMLDef.value * down -> MicroTiMLDef.value
                  val on_ty_leaf : MicroTiMLDef.typing * down -> MicroTiMLDef.typing

                  val transform_proping : MicroTiMLDef.proping * kdown -> MicroTiMLDef.proping
                  val transform_kinding : MicroTiMLDef.kinding * kdown -> MicroTiMLDef.kinding
                  val transform_wfkind : MicroTiMLDef.wfkind * kdown -> MicroTiMLDef.wfkind
                  val transform_tyeq : MicroTiMLDef.tyeq * kdown -> MicroTiMLDef.tyeq

                  val transformer_value : (MicroTiMLDef.value * down -> MicroTiMLDef.value) -> MicroTiMLDef.value * down -> MicroTiMLDef.value option
                  val transformer_typing : (MicroTiMLDef.typing * down -> MicroTiMLDef.typing) * (MicroTiMLDef.value * down -> MicroTiMLDef.value) -> MicroTiMLDef.typing * down -> MicroTiMLDef.typing option
              end) : SIG_EXPR_DERIV_GENERIC_ONLY_DOWN_TRANSFORMER =
struct
open List
open Util
infixr 0 $

structure MicroTiMLDef = MicroTiMLDef
open MicroTiMLDef

open Action

structure Transformer = ExprDerivGenericTransformerFun(
    structure MicroTiMLDef = MicroTiMLDef
    structure Action = struct
    type kdown = kdown
    type tdown = tdown
    type down = down
    type up = unit

    val upward_base = ()
    fun combiner ((), ()) = ()

    val add_kind = add_kind
    val add_type = add_type

    val on_va_leaf = (fn e => (e, ())) o on_va_leaf
    val on_ty_leaf = (fn j => (j, ())) o on_ty_leaf

    val transform_proping = (fn pr => (pr, ())) o transform_proping
    val transform_kinding = (fn kd => (kd, ())) o transform_kinding
    val transform_wfkind = (fn wk => (wk, ())) o transform_wfkind
    val transform_tyeq = (fn te => (te, ())) o transform_tyeq

    fun transformer_value on_value =
      let
          val on_value_no_up = fst o on_value
      in
          Option.map (fn va => (va, ())) o Action.transformer_value on_value_no_up
      end

    fun transformer_typing (on_typing, on_value) =
      let
          val on_typing_no_up = fst o on_typing
          val on_value_no_up = fst o on_value
      in
          Option.map (fn ty => (ty, ())) o Action.transformer_typing (on_typing_no_up, on_value_no_up)
      end
    end)

val transform_value = fst o Transformer.transform_value
val transform_typing = fst o Transformer.transform_typing
end

functor DerivTransformersFun(MicroTiMLDef : SIG_MICRO_TIML_DEF) : SIG_DERIV_TRANSFOMRERS =
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

open ShiftCstr
open ShiftExpr
open SubstCstr
open SubstExpr

structure DerivAssembler = DerivAssemblerFun(MicroTiMLDef)
open DerivAssembler

structure ShiftCtx =
struct
structure CstrDerivHelper = CstrDerivGenericOnlyDownTransformerFun(
    structure MicroTiMLDef = MicroTiMLDef
    structure Action =
    struct
    type down = kctx * int

    fun add_kind (_, (kctxd, kdep)) = (kctxd, kdep + 1)

    fun insert_k a b c = (mapi (fn (i, k) => shift_c_k (length c) (b - 1 - i) k) $ take (a, b)) @ c @ drop (a, b)

    fun on_pr_leaf (PrAdmit (kctx, p), (kctxd, kdep)) = PrAdmit (insert_k kctx kdep kctxd, shift_c_p (length kctxd) kdep p)

    fun on_ke_leaf (KdEqKType (kctx, _, _), (kctxd, kdep)) = as_KdEqKType $ insert_k kctx kdep kctxd
      | on_ke_leaf (KdEqBaseSort (kctx, KBaseSort b, _), (kctxd, kdep)) = as_KdEqBaseSort (insert_k kctx kdep kctxd) b
      | on_ke_leaf _ = raise (Impossible "on_ke_leaf")

    fun on_kd_leaf (KdVar (kctx, CVar x, _), (kctxd, kdep)) = as_KdVar (insert_k kctx kdep kctxd) (if x >= kdep then x + (length kctxd) else x)
      | on_kd_leaf (KdConst (kctx, CConst cn, _), (kctxd, kdep)) = as_KdConst (insert_k kctx kdep kctxd) cn
      | on_kd_leaf (KdAdmit (kctx, c, k), (kctxd, kdep)) = KdAdmit (insert_k kctx kdep kctxd, shift_c_c (length kctxd) kdep c, shift_c_k (length kctxd) kdep k)
      | on_kd_leaf _ = raise (Impossible "on_kd_leaf")

    fun on_wk_leaf (WfKdType (kctx, _), (kctxd, kdep)) = as_WfKdType (insert_k kctx kdep kctxd)
      | on_wk_leaf (WfKdBaseSort (kctx, KBaseSort b), (kctxd, kdep)) = as_WfKdBaseSort (insert_k kctx kdep kctxd) b
      | on_wk_leaf (WfKdAdmit (kctx, k), (kctxd, kdep)) = WfKdAdmit (insert_k kctx kdep kctxd, shift_c_k (length kctxd) kdep k)
      | on_wk_leaf _ = raise (Impossible "on_wk_leaf")

    fun on_wp_leaf (WfPropTrue (kctx, _), (kctxd, kdep)) = as_WfPropTrue (insert_k kctx kdep kctxd)
      | on_wp_leaf (WfPropFalse (kctx, _), (kctxd, kdep)) = as_WfPropFalse (insert_k kctx kdep kctxd)
      | on_wp_leaf _ = raise (Impossible "as_wp_leaf")

    fun on_te_leaf (TyEqVar (kctx, CVar x, _), (kctxd, kdep)) = as_TyEqVar (insert_k kctx kdep kctxd) (if x >= kdep then x + (length kctxd) else x)
      | on_te_leaf (TyEqConst (kctx, CConst cn, _), (kctxd, kdep)) = as_TyEqConst (insert_k kctx kdep kctxd) cn
      | on_te_leaf (TyEqBeta (kctx, CApp (CAbs t1, t2), _), (kctxd, kdep)) = as_TyEqBeta (insert_k kctx kdep kctxd) (shift_c_c (length kctxd) (kdep + 1) t1) (shift_c_c (length kctxd) kdep t2)
      | on_te_leaf (TyEqBetaRev (kctx, _, CApp (CAbs t1, t2)), (kctxd, kdep)) = as_TyEqBetaRev (insert_k kctx kdep kctxd) (shift_c_c (length kctxd) (kdep + 1) t1) (shift_c_c (length kctxd) kdep t2)
      | on_te_leaf (TyEqAbs (kctx, CAbs t, _), (kctxd, kdep)) = as_TyEqAbs (insert_k kctx kdep kctxd) (shift_c_c (length kctxd) (kdep + 1) t)
      | on_te_leaf (TyEqTimeAbs (kctx, CTimeAbs i, _), (kctxd, kdep)) = as_TyEqTimeAbs (insert_k kctx kdep kctxd) (shift_c_c (length kctxd) (kdep + 1) i)
      | on_te_leaf (TyEqTimeApp (kctx, CTimeApp (arity, c1, c2), _), (kctxd, kdep)) = as_TyEqTimeApp (insert_k kctx kdep kctxd) arity (shift_c_c (length kctxd) kdep c1) (shift_c_c (length kctxd) kdep c1)
      | on_te_leaf _ = raise (Impossible "on_te_leaf")

    fun transformer_proping _ = NONE
    fun transformer_kdeq _ _ = NONE
    fun transformer_kinding _ _ = NONE
    fun transformer_wfkind _ _ = NONE
    fun transformer_wfprop _ _ = NONE
    fun transformer_tyeq _ _ = NONE
    end)

structure ExprDerivHelper = ExprDerivGenericOnlyDownTransformerFun(
    structure MicroTiMLDef = MicroTiMLDef
    structure Action =
    struct
    type kdown = kctx * int
    type tdown = tctx * int
    type down =  kdown * tdown

    fun add_kind (_, ((kctxd, kdep), (tctxd, tdep))) = ((kctxd, kdep + 1), (map shift0_c_c tctxd, tdep))
    fun add_type (_, (tctxd, tdep)) = (tctxd, tdep + 1)

    fun insert_k a b c = (mapi (fn (i, k) => shift_c_k (length c) (b - 1 - i) k) $ take (a, b)) @ c @ drop (a, b)
    fun insert_t a b c = take (a, b) @ c @ drop (a, b)

    fun on_va_leaf (VConst (EConst cn), _) = as_VConst cn
      | on_va_leaf (VAbs (EAbs e), ((kctxd, kdep), (tctxd, tdep))) = as_VAbs (shift_e_e (length tctxd) (tdep + 1) $ shift_c_e (length kctxd) kdep e)
      | on_va_leaf (VAbsC (EAbsC e), ((kctxd, kdep), (tctxd, tdep))) = as_VAbsC (shift_e_e (length tctxd) tdep $ shift_c_e (length kctxd) (kdep + 1) e)
      | on_va_leaf _ = raise (Impossible "as_va_leaf")

    fun on_ty_leaf (TyVar ((kctx, tctx), EVar x, _, _), ((kctxd, kdep), (tctxd, tdep))) = as_TyVar (insert_k kctx kdep kctxd, insert_t (map (shift_c_c (length kctxd) kdep) tctx) tdep tctxd) (if x >= tdep then x + (length tctxd) else x)
      | on_ty_leaf (TyConst ((kctx, tctx), EConst cn, _, _), ((kctxd, kdep), (tctxd, tdep))) = as_TyConst (insert_k kctx kdep kctxd, insert_t (map (shift_c_c (length kctxd) kdep) tctx) tdep tctxd) cn
      | on_ty_leaf (TyFix (((kctx, tctx), EFix _, _, _), kd, ty), ((kctxd, kdep), (tctxd, tdep))) = as_TyFix (insert_k kctx kdep kctxd, insert_t (map (shift_c_c (length kctxd) kdep) tctx) tdep tctxd) kd ty
      | on_ty_leaf _ = raise (Impossible "as_ty_leaf")

    val transform_proping = CstrDerivHelper.transform_proping
    val transform_kinding = CstrDerivHelper.transform_kinding
    val transform_wfkind = CstrDerivHelper.transform_wfkind
    val transform_tyeq = CstrDerivHelper.transform_tyeq

    fun transformer_value _ _ = NONE
    fun transformer_typing _ _ = NONE
    end)

fun shift_ctx_ty ((kctxd, kdep), (tctxd, tdep)) ty = ExprDerivHelper.transform_typing (ty, ((kctxd, kdep), (tctxd, tdep)))
fun shift_ctx_va ((kctxd, kdep), (tctxd, tdep)) va = ExprDerivHelper.transform_value (va, ((kctxd, kdep), (tctxd, tdep)))
fun shift_ctx_kd (kctxd, kdep) kd = CstrDerivHelper.transform_kinding (kd, (kctxd, kdep))
fun shift_ctx_te (kctxd, kdep) te = CstrDerivHelper.transform_tyeq (te, (kctxd, kdep))
fun shift_ctx_pr (kctxd, kdep) pr = CstrDerivHelper.transform_proping (pr, (kctxd, kdep))
fun shift_ctx_wk (kctxd, kdep) wk = CstrDerivHelper.transform_wfkind (wk, (kctxd, kdep))
fun shift_ctx_ke (kctxd, kdep) ke = CstrDerivHelper.transform_kdeq (ke, (kctxd, kdep))

fun shift0_ctx_ty (kctxd, tctxd) = shift_ctx_ty ((kctxd, 0), (tctxd, 0))
fun shift0_ctx_va (kctxd, tctxd) = shift_ctx_va ((kctxd, 0), (tctxd, 0))
fun shift0_ctx_kd kctxd = shift_ctx_kd (kctxd, 0)
fun shift0_ctx_te kctxd = shift_ctx_te (kctxd, 0)
fun shift0_ctx_pr kctxd = shift_ctx_pr (kctxd, 0)
fun shift0_ctx_wk kctxd = shift_ctx_wk (kctxd, 0)
fun shift0_ctx_ke kctxd = shift_ctx_ke (kctxd, 0)
end

structure ChangeCtx =
struct
structure CstrDerivHelper = CstrDerivGenericOnlyDownTransformerFun(
    structure MicroTiMLDef = MicroTiMLDef
    structure Action =
    struct
    type down = kctx

    fun add_kind (k, kctx) = k :: kctx

    fun on_pr_leaf (PrAdmit (_, p), kctx) = PrAdmit (kctx, p)

    fun on_ke_leaf (KdEqKType (_, _, _), kctx) = as_KdEqKType kctx
      | on_ke_leaf (KdEqBaseSort (_, KBaseSort b, _), kctx) = as_KdEqBaseSort kctx b
      | on_ke_leaf _ = raise (Impossible "on_ke_leaf")

    fun on_kd_leaf (KdVar (_, CVar x, _), kctx) = as_KdVar kctx x
      | on_kd_leaf (KdConst (_, CConst cn, _), kctx) = as_KdConst kctx cn
      | on_kd_leaf (KdAdmit (_, c, k), kctx) = KdAdmit (kctx, c, k)
      | on_kd_leaf _ = raise (Impossible "on_kd_leaf")

    fun on_wk_leaf (WfKdType (_, _), kctx) = as_WfKdType kctx
      | on_wk_leaf (WfKdBaseSort (_, KBaseSort b), kctx) = as_WfKdBaseSort kctx b
      | on_wk_leaf (WfKdAdmit (_, k), kctx) = WfKdAdmit (kctx, k)
      | on_wk_leaf _ = raise (Impossible "on_wk_leaf")

    fun on_wp_leaf (WfPropTrue (_, _), kctx) = as_WfPropTrue kctx
      | on_wp_leaf (WfPropFalse (_, _), kctx) = as_WfPropFalse kctx
      | on_wp_leaf _ = raise (Impossible "on_wp_leaf")

    fun on_te_leaf (TyEqVar (_, CVar x, _), kctx) = as_TyEqVar kctx x
      | on_te_leaf (TyEqConst (_, CConst cn, _), kctx) = as_TyEqConst kctx cn
      | on_te_leaf (TyEqBeta (_, CApp (CAbs t1, t2), _), kctx) = as_TyEqBeta kctx t1 t2
      | on_te_leaf (TyEqBetaRev (_, _, CApp (CAbs t1, t2)), kctx) = as_TyEqBetaRev kctx t1 t2
      | on_te_leaf (TyEqAbs (_, CAbs t, _), kctx) = as_TyEqAbs kctx t
      | on_te_leaf (TyEqTimeAbs (_, CTimeAbs i, _), kctx) = as_TyEqTimeAbs kctx i
      | on_te_leaf (TyEqTimeApp (_, CTimeApp (arity, c1, c2), _), kctx) = as_TyEqTimeApp kctx arity c1 c2
      | on_te_leaf _ = raise (Impossible "on_te_leaf")

    fun transformer_proping _ = NONE
    fun transformer_kdeq _ _ = NONE
    fun transformer_kinding _ _ = NONE
    fun transformer_wfkind _ _ = NONE
    fun transformer_wfprop _ _ = NONE
    fun transformer_tyeq _ _ = NONE
    end)

structure ExprDerivHelper = ExprDerivGenericOnlyDownTransformerFun(
    structure MicroTiMLDef = MicroTiMLDef
    structure Action =
    struct
    type kdown = kctx
    type tdown = tctx
    type down = kdown * tdown

    fun add_kind (k, (kctx, tctx)) = (k :: kctx, map shift0_c_c tctx)
    fun add_type (t, tctx) = t :: tctx

    fun on_va_leaf (e, _) = e

    fun on_ty_leaf (TyVar ((_, _), EVar x, _, _), (kctx, tctx)) = as_TyVar (kctx, tctx) x
      | on_ty_leaf (TyConst ((_, _), EConst cn, _, _), (kctx, tctx)) = as_TyConst (kctx, tctx) cn
      | on_ty_leaf (TyFix (((_, _), EFix _, _, _), kd, ty), (kctx, tctx)) = as_TyFix (kctx, tctx) kd ty
      | on_ty_leaf _ = raise (Impossible "on_ty_leaf")

    val transform_proping = CstrDerivHelper.transform_proping
    val transform_kinding = CstrDerivHelper.transform_kinding
    val transform_wfkind = CstrDerivHelper.transform_wfkind
    val transform_tyeq = CstrDerivHelper.transform_tyeq

    fun transformer_value _ _ = NONE
    fun transformer_typing _ _ = NONE
    end)

fun change_ctx_wk kctx wk = CstrDerivHelper.transform_wfkind (wk, kctx)
fun change_ctx_kd kctx kd = CstrDerivHelper.transform_kinding (kd, kctx)
fun change_ctx_ty ctx ty = ExprDerivHelper.transform_typing (ty, ctx)
fun change_ctx_va ctx va = ExprDerivHelper.transform_value (va, ctx)
fun change_ctx_wp kctx wp = CstrDerivHelper.transform_wfprop (wp, kctx)
fun change_ctx_ke kctx ke = CstrDerivHelper.transform_kdeq (ke, kctx)
fun change_ctx_pr kctx pr = CstrDerivHelper.transform_proping (pr, kctx)
fun change_ctx_te kctx te = CstrDerivHelper.transform_tyeq (te, kctx)
end

structure DerivFVCstr =
struct
open FVUtil

structure CstrDerivHelper = CstrDerivGenericTransformerFun(
    structure MicroTiMLDef = MicroTiMLDef
    structure Action =
    struct
    type down = int
    type up = int list

    val upward_base = []
    val combiner = unique_merge

    fun add_kind (_, dep) = dep + 1

    fun on_pr_leaf (pr as PrAdmit (kctx, p), dep) = (pr, FVCstr.free_vars_c_p dep p)

    fun on_ke_leaf (ke as KdEqKType (_, _, _), _) = (ke, [])
      | on_ke_leaf (ke as KdEqBaseSort (_, _, _), _) = (ke, [])
      | on_ke_leaf _ = raise (Impossible "on_ke_leaf")

    fun on_kd_leaf (kd as KdVar (_, CVar x, _), dep) = (kd, if x >= dep then [x - dep] else [])
      | on_kd_leaf (kd as KdConst (_, _, _), _) = (kd, [])
      | on_kd_leaf (kd as KdAdmit (kctx, c, k), dep) = (kd, unique_merge (FVCstr.free_vars_c_c dep c, FVCstr.free_vars_c_k dep k))
      | on_kd_leaf _ = raise (Impossible "on_kd_leaf")

    fun on_wk_leaf (wk as WfKdType (_, _), _) = (wk, [])
      | on_wk_leaf (wk as WfKdBaseSort (_, _), _) = (wk, [])
      | on_wk_leaf _ = raise (Impossible "on_wk_leaf")

    fun on_wp_leaf (wp as WfPropTrue (_, _), _) = (wp, [])
      | on_wp_leaf (wp as WfPropFalse (_, _), _) = (wp, [])
      | on_wp_leaf _ = raise (Impossible "on_wp_leaf")

    fun on_te_leaf (te as TyEqVar (_, CVar x, _), dep) = (te, if x >= dep then [x - dep] else [])
      | on_te_leaf (te as TyEqConst (_, _, _), _) = (te, [])
      | on_te_leaf (te as TyEqBeta (_, CApp (CAbs t1, t2), _), dep) = (te, unique_merge (FVCstr.free_vars_c_c (dep + 1) t1, FVCstr.free_vars_c_c dep t2))
      | on_te_leaf (te as TyEqBetaRev (_, _, CApp (CAbs t1, t2)), dep) = (te, unique_merge (FVCstr.free_vars_c_c (dep + 1) t1, FVCstr.free_vars_c_c dep t2))
      | on_te_leaf (te as TyEqAbs (_, CAbs t, _), dep) = (te, FVCstr.free_vars_c_c (dep + 1) t)
      | on_te_leaf (te as TyEqTimeAbs (_, CTimeAbs i, _), dep) = (te, FVCstr.free_vars_c_c (dep + 1) i)
      | on_te_leaf (te as TyEqTimeApp (_, CTimeApp (arity, c1, c2), _), dep) = (te, unique_merge (FVCstr.free_vars_c_c dep c1, FVCstr.free_vars_c_c dep c2))
      | on_te_leaf _ = raise (Impossible "on_te_leaf")

    fun transformer_proping _ = NONE
    fun transformer_kdeq _ _ = NONE
    fun transformer_kinding _ _ = NONE
    fun transformer_wfkind _ _ = NONE
    fun transformer_wfprop _ _ = NONE
    fun transformer_tyeq _ _ = NONE
    end)

structure ExprDerivHelper = ExprDerivGenericTransformerFun(
    structure MicroTiMLDef = MicroTiMLDef
    structure Action =
    struct
    type kdown = int
    type tdown = unit
    type down = kdown * tdown
    type up = int list

    val upward_base = []
    val combiner = unique_merge

    fun add_kind (_, (dep, ())) = (dep + 1, ())
    fun add_type (_, ()) = ()

    fun on_va_leaf (va as VConst _, _) = (va, [])
      | on_va_leaf (va as VAbs (EAbs e), (dep, ())) = (va, FVCstr.free_vars_c_e dep e)
      | on_va_leaf (va as VAbsC (EAbsC e), (dep, ())) = (va, FVCstr.free_vars_c_e (dep + 1) e)
      | on_va_leaf _ = raise (Impossible "on_va_leaf")

    fun on_ty_leaf (ty as TyVar (_, _, t, i), (dep, ())) = (ty, unique_merge (FVCstr.free_vars_c_c dep t, FVCstr.free_vars_c_c dep i))
      | on_ty_leaf (ty as TyConst (_, _, t, i), (dep, ())) = (ty, unique_merge (FVCstr.free_vars_c_c dep t, FVCstr.free_vars_c_c dep i))
      | on_ty_leaf (ty as TyFix ((_, _, t, i), _, _), (dep, ())) = (ty, unique_merge (FVCstr.free_vars_c_c dep t, FVCstr.free_vars_c_c dep i))
      | on_ty_leaf _ = raise (Impossible "on_ty_leaf")

    val transform_proping = CstrDerivHelper.transform_proping
    val transform_kinding = CstrDerivHelper.transform_kinding
    val transform_wfkind = CstrDerivHelper.transform_wfkind
    val transform_tyeq = CstrDerivHelper.transform_tyeq

    fun transformer_value _ _ = NONE
    fun transformer_typing _ _ = NONE
    end)

fun free_vars_c_ty d ty = #2 (ExprDerivHelper.transform_typing (ty, (d, ())))

val free_vars0_c_ty = free_vars_c_ty 0
end

structure DerivFVExpr =
struct
open FVUtil

structure ExprDerivHelper = ExprDerivGenericTransformerFun(
    structure MicroTiMLDef = MicroTiMLDef
    structure Action =
    struct
    type kdown = unit
    type tdown = int
    type down = kdown * tdown
    type up = int list

    val upward_base = []
    val combiner = unique_merge

    fun add_kind (_, ((), dep)) = ((), dep)
    fun add_type (_, dep) = dep + 1

    fun on_va_leaf (va as VConst _, _) = (va, [])
      | on_va_leaf (va as VAbs (EAbs e), ((), dep)) = (va, FVExpr.free_vars_e_e (dep + 1) e)
      | on_va_leaf (va as VAbsC (EAbsC e), ((), dep)) = (va, FVExpr.free_vars_e_e dep e)
      | on_va_leaf _ = raise (Impossible "on_va_leaf")

    fun on_ty_leaf (ty as TyVar (ctx, EVar x, _, _), ((), dep)) = (ty, if x >= dep then [x - dep] else [])
      | on_ty_leaf (ty as TyConst _, _) = (ty, [])
      | on_ty_leaf (ty as TyFix _, _) = (ty, [])
      | on_ty_leaf _ = raise (Impossible "on_ty_leaf")

    fun transform_proping (pr, kdown) = (pr, [])
    fun transform_kinding (kd, kdown) = (kd, [])
    fun transform_wfkind (wk, kdown) = (wk, [])
    fun transform_tyeq (te, kdown) = (te, [])

    fun transformer_value _ _ = NONE
    fun transformer_typing _ _ = NONE
    end)

fun free_vars_e_ty d ty = #2 (ExprDerivHelper.transform_typing (ty, ((), d)))

val free_vars0_e_ty = free_vars_e_ty 0
end

structure DerivSubstTyping =
struct
structure ExprDerivHelper = ExprDerivGenericOnlyDownTransformerFun(
    structure MicroTiMLDef = MicroTiMLDef
    structure Action =
    struct
    type kdown = unit
    type tdown = typing * int
    type down = kdown * tdown

    fun add_kind (k, ((), (to, who))) = ((), (ShiftCtx.shift0_ctx_ty ([k], []) to, who))
    fun add_type (t, (to, who)) = (ShiftCtx.shift0_ctx_ty ([], [t]) to, who + 1)

    fun on_va_leaf (va, _) = va

    fun on_ty_leaf (TyVar ((kctx, tctx), EVar x, _, _), ((), (to, who))) =
      if x = who then
          to
      else
          if x < who then
              as_TyVar (kctx, take (tctx, who) @ drop (tctx, who + 1)) x
          else
              as_TyVar (kctx, take (tctx, who) @ drop (tctx, who + 1)) (x - 1)
      | on_ty_leaf (TyConst ((kctx, tctx), EConst cn, _, _), ((), (to, who))) = as_TyConst (kctx, take (tctx, who) @ drop (tctx, who + 1)) cn
      | on_ty_leaf (TyFix (((kctx, tctx), _, _, _), kd, ty), ((), (to, who))) = as_TyFix (kctx, take (tctx, who) @ drop (tctx, who + 1)) kd ty
      | on_ty_leaf _ = raise (Impossible "on_ty_leaf")

    fun transform_proping (pr, kdown) = pr
    fun transform_kinding (kd, kdown) = kd
    fun transform_wfkind (wk, kdown) = wk
    fun transform_tyeq (te, kdown) = te

    fun transformer_value _ _ = NONE
    fun transformer_typing _ _ = NONE
    end)

fun subst_ty_ty to who ty = ExprDerivHelper.transform_typing (ty, ((), (to, who)))

fun subst0_ty_ty to = subst_ty_ty to 0
end

(* structure DerivDirectSubstCstr = *)
(* struct *)
(* open DirectSubstCstr *)

(* structure CstrDerivHelper = CstrDerivGenericOnlyDownTransformerFun( *)
(*     structure MicroTiMLDef = MicroTiMLDef *)
(*     structure Action = *)
(*     struct *)
(*     type down = cstr * int *)

(*     fun add_kind (_, (to, who)) = (shift0_c_c to, who + 1) *)

(*     fun on_pr_leaf ((kctx, p), (to, who)) = (kctx, dsubst_c_p to who p) *)
(*     fun on_ke_leaf ((kctx, k1, k2), (to, who)) = (kctx, dsubst_c_k to who k1, dsubst_c_k to who k2) *)
(*     fun on_kd_leaf ((kctx, c, k), (to, who)) = (kctx, dsubst_c_c to who c, dsubst_c_k to who k) *)
(*     fun on_wk_leaf ((kctx, k), (to, who)) = (kctx, dsubst_c_k to who k) *)
(*     fun on_wp_leaf ((kctx, p), (to, who)) = (kctx, dsubst_c_p to who p) *)
(*     fun on_te_leaf ((kctx, t1, t2), (to, who)) = (kctx, dsubst_c_c to who t1, dsubst_c_c to who t2) *)

(*     fun transformer_proping _ = NONE *)
(*     fun transformer_kdeq _ _ = NONE *)
(*     fun transformer_kinding _ _ = NONE *)
(*     fun transformer_wfkind _ _ = NONE *)
(*     fun transformer_wfprop _ _ = NONE *)
(*     fun transformer_tyeq _ _ = NONE *)
(*     end) *)

(* structure ExprDerivHelper = ExprDerivGenericOnlyDownTransformerFun( *)
(*     structure MicroTiMLDef = MicroTiMLDef *)
(*     structure Action = *)
(*     struct *)
(*     type kdown = cstr * int *)
(*     type tdown = unit *)
(*     type down = kdown * tdown *)

(*     fun add_kind (_, ((to, who), ())) = ((shift0_c_c to, who + 1), ()) *)
(*     fun add_type (_, ()) = () *)

(*     fun on_ty_leaf ((ctx, e, t, i), ((to, who), ())) = (ctx, dsubst_c_e to who e, dsubst_c_c to who t, dsubst_c_c to who i) *)

(*     val transform_proping = CstrDerivHelper.transform_proping *)
(*     val transform_kinding = CstrDerivHelper.transform_kinding *)
(*     val transform_wfkind = CstrDerivHelper.transform_wfkind *)
(*     val transform_tyeq = CstrDerivHelper.transform_tyeq *)

(*     fun transformer_typing _ _ = NONE *)
(*     end) *)

(* fun dsubst_c_ty to who ty = ExprDerivHelper.transform_typing (ty, ((to, who), ())) *)
(* fun dsubst_c_kd to who kd = CstrDerivHelper.transform_kinding (kd, (to, who)) *)
(* fun dsubst_c_wk to who wk = CstrDerivHelper.transform_wfkind (wk, (to, who)) *)

(* fun dsubst0_c_ty to = dsubst_c_ty to 0 *)
(* fun dsubst0_c_kd to = dsubst_c_kd to 0 *)
(* fun dsubst0_c_wk to = dsubst_c_wk to 0 *)
(* end *)

(* structure DerivDirectSubstExpr = *)
(* struct *)
(* open DirectSubstExpr *)

(* structure ExprDerivHelper = ExprDerivGenericOnlyDownTransformerFun( *)
(*     structure MicroTiMLDef = MicroTiMLDef *)
(*     structure Action = *)
(*     struct *)
(*     type kdown = unit *)
(*     type tdown = expr * int *)
(*     type down = kdown * tdown *)

(*     fun add_kind (_, ((), (to, who))) = ((), (shift0_c_e to, who)) *)
(*     fun add_type (_, (to, who)) = (shift0_e_e to, who + 1) *)

(*     fun on_ty_leaf ((ctx, e, t, i), ((), (to, who))) = (ctx, dsubst_e_e to who e, t, i) *)

(*     fun transform_proping (pr, kdown) = pr *)
(*     fun transform_kinding (kd, kdown) = kd *)
(*     fun transform_wfkind (wk, kdown) = wk *)
(*     fun transform_tyeq (te, kdown) = te *)

(*     fun transformer_typing _ _ = NONE *)
(*     end) *)

(* fun dsubst_e_ty to who ty = ExprDerivHelper.transform_typing (ty, ((), (to, who))) *)

(* fun dsubst0_e_ty to = dsubst_e_ty to 0 *)
(* end *)
end
