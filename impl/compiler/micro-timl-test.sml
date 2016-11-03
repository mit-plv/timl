structure MicroTiMLTest : SIG_MICRO_TIML_TEST =
struct
open List
open Util
infixr 0 $

structure NatTime =
struct
open Util

type time_type = int

val Time0 = 0
val Time1 = 1

val str_time = str_int
end

structure IntNat =
struct
open Util

type nat_type = int

fun from_int i = i
val str_nat = str_int
end

structure MicroTiMLDef = MicroTiMLDefFun(
    structure Time = NatTime
    structure Nat = IntNat)

open MicroTiMLDef
structure MicroTiMLUtil = MicroTiMLUtilFun(MicroTiMLDef)
open MicroTiMLUtil
structure AstTransformers = AstTransformersFun(MicroTiMLDef)
open AstTransformers
structure DerivTransformers = DerivTransformersFun(MicroTiMLDef)
open DerivTransformers
structure DerivChecker = DerivCheckerFun(MicroTiMLDef)
open DerivChecker
(*structure MicroTiMLHoistedDef = MicroTiMLHoistedDefFun(MicroTiMLDef)
open MicroTiMLHoistedDef
structure HoistedDerivChecker = HoistedDerivCheckerFun(MicroTiMLHoistedDef)
open HoistedDerivChecker*)

open DerivAssembler
open ShiftCtx
open PlainPrinter
open ShiftCstr
open ShiftExpr
open SubstCstr
open SubstExpr

fun TySub ((ctx, e, t, i), ty, te, pr) =
  let
      val jty = extract_judge_typing ty
      val ty1 = TySubTy ((ctx, e, t, #4 jty), ty, te)
      val ty2 = TySubTi ((ctx, e, t, i), ty1, pr)
  in
      ty2
  end

fun gen_kdeq_refl kctx k =
  case k of
      KType => KdEqKType (kctx, k, k)
    | KArrow (k1, k2) =>
      let
          val ke1 = gen_kdeq_refl kctx k1
          val ke2 = gen_kdeq_refl kctx k2
      in
          KdEqKArrow (as_KdEqKArrow ke1 ke2, ke1, ke2)
      end
    | KBaseSort s => KdEqBaseSort (kctx, k, k)
    | KSubset (k, p) =>
      let
          val ke = gen_kdeq_refl kctx k
          val pr = PrAdmit (k :: kctx, PIff (p, p))
      in
          KdEqSubset (as_KdEqKSubset ke pr, ke, pr)
      end

fun gen_tyeq_refl kctx t =
  case t of
      CVar x => TyEqVar (kctx, t, t)
    | CConst cn => TyEqConst (kctx, t, t)
    | CBinOp (opr, t1, t2) =>
      let
          val te1 = gen_tyeq_refl kctx t1
          val te2 = gen_tyeq_refl kctx t2
      in
          TyEqBinOp (as_TyEqBinOp opr te1 te2, te1, te2)
      end
    | CIte (i1, i2, i3) =>
      let
          val te1 = gen_tyeq_refl kctx i1
          val te2 = gen_tyeq_refl kctx i2
          val te3 = gen_tyeq_refl kctx i3
      in
          TyEqIte (as_TyEqIte te1 te2 te3, te1, te2, te3)
      end
    | CTimeAbs c => TyEqTimeAbs (kctx, t, t)
    | CTimeApp (arity, c1, c2) =>
      let
          val te1 = gen_tyeq_refl kctx c1
          val te2 = gen_tyeq_refl kctx c2
      in
          TyEqTimeApp (as_TyEqTimeApp arity te1 te2, te1, te2)
      end
    | CArrow (t1, i, t2) =>
      let
          val te1 = gen_tyeq_refl kctx t1
          val pr = PrAdmit (kctx, TEq (i, i))
          val te2 = gen_tyeq_refl kctx t2
      in
          TyEqArrow (as_TyEqArrow te1 pr te2, te1, pr, te2)
      end
    | CAbs c => TyEqAbs (kctx, t, t)
    | CApp (c1, c2) =>
      let
          val te1 = gen_tyeq_refl kctx c1
          val te2 = gen_tyeq_refl kctx c2
      in
          TyEqApp (as_TyEqApp te1 te2, te1, te2)
      end
    | CQuan (q, k, c) =>
      let
          val ke = gen_kdeq_refl kctx k
          val te = gen_tyeq_refl (k :: kctx) c
      in
          TyEqQuan (as_TyEqQuan q ke te, ke, te)
      end
    | CRec (k, c) =>
      let
          val ke = gen_kdeq_refl kctx k
          val te = gen_tyeq_refl (k :: kctx) c
      in
          TyEqRec (as_TyEqRec ke te, ke, te)
      end
    | CRef c =>
      let
          val te = gen_tyeq_refl kctx c
      in
          TyEqRef (as_TyEqRef te, te)
      end
    | CUnOp (opr, c) =>
      let
          val te = gen_tyeq_refl kctx c
      in
          TyEqUnOp (as_TyEqUnOp opr te, te)
      end

(*fun test_cps () =
  let
      val tctx = [CArrow (CInt, T1, CArrow (CInt, T1, CInt)), CArrow (CInt, T1, CInt), CInt, CArrow (CInt, T1, CInt), CArrow (CInt, T1, CInt), CInt, CArrow (CInt, T0, CTypeUnit)]
      val tctx = List.map (CPS.transform_type) tctx
      val ctx = ([], tctx)
      val d1 = TyVar (ctx, EVar 1, CArrow (CInt, T1, CInt), T0)
      val d2 = TyVar (ctx, EVar 2, CInt, T0)
      val d3 = TyApp (as_TyApp d1 d2, d1, d2)
      val d4 = TyVar (ctx, EVar 0, CArrow (CInt, T1, CArrow (CInt, T1, CInt)), T0)
      val d5 = TyApp (as_TyApp d4 d3, d4, d3)
      val d6 = TyVar (ctx, EVar 4, CArrow (CInt, T1, CInt), T0)
      val d7 = TyVar (ctx, EVar 5, CInt, T0)
      val d8 = TyApp (as_TyApp d6 d7, d6, d7)
      val d9 = TyVar (ctx, EVar 3, CArrow (CInt, T1, CInt), T0)
      val d10 = TyApp (as_TyApp d9 d8, d9, d8)
      val d11 = TyApp (as_TyApp d5 d10, d5, d10)
      val cps_ty = CPS.cps_deriv d11
      val () = println $ str_expr $ #2 (extract_judge_typing cps_ty)
      val () = check_typing cps_ty
      val wrap_ty = WrapLambda.wrap_lambda_deriv cps_ty
      val () = println $ str_expr $ #2 (extract_judge_typing wrap_ty)
      val () = check_typing wrap_ty
  in
      println ""
  end*)

fun test_absc_appc () =
  let
      val e1 = EInl ETT
      val ct1 = ([KType], [])
      val i1 = T0
      val t1 = CSum (CTypeUnit, CVar 0)
      val d1 = TyInj ((ct1, e1, t1, i1), TyConst (ct1, ETT, CTypeUnit, T0), KdVar (fst ct1, CVar 0, KType))
      val () = check_typing d1
      val e2 = EAbsC e1
      val ct2 = ([], [])
      val i2 = T0
      val t2 = CForall (KType, CSum (CTypeUnit, CVar 0))
      val d2 = TyAbsC ((ct2, e2, t2, i2), WfKdType (fst ct2, KType), d1)
      val () = check_typing d2
      val e3 = EAppC (e2, CInt)
      val ct3 = ct2
      val i3 = T0
      val t3 = CSum (CTypeUnit, CInt)
      val d3 = TyAppC ((ct3, e3, t3, i3), d2, KdConst (fst ct3, CInt, KType))
      val () = check_typing d3
      val cps_ty = CPS.cps_deriv d3
      val () = println $ str_expr $ #2 (extract_judge_typing cps_ty)
      val () = check_typing cps_ty
  in
      println ""
  end

fun test_abs_app () =
  let
      val e1 = EAbs (EVar 0)
      val ct1 = ([], [])
      val i1 = T0
      val t1 = CArrow (CInt, T0, CInt)
      val d1 = TyAbs ((ct1, e1, t1, i1), KdConst ([], CInt, KType), TyVar (([], [CInt]), EVar 0, CInt, T0))
      val () = check_typing d1
      val d2 = TyApp (as_TyApp d1 (TyConst (([], []), EConst (ECInt 2), CInt, T0)), d1, TyConst (([], []), EConst (ECInt 2), CInt, T0))
      val () = check_typing d2
      val cps_ty = CPS.cps_deriv d2
      val () = println $ str_expr $ #2 (extract_judge_typing cps_ty)
      val () = check_typing cps_ty
      (*val wrap_ty = WrapLambda.wrap_lambda_deriv cps_ty
      val () = println $ str_expr $ #2 (extract_judge_typing wrap_ty)
      val () = check_typing wrap_ty
      val clo_ty = CloConv.clo_conv_deriv wrap_ty
      val () = println $ str_expr $ #2 (extract_judge_typing clo_ty)
      val () = check_typing clo_ty*)
      (*val hoisted_ty = hoist_deriv clo_ty
      val () = print $ str_program $ #1 (extract_judge_ptyping hoisted_ty)
      val () = HoistedDerivChecker.check_program hoisted_ty*)
  in
      println ""
  end

fun test_currying () =
  let
      val e1 = EAbs (EAbs (EPair (EVar 1, EVar 0)))
      val ct1 = ([], [])
      val i1 = T0
      val t1 = CArrow (CInt, T0, CArrow (CInt, Tadd (T0, T0), CProd (CInt, CInt)))
      val d1 = TyAbs ((ct1, e1, t1, i1), KdConst ([], CInt, KType), TyAbs ((([], [CInt]), EAbs (EPair (EVar 1, EVar 0)), CArrow (CInt, Tadd (T0, T0), CProd (CInt, CInt)), T0), KdConst ([], CInt, KType), TyPair ((([], [CInt, CInt]), EPair (EVar 1, EVar 0), CProd (CInt, CInt), Tadd (T0, T0)), TyVar (([], [CInt, CInt]), EVar 1, CInt, T0), TyVar (([], [CInt, CInt]), EVar 0, CInt, T0))))
      val () = check_typing d1
      val d2 = TyApp (as_TyApp d1 (TyConst (([], []), EConst (ECInt 2), CInt, T0)), d1, TyConst (([], []), EConst (ECInt 2), CInt, T0))
      val () = check_typing d2
      val d3 = TyApp (as_TyApp d2 (TyConst (([], []), EConst (ECInt 6), CInt, T0)), d2, TyConst (([], []), EConst (ECInt 6), CInt, T0))
      val () = check_typing d3
      val cps_ty = CPS.cps_deriv d3
      val () = println $ str_expr $ #2 (extract_judge_typing cps_ty)
      val () = check_typing cps_ty
      (*val wrap_ty = WrapLambda.wrap_lambda_deriv cps_ty
      val () = println $ str_expr $ #2 (extract_judge_typing wrap_ty)
      val () = check_typing wrap_ty
      val clo_ty = CloConv.clo_conv_deriv wrap_ty
      val () = println $ str_expr $ #2 (extract_judge_typing clo_ty)
      val () = check_typing clo_ty*)
      (*val hoisted_ty = hoist_deriv clo_ty
      val () = print $ str_program $ #1 (extract_judge_ptyping hoisted_ty)
      val () = HoistedDerivChecker.check_program hoisted_ty*)
  (*val anf_ty = fst $ ANF.normalize_deriv clo_conv_deriv
      val janf_ty = extract_judge_typing anf_ty
      val () = println $ str_expr $ #2 janf_ty
      val () = check_typing anf_ty
      val hoisted_ty = Hoist.hoist anf_ty
      val () = HoistedDerivChecker.check_program hoisted_ty*)
  in
      println ""
  end

fun test_concat () =
  let
      fun get_nat i = CNat (Nat.from_int i)
      val c1 = CExists (KSubset (KUnit, PBinPred (PBNatEq, CVar 1, get_nat 0)), CTypeUnit)
      val ct1 = [KNat, KType, KArrow (KType, KArrow (KNat, KType))]
      val d1 = KdQuan ((ct1, c1, KType), WfKdSubset ((ct1, KSubset (KUnit, PBinPred (PBNatEq, CVar 1, get_nat 0))), WfKdBaseSort (ct1, KUnit), WfPropBinPred ((KUnit :: ct1, PBinPred (PBNatEq, CVar 1, get_nat 0)), KdVar (KUnit :: ct1, CVar 1, KNat), KdConst (KUnit :: ct1, get_nat 0, KNat))), KdConst ((KSubset (KUnit, PBinPred (PBNatEq, CVar 1, get_nat 0))) :: ct1, CTypeUnit, KType))
      val () = check_kinding d1
      val c2 = CApps (CVar 4) [CVar 3, CVar 1]
      val ct2 = KSubset (KUnit, PBinPred (PBNatEq, CVar 2, CBinOp (CBNatAdd, CVar 1, get_nat 1))) :: KNat :: ct1
      val d2 = KdApp ((ct2, c2, KType), KdApp ((ct2, CApp (CVar 4, CVar 3), KArrow (KNat, KType)), KdVar (ct2, CVar 4, shift_c_k 5 0 (nth (ct2, 4))), KdVar (ct2, CVar 3, shift_c_k 4 0 (nth (ct2, 3)))), KdVar (ct2, CVar 1, shift_c_k 2 0 (nth (ct2, 1))))
      val () = check_kinding d2
      val c3 = CProd (CVar 3, c2)
      val ct3 = ct2
      val d3 = KdBinOp ((ct3, c3, KType), KdVar (ct3, CVar 3, shift_c_k 4 0 (nth (ct3, 3))), d2)
      val () = check_kinding d3
      val c4 = CExists (KSubset (KUnit, PBinPred (PBNatEq, CVar 2, CBinOp (CBNatAdd, CVar 1, get_nat 1))), c3)
      val ct4 = tl ct3
      val d4 = KdQuan ((ct4, c4, KType), WfKdSubset ((ct4, KSubset (KUnit, PBinPred (PBNatEq, CVar 2, CBinOp (CBNatAdd, CVar 1, get_nat 1)))), WfKdBaseSort (ct4, KUnit), WfPropBinPred ((KUnit :: ct4, PBinPred (PBNatEq, CVar 2, CBinOp (CBNatAdd, CVar 1, get_nat 1))), KdVar (KUnit :: ct4, CVar 2, KNat), KdBinOp ((KUnit :: ct4, CBinOp (CBNatAdd, CVar 1, get_nat 1), KNat), KdVar (KUnit :: ct4, CVar 1, KNat), KdConst (KUnit :: ct4, get_nat 1, KNat)))), d3)
      val () = check_kinding d4
      val c5 = CExists (KNat, c4)
      val ct5 = tl ct4
      val d5 = KdQuan ((ct5, c5, KType), WfKdBaseSort (ct5, KNat), d4)
      val () = check_kinding d5
      val c6 = CSum (c1, c5)
      val ct6 = ct5
      val d6 = KdBinOp ((ct6, c6, KType), d1, d5)
      val () = check_kinding d6
      val c7 = CAbs c6
      val ct7 = tl ct6
      val d7 = KdAbs ((ct7, c7, KArrow (KNat, KType)), WfKdBaseSort (ct7, KNat), d6)
      val () = check_kinding d7
      val c8 = CAbs c7
      val ct8 = tl ct7
      val d8 = KdAbs ((ct8, c8, KArrow (KType, KArrow (KNat, KType))), WfKdType (ct8, KType), d7)
      val () = check_kinding d8
      val c9 = CRec (KArrow (KType, KArrow (KNat, KType)), c8)
      val ct9 = tl ct8
      val d9 = KdRec ((ct9, c9, KArrow (KType, KArrow (KNat, KType))), WfKdArrow ((ct9, KArrow (KType, KArrow (KNat, KType))), WfKdType (ct9, KType), WfKdArrow ((ct9, KArrow (KNat, KType)), WfKdBaseSort (ct9, KNat), WfKdType (ct9, KType))), d8)
      val () = check_kinding d9
      val list_dec = c9
      val list_kd = d9
      val c10 = CApps list_dec [CVar 2, CBinOp (CBNatAdd, CVar 1, CVar 0)]
      val ct10 = [KNat, KNat, KType]
      val d10 = KdApp ((ct10, c10, KType), KdApp ((ct10, CApp (list_dec, CVar 2), KArrow (KNat, KType)), shift0_ctx_kd (ct10, []) list_kd, KdVar (ct10, CVar 2, KType)), KdBinOp ((ct10, CBinOp (CBNatAdd, CVar 1, CVar 0), KNat), KdVar (ct10, CVar 1, KNat), KdVar (ct10, CVar 0, KNat)))
      val () = check_kinding d10
      val c11 = CApps list_dec [CVar 2, CVar 1]
      val ct11 = ct10
      val d11 = KdApp ((ct11, c11, KType), KdApp ((ct11, CApp (list_dec, CVar 2), KArrow (KNat, KType)), shift0_ctx_kd (ct11, []) list_kd, KdVar (ct11, CVar 2, KType)), KdVar (ct11, CVar 1, KNat))
      val () = check_kinding d11
      val c12 = CApps list_dec [CVar 2, CVar 0]
      val ct12 = ct11
      val d12 = KdApp ((ct12, c12, KType), KdApp ((ct12, CApp (list_dec, CVar 2), KArrow (KNat, KType)), shift0_ctx_kd (ct12, []) list_kd, KdVar (ct12, CVar 2, KType)), KdVar (ct12, CVar 0, KNat))
      val () = check_kinding d12
      val c13 = CProd (c11, c12)
      val ct13 = ct12
      val d13 = KdBinOp ((ct13, c13, KType), d11, d12)
      val () = check_kinding d13
      val c14 = CArrow (c13, TfromNat (CVar 1), c10)
      val ct14 = ct13
      val d14 = KdArrow ((ct14, c14, KType), d13, KdUnOp ((ct14, TfromNat (CVar 1), KTime), KdVar (ct14, CVar 1, KNat)), d10)
      val () = check_kinding d14
      val c15 = CForall (KNat, c14)
      val ct15 = tl ct14
      val d15 = KdQuan ((ct15, c15, KType), WfKdBaseSort (ct15, KNat), d14)
      val () = check_kinding d15
      val c16 = CForall (KNat, c15)
      val ct16 = tl ct15
      val d16 = KdQuan ((ct16, c16, KType), WfKdBaseSort (ct16, KNat), d15)
      val () = check_kinding d16
      val c17 = CForall (KType, c16)
      val ct17 = tl ct16
      val d17 = KdQuan ((ct17, c17, KType), WfKdType (ct17, KType), d16)
      val () = check_kinding d17
      val concat_t = c17
      val concat_kd = d17
      val e18 = EProj (ProjSnd, EVar 1)
      val ct18 = ([KNat, KNat, KType], [CExists (KSubset (KUnit, PBinPred (PBNatEq, CVar 2, get_nat 0)), CTypeUnit), CProd (CApps list_dec [CVar 2, CVar 1], CApps list_dec [CVar 2, CVar 0]), concat_t])
      val t18 = CApps list_dec [CVar 2, CVar 0]
      val i18 = T0
      val d18 = TyProj ((ct18, e18, t18, i18), TyVar (ct18, EVar 1, nth (snd ct18, 1), T0))
      val () = check_typing d18
      val e19 = e18
      val ct19 = ct18
      val t19 = CApps list_dec [CVar 2, CBinOp (CBNatAdd, CVar 1, CVar 0)]
      val i19 = TfromNat (CVar 1)
      val d19 = TySub ((ct19, e19, t19, i19), d18, TyEqApp ((fst ct19, t18, t19), TyEqApp ((fst ct19, CApp (list_dec, CVar 2), CApp (list_dec, CVar 2)), TyEqRec ((fst ct19, list_dec, list_dec), KdEqKArrow ((fst ct19, KArrow (KType, KArrow (KNat, KType)), KArrow (KType, KArrow (KNat, KType))), KdEqKType (fst ct19, KType, KType), KdEqKArrow ((fst ct19, KArrow (KNat, KType), KArrow (KNat, KType)), KdEqBaseSort (fst ct19, KNat, KNat), KdEqKType (fst ct19, KType, KType))), TyEqAbs (KArrow (KType, KArrow (KNat, KType)) :: fst ct19, c8, c8)), TyEqVar (fst ct19, CVar 2, CVar 2)), TyEqNat ((fst ct19, CVar 0, CBinOp (CBNatAdd, CVar 1, CVar 0)), KdVar (fst ct19, CVar 0, KNat), KdBinOp ((fst ct19, CBinOp (CBNatAdd, CVar 1, CVar 0), KNat), KdVar (fst ct19, CVar 1, KNat), KdVar (fst ct19, CVar 0, KNat)), PrAdmit (fst ct19, PBinPred (PBNatEq, CVar 0, CBinOp (CBNatAdd, CVar 1, CVar 0))))), PrAdmit (fst ct19, TLe (i18, i19)))
      val () = check_typing d19
      val e20 = EProj (ProjFst, EVar 0)
      val ct20 = ([KSubset (KUnit, PBinPred (PBNatEq, CVar 3, CBinOp (CBNatAdd, CVar 1, get_nat 1))), KNat, KNat, KNat, KType], [CProd (CVar 4, CApps list_dec [CVar 4, CVar 1]), CExists (KSubset (KUnit, PBinPred (PBNatEq, CVar 4, CBinOp (CBNatAdd, CVar 2, get_nat 1))), CProd (CVar 5, CApps list_dec [CVar 5, CVar 2])), CExists (KNat, CExists (KSubset (KUnit, PBinPred (PBNatEq, CVar 5, CBinOp (CBNatAdd, CVar 1, get_nat 1))), CProd (CVar 6, CApps list_dec [CVar 6, CVar 1]))), CProd (CApps list_dec [CVar 4, CVar 3], CApps list_dec [CVar 4, CVar 2]), concat_t])
      val t20 = CVar 4
      val i20 = T0
      val d20 = TyProj ((ct20, e20, t20, i20), TyVar (ct20, EVar 0, nth (snd ct20, 0), T0))
      val () = check_typing d20
      val e21 = EProj (ProjSnd, EVar 0)
      val ct21 = ct20
      val t21 = CApps list_dec [CVar 4, CVar 1]
      val i21 = T0
      val d21 = TyProj ((ct21, e21, t21, i21), TyVar (ct21, EVar 0, nth (snd ct21, 0), T0))
      val () = check_typing d21
      val e22 = EProj (ProjSnd, EVar 3)
      val ct22 = ct21
      val t22 = CApps list_dec [CVar 4, CVar 2]
      val i22 = T0
      val d22 = TyProj ((ct22, e22, t22, i22), TyVar (ct22, EVar 3, nth (snd ct22, 3), T0))
      val () = check_typing d22
      val e23 = EPair (e21, e22)
      val ct23 = ct22
      val t23 = CProd (t21, t22)
      val i23 = Tadd (i21, i22)
      val d23 = TyPair ((ct23, e23, t23, i23), d21, d22)
      val () = check_typing d23
      val e24 = EAppC (EVar 4, CVar 4)
      val ct24 = ct23
      val t24 = subst0_c_c (CVar 4) (#3 (extract_c_quan concat_t))
      val i24 = T0
      val d24 = TyAppC ((ct24, e24, t24, i24), TyVar (ct24, EVar 4, nth (snd ct24, 4), T0), KdVar (fst ct24, CVar 4, KType))
      val () = check_typing d24
      val e25 = EAppC (e24, CVar 1)
      val ct25 = ct24
      val t25 = subst0_c_c (CVar 1) (#3 (extract_c_quan t24))
      val i25 = i24
      val d25 = TyAppC ((ct25, e25, t25, i25), d24, KdVar (fst ct25, CVar 1, KNat))
      val () = check_typing d25
      val e26 = EAppC (e25, CVar 2)
      val ct26 = ct25
      val t26 = subst0_c_c (CVar 2) (#3 (extract_c_quan t25))
      val i26 = i25
      val d26 = TyAppC ((ct26, e26, t26, i26), d25, KdVar (fst ct25, CVar 2, KNat))
      val () = check_typing d26
      val e27 = EApp (e26, e23)
      val ct27 = ct26
      val t27 = CApps list_dec [CVar 4, CBinOp (CBNatAdd, CVar 1, CVar 2)]
      val i27 = Tadd (Tadd (Tadd (i26, i23), T1), CUnOp (CUNat2Time, CVar 1))
      val d27 = TyApp ((ct27, e27, t27, i27), d26, d23)
      val () = check_typing d27
      val e28 = EProj (ProjFst, EVar 0)
      val ct28 = ct27
      val t28 = CVar 4
      val i28 = T0
      val d28 = TyProj ((ct28, e28, t28, i28), TyVar (ct28, EVar 0, nth (snd ct28, 0), T0))
      val () = check_typing d28
      val e29 = EPair (e28, e27)
      val ct29 = ct28
      val t29 = CProd (t28, t27)
      val i29 = Tadd (i28, i27)
      val d29 = TyPair ((ct29, e29, t29, i29), d28, d27)
      val () = check_typing d29
      val e30 = e29
      val ct30 = ct29
      val t30 = t29
      val i30 = CUnOp (CUNat2Time, CVar 3)
      val d30 = TySub ((ct30, e30, t30, i30), d29, TyEqBinOp ((fst ct30, t29, t30), TyEqVar (fst ct30, CVar 4, CVar 4), TyEqApp ((fst ct30, t27, t27), TyEqApp ((fst ct30, CApp (list_dec, CVar 4), CApp (list_dec, CVar 4)), TyEqRec ((fst ct30, list_dec, list_dec), KdEqKArrow ((fst ct30, KArrow (KType, KArrow (KNat, KType)), KArrow (KType, KArrow (KNat, KType))), KdEqKType (fst ct30, KType, KType), KdEqKArrow ((fst ct30, KArrow (KNat, KType), KArrow (KNat, KType)), KdEqBaseSort (fst ct30, KNat, KNat), KdEqKType (fst ct30, KType, KType))), TyEqAbs (KArrow (KType, KArrow (KNat, KType)) :: fst ct30, c8, c8)), TyEqVar (fst ct30, CVar 4, CVar 4)), TyEqBinOp ((fst ct30, CBinOp (CBNatAdd, CVar 1, CVar 2), CBinOp (CBNatAdd, CVar 1, CVar 2)), TyEqVar (fst ct30, CVar 1, CVar 1), TyEqVar (fst ct30, CVar 2, CVar 2)))), PrAdmit (fst ct30, TLe (i29, i30)))
      val () = check_typing d30
      val e31 = EPack (CVar 0, e30)
      val ct31 = ct30
      val t31 = CExists (KSubset (KUnit, PBinPred (PBNatEq, CVar 4, CBinOp (CBNatAdd, CVar 2, get_nat 1))), shift_c_c 1 1 t30)
      val i31 = i30
      val d31 = TyPack ((ct31, e31, t31, i31), KdQuan ((fst ct31, t31, KType), WfKdSubset ((fst ct31, KSubset (KUnit, PBinPred (PBNatEq, CVar 4, CBinOp (CBNatAdd, CVar 2, get_nat 1)))), WfKdBaseSort (fst ct31, KUnit), WfPropBinPred ((KUnit :: fst ct31, PBinPred (PBNatEq, CVar 4, CBinOp (CBNatAdd, CVar 2, get_nat 1))), KdVar (KUnit :: fst ct31, CVar 4, KNat), KdBinOp ((KUnit :: fst ct31, CBinOp (CBNatAdd, CVar 2, get_nat 1), KNat), KdVar (KUnit :: fst ct31, CVar 2, KNat), KdConst (KUnit :: fst ct31, get_nat 1, KNat)))), KdBinOp ((KSubset (KUnit, PBinPred (PBNatEq, CVar 4, CBinOp (CBNatAdd, CVar 2, get_nat 1))) :: fst ct31, shift0_c_c t29, KType), KdVar (KSubset (KUnit, PBinPred (PBNatEq, CVar 4, CBinOp (CBNatAdd, CVar 2, get_nat 1))) :: fst ct31, shift0_c_c t28, KType), KdApp ((KSubset (KUnit, PBinPred (PBNatEq, CVar 4, CBinOp (CBNatAdd, CVar 2, get_nat 1))) :: fst ct31, shift0_c_c t27, KType), KdApp ((KSubset (KUnit, PBinPred (PBNatEq, CVar 4, CBinOp (CBNatAdd, CVar 2, get_nat 1))) :: fst ct31, CApp (list_dec, CVar 5), KArrow (KNat, KType)), shift0_ctx_kd (KSubset (KUnit, PBinPred (PBNatEq, CVar 4, CBinOp (CBNatAdd, CVar 2, get_nat 1))) :: fst ct31, []) list_kd, KdVar (KSubset (KUnit, PBinPred (PBNatEq, CVar 4, CBinOp (CBNatAdd, CVar 2, get_nat 1))) :: fst ct31, CVar 5, KType)), KdBinOp ((KSubset (KUnit, PBinPred (PBNatEq, CVar 4, CBinOp (CBNatAdd, CVar 2, get_nat 1))) :: fst ct31, CBinOp (CBNatAdd, CVar 2, CVar 3), KNat), KdVar (KSubset (KUnit, PBinPred (PBNatEq, CVar 4, CBinOp (CBNatAdd, CVar 2, get_nat 1))) :: fst ct31, CVar 2, KNat), KdVar (KSubset (KUnit, PBinPred (PBNatEq, CVar 4, CBinOp (CBNatAdd, CVar 2, get_nat 1))) :: fst ct31, CVar 3, KNat))))), KdVar (fst ct31, CVar 0, shift_c_k 1 0 (nth (fst ct31, 0))), d30)
      val () = check_typing d31
      val e32 = e31
      val ct32 = ct31
      val t32 = CExists (KSubset (KUnit, PBinPred (PBNatEq, CBinOp (CBNatAdd, CVar 4, CVar 3), CBinOp (CBNatAdd, CBinOp (CBNatAdd, CVar 2, CVar 3), get_nat 1))), shift_c_c 1 1 t30)
      val i32 = i31
      val d32 = TySub ((ct32, e32, t32, i32), d31, TyEqQuan ((fst ct32, t31, t32), KdEqSubset ((fst ct32, KSubset (KUnit, PBinPred (PBNatEq, CVar 4, CBinOp (CBNatAdd, CVar 2, get_nat 1))), KSubset (KUnit, PBinPred (PBNatEq, CBinOp (CBNatAdd, CVar 4, CVar 3), CBinOp (CBNatAdd, CBinOp (CBNatAdd, CVar 2, CVar 3), get_nat 1)))), KdEqBaseSort (fst ct32, KUnit, KUnit), PrAdmit (KUnit :: fst ct32, PIff (PBinPred (PBNatEq, CVar 4, CBinOp (CBNatAdd, CVar 2, get_nat 1)), PBinPred (PBNatEq, CBinOp (CBNatAdd, CVar 4, CVar 3), CBinOp (CBNatAdd, CBinOp (CBNatAdd, CVar 2, CVar 3), get_nat 1))))), shift0_ctx_te ([KSubset (KUnit, PBinPred (PBNatEq, CVar 4, CBinOp (CBNatAdd, CVar 2, get_nat 1)))], []) (TyEqBinOp ((fst ct32, t30, t30), TyEqVar (fst ct32, CVar 4, CVar 4), TyEqApp ((fst ct30, t27, t27), TyEqApp ((fst ct30, CApp (list_dec, CVar 4), CApp (list_dec, CVar 4)), TyEqRec ((fst ct30, list_dec, list_dec), KdEqKArrow ((fst ct30, KArrow (KType, KArrow (KNat, KType)), KArrow (KType, KArrow (KNat, KType))), KdEqKType (fst ct30, KType, KType), KdEqKArrow ((fst ct30, KArrow (KNat, KType), KArrow (KNat, KType)), KdEqBaseSort (fst ct30, KNat, KNat), KdEqKType (fst ct30, KType, KType))), TyEqAbs (KArrow (KType, KArrow (KNat, KType)) :: fst ct30, c8, c8)), TyEqVar (fst ct30, CVar 4, CVar 4)), TyEqBinOp ((fst ct30, CBinOp (CBNatAdd, CVar 1, CVar 2), CBinOp (CBNatAdd, CVar 1, CVar 2)), TyEqVar (fst ct30, CVar 1, CVar 1), TyEqVar (fst ct30, CVar 2, CVar 2)))))), PrAdmit (fst ct32, TLe (i31, i32)))
      val () = check_typing d32
      val e33 = EPack (CBinOp (CBNatAdd, CVar 1, CVar 2), e32)
      val ct33 = ct32
      val t33 = CExists (KNat, CExists (KSubset (KUnit, PBinPred (PBNatEq, CBinOp (CBNatAdd, CVar 5, CVar 4), CBinOp (CBNatAdd, CVar 1, get_nat 1))), CProd (CVar 6, CApps list_dec [CVar 6, CVar 1])))
      val i33 = i32
      val tmp1 = [KSubset (KUnit, PBinPred (PBNatEq, CBinOp (CBNatAdd, CVar 5, CVar 4), CBinOp (CBNatAdd, CVar 1, get_nat 1))), KNat] @ fst ct33
      val d33 = TyPack ((ct33, e33, t33, i33), KdQuan ((fst ct33, CExists (KNat, CExists (KSubset (KUnit, PBinPred (PBNatEq, CBinOp (CBNatAdd, CVar 5, CVar 4), CBinOp (CBNatAdd, CVar 1, get_nat 1))), CProd (CVar 6, CApps list_dec [CVar 6, CVar 1]))), KType), WfKdBaseSort (fst ct33, KNat), KdQuan ((KNat :: fst ct33, CExists (KSubset (KUnit, PBinPred (PBNatEq, CBinOp (CBNatAdd, CVar 5, CVar 4), CBinOp (CBNatAdd, CVar 1, get_nat 1))), CProd (CVar 6, CApps list_dec [CVar 6, CVar 1])), KType), WfKdSubset ((KNat :: fst ct33, KSubset (KUnit, PBinPred (PBNatEq, CBinOp (CBNatAdd, CVar 5, CVar 4), CBinOp (CBNatAdd, CVar 1, get_nat 1)))), WfKdBaseSort (KNat :: fst ct33, KUnit), WfPropBinPred ((KUnit :: KNat :: fst ct33, PBinPred (PBNatEq, CBinOp (CBNatAdd, CVar 5, CVar 4), CBinOp (CBNatAdd, CVar 1, get_nat 1))), KdBinOp ((KUnit :: KNat :: fst ct33, CBinOp (CBNatAdd, CVar 5, CVar 4), KNat), KdVar (KUnit :: KNat :: fst ct33, CVar 5, KNat), KdVar (KUnit :: KNat :: fst ct33, CVar 4, KNat)), KdBinOp ((KUnit :: KNat :: fst ct33, CBinOp (CBNatAdd, CVar 1, get_nat 1), KNat), KdVar (KUnit :: KNat :: fst ct33, CVar 1, KNat), KdConst (KUnit :: KNat :: fst ct33, get_nat 1, KNat)))), KdBinOp ((tmp1, CProd (CVar 6, CApps list_dec [CVar 6, CVar 1]), KType), KdVar (tmp1, CVar 6, KType), KdApp ((tmp1, CApps list_dec [CVar 6, CVar 1], KType), KdApp ((tmp1, CApp (list_dec, CVar 6), KArrow (KNat, KType)), shift0_ctx_kd (tmp1, []) list_kd, KdVar (tmp1, CVar 6, KType)), KdVar (tmp1, CVar 1, KNat))))), KdBinOp ((fst ct33, CBinOp (CBNatAdd, CVar 1, CVar 2), KNat), KdVar (fst ct33, CVar 1, KNat), KdVar (fst ct33, CVar 2, KNat)), d32)
      val () = check_typing d33
      val e34 = EInj (InjInr, e33)
      val ct34 = ct33
      val t34 = CSum (CExists (KSubset (KUnit, PBinPred (PBNatEq, CBinOp (CBNatAdd, CVar 4, CVar 3), get_nat 0)), CTypeUnit), t33)
      val i34 = i33
      val d34 = TyInj ((ct34, e34, t34, i34), d33, KdQuan ((fst ct34, CExists (KSubset (KUnit, PBinPred (PBNatEq, CBinOp (CBNatAdd, CVar 4, CVar 3), get_nat 0)), CTypeUnit), KType), WfKdSubset ((fst ct34, KSubset (KUnit, PBinPred (PBNatEq, CBinOp (CBNatAdd, CVar 4, CVar 3), get_nat 0))), WfKdBaseSort (fst ct34, KUnit), WfPropBinPred ((KUnit :: fst ct34, PBinPred (PBNatEq, CBinOp (CBNatAdd, CVar 4, CVar 3), get_nat 0)), KdBinOp ((KUnit :: fst ct34, CBinOp (CBNatAdd, CVar 4, CVar 3), KNat), KdVar (KUnit :: fst ct34, CVar 4, KNat), KdVar (KUnit :: fst ct34, CVar 3, KNat)), KdConst (KUnit :: fst ct34, get_nat 0, KNat))), KdConst (KSubset (KUnit, PBinPred (PBNatEq, CBinOp (CBNatAdd, CVar 4, CVar 3), get_nat 0)) :: fst ct34, CTypeUnit, KType)))
      val () = check_typing d34
      val e35 = e34
      val ct35 = ct34
      val t35 = CApp (CAbs (CSum (CExists (KSubset (KUnit, PBinPred (PBNatEq, CVar 1, get_nat 0)), CTypeUnit), CExists (KNat, CExists (KSubset (KUnit, PBinPred (PBNatEq, CVar 2, CBinOp (CBNatAdd, CVar 1, get_nat 1))), CProd (CVar 7, CApps list_dec [CVar 7, CVar 1]))))), CBinOp (CBNatAdd, CVar 3, CVar 2))
      val i35 = i34
      val d35 = TySub ((ct35, e35, t35, i35), d34, TyEqBetaRev ((fst ct35, t34, t35), TyEqAbs (fst ct35, CAbs (CSum (CExists (KSubset (KUnit, PBinPred (PBNatEq, CVar 1, get_nat 0)), CTypeUnit), CExists (KNat, CExists (KSubset (KUnit, PBinPred (PBNatEq, CVar 2, CBinOp (CBNatAdd, CVar 1, get_nat 1))), CProd (CVar 7, CApps list_dec [CVar 7, CVar 1]))))), CAbs (CSum (CExists (KSubset (KUnit, PBinPred (PBNatEq, CVar 1, get_nat 0)), CTypeUnit), CExists (KNat, CExists (KSubset (KUnit, PBinPred (PBNatEq, CVar 2, CBinOp (CBNatAdd, CVar 1, get_nat 1))), CProd (CVar 7, CApps list_dec [CVar 7, CVar 1])))))), TyEqBinOp ((fst ct35, CBinOp (CBNatAdd, CVar 3, CVar 2), CBinOp (CBNatAdd, CVar 3, CVar 2)), TyEqVar (fst ct35, CVar 3, CVar 3), TyEqVar (fst ct35, CVar 2, CVar 2)), gen_tyeq_refl (fst ct35) t34), PrAdmit (fst ct35, TLe (i34, i35)))
      val () = check_typing d35
      val e36 = e35
      val ct36 = ct35
      val t36 = CApps (CAbs (CAbs (CSum (CExists (KSubset (KUnit, PBinPred (PBNatEq, CVar 1, get_nat 0)), CTypeUnit), CExists (KNat, CExists (KSubset (KUnit, PBinPred (PBNatEq, CVar 2, CBinOp (CBNatAdd, CVar 1, get_nat 1))), CProd (CVar 3, CApps list_dec [CVar 3, CVar 1]))))))) [CVar 4, CBinOp (CBNatAdd, CVar 3, CVar 2)]
      val i36 = i35
      val d36 = TySub ((ct36, e36, t36, i36), d35, TyEqApp ((fst ct36, t35, t36), TyEqBetaRev ((fst ct36, CAbs (CSum (CExists (KSubset (KUnit, PBinPred (PBNatEq, CVar 1, get_nat 0)), CTypeUnit), CExists (KNat, CExists (KSubset (KUnit, PBinPred (PBNatEq, CVar 2, CBinOp (CBNatAdd, CVar 1, get_nat 1))), CProd (CVar 7, CApps list_dec [CVar 7, CVar 1]))))), CApp (CAbs (CAbs (CSum (CExists (KSubset (KUnit, PBinPred (PBNatEq, CVar 1, get_nat 0)), CTypeUnit), CExists (KNat, CExists (KSubset (KUnit, PBinPred (PBNatEq, CVar 2, CBinOp (CBNatAdd, CVar 1, get_nat 1))), CProd (CVar 3, CApps list_dec [CVar 3, CVar 1])))))), CVar 4)), gen_tyeq_refl (fst ct36) (CAbs (CAbs (CSum (CExists (KSubset (KUnit, PBinPred (PBNatEq, CVar 1, get_nat 0)), CTypeUnit), CExists (KNat, CExists (KSubset (KUnit, PBinPred (PBNatEq, CVar 2, CBinOp (CBNatAdd, CVar 1, get_nat 1))), CProd (CVar 3, CApps list_dec [CVar 3, CVar 1]))))))), gen_tyeq_refl (fst ct36) (CVar 4),gen_tyeq_refl (fst ct36) (CAbs (CSum (CExists (KSubset (KUnit, PBinPred (PBNatEq, CVar 1, get_nat 0)), CTypeUnit), CExists (KNat, CExists (KSubset (KUnit, PBinPred (PBNatEq, CVar 2, CBinOp (CBNatAdd, CVar 1, get_nat 1))), CProd (CVar 7, CApps list_dec [CVar 7, CVar 1]))))))), gen_tyeq_refl (fst ct36) (CBinOp (CBNatAdd, CVar 3, CVar 2))), PrAdmit (fst ct36, TLe (i35, i36)))
      val () = check_typing d36
      val e37 = EFold e36
      val ct37 = ct36
      val t37 = CApps list_dec [CVar 4, CBinOp (CBNatAdd, CVar 3, CVar 2)]
      val i37 = i36
      val d37 = TyFold ((ct37, e37, t37, i37), KdApp ((fst ct37, t37, KType), KdApp ((fst ct37, CApp (list_dec, CVar 4), KArrow (KNat, KType)), shift0_ctx_kd ct37 list_kd, KdVar (fst ct37, CVar 4, KType)), KdBinOp ((fst ct37, CBinOp (CBNatAdd, CVar 3, CVar 2), KNat), KdVar (fst ct35, CVar 3, KNat), KdVar (fst ct37, CVar 2, KNat))), d36)
      val () = check_typing d37
      val e38 = EUnpack (EVar 0, e37)
      val ct38 = (tl $ fst ct37, map (shift_c_c ~1 0) $ tl $ snd ct37)
      val t38 = shift_c_c ~1 0 t37
      val i38 = Tadd (T0, shift_c_c ~1 0 i37)
      val d38 = TyUnpack ((ct38, e38, t38, i38), TyVar (ct38, EVar 0, hd $ snd ct38, T0), d37)
      val () = check_typing d38
      val e39 = EUnpack (EVar 0, e38)
      val ct39 = (tl $ fst ct38, map (shift_c_c ~1 0) $ tl $ snd ct38)
      val t39 = shift_c_c ~1 0 t38
      val i39 = Tadd (T0, shift_c_c ~1 0 i38)
      val d39 = TyUnpack ((ct39, e39, t39, i39), TyVar (ct39, EVar 0, hd $ snd ct39, T0), d38)
      val () = check_typing d39
      val e40 = EProj (ProjFst, EVar 0)
      val ct40 = (fst ct39, tl $ snd ct39)
      val t40 = CApps list_dec [CVar 2, CVar 1]
      val i40 = T0
      val d40 = TyProj ((ct40, e40, t40, i40), TyVar (ct40, EVar 0, hd $ snd ct40, T0))
      val () = check_typing d40
      val e41 = EUnfold e40
      val ct41 = ct40
      val (_, list_body) = extract_c_rec list_dec
      val t41 = CApps (subst0_c_c list_dec list_body) [CVar 2, CVar 1]
      val i41 = T0
      val d41 = TyUnfold ((ct41, e41, t41, i41), d40)
      val () = check_typing d41
      val e42 = e41
      val ct42 = ct41
      val t42 = CApp (subst0_c_c (CVar 2) (extract_c_abs $ subst0_c_c list_dec list_body), CVar 1)
      val i42 = i41
      val d42 = TySub ((ct42, e42, t42, i42), d41, TyEqApp ((fst ct42, t41, t42), TyEqBeta ((fst ct42, CApp (subst0_c_c list_dec list_body, CVar 2), subst0_c_c (CVar 2) (extract_c_abs $ subst0_c_c list_dec list_body)), gen_tyeq_refl (fst ct42) (subst0_c_c list_dec list_body), gen_tyeq_refl (fst ct42) (CVar 2), gen_tyeq_refl (fst ct42) (subst0_c_c (CVar 2) (extract_c_abs $ subst0_c_c list_dec list_body))), gen_tyeq_refl (fst ct42) (CVar 1)), PrAdmit (fst ct42, TLe (i41, i42)))
      val () = check_typing d42
      val e43 = e42
      val ct43 = ct42
      val t43 = subst0_c_c (CVar 1) (extract_c_abs $ subst0_c_c (CVar 2) (extract_c_abs $ subst0_c_c list_dec list_body))
      val i43 = i42
      val d43 = TySub ((ct43, e43, t43, i43), d42, TyEqBeta ((fst ct43, t42, t43), gen_tyeq_refl (fst ct43) (subst0_c_c (CVar 2) (extract_c_abs $ subst0_c_c list_dec list_body)), gen_tyeq_refl (fst ct43) (CVar 1), gen_tyeq_refl (fst ct43) t43), PrAdmit (fst ct43, TLe (i42, i43)))
      val () = check_typing d43
      val e44 = ECase (e43, e19, e39)
      val ct44 = ct43
      val t44 = t19
      val i44 = Tadd (i43, Tmax (i19, i39))
      val d44 = TyCase ((ct44, e44, t44, i44), d43, d19, d39)
      val () = check_typing d44
      val e45 = e44
      val ct45 = ct44
      val t45 = t44
      val i45 = CUnOp (CUNat2Time, CVar 1)
      val d45 = TySub ((ct45, e45, t45, i45), d44, gen_tyeq_refl (fst ct45) t45, PrAdmit (fst ct45, TLe (i44, i45)))
      val () = check_typing d45
      val e46 = EAbs e45
      val ct46 = (fst ct45, tl $ snd ct45)
      val t46 = CArrow (hd $ snd ct45, i45, t45)
      val i46 = T0
      val d46 = TyAbs ((ct46, e46, t46, i46), KdBinOp ((fst ct46, CProd (CApps list_dec [CVar 2, CVar 1], CApps list_dec [CVar 2, CVar 0]), KType), KdApp ((fst ct46, CApps list_dec [CVar 2, CVar 1], KType), KdApp ((fst ct46, CApp (list_dec, CVar 2), KArrow (KNat, KType)), shift0_ctx_kd ct46 list_kd, KdVar (fst ct46, CVar 2, KType)), KdVar (fst ct46, CVar 1, KNat)), KdApp ((fst ct46, CApps list_dec [CVar 2, CVar 0], KType), KdApp ((fst ct46, CApp (list_dec, CVar 2), KArrow (KNat, KType)), shift0_ctx_kd ct46 list_kd, KdVar (fst ct46, CVar 2, KType)), KdVar (fst ct46, CVar 0, KNat))), d45)
      val () = check_typing d46
      val e47 = EAbsC e46
      val ct47 = (tl $ fst ct46, map (shift_c_c ~1 0) $ snd ct46)
      val t47 = CForall (KNat, t46)
      val i47 = T0
      val d47 = TyAbsC ((ct47, e47, t47, i47), WfKdBaseSort (fst ct47, KNat), d46)
      val () = check_typing d47
      val e48 = EAbsC e47
      val ct48 = (tl $ fst ct47, map (shift_c_c ~1 0) $ snd ct47)
      val t48 = CForall (KNat, t47)
      val i48 = T0
      val d48 = TyAbsC ((ct48, e48, t48, i48), WfKdBaseSort (fst ct48, KNat), d47)
      val () = check_typing d48
      val e49 = EAbsC e48
      val ct49 = (tl $ fst ct48, map (shift_c_c ~1 0) $ snd ct48)
      val t49 = CForall (KType, t48)
      val i49 = T0
      val d49 = TyAbsC ((ct49, e49, t49, i49), WfKdType (fst ct49, KType), d48)
      val () = check_typing d49
      val e50 = ERec e49
      val ct50 = (fst ct49, tl $ snd ct49)
      val t50 = t49
      val i50 = T0
      val d50 = TyRec ((ct50, e50, t50, i50), concat_kd, d49)
      val () = check_typing d50
      val cps_ty = CPS.cps_deriv d50
      val () = println $ str_expr $ #2 (extract_judge_typing cps_ty)
      val () = check_typing cps_ty
      (*val wrap_ty = WrapLambda.wrap_lambda_deriv cps_ty
      val () = println $ str_expr $ #2 (extract_judge_typing wrap_ty)
      val () = check_typing wrap_ty
      val clo_ty = CloConv.clo_conv_deriv wrap_ty
      val () = println $ str_expr $ #2 (extract_judge_typing clo_ty)
      val () = check_typing clo_ty*)
      (*val hoisted_ty = hoist_deriv clo_ty
      val () = print $ str_program $ #1 (extract_judge_ptyping hoisted_ty)
      val () = HoistedDerivChecker.check_program hoisted_ty*)
  (*val concat_anf_ty = fst $ ANF.normalize_deriv concat_clo_conv_deriv
      val jconcat_anf_ty = extract_judge_typing concat_anf_ty
      val () = println $ str_expr $ #2 jconcat_anf_ty
      val () = check_typing concat_anf_ty
      val concat_hoisted_ty = Hoist.hoist concat_anf_ty
      val () = HoistedDerivChecker.check_program concat_hoisted_ty*)
  in
      println ""
  end

fun test () =
  let
      (*val () = test_cps ()*)
      val () = test_absc_appc ()
      val () = test_abs_app ()
      val () = test_currying ()
      val () = test_concat ()
  in
      ()
  end
(*open Util
  open MicroTiML

  fun test_len () =
    let
      val list_cstr = CstrRec (KdArrow (KdProper, KdArrow (KdNat, KdProper)), CstrAbs (KdProper, CstrAbs (KdNat, CstrSum (CstrExists (KdSubset (KdUnit, PrBinRel (PrRelEq, CstrVar 1, CstrNat 0)), CstrTypeUnit), CstrExists (KdSubset (KdNat, PrBinRel (PrRelEq, CstrVar 1, CstrBinOp (CstrBopAdd, CstrVar 0, CstrNat 1))), CstrProd (CstrVar 2, CstrApp (CstrApp (CstrVar 3, CstrVar 2), CstrVar 0)))))))
      val c1 = CstrExists (KdSubset (KdUnit, PrBinRel (PrRelEq, CstrVar 1, CstrNat 0)), CstrTypeUnit)
      val ct1 = [BdKind KdNat, BdKind KdProper, BdKind (KdArrow (KdProper, KdArrow (KdNat, KdProper)))]
      val d1 = KdDerivExists ((ct1, c1, KdProper), KdWfDerivSubset ((ct1, KdSubset (KdUnit, PrBinRel (PrRelEq, CstrVar 1, CstrNat 0))), KdWfDerivUnit (ct1, KdUnit), PrWfDerivBinRel ((BdKind KdUnit :: ct1, PrBinRel (PrRelEq, CstrVar 1, CstrNat 0)), KdDerivVar (BdKind KdUnit :: ct1, CstrVar 1, KdNat), KdDerivNat (BdKind KdUnit :: ct1, CstrNat 0, KdNat))), KdDerivTypeUnit (BdKind (KdSubset (KdUnit, PrBinRel (PrRelEq, CstrVar 1, CstrNat 0))) :: ct1, CstrTypeUnit, KdProper))
      val c2 = CstrExists (KdSubset (KdNat, PrBinRel (PrRelEq, CstrVar 1, CstrBinOp (CstrBopAdd, CstrVar 0, CstrNat 1))), CstrProd (CstrVar 2, CstrApp (CstrApp (CstrVar 3, CstrVar 2), CstrVar 0)))
      val ct2 = ct1
      val d2 = KdDerivExists ((ct2, c2, KdProper), KdWfDerivSubset ((ct2, KdSubset (KdNat, PrBinRel (PrRelEq, CstrVar 1, CstrBinOp (CstrBopAdd, CstrVar 0, CstrNat 1)))), KdWfDerivNat (ct2, KdNat), PrWfDerivBinRel ((BdKind KdNat :: ct2, PrBinRel (PrRelEq, CstrVar 1, CstrBinOp (CstrBopAdd, CstrVar 0, CstrNat 1))), KdDerivVar (BdKind KdNat :: ct2, CstrVar 1, KdNat), KdDerivBinOp ((BdKind KdNat :: ct2, CstrBinOp (CstrBopAdd, CstrVar 0, CstrNat 1), KdNat), KdDerivVar (BdKind KdNat :: ct2, CstrVar 0, KdNat), KdDerivNat (BdKind KdNat :: ct2, CstrNat 1, KdNat)))), KdDerivProd ((BdKind (KdSubset (KdNat, PrBinRel (PrRelEq, CstrVar 1, CstrBinOp (CstrBopAdd, CstrVar 0, CstrNat 1)))) :: ct2, CstrProd (CstrVar 2, CstrApp (CstrApp (CstrVar 3, CstrVar 2), CstrVar 0)), KdProper), KdDerivVar (BdKind (KdSubset (KdNat, PrBinRel (PrRelEq, CstrVar 1, CstrBinOp (CstrBopAdd, CstrVar 0, CstrNat 1)))) :: ct2, CstrVar 2, KdProper), KdDerivApp ((BdKind (KdSubset (KdNat, PrBinRel (PrRelEq, CstrVar 1, CstrBinOp (CstrBopAdd, CstrVar 0, CstrNat 1)))) :: ct2, CstrApp (CstrApp (CstrVar 3, CstrVar 2), CstrVar 0), KdProper), KdDerivApp ((BdKind (KdSubset (KdNat, PrBinRel (PrRelEq, CstrVar 1, CstrBinOp (CstrBopAdd, CstrVar 0, CstrNat 1)))) :: ct2, CstrApp (CstrVar 3, CstrVar 2), KdArrow (KdNat, KdProper)), KdDerivVar (BdKind (KdSubset (KdNat, PrBinRel (PrRelEq, CstrVar 1, CstrBinOp (CstrBopAdd, CstrVar 0, CstrNat 1)))) :: ct2, CstrVar 3, KdArrow (KdProper, KdArrow (KdNat, KdProper))), KdDerivVar (BdKind (KdSubset (KdNat, PrBinRel (PrRelEq, CstrVar 1, CstrBinOp (CstrBopAdd, CstrVar 0, CstrNat 1)))) :: ct2, CstrVar 2, KdProper)), KdDerivBase ((BdKind (KdSubset (KdNat, PrBinRel (PrRelEq, CstrVar 1, CstrBinOp (CstrBopAdd, CstrVar 0, CstrNat 1)))) :: ct2, CstrVar 0, KdNat), KdDerivVar (BdKind (KdSubset (KdNat, PrBinRel (PrRelEq, CstrVar 1, CstrBinOp (CstrBopAdd, CstrVar 0, CstrNat 1)))) :: ct2, CstrVar 0, KdSubset (KdNat, PrBinRel (PrRelEq, CstrVar 2, CstrBinOp (CstrBopAdd, CstrVar 0, CstrNat 1))))))))
      val c3 = CstrSum (c1, c2)
      val ct3 = ct2
      val d3 = KdDerivSum ((ct3, c3, KdProper), d1, d2)
      val c4 = CstrAbs (KdNat, c3)
      val ct4 = tl ct3
      val d4 = KdDerivAbs ((ct4, c4, KdArrow (KdNat, KdProper)), KdWfDerivNat (ct4, KdNat), d3)
      val c5 = CstrAbs (KdProper, c4)
      val ct5 = tl ct4
      val d5 = KdDerivAbs ((ct5, c5, KdArrow (KdProper, KdArrow (KdNat, KdProper))), KdWfDerivProper (ct5, KdProper), d4)
      val c6 = CstrRec (KdArrow (KdProper, KdArrow (KdNat, KdProper)), c5)
      val ct6 = tl ct5
      val d6 = KdDerivRec ((ct6, c6, KdArrow (KdProper, KdArrow (KdNat, KdProper))), KdWfDerivArrow ((ct6, KdArrow (KdProper, KdArrow (KdNat, KdProper))), KdWfDerivProper (ct6, KdProper), KdWfDerivArrow ((ct6, KdArrow (KdNat, KdProper)), KdWfDerivNat (ct6, KdNat), KdWfDerivProper (ct6, KdProper))), d5)
      val list_cstr_body = CstrAbs (KdProper, CstrAbs (KdNat, CstrSum (CstrExists (KdSubset (KdUnit, PrBinRel (PrRelEq, CstrVar 1, CstrNat 0)), CstrTypeUnit), CstrExists (KdSubset (KdNat, PrBinRel (PrRelEq, CstrVar 1, CstrBinOp (CstrBopAdd, CstrVar 0, CstrNat 1))), CstrProd (CstrVar 2, CstrApp (CstrApp (CstrVar 3, CstrVar 2), CstrVar 0))))))
      fun unfold_list_cstr ty n =
        let
          val tmp1 = Passes.TermSubstConstr.subst_constr_in_constr_top list_cstr list_cstr_body
          val (_, body1) = extract_cstr_abs tmp1
          val tmp2 = Passes.TermSubstConstr.subst_constr_in_constr_top ty body1
          val (_, body2) = extract_cstr_abs tmp2
          val tmp3 = Passes.TermSubstConstr.subst_constr_in_constr_top n body2
        in
          tmp3
        end
      val plus_ty = CstrForall (KdNat, CstrForall (KdNat, CstrArrow (CstrProd (CstrTypeNat (CstrVar 1), CstrTypeNat (CstrVar 0)), CstrTypeNat (CstrBinOp (CstrBopAdd, CstrVar 1, CstrVar 0)), CstrTime "1.0")))
      val len_ty = CstrForall (KdProper, CstrForall (KdNat, CstrArrow (CstrApp (CstrApp (list_cstr, CstrVar 1), CstrVar 0), CstrTypeNat (CstrVar 0), CstrBinOp (CstrBopMult, CstrTime "3.0", CstrUnOp (CstrUopNat2Time, CstrVar 0)))))
      val c7 = CstrBinOp (CstrBopMult, CstrTime "3.0", CstrUnOp (CstrUopNat2Time, CstrVar 0))
      val ct7 = [BdKind KdNat, BdKind KdProper]
      val d7 = KdDerivBinOp ((ct7, c7, KdTimeFun 0), KdDerivTime (ct7, CstrTime "3.0", KdTimeFun 0), KdDerivUnOp ((ct7, CstrUnOp (CstrUopNat2Time, CstrVar 0), KdTimeFun 0), KdDerivVar (ct7, CstrVar 0, KdNat)))
      val c8 = CstrApp (CstrApp (list_cstr, CstrVar 1), CstrVar 0)
      val ct8 = ct7
      val d8 = KdDerivApp ((ct8, c8, KdProper), KdDerivApp ((ct8, CstrApp (list_cstr, CstrVar 1), KdArrow (KdNat, KdProper)), DerivationPasses.TypingDerivationShift.shift_kinding_derivation_above ct8 0 d6, KdDerivVar (ct8, CstrVar 1, KdProper)), KdDerivVar (ct8, CstrVar 0, KdNat))
      val c9 = CstrArrow (c8, CstrTypeNat (CstrVar 0), c7)
      val ct9 = ct8
      val d9 = KdDerivArrow ((ct9, c9, KdProper), d8, KdDerivTypeNat ((ct9, CstrTypeNat (CstrVar 0), KdProper), KdDerivVar (ct9, CstrVar 0, KdNat)), d7)
      val c10 = CstrForall (KdProper, CstrForall (KdNat, c9))
      val ct10 = tl (tl ct9)
      val d10 = KdDerivForall ((ct10, c10, KdProper), KdWfDerivProper (ct10, KdProper), KdDerivForall ((tl ct9, CstrForall (KdNat, c9), KdProper), KdWfDerivNat (tl ct9, KdNat), d9))
      fun app_type_fun ty1 cstr2 =
        let
          val (_, body1) = extract_cstr_forall ty1
          val tmp1 = Passes.TermSubstConstr.subst_constr_in_constr_top cstr2 body1
        in
          tmp1
        end
      val tm1 = TmNat 0
      val tm1_ctx = [BdType (CstrExists (KdSubset (KdUnit, PrBinRel (PrRelEq, CstrVar 2, CstrNat 0)), CstrTypeUnit)), BdType (CstrApp (CstrApp (list_cstr, CstrVar 1), CstrVar 0)), BdKind KdNat, BdKind KdProper, BdType len_ty, BdType plus_ty]
      val tm1_ty = CstrTypeNat (CstrNat 0)
      val tm1_ti = CstrTime "0.0"
      val tm1_rel = (tm1_ctx, tm1, tm1_ty, tm1_ti)
      val tm1_deriv = TyDerivNat tm1_rel
      val tm1_5_rel = (tm1_ctx, tm1, CstrTypeNat (CstrVar 2), CstrTime "0.0")
      val tm1_5_deriv = TyDerivSub (tm1_5_rel, tm1_deriv, TyEqDerivAssume (tm1_ctx, tm1_ty, #3 tm1_5_rel), PrDerivAdmit (tm1_ctx, PrBinRel (PrRelLe, #4 tm1_rel, #4 tm1_5_rel)))
      val tm2 = TmNat 1
      val tm2_ctx = [BdType (CstrProd (CstrVar 4, CstrApp (CstrApp (list_cstr, CstrVar 4), CstrVar 0))), BdKind (KdSubset (KdNat, PrBinRel (PrRelEq, CstrVar 3, CstrBinOp (CstrBopAdd, CstrVar 0, CstrNat 1)))), BdType (CstrExists (KdSubset (KdNat, PrBinRel (PrRelEq, CstrVar 2, CstrBinOp (CstrBopAdd, CstrVar 0, CstrNat 1))), CstrProd (CstrVar 3, CstrApp (CstrApp (list_cstr, CstrVar 3), CstrVar 0))))] @ (tl tm1_ctx)
      val tm2_ty = CstrTypeNat (CstrNat 1)
      val tm2_ti = CstrTime "0.0"
      val tm2_rel = (tm2_ctx, tm2, tm2_ty, tm2_ti)
      val tm2_deriv = TyDerivNat tm2_rel
      val tm3 = TmVar 6
      val tm3_ctx = tm2_ctx
      val tm3_ty = len_ty
      val tm3_ti = CstrTime "0.0"
      val tm3_rel = (tm3_ctx, tm3, tm3_ty, tm3_ti)
      val tm3_deriv = TyDerivVar tm3_rel
      val cstr1 = CstrVar 5
      val cstr1_ctx = tm3_ctx
      val cstr1_kd = KdProper
      val cstr1_rel = (cstr1_ctx, cstr1, cstr1_kd)
      val cstr1_deriv = KdDerivVar cstr1_rel
      val tm4 = TmCstrApp (tm3, cstr1)
      val tm4_ctx = tm3_ctx
      val tm4_ty = app_type_fun tm3_ty cstr1
      val tm4_ti = tm3_ti
      val tm4_rel = (tm4_ctx, tm4, tm4_ty, tm4_ti)
      val tm4_deriv = TyDerivCstrApp (tm4_rel, tm3_deriv, cstr1_deriv)
      val cstr2 = CstrVar 1
      val cstr2_ctx = tm4_ctx
      val cstr2_kd = KdNat
      val cstr2_rel = (cstr2_ctx, cstr2, cstr2_kd)
      val cstr2_deriv = KdDerivBase (cstr2_rel, KdDerivVar (cstr2_ctx, cstr2, KdSubset (KdNat, PrBinRel (PrRelEq, CstrVar 5, CstrBinOp (CstrBopAdd, CstrVar 0, CstrNat 1)))))
      val tm5 = TmCstrApp (tm4, cstr2)
      val tm5_ctx = cstr2_ctx
      val tm5_ty = app_type_fun tm4_ty cstr2
      val tm5_ti = tm4_ti
      val tm5_rel = (tm5_ctx, tm5, tm5_ty, tm5_ti)
      val tm5_deriv = TyDerivCstrApp (tm5_rel, tm4_deriv, cstr2_deriv)
      val tm6 = TmVar 0
      val tm6_ctx = tm5_ctx
      val tm6_ty = CstrProd (CstrVar 5, CstrApp (CstrApp (list_cstr, CstrVar 5), CstrVar 1))
      val tm6_ti = CstrTime "0.0"
      val tm6_rel = (tm6_ctx, tm6, tm6_ty, tm6_ti)
      val tm6_deriv = TyDerivVar tm6_rel
      val tm7 = TmSnd tm6
      val tm7_ctx = tm6_ctx
      val tm7_ty = CstrApp (CstrApp (list_cstr, CstrVar 5), CstrVar 1)
      val tm7_ti = tm6_ti
      val tm7_rel = (tm7_ctx, tm7, tm7_ty, tm7_ti)
      val tm7_deriv = TyDerivSnd (tm7_rel, tm6_deriv)
      val tm8 = TmApp (tm5, tm7)
      val tm8_ctx = tm7_ctx
      val tm8_ty = #2 (extract_cstr_arrow tm5_ty)
      val tm8_ti = CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, tm5_ti, tm7_ti), CstrTime "1.0"), #3 (extract_cstr_arrow tm5_ty))
      val tm8_rel = (tm8_ctx, tm8, tm8_ty, tm8_ti)
      val tm8_deriv = TyDerivApp (tm8_rel, tm5_deriv, tm7_deriv)
      val tm9 = TmPair (tm2, tm8)
      val tm9_ctx = tm8_ctx
      val tm9_ty = CstrProd (tm2_ty, tm8_ty)
      val tm9_ti = CstrBinOp (CstrBopAdd, tm2_ti, tm8_ti)
      val tm9_rel = (tm9_ctx, tm9, tm9_ty, tm9_ti)
      val tm9_deriv = TyDerivPair (tm9_rel, tm2_deriv, tm8_deriv)
      val cstr3 = CstrNat 1
      val cstr3_ctx = tm9_ctx
      val cstr3_kd = KdNat
      val cstr3_rel = (cstr3_ctx, cstr3, cstr3_kd)
      val cstr3_deriv = KdDerivNat cstr3_rel
      val tm10 = TmVar 7
      val tm10_ctx = cstr3_ctx
      val tm10_ty = plus_ty
      val tm10_ti = CstrTime "0.0"
      val tm10_rel = (tm10_ctx, tm10, tm10_ty, tm10_ti)
      val tm10_deriv = TyDerivVar tm10_rel
      val tm11 = TmCstrApp (tm10, cstr3)
      val tm11_ctx = tm10_ctx
      val tm11_ty = app_type_fun tm10_ty cstr3
      val tm11_ti = tm10_ti
      val tm11_rel = (tm11_ctx, tm11, tm11_ty, tm11_ti)
      val tm11_deriv = TyDerivCstrApp (tm11_rel, tm10_deriv, cstr3_deriv)
      val tm12 = TmCstrApp (tm11, cstr2)
      val tm12_ctx = tm11_ctx
      val tm12_ty = app_type_fun tm11_ty cstr2
      val tm12_ti = tm11_ti
      val tm12_rel = (tm12_ctx, tm12, tm12_ty, tm12_ti)
      val tm12_deriv = TyDerivCstrApp (tm12_rel, tm11_deriv, cstr2_deriv)
      val tm13 = TmApp (tm12, tm9)
      val tm13_ctx = tm12_ctx
      val tm13_ty = #2 (extract_cstr_arrow tm12_ty)
      val tm13_ti = CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, tm12_ti, tm9_ti), CstrTime "1.0"), #3 (extract_cstr_arrow tm12_ty))
      val tm13_rel = (tm13_ctx, tm13, tm13_ty, tm13_ti)
      val tm13_deriv = TyDerivApp (tm13_rel, tm12_deriv, tm9_deriv)
      val tm13_5_rel = (tm13_ctx, tm13, CstrTypeNat (CstrVar 4), CstrBinOp (CstrBopMult, CstrTime "3.0", CstrUnOp (CstrUopNat2Time, CstrVar 4)))
      val tm13_5_deriv = TyDerivSub (tm13_5_rel, tm13_deriv, TyEqDerivAssume (tm13_ctx, tm13_ty, #3 tm13_5_rel), PrDerivAdmit (tm13_ctx, PrBinRel (PrRelLe, #4 tm13_rel, #4 tm13_5_rel)))
      val tm14 = TmVar 0
      val tm14_ctx = tl (tl tm13_ctx)
      val tm14_ty = CstrExists (KdSubset (KdNat, PrBinRel (PrRelEq, CstrVar 3, CstrBinOp (CstrBopAdd, CstrVar 0, CstrNat 1))), CstrProd (CstrVar 4, CstrApp (CstrApp (list_cstr, CstrVar 4), CstrVar 0)))
      val tm14_ti = CstrTime "0.0"
      val tm14_rel = (tm14_ctx, tm14, tm14_ty, tm14_ti)
      val tm14_deriv = TyDerivVar tm14_rel
      val tm15 = TmUnpack (tm14, tm13)
      val tm15_ctx = tm14_ctx
      val tm15_ty = CstrTypeNat (CstrVar 2)
      val tm15_ti = CstrBinOp (CstrBopAdd, tm14_ti, CstrBinOp (CstrBopMult, CstrTime "3.0", CstrUnOp (CstrUopNat2Time, CstrVar 2)))
      val tm15_rel = (tm15_ctx, tm15, tm15_ty, tm15_ti)
      val tm15_deriv = TyDerivUnpack (tm15_rel, tm14_deriv, tm13_5_deriv)
      val tm16 = TmVar 0
      val tm16_ctx = tl tm15_ctx
      val tm16_ty = CstrApp (CstrApp (list_cstr, CstrVar 2), CstrVar 1)
      val tm16_ti = CstrTime "0.0"
      val tm16_rel = (tm16_ctx, tm16, tm16_ty, tm16_ti)
      val tm16_deriv = TyDerivVar tm16_rel
      val tm17 = TmUnfold tm16
      val tm17_ctx = tm16_ctx
      val tm17_ty = unfold_list_cstr (CstrVar 2) (CstrVar 1)
      val tm17_ti = tm16_ti
      val tm17_rel = (tm17_ctx, tm17, tm17_ty, tm17_ti)
      val tm17_deriv = TyDerivUnfold (tm17_rel, tm16_deriv)
      val tm18 = TmCase (tm17, tm1, tm15)
      val tm18_ctx = tm17_ctx
      val tm18_ty = CstrTypeNat (CstrVar 1)
      val tm18_ti = CstrBinOp (CstrBopAdd, tm17_ti, CstrBinOp (CstrBopMax, CstrTime "0.0", CstrBinOp (CstrBopAdd, CstrTime "0.0", CstrBinOp (CstrBopMult, CstrTime "3.0", CstrUnOp (CstrUopNat2Time, CstrVar 1)))))
      val tm18_rel = (tm18_ctx, tm18, tm18_ty, tm18_ti)
      val tm18_deriv = TyDerivCase (tm18_rel, tm17_deriv, tm1_5_deriv, tm15_deriv)
      val tm18_5_rel = (tm18_ctx, tm18, tm18_ty, CstrBinOp (CstrBopMult, CstrTime "3.0", CstrUnOp (CstrUopNat2Time, CstrVar 1)))
      val tm18_5_deriv = TyDerivSub (tm18_5_rel, tm18_deriv, TyEqDerivAssume (tm18_ctx, tm18_ty, #3 tm18_5_rel), PrDerivAdmit (tm18_ctx, PrBinRel (PrRelLe, #4 tm18_rel, #4 tm18_5_rel)))
      val tm19 = TmAbs (CstrApp (CstrApp (list_cstr, CstrVar 1), CstrVar 0), tm18)
      val tm19_ctx = tl tm18_ctx
      val tm19_ty = CstrArrow (CstrApp (CstrApp (list_cstr, CstrVar 1), CstrVar 0), CstrTypeNat (CstrVar 0), CstrBinOp (CstrBopMult, CstrTime "3.0", CstrUnOp (CstrUopNat2Time, CstrVar 0)))
      val tm19_ti = CstrTime "0.0"
      val tm19_rel = (tm19_ctx, tm19, tm19_ty, tm19_ti)
      val tm19_deriv = TyDerivAbs (tm19_rel, KdDerivApp ((tm19_ctx, CstrApp (CstrApp (list_cstr, CstrVar 1), CstrVar 0), KdProper), KdDerivApp ((tm19_ctx, CstrApp (list_cstr, CstrVar 1), KdArrow (KdNat, KdProper)), DerivationPasses.TypingDerivationShift.shift_kinding_derivation_above tm19_ctx 0 d6, KdDerivVar (tm19_ctx, CstrVar 1, KdProper)), KdDerivVar (tm19_ctx, CstrVar 0, KdNat)), tm18_5_deriv)
      val tm20 = TmCstrAbs (KdNat, tm19)
      val tm20_ctx = tl tm19_ctx
      val tm20_ty = CstrForall (KdNat, tm19_ty)
      val tm20_ti = CstrTime "0.0"
      val tm20_rel = (tm20_ctx, tm20, tm20_ty, tm20_ti)
      val tm20_deriv = TyDerivCstrAbs (tm20_rel, KdWfDerivNat (tm20_ctx, KdNat), tm19_deriv)
      val tm21 = TmCstrAbs (KdProper, tm20)
      val tm21_ctx = tl tm20_ctx
      val tm21_ty = CstrForall (KdProper, tm20_ty)
      val tm21_ti = CstrTime "0.0"
      val tm21_rel = (tm21_ctx, tm21, tm21_ty, tm21_ti)
      val tm21_deriv = TyDerivCstrAbs (tm21_rel, KdWfDerivProper (tm21_ctx, KdProper), tm20_deriv)
      val tm22 = TmRec (len_ty, tm21)
      val tm22_ctx = tl tm21_ctx
      val tm22_ty = len_ty
      val tm22_ti = CstrTime "0.0"
      val tm22_rel = (tm22_ctx, tm22, tm22_ty, tm22_ti)
      val tm22_deriv = TyDerivRec (tm22_rel, DerivationPasses.TypingDerivationShift.shift_kinding_derivation_above tm22_ctx 0 d10, tm21_deriv)
      val _ = println (str_bool (MicroTiMLChecker.check_typing_derivation tm22_deriv))
      val tm22_deriv_new = DerivationPasses.ANF.normalize_derivation tm22_deriv
      val _ = println (str_bool (MicroTiMLChecker.check_typing_derivation tm22_deriv_new))
      val tm22_deriv_clo = #1 (DerivationPasses.CloConv.transform_typing_derivation (tm22_deriv_new, ()))
      (*val _ = println (snd (Passes.Printer.transform_term (#2 (extract_tyrel tm22_deriv_new), ["plus"])))
      val _ = println (snd (Passes.Printer.transform_term (#2 (extract_tyrel tm22_deriv_clo), ["plus"])))*)
    in
      tm22_deriv
    end

  fun test_fac () =
    let
      val bool_cstr = CstrAbs (KdBool, CstrSum (CstrExists (KdSubset (KdUnit, PrBinRel (PrRelEq, CstrVar 1, CstrTrue)), CstrTypeUnit), CstrExists (KdSubset (KdUnit, PrBinRel (PrRelEq, CstrVar 1, CstrFalse)), CstrTypeUnit)))
      val bool_cstr_body = CstrSum (CstrExists (KdSubset (KdUnit, PrBinRel (PrRelEq, CstrVar 1, CstrTrue)), CstrTypeUnit), CstrExists (KdSubset (KdUnit, PrBinRel (PrRelEq, CstrVar 1, CstrFalse)), CstrTypeUnit))
      val is_zero_ty = CstrForall (KdNat, CstrArrow (CstrTypeNat (CstrVar 0), Passes.TermSubstConstr.subst_constr_in_constr_top (CstrBinOp (CstrBopEq, CstrVar 0, CstrNat 0)) bool_cstr_body, CstrTime "1.0"))
      val minus_ty = CstrForall (KdNat, CstrForall (KdNat, CstrArrow (CstrProd (CstrTypeNat (CstrVar 1), CstrTypeNat (CstrVar 0)), CstrTypeNat (CstrBinOp (CstrBopDiff, CstrVar 1, CstrVar 0)), CstrTime "1.0")))
      val mult_ty = CstrArrow (CstrProd (CstrExists (KdNat, CstrTypeNat (CstrVar 0)), CstrExists (KdNat, CstrTypeNat (CstrVar 0))), CstrExists (KdNat, CstrTypeNat (CstrVar 0)), CstrTime "1.0")
      val fac_ty = CstrForall (KdNat, CstrArrow (CstrTypeNat (CstrVar 0), CstrExists (KdNat, CstrTypeNat (CstrVar 0)), CstrBinOp (CstrBopMult, CstrTime "7.0", CstrUnOp (CstrUopNat2Time, CstrVar 0))))
      val tm1 = TmPack (CstrNat 1, TmNat 1)
      val tm1_ctx = [BdType (CstrExists (KdSubset (KdUnit, PrBinRel (PrRelEq, CstrBinOp (CstrBopEq, CstrVar 2, CstrNat 0), CstrTrue)), CstrTypeUnit)), BdType (CstrTypeNat (CstrVar 0)), BdKind KdNat, BdType fac_ty, BdType mult_ty, BdType minus_ty, BdType is_zero_ty]
      val tm1_rel = (tm1_ctx, tm1, CstrExists (KdNat, CstrTypeNat (CstrVar 0)), CstrTime "0.0")
      val tm1_deriv = TyDerivPack (tm1_rel, KdDerivExists ((tm1_ctx, CstrExists (KdNat, CstrTypeNat (CstrVar 0)), KdProper), KdWfDerivNat (tm1_ctx, KdNat), KdDerivTypeNat ((BdKind KdNat :: tm1_ctx, CstrTypeNat (CstrVar 0), KdProper), KdDerivVar (BdKind KdNat :: tm1_ctx, CstrVar 0, KdNat))), KdDerivNat (tm1_ctx, CstrNat 1, KdNat), TyDerivNat (tm1_ctx, TmNat 1, CstrTypeNat (CstrNat 1), CstrTime "0.0"))
      val tm2 = TmPair (TmVar 1, TmNat 1)
      val tm2_ctx = [BdType (CstrExists (KdSubset (KdUnit, PrBinRel (PrRelEq, CstrBinOp (CstrBopEq, CstrVar 2, CstrNat 0), CstrFalse)), CstrTypeUnit)), BdType (CstrTypeNat (CstrVar 0)), BdKind KdNat, BdType fac_ty, BdType mult_ty, BdType minus_ty, BdType is_zero_ty]
      val tm2_rel = (tm2_ctx, tm2, CstrProd (CstrTypeNat (CstrVar 2), CstrTypeNat (CstrNat 1)), CstrBinOp (CstrBopAdd, CstrTime "0.0", CstrTime "0.0"))
      val tm2_deriv = TyDerivPair (tm2_rel, TyDerivVar (tm2_ctx, TmVar 1, CstrTypeNat (CstrVar 2), CstrTime "0.0"), TyDerivNat (tm2_ctx, TmNat 1, CstrTypeNat (CstrNat 1), CstrTime "0.0"))
      val tm3 = TmCstrApp (TmCstrApp (TmVar 5, CstrVar 2), CstrNat 1)
      val tm3_ctx = tm2_ctx
      val tm3_rel = (tm3_ctx, tm3, CstrArrow (CstrProd (CstrTypeNat (CstrVar 2), CstrTypeNat (CstrNat 1)), CstrTypeNat (CstrBinOp (CstrBopDiff, CstrVar 2, CstrNat 1)), CstrTime "1.0"), CstrTime "0.0")
      val tm3_deriv = TyDerivCstrApp (tm3_rel, TyDerivCstrApp ((tm3_ctx, TmCstrApp (TmVar 5, CstrVar 2), CstrForall (KdNat, CstrArrow (CstrProd (CstrTypeNat (CstrVar 3), CstrTypeNat (CstrVar 0)), CstrTypeNat (CstrBinOp (CstrBopDiff, CstrVar 3, CstrVar 0)), CstrTime "1.0")), CstrTime "0.0"), TyDerivVar (tm3_ctx, TmVar 5, minus_ty, CstrTime "0.0"), KdDerivVar (tm3_ctx, CstrVar 2, KdNat)), KdDerivNat (tm3_ctx, CstrNat 1, KdNat))
      val tm4 = TmApp (tm3, tm2)
      val tm4_ctx = tm3_ctx
      val tm4_rel = (tm4_ctx, tm4, CstrTypeNat (CstrBinOp (CstrBopDiff, CstrVar 2, CstrNat 1)), CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrTime "0.0", CstrBinOp (CstrBopAdd, CstrTime "0.0", CstrTime "0.0")), CstrTime "1.0"), CstrTime "1.0"))
      val tm4_deriv = TyDerivApp (tm4_rel, tm3_deriv, tm2_deriv)
      val tm5 = TmCstrApp (TmVar 3, CstrBinOp (CstrBopDiff, CstrVar 2, CstrNat 1))
      val tm5_ctx = tm4_ctx
      val tm5_rel = (tm5_ctx, tm5, CstrArrow (CstrTypeNat (CstrBinOp (CstrBopDiff, CstrVar 2, CstrNat 1)), CstrExists (KdNat, CstrTypeNat (CstrVar 0)), CstrBinOp (CstrBopMult, CstrTime "7.0", CstrUnOp (CstrUopNat2Time, CstrBinOp (CstrBopDiff, CstrVar 2, CstrNat 1)))), CstrTime "0.0")
      val tm5_deriv = TyDerivCstrApp (tm5_rel, TyDerivVar (tm5_ctx, TmVar 3, fac_ty, CstrTime "0.0"), KdDerivBinOp ((tm5_ctx, CstrBinOp (CstrBopDiff, CstrVar 2, CstrNat 1), KdNat), KdDerivVar (tm5_ctx, CstrVar 2, KdNat), KdDerivNat (tm5_ctx, CstrNat 1, KdNat)))
      val tm6 = TmApp (tm5, tm4)
      val tm6_ctx = tm5_ctx
      val tm6_rel = (tm6_ctx, tm6, CstrExists (KdNat, CstrTypeNat (CstrVar 0)), CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrTime "0.0", CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrTime "0.0", CstrBinOp (CstrBopAdd, CstrTime "0.0", CstrTime "0.0")), CstrTime "1.0"), CstrTime "1.0")), CstrTime "1.0"), CstrBinOp (CstrBopMult, CstrTime "7.0", CstrUnOp (CstrUopNat2Time, CstrBinOp (CstrBopDiff, CstrVar 2, CstrNat 1)))))
      val tm6_deriv = TyDerivApp (tm6_rel, tm5_deriv, tm4_deriv)
      val tm7 = TmPack (CstrVar 2, TmVar 1)
      val tm7_ctx = tm6_ctx
      val tm7_rel = (tm7_ctx, tm7, CstrExists (KdNat, CstrTypeNat (CstrVar 0)), CstrTime "0.0")
      val tm7_deriv = TyDerivPack (tm7_rel, KdDerivExists ((tm7_ctx, CstrExists (KdNat, CstrTypeNat (CstrVar 0)), KdProper), KdWfDerivNat (tm7_ctx, KdNat), KdDerivTypeNat ((BdKind KdNat :: tm7_ctx, CstrTypeNat (CstrVar 0), KdProper), KdDerivVar (BdKind KdNat :: tm7_ctx, CstrVar 0, KdNat))), KdDerivVar (tm7_ctx, CstrVar 2, KdNat), TyDerivVar (tm7_ctx, TmVar 1, CstrTypeNat (CstrVar 2), CstrTime "0.0"))
      val tm8 = TmPair (tm7, tm6)
      val tm8_ctx = tm7_ctx
      val tm8_rel = (tm8_ctx, tm8, CstrProd (CstrExists (KdNat, CstrTypeNat (CstrVar 0)), CstrExists (KdNat, CstrTypeNat (CstrVar 0))), CstrBinOp (CstrBopAdd, CstrTime "0.0", CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrTime "0.0", CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrTime "0.0", CstrBinOp (CstrBopAdd, CstrTime "0.0", CstrTime "0.0")), CstrTime "1.0"), CstrTime "1.0")), CstrTime "1.0"), CstrBinOp (CstrBopMult, CstrTime "7.0", CstrUnOp (CstrUopNat2Time, CstrBinOp (CstrBopDiff, CstrVar 2, CstrNat 1))))))
      val tm8_deriv = TyDerivPair (tm8_rel, tm7_deriv, tm6_deriv)
      val tm9 = TmApp (TmVar 4, tm8)
      val tm9_ctx = tm8_ctx
      val tm9_rel = (tm9_ctx, tm9, CstrExists (KdNat, CstrTypeNat (CstrVar 0)), CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrTime "0.0", CstrBinOp (CstrBopAdd, CstrTime "0.0", CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrTime "0.0", CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrTime "0.0", CstrBinOp (CstrBopAdd, CstrTime "0.0", CstrTime "0.0")), CstrTime "1.0"), CstrTime "1.0")), CstrTime "1.0"), CstrBinOp (CstrBopMult, CstrTime "7.0", CstrUnOp (CstrUopNat2Time, CstrBinOp (CstrBopDiff, CstrVar 2, CstrNat 1)))))), CstrTime "1.0"), CstrTime "1.0"))
      val tm9_deriv = TyDerivApp (tm9_rel, TyDerivVar (tm9_ctx, TmVar 4, mult_ty, CstrTime "0.0"), tm8_deriv)
      val tm10 = TmCstrApp (TmVar 5, CstrVar 1)
      val tm10_ctx = List.tl tm9_ctx
      val tm10_rel = (tm10_ctx, tm10, CstrArrow (CstrTypeNat (CstrVar 1), Passes.TermSubstConstr.subst_constr_in_constr_top (CstrBinOp (CstrBopEq, CstrVar 1, CstrNat 0)) bool_cstr_body, CstrTime "1.0"), CstrTime "0.0")
      val tm10_deriv = TyDerivCstrApp (tm10_rel, TyDerivVar (tm10_ctx, TmVar 5, is_zero_ty, CstrTime "0.0"), KdDerivVar (tm10_ctx, CstrVar 1, KdNat))
      val tm11 = TmApp (tm10, TmVar 0)
      val tm11_ctx = tm10_ctx
      val tm11_rel = (tm11_ctx, tm11, Passes.TermSubstConstr.subst_constr_in_constr_top (CstrBinOp (CstrBopEq, CstrVar 1, CstrNat 0)) bool_cstr_body, CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrTime "0.0", CstrTime "0.0"), CstrTime "1.0"), CstrTime "1.0"))
      val tm11_deriv = TyDerivApp (tm11_rel, tm10_deriv, TyDerivVar (tm11_ctx, TmVar 0, CstrTypeNat (CstrVar 1), CstrTime "0.0"))
      val tm12 = TmCase (tm11, tm1, tm9)
      val tm12_ctx = tm11_ctx
      val tm12_rel = (tm12_ctx, tm12, CstrExists (KdNat, CstrTypeNat (CstrVar 0)), CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrTime "0.0", CstrTime "0.0"), CstrTime "1.0"), CstrTime "1.0"), CstrBinOp (CstrBopMax, CstrTime "0.0", CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrTime "0.0", CstrBinOp (CstrBopAdd, CstrTime "0.0", CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrTime "0.0", CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrTime "0.0", CstrBinOp (CstrBopAdd, CstrTime "0.0", CstrTime "0.0")), CstrTime "1.0"), CstrTime "1.0")), CstrTime "1.0"), CstrBinOp (CstrBopMult, CstrTime "7.0", CstrUnOp (CstrUopNat2Time, CstrBinOp (CstrBopDiff, CstrVar 1, CstrNat 1)))))), CstrTime "1.0"), CstrTime "1.0"))))
      val tm12_deriv = TyDerivCase (tm12_rel, tm11_deriv, tm1_deriv, tm9_deriv)
      val tm125_rel = (tm12_ctx, tm12, #3 tm12_rel, CstrBinOp (CstrBopMult, CstrTime "7.0", CstrUnOp (CstrUopNat2Time, CstrVar 1)))
      val tm125_deriv = TyDerivSub (tm125_rel, tm12_deriv, TyEqDerivAssume (tm12_ctx, #3 tm12_rel, #3 tm125_rel), PrDerivAdmit (tm12_ctx, PrBinRel (PrRelLe, #4 tm12_rel, #4 tm125_rel)))
      val tm13 = TmAbs (CstrTypeNat (CstrVar 0), tm12)
      val tm13_ctx = List.tl tm12_ctx
      val tm13_rel = (tm13_ctx, tm13, CstrArrow (CstrTypeNat (CstrVar 0), CstrExists (KdNat, CstrTypeNat (CstrVar 0)), CstrBinOp (CstrBopMult, CstrTime "7.0", CstrUnOp (CstrUopNat2Time, CstrVar 0))), CstrTime "0.0")
      val tm13_deriv = TyDerivAbs (tm13_rel, KdDerivTypeNat ((tm13_ctx, CstrTypeNat (CstrVar 0), KdProper), KdDerivVar (tm13_ctx, CstrVar 0, KdNat)), tm125_deriv)
      val tm14 = TmCstrAbs (KdNat, tm13)
      val tm14_ctx = List.tl tm13_ctx
      val tm14_rel = (tm14_ctx, tm14, fac_ty, CstrTime "0.0")
      val tm14_deriv = TyDerivCstrAbs (tm14_rel, KdWfDerivNat (tm14_ctx, KdNat), tm13_deriv)
      val tm15 = TmRec (fac_ty, tm14)
      val tm15_ctx = List.tl tm14_ctx
      val tm15_rel = (tm15_ctx, tm15, fac_ty, CstrTime "0.0")
      val tm15_deriv = TyDerivRec (tm15_rel, KdDerivForall ((tm15_ctx, fac_ty, KdProper), KdWfDerivNat (tm15_ctx, KdNat), KdDerivArrow ((BdKind KdNat :: tm15_ctx, CstrArrow (CstrTypeNat (CstrVar 0), CstrExists (KdNat, CstrTypeNat (CstrVar 0)), CstrBinOp (CstrBopMult, CstrTime "7.0", CstrUnOp (CstrUopNat2Time, CstrVar 0))), KdProper), KdDerivTypeNat ((BdKind KdNat :: tm15_ctx, CstrTypeNat (CstrVar 0), KdProper), KdDerivVar (BdKind KdNat :: tm15_ctx, CstrVar 0, KdNat)), KdDerivExists ((BdKind KdNat :: tm15_ctx, CstrExists (KdNat, CstrTypeNat (CstrVar 0)), KdProper), KdWfDerivNat (BdKind KdNat :: tm15_ctx, KdNat), KdDerivTypeNat ((BdKind KdNat :: BdKind KdNat :: tm15_ctx, CstrTypeNat (CstrVar 0), KdProper), KdDerivVar (BdKind KdNat :: BdKind KdNat :: tm15_ctx, CstrVar 0, KdNat))), KdDerivBinOp ((BdKind KdNat :: tm15_ctx, CstrBinOp (CstrBopMult, CstrTime "7.0", CstrUnOp (CstrUopNat2Time, CstrVar 0)), KdTimeFun 0), KdDerivTime (BdKind KdNat :: tm15_ctx, CstrTime "7.0", KdTimeFun 0), KdDerivUnOp ((BdKind KdNat :: tm15_ctx, CstrUnOp (CstrUopNat2Time, CstrVar 0), KdTimeFun 0), KdDerivVar (BdKind KdNat :: tm15_ctx, CstrVar 0, KdNat))))), tm14_deriv)
      val _ = println (str_bool (MicroTiMLChecker.check_typing_derivation tm15_deriv))
      val tm15_deriv_new = DerivationPasses.ANF.normalize_derivation tm15_deriv
      val _ = println (str_bool (MicroTiMLChecker.check_typing_derivation tm15_deriv_new))
      (*val tm15_deriv_clo = #1 (DerivationPasses.CloConv.transform_typing_derivation (tm15_deriv, ()))*)
    in
      tm15_deriv
    end

  fun main (prog : string, args : string list) =
    let
      val _ = test_len ()
      val _ = test_fac ()
    in
      0
    end*)
end
