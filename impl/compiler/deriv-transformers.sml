functor DerivTransformersFun(MicroTiMLDef : SIG_MICRO_TIML_DEF) : SIG_DERIV_TRANSFOMRERS =
struct
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

structure DerivAssembler =
struct
fun as_KdEqKArrow ke1 ke2 =
  let
      val jke1 = extract_judge_kdeq ke1
      val jke2 = extract_judge_kdeq ke2
  in
      (#1 jke1, KArrow (#2 jke1, #2 jke2), KArrow (#3 jke1, #3 jke2))
  end

fun as_KdEqKSubset ke pr =
  let
      val jke = extract_judge_kdeq ke
      val jpr = extract_judge_proping pr
      val (_, p1, p2) = extract_p_bin_conn (#2 jpr)
  in
      (#1 jke, KSubset (#2 jke, p1), KSubset (#3 jke, p2))
  end

fun as_WfPropQuan q b wp =
  let
      val jwp = extract_judge_wfprop wp
  in
      (tl $ #1 jwp, PQuan (q, b, #2 jwp))
  end

fun as_WfPropBinPred opr kd1 kd2 =
  let
      val jkd1 = extract_judge_kinding kd1
      val jkd2 = extract_judge_kinding kd2
  in
      (#1 jkd1, PBinPred (opr, #2 jkd1, #2 jkd2))
  end

fun as_WfPropNot wp =
  let
      val jwp = extract_judge_wfprop wp
  in
      (#1 jwp, PNot (#2 jwp))
  end

fun as_WfPropBinConn opr wp1 wp2 =
  let
      val jwp1 = extract_judge_wfprop wp1
      val jwp2 = extract_judge_wfprop wp2
  in
      (#1 jwp1, PBinConn (opr, #2 jwp1, #2 jwp2))
  end

fun as_WfKdSubset wk wp =
  let
      val jwk = extract_judge_wfkind wk
      val jwp = extract_judge_wfprop wp
  in
      (#1 jwk, KSubset (#2 jwk, #2 jwp))
  end

fun as_WfKdArrow wk1 wk2 =
  let
      val jwk1 = extract_judge_wfkind wk1
      val jwk2 = extract_judge_wfkind wk2
  in
      (#1 jwk1, KArrow (#2 jwk1, #2 jwk2))
  end

fun as_KdEq kd ke =
  let
      val jkd = extract_judge_kinding kd
      val jke = extract_judge_kdeq ke
  in
      (#1 jkd, #2 jkd, #2 jke)
  end

fun as_KdRef kd =
  let
      val jkd = extract_judge_kinding kd
  in
      (#1 jkd, CRef (#2 jkd), KType)
  end

fun as_KdRec wk kd =
  let
      val jwk = extract_judge_wfkind wk
      val jkd = extract_judge_kinding kd
  in
      (#1 jwk, CRec (#2 jwk, #2 jkd), #2 jwk)
  end

fun as_KdQuan q wk kd =
  let
      val jwk = extract_judge_wfkind wk
      val jkd = extract_judge_kinding kd
  in
      (#1 jwk, CQuan (q, #2 jwk, #2 jkd), KType)
  end

fun as_KdTimeApp kd1 kd2 =
  let
      val jkd1 = extract_judge_kinding kd1
      val arity = extract_k_time_fun (#3 jkd1)
      val jkd2 = extract_judge_kinding kd2
  in
      (#1 jkd1, CTimeApp (arity - 1, #2 jkd1, #2 jkd2), KTimeFun (arity - 1))
  end

fun as_KdTimeAbs kd =
  let
      val jkd = extract_judge_kinding kd
      val arity = extract_k_time_fun (#3 jkd)
  in
      (tl $ #1 jkd, CTimeAbs (#2 jkd), KTimeFun (arity + 1))
  end

fun as_KdApp kd1 kd2 =
  let
      val jkd1 = extract_judge_kinding kd1
      val jkd2 = extract_judge_kinding kd2
      val (k1, k2) = extract_k_arrow (#3 jkd1)
  in
      (#1 jkd1, CApp (#2 jkd1, #2 jkd2), k2)
  end

fun as_KdAbs wk kd =
  let
      val jwk = extract_judge_wfkind wk
      val jkd = extract_judge_kinding kd
  in
      (#1 jwk, CAbs (#2 jkd), KArrow (#2 jwk, shift_c_k ~1 0 (#3 jkd)))
  end

fun as_KdArrow kd1 kd2 kd3 =
  let
      val jkd1 = extract_judge_kinding kd1
      val jkd2 = extract_judge_kinding kd2
      val jkd3 = extract_judge_kinding kd3
  in
      (#1 jkd1, CArrow (#2 jkd1, #2 jkd2, #2 jkd3), KType)
  end

fun as_KdIte kd1 kd2 kd3 =
  let
      val jkd1 = extract_judge_kinding kd1
      val jkd2 = extract_judge_kinding kd2
      val jkd3 = extract_judge_kinding kd3
  in
      (#1 jkd1, CIte (#2 jkd1, #2 jkd2, #2 jkd3), #3 jkd2)
  end

fun as_KdBinOp opr kd1 kd2 =
  let
      val jkd1 = extract_judge_kinding kd1
      val jkd2 = extract_judge_kinding kd2
  in
      (#1 jkd1, CBinOp (opr, #2 jkd1, #2 jkd2), cbinop_result_kind opr)
  end

fun as_KdUnOp opr kd =
  let
      val jkd = extract_judge_kinding kd
  in
      (#1 jkd, CUnOp (opr, #2 jkd), cunop_result_kind opr)
  end

fun as_TyEqRef te =
  let
      val jte = extract_judge_tyeq te
  in
      (#1 jte, CRef (#2 jte), CRef (#3 jte))
  end

fun as_TyEqRec ke te =
  let
      val jke = extract_judge_kdeq ke
      val jte = extract_judge_tyeq te
  in
      (#1 jke, CRec (#2 jke, #2 jte), CRec (#3 jke, #3 jte))
  end

fun as_TyEqBetaRev te1 te2 te3 =
  let
      val jte1 = extract_judge_tyeq te1
      val jte2 = extract_judge_tyeq te2
      val jte3 = extract_judge_tyeq te3
  in
      (#1 jte1, #2 jte3, CApp (#3 jte1, #3 jte2))
  end

fun as_TyEqBeta te1 te2 te3 =
  let
      val jte1 = extract_judge_tyeq te1
      val jte2 = extract_judge_tyeq te2
      val jte3 = extract_judge_tyeq te3
  in
      (#1 jte1, CApp (#2 jte1, #2 jte2), #3 jte3)
  end

fun as_TyEqNat kd1 kd2 pr =
  let
      val jpr = extract_judge_proping pr
      val (_, i1, i2) = extract_p_bin_pred (#2 jpr)
  in
      (#1 jpr, i1, i2)
  end

fun as_TyEqTimeApp arity te1 te2 =
  let
      val jte1 = extract_judge_tyeq te1
      val jte2 = extract_judge_tyeq te2
  in
      (#1 jte1, CTimeApp (arity, #2 jte1, #2 jte2), CTimeApp (arity, #3 jte1, #3 jte2))
  end

fun as_TyEqQuan q ke te =
  let
      val jke = extract_judge_kdeq ke
      val jte = extract_judge_tyeq te
  in
      (#1 jke, CQuan (q, #2 jke, #2 jte), CQuan (q, #3 jke, #3 jte))
  end

fun as_TyEqApp te1 te2 =
  let
      val jte1 = extract_judge_tyeq te1
      val jte2 = extract_judge_tyeq te2
  in
      (#1 jte1, CApp (#2 jte1, #2 jte2), CApp (#3 jte1, #3 jte2))
  end

fun as_TyEqArrow te1 pr te2 =
  let
      val jte1 = extract_judge_tyeq te1
      val jpr = extract_judge_proping pr
      val jte2 = extract_judge_tyeq te2
      val (_, i1, i2) = extract_p_bin_pred (#2 jpr)
  in
      (#1 jte1, CArrow (#2 jte1, i1, #2 jte2), CArrow (#3 jte1, i2, #3 jte2))
  end

fun as_TyEqIte te1 te2 te3 =
  let
      val jte1 = extract_judge_tyeq te1
      val jte2 = extract_judge_tyeq te2
      val jte3 = extract_judge_tyeq te3
  in
      (#1 jte1, CIte (#2 jte1, #2 jte2, #2 jte3), CIte (#3 jte1, #3 jte2, #3 jte3))
  end

fun as_TyEqBinOp opr te1 te2 =
  let
      val jte1 = extract_judge_tyeq te1
      val jte2 = extract_judge_tyeq te2
  in
      (#1 jte1, CBinOp (opr, #2 jte1, #2 jte2), CBinOp (opr, #3 jte1, #3 jte2))
  end

fun as_TyEqUnOp opr te =
  let
      val jte = extract_judge_tyeq te
  in
      (#1 jte, CUnOp (opr, #2 jte), CUnOp (opr, #3 jte))
  end

fun as_TyApp ty1 ty2 =
  let
      val jty1 = extract_judge_typing ty1
      val jty2 = extract_judge_typing ty2
      val (t1, i, t2) = extract_c_arrow (#3 jty1)
  in
      (#1 jty1, EApp (#2 jty1, #2 jty2), t2, Tadd (Tadd (Tadd (#4 jty1, #4 jty2), T1), i))
  end

fun as_TyAppK ty1 ty2 =
  let
      val jty1 = extract_judge_typing ty1
      val jty2 = extract_judge_typing ty2
      val (t1, i, t2) = extract_c_arrow (#3 jty1)
  in
      (#1 jty1, EApp (#2 jty1, #2 jty2), t2, Tadd (Tadd (#4 jty1, #4 jty2), i))
  end

fun as_TyAbs kd ty =
  let
      val jkd = extract_judge_kinding kd
      val jty = extract_judge_typing ty
  in
      ((#1 jkd, tl o snd $ #1 jty), EAbs (#2 jty), CArrow (#2 jkd, #4 jty, #3 jty), T0)
  end

fun as_TySubTy ty te =
  let
      val jty = extract_judge_typing ty
      val jte = extract_judge_tyeq te
  in
      (#1 jty, #2 jty, #3 jte, #4 jty)
  end

fun as_TySubTi ty pr =
  let
      val jty = extract_judge_typing ty
      val jpr = extract_judge_proping pr
      val (_, i1, i2) = extract_p_bin_pred (#2 jpr)
  in
      (#1 jty, #2 jty, #3 jty, i2)
  end

fun as_TyWrite ty1 ty2 =
  let
      val jty1 = extract_judge_typing ty1
      val jty2 = extract_judge_typing ty2
  in
      (#1 jty1, EWrite (#2 jty1, #2 jty2), CTypeUnit, Tadd (#4 jty1, #4 jty2))
  end

fun as_TyRead ty =
  let
      val jty = extract_judge_typing ty
      val t = extract_c_ref (#3 jty)
  in
      (#1 jty, ERead (#2 jty), t, #4 jty)
  end

fun as_TyNew ty =
  let
      val jty = extract_judge_typing ty
  in
      (#1 jty, ENew (#2 jty), CRef (#3 jty), #4 jty)
  end

fun as_TyCase ty1 ty2 ty3 =
  let
      val jty1 = extract_judge_typing ty1
      val jty2 = extract_judge_typing ty2
      val jty3 = extract_judge_typing ty3
  in
      (#1 jty1, ECase (#2 jty1, #2 jty2, #2 jty3), #3 jty2, Tadd (#4 jty1, Tmax (#4 jty2, #4 jty3)))
  end

fun as_TyInj inj ty kd =
  let
      val jty = extract_judge_typing ty
      val jkd = extract_judge_kinding kd
  in
      (#1 jty, EInj (inj, #2 jty), case inj of InjInl => CSum (#3 jty, #2 jkd) | InjInr => CSum (#2 jkd, #3 jty), #4 jty)
  end

fun as_TyProj p ty =
  let
      val jty = extract_judge_typing ty
      val (t1, t2) = extract_c_prod (#3 jty)
  in
      (#1 jty, EProj (p, #2 jty), case p of ProjFst => t1 | ProjSnd => t2, #4 jty)
  end

fun as_TyPair ty1 ty2 =
  let
      val jty1 = extract_judge_typing ty1
      val jty2 = extract_judge_typing ty2
  in
      (#1 jty1, EPair (#2 jty1, #2 jty2), CProd (#3 jty1, #3 jty2), Tadd (#4 jty1, #4 jty2))
  end

fun as_TyUnpack ty1 ty2 =
  let
      val jty1 = extract_judge_typing ty1
      val jty2 = extract_judge_typing ty2
  in
      (#1 jty1, EUnpack (#2 jty1, #2 jty2), shift_c_c ~1 0 (#3 jty2), Tadd (#4 jty1, shift_c_c ~1 0 (#4 jty2)))
  end

fun as_TyPack kd1 kd2 ty =
  let
      val jkd1 = extract_judge_kinding kd1
      val jkd2 = extract_judge_kinding kd2
      val jty = extract_judge_typing ty
  in
      (#1 jty, EPack (#2 jkd2, #2 jty), #2 jkd1, #4 jty)
  end

fun as_TyUnfold ty =
  let
      val jty = extract_judge_typing ty
      fun unfold_CApps t cs =
        case t of
            CApp (t, c) => unfold_CApps t (c :: cs)
          | _ => (t, cs)
      val (t, cs) = unfold_CApps (#3 jty) []
      val (k, t1) = extract_c_rec t
  in
      (#1 jty, EUnfold (#2 jty), CApps (subst_c_c t 0 t1) cs, #4 jty)
  end

fun as_TyFold kd ty =
  let
      val jkd = extract_judge_kinding kd
      val jty = extract_judge_typing ty
  in
      (#1 jty, EFold (#2 jty), #2 jkd, #4 jty)
  end

fun as_TyHalt ty =
  let
      val jty = extract_judge_typing ty
  in
      (#1 jty, EHalt (#2 jty), CTypeUnit, #4 jty)
  end

fun as_TyRec kd ty =
  let
      val jkd = extract_judge_kinding kd
      val jty = extract_judge_typing ty
  in
      ((#1 jkd, tl o snd $ #1 jty), ERec (#2 jty), #3 jty, T0)
  end

fun as_TyFix ctx kd ty =
  let
      val jkd = extract_judge_kinding kd
      val jty = extract_judge_typing ty
  in
      (ctx, EFix (length $ fst $ #1 jty, #2 jty), #2 jkd, T0)
  end

fun as_TyAbsC wk ty =
  let
      val jwk = extract_judge_wfkind wk
      val jty = extract_judge_typing ty
  in
      ((#1 jwk, map (shift_c_c ~1 0) o snd $ #1 jty), EAbsC (#2 jty), CForall (#2 jwk, #3 jty), T0)
  end

fun as_TyAppC ty kd =
  let
      val jty = extract_judge_typing ty
      val jkd = extract_judge_kinding kd
      val (_, k, t) = extract_c_quan (#3 jty)
  in
      (#1 jty, EAppC (#2 jty, #2 jkd), subst_c_c (#2 jkd) 0 t, #4 jty)
  end

fun as_TyLet ty1 ty2 =
  let
      val jty1 = extract_judge_typing ty1
      val jty2 = extract_judge_typing ty2
  in
      (#1 jty1, ELet (#2 jty1, #2 jty2), #3 jty2, Tadd (#4 jty1, #4 jty2))
  end

fun as_TyPrimBinOp opr ty1 ty2 =
  let
      val jty1 = extract_judge_typing ty1
      val jty2 = extract_judge_typing ty2
  in
      (#1 jty1, EBinOp (EBPrim opr, #2 jty1, #2 jty2), pebinop_result_type opr, Tadd (#4 jty1, #4 jty2))
  end
end

functor CstrDerivGenericTransformer(
    Action:
    sig
        type down
        type up

        val upward_base : up
        val combiner : up * up -> up

        val add_kind : kind * down -> down

        val on_pr_leaf : proping_judgement * down -> proping_judgement * up
        val on_ke_leaf : kdeq_judgement * down -> kdeq_judgement * up
        val on_kd_leaf : kinding_judgement * down -> kinding_judgement * up
        val on_wk_leaf : wfkind_judgement * down -> wfkind_judgement * up
        val on_wp_leaf : wfprop_judgement * down -> wfprop_judgement * up
        val on_te_leaf : tyeq_judgement * down -> tyeq_judgement * up

        val transformer_proping : proping * down -> (proping * up) option
        val transformer_kdeq : (kdeq * down -> kdeq * up) * (proping * down -> proping * up) -> kdeq * down -> (kdeq * up) option
        val transformer_kinding : (kinding * down -> kinding * up) * (wfkind * down -> wfkind * up) * (kdeq * down -> kdeq * up) -> kinding * down -> (kinding * up) option
        val transformer_wfkind : (wfkind * down -> wfkind * up) * (wfprop * down -> wfprop * up) -> wfkind * down -> (wfkind * up) option
        val transformer_wfprop : (wfprop * down -> wfprop * up) * (kinding * down -> kinding * up) -> wfprop * down -> (wfprop * up) option
        val transformer_tyeq : (tyeq * down -> tyeq * up) * (proping * down -> proping * up) * (kdeq * down -> kdeq * up) * (kinding * down -> kinding * up) -> tyeq * down -> (tyeq * up) option
    end) =
struct
open List
open DerivAssembler

val combine = foldl Action.combiner Action.upward_base

fun default_transform_proping (pr, down) =
  case pr of
      PrAdmit judge =>
      let
          val (judge, up) = Action.on_pr_leaf (judge, down)
      in
          (PrAdmit judge, combine [up])
      end

and transform_proping (pr, down) =
    case Action.transformer_proping (pr, down) of
        SOME res => res
      | NONE => default_transform_proping (pr, down)

fun default_transform_kdeq (ke, down) =
    case ke of
        KdEqKType judge =>
        let
            val (judge, up) = Action.on_ke_leaf (judge, down)
        in
            (KdEqKType judge, combine [up])
        end
      | KdEqKArrow (judge, ke1, ke2) =>
        let
            val (ke1, up1) = transform_kdeq (ke1, down)
            val (ke2, up2) = transform_kdeq (ke2, down)
        in
            (KdEqKArrow (as_KdEqKArrow ke1 ke2, ke1, ke2), combine [up1, up2])
        end
      | KdEqBaseSort judge =>
        let
            val (judge, up) = Action.on_ke_leaf (judge, down)
        in
            (KdEqBaseSort judge, combine [up])
        end
      | KdEqSubset (judge, ke, pr) =>
        let
            val (ke, up1) = transform_kdeq (ke, down)
            val jke = extract_judge_kdeq ke
            val (pr, up2) = transform_proping (pr, Action.add_kind (#2 jke, down))
        in
            (KdEqSubset (as_KdEqKSubset ke pr, ke, pr), combine [up1, up2])
        end

and transform_kdeq (ke, down) =
    case Action.transformer_kdeq (transform_kdeq, transform_proping) (ke, down) of
        SOME res => res
      | NONE => default_transform_kdeq (ke, down)

fun default_transform_kinding (kd, down) =
    case kd of
        KdVar judge =>
        let
            val (judge, up) = Action.on_kd_leaf (judge, down)
        in
            (KdVar judge, combine [up])
        end
      | KdConst judge =>
        let
            val (judge, up) = Action.on_kd_leaf (judge, down)
        in
            (KdConst judge, combine [up])
        end
      | KdBinOp (judge, kd1, kd2) =>
        let
            val (kd1, up1) = transform_kinding (kd1, down)
            val (kd2, up2) = transform_kinding (kd2, down)
            val (opr, _, _) = extract_c_bin_op (#2 judge)
        in
            (KdBinOp (as_KdBinOp opr kd1 kd2, kd1, kd2), combine [up1, up2])
        end
      | KdIte (judge, kd1, kd2, kd3) =>
        let
            val (kd1, up1) = transform_kinding (kd1, down)
            val (kd2, up2) = transform_kinding (kd2, down)
            val (kd3, up3) = transform_kinding (kd3, down)
        in
            (KdIte (as_KdIte kd1 kd2 kd3, kd1, kd2, kd3), combine [up1, up2, up3])
        end
      | KdArrow (judge, kd1, kd2, kd3) =>
        let
            val (kd1, up1) = transform_kinding (kd1, down)
            val (kd2, up2) = transform_kinding (kd2, down)
            val (kd3, up3) = transform_kinding (kd3, down)
        in
            (KdArrow (as_KdArrow kd1 kd2 kd3, kd1, kd2, kd3), combine [up1, up2, up3])
        end
      | KdAbs (judge, wk, kd) =>
        let
            val (wk, up1) = transform_wfkind (wk, down)
            val jwk = extract_judge_wfkind wk
            val (kd, up2) = transform_kinding (kd, Action.add_kind (#2 jwk, down))
        in
            (KdAbs (as_KdAbs wk kd, wk, kd), combine [up1, up2])
        end
      | KdApp (judge, kd1, kd2) =>
        let
            val (kd1, up1) = transform_kinding (kd1, down)
            val (kd2, up2) = transform_kinding (kd2, down)
        in
            (KdApp (as_KdApp kd1 kd2, kd1, kd2), combine [up1, up2])
        end
      | KdTimeAbs (judge, kd) =>
        let
            val (kd, up1) = transform_kinding (kd, Action.add_kind (KNat, down))
        in
            (KdTimeAbs (as_KdTimeAbs kd, kd), combine [up1])
        end
      | KdTimeApp (judge, kd1, kd2) =>
        let
            val (kd1, up1) = transform_kinding (kd1, down)
            val (kd2, up2) = transform_kinding (kd2, down)
        in
            (KdTimeApp (as_KdTimeApp kd1 kd2, kd1, kd2), combine [up1, up2])
        end
      | KdQuan (judge, wk, kd) =>
        let
            val (wk, up1) = transform_wfkind (wk, down)
            val jwk = extract_judge_wfkind wk
            val (kd, up2) = transform_kinding (kd, Action.add_kind (#2 jwk, down))
            val (q, _, _) = extract_c_quan (#2 judge)
        in
            (KdQuan (as_KdQuan q wk kd, wk, kd), combine [up1, up2])
        end
      | KdRec (judge, wk, kd) =>
        let
            val (wk, up1) = transform_wfkind (wk, down)
            val jwk = extract_judge_wfkind wk
            val (kd, up2) = transform_kinding (kd, Action.add_kind (#2 jwk, down))
        in
            (KdRec (as_KdRec wk kd, wk, kd), combine [up1, up2])
        end
      | KdRef (judge, kd) =>
        let
            val (kd, up1) = transform_kinding (kd, down)
        in
            (KdRef (as_KdRef kd, kd), combine [up1])
        end
      | KdEq (judge, kd, ke) =>
        let
            val (kd, up1) = transform_kinding (kd, down)
            val (ke, up2) = transform_kdeq (ke, down)
        in
            (KdEq (as_KdEq kd ke, kd, ke), combine [up1, up2])
        end
      | KdUnOp (judge, kd) =>
        let
            val (kd, up1) = transform_kinding (kd, down)
            val (opr, _) = extract_c_un_op (#2 judge)
        in
            (KdUnOp (as_KdUnOp opr kd, kd), combine [up1])
        end
      | KdAdmit judge =>
        let
            val (judge, up) = Action.on_kd_leaf (judge, down)
        in
            (KdAdmit judge, combine [up])
        end

and transform_kinding (kd, down) =
    case Action.transformer_kinding (transform_kinding, transform_wfkind, transform_kdeq) (kd, down) of
        SOME res => res
      | NONE => default_transform_kinding (kd, down)

and default_transform_wfkind (wk, down) =
    case wk of
        WfKdType judge =>
        let
            val (judge, up) = Action.on_wk_leaf (judge, down)
        in
            (WfKdType judge, combine [up])
        end
      | WfKdArrow (judge, wk1, wk2) =>
        let
            val (wk1, up1) = transform_wfkind (wk1, down)
            val (wk2, up2) = transform_wfkind (wk2, down)
        in
            (WfKdArrow (as_WfKdArrow wk1 wk2, wk1, wk2), combine [up1, up2])
        end
      | WfKdBaseSort judge =>
        let
            val (judge, up) = Action.on_wk_leaf (judge, down)
        in
            (WfKdBaseSort judge, combine [up])
        end
      | WfKdSubset (judge, wk, wp) =>
        let
            val (wk, up1) = transform_wfkind (wk, down)
            val jwk = extract_judge_wfkind wk
            val (wp, up2) = transform_wfprop (wp, Action.add_kind (#2 jwk, down))
        in
            (WfKdSubset (as_WfKdSubset wk wp, wk, wp), combine [up1, up2])
        end
      | WfKdAdmit judge =>
        let
            val (judge, up) = Action.on_wk_leaf (judge, down)
        in
            (WfKdAdmit judge, combine [up])
        end

and transform_wfkind (wk, down) =
    case Action.transformer_wfkind (transform_wfkind, transform_wfprop) (wk, down) of
        SOME res => res
      | NONE => default_transform_wfkind (wk, down)

and default_transform_wfprop (wp, down) =
    case wp of
        WfPropTrue judge =>
        let
            val (judge, up) = Action.on_wp_leaf (judge, down)
        in
            (WfPropTrue judge, combine [up])
        end
      | WfPropFalse judge =>
        let
            val (judge, up) = Action.on_wp_leaf (judge, down)
        in
            (WfPropFalse judge, combine [up])
        end
      | WfPropBinConn (judge, wp1, wp2) =>
        let
            val (wp1, up1) = transform_wfprop (wp1, down)
            val (wp2, up2) = transform_wfprop (wp2, down)
            val (opr, _, _) = extract_p_bin_conn (#2 judge)
        in
            (WfPropBinConn (as_WfPropBinConn opr wp1 wp2, wp1, wp2), combine [up1, up2])
        end
      | WfPropNot (judge, wp) =>
        let
            val (wp, up1) = transform_wfprop (wp, down)
        in
            (WfPropNot (as_WfPropNot wp, wp), combine [up1])
        end
      | WfPropBinPred (judge, kd1, kd2) =>
        let
            val (kd1, up1) = transform_kinding (kd1, down)
            val (kd2, up2) = transform_kinding (kd2, down)
            val (opr, _, _) = extract_p_bin_pred (#2 judge)
        in
            (WfPropBinPred (as_WfPropBinPred opr kd1 kd2, kd1, kd2), combine [up1, up2])
        end
      | WfPropQuan (judge, wp) =>
        let
            val (q, b, _) = extract_p_quan (#2 judge)
            val (wp, up1) = transform_wfprop (wp, Action.add_kind (KBaseSort b, down))
        in
            (WfPropQuan (as_WfPropQuan q b wp, wp), combine [up1])
        end

and transform_wfprop (wp, down) =
    case Action.transformer_wfprop (transform_wfprop, transform_kinding) (wp, down) of
        SOME res => res
      | NONE => default_transform_wfprop (wp, down)

fun default_transform_tyeq (te, down) =
    case te of
        TyEqVar judge =>
        let
            val (judge, up) = Action.on_te_leaf (judge, down)
        in
            (TyEqVar judge, combine [up])
        end
      | TyEqConst judge =>
        let
            val (judge, up) = Action.on_te_leaf (judge, down)
        in
            (TyEqConst judge, combine [up])
        end
      | TyEqBinOp (judge, te1, te2) =>
        let
            val (te1, up1) = transform_tyeq (te1, down)
            val (te2, up2) = transform_tyeq (te2, down)
            val (opr, _, _) = extract_c_bin_op (#2 judge)
        in
            (TyEqBinOp (as_TyEqBinOp opr te1 te2, te1, te2), combine [up1, up2])
        end
      | TyEqIte (judge, te1, te2, te3) =>
        let
            val (te1, up1) = transform_tyeq (te1, down)
            val (te2, up2) = transform_tyeq (te2, down)
            val (te3, up3) = transform_tyeq (te3, down)
        in
            (TyEqIte (as_TyEqIte te1 te2 te3, te1, te2, te3), combine [up1, up2, up3])
        end
      | TyEqArrow (judge, te1, pr, te2) =>
        let
            val (te1, up1) = transform_tyeq (te1, down)
            val (pr, up2) = transform_proping (pr, down)
            val (te2, up3) = transform_tyeq (te2, down)
        in
            (TyEqArrow (as_TyEqArrow te1 pr te2, te1, pr, te2), combine [up1, up2, up3])
        end
      | TyEqApp (judge, te1, te2) =>
        let
            val (te1, up1) = transform_tyeq (te1, down)
            val (te2, up2) = transform_tyeq (te2, down)
        in
            (TyEqApp (as_TyEqApp te1 te2, te1, te2), combine [up1, up2])
        end
      | TyEqTimeApp (judge, te1, te2) =>
        let
            val (te1, up1) = transform_tyeq (te1, down)
            val (te2, up2) = transform_tyeq (te2, down)
            val (arity, _, _) = extract_c_time_app (#2 judge)
        in
            (TyEqTimeApp (as_TyEqTimeApp arity te1 te2, te1, te2), combine [up1, up2])
        end
      | TyEqBeta (judge, te1, te2, te3) =>
        let
            val (te1, up1) = transform_tyeq (te1, down)
            val (te2, up2) = transform_tyeq (te2, down)
            val (te3, up3) = transform_tyeq (te3, down)
        in
            (TyEqBeta (as_TyEqBeta te1 te2 te3, te1, te2, te3), combine [up1, up2, up3])
        end
      | TyEqBetaRev (judge, te1, te2, te3) =>
        let
            val (te1, up1) = transform_tyeq (te1, down)
            val (te2, up2) = transform_tyeq (te2, down)
            val (te3, up3) = transform_tyeq (te3, down)
        in
            (TyEqBetaRev (as_TyEqBetaRev te1 te2 te3, te1, te2, te3), combine [up1, up2, up3])
        end
      | TyEqQuan (judge, ke, te) =>
        let
            val (ke, up1) = transform_kdeq (ke, down)
            val jke = extract_judge_kdeq ke
            val (te, up2) = transform_tyeq (te, Action.add_kind (#2 jke, down))
            val (q, _, _) = extract_c_quan (#2 judge)
        in
            (TyEqQuan (as_TyEqQuan q ke te, ke, te), combine [up1, up2])
        end
      | TyEqRec (judge, ke, te) =>
        let
            val (ke, up1) = transform_kdeq (ke, down)
            val jke = extract_judge_kdeq ke
            val (te, up2) = transform_tyeq (te, Action.add_kind (#2 jke, down))
        in
            (TyEqRec (as_TyEqRec ke te, ke, te), combine [up1, up2])
        end
      | TyEqRef (judge, te) =>
        let
            val (te, up1) = transform_tyeq (te, down)
        in
            (TyEqRef (as_TyEqRef te, te), combine [up1])
        end
      | TyEqAbs judge =>
        let
            val (judge, up) = Action.on_te_leaf (judge, down)
        in
            (TyEqAbs judge, combine [up])
        end
      | TyEqTimeAbs judge =>
        let
            val (judge, up) = Action.on_te_leaf (judge, down)
        in
            (TyEqTimeAbs judge, combine [up])
        end
      | TyEqUnOp (judge, te) =>
        let
            val (te, up1) = transform_tyeq (te, down)
            val (opr, _) = extract_c_un_op (#2 judge)
        in
            (TyEqUnOp (as_TyEqUnOp opr te, te), combine [up1])
        end
      | TyEqNat (judge, kd1, kd2, pr) =>
        let
            val (kd1, up1) = transform_kinding (kd1, down)
            val (kd2, up2) = transform_kinding (kd2, down)
            val (pr, up3) = transform_proping (pr, down)
        in
            (TyEqNat (as_TyEqNat kd1 kd2 pr, kd1, kd2, pr), combine [up1, up2, up3])
        end

and transform_tyeq (te, down) =
    case Action.transformer_tyeq (transform_tyeq, transform_proping, transform_kdeq, transform_kinding) (te, down) of
        SOME res => res
      | NONE => default_transform_tyeq (te, down)
end

functor ExprDerivGenericTransformer(
    Action:
    sig
        type kdown
        type tdown
        type down = kdown * tdown
        type up

        val upward_base : up
        val combiner : up * up -> up

        val add_kind : kind * down -> down
        val add_type : cstr * tdown -> tdown

        val on_ty_leaf : typing_judgement * down -> typing_judgement * up

        val transform_proping : proping * kdown -> proping * up
        val transform_kinding : kinding * kdown -> kinding * up
        val transform_wfkind : wfkind * kdown -> wfkind * up
        val transform_tyeq : tyeq * kdown -> tyeq * up

        val transformer_typing : (typing * down -> typing * up) -> typing * down -> (typing * up) option
    end) =
struct
open List
open DerivAssembler

val combine = foldl Action.combiner Action.upward_base

fun default_transform_typing (ty, down as (kdown, tdown)) =
    case ty of
        TyVar judge =>
        let
            val (judge, up) = Action.on_ty_leaf (judge, down)
        in
            (TyVar judge, combine [up])
        end
      | TyApp (judge, ty1, ty2) =>
        let
            val (ty1, up1) = transform_typing (ty1, down)
            val (ty2, up2) = transform_typing (ty2, down)
        in
            (TyApp (as_TyApp ty1 ty2, ty1, ty2), combine [up1, up2])
        end
      | TyAbs (judge, kd, ty) =>
        let
            val (kd, up1) = Action.transform_kinding (kd, kdown)
            val jkd = extract_judge_kinding kd
            val (ty, up2) = transform_typing (ty, (kdown, Action.add_type (#2 jkd, tdown)))
        in
            (TyAbs (as_TyAbs kd ty, kd, ty), combine [up1, up2])
        end
      | TyAppC (judge, ty, kd) =>
        let
            val (ty, up1) = transform_typing (ty, down)
            val (kd, up2) = Action.transform_kinding (kd, kdown)
        in
            (TyAppC (as_TyAppC ty kd, ty, kd), combine [up1, up2])
        end
      | TyAbsC (judge, wk, ty) =>
        let
            val (wk, up1) = Action.transform_wfkind (wk, kdown)
            val jwk = extract_judge_wfkind wk
            val (ty, up2) = transform_typing (ty, Action.add_kind (#2 jwk, down))
        in
            (TyAbsC (as_TyAbsC wk ty, wk, ty), combine [up1, up2])
        end
      | TyRec (judge, kd, ty) =>
        let
            val (kd, up1) = Action.transform_kinding (kd, kdown)
            val jkd = extract_judge_kinding kd
            val (ty, up2) = transform_typing (ty, (kdown, Action.add_type (#2 jkd, tdown)))
        in
            (TyRec (as_TyRec kd ty, kd, ty), combine [up1, up2])
        end
      | TyFold (judge, kd, ty) =>
        let
            val (kd, up1) = Action.transform_kinding (kd, kdown)
            val (ty, up2) = transform_typing (ty, down)
        in
            (TyFold (as_TyFold kd ty, kd, ty), combine [up1, up2])
        end
      | TyUnfold (judge, ty) =>
        let
            val (ty, up1) = transform_typing (ty, down)
        in
            (TyUnfold (as_TyUnfold ty, ty), combine [up1])
        end
      | TyPack (judge, kd1, kd2, ty) =>
        let
            val (kd1, up1) = Action.transform_kinding (kd1, kdown)
            val (kd2, up2) = Action.transform_kinding (kd2, kdown)
            val (ty, up3) = transform_typing (ty, down)
        in
            (TyPack (as_TyPack kd1 kd2 ty, kd1, kd2, ty), combine [up1, up2, up3])
        end
      | TyUnpack (judge, ty1, ty2) =>
        let
            val (ty1, up1) = transform_typing (ty1, down)
            val jty1 = extract_judge_typing ty1
            val (_, k, t) = extract_c_quan (#3 jty1)
            val (ty2, up2) = transform_typing (ty2, let val (kdown, tdown) = Action.add_kind (k, down) in (kdown, Action.add_type (t, tdown)) end)
        in
            (TyUnpack (as_TyUnpack ty1 ty2, ty1, ty2), combine [up1, up2])
        end
      | TyConst judge =>
        let
            val (judge, up) = Action.on_ty_leaf (judge, down)
        in
            (TyConst judge, combine [up])
        end
      | TyPair (judge, ty1, ty2) =>
        let
            val (ty1, up1) = transform_typing (ty1, down)
            val (ty2, up2) = transform_typing (ty2, down)
        in
            (TyPair (as_TyPair ty1 ty2, ty1, ty2), combine [up1, up2])
        end
      | TyProj (judge, ty) =>
        let
            val (ty, up1) = transform_typing (ty, down)
            val (p, _) = extract_e_proj (#2 judge)
        in
            (TyProj (as_TyProj p ty, ty), combine [up1])
        end
      | TyInj (judge, ty, kd) =>
        let
            val (ty, up1) = transform_typing (ty, down)
            val (kd, up2) = Action.transform_kinding (kd, kdown)
            val (inj, _) = extract_e_inj (#2 judge)
        in
            (TyInj (as_TyInj inj ty kd, ty, kd), combine [up1, up2])
        end
      | TyCase (judge, ty1, ty2, ty3) =>
        let
            val (ty1, up1) = transform_typing (ty1, down)
            val jty1 = extract_judge_typing ty1
            val (t1, t2) = extract_c_sum (#3 jty1)
            val (ty2, up2) = transform_typing (ty2, (kdown, Action.add_type (t1, tdown)))
            val (ty3, up3) = transform_typing (ty3, (kdown, Action.add_type (t2, tdown)))
        in
            (TyCase (as_TyCase ty1 ty2 ty3, ty1, ty2, ty3), combine [up1, up2, up3])
        end
      | TyNew (judge, ty) =>
        let
            val (ty, up1) = transform_typing (ty, down)
        in
            (TyNew (as_TyNew ty, ty), combine [up1])
        end
      | TyRead (judge, ty) =>
        let
            val (ty, up1) = transform_typing (ty, down)
        in
            (TyRead (as_TyRead ty, ty), combine [up1])
        end
      | TyWrite (judge, ty1, ty2) =>
        let
            val (ty1, up1) = transform_typing (ty1, down)
            val (ty2, up2) = transform_typing (ty2, down)
        in
            (TyWrite (as_TyWrite ty1 ty2, ty1, ty2), combine [up1, up2])
        end
      | TySubTy (judge, ty, te) =>
        let
            val (ty, up1) = transform_typing (ty, down)
            val (te, up2) = Action.transform_tyeq (te, kdown)
        in
            (TySubTy (as_TySubTy ty te, ty, te), combine [up1, up2])
        end
      | TySubTi (judge, ty, pr) =>
        let
            val (ty, up1) = transform_typing (ty, down)
            val (pr, up2) = Action.transform_proping (pr, kdown)
        in
            (TySubTi (as_TySubTi ty pr, ty, pr), combine [up1, up2])
        end
      | TyHalt (judge, ty) =>
        let
            val (ty, up1) = transform_typing (ty, down)
        in
            (TyHalt (as_TyHalt ty, ty), combine [up1])
        end
      | TyLet (judge, ty1, ty2) =>
        let
            val (ty1, up1) = transform_typing (ty1, down)
            val jty1 = extract_judge_typing ty1
            val (ty2, up2) = transform_typing (ty2, (kdown, Action.add_type (#3 jty1, tdown)))
        in
            (TyLet (as_TyLet ty1 ty2, ty1, ty2), combine [up1, up2])
        end
      | TyFix (judge, kd, ty) =>
        let
            val (judge, up) = Action.on_ty_leaf (judge, down)
        in
            (TyFix (judge, kd, ty), combine [up])
        end
      | TyPrimBinOp (judge, ty1, ty2) =>
        let
            val (ty1, up1) = transform_typing (ty1, down)
            val (ty2, up2) = transform_typing (ty2, down)
            val (opr, _, _) = extract_e_prim_bin_op (#2 judge)
        in
            (TyPrimBinOp (as_TyPrimBinOp opr ty1 ty2, ty1, ty2), combine [up1, up2])
        end

and transform_typing (ty, down) =
    case Action.transformer_typing transform_typing (ty, down) of
        SOME res => res
      | NONE => default_transform_typing (ty, down)
end

functor CstrDerivGenericOnlyDownTransformer(
    Action:
    sig
        type down

        val add_kind : kind * down -> down

        val on_pr_leaf : proping_judgement * down -> proping_judgement
        val on_ke_leaf : kdeq_judgement * down -> kdeq_judgement
        val on_kd_leaf : kinding_judgement * down -> kinding_judgement
        val on_wk_leaf : wfkind_judgement * down -> wfkind_judgement
        val on_wp_leaf : wfprop_judgement * down -> wfprop_judgement
        val on_te_leaf : tyeq_judgement * down -> tyeq_judgement

        val transformer_proping : proping * down -> proping option
        val transformer_kdeq : (kdeq * down -> kdeq) * (proping * down -> proping) -> kdeq * down -> kdeq option
        val transformer_kinding : (kinding * down -> kinding) * (wfkind * down -> wfkind) * (kdeq * down -> kdeq) -> kinding * down -> kinding option
        val transformer_wfkind : (wfkind * down -> wfkind) * (wfprop * down -> wfprop) -> wfkind * down -> wfkind option
        val transformer_wfprop : (wfprop * down -> wfprop) * (kinding * down -> kinding) -> wfprop * down -> wfprop option
        val transformer_tyeq : (tyeq * down -> tyeq) * (proping * down -> proping) * (kdeq * down -> kdeq) * (kinding * down -> kinding) -> tyeq * down -> tyeq option
    end) =
struct
structure Transformer = CstrDerivGenericTransformer(
    struct
    type down = Action.down
    type up = unit

    val upward_base = ()
    fun combiner ((), ()) = ()

    val add_kind = Action.add_kind

    val on_pr_leaf = (fn j => (j, ())) o Action.on_pr_leaf
    val on_ke_leaf = (fn j => (j, ())) o Action.on_ke_leaf
    val on_kd_leaf = (fn j => (j, ())) o Action.on_kd_leaf
    val on_wk_leaf = (fn j => (j, ())) o Action.on_wk_leaf
    val on_wp_leaf = (fn j => (j, ())) o Action.on_wp_leaf
    val on_te_leaf = (fn j => (j, ())) o Action.on_te_leaf

    val transformer_proping = Option.map (fn pr => (pr, ())) o Action.transformer_proping

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

    fun transformer_tyeq (on_tyeq, on_proping, on_kdeq, on_kinding) =
      let
          val on_tyeq_no_up = fst o on_tyeq
          val on_proping_no_up = fst o on_proping
          val on_kdeq_no_up = fst o on_kdeq
          val on_kinding_no_up = fst o on_kinding
      in
          Option.map (fn te => (te, ())) o Action.transformer_tyeq (on_tyeq_no_up, on_proping_no_up, on_kdeq_no_up, on_kinding_no_up)
      end
    end)

val transform_proping = fst o Transformer.transform_proping
val transform_kdeq = fst o Transformer.transform_kdeq
val transform_kinding = fst o Transformer.transform_kinding
val transform_wfkind = fst o Transformer.transform_wfkind
val transform_wfprop = fst o Transformer.transform_wfprop
val transform_tyeq = fst o Transformer.transform_tyeq
end

functor ExprDerivGenericOnlyDownTransformer(
    Action:
    sig
        type kdown
        type tdown
        type down = kdown * tdown

        val add_kind : kind * down -> down
        val add_type : cstr * tdown -> tdown

        val on_ty_leaf : typing_judgement * down -> typing_judgement

        val transform_proping : proping * kdown -> proping
        val transform_kinding : kinding * kdown -> kinding
        val transform_wfkind : wfkind * kdown -> wfkind
        val transform_tyeq : tyeq * kdown -> tyeq

        val transformer_typing : (typing * down -> typing) -> typing * down -> typing option
    end) =
struct
structure Transformer = ExprDerivGenericTransformer(
    struct
    type kdown = Action.kdown
    type tdown = Action.tdown
    type down = Action.down
    type up = unit

    val upward_base = ()
    fun combiner ((), ()) = ()

    val add_kind = Action.add_kind
    val add_type = Action.add_type

    val on_ty_leaf = (fn j => (j, ())) o Action.on_ty_leaf

    val transform_proping = (fn pr => (pr, ())) o Action.transform_proping
    val transform_kinding = (fn kd => (kd, ())) o Action.transform_kinding
    val transform_wfkind = (fn wk => (wk, ())) o Action.transform_wfkind
    val transform_tyeq = (fn te => (te, ())) o Action.transform_tyeq

    fun transformer_typing on_typing =
      let
          val on_typing_no_up = fst o on_typing
      in
          Option.map (fn ty => (ty, ())) o Action.transformer_typing on_typing_no_up
      end
    end)

val transform_typing = fst o Transformer.transform_typing
end

structure ShiftCtx =
struct
open List

structure CstrDerivHelper = CstrDerivGenericOnlyDownTransformer(
    struct
    type down = kctx * int

    fun add_kind (_, (kctxd, kdep)) = (kctxd, kdep + 1)

    fun insert_k a b c = (mapi (fn (i, k) => shift_c_k (length c) (b - 1 - i) k) $ take (a, b)) @ c @ drop (a, b)

    fun on_pr_leaf ((kctx, p), (kctxd, kdep)) =
      (insert_k kctx kdep kctxd, shift_c_p (length kctxd) kdep p)
    fun on_ke_leaf ((kctx, k1, k2), (kctxd, kdep)) =
      (insert_k kctx kdep kctxd, shift_c_k (length kctxd) kdep k1, shift_c_k (length kctxd) kdep k2)
    fun on_kd_leaf ((kctx, c, k), (kctxd, kdep)) =
      (insert_k kctx kdep kctxd, shift_c_c (length kctxd) kdep c, shift_c_k (length kctxd) kdep k)
    fun on_wk_leaf ((kctx, k), (kctxd, kdep)) =
      (insert_k kctx kdep kctxd, shift_c_k (length kctxd) kdep k)
    fun on_wp_leaf ((kctx, p), (kctxd, kdep)) =
      (insert_k kctx kdep kctxd, shift_c_p (length kctxd) kdep p)
    fun on_te_leaf ((kctx, t1, t2), (kctxd, kdep)) =
      (insert_k kctx kdep kctxd, shift_c_c (length kctxd) kdep t1, shift_c_c (length kctxd) kdep t2)

    fun transformer_proping _ = NONE
    fun transformer_kdeq _ _ = NONE
    fun transformer_kinding _ _ = NONE
    fun transformer_wfkind _ _ = NONE
    fun transformer_wfprop _ _ = NONE
    fun transformer_tyeq _ _ = NONE
    end)

structure ExprDerivHelper = ExprDerivGenericOnlyDownTransformer(
    struct
    type kdown = kctx * int
    type tdown = tctx * int
    type down =  kdown * tdown

    fun add_kind (_, ((kctxd, kdep), (tctxd, tdep))) = ((kctxd, kdep + 1), (map shift0_c_c tctxd, tdep))
    fun add_type (_, (tctxd, tdep)) = (tctxd, tdep + 1)

    fun insert_k a b c = (mapi (fn (i, k) => shift_c_k (length c) (b - 1 - i) k) $ take (a, b)) @ c @ drop (a, b)
    fun insert_t a b c = take (a, b) @ c @ drop (a, b)

    fun on_ty_leaf (((kctx, tctx), e, t, i), ((kctxd, kdep), (tctxd, tdep))) =
      let
          val kctx = insert_k kctx kdep kctxd
          val tctx = insert_t (map (shift_c_c (length kctxd) kdep) tctx) tdep tctxd
      in
          ((kctx, tctx), shift_e_e (length tctxd) tdep (shift_c_e (length kctxd) kdep e),
           shift_c_c (length kctxd) kdep t, shift_c_c (length kctxd) kdep i)
      end

    val transform_proping = CstrDerivHelper.transform_proping
    val transform_kinding = CstrDerivHelper.transform_kinding
    val transform_wfkind = CstrDerivHelper.transform_wfkind
    val transform_tyeq = CstrDerivHelper.transform_tyeq

    fun transformer_typing _ _ = NONE
    end)

fun shift_ctx_ty ((kctxd, kdep), (tctxd, tdep)) ty = ExprDerivHelper.transform_typing (ty, ((kctxd, kdep), (tctxd, tdep)))
fun shift_ctx_kd (kctxd, kdep) kd = CstrDerivHelper.transform_kinding (kd, (kctxd, kdep))
fun shift_ctx_te (kctxd, kdep) te = CstrDerivHelper.transform_tyeq (te, (kctxd, kdep))
fun shift_ctx_pr (kctxd, kdep) pr = CstrDerivHelper.transform_proping (pr, (kctxd, kdep))
fun shift_ctx_wk (kctxd, kdep) wk = CstrDerivHelper.transform_wfkind (wk, (kctxd, kdep))
fun shift_ctx_ke (kctxd, kdep) ke = CstrDerivHelper.transform_kdeq (ke, (kctxd, kdep))

fun shift0_ctx_ty (kctxd, tctxd) = shift_ctx_ty ((kctxd, 0), (tctxd, 0))
fun shift0_ctx_kd kctxd = shift_ctx_kd (kctxd, 0)
fun shift0_ctx_te kctxd = shift_ctx_te (kctxd, 0)
fun shift0_ctx_pr kctxd = shift_ctx_pr (kctxd, 0)
fun shift0_ctx_wk kctxd = shift_ctx_wk (kctxd, 0)
fun shift0_ctx_ke kctxd = shift_ctx_ke (kctxd, 0)
end

structure ChangeCtx =
struct
structure CstrDerivHelper = CstrDerivGenericOnlyDownTransformer(
    struct
    type down = kctx

    fun add_kind (k, kctx) = k :: kctx

    fun on_pr_leaf ((_, p), kctx) = (kctx, p)
    fun on_ke_leaf ((_, k1, k2), kctx) = (kctx, k1, k2)
    fun on_kd_leaf ((_, c, k), kctx) = (kctx, c, k)
    fun on_wk_leaf ((_, k), kctx) = (kctx, k)
    fun on_wp_leaf ((_, p), kctx) = (kctx, p)
    fun on_te_leaf ((_, c1, c2), kctx) = (kctx, c1, c2)

    fun transformer_proping _ = NONE
    fun transformer_kdeq _ _ = NONE
    fun transformer_kinding _ _ = NONE
    fun transformer_wfkind _ _ = NONE
    fun transformer_wfprop _ _ = NONE
    fun transformer_tyeq _ _ = NONE
    end)

structure ExprDerivHelper = ExprDerivGenericOnlyDownTransformer(
    struct
    type kdown = kctx
    type tdown = tctx
    type down = kdown * tdown

    fun add_kind (k, (kctx, tctx)) = (k :: kctx, map shift0_c_c tctx)
    fun add_type (t, tctx) = t :: tctx

    fun on_ty_leaf ((_, e, t, i), ctx) = (ctx, e, t, i)

    val transform_proping = CstrDerivHelper.transform_proping
    val transform_kinding = CstrDerivHelper.transform_kinding
    val transform_wfkind = CstrDerivHelper.transform_wfkind
    val transform_tyeq = CstrDerivHelper.transform_tyeq

    fun transformer_typing _ _ = NONE
    end)

fun change_ctx_wk kctx wk = CstrDerivHelper.transform_wfkind (wk, kctx)
fun change_ctx_kd kctx kd = CstrDerivHelper.transform_kinding (kd, kctx)
fun change_ctx_ty ctx ty = ExprDerivHelper.transform_typing (ty, ctx)
end

structure DerivFVCstr =
struct
open List
open FVUtil

structure CstrDerivHelper = CstrDerivGenericTransformer(
    struct
    type down = int
    type up = int list

    val upward_base = []
    val combiner = unique_merge

    fun add_kind (_, dep) = dep + 1

    fun on_pr_leaf (pr as (kctx, p), dep) = (pr, FVCstr.free_vars_c_p dep p)
    fun on_ke_leaf (ke as (kctx, k1, k2), dep) = (ke, combiner (FVCstr.free_vars_c_k dep k1, FVCstr.free_vars_c_k dep k2))
    fun on_kd_leaf (kd as (kctx, c, k), dep) = (kd, combiner (FVCstr.free_vars_c_c dep c, FVCstr.free_vars_c_k dep k))
    fun on_wk_leaf (wk as (kctx, k), dep) = (wk, FVCstr.free_vars_c_k dep k)
    fun on_wp_leaf (wp as (kctx, p), dep) = (wp, FVCstr.free_vars_c_p dep p)
    fun on_te_leaf (te as (kctx, t1, t2), dep) = (te, combiner (FVCstr.free_vars_c_c dep t1, FVCstr.free_vars_c_c dep t2))

    fun transformer_proping _ = NONE
    fun transformer_kdeq _ _ = NONE
    fun transformer_kinding _ _ = NONE
    fun transformer_wfkind _ _ = NONE
    fun transformer_wfprop _ _ = NONE
    fun transformer_tyeq _ _ = NONE
    end)

structure ExprDerivHelper = ExprDerivGenericTransformer(
    struct
    type kdown = int
    type tdown = unit
    type down = kdown * tdown
    type up = int list

    val upward_base = []
    val combiner = unique_merge

    fun add_kind (_, (dep, ())) = (dep + 1, ())
    fun add_type (_, ()) = ()

    fun on_ty_leaf (ty as (ctx, e, t, i), (dep, ()))= (ty, combiner (combiner (FVCstr.free_vars_c_e dep e, FVCstr.free_vars_c_c dep t), FVCstr.free_vars_c_c dep i))

    val transform_proping = CstrDerivHelper.transform_proping
    val transform_kinding = CstrDerivHelper.transform_kinding
    val transform_wfkind = CstrDerivHelper.transform_wfkind
    val transform_tyeq = CstrDerivHelper.transform_tyeq

    fun transformer_typing _ _ = NONE
    end)

fun free_vars_c_ty d ty = #2 (ExprDerivHelper.transform_typing (ty, (d, ())))

val free_vars0_c_ty = free_vars_c_ty 0
end

structure DerivFVExpr =
struct
open List
open FVUtil

structure ExprDerivHelper = ExprDerivGenericTransformer(
    struct
    type kdown = unit
    type tdown = int
    type down = kdown * tdown
    type up = int list

    val upward_base = []
    val combiner = unique_merge

    fun add_kind (_, ((), dep)) = ((), dep)
    fun add_type (_, dep) = dep + 1

    fun on_ty_leaf (ty as (ctx, e, t, i), ((), dep)) = (ty, FVExpr.free_vars_e_e dep e)

    fun transform_proping (pr, kdown) = (pr, [])
    fun transform_kinding (kd, kdown) = (kd, [])
    fun transform_wfkind (wk, kdown) = (wk, [])
    fun transform_tyeq (te, kdown) = (te, [])

    fun transformer_typing _ _ = NONE
    end)

fun free_vars_e_ty d ty = #2 (ExprDerivHelper.transform_typing (ty, ((), d)))

val free_vars0_e_ty = free_vars_e_ty 0
end

structure DerivSubstTyping =
struct
open List

structure ExprDerivHelper = ExprDerivGenericOnlyDownTransformer(
    struct
    type kdown = unit
    type tdown = typing * int
    type down = kdown * tdown

    fun add_kind (k, ((), (to, who))) = ((), (ShiftCtx.shift0_ctx_ty ([k], []) to, who))
    fun add_type (t, (to, who)) = (ShiftCtx.shift0_ctx_ty ([], [t]) to, who + 1)

    fun on_ty_leaf (((kctx, tctx), e, t, i), ((), (to, who))) =
      case e of
          EConst cn => ((kctx, take (tctx, who) @ drop (tctx, who + 1)), EConst cn, t, i)
        | _ => raise (Impossible "DerivSubstTyping")

    fun transform_proping (pr, kdown) = pr
    fun transform_kinding (kd, kdown) = kd
    fun transform_wfkind (wk, kdown) = wk
    fun transform_tyeq (te, kdown) = te

    fun transformer_typing on_typing (ty, ((), (to, who))) =
      case ty of
          TyVar ((kctx, tctx), e, t, i) =>
          (case e of
               EVar x =>
               if x = who then SOME to
               else
                   if x < who then
                       SOME (TyVar ((kctx, take (tctx, who) @ drop (tctx, who + 1)), EVar x, t, i))
                   else
                       SOME (TyVar ((kctx, take (tctx, who) @ drop (tctx, who + 1)), EVar (x - 1), t, i))
             | _ => raise (Impossible "DerivSubstTyping"))
        | TyFix (((kctx, tctx), t, e, i), kd, ty) => SOME (TyFix (((kctx, take (tctx, who) @ drop (tctx, who + 1)), t, e, i), kd, ty))
        | _ => NONE
    end)

fun subst_ty_ty to who ty = ExprDerivHelper.transform_typing (ty, ((), (to, who)))

fun subst0_ty_ty to = subst_ty_ty to 0
end

structure DerivSubstKinding =
struct
open List
open DerivAssembler

structure CstrDerivHelper = CstrDerivGenericOnlyDownTransformer(
    struct
    type down = kinding * int

    fun add_kind (k, (to, who)) = (ShiftCtx.shift0_ctx_kd [k] to, who + 1)

    fun on_pr_leaf ((_, p), (to, who)) =
      let
          val (kctx, c, _) = extract_judge_kinding to
      in
          (kctx, subst_c_p c who p)
      end
    fun on_ke_leaf ((_, k1, k2), (to, who)) =
      let
          val (kctx, c, _) = extract_judge_kinding to
      in
          (kctx, subst_c_k c who k1, subst_c_k c who k2)
      end
    fun on_kd_leaf ((_, t, k), (to, who)) =
      let
          val (kctx, c, _) = extract_judge_kinding to
      in
          (kctx, subst_c_c c who t, subst_c_k c who k)
      end
    fun on_wk_leaf ((_, k), (to, who)) =
      let
          val (kctx, c, _) = extract_judge_kinding to
      in
          (kctx, subst_c_k c who k)
      end
    fun on_wp_leaf ((_, p), (to, who)) =
      let
          val (kctx, c, _) = extract_judge_kinding to
      in
          (kctx, subst_c_p c who p)
      end
    fun on_te_leaf ((_, t1, t2), (to, who)) =
      let
          val (kctx, c, _) = extract_judge_kinding to
      in
          (kctx, subst_c_c c who t1, subst_c_c c who t1)
      end

    fun transformer_kinding (on_kinding, on_wfkind, on_kdeq) (kd, (to, who)) =
      case kd of
          KdVar (kctx, c, k) =>
          (case c of
               CVar x =>
               if x = who then SOME to
               else
                   let
                       val (kctx, _, _) = extract_judge_kinding to
                   in
                       if x < who then
                           SOME (KdVar (kctx, CVar x, shift_c_k (1 + x) 0 $ nth (kctx, x)))
                       else
                           SOME (KdVar (kctx, CVar (x - 1), shift_c_k x 0 $ nth (kctx, x - 1)))
                   end
             | _ => raise (Impossible "DerivSubstKinding"))
        | _ => NONE

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

    fun transformer_tyeq (on_tyeq, on_proping, on_kdeq, on_kinding) (te, (to, who)) =
      case te of
          TyEqVar (kctx, t, _) =>
          (case t of
               CVar x =>
               if x = who then
                   let
                       val (kctx, c, _) = extract_judge_kinding to
                   in
                       SOME (gen_tyeq_refl kctx c)
                   end
               else
                   let
                       val (kctx, _, _) = extract_judge_kinding to
                   in
                       if x < who then
                           SOME (TyEqVar (kctx, CVar x, CVar x))
                       else
                           SOME (TyEqVar (kctx, CVar (x - 1), CVar (x - 1)))
                   end
             | _ => raise (Impossible "DerivSubstKinding"))
        | _ => NONE

    fun transformer_proping _ = NONE
    fun transformer_kdeq _ _ = NONE
    fun transformer_wfkind _ _ = NONE
    fun transformer_wfprop _ _ = NONE
    end)

fun subst_kd_kd to who kd = CstrDerivHelper.transform_kinding (kd, (to, who))

fun subst0_kd_kd to = subst_kd_kd to 0
end

structure DerivDirectSubstCstr =
struct
open DirectSubstCstr

structure CstrDerivHelper = CstrDerivGenericOnlyDownTransformer(
    struct
    type down = cstr * int

    fun add_kind (_, (to, who)) = (shift0_c_c to, who + 1)

    fun on_pr_leaf ((kctx, p), (to, who)) = (kctx, dsubst_c_p to who p)
    fun on_ke_leaf ((kctx, k1, k2), (to, who)) = (kctx, dsubst_c_k to who k1, dsubst_c_k to who k2)
    fun on_kd_leaf ((kctx, c, k), (to, who)) = (kctx, dsubst_c_c to who c, dsubst_c_k to who k)
    fun on_wk_leaf ((kctx, k), (to, who)) = (kctx, dsubst_c_k to who k)
    fun on_wp_leaf ((kctx, p), (to, who)) = (kctx, dsubst_c_p to who p)
    fun on_te_leaf ((kctx, t1, t2), (to, who)) = (kctx, dsubst_c_c to who t1, dsubst_c_c to who t2)

    fun transformer_proping _ = NONE
    fun transformer_kdeq _ _ = NONE
    fun transformer_kinding _ _ = NONE
    fun transformer_wfkind _ _ = NONE
    fun transformer_wfprop _ _ = NONE
    fun transformer_tyeq _ _ = NONE
    end)

structure ExprDerivHelper = ExprDerivGenericOnlyDownTransformer(
    struct
    type kdown = cstr * int
    type tdown = unit
    type down = kdown * tdown

    fun add_kind (_, ((to, who), ())) = ((shift0_c_c to, who + 1), ())
    fun add_type (_, ()) = ()

    fun on_ty_leaf ((ctx, e, t, i), ((to, who), ())) = (ctx, dsubst_c_e to who e, dsubst_c_c to who t, dsubst_c_c to who i)

    val transform_proping = CstrDerivHelper.transform_proping
    val transform_kinding = CstrDerivHelper.transform_kinding
    val transform_wfkind = CstrDerivHelper.transform_wfkind
    val transform_tyeq = CstrDerivHelper.transform_tyeq

    fun transformer_typing _ _ = NONE
    end)

fun dsubst_c_ty to who ty = ExprDerivHelper.transform_typing (ty, ((to, who), ()))
fun dsubst_c_kd to who kd = CstrDerivHelper.transform_kinding (kd, (to, who))
fun dsubst_c_wk to who wk = CstrDerivHelper.transform_wfkind (wk, (to, who))

fun dsubst0_c_ty to = dsubst_c_ty to 0
fun dsubst0_c_kd to = dsubst_c_kd to 0
fun dsubst0_c_wk to = dsubst_c_wk to 0
end

structure DerivDirectSubstExpr =
struct
open DirectSubstExpr

structure ExprDerivHelper = ExprDerivGenericOnlyDownTransformer(
    struct
    type kdown = unit
    type tdown = expr * int
    type down = kdown * tdown

    fun add_kind (_, ((), (to, who))) = ((), (shift0_c_e to, who))
    fun add_type (_, (to, who)) = (shift0_e_e to, who + 1)

    fun on_ty_leaf ((ctx, e, t, i), ((), (to, who))) = (ctx, dsubst_e_e to who e, t, i)

    fun transform_proping (pr, kdown) = pr
    fun transform_kinding (kd, kdown) = kd
    fun transform_wfkind (wk, kdown) = wk
    fun transform_tyeq (te, kdown) = te

    fun transformer_typing _ _ = NONE
    end)

fun dsubst_e_ty to who ty = ExprDerivHelper.transform_typing (ty, ((), (to, who)))

fun dsubst0_e_ty to = dsubst_e_ty to 0
end
end
