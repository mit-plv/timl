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
end

functor DerivGenericTransformer(
    Action:
    sig
        type down
        type up

        val upward_base : up
        val combiner : up * up -> up

        val add_kind : (kind * down) -> down
        val add_type : (cstr * down) -> down

        val on_pr_leaf : proping_judgement * down -> proping_judgement * up
        val on_ke_leaf : kdeq_judgement * down -> kdeq_judgement * up
        val on_kd_leaf : kinding_judgement * down -> kinding_judgement * up
        val on_wk_leaf : wfkind_judgement * down -> wfkind_judgement * up
        val on_wp_leaf : wfprop_judgement * down -> wfprop_judgement * up
        val on_te_leaf : tyeq_judgement * down -> tyeq_judgement * up
        val on_ty_leaf : typing_judgement * down -> typing_judgement * up

        val transformer_proping : proping * down -> (proping * up) option
        val transformer_kdeq : (kdeq * down -> kdeq * up) * (proping * down -> proping * up) -> kdeq * down -> (kdeq * up) option
        val transformer_kinding : (kinding * down -> kinding * up) * (wfkind * down -> wfkind * up) * (kdeq * down -> kdeq * up) -> kinding * down -> (kinding * up) option
        val transformer_wfkind : (wfkind * down -> wfkind * up) * (wfprop * down -> wfprop * up) -> wfkind * down -> (wfkind * up) option
        val transformer_wfprop : (wfprop * down -> wfprop * up) * (kinding * down -> kinding * up) -> wfprop * down -> (wfprop * up) option
        val transformer_tyeq : (tyeq * down -> tyeq * up) * (proping * down -> proping * up) * (kdeq * down -> kdeq * up) * (kinding * down -> kinding * up) -> tyeq * down -> (tyeq * up) option
        val transformer_typing : (typing * down -> typing * up) * (kinding * down -> kinding * up) * (wfkind * down -> wfkind * up) * (tyeq * down -> tyeq * up) * (proping * down -> proping * up) -> typing * down -> (typing * up) option
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

and default_transform_kdeq (ke, down) =
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

and default_transform_kinding (kd, down) =
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

and default_transform_tyeq (te, down) =
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

and default_transform_typing (ty, down) =
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
            val (kd, up1) = transform_kinding (kd, down)
            val jkd = extract_judge_kinding kd
            val (ty, up2) = transform_typing (ty, Action.add_type (#2 jkd, down))
        in
            (TyAbs (as_TyAbs kd ty, kd, ty), combine [up1, up2])
        end
      | TyAppC (judge, ty, kd) =>
        let
            val (ty, up1) = transform_typing (ty, down)
            val (kd, up2) = transform_kinding (kd, down)
        in
            (TyAppC (as_TyAppC ty kd, ty, kd), combine [up1, up2])
        end
      | TyAbsC (judge, wk, ty) =>
        let
            val (wk, up1) = transform_wfkind (wk, down)
            val jwk = extract_judge_wfkind wk
            val (ty, up2) = transform_typing (ty, Action.add_kind (#2 jwk, down))
        in
            (TyAbsC (as_TyAbsC wk ty, wk, ty), combine [up1, up2])
        end
      | TyRec (judge, kd, ty) =>
        let
            val (kd, up1) = transform_kinding (kd, down)
            val jkd = extract_judge_kinding kd
            val (ty, up2) = transform_typing (ty, Action.add_type (#2 jkd, down))
        in
            (TyRec (as_TyRec kd ty, kd, ty), combine [up1, up2])
        end
      | TyFold (judge, kd, ty) =>
        let
            val (kd, up1) = transform_kinding (kd, down)
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
            val (kd1, up1) = transform_kinding (kd1, down)
            val (kd2, up2) = transform_kinding (kd2, down)
            val (ty, up3) = transform_typing (ty, down)
        in
            (TyPack (as_TyPack kd1 kd2 ty, kd1, kd2, ty), combine [up1, up2, up3])
        end
      | TyUnpack (judge, ty1, ty2) =>
        let
            val (ty1, up1) = transform_typing (ty1, down)
            val jty1 = extract_judge_typing ty1
            val (_, k, t) = extract_c_quan (#3 jty1)
            val (ty2, up2) = transform_typing (ty2, Action.add_type (t, Action.add_kind (k, down)))
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
            val (kd, up2) = transform_kinding (kd, down)
            val (inj, _) = extract_e_inj (#2 judge)
        in
            (TyInj (as_TyInj inj ty kd, ty, kd), combine [up1, up2])
        end
      | TyCase (judge, ty1, ty2, ty3) =>
        let
            val (ty1, up1) = transform_typing (ty1, down)
            val jty1 = extract_judge_typing ty1
            val (t1, t2) = extract_c_sum (#3 jty1)
            val (ty2, up2) = transform_typing (ty2, Action.add_type (t1, down))
            val (ty3, up3) = transform_typing (ty3, Action.add_type (t2, down))
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
            val (te, up2) = transform_tyeq (te, down)
        in
            (TySubTy (as_TySubTy ty te, ty, te), combine [up1, up2])
        end
      | TySubTi (judge, ty, pr) =>
        let
            val (ty, up1) = transform_typing (ty, down)
            val (pr, up2) = transform_proping (pr, down)
        in
            (TySubTi (as_TySubTi ty pr, ty, pr), combine [up1, up2])
        end
      | TyHalt (judge, ty) =>
        let
            val (ty, up1) = transform_typing (ty, down)
        in
            (TyHalt (as_TyHalt ty, ty), combine [up1])
        end
      | TyAppK (judge, ty1, ty2) =>
        let
            val (ty1, up1) = transform_typing (ty1, down)
            val (ty2, up2) = transform_typing (ty2, down)
        in
            (TyAppK (as_TyAppK ty1 ty2, ty1, ty2), combine [up1, up2])
        end
      | TyLet (judge, ty1, ty2) =>
        let
            val (ty1, up1) = transform_typing (ty1, down)
            val jty1 = extract_judge_typing ty1
            val (ty2, up2) = transform_typing (ty2, Action.add_type (#3 jty1, down))
        in
            (TyLet (as_TyLet ty1 ty2, ty1, ty2), combine [up1, up2])
        end
      | TyFix (judge, kd, ty) => raise (Impossible "TyFix transformer not implemented")

and transform_typing (ty, down) =
    case Action.transformer_typing (transform_typing, transform_kinding, transform_wfkind, transform_tyeq, transform_proping) (ty, down) of
        SOME res => res
      | NONE => default_transform_typing (ty, down)
end

functor DerivGenericOnlyDownTransformer(
    Action:
    sig
        type down

        val add_kind : (kind * down) -> down
        val add_type : (cstr * down) -> down

        val on_pr_leaf : proping_judgement * down -> proping_judgement
        val on_ke_leaf : kdeq_judgement * down -> kdeq_judgement
        val on_kd_leaf : kinding_judgement * down -> kinding_judgement
        val on_wk_leaf : wfkind_judgement * down -> wfkind_judgement
        val on_wp_leaf : wfprop_judgement * down -> wfprop_judgement
        val on_te_leaf : tyeq_judgement * down -> tyeq_judgement
        val on_ty_leaf : typing_judgement * down -> typing_judgement

        val transformer_proping : proping * down -> proping option
        val transformer_kdeq : (kdeq * down -> kdeq) * (proping * down -> proping) -> kdeq * down -> kdeq option
        val transformer_kinding : (kinding * down -> kinding) * (wfkind * down -> wfkind) * (kdeq * down -> kdeq) -> kinding * down -> kinding option
        val transformer_wfkind : (wfkind * down -> wfkind) * (wfprop * down -> wfprop) -> wfkind * down -> wfkind option
        val transformer_wfprop : (wfprop * down -> wfprop) * (kinding * down -> kinding) -> wfprop * down -> wfprop option
        val transformer_tyeq : (tyeq * down -> tyeq) * (proping * down -> proping) * (kdeq * down -> kdeq) * (kinding * down -> kinding) -> tyeq * down -> tyeq option
        val transformer_typing : (typing * down -> typing) * (kinding * down -> kinding) * (wfkind * down -> wfkind) * (tyeq * down -> tyeq) * (proping * down -> proping) -> typing * down -> typing option
    end) =
struct
structure Transformer = DerivGenericTransformer(
    struct
    type down = Action.down
    type up = unit

    val upward_base = ()
    fun combiner ((), ()) = ()

    val add_kind = Action.add_kind
    val add_type = Action.add_type

    val on_pr_leaf = (fn j => (j, ())) o Action.on_pr_leaf
    val on_ke_leaf = (fn j => (j, ())) o Action.on_ke_leaf
    val on_kd_leaf = (fn j => (j, ())) o Action.on_kd_leaf
    val on_wk_leaf = (fn j => (j, ())) o Action.on_wk_leaf
    val on_wp_leaf = (fn j => (j, ())) o Action.on_wp_leaf
    val on_te_leaf = (fn j => (j, ())) o Action.on_te_leaf
    val on_ty_leaf = (fn j => (j, ())) o Action.on_ty_leaf

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

    fun transformer_typing (on_typing, on_kinding, on_wfkind, on_tyeq, on_proping) =
      let
          val on_typing_no_up = fst o on_typing
          val on_kinding_no_up = fst o on_kinding
          val on_wfkind_no_up = fst o on_wfkind
          val on_tyeq_no_up = fst o on_tyeq
          val on_proping_no_up = fst o on_proping
      in
          Option.map (fn ty => (ty, ())) o
          Action.transformer_typing (on_typing_no_up, on_kinding_no_up, on_wfkind_no_up, on_tyeq_no_up, on_proping_no_up)
      end
    end)

val transform_proping = fst o Transformer.transform_proping
val transform_kdeq = fst o Transformer.transform_kdeq
val transform_kinding = fst o Transformer.transform_kinding
val transform_wfkind = fst o Transformer.transform_wfkind
val transform_wfprop = fst o Transformer.transform_wfprop
val transform_tyeq = fst o Transformer.transform_tyeq
val transform_typing = fst o Transformer.transform_typing
end

functor DerivGenericOnlyUpTransformer(
    Action:
    sig
        type up

        val upward_base : up
        val combiner : up * up -> up

        val on_pr_leaf : proping_judgement -> proping_judgement * up
        val on_ke_leaf : kdeq_judgement -> kdeq_judgement * up
        val on_kd_leaf : kinding_judgement -> kinding_judgement * up
        val on_wk_leaf : wfkind_judgement -> wfkind_judgement * up
        val on_wp_leaf : wfprop_judgement -> wfprop_judgement * up
        val on_te_leaf : tyeq_judgement -> tyeq_judgement * up
        val on_ty_leaf : typing_judgement -> typing_judgement * up

        val transformer_proping : proping -> (proping * up) option
        val transformer_kdeq : (kdeq -> kdeq * up) * (proping -> proping * up) -> kdeq -> (kdeq * up) option
        val transformer_kinding : (kinding -> kinding * up) * (wfkind -> wfkind * up) * (kdeq -> kdeq * up) -> kinding -> (kinding * up) option
        val transformer_wfkind : (wfkind -> wfkind * up) * (wfprop -> wfprop * up) -> wfkind -> (wfkind * up) option
        val transformer_wfprop : (wfprop -> wfprop * up) * (kinding -> kinding * up) -> wfprop -> (wfprop * up) option
        val transformer_tyeq : (tyeq -> tyeq * up) * (proping -> proping * up) * (kdeq -> kdeq * up) * (kinding -> kinding * up) -> tyeq -> (tyeq * up) option
        val transformer_typing : (typing -> typing * up) * (kinding -> kinding * up) * (wfkind -> wfkind * up) * (tyeq -> tyeq * up) * (proping -> proping * up) -> typing -> (typing * up) option
    end) =
struct
structure Transformer = DerivGenericTransformer(
    struct
    type down = unit
    type up = Action.up

    val upward_base = Action.upward_base
    val combiner = Action.combiner

    fun add_kind (_, ()) = ()
    fun add_type (_, ()) = ()

    fun on_pr_leaf (j, ()) = Action.on_pr_leaf j
    fun on_ke_leaf (j, ()) = Action.on_ke_leaf j
    fun on_kd_leaf (j, ()) = Action.on_kd_leaf j
    fun on_wk_leaf (j, ()) = Action.on_wk_leaf j
    fun on_wp_leaf (j, ()) = Action.on_wp_leaf j
    fun on_te_leaf (j, ()) = Action.on_te_leaf j
    fun on_ty_leaf (j, ()) = Action.on_ty_leaf j

    fun transformer_proping (pr, ()) = Action.transformer_proping pr

    fun transformer_kdeq (on_kdeq, on_proping) =
      let
          val on_kdeq_no_down = on_kdeq o (fn ke => (ke, ()))
          val on_proping_no_down = on_proping o (fn pr => (pr, ()))
      in
          Action.transformer_kdeq (on_kdeq_no_down, on_proping_no_down) o fst
      end

    fun transformer_kinding (on_kinding, on_wfkind, on_kdeq) =
      let
          val on_kinding_no_down = on_kinding o (fn kd => (kd, ()))
          val on_wfkind_no_down = on_wfkind o (fn wk => (wk, ()))
          val on_kdeq_no_down = on_kdeq o (fn ke => (ke, ()))
      in
          Action.transformer_kinding (on_kinding_no_down, on_wfkind_no_down, on_kdeq_no_down) o fst
      end

    fun transformer_wfkind (on_wfkind, on_wfprop) =
      let
          val on_wfkind_no_down = on_wfkind o (fn wk => (wk, ()))
          val on_wfprop_no_down = on_wfprop o (fn wp => (wp, ()))
      in
          Action.transformer_wfkind (on_wfkind_no_down, on_wfprop_no_down) o fst
      end

    fun transformer_wfprop (on_wfprop, on_kinding) =
      let
          val on_wfprop_no_down = on_wfprop o (fn wp => (wp, ()))
          val on_kinding_no_down = on_kinding o (fn kd => (kd, ()))
      in
          Action.transformer_wfprop (on_wfprop_no_down, on_kinding_no_down) o fst
      end

    fun transformer_tyeq (on_tyeq, on_proping, on_kdeq, on_kinding) =
      let
          val on_tyeq_no_down = on_tyeq o (fn te => (te, ()))
          val on_proping_no_down = on_proping o (fn pr => (pr, ()))
          val on_kdeq_no_down = on_kdeq o (fn ke => (ke, ()))
          val on_kinding_no_down = on_kinding o (fn kd => (kd, ()))
      in
          Action.transformer_tyeq (on_tyeq_no_down, on_proping_no_down, on_kdeq_no_down, on_kinding_no_down) o fst
      end

    fun transformer_typing (on_typing, on_kinding, on_wfkind, on_tyeq, on_proping) =
      let
          val on_typing_no_down = on_typing o (fn ty => (ty, ()))
          val on_kinding_no_down = on_kinding o (fn kd => (kd, ()))
          val on_wfkind_no_down = on_wfkind o (fn wk => (wk, ()))
          val on_tyeq_no_down = on_tyeq o (fn te => (te, ()))
          val on_proping_no_down = on_proping o (fn pr => (pr, ()))
      in
          Action.transformer_typing (on_typing_no_down, on_kinding_no_down, on_wfkind_no_down, on_tyeq_no_down, on_proping_no_down) o fst
      end
    end)

val transform_proping = Transformer.transform_proping o (fn pr => (pr, ()))
val transform_kdeq = Transformer.transform_kdeq o (fn ke => (ke, ()))
val transform_kinding = Transformer.transform_kinding o (fn kd => (kd, ()))
val transform_wfkind = Transformer.transform_wfkind o (fn wk => (wk, ()))
val transform_wfprop = Transformer.transform_wfprop o (fn wp => (wp, ()))
val transform_tyeq = Transformer.transform_tyeq o (fn te => (te, ()))
val transform_typing = Transformer.transform_typing o (fn ty => (ty, ()))
end

structure ShiftCtx =
struct
structure Helper = DerivGenericOnlyDownTransformer(
    struct
    open List

    type down = ctx * (int * int)

    fun add_kind (_, ((kctxd, tctxd), (kdep, tdep))) = ((kctxd, map shift0_c_c tctxd), (kdep + 1, tdep))
    fun add_type (_, ((kctxd, tctxd), (kdep, tdep))) = ((kctxd, tctxd), (kdep, tdep + 1))

    fun insert_k a b c = (mapi (fn (i, k) => shift_c_k (length c) (b - 1 - i) k) $ take (a, b)) @ c @ drop (a, b)
    fun insert_t a b c = take (a, b) @ c @ drop (a, b)

    fun on_pr_leaf ((kctx, p), ((kctxd, tctxd), (kdep, tdep))) =
      (insert_k kctx kdep kctxd, shift_c_p (length kctxd) kdep p)
    fun on_ke_leaf ((kctx, k1, k2), ((kctxd, tctxd), (kdep, tdep))) =
      (insert_k kctx kdep kctxd, shift_c_k (length kctxd) kdep k1, shift_c_k (length kctxd) kdep k2)
    fun on_kd_leaf ((kctx, c, k), ((kctxd, tctxd), (kdep, tdep))) =
      (insert_k kctx kdep kctxd, shift_c_c (length kctxd) kdep c, shift_c_k (length kctxd) kdep k)
    fun on_wk_leaf ((kctx, k), ((kctxd, tctxd), (kdep, tdep))) =
      (insert_k kctx kdep kctxd, shift_c_k (length kctxd) kdep k)
    fun on_wp_leaf ((kctx, p), ((kctxd, tctxd), (kdep, tdep))) =
      (insert_k kctx kdep kctxd, shift_c_p (length kctxd) kdep p)
    fun on_te_leaf ((kctx, t1, t2), ((kctxd, tctxd), (kdep, tdep))) =
      (insert_k kctx kdep kctxd, shift_c_c (length kctxd) kdep t1, shift_c_c (length kctxd) kdep t2)
    fun on_ty_leaf (((kctx, tctx), e, t, i), ((kctxd, tctxd), (kdep, tdep))) =
      let
          val kctx = insert_k kctx kdep kctxd
          val tctx = insert_t (map (shift_c_c (length kctxd) kdep) tctx) tdep tctxd
      in
          ((kctx, tctx), shift_e_e (length tctxd) tdep (shift_c_e (length kctxd) kdep e),
           shift_c_c (length kctxd) kdep t, shift_c_c (length kctxd) kdep i)
      end

    fun transformer_typing (on_typing, on_kinding, on_wfkind, on_tyeq, on_proping) (ty, down) =
      case ty of
          TyFix (j, kd, ty) => SOME (TyFix (on_ty_leaf (j, down), kd, ty))
        | _ => NONE

    fun transformer_proping _ = NONE
    fun transformer_kdeq _ _ = NONE
    fun transformer_kinding _ _ = NONE
    fun transformer_wfkind _ _ = NONE
    fun transformer_wfprop _ _ = NONE
    fun transformer_tyeq _ _ = NONE
    end)

fun shift_ctx_ty ctxd dep ty = Helper.transform_typing (ty, (ctxd, dep))
fun shift_ctx_kd ctxd dep kd = Helper.transform_kinding (kd, (ctxd, dep))
fun shift_ctx_te ctxd dep te = Helper.transform_tyeq (te, (ctxd, dep))
fun shift_ctx_pr ctxd dep pr = Helper.transform_proping (pr, (ctxd, dep))
fun shift_ctx_wk ctxd dep wk = Helper.transform_wfkind (wk, (ctxd, dep))
fun shift_ctx_ke ctxd dep ke = Helper.transform_kdeq (ke, (ctxd, dep))

fun shift0_ctx_ty ctxd = shift_ctx_ty ctxd (0, 0)
fun shift0_ctx_kd ctxd = shift_ctx_kd ctxd (0, 0)
fun shift0_ctx_te ctxd = shift_ctx_te ctxd (0, 0)
fun shift0_ctx_pr ctxd = shift_ctx_pr ctxd (0, 0)
fun shift0_ctx_wk ctxd = shift_ctx_wk ctxd (0, 0)
fun shift0_ctx_ke ctxd = shift_ctx_ke ctxd (0, 0)
end

structure DerivFVCstr =
struct
structure Helper = DerivGenericTransformer(
    struct
    open List
    open FVUtil

    type down = int
    type up = int list

    val upward_base = []
    val combiner = unique_merge

    fun add_kind (_, dep) = dep + 1
    fun add_type (_, dep) = dep

    fun on_pr_leaf (pr as (kctx, p), dep) = (pr, FVCstr.free_vars_c_p dep p)
    fun on_ke_leaf (ke as (kctx, k1, k2), dep) = (ke, combiner (FVCstr.free_vars_c_k dep k1, FVCstr.free_vars_c_k dep k2))
    fun on_kd_leaf (kd as (kctx, c, k), dep) = (kd, combiner (FVCstr.free_vars_c_c dep c, FVCstr.free_vars_c_k dep k))
    fun on_wk_leaf (wk as (kctx, k), dep) = (wk, FVCstr.free_vars_c_k dep k)
    fun on_wp_leaf (wp as (kctx, p), dep) = (wp, FVCstr.free_vars_c_p dep p)
    fun on_te_leaf (te as (kctx, t1, t2), dep) = (te, combiner (FVCstr.free_vars_c_c dep t1, FVCstr.free_vars_c_c dep t2))
    fun on_ty_leaf (ty as (ctx, e, t, i), dep) =
      (ty, combiner (combiner (FVCstr.free_vars_c_e dep e, FVCstr.free_vars_c_c dep t), FVCstr.free_vars_c_c dep i))

    fun transformer_typing (on_typing, on_kinding, on_wfkind, on_tyeq, on_proping) (ty, dep) =
      case ty of
          TyFix _ => SOME (ty, [])
        | _ => NONE

    fun transformer_proping _ = NONE
    fun transformer_kdeq _ _ = NONE
    fun transformer_kinding _ _ = NONE
    fun transformer_wfkind _ _ = NONE
    fun transformer_wfprop _ _ = NONE
    fun transformer_tyeq _ _ = NONE
    end)

fun free_vars_c_ty d ty = #2 (Helper.transform_typing (ty, d))

val free_vars0_c_ty = free_vars_c_ty 0
end

structure DerivFVExpr =
struct
structure Helper = DerivGenericTransformer(
    struct
    open List
    open FVUtil

    type down = int
    type up = int list

    val upward_base = []
    val combiner = unique_merge

    fun add_kind (_, dep) = dep
    fun add_type (_, dep) = dep + 1

    fun on_pr_leaf (pr as (kctx, p), dep) = (pr, [])
    fun on_ke_leaf (ke as (kctx, k1, k2), dep) = (ke, [])
    fun on_kd_leaf (kd as (kctx, c, k), dep) = (kd, [])
    fun on_wk_leaf (wk as (kctx, k), dep) = (wk, [])
    fun on_wp_leaf (wp as (kctx, p), dep) = (wp, [])
    fun on_te_leaf (te as (kctx, t1, t2), dep) = (te, [])
    fun on_ty_leaf (ty as (ctx, e, t, i), dep) =
      (ty, FVExpr.free_vars_e_e dep e)

    fun transformer_typing (on_typing, on_kinding, on_wfkind, on_tyeq, on_proping) (ty, dep) =
      case ty of
          TyFix _ => SOME (ty, [])
        | _ => NONE

    fun transformer_proping _ = NONE
    fun transformer_kdeq _ _ = NONE
    fun transformer_kinding _ _ = NONE
    fun transformer_wfkind _ _ = NONE
    fun transformer_wfprop _ _ = NONE
    fun transformer_tyeq _ _ = NONE
    end)

fun free_vars_e_ty d ty = #2 (Helper.transform_typing (ty, d))

val free_vars0_e_ty = free_vars_e_ty 0
end

structure DerivSubstTyping =
struct
structure Helper = DerivGenericOnlyDownTransformer(
    struct
    open List

    type down = typing * int

    fun add_kind (k, (to, who)) = (ShiftCtx.shift_ctx_ty ([k], []) (0, 0) to, who)
    fun add_type (t, (to, who)) = (ShiftCtx.shift_ctx_ty ([], [t]) (0, 0) to, who + 1)

    fun on_pr_leaf (pr, _) = pr
    fun on_ke_leaf (ke, _) = ke
    fun on_kd_leaf (kd, _) = kd
    fun on_wk_leaf (wk, _) = wk
    fun on_wp_leaf (wp, _) = wp
    fun on_te_leaf (te, _) = te
    fun on_ty_leaf (((kctx, tctx), e, t, i), (to, who)) =
      case e of
          EConst cn => ((kctx, take (tctx, who) @ drop (tctx, who + 1)), EConst cn, t, i)
        | _ => raise (Impossible "DerivSubstTyping")

    fun transformer_typing (on_typing, on_kinding, on_wfkind, on_tyeq, on_proping) (ty, (to, who)) =
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

    fun transformer_proping _ = NONE
    fun transformer_kdeq _ _ = NONE
    fun transformer_kinding _ _ = NONE
    fun transformer_wfkind _ _ = NONE
    fun transformer_wfprop _ _ = NONE
    fun transformer_tyeq _ _ = NONE
    end)

fun subst_ty_ty to who ty = Helper.transform_typing (ty, (to, who))

fun subst0_ty_ty to = subst_ty_ty to 0
end

structure DerivDirectSubstCstr =
struct
structure Helper = DerivGenericOnlyDownTransformer(
    struct
    open DirectSubstCstr

    type down = cstr * int

    fun add_kind (_, (to, who)) = (shift0_c_c to, who + 1)
    fun add_type (_, (to, who)) = (to, who)

    fun on_pr_leaf ((kctx, p), (to, who)) = (kctx, dsubst_c_p to who p)
    fun on_ke_leaf ((kctx, k1, k2), (to, who)) = (kctx, dsubst_c_k to who k1, dsubst_c_k to who k2)
    fun on_kd_leaf ((kctx, c, k), (to, who)) = (kctx, dsubst_c_c to who c, dsubst_c_k to who k)
    fun on_wk_leaf ((kctx, k), (to, who)) = (kctx, dsubst_c_k to who k)
    fun on_wp_leaf ((kctx, p), (to, who)) = (kctx, dsubst_c_p to who p)
    fun on_te_leaf ((kctx, t1, t2), (to, who)) = (kctx, dsubst_c_c to who t1, dsubst_c_c to who t2)
    fun on_ty_leaf ((ctx, e, t, i), (to, who)) = (ctx, dsubst_c_e to who e, dsubst_c_c to who t, dsubst_c_c to who i)

    fun transformer_typing (on_typing, on_kinding, on_wfkind, on_tyeq, on_proping) (ty, (to, who)) =
      case ty of
          TyFix _ => SOME ty
        | _ => NONE

    fun transformer_proping _ = NONE
    fun transformer_kdeq _ _ = NONE
    fun transformer_kinding _ _ = NONE
    fun transformer_wfkind _ _ = NONE
    fun transformer_wfprop _ _ = NONE
    fun transformer_tyeq _ _ = NONE
    end)

fun dsubst_c_ty to who ty = Helper.transform_typing (ty, (to, who))
fun dsubst_c_kd to who kd = Helper.transform_kinding (kd, (to, who))
fun dsubst_c_wk to who wk = Helper.transform_wfkind (wk, (to, who))

fun dsubst0_c_ty to = dsubst_c_ty to 0
fun dsubst0_c_kd to = dsubst_c_kd to 0
fun dsubst0_c_wk to = dsubst_c_wk to 0
end

structure DerivDirectSubstExpr =
struct
structure Helper = DerivGenericOnlyDownTransformer(
    struct
    open DirectSubstExpr

    type down = expr * int

    fun add_kind (_, (to, who)) = (shift0_c_e to, who)
    fun add_type (_, (to, who)) = (shift0_e_e to, who + 1)

    fun on_pr_leaf (pr, _) = pr
    fun on_ke_leaf (ke, _) = ke
    fun on_kd_leaf (kd, _) = kd
    fun on_wk_leaf (wk, _) = wk
    fun on_wp_leaf (wp, _) = wp
    fun on_te_leaf (te, _) = te
    fun on_ty_leaf ((ctx, e, t, i), (to, who)) = (ctx, dsubst_e_e to who e, t, i)

    fun transformer_typing (on_typing, on_kinding, on_wfkind, on_tyeq, on_proping) (ty, (to, who)) =
      case ty of
          TyFix _ => SOME ty
        | _ => NONE

    fun transformer_proping _ = NONE
    fun transformer_kdeq _ _ = NONE
    fun transformer_kinding _ _ = NONE
    fun transformer_wfkind _ _ = NONE
    fun transformer_wfprop _ _ = NONE
    fun transformer_tyeq _ _ = NONE
    end)

fun dsubst_e_ty to who ty = Helper.transform_typing (ty, (to, who))

fun dsubst0_e_ty to = dsubst_e_ty to 0
end

(*structure DerivChangeContext =
struct
structure Helper = DerivGenericOnlyDownTransformer(
    struct
    type down = ctx

    fun add_kind (k, (kctx, tctx)) = (k :: kctx, map shift0_c_c tctx)
    fun add_type (t, (kctx, tctx)) = (kctx, t :: tctx)

    fun on_pr_leaf ((_ , p), (kctx, tctx)) = (kctx, p)
    fun on_ke_leaf ((_, k1, k2), (kctx, tctx)) = (kctx, k1, k2)
    fun on_kd_leaf ((_, c, k), (kctx, tctx)) = (kctx, c, k)
    fun on_wk_leaf ((_, k), (kctx, tctx)) = (kctx, k)
    fun on_wp_leaf ((_, p), (kctx, tctx)) = (kctx, p)
    fun on_te_leaf ((_, t1, t2), (kctx, tctx)) = (kctx, t1, t2)
    fun on_ty_leaf ((_, e, t, i), ctx) = (ctx, e, t, i)

    fun transformer_typing (on_typing, on_kinding, on_wfkind, on_tyeq, on_proping) (ty, ctx) =
      case ty of
          TyFix (j, kd, ty) => SOME (TyFix (on_ty_leaf (j, ctx), kd, ty))
        | _ => NONE

    fun transformer_proping _ = NONE
    fun transformer_kdeq _ _ = NONE
    fun transformer_kinding _ _ = NONE
    fun transformer_wfkind _ _ = NONE
    fun transformer_wfprop _ _ = NONE
    fun transformer_tyeq _ _ = NONE
    end)

fun change_ctx_ty ctx ty = Helper.transform_typing (ty, ctx)
fun change_ctx_kd ctx kd = Helper.transform_kinding (kd, ctx)
fun change_ctx_wk ctx wk = Helper.transform_wfkind (wk, ctx)
fun change_ctx_te ctx te = Helper.transform_tyeq (te, ctx)
fun change_ctx_pr ctx pr = Helper.transform_proping (pr, ctx)

val change0_ctx_ty = change_ctx_ty ([], [])
val change0_ctx_kd = change_ctx_kd ([], [])
val change0_ctx_wk = change_ctx_wk ([], [])
val change0_ctx_te = change_ctx_te ([], [])
val change0_ctx_pr = change_ctx_pr ([], [])
end*)

(*structure ANF =
struct
open List
open DerivAssembler
open ShiftCtx

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

fun add_kind (k, (kctx, tctx)) = (k :: kctx, map shift0_c_c tctx)
fun add_type (t, (kctx, tctx)) = (kctx, t :: tctx)

fun concat_ctx ((kctx1, tctx1), (kctx2, tctx2)) =
  (kctx1 @ kctx2, tctx1 @ map (shift_c_c (length kctx1) 0) tctx2)

fun normalize_deriv ty = normalize ty (fn (ty, (kctxd, tctxd), ti) => (ty, ti))

and normalize ty (cont : typing * ctx * cstr -> typing * cstr) =
    case ty of
        TyVar j => cont (ty, ([], []), T0)
      | TyApp (j, ty1, ty2) =>
        normalize_name ty1
                       (fn (ty1, d1 as (kctxd1, tctxd1), ti1) =>
                           normalize_name (shift0_ctx_ty d1 ty2)
                                          (fn (ty2, d2 as (kctxd2, tctxd2), ti2) =>
                                              let
                                                  val ty1 = shift0_ctx_ty d2 ty1
                                                  val jty1 = extract_judge_typing ty1
                                                  val (_, i, _) = extract_c_arrow (#3 jty1)
                                                  val ti1 = shift_c_c (length kctxd2) 0 ti1
                                              in
                                                  cont (TyApp (as_TyApp ty1 ty2, ty1, ty2), concat_ctx (d2, d1), Tadd (Tadd (ti1, ti2), Tadd (T1, i)))
                                              end))
      | TyAppC (j, ty, kd) =>
        normalize_name ty
                       (fn (ty, d as (kctxd, tctxd), ti) =>
                           let
                               val kd = shift0_ctx_kd d kd
                           in
                               cont (TyAppC (as_TyAppC ty kd, ty, kd), d, ti)
                           end)
      | TyFold (j, kd, ty) =>
        normalize_name ty
                       (fn (ty, d as (kctxd, tctxd), ti) =>
                           let
                               val kd = shift0_ctx_kd d kd
                           in
                               cont (TyFold (as_TyFold kd ty, kd, ty), d, ti)
                           end)
      | TyUnfold (j, ty) =>
        normalize_name ty
                       (fn (ty, d as (kctxd, tctxd), ti) => cont (TyUnfold (as_TyUnfold ty, ty), d, ti))
      | TyPack (j, kd1, kd2, ty) =>
        normalize_name ty
                       (fn (ty, d as (kctxd, tctxd), ti) =>
                           let
                               val kd1 = shift0_ctx_kd d kd1
                               val kd2 = shift0_ctx_kd d kd2
                           in
                               cont (TyPack (as_TyPack kd1 kd2 ty, kd1, kd2, ty), d, ti)
                           end)
      | TyUnpack (j, ty1, ty2) =>
        normalize ty1
                  (fn (ty1, d1 as (kctxd1, tctxd1), ti1) =>
                      let
                          val jty1 = extract_judge_typing ty1
                          val (_, k, t) = extract_c_quan (#3 jty1)
                          val ty2 = shift_ctx_ty (kctxd1, map shift0_c_c tctxd1) (1, 1) ty2
                          val (ty2, ti2) = normalize ty2
                                                     (fn (ty2, d2 as (kctxd2, tctxd2), ti2) =>
                                                         cont (ty2, concat_ctx (d2, concat_ctx (([k], [t]), d1)), ti2))
                          val jty2 = extract_judge_typing ty2
                          val ty2 = TySub ((#1 jty2, #2 jty2, #3 jty2, ti2), ty2, gen_tyeq_refl (fst $ #1 jty2) (#3 jty2), PrAdmit (fst $ #1 jty2, TLe (#4 jty2, ti2)))
                      in
                          (TyUnpack (as_TyUnpack ty1 ty2, ty1, ty2), Tadd (ti1, shift_c_c ~1 0 ti2))
                      end)
      | TyConst j => cont (ty, ([], []), T0)
      | TyPair (j, ty1, ty2) =>
        normalize_name ty1
                       (fn (ty1, d1 as (kctxd1, tctxd1), ti1) =>
                           normalize_name (shift0_ctx_ty d1 ty2)
                                          (fn (ty2, d2 as (kctxd2, tctxd2), ti2) =>
                                              let
                                                  val ty1 = shift0_ctx_ty d2 ty1
                                                  val ti1 = shift_c_c (length kctxd2) 0 ti1
                                              in
                                                  cont (TyPair (as_TyPair ty1 ty2, ty1, ty2), concat_ctx (d2, d1), Tadd (ti1, ti2))
                                              end))
      | TyProj (j, ty) =>
        normalize_name ty
                       (fn (ty, d as (kctxd, tctxd), ti) =>
                           let
                               val (p, _) = extract_e_proj (#2 j)
                           in
                               cont (TyProj (as_TyProj p ty, ty), d, ti)
                           end)
      | TyInj (j, ty, kd) =>
        normalize_name ty
                       (fn (ty, d as (kctxd, tctxd), ti) =>
                           let
                               val (inj, _) = extract_e_inj (#2 j)
                               val kd = shift0_ctx_kd d kd
                           in
                               cont (TyInj (as_TyInj inj ty kd, ty, kd), d, ti)
                           end)
      | TyCase (j, ty1, ty2, ty3) =>
        normalize_name ty1
                       (fn (ty1, d1 as (kctxd, tctxd), ti) =>
                           let
                               val ty2 = shift_ctx_ty d1 (0, 1) ty2
                               val ty3 = shift_ctx_ty d1 (0, 1) ty3
                               val (ty2, ti2) = normalize_deriv ty2
                               val (ty3, ti3) = normalize_deriv ty3
                               val jty2 = extract_judge_typing ty2
                               val jty3 = extract_judge_typing ty3
                           in
                               cont (TyCase (as_TyCase ty1 ty2 ty3, ty1, ty2, ty3), d1, Tadd (ti, Tmax (ti2, ti3)))
                           end)
      | TyNew (j, ty) =>
        normalize_name ty
                       (fn (ty, d as (kctxd, tctxd), ti) => cont (TyNew (as_TyNew ty, ty), d, ti))
      | TyRead (j, ty) =>
        normalize_name ty
                       (fn (ty, d as (kctxd, tctxd), ti) => cont (TyRead (as_TyRead ty, ty), d, ti))
      | TyWrite (j, ty1, ty2) =>
        normalize_name ty1
                       (fn (ty1, d1 as (kctxd1, tctxd1), ti1) =>
                           normalize_name (shift0_ctx_ty d1 ty2)
                                          (fn (ty2, d2 as (kctxd2, tctxd2), ti2) =>
                                              let
                                                  val ty1 = shift0_ctx_ty d2 ty1
                                                  val jty1 = extract_judge_typing ty1
                                                  val tylet1 = TyConst (#1 jty1, EConst ECTT, CTypeUnit, T0)
                                                  val (tylet2, ti3) = cont (TyVar ((fst $ #1 jty1, CTypeUnit :: (snd $ #1 jty1)), EVar 0, CTypeUnit, T0), concat_ctx (([], [CTypeUnit]), concat_ctx (d2, d1)), Tadd (shift_c_c (length kctxd2) 0 ti1, ti2))
                                              in
                                                  (TyLet (as_TyLet tylet1 tylet2, tylet1, tylet2), ti3)
                                              end))
      | TyLet (j, ty1, ty2) =>
        normalize ty1
                  (fn (ty1, d1 as (kctxd1, tctxd1), ti1) =>
                      let
                          val jty1 = extract_judge_typing ty1
                          val ty2 = shift_ctx_ty d1 (0, 1) ty2
                          val (ty2, ti2) =
                              normalize ty2 (fn (ty2, d2 as (kctxd2, tctxd2), ti2) => cont (ty2, concat_ctx (d2, concat_ctx (([], [#3 jty1]), d1)), Tadd (shift_c_c (length kctxd2) 0 ti1, ti2)))
                      in
                          (TyLet (as_TyLet ty1 ty2, ty1, ty2), ti2)
                      end)
      | TySub (j, ty, te, pr) =>
        normalize ty
                  (fn (ty, d as (kctxd, tctxd), _) =>
                      let
                          val te = shift0_ctx_te d te
                          val pr = shift0_ctx_pr d pr
                          val jpr = extract_judge_proping pr
                          val (_, _, i2) = extract_p_bin_pred $ #2 jpr
                          val jty = extract_judge_typing ty
                          val pr = PrAdmit (fst $ #1 jty, TLe (#4 jty, #4 jty))
                      in
                          cont (TySub (as_TySub ty te pr, ty, te, pr), d, i2)
                      end)
      | TyFix (j, kd, ty) =>
        let
            val (ty, _) = normalize_deriv ty
            val jkd = extract_judge_kinding kd
            val jty = extract_judge_typing ty
            fun unfold_CForalls t ks =
              case t of
                  CQuan (QuanForall, k, t) => unfold_CForalls t (k :: ks)
                | _ => (t, ks)
            val (t, ks) = unfold_CForalls (#2 jkd) []
            val (t1, i, t2) = extract_c_arrow t
            val te = gen_tyeq_refl (fst $ #1 jty) (#3 jty)
            val pr = PrAdmit (fst $ #1 jty, TLe (#4 jty, i))
            val ty = TySub (as_TySub ty te pr, ty, te, pr)
        in
            cont (TyFix (as_TyFix (#1 j) kd ty, kd, ty), ([], []), T0)
        end
      | _ => raise (Impossible "normalize")

and normalize_name ty cont =
    normalize ty
              (fn (ty, d as (kctxd, tctxd), ti1) =>
                  let
                      val jty = extract_judge_typing ty
                  in
                      if is_atomic (#2 jty) then
                          cont (ty, d, ti1)
                      else
                          let
                              val t = #3 jty
                              val tylet1 = ty
                              val (tylet2, ti2) = cont (TyVar ((fst $ #1 jty, t :: (snd $ #1 jty)), EVar 0, t, T0), concat_ctx (([], [t]), d), ti1)
                          in
                              (TyLet (as_TyLet tylet1 tylet2, tylet1, tylet2), ti2)
                          end
                  end)

and is_atomic e =
    case e of
        EVar _ => true
      | EConst _ => true
      | EAbs _ => true
      | ERec _ => true
      | EAbsC _ => true
      | EFix _ => true
      | _ => false
end*)

structure CPS =
struct
open List
open DerivAssembler
open ShiftCtx
open DerivSubstTyping

fun send_to_cont cont ty =
  case cont of
      TyAbs (_, _, ty_body) => subst0_ty_ty ty ty_body
    | _ => TyAppK (as_TyAppK cont ty, cont, ty)

fun transform_type t =
  case t of
      CVar x => CVar x
    | CConst cn => CConst cn
    | CBinOp (opr, t1, t2) => CBinOp (opr, transform_type t1, transform_type t2)
    | CIte (i1, i2, i3) => CIte (transform_type i1, transform_type i2, transform_type i3)
    | CTimeAbs c => CTimeAbs (transform_type c)
    | CTimeApp (arity, c1, c2) => CTimeApp (arity, transform_type c1, transform_type c2)
    | CArrow (t1, i, t2) =>
      let
          val t1 = shift0_c_c $ transform_type t1
          val i = shift0_c_c $ transform_type i
          val t2 = shift0_c_c $ transform_type t2
          val t2 = CArrow (t2, CVar 0, CTypeUnit)
          val t = CForall (KTime, CArrow (CProd (t1, t2), Tadd (i, CVar 0), CTypeUnit))
      in
          t
      end
    | CAbs c => CAbs (transform_type c)
    | CApp (c1, c2) => CApp (transform_type c1, transform_type c2)
    | CQuan (QuanForall, k, t) =>
      let
          val t = shift0_c_c $ transform_type t
          val t = CArrow (t, CVar 0, CTypeUnit)
          val t = CForall (KTime, CArrow (t, CVar 0, CTypeUnit))
          val t = CForall (k, t)
      in
          t
      end
    | CQuan (QuanExists, k, t) => CExists (k, transform_type t)
    | CRec (k, c) => CRec (k, transform_type c)
    | CRef c => CRef (transform_type c)
    | CUnOp (opr, c) => CUnOp (opr, transform_type c)

fun transform_kinding kd =
  case kd of
      KdVar (kctx, CVar x, k) => KdVar (kctx, CVar x, shift_c_k (1 + x) 0 $ nth (kctx, x))
    | KdConst (kctx, CConst cn, k) => KdConst (kctx, CConst cn, const_kind cn)
    | KdBinOp ((kctx, CBinOp (opr, t1, t2), k), kd1, kd2) =>
      let
          val kd1 = transform_kinding kd1
          val kd2 = transform_kinding kd2
      in
          KdBinOp (as_KdBinOp opr kd1 kd2, kd1, kd2)
      end
    | KdIte ((kctx, CIte (i1, i2, i3), k), kd1, kd2, kd3) =>
      let
          val kd1 = transform_kinding kd1
          val kd2 = transform_kinding kd2
          val kd3 = transform_kinding kd3
      in
          KdIte (as_KdIte kd1 kd2 kd3, kd1, kd2, kd3)
      end
    | KdArrow ((kctx, CArrow (t1, i, t2), k), kd1, kd2, kd3) =>
      let
          val kd1 = shift0_ctx_kd ([KTime], []) $ transform_kinding kd1
          val kd2 = shift0_ctx_kd ([KTime], []) $ transform_kinding kd2
          val kd3 = shift0_ctx_kd ([KTime], []) $ transform_kinding kd3
          val jkd3 = extract_judge_kinding kd3
          val kd3 = KdArrow (as_KdArrow kd3 (KdVar (#1 jkd3, CVar 0, KTime)) (KdConst (#1 jkd3, CTypeUnit, KType)), kd3, KdVar (#1 jkd3, CVar 0, KTime), KdConst (#1 jkd3, CTypeUnit, KType))
          val kdi = KdVar (#1 jkd3, CVar 0, KTime)
          val kd2 = KdBinOp (as_KdBinOp CBTimeAdd kd2 kdi, kd2, kdi)
          val kd = KdArrow (as_KdArrow (KdBinOp (as_KdBinOp CBTypeProd kd1 kd3, kd1, kd3)) kd2 (KdConst (#1 jkd3, CTypeUnit, KType)), KdBinOp (as_KdBinOp CBTypeProd kd1 kd3, kd1, kd3), kd2, KdConst (#1 jkd3, CTypeUnit, KType))
      in
          KdQuan (as_KdQuan QuanForall (WfKdBaseSort (kctx, KTime)) kd, WfKdBaseSort (kctx, KTime), kd)
      end
    | KdAbs ((kctx, CAbs c, k), wk, kd) =>
      let
          val kd = transform_kinding kd
      in
          KdAbs (as_KdAbs wk kd, wk, kd)
      end
    | KdApp ((kctx, CApp (c1, c2), k), kd1, kd2) =>
      let
          val kd1 = transform_kinding kd1
          val kd2 = transform_kinding kd2
      in
          KdApp (as_KdApp kd1 kd2, kd1, kd2)
      end
    | KdTimeAbs ((kctx, CTimeAbs c, k), kd) =>
      let
          val kd = transform_kinding kd
      in
          KdTimeAbs (as_KdTimeAbs kd, kd)
      end
    | KdTimeApp ((kctx, CTimeApp (arity, c1, c2), k), kd1, kd2) =>
      let
          val kd1 = transform_kinding kd1
          val kd2 = transform_kinding kd2
      in
          KdTimeApp (as_KdTimeApp kd1 kd2, kd1, kd2)
      end
    | KdQuan ((kctx, CQuan (QuanForall, k, t), _), wk, kd) =>
      let
          val kd = shift0_ctx_kd ([KTime], []) $ transform_kinding kd
          val jkd = extract_judge_kinding kd
          val kd = KdArrow (as_KdArrow kd (KdVar (#1 jkd, CVar 0, KTime)) (KdConst (#1 jkd, CTypeUnit, KType)), kd, KdVar (#1 jkd, CVar 0, KTime), KdConst (#1 jkd, CTypeUnit, KType))
          val kd = KdArrow (as_KdArrow kd (KdVar (#1 jkd, CVar 0, KTime)) (KdConst (#1 jkd, CTypeUnit, KType)), kd, KdVar (#1 jkd, CVar 0, KTime), KdConst (#1 jkd, CTypeUnit, KType))
          val kd = KdQuan (as_KdQuan QuanForall (WfKdBaseSort (tl $ #1 jkd, KTime)) kd, WfKdBaseSort (tl $ #1 jkd, KTime), kd)
      in
          KdQuan (as_KdQuan QuanForall wk kd, wk, kd)
      end
    | KdQuan ((kctx, CQuan (QuanExists, k, t), _), wk, kd) =>
      let
          val kd = transform_kinding kd
      in
          KdQuan (as_KdQuan QuanExists wk kd, wk, kd)
      end
    | KdRec ((kctx, CRec (k, c), _), wk, kd) =>
      let
          val kd = transform_kinding kd
      in
          KdRec (as_KdRec wk kd, wk, kd)
      end
    | KdRef ((kctx, CRef c, k), kd) =>
      let
          val kd = transform_kinding kd
      in
          KdRef (as_KdRef kd, kd)
      end
    | KdEq (j, kd, ke) =>
      let
          val kd = transform_kinding kd
      in
          KdEq (as_KdEq kd ke, kd, ke)
      end
    | KdUnOp ((kctx, CUnOp (opr, c), k), kd) =>
      let
          val kd = transform_kinding kd
      in
          KdUnOp (as_KdUnOp opr kd, kd)
      end
    | KdAdmit (kctx, c, k) => KdAdmit (kctx, transform_type c, k)
    | _ => raise (Impossible "transform_kinding")

fun transform_tyeq te =
  case te of
      TyEqVar j => TyEqVar j
    | TyEqConst j => TyEqConst j
    | TyEqBinOp ((_, CBinOp (opr, _, _), _), te1, te2) =>
      let
          val te1 = transform_tyeq te1
          val te2 = transform_tyeq te2
      in
          TyEqBinOp (as_TyEqBinOp opr te1 te2, te1, te2)
      end
    | TyEqIte (j, te1, te2, te3) =>
      let
          val te1 = transform_tyeq te1
          val te2 = transform_tyeq te2
          val te3 = transform_tyeq te3
      in
          TyEqIte (as_TyEqIte te1 te2 te3, te1, te2, te3)
      end
    | TyEqArrow (j, te1, pr, te2) =>
      let
          val te1 = shift0_ctx_te ([KTime], []) $ transform_tyeq te1
          val pr = shift0_ctx_pr ([KTime], []) pr
          val te2 = shift0_ctx_te ([KTime], []) $ transform_tyeq te2
          val jte2 = extract_judge_tyeq te2
          val te2 = TyEqArrow (as_TyEqArrow te2 (PrAdmit (#1 jte2, TEq (CVar 0, CVar 0))) (TyEqConst (#1 jte2, CTypeUnit, CTypeUnit)), te2, PrAdmit (#1 jte2, TEq (CVar 0, CVar 0)), TyEqConst (#1 jte2, CTypeUnit, CTypeUnit))
          val jpr = extract_judge_proping pr
          val (_, i1, i2) = extract_p_bin_pred (#2 jpr)
          val pr = PrAdmit (#1 jte2, TEq (Tadd (i1, CVar 0) , Tadd (i2, CVar 0)))
          val te = TyEqArrow (as_TyEqArrow (TyEqBinOp (as_TyEqBinOp CBTypeProd te1 te2, te1, te2)) pr (TyEqConst (#1 jte2, CTypeUnit, CTypeUnit)), TyEqBinOp (as_TyEqBinOp CBTypeProd te1 te2, te1, te2), pr, TyEqConst (#1 jte2, CTypeUnit, CTypeUnit))
      in
          TyEqQuan (as_TyEqQuan QuanForall (KdEqBaseSort (#1 j, KTime, KTime)) te, KdEqBaseSort (#1 j, KTime, KTime), te)
      end
    | TyEqApp (j, te1, te2) =>
      let
          val te1 = transform_tyeq te1
          val te2 = transform_tyeq te2
      in
          TyEqApp (as_TyEqApp te1 te2, te1, te2)
      end
    | TyEqTimeApp ((kctx, CTimeApp (arity, _, _), _), te1, te2) =>
      let
          val te1 = transform_tyeq te1
          val te2 = transform_tyeq te2
      in
          TyEqTimeApp (as_TyEqTimeApp arity te1 te2, te1, te2)
      end
    | TyEqBeta (j, te1, te2, te3) =>
      let
          val te1 = transform_tyeq te1
          val te2 = transform_tyeq te2
          val te3 = transform_tyeq te3
      in
          TyEqBeta (as_TyEqBeta te1 te2 te3, te1, te2, te3)
      end
    | TyEqBetaRev (j, te1, te2, te3) =>
      let
          val te1 = transform_tyeq te1
          val te2 = transform_tyeq te2
          val te3 = transform_tyeq te3
      in
          TyEqBetaRev (as_TyEqBetaRev te1 te2 te3, te1, te2, te3)
      end
    | TyEqQuan ((kctx, CQuan (QuanForall, _, _), _), ke, te) =>
      let
          val te = shift0_ctx_te ([KTime], []) $ transform_tyeq te
          val jte = extract_judge_tyeq te
          val te = TyEqArrow (as_TyEqArrow te (PrAdmit (#1 jte, TEq (CVar 0, CVar 0))) (TyEqConst (#1 jte, CTypeUnit, CTypeUnit)), te, PrAdmit (#1 jte, TEq (CVar 0, CVar 0)), TyEqConst (#1 jte, CTypeUnit, CTypeUnit))
          val te = TyEqArrow (as_TyEqArrow te (PrAdmit (#1 jte, TEq (CVar 0, CVar 0))) (TyEqConst (#1 jte, CTypeUnit, CTypeUnit)), te, PrAdmit (#1 jte, TEq (CVar 0, CVar 0)), TyEqConst (#1 jte, CTypeUnit, CTypeUnit))
          val te = TyEqQuan (as_TyEqQuan QuanForall (KdEqBaseSort (tl $ #1 jte, KTime, KTime)) te, KdEqBaseSort (tl $ #1 jte, KTime, KTime), te)
      in
          TyEqQuan (as_TyEqQuan QuanForall ke te, ke, te)
      end
    | TyEqQuan ((kctx, CQuan (QuanExists, _, _), _), ke, te) =>
      let
          val te = transform_tyeq te
      in
          TyEqQuan (as_TyEqQuan QuanExists ke te, ke, te)
      end
    | TyEqRec (j, ke, te) =>
      let
          val te = transform_tyeq te
      in
          TyEqRec (as_TyEqRec ke te, ke, te)
      end
    | TyEqRef (j, te) =>
      let
          val te = transform_tyeq te
      in
          TyEqRef (as_TyEqRef te, te)
      end
    | TyEqAbs (kctx, t1, t2) => TyEqAbs (kctx, transform_type t1, transform_type t2)
    | TyEqTimeAbs (kctx, t1, t2) => TyEqTimeAbs (kctx, transform_type t1, transform_type t2)
    | TyEqUnOp ((kctx, CUnOp (opr, _), _), te) =>
      let
          val te = transform_tyeq te
      in
          TyEqUnOp (as_TyEqUnOp opr te, te)
      end
    | TyEqNat (j, kd1, kd2, pr) => TyEqNat (j, transform_kinding kd1, transform_kinding kd2, pr)
    | _ => raise (Impossible "transform_tyeq")

fun debug str = ()

fun cps_deriv ty =
  let
      val jty = extract_judge_typing ty
      val kd_arg = KdAdmit (fst $ #1 jty, #3 jty, KType)
      val kd_arg = transform_kinding kd_arg
      val jkd_arg = extract_judge_kinding kd_arg
      val ty_var = TyVar ((fst $ #1 jty, (#2 jkd_arg) :: (snd $ #1 jty)), EVar 0, #2 jkd_arg, T0)
      val ty_body = TyHalt (as_TyHalt ty_var, ty_var)
      val cont = TyAbs (as_TyAbs kd_arg ty_body, kd_arg, ty_body)
  in
      cps ty cont
  end

(*and cps_value ty cont =
    case ty of
        TyConst (_, EConst cn, t, T0) =>
        let
            val jcont = extract_judge_typing cont
            val res = (TyConst (#1 jcont, EConst cn, const_type cn, T0))
        in
            res
        end
      | TyPair (j, ty1, ty2) =>
        let
            val ty1 = cps_value ty1 cont
            val ty2 = cps_value ty2 cont
            val res = TyPair (as_TyPair ty1 ty2, ty1, ty2)
        in
            res
        end
      | TyInj ((_, EUnOp (EUInj inj, _), _, _), ty, kd) =>
        let
            val ty = cps_value ty cont
            val kd = transform_kinding kd
            val res = TyInj (as_TyInj inj ty kd, ty, kd)
        in
            res
        end
      | TyPack (j, kd1, kd2, ty) =>
        let
            val kd1 = transform_kinding kd1
            val kd2 = transform_kinding kd2
            val ty = cps_value ty cont
            val res = TyPack (as_TyPack kd1 kd2 ty, kd1, kd2, ty)
        in
            res
        end
      | TyFold (j, kd, ty) =>
        let
            val kd = transform_kinding kd
            val ty = cps_value ty cont
            val res = TyFold (as_TyFold kd ty, kd, ty)
        in
            res
        end
      | TySubTy (j, ty, te) =>
        let
            val ty = cps_value ty cont
            val te = transform_tyeq te
            val res = TySubTy (as_TySubTy ty te, ty, te)
        in
            res
        end
      | TySubTi (j, ty, pr) =>
        let
            val ty = cps_value ty cont
            (* pr is a prop about time, no need to transform *)
            val res = TySubTi (as_TySubTi ty pr, ty, pr)
        in
            res
        end
     | TyAbs (j, kd, ty) =>
        let
            val kd = shift0_ctx_kd ([KTime], []) kd
            val kd = transform_kinding kd
            val jkd = extract_judge_kinding kd
            val (t1, i, t2) = extract_c_arrow (#3 j)
            val t2 = shift0_c_c t2
            val kd2 = KdAdmit (#1 jkd, t2, KType)
            val kd2 = transform_kinding kd2
            val jkd2 = extract_judge_kinding kd2
            val t2 = #2 jkd2
            val kd2 = KdArrow (as_KdArrow kd2 (KdVar (#1 jkd, CVar 0, KTime)) (KdConst (#1 jkd, CTypeUnit, KType)), kd2, KdVar (#1 jkd, CVar 0, KTime), KdConst (#1 jkd, CTypeUnit, KType))
            val kd = KdBinOp (as_KdBinOp CBTypeProd kd kd2, kd, kd2)
            val jkd = extract_judge_kinding kd
            val (_, t_arg, t_cont) = extract_c_bin_op (#2 jkd)
            val ty = shift_ctx_ty ([KTime], [t_cont, #2 jkd]) (0, 1) ty
            val jty_old = extract_judge_typing ty
            val old_ctx = #1 (extract_judge_typing cont)
            val new_ctx = (KTime :: fst old_ctx, t_arg :: t_cont :: (#2 jkd) :: map shift0_c_c (snd old_ctx))
            val ty = cps ty (TyVar (new_ctx, EVar 1, t_cont, T0))
            val jty = extract_judge_typing ty
            val ty_get_arg = TyProj (as_TyProj ProjFst (TyVar ((fst $ #1 jty, tl $ snd $ #1 jty), EVar 1, #2 jkd, T0)), TyVar ((fst $ #1 jty, tl $ snd $ #1 jty), EVar 1, #2 jkd, T0))
            val ty = TyLet (as_TyLet ty_get_arg ty, ty_get_arg, ty)
            val ty_get_cont = TyProj (as_TyProj ProjSnd (TyVar ((fst $ #1 jty, tl $ tl $ snd $ #1 jty), EVar 0, #2 jkd, T0)), TyVar ((fst $ #1 jty, tl $ tl $ snd $ #1 jty), EVar 0, #2 jkd, T0))
            val ty = TyLet (as_TyLet ty_get_cont ty, ty_get_cont, ty)
            val jty_new = extract_judge_typing ty
            val new_i = Tadd (#4 jty_old, CVar 0)
            val ty = TySubTi ((#1 jty_new, #2 jty_new, #3 jty, new_i), ty, PrAdmit (fst $ #1 jty_new, TLe (#4 jty_new, new_i)))
            val ty = TyAbs (as_TyAbs kd ty, kd, ty)
            val ty = TyAbsC (as_TyAbsC (WfKdBaseSort (tl $ fst $ #1 jty, KTime)) ty, WfKdBaseSort (tl $ fst $ #1 jty, KTime), ty)
            val res = ty
        in
            res
        end
     | TyAbsC (j, wk, ty) =>
       let
           val jwk = extract_judge_wfkind wk
           val ty = cps_value ty (shift0_ctx_ty ([#2 jwk], []) cont)
           val res = TyAbsC (as_TyAbsC wk ty, wk, ty)
       in
           res
       end
     | _ => raise (Impossible "CPS: cps_value a non-value")*)

and cps ty cont =
    case ty of
        TyVar (_, EVar x, t, T0) =>
        let
            val () = debug "TyVar in"
            val jcont = extract_judge_typing cont
            (* the type in judgement isn't transformed, so need to get it from context *)
            val res = send_to_cont cont (TyVar (#1 jcont, EVar x, nth (snd $ #1 jcont, x), T0))
            val () = debug "TyVar out"
        in
            res
        end
      | TyApp (j, ty1, ty2) =>
        let
            val () = debug "TyApp in"
            val jty1 = extract_judge_typing ty1
            val jty2 = extract_judge_typing ty2
            val kd1 = KdAdmit (fst $ #1 jty1, #3 jty1, KType)
            val kd2 = KdAdmit (fst $ #1 jty2, #3 jty2, KType)
            val kd1 = transform_kinding kd1
            val kd2 = transform_kinding kd2
            val jkd1 = extract_judge_kinding kd1
            val jkd2 = extract_judge_kinding kd2
            val t1 = #2 jkd1
            val t2 = #2 jkd2
            val in2_cont = shift0_ctx_ty ([], [t2, t1]) cont
            val in2_jcont = extract_judge_typing in2_cont
            val in1_cont =
                let
                    val t_tmp = subst0_c_c (#2 (extract_c_arrow (#3 in2_jcont))) (#3 (extract_c_quan t1))
                    val d1 = TyVar ((fst $ #1 in2_jcont, CProd (t2, #3 in2_jcont) :: (snd $ #1 in2_jcont)), EVar 2, t1, T0)
                    val d2 = KdAdmit (fst $ #1 in2_jcont, #2 (extract_c_arrow (#3 in2_jcont)), KTime)
                    val d3 = TyAppC (as_TyAppC d1 d2, d1, d2)
                    val d4 = TyVar ((fst $ #1 in2_jcont, CProd (t2, #3 in2_jcont) :: (snd $ #1 in2_jcont)), EVar 0, CProd (t2, #3 in2_jcont), T0)
                    val d5 = TyApp (as_TyApp d3 d4, d3, d4)
                    val d6 = TyVar (#1 in2_jcont, EVar 0, t2, T0)
                    val d7 = TyPair (as_TyPair d6 in2_cont, d6, in2_cont)
                    val d8 = TyLet (as_TyLet d7 d5, d7, d5)
                    val d9 = kd2
                    (*val d1 = TyVar ((fst $ #1 in2_jcont, CProd (t2, #3 in2_jcont) :: t_tmp :: (snd $ #1 in2_jcont)), EVar 1, t_tmp, T0)
                    val d2 = TyVar ((fst $ #1 in2_jcont, CProd (t2, #3 in2_jcont) :: t_tmp :: (snd $ #1 in2_jcont)), EVar 0, CProd (t2, #3 in2_jcont), T0)
                    val d3 = TyApp (as_TyApp d1 d2, d1, d2)
                    val d4 = TyVar ((fst $ #1 in2_jcont, t_tmp :: (snd $ #1 in2_jcont)), EVar 1, t2, T0)
                    val d5 = shift0_ctx_ty ([], [t_tmp]) in2_cont
                    val d6 = TyPair (as_TyPair d4 d5, d4, d5)
                    val d7 = TyLet (as_TyLet d6 d3, d6, d3)
                    val d8 = TyVar (#1 in2_jcont, EVar 1, t1, T0)
                    val d9 = KdAdmit (fst $ #1 in2_jcont, #2 (extract_c_arrow (#3 in2_jcont)), KTime)
                    val d10 = TyAppC (as_TyAppC d8 d9, d8, d9)
                    val d11 = TyLet (as_TyLet d10 d7, d10, d7)
                    val d12 = kd2*)
                in
                    TyAbs (as_TyAbs d9 d8, d9, d8)
                end
            val in1_jcont = extract_judge_typing in1_cont
            val in0_cont =
                let
                    val d1 = cps (shift0_ctx_ty ([], [t1]) ty2) in1_cont
                    val d2 = kd1
                in
                    TyAbs (as_TyAbs d2 d1, d2, d1)
                end
            val res = cps ty1 in0_cont
            val () = debug "TyApp out"
        in
            res
        end
      | TyAbs (j, kd, ty) =>
        let
            val () = debug "TyAbs in"
            val kd = shift0_ctx_kd ([KTime], []) kd
            val kd = transform_kinding kd
            val jkd = extract_judge_kinding kd
            val (t1, i, t2) = extract_c_arrow (#3 j)
            val t2 = shift0_c_c t2
            val kd2 = KdAdmit (#1 jkd, t2, KType)
            val kd2 = transform_kinding kd2
            val jkd2 = extract_judge_kinding kd2
            val t2 = #2 jkd2
            val kd2 = KdArrow (as_KdArrow kd2 (KdVar (#1 jkd, CVar 0, KTime)) (KdConst (#1 jkd, CTypeUnit, KType)), kd2, KdVar (#1 jkd, CVar 0, KTime), KdConst (#1 jkd, CTypeUnit, KType))
            val kd = KdBinOp (as_KdBinOp CBTypeProd kd kd2, kd, kd2)
            val jkd = extract_judge_kinding kd
            val (_, t_arg, t_cont) = extract_c_bin_op (#2 jkd)
            val ty = shift_ctx_ty ([KTime], [t_cont, #2 jkd]) (0, 1) ty
            val jty_old = extract_judge_typing ty
            val old_ctx = #1 (extract_judge_typing cont)
            val new_ctx = (KTime :: fst old_ctx, t_arg :: t_cont :: (#2 jkd) :: map shift0_c_c (snd old_ctx))
            val ty = cps ty (TyVar (new_ctx, EVar 1, t_cont, T0))
            val jty = extract_judge_typing ty
            val ty_get_arg = TyProj (as_TyProj ProjFst (TyVar ((fst $ #1 jty, tl $ snd $ #1 jty), EVar 1, #2 jkd, T0)), TyVar ((fst $ #1 jty, tl $ snd $ #1 jty), EVar 1, #2 jkd, T0))
            val ty = TyLet (as_TyLet ty_get_arg ty, ty_get_arg, ty)
            val ty_get_cont = TyProj (as_TyProj ProjSnd (TyVar ((fst $ #1 jty, tl $ tl $ snd $ #1 jty), EVar 0, #2 jkd, T0)), TyVar ((fst $ #1 jty, tl $ tl $ snd $ #1 jty), EVar 0, #2 jkd, T0))
            val ty = TyLet (as_TyLet ty_get_cont ty, ty_get_cont, ty)
            val jty_new = extract_judge_typing ty
            val new_i = Tadd (#4 jty_old, CVar 0)
            val ty = TySubTi ((#1 jty_new, #2 jty_new, #3 jty, new_i), ty, PrAdmit (fst $ #1 jty_new, TLe (#4 jty_new, new_i)))
            val ty = TyAbs (as_TyAbs kd ty, kd, ty)
            val ty = TyAbsC (as_TyAbsC (WfKdBaseSort (tl $ fst $ #1 jty, KTime)) ty, WfKdBaseSort (tl $ fst $ #1 jty, KTime), ty)
            val res = send_to_cont cont ty
            val () = debug "TyAbs out"
        in
            res
        end
      | TyAppC (j, ty, kd) =>
        let
            val () = debug "TyAppC in"
            val jty = extract_judge_typing ty
            val kdt = KdAdmit (fst $ #1 jty, #3 jty, KType)
            val kdt = transform_kinding kdt
            val jkdt = extract_judge_kinding kdt
            val t = #2 jkdt
            val in1_cont = shift0_ctx_ty ([], [t]) cont
            val kd = transform_kinding kd
            val jkd = extract_judge_kinding kd
            val in1_jcont = extract_judge_typing in1_cont
            val in0_cont =
                let
                    val d1 = TyVar (#1 in1_jcont, EVar 0, t, T0)
                    val d2 = TyAppC (as_TyAppC d1 kd, d1, kd)
                    val d3 = KdAdmit (fst $ #1 in1_jcont, #2 (extract_c_arrow (#3 in1_jcont)), KTime)
                    val d4 = TyAppC (as_TyAppC d2 d3, d2, d3)
                    val d5 = TyAppK (as_TyAppK d4 in1_cont, d4, in1_cont)
                    val d6 = kdt
                    (*val t_tmp1 = subst0_c_c (#2 jkd) (#3 (extract_c_quan t))
                    val t_tmp2 = subst0_c_c (#2 (extract_c_arrow (#3 in1_jcont))) (#3 (extract_c_quan t_tmp1))
                    val d1 = TyVar ((fst $ #1 in1_jcont, t_tmp2 :: t_tmp1 :: (snd $ #1 in1_jcont)), EVar 0, t_tmp2, T0)
                    val d2 = shift0_ctx_ty ([], [t_tmp2, t_tmp1]) in1_cont
                    val d3 = TyAppK (as_TyAppK d1 d2, d1, d2)
                    val d4 = TyVar ((fst $ #1 in1_jcont, t_tmp1 :: (snd $ #1 in1_jcont)), EVar 0, t_tmp1, T0)
                    val d5 = KdAdmit (fst $ #1 in1_jcont, #2 (extract_c_arrow (#3 in1_jcont)), KTime)
                    val d6 = TyAppC (as_TyAppC d4 d5, d4, d5)
                    val d7 = TyLet (as_TyLet d6 d3, d6, d3)
                    val d8 = TyVar (#1 in1_jcont, EVar 0, t, T0)
                    val d9 = TyAppC (as_TyAppC d8 kd, d8, kd)
                    val d10 = TyLet (as_TyLet d9 d7, d9, d7)
                    val d11 = kdt*)
                    (*val t_tmp = subst0_c_c (#2 jkd) (#3 (extract_c_quan t))
                    val d1 = shift0_ctx_ty ([], [t_tmp]) in1_cont
                    val d2 = TyVar ((fst $ #1 in1_jcont, t_tmp :: (snd $ #1 in1_jcont)), EVar 0, t_tmp, T0)
                    val d3 = send_to_cont d1 d2
                    val d4 = TyVar (#1 in1_jcont, EVar 0, t, T0)
                    val d5 = TyAppC (as_TyAppC d4 kd, d4, kd)
                    val d6 = TyLet (as_TyLet d5 d3, d5, d3)
                    val d7 = kdt*)
                in
                    TyAbs (as_TyAbs d6 d5, d6, d5)
                end
            val res = cps ty in0_cont
            val () = debug "TyAppC out"
        in
            res
        end
      | TyAbsC (j, wk, ty) =>
        let
            val () = debug "TyAbsC in"
            val jwk = extract_judge_wfkind wk
            val jty = extract_judge_typing ty
            val t = shift0_c_c $ #3 jty
            val kd = KdAdmit (KTime :: #2 jwk :: #1 jwk, t, KType)
            val kd = transform_kinding kd
            val jkd = extract_judge_kinding kd
            val kd = KdArrow (as_KdArrow kd (KdVar (#1 jkd, CVar 0, KTime)) (KdConst (#1 jkd, CTypeUnit, KType)), kd, KdVar (#1 jkd, CVar 0, KTime), KdConst (#1 jkd, CTypeUnit, KType))
            val jkd = extract_judge_kinding kd
            val t = #2 jkd
            val ty = shift0_ctx_ty ([KTime], [t]) ty
            (* need to use cont's context since the type in orignal context isn't transformed *)
            val old_ctx = #1 (extract_judge_typing cont)
            val new_ctx = (KTime :: #2 jwk :: fst old_ctx, t :: map (shift_c_c 2 0) (snd old_ctx))
            val ty = cps ty (TyVar (new_ctx, EVar 0, t, T0))
            val jty_new = extract_judge_typing ty
            val ty = TySubTi ((#1 jty_new, #2 jty_new, #3 jty_new, CVar 0), ty, PrAdmit (fst $ #1 jty_new, TLe (#4 jty_new, CVar 0)))
            val ty = TyAbs (as_TyAbs kd ty, kd, ty)
            val ty = TyAbsC (as_TyAbsC (WfKdBaseSort (tl $ fst $ #1 jty_new, KTime)) ty, WfKdBaseSort (tl $ fst $ #1 jty_new, KTime), ty)
            val ty = TyAbsC (as_TyAbsC wk ty, wk, ty)
            val res = send_to_cont cont ty
            val () = debug "TyAbsC out"
        in
            res
        end
        (*let
            val jwk = extract_judge_wfkind wk
            val ty = cps_value ty (shift0_ctx_ty ([#2 jwk], []) cont)
            val ty = TyAbsC (as_TyAbsC wk ty, wk, ty)
            val res = send_to_cont cont ty
            val () = debug "TyAbsC out"
        in
            res
        end*)
      | TyRec (j, kd, ty) =>
        let
            val () = debug "TyRec in"
            val kd = transform_kinding kd
            val jkd = extract_judge_kinding kd
            val jty = extract_judge_typing ty
            val old_ctx = #1 (extract_judge_typing cont)
            val new_ctx = (fst old_ctx, (#2 jkd) :: snd old_ctx)
            val ty = cps ty (TyAbs (as_TyAbs kd (TyVar ((fst new_ctx, #2 jkd :: snd new_ctx), EVar 0, #2 jkd, T0)), kd, TyVar ((fst new_ctx, #2 jkd :: snd new_ctx), EVar 0, #2 jkd, T0)))
            val ty = TyRec (as_TyRec kd ty, kd, ty)
            val res = send_to_cont cont ty
            val () = debug "TyRec out"
        in
            res
        end
      | TyFold (j, kd, ty) =>
        let
            val () = debug "TyFold in"
            val jty = extract_judge_typing ty
            val kdt = KdAdmit (fst $ #1 jty, #3 jty, KType)
            val kdt = transform_kinding kdt
            val jkdt = extract_judge_kinding kdt
            val t = #2 jkdt
            val in1_cont = shift0_ctx_ty ([], [t]) cont
            val in1_jcont = extract_judge_typing in1_cont
            val in0_cont =
                let
                    val t_tmp = transform_type (#3 j)
                    val d1 = shift0_ctx_ty ([], [t_tmp]) in1_cont
                    val d2 = TyVar ((fst $ #1 in1_jcont, t_tmp :: (snd $ #1 in1_jcont)), EVar 0, t_tmp, T0)
                    val d3 = send_to_cont d1 d2
                    val d4 = TyVar (#1 in1_jcont, EVar 0, t, T0)
                    val d5 = transform_kinding kd
                    val d6 = TyFold (as_TyFold d5 d4, d5, d4)
                    val d7 = TyLet (as_TyLet d6 d3, d6, d3)
                    val d8 = kdt
                in
                    TyAbs (as_TyAbs d8 d7, d8, d7)
                end
            val res = cps ty in0_cont
            val () = debug "TyFold out"
        in
            res
        end
      | TyUnfold (j, ty) =>
        let
            val () = debug "TyUnfold in"
            val jty = extract_judge_typing ty
            val kdt = KdAdmit (fst $ #1 jty, #3 jty, KType)
            val kdt = transform_kinding kdt
            val jkdt = extract_judge_kinding kdt
            val t = #2 jkdt
            val in1_cont = shift0_ctx_ty ([], [t]) cont
            val in1_jcont = extract_judge_typing in1_cont
            val in0_cont =
                let
                    val t_tmp = transform_type (#3 j)
                    val d1 = shift0_ctx_ty ([], [t_tmp]) in1_cont
                    val d2 = TyVar ((fst $ #1 in1_jcont, t_tmp :: (snd $ #1 in1_jcont)), EVar 0, t_tmp, T0)
                    val d3 = send_to_cont d1 d2
                    val d4 = TyVar (#1 in1_jcont, EVar 0, t, T0)
                    val d5 = TyUnfold (as_TyUnfold d4, d4)
                    val d6 = TyLet (as_TyLet d5 d3, d5, d3)
                    val d7 = kdt
                in
                    TyAbs (as_TyAbs d7 d6, d7, d6)
                end
            val res = cps ty in0_cont
            val () = debug "TyUnfold out"
        in
            res
        end
      | TyPack (j, kd1, kd2, ty) =>
        let
            val () = debug "TyPack in"
            val kd1 = transform_kinding kd1
            val kd2 = transform_kinding kd2
            val jty = extract_judge_typing ty
            val kdt = KdAdmit (fst $ #1 jty, #3 jty, KType)
            val kdt = transform_kinding kdt
            val jkdt = extract_judge_kinding kdt
            val t = #2 jkdt
            val in1_cont = shift0_ctx_ty ([], [t]) cont
            val in1_jcont = extract_judge_typing in1_cont
            val in0_cont =
                let
                    val t_tmp = transform_type (#3 j)
                    val d1 = shift0_ctx_ty ([], [t_tmp]) in1_cont
                    val d2 = TyVar ((fst $ #1 in1_jcont, t_tmp :: (snd $ #1 in1_jcont)), EVar 0, t_tmp, T0)
                    val d3 = send_to_cont d1 d2
                    val d4 = TyVar (#1 in1_jcont, EVar 0, t, T0)
                    val d5 = TyPack (as_TyPack kd1 kd2 d4, kd1, kd2, d4)
                    val d6 = TyLet (as_TyLet d5 d3, d5, d3)
                    val d7 = kdt
                in
                    TyAbs (as_TyAbs d7 d6, d7, d6)
                end
            val res = cps ty in0_cont
            val () = debug "TyPack out"
        in
            res
        end
      | TyUnpack (j, ty1, ty2) =>
        let
            val () = debug "TyUnpack in"
            val jty1 = extract_judge_typing ty1
            val kdt = KdAdmit (fst $ #1 jty1, #3 jty1, KType)
            val kdt = transform_kinding kdt
            val jkdt = extract_judge_kinding kdt
            val t = #2 jkdt
            val (_, k, t_body) = extract_c_quan t
            val in1_cont = shift0_ctx_ty ([], [t]) cont
            val in1_jcont = extract_judge_typing in1_cont
            val in0_cont =
                let
                    val d1 = shift0_ctx_ty ([k], [t_body]) in1_cont
                    val d2 = shift_ctx_ty ([], [shift0_c_c t]) (1, 1) ty2
                    val jd2 = extract_judge_typing d2
                    val d2 = cps d2 d1
                    val d3 = TyVar (#1 in1_jcont, EVar 0, t, T0)
                    val d4 = TyUnpack (as_TyUnpack d3 d2, d3, d2)
                    val d5 = kdt
                in
                    TyAbs (as_TyAbs d5 d4, d5, d4)
                end
            val res = cps ty1 in0_cont
            val () = debug "TyUnpack out"
        in
            res
        end
      | TyConst (_, EConst cn, t, T0) =>
        let
            val () = debug "TyConst in"
            val jcont = extract_judge_typing cont
            val res = send_to_cont cont (TyConst (#1 jcont, EConst cn, const_type cn, T0))
            val () = debug "TyConst out"
        in
            res
        end
      | TyPair (j, ty1, ty2) =>
        let
            val () = debug "TyPair in"
            val jty1 = extract_judge_typing ty1
            val jty2 = extract_judge_typing ty2
            val kd1 = KdAdmit (fst $ #1 jty1, #3 jty1, KType)
            val kd2 = KdAdmit (fst $ #1 jty2, #3 jty2, KType)
            val kd1 = transform_kinding kd1
            val kd2 = transform_kinding kd2
            val jkd1 = extract_judge_kinding kd1
            val jkd2 = extract_judge_kinding kd2
            val t1 = #2 jkd1
            val t2 = #2 jkd2
            val in2_cont = shift0_ctx_ty ([], [t2, t1]) cont
            val in2_jcont = extract_judge_typing in2_cont
            val in1_cont =
                let
                    val d1 = shift0_ctx_ty ([], [CProd (t1, t2)]) in2_cont
                    val d2 = TyVar ((fst $ #1 in2_jcont, CProd (t1, t2) :: (snd $ #1 in2_jcont)), EVar 0, CProd (t1, t2), T0)
                    val d3 = send_to_cont d1 d2
                    val d4 = TyVar (#1 in2_jcont, EVar 1, t1, T0)
                    val d5 = TyVar (#1 in2_jcont, EVar 0, t2, T0)
                    val d6 = TyPair (as_TyPair d4 d5, d4, d5)
                    val d7 = TyLet (as_TyLet d6 d3, d6, d3)
                    val d8 = kd2
                in
                    TyAbs (as_TyAbs d8 d7, d8, d7)
                end
            val in1_jcont = extract_judge_typing in1_cont
            val in0_cont =
                let
                    val d1 = cps (shift0_ctx_ty ([], [t1]) ty2) in1_cont
                    val d2 = kd1
                in
                    TyAbs (as_TyAbs d2 d1, d2, d1)
                end
            val res = cps ty1 in0_cont
            val () = debug "TyPair out"
        in
            res
        end
      | TyProj (j as (_, EUnOp (EUProj p, _), _, _), ty) =>
        let
            val () = debug "TyProj in"
            val jty = extract_judge_typing ty
            val kdt = KdAdmit (fst $ #1 jty, #3 jty, KType)
            val kdt = transform_kinding kdt
            val jkdt = extract_judge_kinding kdt
            val t = #2 jkdt
            val in1_cont = shift0_ctx_ty ([], [t]) cont
            val in1_jcont = extract_judge_typing in1_cont
            val in0_cont =
                let
                    val t_tmp = transform_type (#3 j)
                    val d1 = shift0_ctx_ty ([], [t_tmp]) in1_cont
                    val d2 = TyVar ((fst $ #1 in1_jcont, t_tmp :: (snd $ #1 in1_jcont)), EVar 0, t_tmp, T0)
                    val d3 = send_to_cont d1 d2
                    val d4 = TyVar (#1 in1_jcont, EVar 0, t, T0)
                    val d5 = TyProj (as_TyProj p d4, d4)
                    val d6 = TyLet (as_TyLet d5 d3, d5, d3)
                    val d7 = kdt
                in
                    TyAbs (as_TyAbs d7 d6, d7, d6)
                end
            val res = cps ty in0_cont
            val () = debug "TyProj out"
        in
            res
        end
      | TyInj (j as (_, EUnOp (EUInj inj, _), _, _), ty, kd) =>
        let
            val () = debug "TyInj in"
            val jty = extract_judge_typing ty
            val kdt = KdAdmit (fst $ #1 jty, #3 jty, KType)
            val kdt = transform_kinding kdt
            val jkdt = extract_judge_kinding kdt
            val t = #2 jkdt
            val kd = transform_kinding kd
            val in1_cont = shift0_ctx_ty ([], [t]) cont
            val in1_jcont = extract_judge_typing in1_cont
            val in0_cont =
                let
                    val t_tmp = transform_type (#3 j)
                    val d1 = shift0_ctx_ty ([], [t_tmp]) in1_cont
                    val d2 = TyVar ((fst $ #1 in1_jcont, t_tmp :: (snd $ #1 in1_jcont)), EVar 0, t_tmp, T0)
                    val d3 = send_to_cont d1 d2
                    val d4 = TyVar (#1 in1_jcont, EVar 0, t, T0)
                    val d5 = TyInj (as_TyInj inj d4 kd, d4, kd)
                    val d6 = TyLet (as_TyLet d5 d3, d5, d3)
                    val d7 = kdt
                in
                    TyAbs (as_TyAbs d7 d6, d7, d6)
                end
            val res = cps ty in0_cont
            val () = debug "TyInj out"
        in
            res
        end
      | TyCase (j, ty, ty1, ty2) =>
        let
            val () = debug "TyCase in"
            val jty1 = extract_judge_typing ty1
            val jty2 = extract_judge_typing ty2
            val jty = extract_judge_typing ty
            val kdt = KdAdmit (fst $ #1 jty, #3 jty, KType)
            val kdt = transform_kinding kdt
            val jkdt = extract_judge_kinding kdt
            val t = #2 jkdt
            val in1_cont = shift0_ctx_ty ([], [t]) cont
            val in1_jcont = extract_judge_typing in1_cont
            val in0_cont =
                let
                    val (t1_tmp, t2_tmp) = extract_c_sum t
                    val d1 = TyVar ((fst $ #1 in1_jcont, t1_tmp :: (#3 in1_jcont) :: (snd $ #1 in1_jcont)), EVar 1, #3 in1_jcont, T0)
                    val d2 = cps (shift_ctx_ty ([], [#3 in1_jcont, t]) (0, 1) ty1) d1
                    val d3 = TyVar ((fst $ #1 in1_jcont, t2_tmp :: (#3 in1_jcont) :: (snd $ #1 in1_jcont)), EVar 1, #3 in1_jcont, T0)
                    val d4 = cps (shift_ctx_ty ([], [#3 in1_jcont, t]) (0, 1) ty2) d3
                    val d5 = TyVar ((fst $ #1 in1_jcont, (#3 in1_jcont) :: (snd $ #1 in1_jcont)), EVar 1, t, T0)
                    val d6 = TyCase (as_TyCase d5 d2 d4, d5, d2, d4)
                    val d7 = TyLet (as_TyLet in1_cont d6, in1_cont, d6)
                    val d8 = kdt
                in
                    TyAbs (as_TyAbs d8 d7, d8, d7)
                end
            val res = cps ty in0_cont
            val () = debug "TyCase out"
        in
            res
        end
      | TyNew (j, ty) =>
        let
            val jty = extract_judge_typing ty
            val kdt = KdAdmit (fst $ #1 jty, #3 jty, KType)
            val kdt = transform_kinding kdt
            val jkdt = extract_judge_kinding kdt
            val t = #2 jkdt
            val in1_cont = shift0_ctx_ty ([], [t]) cont
            val in1_jcont = extract_judge_typing in1_cont
            val in0_cont =
                let
                    val t_tmp = transform_type (#3 j)
                    val d1 = shift0_ctx_ty ([], [t_tmp]) in1_cont
                    val d2 = TyVar ((fst $ #1 in1_jcont, t_tmp :: (snd $ #1 in1_jcont)), EVar 0, t_tmp, T0)
                    val d3 = send_to_cont d1 d2
                    val d4 = TyVar (#1 in1_jcont, EVar 0, t, T0)
                    val d5 = TyNew (as_TyNew d4, d4)
                    val d6 = TyLet (as_TyLet d5 d3, d5, d3)
                    val d7 = kdt
                in
                    TyAbs (as_TyAbs d7 d6, d7, d6)
                end
        in
            cps ty in0_cont
        end
      | TyRead (j, ty) =>
        let
            val jty = extract_judge_typing ty
            val kdt = KdAdmit (fst $ #1 jty, #3 jty, KType)
            val kdt = transform_kinding kdt
            val jkdt = extract_judge_kinding kdt
            val t = #2 jkdt
            val in1_cont = shift0_ctx_ty ([], [t]) cont
            val in1_jcont = extract_judge_typing in1_cont
            val in0_cont =
                let
                    val t_tmp = transform_type (#3 j)
                    val d1 = shift0_ctx_ty ([], [t_tmp]) in1_cont
                    val d2 = TyVar ((fst $ #1 in1_jcont, t_tmp :: (snd $ #1 in1_jcont)), EVar 0, t_tmp, T0)
                    val d3 = send_to_cont d1 d2
                    val d4 = TyVar (#1 in1_jcont, EVar 0, t, T0)
                    val d5 = TyRead (as_TyRead d4, d4)
                    val d6 = TyLet (as_TyLet d5 d3, d5, d3)
                    val d7 = kdt
                in
                    TyAbs (as_TyAbs d7 d6, d7, d6)
                end
        in
            cps ty in0_cont
        end
      | TyWrite (j, ty1, ty2) =>
        let
            val jty1 = extract_judge_typing ty1
            val jty2 = extract_judge_typing ty2
            val kd1 = KdAdmit (fst $ #1 jty1, #3 jty1, KType)
            val kd2 = KdAdmit (fst $ #1 jty2, #3 jty2, KType)
            val kd1 = transform_kinding kd1
            val kd2 = transform_kinding kd2
            val jkd1 = extract_judge_kinding kd1
            val jkd2 = extract_judge_kinding kd2
            val t1 = #2 jkd1
            val t2 = #2 jkd2
            val in2_cont = shift0_ctx_ty ([], [t2, t1]) cont
            val in2_jcont = extract_judge_typing in2_cont
            val in1_cont =
                let
                    val d1 = shift0_ctx_ty ([], [CTypeUnit]) in2_cont
                    (* to model effect explicitly *)
                    val d2 = TyConst ((fst $ #1 in2_jcont, CTypeUnit :: (snd $ #1 in2_jcont)), EConst ECTT, CTypeUnit, T0)
                    val d3 = send_to_cont d1 d2
                    val d4 = TyVar (#1 in2_jcont, EVar 1, t1, T0)
                    val d5 = TyVar (#1 in2_jcont, EVar 0, t2, T0)
                    val d6 = TyWrite (as_TyWrite d4 d5, d4, d5)
                    val d7 = TyLet (as_TyLet d6 d3, d6, d3)
                    val d8 = kd2
                in
                    TyAbs (as_TyAbs d8 d7, d8, d7)
                end
            val in1_jcont = extract_judge_typing in1_cont
            val in0_cont =
                let
                    val d1 = cps (shift0_ctx_ty ([], [t1]) ty2) in1_cont
                    val d2 = kd1
                in
                    TyAbs (as_TyAbs d2 d1, d2, d1)
                end
        in
            cps ty1 in0_cont
        end
      | TySubTy (j, ty, te) =>
        let
            val () = debug "TySubTy in"
            val jty = extract_judge_typing ty
            val kdt = KdAdmit (fst $ #1 jty, #3 jty, KType)
            val kdt = transform_kinding kdt
            val jkdt = extract_judge_kinding kdt
            val t = #2 jkdt
            val in1_cont = shift0_ctx_ty ([], [t]) cont
            val in1_jcont = extract_judge_typing in1_cont
            val in0_cont =
                let
                    val t_tmp = transform_type (#3 j)
                    val d1 = in1_cont
                    val d2 = TyVar (#1 in1_jcont, EVar 0, t, T0)
                    val d3 = TySubTy ((#1 in1_jcont, EVar 0, t_tmp, T0), d2, transform_tyeq te)
                    val d4 = send_to_cont d1 d3
                    val d5 = kdt
                in
                    TyAbs (as_TyAbs d5 d4, d5, d4)
                end
            val res = cps ty in0_cont
            val in0_jcont = extract_judge_typing in0_cont
            val ti = Tadd (#4 j, #2 (extract_c_arrow $ #3 in0_jcont))
            val jres = extract_judge_typing res
            val res = TySubTi ((#1 jres, #2 jres, #3 jres, ti), res, PrAdmit (fst $ #1 jres, TLe (#4 jres, ti)))
            val () = debug "TySubTy out"
        in
            res
        end
      | TySubTi (j, ty, pr) =>
        let
            val () = debug "TySubTi in"
            val jty = extract_judge_typing ty
            val kdt = KdAdmit (fst $ #1 jty, #3 jty, KType)
            val kdt = transform_kinding kdt
            val jkdt = extract_judge_kinding kdt
            val t = #2 jkdt
            val in1_cont = shift0_ctx_ty ([], [t]) cont
            val in1_jcont = extract_judge_typing in1_cont
            val in0_cont =
                let
                    val t_tmp = transform_type (#3 j)
                    val d1 = in1_cont
                    val d2 = TyVar (#1 in1_jcont, EVar 0, t, T0)
                    val d3 = TySubTi ((#1 in1_jcont, EVar 0, t_tmp, T0), d2, PrAdmit (fst $ #1 in1_jcont, TLe (T0, T0)))
                    val d4 = send_to_cont d1 d3
                    val d5 = kdt
                in
                    TyAbs (as_TyAbs d5 d4, d5, d4)
                end
            val res = cps ty in0_cont
            val in0_jcont = extract_judge_typing in0_cont
            val ti = Tadd (#4 j, #2 (extract_c_arrow $ #3 in0_jcont))
            val jres = extract_judge_typing res
            val res = TySubTi ((#1 jres, #2 jres, #3 jres, ti), res, PrAdmit (fst $ #1 jres, TLe (#4 jres, ti)))
            val () = debug "TySubTi out"
        in
            res
        end
      | _ => raise (Impossible "CPS")
end

structure WrapLambda =
struct
structure Helper = DerivGenericOnlyDownTransformer(
    struct
    open DerivAssembler

    type down = unit

    fun add_kind (k, ()) = ()
    fun add_type (t, ()) = ()

    fun on_pr_leaf (pr, ()) = pr
    fun on_ke_leaf (ke, ()) = ke
    fun on_kd_leaf (kd, ()) = kd
    fun on_wk_leaf (wk, ()) = wk
    fun on_wp_leaf (wp, ()) = wp
    fun on_te_leaf (te, ()) = te
    fun on_ty_leaf (ty, ()) = ty

    fun transformer_typing (on_typing, on_kinding, on_wfkind, on_tyeq, on_proping) (ty, ()) =
      case ty of
          TyAbsC ((ctx, _, t, _), wk, _) =>
          let
              val (_, k, t_body) = extract_c_quan t
              val kd = KdQuan ((fst ctx, t, KType), wk, KdAdmit (k :: fst ctx, t_body, KType))
              val ty = ShiftCtx.shift0_ctx_ty ([], [t]) ty
          in
              SOME (on_typing (TyRec (as_TyRec kd ty, kd, ty), ()))
          end
        | TyAbs ((ctx, _, t, _), kd, _) =>
          let
              val (t1, i, t2) = extract_c_arrow t
              val kd = KdArrow ((fst ctx, t, KType), kd, KdAdmit (fst ctx, i, KTime), KdAdmit (fst ctx, t2, KType))
              val ty = ShiftCtx.shift0_ctx_ty ([], [t]) ty
          in
              SOME (on_typing (TyRec (as_TyRec kd ty, kd, ty), ()))
          end
        | TyRec (j, kd, ty) =>
          let
              fun unfold_ty ty wks =
                case ty of
                    TyAbsC (j, wk, ty) => unfold_ty ty (wk :: wks)
                  | _ => (ty, wks)
              val (ty, wks) = unfold_ty ty []
          in
              case ty of
                  TyAbs (j_abs, kd_arg, ty_body) =>
                  let
                      val ty_body = on_typing (ty_body, ())
                      val ty = TyAbs (as_TyAbs kd_arg ty_body, kd_arg, ty_body)
                      val ty = foldl (fn (wk, ty) => TyAbsC (as_TyAbsC wk ty, wk, ty)) ty wks
                  in
                      SOME (TyRec (as_TyRec kd ty, kd, ty))
                  end
                | _ => raise (Impossible "WrapLambda")
          end
        | TyFix _ => raise (Impossible "WrapLambda")
        | _ => NONE

    fun transformer_proping _ = NONE
    fun transformer_kdeq _ _ = NONE
    fun transformer_kinding _ _ = NONE
    fun transformer_wfkind _ _ = NONE
    fun transformer_wfprop _ _ = NONE
    fun transformer_tyeq _ _ = NONE
    end)

fun wrap_lambda_deriv ty = Helper.transform_typing (ty, ())
end

structure CloConv =
struct
structure Helper = DerivGenericOnlyDownTransformer(
    struct
    open List
    open DerivFVCstr
    open DerivFVExpr
    open DerivDirectSubstCstr
    open DerivDirectSubstExpr
    open DirectSubstCstr
    open DirectSubstExpr
    open DerivAssembler
    open ShiftCtx

    type down = ctx

    fun add_kind (k, (kctx, tctx)) = (k :: kctx, map (shift_c_c 1 0) tctx)
    fun add_type (t, (kctx, tctx)) = (kctx, t :: tctx)

    fun transform_type t =
      case t of
          CVar x => CVar x
        | CConst cn => CConst cn
        | CBinOp (opr, t1, t2) =>
          let
              val t1 = transform_type t1
              val t2 = transform_type t2
          in
              CBinOp (opr, t1, t2)
          end
        | CIte (i1, i2, i3) =>
          let
              val i1 = transform_type i1
              val i2 = transform_type i2
              val i3 = transform_type i3
          in
              CIte (i1, i2, i3)
          end
        | CTimeAbs c => CTimeAbs (transform_type c)
        | CTimeApp (arity, c1, c2) =>
          let
              val c1 = transform_type c1
              val c2 = transform_type c2
          in
              CTimeApp (arity, c1, c2)
          end
        | CArrow (t1, i, t2) =>
          let
              val t1 = transform_type t1
              val i = transform_type i
              val t2 = transform_type t2
          in
              CExists (KType, CProd (CArrow (CProd (CVar 0, ShiftCstr.shift0_c_c t1), ShiftCstr.shift0_c_c i, ShiftCstr.shift0_c_c t2), CVar 0))
          end
        | CAbs c => CAbs (transform_type c)
        | CApp (c1, c2) =>
          let
              val c1 = transform_type c1
              val c2 = transform_type c2
          in
              CApp (c1, c2)
          end
        | CQuan (QuanForall, _, _) =>
          let
              fun unfold_CForalls t ks =
                case t of
                    CQuan (QuanForall, k, t) => unfold_CForalls t (k :: ks)
                  | _ => (t, ks)
              val (t, ks) = unfold_CForalls t []
              val cnt_ks = length ks
              val (t1, i, t2) = extract_c_arrow t
              val t1 = shift_c_c 1 cnt_ks $ transform_type t1
              val i = shift_c_c 1 cnt_ks $ transform_type i
              val t2 = shift_c_c 1 cnt_ks $ transform_type t2
              val t = CArrow (CProd (CVar cnt_ks, t1), i, t2)
              val t = foldli (fn (i, k, t) => CForall (shift_c_k 1 (cnt_ks - 1 - i) k, t)) t ks
              val t = CProd (t, CVar 0)
          in
              CExists (KType, t)
          end
        | CQuan (QuanExists, k, c) =>
          let
              val c = transform_type c
          in
              CExists (k, c)
          end
        | CRec (k, c) =>
          let
              val c = transform_type c
          in
              CRec (k, c)
          end
        | CRef c => CRef (transform_type c)
        | CUnOp (opr, c) => CUnOp (opr, transform_type c)

    fun on_pr_leaf ((_, p), (kctx, _)) = (kctx, p)
    fun on_ke_leaf ((_, k1, k2), (kctx, tctx)) = (kctx, k1, k2)
    fun on_kd_leaf ((_, c, k), (kctx, tctx)) = (kctx, transform_type c, k)
    fun on_wk_leaf ((_, k), (kctx, tctx)) = (kctx, k)
    fun on_wp_leaf ((_, p), (kctx, tctx)) = (kctx, p)
    fun on_te_leaf ((_, t1, t2), (kctx, tctx)) = (kctx, transform_type t1, transform_type t2)
    fun on_ty_leaf (ty as ((_, _), e, t, i), (kctx, tctx)) =
      case e of
          EVar x => ((kctx, tctx), e, List.nth (tctx, x), T0)
        | EConst cn => ((kctx, tctx), e, const_type cn, T0)
        | _ => raise (Impossible "CloConv")

    fun debug s = ()

    fun transformer_typing (on_typing, on_kinding, on_wfkind, on_tyeq, on_proping) (ty, (kctx, tctx)) =
      case ty of
          TyRec (_, kd, ty_inner) =>
          let
              val () = debug "IN REC"
              fun unfold_ty ty wks =
                case ty of
                    TyAbsC (j, wk, ty) => unfold_ty ty (wk :: wks)
                  | _ => (ty, wks)
              val (ty_abs, wks) = unfold_ty ty_inner []
          in
              case ty_abs of
                  TyAbs (j_abs, kd_arg, ty_body) =>
                  let
                      val fcv = free_vars0_c_ty ty
                      val fev = free_vars0_e_ty ty
                      val kinds = map (fn x => shift_c_k (1 + x) 0 (nth (kctx, x))) fcv
                      val new_kinds = snd $ ListPair.unzip $
                                          foldri (fn (i, (x, k), pairs) =>
                                                     (x, foldli (fn (j, (y, _), k) => dsubst_c_k (CVar j) y k) k pairs) :: pairs)
                                          [] (ListPair.zip (fcv, kinds))
                      val (_, new_wks) = foldr
                                             (fn (k, (new_kinds, new_wks)) =>
                                                 let
                                                     val wk = WfKdAdmit (new_kinds, k)
                                                 in
                                                     (k :: new_kinds, wk :: new_wks)
                                                 end) ([], []) new_kinds
                      val types = map (fn x => nth (tctx, x)) fev
                      val new_types = map (fn t => foldli (fn (j, x, t) => dsubst_c_c (CVar j) x t) t fcv) types
                      val cnt_wks = length wks
                      val cnt_new_types = length new_types

                      val ori_wks = mapi (fn (i, wk) => foldli (fn (j, x, wk) => dsubst_c_wk (CVar (j + cnt_wks - 1 - i)) (x + cnt_wks - 1 - i) wk) wk fcv) wks
                      val (all_kinds, ori_wks) = foldr
                                                     (fn (wk, (ori_kinds, ori_wks)) =>
                                                         let
                                                             val jwk = extract_judge_wfkind wk
                                                             val wk = on_wfkind (wk, (ori_kinds, []))
                                                         in
                                                             (#2 jwk :: ori_kinds, wk :: ori_wks)
                                                         end) (new_kinds, []) ori_wks
                      val ori_kinds = take (all_kinds, cnt_wks)
                      val new_types = map (shift_c_c cnt_wks 0) new_types

                      val kd_arg = foldli (fn (j, x, kd) => dsubst_c_kd (CVar (j + cnt_wks)) (x + cnt_wks) kd) kd_arg fcv
                      val kd_arg = on_kinding (kd_arg, (all_kinds, []))
                      val t_arg = #2 (extract_judge_kinding kd_arg)
                      val (_, ti_abs, t_res) = extract_c_arrow (#3 j_abs)
                      val ti_abs = foldli (fn (j, x, c) => dsubst_c_c (CVar (j + cnt_wks)) (x + cnt_wks) c) ti_abs fcv
                      val kd_time = KdAdmit (all_kinds, ti_abs, KTime)
                      val kd_time = on_kinding (kd_time, (all_kinds, []))
                      val ti_abs = #2 (extract_judge_kinding kd_time)
                      val t_res = foldli (fn (j, x, t) => dsubst_c_c (CVar (j + cnt_wks)) (x + cnt_wks) t) t_res fcv
                      val kd_res = KdAdmit (all_kinds, t_res, KType)
                      val kd_res = on_kinding (kd_res, (all_kinds, []))
                      val t_res = #2 (extract_judge_kinding kd_res)

                      val kd_env = foldl (fn (t, kd) =>
                                             let
                                                 val kdt = KdAdmit (all_kinds, t, KType)
                                             in
                                                 KdBinOp (as_KdBinOp CBTypeProd kdt kd, kdt, kd)
                                             end) (KdConst (all_kinds, CTypeUnit, KType)) new_types
                      val t_env = #2 (extract_judge_kinding kd_env)
                      val kd_param = KdBinOp (as_KdBinOp CBTypeProd kd_env kd_arg, kd_env, kd_arg)
                      val t_param = #2 (extract_judge_kinding kd_param)

                      val kd_arrow = KdArrow (as_KdArrow kd_param kd_time kd_res, kd_param, kd_time, kd_res)
                      val t_arrow = #2 (extract_judge_kinding kd_arrow)
                      val kd_self = foldl (fn (wk, kd) => KdQuan (as_KdQuan QuanForall wk kd, wk, kd)) kd_arrow (ori_wks @ new_wks)
                      val t_self = #2 (extract_judge_kinding kd_self)

                      val kctx_base = all_kinds
                      val tctx_base = [t_param, t_self]

                      val tctx_env =
                          let
                              fun inner t tctx =
                                case t of
                                    CBinOp (CBTypeProd, t1, t2) =>
                                    inner t2 (t2 :: t1 :: tctx)
                                  | _ => tctx
                          in
                              inner t_env (t_env :: tctx_base)
                          end

                      (*val tctx_self = foldl (fn (k, t) => CForall (k, t)) (CExists (KType, CProd (CArrow (CProd (CVar 0, shift_c_c 1 0 t_arg), shift_c_c 1 0 ti_abs, shift_c_c 1 0 t_res), CVar 0))) ori_kinds :: tctx_env*)
                      val t_self_paritial =
                          let
                              val t1 = foldri (fn (j, _, t) => subst0_c_c (CVar (j + cnt_wks)) (#3 (extract_c_quan t))) t_self new_wks
                              val t2 = shift_c_c 1 cnt_wks t1
                              fun iter t ks =
                                  case t of
                                      CQuan (QuanForall, k, t) => iter t (k :: ks)
                                    | _ => (t, ks)
                              val (t3, ks) = iter t2 []
                              val (t31, t3i, t32) = extract_c_arrow t3
                              val (_, t312) = extract_c_prod t31
                              val t4 = CArrow (CProd (CVar cnt_wks, t312), t3i, t32)
                              val t5 = foldl (fn (k, t) => CForall (k, t)) t4 ks
                              val t6 = CExists (KType, CProd (t5, CVar 0))
                          in
                              t6
                          end
                      val () = debug $ PlainPrinter.str_cstr t_self_paritial

                      val tctx_self = t_self_paritial :: tctx_env

                      val tctx_arg = t_arg :: tctx_self

                      val ty_body = foldli (fn (j, x, ty) => dsubst_c_ty (CVar (j + cnt_wks)) (x + cnt_wks) ty) ty_body fcv
                      val ty_body = foldli (fn (j, x, ty) => dsubst_e_ty (EVar (j + 2)) (x + 2) ty) ty_body fev
                      val ty_body = foldri (fn (j, x, ty) => dsubst_e_ty (EVar (2 * j + 3)) (j + 2) ty) ty_body fev
                      val ty_body = on_typing (ty_body, (all_kinds, tctx_arg))

                      val ty_wrap_arg =
                          let
                              val ctx = (kctx_base, tctx_self)
                              val param_idx = length tctx_self - 2
                              val e = EProj (ProjSnd, EVar param_idx)
                              val t = t_arg
                              val i = T0
                              val ty = TyProj ((ctx, e, t, i), TyVar (ctx, EVar param_idx, t_param, T0))
                          in
                              TyLet (as_TyLet ty ty_body, ty, ty_body)
                          end

                      (*val ty_wrap_self =
                          let
                              val ctx = (kctx_base, tctx_env)
                              val self_idx = length tctx_env - 1
                              val param_idx = self_idx - 1
                              val env_idx = param_idx - 1
                              val ty0 = TyVar (ctx, EVar env_idx, t_env, T0)
                              val ty1 = TyVar (ctx, EVar self_idx, t_self, T0)
                              val ty2 = foldri (fn (i, _, ty) =>
                                                   let
                                                       val jty = extract_judge_typing ty
                                                       val (_, k, t_body) = extract_c_quan (#3 jty)
                                                       val kd = KdVar (fst $ #1 jty, CVar (i + cnt_wks), k)
                                                   in
                                                       TyAppC (as_TyAppC ty kd, ty, kd)
                                                   end) ty1 new_kinds
                              val ty3 = ShiftCtx.shift_ctx_ty (ori_kinds, []) (0, 0) ty2
                              val ty4 = foldri (fn (i, _, ty) =>
                                                   let
                                                       val jty = extract_judge_typing ty
                                                       val (_, k, t_body) = extract_c_quan (#3 jty)
                                                       val kd = KdVar (fst $ #1 jty, CVar i, k)
                                                   in
                                                       TyAppC (as_TyAppC ty kd, ty, kd)
                                                   end) ty3 ori_kinds
                              val kd5 = ShiftCtx.shift_ctx_kd (ori_kinds, []) (0, 0) kd_env
                              val ty6 = ShiftCtx.shift_ctx_ty (ori_kinds, []) (0, 0) ty0
                              val ty7 = TyPair (as_TyPair ty4 ty6, ty4, ty6)
                              val jty7 = extract_judge_typing ty7
                              val ty7_sub = TySubTi ((#1 jty7, #2 jty7, #3 jty7, T0), ty7, PrAdmit (fst $ #1 jty7, TLe (#4 jty7, T0)))
                              val jty4 = extract_judge_typing ty4
                              val (t4_1, t4_i, t4_2) = extract_c_arrow (#3 jty4)
                              val (t4_11, t4_12) = extract_c_prod t4_1
                              val t_tmp = CExists (KType, CProd (CArrow (CProd (CVar 0, shift_c_c 1 0 t4_12), shift_c_c 1 0 t4_i, shift_c_c 1 0 t4_2), CVar 0))
                              val kd8 = KdAdmit (fst $ #1 jty4, t_tmp, KType)
                              val ty9 = TyPack (as_TyPack kd8 kd5 ty7_sub, kd8, kd5, ty7_sub)
                              val ty10 = foldl (fn (_, ty) =>
                                                   let
                                                       val jty = extract_judge_typing ty
                                                       val wk = WfKdAdmit (tl $ fst $ #1 jty, hd $ fst $ #1 jty)
                                                   in
                                                       TyAbsC (as_TyAbsC wk ty, wk, ty)
                                                   end) ty9 ori_kinds
                          in
                              TyLet (as_TyLet ty10 ty_wrap_arg, ty10, ty_wrap_arg)
                          end*)

                      val ty_wrap_self =
                          let
                              val ctx = (kctx_base, tctx_env)
                              val self_idx = length tctx_env - 1
                              val param_idx = self_idx - 1
                              val env_idx = param_idx - 1
                              val ty0 = TyVar (ctx, EVar env_idx, t_env, T0)
                              val ty1 = TyVar (ctx, EVar self_idx, t_self, T0)
                              val ty2 = foldri (fn (i, _, ty) =>
                                                   let
                                                       val jty = extract_judge_typing ty
                                                       val (_, k, t_body) = extract_c_quan (#3 jty)
                                                       val kd = KdVar (fst $ #1 jty, CVar (i + cnt_wks), k)
                                                   in
                                                       TyAppC (as_TyAppC ty kd, ty, kd)
                                                   end) ty1 new_kinds
                              val ty3 = TyPair (as_TyPair ty2 ty0, ty2, ty0)
                              val kd4 = KdAdmit (kctx_base, t_self_paritial, KType)
                              val ty5 = TyPack (as_TyPack kd4 kd_env ty3, kd4, kd_env, ty3)
                          in
                              TyLet (as_TyLet ty5 ty_wrap_arg, ty5, ty_wrap_arg)
                          end

                      val ty_wrap_env =
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
                                  val ty = inner t_env ty_wrap_self
                                  val jty = extract_judge_typing ty
                                  val (kctx, tctx) = #1 jty
                                  val tctx = tl tctx
                                  val ty1 = TyVar ((kctx, tctx), EVar 0, nth (tctx, 0), T0)
                                  val ty2 = TyProj (as_TyProj ProjFst ty1, ty1)
                              in
                                  TyLet (as_TyLet ty2 ty, ty2, ty)
                              end
                          end

                      val jty_wrap_env = extract_judge_typing ty_wrap_env
                      val ty_sub = TySubTi ((#1 jty_wrap_env, #2 jty_wrap_env, #3 jty_wrap_env, ti_abs), ty_wrap_env, PrAdmit (fst $ #1 jty_wrap_env, TLe (#4 jty_wrap_env, ti_abs)))
                      val ty_fix = TyFix (as_TyFix (kctx, tctx) kd_self ty_sub, kd_self, ty_sub)

                      val ty_construct =
                          foldl (fn (i, ty) =>
                                    let
                                        val tyv = TyVar ((kctx, tctx), EVar i, nth (tctx, i), T0)
                                    in
                                        TyPair (as_TyPair tyv ty, tyv, ty)
                                    end) (TyConst ((kctx, tctx), EConst ECTT, CTypeUnit, T0)) fev
                      val kd_construct =
                          foldl (fn (t, kd) =>
                                    let
                                        val kdt = KdAdmit (kctx, t, KType)
                                    in
                                        KdBinOp (as_KdBinOp CBTypeProd kdt kd, kdt, kd)
                                    end) (KdConst (kctx, CTypeUnit, KType)) types

                      val ty_app_c =
                          foldr (fn (x, ty) =>
                                    let
                                        val jty = extract_judge_typing ty
                                        val (_, k, t_body) = extract_c_quan (#3 jty)
                                        val kd = KdVar (kctx, CVar x, k)
                                    in
                                        TyAppC (as_TyAppC ty kd, ty, kd)
                                    end) ty_fix fcv
                      (*val (_, wks) = foldr (fn (wk, (kctx, wks)) =>
                                               let
                                                   val jwk = extract_judge_wfkind wk
                                                   val wk = on_wfkind (wk, (kctx, []))
                                               in
                                                   (#2 jwk :: kctx, wk :: wks)
                                               end) (kctx, []) wks
                      val raw_kinds = map (snd o extract_judge_wfkind) wks
                      val ty_app_c = ShiftCtx.shift_ctx_ty (raw_kinds, []) (0, 0) ty_app_c
                      val ty_app_c = foldri (fn (i, _, ty) =>
                                                let
                                                    val jty = extract_judge_typing ty
                                                    val (_, k, t_body) = extract_c_quan (#3 jty)
                                                    val kd = KdVar (fst $ #1 jty, CVar i, k)
                                                in
                                                    TyAppC (as_TyAppC ty kd, ty, kd)
                                                end) ty_app_c raw_kinds*)
                      val jty_app_c = extract_judge_typing ty_app_c
                      (*val (t_app_c_1, t_app_c_i, t_app_c_2) = extract_c_arrow (#3 jty_app_c)
                      val (t_app_c_11, t_app_c_12) = extract_c_prod (t_app_c_1)*)
                      val t_tmp =
                          let
                              val t1 = #3 jty_app_c
                              val t2 = shift_c_c 1 cnt_wks t1
                              fun iter t ks =
                                case t of
                                    CQuan (CForall, k, t) => iter t (k :: ks)
                                  | _ => (t, ks)
                              val (t3, ks) = iter t2 []
                              val (t31, t3i, t32) = extract_c_arrow t3
                              val (_, t312) = extract_c_prod t31
                              val t4 = CArrow (CProd (CVar cnt_wks, t312), t3i, t32)
                              val t5 = foldl (fn (k, t) => CForall (k, t)) t4 ks
                              val t6= CProd (t5, CVar 0)
                          in
                              CExists (KType, t6)
                          end
                      (*val t_tmp = CExists (KType, CProd (CArrow (CProd (CVar 0, shift_c_c 1 0 t_app_c_12), shift_c_c 1 0 t_app_c_i, shift_c_c 1 0 t_app_c_2), CVar 0))*)
                      val kd_tmp = KdAdmit (fst $ #1 jty_app_c, t_tmp, KType)
                      (*val ty_construct_shifted = ShiftCtx.shift_ctx_ty (raw_kinds, []) (0, 0) ty_construct
                      val kd_construct_shifted = ShiftCtx.shift_ctx_kd (raw_kinds, []) (0, 0) kd_construct
                      val ty_clo = TyPair (as_TyPair ty_app_c ty_construct_shifted, ty_app_c, ty_construct_shifted)
                      val jty_clo = extract_judge_typing ty_clo
                      val ty_clo_sub = TySubTi ((#1 jty_clo, #2 jty_clo, #3 jty_clo, T0), ty_clo, PrAdmit (fst $ #1 jty_clo, TLe (#4 jty_clo, T0)))
                      val ty_pack = TyPack (as_TyPack kd_tmp kd_construct_shifted ty_clo_sub, kd_tmp, kd_construct_shifted, ty_clo_sub)*)
                      val ty_clo = TyPair (as_TyPair ty_app_c ty_construct, ty_app_c, ty_construct)
                      val jty_clo = extract_judge_typing ty_clo
                      val ty_clo_sub = TySubTi ((#1 jty_clo, #2 jty_clo, #3 jty_clo, T0), ty_clo, PrAdmit (fst $ #1 jty_clo, TLe (#4 jty_clo, T0)))
                      val ty_pack = TyPack (as_TyPack kd_tmp kd_construct ty_clo_sub, kd_tmp, kd_construct, ty_clo_sub)

                      (*val ty_res =
                          foldl (fn (_, ty) =>
                                    let
                                        val jty = extract_judge_typing ty
                                        val wk = WfKdAdmit (tl $ fst $ #1 jty, hd $ fst $ #1 jty)
                                    in
                                        TyAbsC (as_TyAbsC wk ty, wk, ty)
                                    end) ty_pack raw_kinds*)
                      val () = debug "OUT REC"
                  in
                      SOME ty_pack
                  end
                | _ => raise (Impossible "CloConv")
          end
        | TyApp ((_, _, _, ti), ty1, ty2) =>
          let
              val () = debug "IN APP"
              fun unfold_TyAppC ty kds =
                case ty of
                    TyAppC (_, ty, kd) => unfold_TyAppC ty (kd :: kds)
                  | _ => (ty, kds)
              val (ty1, kds) = unfold_TyAppC ty1 []

              val ty1 = on_typing (ty1, (kctx, tctx))
              val ty2 = on_typing (ty2, (kctx, tctx))
              val jty1 = extract_judge_typing ty1
              val jty2 = extract_judge_typing ty2
              val () = debug $ PlainPrinter.str_cstr $ #3 jty1
              val (_, _, t_clo) = extract_c_quan (#3 jty1)
              val (t_func, t_env) = extract_c_prod t_clo

              val ty3 = TyVar ((KType :: kctx, CProd (t_env, shift0_c_c (#3 jty2)) :: t_env :: t_func :: t_clo :: map shift0_c_c tctx), EVar 2, t_func, T0)
              val () = debug $ PlainPrinter.str_cstr $ #3 (extract_judge_typing ty3)
              val ty3 = foldl (fn (kd, ty) => TyAppC (as_TyAppC ty kd, ty, kd)) ty3 (map (shift0_ctx_kd ([KType], [])) kds)
              val () = debug $ PlainPrinter.str_cstr $ #3 (extract_judge_typing ty3)
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
              val () = debug $ PlainPrinter.str_expr $ #2 (extract_judge_typing ty17)
              val () = debug "OUT APP"
          in
              SOME ty17
          end
        | TyAppK ((_, _, _, ti), ty1, ty2) =>
          let
              val () = debug "IN APPK"
              fun unfold_TyAppC ty kds =
                case ty of
                    TyAppC (_, ty, kd) => unfold_TyAppC ty (kd :: kds)
                  | _ => (ty, kds)
              val (ty1, kds) = unfold_TyAppC ty1 []

              val ty1 = on_typing (ty1, (kctx, tctx))
              val ty2 = on_typing (ty2, (kctx, tctx))
              val jty1 = extract_judge_typing ty1
              val jty2 = extract_judge_typing ty2
              val (_, _, t_clo) = extract_c_quan (#3 jty1)
              val (t_func, t_env) = extract_c_prod t_clo

              val ty3 = TyVar ((KType :: kctx, CProd (t_env, ShiftCstr.shift0_c_c (#3 jty2)) :: t_env :: t_func :: t_clo :: map ShiftCstr.shift0_c_c tctx), EVar 2, t_func, T0)
              val ty3 = foldl (fn (kd, ty) => TyAppC (as_TyAppC ty kd, ty, kd)) ty3 (map (shift0_ctx_kd ([KType], [])) kds)
              val ty4 =
                  let
                      val jty3 = extract_judge_typing ty3
                  in
                      TyVar (#1 jty3, EVar 0, hd (snd $ #1 jty3), T0)
                  end
              val ty5 = TyAppK (as_TyAppK ty3 ty4, ty3, ty4)
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
              val () = debug "OUT APPK"
          in
              SOME ty17
          end
        | TyFix _ => raise (Impossible "CloConv")
        | TyAbs _ => raise (Impossible "CloConv")
        | TyAbsC _ => raise (Impossible "CloConv")
        | TyAppC _ => raise (Impossible "CloConv")
        | _ => NONE

    fun transformer_tyeq (on_tyeq, on_proping, on_kdeq, on_kinding) (te, (kctx, tctx)) =
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
              val te1 = shift_ctx_te ([KType], []) (cnt_kes, 0) $ on_tyeq (te1, (cur_kctx, tctx))
              val pr = shift_ctx_pr ([KType], []) (cnt_kes, 0) $ on_proping (pr, (cur_kctx, tctx))
              val te2 = shift_ctx_te ([KType], []) (cnt_kes, 0) $ on_tyeq (te2, (cur_kctx, tctx))
              val new_kctx = #1 (extract_judge_tyeq te1)
              val te1 = TyEqBinOp (as_TyEqBinOp CBTypeProd (TyEqVar (new_kctx, CVar cnt_kes, CVar cnt_kes)) te1, TyEqVar (new_kctx, CVar cnt_kes, CVar cnt_kes), te1)
              val te = TyEqArrow (as_TyEqArrow te1 pr te2, te1, pr, te2)
              val te = foldli (fn (j, ke, te) =>
                                  let
                                      val ke = shift_ctx_ke ([KType], []) (cnt_kes - 1 - j, 0) ke
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
              val te1 = ShiftCtx.shift0_ctx_te ([KType], []) $ on_tyeq (te1, (kctx, tctx))
              val pr = ShiftCtx.shift0_ctx_pr ([KType], []) $ on_proping (pr, (kctx, tctx))
              val te2 = ShiftCtx.shift0_ctx_te ([KType], []) $ on_tyeq (te2, (kctx, tctx))
              val te1 = TyEqBinOp (as_TyEqBinOp CBTypeProd (TyEqVar (KType :: kctx, CVar 0, CVar 0)) te1, TyEqVar (KType :: kctx, CVar 0, CVar 0), te1)
              val te = TyEqArrow (as_TyEqArrow te1 pr te2, te1, pr, te2)
              val ke = KdEqKType (kctx, KType, KType)
              val te = ShiftCtx.shift0_ctx_te ([KType], []) te
              val te = TyEqBinOp (as_TyEqBinOp CBTypeProd te (TyEqVar (KType :: kctx, CVar 0, CVar 0)), te, TyEqVar (KType :: kctx, CVar 0, CVar 0))
          in
              SOME (TyEqQuan (as_TyEqQuan QuanExists ke te, ke, te))
          end
        | _ => NONE

    fun transformer_kinding (on_kinding, on_wfkind, on_kdeq) (kd, (kctx, tctx)) =
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
              val kd1 = shift_ctx_kd ([KType], []) (cnt_wks, 0) $ on_kinding (kd1, (cur_kctx, tctx))
              val kd2 = shift_ctx_kd ([KType], []) (cnt_wks, 0) $ on_kinding (kd2, (cur_kctx, tctx))
              val kd3 = shift_ctx_kd ([KType], []) (cnt_wks, 0) $ on_kinding (kd3, (cur_kctx, tctx))
              val new_kctx = #1 (extract_judge_kinding kd1)
              val kd1 = KdBinOp (as_KdBinOp CBTypeProd (KdVar (new_kctx, CVar cnt_wks, KType)) kd1, KdVar (new_kctx, CVar cnt_wks, KType), kd1)
              val kd = KdArrow (as_KdArrow kd1 kd2 kd3, kd1, kd2, kd3)
              val kd = foldli (fn (i, wk, kd) =>
                                  let
                                      val wk = shift_ctx_wk ([KType], []) (cnt_wks - 1 - i, 0) wk
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
              val kd1 = ShiftCtx.shift0_ctx_kd ([KType], []) $ on_kinding (kd1, (kctx, tctx))
              val kd2 = ShiftCtx.shift0_ctx_kd ([KType], []) $ on_kinding (kd2, (kctx, tctx))
              val kd3 = ShiftCtx.shift0_ctx_kd ([KType], []) $ on_kinding (kd3, (kctx, tctx))
              val kd1 = KdBinOp (as_KdBinOp CBTypeProd (KdVar (KType :: kctx, CVar 0, KType)) kd1, KdVar (KType :: kctx, CVar 0, KType), kd1)
              val kd = KdArrow (as_KdArrow kd1 kd2 kd3, kd1, kd2, kd3)
              val wk = WfKdType (kctx, KType)
              val kd = KdBinOp (as_KdBinOp CBTypeProd kd (KdVar (KType :: kctx, CVar 0, KType)), kd, KdVar (KType :: kctx, CVar 0, KType))
          in
              SOME (KdQuan (as_KdQuan QuanExists wk kd, wk, kd))
          end
        | _ => NONE

    fun transformer_proping _ = NONE
    fun transformer_kdeq _ _ = NONE
    fun transformer_wfkind _ _ = NONE
    fun transformer_wfprop _ _ = NONE
    end)

fun clo_conv_deriv ty = Helper.transform_typing (ty, ([], []))
end
end
