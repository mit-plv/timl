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

fun as_KdRec name wk kd =
  let
      val jwk = extract_judge_wfkind wk
      val jkd = extract_judge_kinding kd
  in
      (#1 jwk, CRec (name, #2 jwk, #2 jkd), #2 jwk)
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

fun as_TyEqRec name1 name2 ke te =
  let
      val jke = extract_judge_kdeq ke
      val jte = extract_judge_tyeq te
  in
      (#1 jke, CRec (name1, #2 jke, #2 jte), CRec (name2, #3 jke, #3 jte))
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
      val (_, k, t1) = extract_c_rec t
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
            val (name, _, _) = extract_c_rec (#2 judge)
            val (wk, up1) = transform_wfkind (wk, down)
            val jwk = extract_judge_wfkind wk
            val (kd, up2) = transform_kinding (kd, Action.add_kind (#2 jwk, down))
        in
            (KdRec (as_KdRec name wk kd, wk, kd), combine [up1, up2])
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
            val (name1, _, _) = extract_c_rec (#2 judge)
            val (name2, _, _) = extract_c_rec (#3 judge)
            val (ke, up1) = transform_kdeq (ke, down)
            val jke = extract_judge_kdeq ke
            val (te, up2) = transform_tyeq (te, Action.add_kind (#2 jke, down))
        in
            (TyEqRec (as_TyEqRec name1 name2 ke te, ke, te), combine [up1, up2])
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

structure CloConv =
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
    | CRec (name, k, c) =>
      let
          val c = transform_type c
      in
          CRec (name, k, c)
      end
    | CRef c => CRef (transform_type c)
    | CUnOp (opr, c) => CUnOp (opr, transform_type c)

structure CstrHelper = CstrDerivGenericOnlyDownTransformer(
    struct
    type down = kctx

    fun add_kind (k, kctx) = k :: kctx

    fun on_pr_leaf ((_, p), kctx) = (kctx, p)
    fun on_ke_leaf ((_, k1, k2), kctx) = (kctx, k1, k2)
    fun on_kd_leaf ((_, c, k), kctx) = (kctx, transform_type c, k)
    fun on_wk_leaf ((_, k), kctx) = (kctx, k)
    fun on_wp_leaf ((_, p), kctx) = (kctx, p)
    fun on_te_leaf ((_, t1, t2), kctx) = (kctx, transform_type t1, transform_type t2)

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
              val te1 = ShiftCtx.shift0_ctx_te [KType] $ on_tyeq (te1, kctx)
              val pr = ShiftCtx.shift0_ctx_pr [KType] $ on_proping (pr, kctx)
              val te2 = ShiftCtx.shift0_ctx_te [KType] $ on_tyeq (te2, kctx)
              val te1 = TyEqBinOp (as_TyEqBinOp CBTypeProd (TyEqVar (KType :: kctx, CVar 0, CVar 0)) te1, TyEqVar (KType :: kctx, CVar 0, CVar 0), te1)
              val te = TyEqArrow (as_TyEqArrow te1 pr te2, te1, pr, te2)
              val ke = KdEqKType (kctx, KType, KType)
              val te = ShiftCtx.shift0_ctx_te [KType] te
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
              val kd1 = ShiftCtx.shift0_ctx_kd [KType] $ on_kinding (kd1, kctx)
              val kd2 = ShiftCtx.shift0_ctx_kd [KType] $ on_kinding (kd2, kctx)
              val kd3 = ShiftCtx.shift0_ctx_kd [KType] $ on_kinding (kd3, kctx)
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

structure ExprHelper = ExprDerivGenericOnlyDownTransformer(
    struct
    type kdown = kctx
    type tdown = tctx
    type down = kdown * tdown

    fun add_kind (k, (kctx, tctx)) = (k :: kctx, map (shift_c_c 1 0) tctx)
    fun add_type (t, tctx) = t :: tctx

    fun on_ty_leaf (ty as ((_, _), e, t, i), (kctx, tctx)) =
      case e of
          EVar x => ((kctx, tctx), e, List.nth (tctx, x), T0)
        | EConst cn => ((kctx, tctx), e, const_type cn, T0)
        | _ => raise (Impossible "CloConv")

    val transform_proping = CstrHelper.transform_proping
    val transform_kinding = CstrHelper.transform_kinding
    val transform_wfkind = CstrHelper.transform_wfkind
    val transform_tyeq = CstrHelper.transform_tyeq

    fun debug s = ()

    fun transformer_typing on_typing (ty, (kctx, tctx)) =
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
                                                             val wk = transform_wfkind (wk, ori_kinds)
                                                         in
                                                             (#2 jwk :: ori_kinds, wk :: ori_wks)
                                                         end) (new_kinds, []) ori_wks
                      val ori_kinds = take (all_kinds, cnt_wks)
                      val new_types = map (shift_c_c cnt_wks 0) new_types

                      val kd_arg = foldli (fn (j, x, kd) => dsubst_c_kd (CVar (j + cnt_wks)) (x + cnt_wks) kd) kd_arg fcv
                      val kd_arg = transform_kinding (kd_arg, all_kinds)
                      val t_arg = #2 (extract_judge_kinding kd_arg)
                      val (_, ti_abs, t_res) = extract_c_arrow (#3 j_abs)
                      val ti_abs = foldli (fn (j, x, c) => dsubst_c_c (CVar (j + cnt_wks)) (x + cnt_wks) c) ti_abs fcv
                      val kd_time = KdAdmit (all_kinds, ti_abs, KTime)
                      val kd_time = transform_kinding (kd_time, all_kinds)
                      val ti_abs = #2 (extract_judge_kinding kd_time)
                      val t_res = foldli (fn (j, x, t) => dsubst_c_c (CVar (j + cnt_wks)) (x + cnt_wks) t) t_res fcv
                      val kd_res = KdAdmit (all_kinds, t_res, KType)
                      val kd_res = transform_kinding (kd_res, all_kinds)
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
                              val t1 = foldri (fn (i, _, t) => subst0_c_c (CVar (i + cnt_wks)) (#3 (extract_c_quan t))) t_self new_wks
                              (*val t2 = shift_c_c 1 cnt_wks t1*)
                              val t2 = t1
                              fun iter t ks =
                                  case t of
                                      CQuan (QuanForall, k, t) => iter t (k :: ks)
                                    | _ => (t, ks)
                              val (t3, ks) = iter t2 []
                              val (t31, t3i, t32) = extract_c_arrow t3
                              val (_, t312) = extract_c_prod t31
                              val t4 = CArrow (CProd (CVar cnt_wks, shift_c_c 1 cnt_wks t312), shift_c_c 1 cnt_wks t3i, shift_c_c 1 cnt_wks t32)
                              val t5 = foldli (fn (i, k, t) => CForall (shift_c_k 1 (cnt_wks - 1 - i) k, t)) t4 ks
                              val t6 = CExists (KType, CProd (t5, CVar 0))
                          in
                              t6
                          end

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
                              (*val t2 = shift_c_c 1 cnt_wks t1*)
                              val t2 = t1
                              fun iter t ks =
                                case t of
                                    CQuan (CForall, k, t) => iter t (k :: ks)
                                  | _ => (t, ks)
                              val (t3, ks) = iter t2 []
                              val (t31, t3i, t32) = extract_c_arrow t3
                              val (_, t312) = extract_c_prod t31
                              val t4 = CArrow (CProd (CVar cnt_wks, shift_c_c 1 cnt_wks t312), shift_c_c 1 cnt_wks t3i, shift_c_c 1 cnt_wks t32)
                              val t5 = foldli (fn (i, k, t) => CForall (shift_c_k 1 (cnt_wks - 1 - i) k, t)) t4 ks
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
              val ty3 = foldl (fn (kd, ty) => TyAppC (as_TyAppC ty kd, ty, kd)) ty3 (map (fn kd => shift0_ctx_kd [KType] (transform_kinding (kd, kctx))) kds)
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
    end)

fun clo_conv_deriv ty = ExprHelper.transform_typing (ty, ([], []))
end
end
