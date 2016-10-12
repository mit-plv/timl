functor TypingDerivationTransformPass(Arg:
sig
  type down
  type up

  val on_typing_relation : MicroTiML.typing_relation * down -> MicroTiML.typing_relation * up
  val on_kinding_relation : MicroTiML.kinding_relation * down -> MicroTiML.kinding_relation * up
  val on_proping_relation : MicroTiML.proping_relation * down -> MicroTiML.proping_relation * up

  val on_kind_wellformness_relation : MicroTiML.kind_wellformedness_relation * down -> MicroTiML.kind_wellformedness_relation * up
  val on_prop_wellformness_relation : MicroTiML.prop_wellformedness_relation * down -> MicroTiML.prop_wellformedness_relation * up

  val on_type_equivalence_relation : MicroTiML.type_equivalence_relation * down -> MicroTiML.type_equivalence_relation * up
  (*val on_kind_equivalence_relation : MicroTiML.kind_equivalence_relation * down -> MicroTiML.kind_equivalence_relation * up
  val on_kind_sub_relation : MicroTiML.kind_sub_relation * down -> MicroTiML.kind_sub_relation * up*)

  val transformer_typing_derivation : (MicroTiML.typing_derivation * down -> MicroTiML.typing_derivation * up) * (MicroTiML.kinding_derivation * down -> MicroTiML.kinding_derivation * up) * (MicroTiML.proping_derivation * down -> MicroTiML.proping_derivation * up) * (MicroTiML.kind_wellformedness_derivation * down -> MicroTiML.kind_wellformedness_derivation * up) * (MicroTiML.type_equivalence_derivation * down -> MicroTiML.type_equivalence_derivation * up) -> (MicroTiML.typing_derivation * down) -> (MicroTiML.typing_derivation * up) option
  val transformer_kinding_derivation : (MicroTiML.kinding_derivation * down -> MicroTiML.kinding_derivation * up) * (MicroTiML.proping_derivation * down -> MicroTiML.proping_derivation * up) * (MicroTiML.kind_wellformedness_derivation * down -> MicroTiML.kind_wellformedness_derivation * up) -> (MicroTiML.kinding_derivation * down) -> (MicroTiML.kinding_derivation * up) option
  val transformer_proping_derivation : (MicroTiML.proping_derivation * down) -> (MicroTiML.proping_derivation * up) option

  val transformer_kind_wellformness_derivation : (MicroTiML.kind_wellformedness_derivation * down -> MicroTiML.kind_wellformedness_derivation * up) * (MicroTiML.prop_wellformedness_derivation * down -> MicroTiML.prop_wellformedness_derivation * up) -> (MicroTiML.kind_wellformedness_derivation * down) -> (MicroTiML.kind_wellformedness_derivation * up) option
  val transformer_prop_wellformness_derivation : (MicroTiML.prop_wellformedness_derivation * down -> MicroTiML.prop_wellformedness_derivation * up) * (MicroTiML.kind_wellformedness_derivation * down -> MicroTiML.kind_wellformedness_derivation * up) * (MicroTiML.kinding_derivation * down -> MicroTiML.kinding_derivation * up) -> (MicroTiML.prop_wellformedness_derivation * down) -> (MicroTiML.prop_wellformedness_derivation * up) option

  val transformer_type_equivalence_derivation : (MicroTiML.type_equivalence_derivation * down -> MicroTiML.type_equivalence_derivation * up) * (MicroTiML.kind_equivalence_derivation * down -> MicroTiML.kind_equivalence_derivation * up) * (MicroTiML.proping_derivation * down -> MicroTiML.proping_derivation * up) -> (MicroTiML.type_equivalence_derivation * down) -> (MicroTiML.type_equivalence_derivation * up) option
  val transformer_kind_equivalence_derivation : (MicroTiML.kind_sub_derivation * down -> MicroTiML.kind_sub_derivation * up) -> (MicroTiML.kind_equivalence_derivation * down) -> (MicroTiML.kind_equivalence_derivation * up) option
  val transformer_kind_sub_derivation : (MicroTiML.kinding_derivation * down -> MicroTiML.kinding_derivation * up) -> (MicroTiML.kind_sub_derivation * down) -> (MicroTiML.kind_sub_derivation * up) option

  val upward_base : up
  val combiner : (up * up) -> up
end
) =
struct
  open MicroTiML

  fun combine (ups : Arg.up list) = List.foldl Arg.combiner Arg.upward_base ups

  fun default_transform_typing_derivation (tyderiv : typing_derivation, down : Arg.down) =
    let
      fun on_rel tyrel = Arg.on_typing_relation (tyrel, down)
      fun on_tyderiv tyderiv = transform_typing_derivation (tyderiv, down)
      fun on_kdderiv kdderiv = transform_kinding_derivation (kdderiv, down)
      fun on_prderiv prderiv = transform_proping_derivation (prderiv, down)
      fun on_kdwf kdwf = transform_kind_wellformness_derivation (kdwf, down)
      fun on_tyeq tyeq = transform_type_equivalence_derivation (tyeq, down)
    in
      case tyderiv of
        TyDerivSub (tyrel, tyderiv1, tyeq2, prderiv3) =>
          let
            (*val (tyrel, up0) = on_rel tyrel*)
            val (tyderiv1, up1) = on_tyderiv tyderiv1
            val (tyeq2, up2) = on_tyeq tyeq2
            val (prderiv3, up3) = on_prderiv prderiv3
            val tyrel1 = extract_tyrel tyderiv1
            val tyeqrel2 = extract_tyeqrel tyeq2
            val prrel3 = extract_prrel prderiv3
            val tyrel_new = (#1 tyrel1, #2 tyrel1, #3 tyeqrel2, #3 (extract_pr_bin_rel (#2 prrel3)))
          in
            (TyDerivSub (tyrel_new, tyderiv1, tyeq2, prderiv3), combine [up1, up2, up3])
          end
      | TyDerivVar tyrel =>
          let
            val (tyrel, up0) = on_rel tyrel
          in
            (TyDerivVar tyrel, combine [up0])
          end
      | TyDerivInt tyrel =>
          let
            val (tyrel, up0) = on_rel tyrel
          in
            (TyDerivInt tyrel, combine [up0])
          end
      | TyDerivNat tyrel =>
          let
            val (tyrel, up0) = on_rel tyrel
          in
            (TyDerivNat tyrel, combine [up0])
          end
      | TyDerivUnit tyrel =>
          let
            val (tyrel, up0) = on_rel tyrel
          in
            (TyDerivUnit tyrel, combine [up0])
          end
      | TyDerivApp (tyrel, tyderiv1, tyderiv2) =>
          let
            (*val (tyrel, up0) = on_rel tyrel*)
            val (tyderiv1, up1) = on_tyderiv tyderiv1
            val (tyderiv2, up2) = on_tyderiv tyderiv2
            val tyrel1 = extract_tyrel tyderiv1
            val tyrel2 = extract_tyrel tyderiv2
            val (ty1, ty2, ti) = extract_cstr_arrow (#3 tyrel1)
            val tyrel_new = (#1 tyrel1, TmApp (#2 tyrel1, #2 tyrel2), ty2, CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, #4 tyrel1, #4 tyrel2), CstrTime "1.0"), ti))
          in
            (TyDerivApp (tyrel_new, tyderiv1, tyderiv2), combine [up1, up2])
          end
      | TyDerivAbs (tyrel, kdderiv1, tyderiv2) =>
          let
            (*val (tyrel, up0) = on_rel tyrel*)
            val (kdderiv1, up1) = on_kdderiv kdderiv1
            val (tyderiv2, up2) = on_tyderiv tyderiv2
            val kdrel1 = extract_kdrel kdderiv1
            val tyrel2 = extract_tyrel tyderiv2
            val tyrel_new = (#1 kdrel1, TmAbs (#2 kdrel1, #2 tyrel2), CstrArrow (#2 kdrel1, Passes.TermShift.shift_constr ~1 (#3 tyrel2), Passes.TermShift.shift_constr ~1 (#4 tyrel2)), CstrTime "0.0")
          in
           (TyDerivAbs (tyrel_new, kdderiv1, tyderiv2), combine [up1, up2])
          end
      | TyDerivRec (tyrel, kdderiv1, tyderiv2) =>
          let
            (*val (tyrel, up0) = on_rel tyrel*)
            val (kdderiv1, up1) = on_kdderiv kdderiv1
            val (tyderiv2, up2) = on_tyderiv tyderiv2
            val kdrel1 = extract_kdrel kdderiv1
            val tyrel2 = extract_tyrel tyderiv2
            val tyrel_new = (#1 kdrel1, TmRec (#2 kdrel1, #2 tyrel2), #2 kdrel1, CstrTime "0.0")
          in
            (TyDerivRec (tyrel_new, kdderiv1, tyderiv2), combine [up1, up2])
          end
      | TyDerivPair (tyrel, tyderiv1, tyderiv2) =>
          let
            (*val (tyrel, up0) = on_rel tyrel*)
            val (tyderiv1, up1) = on_tyderiv tyderiv1
            val (tyderiv2, up2) = on_tyderiv tyderiv2
            val tyrel1 = extract_tyrel tyderiv1
            val tyrel2 = extract_tyrel tyderiv2
            val tyrel_new = (#1 tyrel1, TmPair (#2 tyrel1, #2 tyrel2), CstrProd (#3 tyrel1, #3 tyrel2), CstrBinOp (CstrBopAdd, #4 tyrel1, #4 tyrel2))
          in
            (TyDerivPair (tyrel_new, tyderiv1, tyderiv2), combine [up1, up2])
          end
      | TyDerivFst (tyrel, tyderiv1) =>
          let
            (*val (tyrel, up0) = on_rel tyrel*)
            val (tyderiv1, up1) = on_tyderiv tyderiv1
            val tyrel1 = extract_tyrel tyderiv1
            val (ty1, ty2) = extract_cstr_prod (#3 tyrel1)
            val tyrel_new = (#1 tyrel1, TmFst (#2 tyrel1), ty1, #4 tyrel1)
          in
            (TyDerivFst (tyrel_new, tyderiv1), combine [up1])
          end
      | TyDerivSnd (tyrel, tyderiv1) =>
          let
            (*val (tyrel, up0) = on_rel tyrel*)
            val (tyderiv1, up1) = on_tyderiv tyderiv1
            val tyrel1 = extract_tyrel tyderiv1
            val (ty1, ty2) = extract_cstr_prod (#3 tyrel1)
            val tyrel_new = (#1 tyrel1, TmSnd (#2 tyrel1), ty2, #4 tyrel1)
          in
            (TyDerivSnd (tyrel_new, tyderiv1), combine [up1])
          end
      | TyDerivInLeft (tyrel, kdderiv1, tyderiv2) =>
          let
            (*val (tyrel, up0) = on_rel tyrel*)
            val (kdderiv1, up1) = on_kdderiv kdderiv1
            val (tyderiv2, up2) = on_tyderiv tyderiv2
            val kdrel1 = extract_kdrel kdderiv1
            val tyrel2 = extract_tyrel tyderiv2
            val tyrel_new = (#1 kdrel1, TmInLeft (#2 tyrel2), CstrSum (#3 tyrel2, #2 kdrel1), #4 tyrel2)
          in
            (TyDerivInLeft (tyrel_new, kdderiv1, tyderiv2), combine [up1, up2])
          end
      | TyDerivInRight (tyrel, kdderiv1, tyderiv2) =>
          let
            (*val (tyrel, up0) = on_rel tyrel*)
            val (kdderiv1, up1) = on_kdderiv kdderiv1
            val (tyderiv2, up2) = on_tyderiv tyderiv2
            val kdrel1 = extract_kdrel kdderiv1
            val tyrel2 = extract_tyrel tyderiv2
            val tyrel_new = (#1 kdrel1, TmInRight (#2 tyrel2), CstrSum (#2 kdrel1, #3 tyrel2), #4 tyrel2)
          in
            (TyDerivInRight (tyrel_new, kdderiv1, tyderiv2), combine [up1, up2])
          end
      | TyDerivCase (tyrel, tyderiv1, tyderiv2, tyderiv3) =>
          let
            (*val (tyrel, up0) = on_rel tyrel*)
            val (tyderiv1, up1) = on_tyderiv tyderiv1
            val (tyderiv2, up2) = on_tyderiv tyderiv2
            val (tyderiv3, up3) = on_tyderiv tyderiv3
            val tyrel1 = extract_tyrel tyderiv1
            val tyrel2 = extract_tyrel tyderiv2
            val tyrel3 = extract_tyrel tyderiv3
            val tyrel_new = (#1 tyrel1, TmCase (#2 tyrel1, #2 tyrel2, #2 tyrel3), Passes.TermShift.shift_constr ~1 (#3 tyrel2), CstrBinOp (CstrBopAdd, #4 tyrel1, CstrBinOp (CstrBopMax, Passes.TermShift.shift_constr ~1 (#4 tyrel2), Passes.TermShift.shift_constr ~1 (#4 tyrel3))))
          in
            (TyDerivCase (tyrel_new, tyderiv1, tyderiv2, tyderiv3), combine [up1, up2, up3])
          end
      | TyDerivFold (tyrel, kdderiv1, tyderiv2) =>
          let
            (*val (tyrel, up0) = on_rel tyrel*)
            val (kdderiv1, up1) = on_kdderiv kdderiv1
            val (tyderiv2, up2) = on_tyderiv tyderiv2
            val kdrel1 = extract_kdrel kdderiv1
            val tyrel2 = extract_tyrel tyderiv2
            val tyrel_new = (#1 kdrel1, TmFold (#2 tyrel2), #2 kdrel1, #4 tyrel2)
          in
            (TyDerivFold (tyrel_new, kdderiv1, tyderiv2), combine [up1, up2])
          end
      | TyDerivUnfold (tyrel, tyderiv1) =>
          let
            (*val (tyrel, up0) = on_rel tyrel*)
            val (tyderiv1, up1) = on_tyderiv tyderiv1
            val tyrel1 = extract_tyrel tyderiv1
            fun unfold_app ty1 rands =
              case ty1 of
                CstrApp (cstr1, cstr2) => unfold_app cstr1 (cstr2 :: rands)
              | _ => (ty1, rands)
            fun fold_app ty1 rands =
              case rands of
                [] => ty1
              | hd :: tl => fold_app (Passes.TermSubstConstr.subst_constr_in_constr_top hd (#2 (extract_cstr_abs ty1))) tl
            val (ty1, rands) = unfold_app (#3 tyrel1) []
            val (kd1, ty_body) = extract_cstr_rec ty1
            val tyrel_new = (#1 tyrel1, TmUnfold (#2 tyrel1), fold_app (Passes.TermSubstConstr.subst_constr_in_constr_top ty1 ty_body) rands, #4 tyrel1)
          in
            (TyDerivUnfold (tyrel_new, tyderiv1), combine [up1])
          end
      | TyDerivPack (tyrel, kdderiv1, kdderiv2, tyderiv3) =>
          let
            (*val (tyrel, up0) = on_rel tyrel*)
            val (kdderiv1, up1) = on_kdderiv kdderiv1
            val (kdderiv2, up2) = on_kdderiv kdderiv2
            val (tyderiv3, up3) = on_tyderiv tyderiv3
            val kdrel1 = extract_kdrel kdderiv1
            val kdrel2 = extract_kdrel kdderiv2
            val tyrel3 = extract_tyrel tyderiv3
            val tyrel_new = (#1 kdrel1, TmPack (#2 kdrel2, #2 tyrel3), #2 kdrel1, #4 tyrel3)
          in
            (TyDerivPack (tyrel_new, kdderiv1, kdderiv2, tyderiv3), combine [up1, up2, up3])
          end
      | TyDerivUnpack (tyrel, tyderiv1, tyderiv2) =>
          let
            (*val (tyrel, up0) = on_rel tyrel*)
            val (tyderiv1, up1) = on_tyderiv tyderiv1
            val (tyderiv2, up2) = on_tyderiv tyderiv2
            val tyrel1 = extract_tyrel tyderiv1
            val tyrel2 = extract_tyrel tyderiv2
            val tyrel_new = (#1 tyrel1, TmUnpack (#2 tyrel1, #2 tyrel2), Passes.TermShift.shift_constr ~2 (#3 tyrel2), Passes.TermShift.shift_constr ~2 (#4 tyrel2))
          in
            (TyDerivUnpack (tyrel_new, tyderiv1, tyderiv2), combine [up1, up2])
          end
      | TyDerivCstrAbs (tyrel, kdwf1, tyderiv2) =>
          let
            (*val (tyrel, up0) = on_rel tyrel*)
            val (kdwf1, up1) = on_kdwf kdwf1
            val (tyderiv2, up2) = on_tyderiv tyderiv2
            val kdwfrel1 = extract_kdwfrel kdwf1
            val tyrel2 = extract_tyrel tyderiv2
            val tyrel_new = (#1 kdwfrel1, TmCstrAbs (#2 kdwfrel1, #2 tyrel2), CstrForall (#2 kdwfrel1, #3 tyrel2), CstrTime "0.0")
          in
            (TyDerivCstrAbs (tyrel_new, kdwf1, tyderiv2), combine [up1, up2])
          end
      | TyDerivCstrApp (tyrel, tyderiv1, kdderiv2) =>
          let
            (*val (tyrel, up0) = on_rel tyrel*)
            val (tyderiv1, up1) = on_tyderiv tyderiv1
            val (kdderiv2, up2) = on_kdderiv kdderiv2
            val tyrel1 = extract_tyrel tyderiv1
            val kdrel2 = extract_kdrel kdderiv2
            val (kd1, ty_body) = extract_cstr_forall (#3 tyrel1)
            val tyrel_new = (#1 tyrel1, TmCstrApp (#2 tyrel1, #2 kdrel2), Passes.TermSubstConstr.subst_constr_in_constr_top (#2 kdrel2) ty_body, #4 tyrel1)
          in
            (TyDerivCstrApp (tyrel_new, tyderiv1, kdderiv2), combine [up1, up2])
          end
      | TyDerivBinOp (tyrel, tyderiv1, tyderiv2) =>
          let
            (*val (tyrel, up0) = on_rel tyrel*)
            val (tyderiv1, up1) = on_tyderiv tyderiv1
            val (tyderiv2, up2) = on_tyderiv tyderiv2
            val tyrel1 = extract_tyrel tyderiv1
            val tyrel2 = extract_tyrel tyderiv2
            val (bop, _, _) = extract_tm_bin_op (#2 tyrel)
            val (tyr, (ty1, ty2)) = term_bin_op_to_constr bop
            val tyrel_new = (#1 tyrel1, TmBinOp (bop, #2 tyrel1, #2 tyrel2), tyr, CstrBinOp (CstrBopAdd, #4 tyrel1, #4 tyrel2))
          in
            (TyDerivBinOp (tyrel_new, tyderiv1, tyderiv2), combine [up1, up2])
          end
      | TyDerivArrayNew (tyrel, tyderiv1, tyderiv2) =>
          let
            (*val (tyrel, up0) = on_rel tyrel*)
            val (tyderiv1, up1) = on_tyderiv tyderiv1
            val (tyderiv2, up2) = on_tyderiv tyderiv2
            val tyrel1 = extract_tyrel tyderiv1
            val tyrel2 = extract_tyrel tyderiv2
            val cstr = extract_cstr_type_nat (#3 tyrel2)
            val tyrel_new = (#1 tyrel1, TmArrayNew (#2 tyrel1, #2 tyrel2), CstrTypeArray (#3 tyrel1, cstr), CstrBinOp (CstrBopAdd, #4 tyrel1, #4 tyrel2))
          in
            (TyDerivArrayNew (tyrel_new, tyderiv1, tyderiv2), combine [up1, up2])
          end
      | TyDerivArrayGet (tyrel, tyderiv1, tyderiv2, prderiv3) =>
          let
            (*val (tyrel, up0) = on_rel tyrel*)
            val (tyderiv1, up1) = on_tyderiv tyderiv1
            val (tyderiv2, up2) = on_tyderiv tyderiv2
            val (prderiv3, up3) = on_prderiv prderiv3
            val tyrel1 = extract_tyrel tyderiv1
            val tyrel2 = extract_tyrel tyderiv2
            val prrel3 = extract_prrel prderiv3
            val (cstr1, cstr2) = extract_cstr_type_array (#3 tyrel1)
            val tyrel_new = (#1 tyrel1, TmArrayGet (#2 tyrel1, #2 tyrel2), cstr1, CstrBinOp (CstrBopAdd, #4 tyrel1, #4 tyrel2))
          in
            (TyDerivArrayGet (tyrel_new, tyderiv1, tyderiv2, prderiv3), combine [up1, up2, up3])
          end
      | TyDerivArrayPut (tyrel, tyderiv1, tyderiv2, prderiv3, tyderiv4) =>
          let
            (*val (tyrel, up0) = on_rel tyrel*)
            val (tyderiv1, up1) = on_tyderiv tyderiv1
            val (tyderiv2, up2) = on_tyderiv tyderiv2
            val (prderiv3, up3) = on_prderiv prderiv3
            val (tyderiv4, up4) = on_tyderiv tyderiv4
            val tyrel1 = extract_tyrel tyderiv1
            val tyrel2 = extract_tyrel tyderiv2
            val prrel3 = extract_prrel prderiv3
            val tyrel4 = extract_tyrel tyderiv4
            val tyrel_new = (#1 tyrel1, TmArrayPut (#2 tyrel1, #2 tyrel2, #2 tyrel4), CstrTypeUnit, CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, #4 tyrel1, #4 tyrel2), #4 tyrel4))
          in
            (TyDerivArrayPut (tyrel_new, tyderiv1, tyderiv2, prderiv3, tyderiv4), combine [up1, up2, up3, up4])
          end
      | TyDerivLet (tyrel, tyderiv2, tyderiv3) =>
          let
            (*val (tyrel, up0) = on_rel tyrel*)
            val (tyderiv2, up2) = on_tyderiv tyderiv2
            val (tyderiv3, up3) = on_tyderiv tyderiv3
            val tyrel2 = extract_tyrel tyderiv2
            val tyrel3 = extract_tyrel tyderiv3
            val tyrel_new = (#1 tyrel2, TmLet (#2 tyrel2, #2 tyrel3), Passes.TermShift.shift_constr ~1 (#3 tyrel3), CstrBinOp (CstrBopAdd, #4 tyrel2, Passes.TermShift.shift_constr ~1 (#4 tyrel3)))
          in
            (TyDerivLet (tyrel_new, tyderiv2, tyderiv3), combine [up2, up3])
          end
      | TyDerivNever (tyrel, kdderiv1, prderiv2) =>
          let
            (*val (tyrel, up0) = on_rel tyrel*)
            val (kdderiv1, up1) = on_kdderiv kdderiv1
            val (prderiv2, up2) = on_prderiv prderiv2
            val kdrel1 = extract_kdrel kdderiv1
            val prrel2 = extract_prrel prderiv2
            val tyrel_new = (#1 kdrel1, TmNever, #2 kdrel1, CstrTime "0.0")
          in
            (TyDerivNever (tyrel_new, kdderiv1, prderiv2), combine [up1, up2])
          end
    end

  and transform_typing_derivation (tyderiv : typing_derivation, down : Arg.down) =
    case Arg.transformer_typing_derivation (transform_typing_derivation, transform_kinding_derivation, transform_proping_derivation, transform_kind_wellformness_derivation, transform_type_equivalence_derivation) (tyderiv, down) of
      SOME res => res
    | NONE => default_transform_typing_derivation (tyderiv, down)

  and default_transform_kinding_derivation (kdderiv : kinding_derivation, down : Arg.down) =
    let
      fun on_rel kdrel = Arg.on_kinding_relation (kdrel, down)
      fun on_kdderiv kdderiv = transform_kinding_derivation (kdderiv, down)
      fun on_prderiv prderiv = transform_proping_derivation (prderiv, down)
      fun on_kdwf kdwf = transform_kind_wellformness_derivation (kdwf, down)
    in
      case kdderiv of
        KdDerivAssume kdrel =>
          let
            val (kdrel, up0) = on_rel kdrel
          in
            (KdDerivAssume kdrel, combine [up0])
          end
      | KdDerivRefine (kdrel, kdderiv1, prderiv2) =>
          let
            (*val (kdrel, up0) = on_rel kdrel*)
            val (kdderiv1, up1) = on_kdderiv kdderiv1
            val (prderiv2, up2) = on_prderiv prderiv2
            val kdrel1 = extract_kdrel kdderiv1
            val prrel2 = extract_prrel prderiv2
            val kdrel_new = (#1 kdrel1, #2 kdrel1, KdSubset (#3 kdrel1, #2 prrel2))
          in
            (KdDerivRefine (kdrel_new, kdderiv1, prderiv2), combine [up1, up2])
          end
      | KdDerivBase (kdrel, kdderiv1) =>
          let
            (*val (kdrel, up0) = on_rel kdrel*)
            val (kdderiv1, up1) = on_kdderiv kdderiv1
            val kdrel1 = extract_kdrel kdderiv1
            fun inner_most kd =
              case kd of
                KdSubset (kd, _) => inner_most kd
              | _ => kd
            val kdrel_new = (#1 kdrel1, #2 kdrel1, inner_most (#3 kdrel1))
          in
            (KdDerivBase (kdrel_new, kdderiv1), combine [up1])
          end
      | KdDerivVar kdrel =>
          let
            val (kdrel, up0) = on_rel kdrel
          in
            (KdDerivVar kdrel, combine [up0])
          end
      | KdDerivNat kdrel =>
          let
            val (kdrel, up0) = on_rel kdrel
          in
            (KdDerivNat kdrel, combine [up0])
          end
      | KdDerivTime kdrel =>
          let
            val (kdrel, up0) = on_rel kdrel
          in
            (KdDerivTime kdrel, combine [up0])
          end
      | KdDerivUnit kdrel =>
          let
            val (kdrel, up0) = on_rel kdrel
          in
            (KdDerivUnit kdrel, combine [up0])
          end
      | KdDerivTrue kdrel =>
          let
            val (kdrel, up0) = on_rel kdrel
          in
            (KdDerivTrue kdrel, combine [up0])
          end
      | KdDerivFalse kdrel =>
          let
            val (kdrel, up0) = on_rel kdrel
          in
            (KdDerivFalse kdrel, combine [up0])
          end
      | KdDerivUnOp (kdrel, kdderiv1) =>
          let
            (*val (kdrel, up0) = on_rel kdrel*)
            val (kdderiv1, up1) = on_kdderiv kdderiv1
            val kdrel1 = extract_kdrel kdderiv1
            val (uop, _) = extract_cstr_un_op (#2 kdrel)
            val (kdr, _) = cstr_un_op_to_kind uop
            val kdrel_new = (#1 kdrel1, CstrUnOp (uop, #2 kdrel1), kdr)
          in
            (KdDerivUnOp (kdrel_new, kdderiv1), combine [up1])
          end
      | KdDerivBinOp (kdrel, kdderiv1, kdderiv2) =>
          let
            (*val (kdrel, up0) = on_rel kdrel*)
            val (kdderiv1, up1) = on_kdderiv kdderiv1
            val (kdderiv2, up2) = on_kdderiv kdderiv2
            val kdrel1 = extract_kdrel kdderiv1
            val kdrel2 = extract_kdrel kdderiv2
            val (bop, _, _) = extract_cstr_bin_op (#2 kdrel)
            val kdr =
              case bop of
                CstrBopTimeApp => KdTimeFun (extract_kd_time_fun (#3 kdrel1) - 1)
              | _ => fst (Option.valOf (List.find (fn (kdr, (kd1, kd2)) => kd1 = (#3 kdrel1) andalso kd2 = (#3 kdrel2)) (cstr_bin_op_to_kind bop)))
            val kdrel_new = (#1 kdrel1, CstrBinOp (bop, #2 kdrel1, #2 kdrel2), kdr)
          in
            (KdDerivBinOp (kdrel_new, kdderiv1, kdderiv2), combine [up1, up2])
          end
      | KdDerivIte (kdrel, kdderiv1, kdderiv2, kdderiv3) =>
          let
            (*val (kdrel, up0) = on_rel kdrel*)
            val (kdderiv1, up1) = on_kdderiv kdderiv1
            val (kdderiv2, up2) = on_kdderiv kdderiv2
            val (kdderiv3, up3) = on_kdderiv kdderiv3
            val kdrel1 = extract_kdrel kdderiv1
            val kdrel2 = extract_kdrel kdderiv2
            val kdrel3 = extract_kdrel kdderiv3
            val kdrel_new = (#1 kdrel1, CstrIte (#2 kdrel1, #2 kdrel2, #2 kdrel3), #3 kdrel2)
          in
            (KdDerivIte (kdrel_new, kdderiv1, kdderiv2, kdderiv3), combine [up1, up2, up3])
          end
      | KdDerivTimeAbs (kdrel, kdderiv1) =>
          let
            (*val (kdrel, up0) = on_rel kdrel*)
            val (kdderiv1, up1) = on_kdderiv kdderiv1
            val kdrel1 = extract_kdrel kdderiv1
            val kdrel_new = (#1 kdrel1, CstrTimeAbs (#2 kdrel1), KdTimeFun (extract_kd_time_fun (#3 kdrel1) + 1))
          in
            (KdDerivTimeAbs (kdrel_new, kdderiv1), combine [up1])
          end
      | KdDerivProd (kdrel, kdderiv1, kdderiv2) =>
          let
            (*val (kdrel, up0) = on_rel kdrel*)
            val (kdderiv1, up1) = on_kdderiv kdderiv1
            val (kdderiv2, up2) = on_kdderiv kdderiv2
            val kdrel1 = extract_kdrel kdderiv1
            val kdrel2 = extract_kdrel kdderiv2
            val kdrel_new = (#1 kdrel1, CstrProd (#2 kdrel1, #2 kdrel2), KdProper)
          in
            (KdDerivProd (kdrel_new, kdderiv1, kdderiv2), combine [up1, up2])
          end
      | KdDerivSum (kdrel, kdderiv1, kdderiv2) =>
          let
            (*val (kdrel, up0) = on_rel kdrel*)
            val (kdderiv1, up1) = on_kdderiv kdderiv1
            val (kdderiv2, up2) = on_kdderiv kdderiv2
            val kdrel1 = extract_kdrel kdderiv1
            val kdrel2 = extract_kdrel kdderiv2
            val kdrel_new = (#1 kdrel1, CstrSum (#2 kdrel1, #2 kdrel2), KdProper)
          in
            (KdDerivSum (kdrel_new, kdderiv1, kdderiv2), combine [up1, up2])
          end
      | KdDerivArrow (kdrel, kdderiv1, kdderiv2, kdderiv3) =>
          let
            (*val (kdrel, up0) = on_rel kdrel*)
            val (kdderiv1, up1) = on_kdderiv kdderiv1
            val (kdderiv2, up2) = on_kdderiv kdderiv2
            val (kdderiv3, up3) = on_kdderiv kdderiv3
            val kdrel1 = extract_kdrel kdderiv1
            val kdrel2 = extract_kdrel kdderiv2
            val kdrel3 = extract_kdrel kdderiv3
            val kdrel_new = (#1 kdrel1, CstrArrow (#2 kdrel1, #2 kdrel2, #2 kdrel3), KdProper)
          in
            (KdDerivArrow (kdrel_new, kdderiv1, kdderiv2, kdderiv3), combine [up1, up2, up3])
          end
      | KdDerivApp (kdrel, kdderiv1, kdderiv2) =>
          let
            (*val (kdrel, up0) = on_rel kdrel*)
            val (kdderiv1, up1) = on_kdderiv kdderiv1
            val (kdderiv2, up2) = on_kdderiv kdderiv2
            val kdrel1 = extract_kdrel kdderiv1
            val kdrel2 = extract_kdrel kdderiv2
            val (kd1, kd2) = extract_kd_arrow (#3 kdrel1)
            val kdrel_new = (#1 kdrel1, CstrApp (#2 kdrel1, #2 kdrel2), kd2)
          in
            (KdDerivApp (kdrel_new, kdderiv1, kdderiv2), combine [up1, up2])
          end
      | KdDerivAbs (kdrel, kdwf1, kdderiv2) =>
          let
            (*val (kdrel, up0) = on_rel kdrel*)
            val (kdwf1, up1) = on_kdwf kdwf1
            val (kdderiv2, up2) = on_kdderiv kdderiv2
            val kdwfrel1 = extract_kdwfrel kdwf1
            val kdrel2 = extract_kdrel kdderiv2
            val kdrel_new = (#1 kdwfrel1, CstrAbs (#2 kdwfrel1, #2 kdrel2), KdArrow (#2 kdwfrel1, Passes.TermShift.shift_kind ~1 (#3 kdrel2)))
          in
            (KdDerivAbs (kdrel_new, kdwf1, kdderiv2), combine [up1, up2])
          end
      | KdDerivForall (kdrel, kdwf1, kdderiv2) =>
          let
            (*val (kdrel, up0) = on_rel kdrel*)
            val (kdwf1, up1) = on_kdwf kdwf1
            val (kdderiv2, up2) = on_kdderiv kdderiv2
            val kdwfrel1 = extract_kdwfrel kdwf1
            val kdrel2 = extract_kdrel kdderiv2
            val kdrel_new = (#1 kdwfrel1, CstrForall (#2 kdwfrel1, #2 kdrel2), KdProper)
          in
            (KdDerivForall (kdrel_new, kdwf1, kdderiv2), combine [up1, up2])
          end
      | KdDerivExists (kdrel, kdwf1, kdderiv2) =>
          let
            (*val (kdrel, up0) = on_rel kdrel*)
            val (kdwf1, up1) = on_kdwf kdwf1
            val (kdderiv2, up2) = on_kdderiv kdderiv2
            val kdwfrel1 = extract_kdwfrel kdwf1
            val kdrel2 = extract_kdrel kdderiv2
            val kdrel_new = (#1 kdwfrel1, CstrExists (#2 kdwfrel1, #2 kdrel2), KdProper)
          in
            (KdDerivExists (kdrel_new, kdwf1, kdderiv2), combine [up1, up2])
          end
      | KdDerivRec (kdrel, kdwf1, kdderiv2) =>
          let
            (*val (kdrel, up0) = on_rel kdrel*)
            val (kdwf1, up1) = on_kdwf kdwf1
            val (kdderiv2, up2) = on_kdderiv kdderiv2
            val kdwfrel1 = extract_kdwfrel kdwf1
            val kdrel2 = extract_kdrel kdderiv2
            val kdrel_new = (#1 kdwfrel1, CstrRec (#2 kdwfrel1, #2 kdrel2), #2 kdwfrel1)
          in
            (KdDerivRec (kdrel_new, kdwf1, kdderiv2), combine [up1, up2])
          end
      | KdDerivTypeUnit kdrel =>
          let
            val (kdrel, up0) = on_rel kdrel
          in
            (KdDerivTypeUnit kdrel, combine [up0])
          end
      | KdDerivTypeInt kdrel =>
          let
            val (kdrel, up0) = on_rel kdrel
          in
            (KdDerivTypeInt kdrel, combine [up0])
          end
      | KdDerivTypeNat (kdrel, kdderiv1) =>
          let
            (*val (kdrel, up0) = on_rel kdrel*)
            val (kdderiv1, up1) = on_kdderiv kdderiv1
            val kdrel1 = extract_kdrel kdderiv1
            val kdrel_new = (#1 kdrel1, CstrTypeNat (#2 kdrel1), KdProper)
          in
            (KdDerivTypeNat (kdrel_new, kdderiv1), combine [up1])
          end
      | KdDerivTypeArray (kdrel, kdderiv1, kdderiv2) =>
          let
            (*val (kdrel, up0) = on_rel kdrel*)
            val (kdderiv1, up1) = on_kdderiv kdderiv1
            val (kdderiv2, up2) = on_kdderiv kdderiv2
            val kdrel1 = extract_kdrel kdderiv1
            val kdrel2 = extract_kdrel kdderiv2
            val kdrel_new = (#1 kdrel1, CstrTypeArray (#2 kdrel1, #2 kdrel2), KdProper)
          in
            (KdDerivTypeArray (kdrel_new, kdderiv1, kdderiv2), combine [up1, up2])
          end
    end

  and transform_kinding_derivation (kdderiv : kinding_derivation, down : Arg.down) =
    case Arg.transformer_kinding_derivation (transform_kinding_derivation, transform_proping_derivation, transform_kind_wellformness_derivation) (kdderiv, down) of
      SOME res => res
    | NONE => default_transform_kinding_derivation (kdderiv, down)

  and default_transform_proping_derivation (prderiv : proping_derivation, down : Arg.down) =
    case prderiv of
      PrDerivAdmit prrel =>
        let
          val (prrel, up0) = Arg.on_proping_relation (prrel, down)
        in
          (PrDerivAdmit prrel, combine [up0])
        end

  and transform_proping_derivation (prderiv : proping_derivation, down : Arg.down) =
    case Arg.transformer_proping_derivation (prderiv, down) of
      SOME res => res
    | NONE => default_transform_proping_derivation (prderiv, down)

  and default_transform_kind_wellformness_derivation (kdwf : kind_wellformedness_derivation, down : Arg.down) =
    let
      fun on_rel kdrel = Arg.on_kind_wellformness_relation (kdrel, down)
      fun on_kdwf kdwf = transform_kind_wellformness_derivation (kdwf, down)
      fun on_prwf prwf = transform_prop_wellformness_derivation (prwf, down)
    in
      case kdwf of
        KdWfDerivAssume kdrel =>
          let
            val (kdrel, up0) = on_rel kdrel
          in
            (KdWfDerivAssume kdrel, combine [up0])
          end
      | KdWfDerivNat kdrel =>
          let
            val (kdrel, up0) = on_rel kdrel
          in
            (KdWfDerivNat kdrel, combine [up0])
          end
      | KdWfDerivBool kdrel =>
          let
            val (kdrel, up0) = on_rel kdrel
          in
            (KdWfDerivBool kdrel, combine [up0])
          end
      | KdWfDerivUnit kdrel =>
          let
            val (kdrel, up0) = on_rel kdrel
          in
            (KdWfDerivUnit kdrel, combine [up0])
          end
      | KdWfDerivTimeFun kdrel =>
          let
            val (kdrel, up0) = on_rel kdrel
          in
            (KdWfDerivTimeFun kdrel, combine [up0])
          end
      | KdWfDerivSubset (kdrel, kdwf1, prwf2) =>
          let
            (*val (kdrel, up0) = on_rel kdrel*)
            val (kdwf1, up1) = on_kdwf kdwf1
            val (prwf2, up2) = on_prwf prwf2
            val kdwfrel1 = extract_kdwfrel kdwf1
            val prwfrel2 = extract_prwfrel prwf2
            val kdrel_new = (#1 kdwfrel1, KdSubset (#2 kdwfrel1, #2 prwfrel2))
          in
            (KdWfDerivSubset (kdrel_new, kdwf1, prwf2), combine [up1, up2])
          end
      | KdWfDerivProper kdrel =>
          let
            val (kdrel, up0) = on_rel kdrel
          in
            (KdWfDerivProper kdrel, combine [up0])
          end
      | KdWfDerivArrow (kdrel, kdwf1, kdwf2) =>
          let
            (*val (kdrel, up0) = on_rel kdrel*)
            val (kdwf1, up1) = on_kdwf kdwf1
            val (kdwf2, up2) = on_kdwf kdwf2
            val kdwfrel1 = extract_kdwfrel kdwf1
            val kdwfrel2 = extract_kdwfrel kdwf2
            val kdrel_new = (#1 kdwfrel1, KdArrow (#2 kdwfrel1, #2 kdwfrel2))
          in
            (KdWfDerivArrow (kdrel_new, kdwf1, kdwf2), combine [up1, up2])
          end
    end

  and transform_kind_wellformness_derivation (kdwf : kind_wellformedness_derivation, down : Arg.down) =
    case Arg.transformer_kind_wellformness_derivation (transform_kind_wellformness_derivation, transform_prop_wellformness_derivation) (kdwf, down) of
      SOME res => res
    | NONE => default_transform_kind_wellformness_derivation (kdwf, down)

  and default_transform_prop_wellformness_derivation (prwf : prop_wellformedness_derivation, down : Arg.down) =
    let
      fun on_rel prrel = Arg.on_prop_wellformness_relation (prrel, down)
      fun on_kdwf kdwf = transform_kind_wellformness_derivation (kdwf, down)
      fun on_prwf prwf = transform_prop_wellformness_derivation (prwf, down)
      fun on_kdderiv kdderiv = transform_kinding_derivation (kdderiv, down)
    in
      case prwf of
        PrWfDerivTop prrel =>
          let
            val (prrel, up0) = on_rel prrel
          in
            (PrWfDerivTop prrel, combine [up0])
          end
      | PrWfDerivBot prrel =>
          let
            val (prrel, up0) = on_rel prrel
          in
            (PrWfDerivBot prrel, combine [up0])
          end
      | PrWfDerivBinConn (prrel, prwf1, prwf2) =>
          let
            (*val (prrel, up0) = on_rel prrel*)
            val (prwf1, up1) = on_prwf prwf1
            val (prwf2, up2) = on_prwf prwf2
            val prwfrel1 = extract_prwfrel prwf1
            val prwfrel2 = extract_prwfrel prwf2
            val (conn, _, _) = extract_pr_bin_conn (#2 prrel)
            val prrel_new = (#1 prwfrel1, PrBinConn (conn, #2 prwfrel1, #2 prwfrel2))
          in
            (PrWfDerivBinConn (prrel_new, prwf1, prwf2), combine [up1, up2])
          end
      | PrWfDerivNot (prrel, prwf1) =>
          let
            (*val (prrel, up0) = on_rel prrel*)
            val (prwf1, up1) = on_prwf prwf1
            val prwfrel1 = extract_prwfrel prwf1
            val prrel_new = (#1 prwfrel1, PrNot (#2 prwfrel1))
          in
            (PrWfDerivNot (prrel_new, prwf1), combine [up1])
          end
      | PrWfDerivBinRel (prrel, kdderiv1, kdderiv2) =>
          let
            (*val (prrel, up0) = on_rel prrel*)
            val (kdderiv1, up1) = on_kdderiv kdderiv1
            val (kdderiv2, up2) = on_kdderiv kdderiv2
            val kdrel1 = extract_kdrel kdderiv1
            val kdrel2 = extract_kdrel kdderiv2
            val (rel, _, _) = extract_pr_bin_rel (#2 prrel)
            val prrel_new = (#1 kdrel1, PrBinRel (rel, #2 kdrel1, #2 kdrel2))
          in
            (PrWfDerivBinRel (prrel_new, kdderiv1, kdderiv2), combine [up1, up2])
          end
      | PrWfDerivForall (prrel, kdwf1, prwf2) =>
          let
            (*val (prrel, up0) = on_rel prrel*)
            val (kdwf1, up1) = on_kdwf kdwf1
            val (prwf2, up2) = on_prwf prwf2
            val kdwfrel1 = extract_kdwfrel kdwf1
            val prwfrel2 = extract_prwfrel prwf2
            val prrel_new = (#1 kdwfrel1, PrForall (#2 kdwfrel1, #2 prwfrel2))
          in
            (PrWfDerivForall (prrel_new, kdwf1, prwf2), combine [up1, up2])
          end
      | PrWfDerivExists (prrel, kdwf1, prwf2) =>
          let
            (*val (prrel, up0) = on_rel prrel*)
            val (kdwf1, up1) = on_kdwf kdwf1
            val (prwf2, up2) = on_prwf prwf2
            val kdwfrel1 = extract_kdwfrel kdwf1
            val prwfrel2 = extract_prwfrel prwf2
            val prrel_new = (#1 kdwfrel1, PrExists (#2 kdwfrel1, #2 prwfrel2))
          in
            (PrWfDerivExists (prrel_new, kdwf1, prwf2), combine [up1, up2])
          end
    end

  and transform_prop_wellformness_derivation (prwf : prop_wellformedness_derivation, down : Arg.down) =
    case Arg.transformer_prop_wellformness_derivation (transform_prop_wellformness_derivation, transform_kind_wellformness_derivation, transform_kinding_derivation) (prwf, down) of
      SOME res => res
    | NONE => default_transform_prop_wellformness_derivation (prwf, down)

  and default_transform_type_equivalence_derivation (tyeq : type_equivalence_derivation, down : Arg.down) =
    let
      fun on_rel tyrel = Arg.on_type_equivalence_relation (tyrel, down)
      fun on_prderiv prderiv = transform_proping_derivation (prderiv, down)
      fun on_tyeq tyeq = transform_type_equivalence_derivation (tyeq, down)
      fun on_kdeq kdeq = transform_kind_equivalence_derivation (kdeq, down)
    in
      case tyeq of
        TyEqDerivAssume tyrel =>
          let
            val (tyrel, up0) = on_rel tyrel
          in
            (TyEqDerivAssume tyrel, combine [up0])
          end
      | TyEqDerivTypeUnit tyrel =>
          let
            val (tyrel, up0) = on_rel tyrel
          in
            (TyEqDerivTypeUnit tyrel, combine [up0])
          end
      | TyEqDerivTypeInt tyrel =>
          let
            val (tyrel, up0) = on_rel tyrel
          in
            (TyEqDerivTypeInt tyrel, combine [up0])
          end
      | TyEqDerivTypeNat (tyrel, prderiv1) =>
          let
            (*val (tyrel, up0) = on_rel tyrel*)
            val (prderiv1, up1) = on_prderiv prderiv1
            val prrel1 = extract_prrel prderiv1
            val (_,  cstr1, cstr2) = extract_pr_bin_rel (#2 prrel1)
            val tyrel_new = (#1 prrel1, CstrTypeNat cstr1, CstrTypeNat cstr2)
          in
            (TyEqDerivTypeNat (tyrel_new, prderiv1), combine [up1])
          end
      | TyEqDerivTypeArray (tyrel, tyeq1, prderiv2) =>
          let
            (*val (tyrel, up0) = on_rel tyrel*)
            val (tyeq1, up1) = on_tyeq tyeq1
            val (prderiv2, up2) = on_prderiv prderiv2
            val tyeqrel1 = extract_tyeqrel tyeq1
            val prrel2 = extract_prrel prderiv2
            val (_, cstr1, cstr2) = extract_pr_bin_rel (#2 prrel2)
            val tyrel_new = (#1 tyeqrel1, CstrTypeArray (#2 tyeqrel1, cstr1), CstrTypeArray (#3 tyeqrel1, cstr2))
          in
            (TyEqDerivTypeArray (tyrel_new, tyeq1, prderiv2), combine [up1, up2])
          end
      | TyEqDerivArrow (tyrel, tyeq1, tyeq2, prderiv3) =>
          let
            (*val (tyrel, up0) = on_rel tyrel*)
            val (tyeq1, up1) = on_tyeq tyeq1
            val (tyeq2, up2) = on_tyeq tyeq2
            val (prderiv3, up3) = on_prderiv prderiv3
            val tyeqrel1 = extract_tyeqrel tyeq1
            val tyeqrel2 = extract_tyeqrel tyeq1
            val prrel3 = extract_prrel prderiv3
            val (_, ti1, ti2) = extract_pr_bin_rel (#2 prrel3)
            val tyrel_new = (#1 tyeqrel1, CstrArrow (#2 tyeqrel1, #2 tyeqrel2, ti1), CstrArrow (#3 tyeqrel1, #3 tyeqrel2, ti2))
          in
            (TyEqDerivArrow (tyrel_new, tyeq1, tyeq2, prderiv3), combine [up1, up2, up3])
          end
      | TyEqDerivProd (tyrel, tyeq1, tyeq2) =>
          let
            (*val (tyrel, up0) = on_rel tyrel*)
            val (tyeq1, up1) = on_tyeq tyeq1
            val (tyeq2, up2) = on_tyeq tyeq2
            val tyeqrel1 = extract_tyeqrel tyeq1
            val tyeqrel2 = extract_tyeqrel tyeq2
            val tyrel_new = (#1 tyeqrel1, CstrProd (#2 tyeqrel1, #2 tyeqrel2), CstrProd (#3 tyeqrel1, #3 tyeqrel2))
          in
            (TyEqDerivProd (tyrel_new, tyeq1, tyeq2), combine [up1, up2])
          end
      | TyEqDerivSum (tyrel, tyeq1, tyeq2) =>
          let
            (*val (tyrel, up0) = on_rel tyrel*)
            val (tyeq1, up1) = on_tyeq tyeq1
            val (tyeq2, up2) = on_tyeq tyeq2
            val tyeqrel1 = extract_tyeqrel tyeq1
            val tyeqrel2 = extract_tyeqrel tyeq2
            val tyrel_new = (#1 tyeqrel1, CstrSum (#2 tyeqrel1, #2 tyeqrel2), CstrSum (#3 tyeqrel1, #3 tyeqrel2))
          in
            (TyEqDerivSum (tyrel_new, tyeq1, tyeq2), combine [up1, up2])
          end
      | TyEqDerivForall (tyrel, kdeq1, tyeq2) =>
          let
            (*val (tyrel, up0) = on_rel tyrel*)
            val (kdeq1, up1) = on_kdeq kdeq1
            val (tyeq2, up2) = on_tyeq tyeq2
            val kdeqrel1 = extract_kdeqrel kdeq1
            val tyeqrel2 = extract_tyeqrel tyeq2
            val tyrel_new = (#1 kdeqrel1, CstrForall (#2 kdeqrel1, #2 tyeqrel2), CstrForall (#3 kdeqrel1, #3 tyeqrel2))
          in
            (TyEqDerivForall (tyrel_new, kdeq1, tyeq2), combine [up1, up2])
          end
      | TyEqDerivExists (tyrel, kdeq1, tyeq2) =>
          let
            (*val (tyrel, up0) = on_rel tyrel*)
            val (kdeq1, up1) = on_kdeq kdeq1
            val (tyeq2, up2) = on_tyeq tyeq2
            val kdeqrel1 = extract_kdeqrel kdeq1
            val tyeqrel2 = extract_tyeqrel tyeq2
            val tyrel_new = (#1 kdeqrel1, CstrExists (#2 kdeqrel1, #2 tyeqrel2), CstrExists (#3 kdeqrel1, #3 tyeqrel2))
          in
            (TyEqDerivExists (tyrel_new, kdeq1, tyeq2), combine [up1, up2])
          end
      | TyEqDerivRec (tyrel, kdeq1, tyeq2) =>
          let
            (*val (tyrel, up0) = on_rel tyrel*)
            val (kdeq1, up1) = on_kdeq kdeq1
            val (tyeq2, up2) = on_tyeq tyeq2
            val kdeqrel1 = extract_kdeqrel kdeq1
            val tyeqrel2 = extract_tyeqrel tyeq2
            val tyrel_new = (#1 kdeqrel1, CstrRec (#2 kdeqrel1, #2 tyeqrel2), CstrRec (#3 kdeqrel1, #3 tyeqrel2))
          in
            (TyEqDerivRec (tyrel_new, kdeq1, tyeq2), combine [up1, up2])
          end
      | TyEqDerivAbs (tyrel, kdeq1, tyeq2) =>
          let
            (*val (tyrel, up0) = on_rel tyrel*)
            val (kdeq1, up1) = on_kdeq kdeq1
            val (tyeq2, up2) = on_tyeq tyeq2
            val kdeqrel1 = extract_kdeqrel kdeq1
            val tyeqrel2 = extract_tyeqrel tyeq2
            val tyrel_new = (#1 kdeqrel1, CstrAbs (#2 kdeqrel1, #2 tyeqrel2), CstrAbs (#3 kdeqrel1, #3 tyeqrel2))
          in
            (TyEqDerivAbs (tyrel_new, kdeq1, tyeq2), combine [up1, up2])
          end
      | TyEqDerivApp (tyrel, tyeq1, tyeq2) =>
          let
            (*val (tyrel, up0) = on_rel tyrel*)
            val (tyeq1, up1) = on_tyeq tyeq1
            val (tyeq2, up2) = on_tyeq tyeq2
            val tyeqrel1 = extract_tyeqrel tyeq1
            val tyeqrel2 = extract_tyeqrel tyeq2
            val tyrel_new = (#1 tyeqrel1, CstrApp (#2 tyeqrel1, #2 tyeqrel2), CstrApp (#3 tyeqrel1, #3 tyeqrel2))
          in
            (TyEqDerivApp (tyrel_new, tyeq1, tyeq2), combine [up1, up2])
          end
      | TyEqDerivIndex (tyrel, prderiv1) =>
          let
            (*val (tyrel, up0) = on_rel tyrel*)
            val (prderiv1, up1) = on_prderiv prderiv1
            val prrel1 = extract_prrel prderiv1
            val (_, cstr1, cstr2) = extract_pr_bin_rel (#2 prrel1)
            val tyrel_new = (#1 prrel1, cstr1, cstr2)
          in
            (TyEqDerivIndex (tyrel_new, prderiv1), combine [up1])
          end
    end

  and transform_type_equivalence_derivation (tyeq : type_equivalence_derivation, down : Arg.down) =
    case Arg.transformer_type_equivalence_derivation (transform_type_equivalence_derivation, transform_kind_equivalence_derivation, transform_proping_derivation) (tyeq, down) of
      SOME res => res
    | NONE => default_transform_type_equivalence_derivation (tyeq, down)

  and default_transform_kind_equivalence_derivation (kdeq : kind_equivalence_derivation, down : Arg.down) =
    let
      (*fun on_rel kdrel = Arg.on_kind_equivalence_relation (kdrel, down)*)
      fun on_kdsub kdsub = transform_kind_sub_derivation (kdsub, down)
    in
      case kdeq of
        KdEqDerivBiSub (kdrel, kdsub1, kdsub2) =>
          let
            (*val (kdrel, up0) = on_rel kdrel*)
            val (kdsub1, up1) = on_kdsub kdsub1
            val (kdsub2, up2) = on_kdsub kdsub2
            val kdsubrel1 = extract_kdsubrel kdsub1
            val kdsubrel2 = extract_kdsubrel kdsub2
            val kdrel_new = (#1 kdsubrel1, #2 kdsubrel1, #3 kdsubrel1)
          in
            (KdEqDerivBiSub (kdrel_new, kdsub1, kdsub2), combine [up1, up2])
          end
    end

  and transform_kind_equivalence_derivation (kdeq : kind_equivalence_derivation, down : Arg.down) =
    case Arg.transformer_kind_equivalence_derivation transform_kind_sub_derivation (kdeq, down) of
      SOME res => res
    | NONE => default_transform_kind_equivalence_derivation (kdeq, down)

  and default_transform_kind_sub_derivation (kdsub : kind_sub_derivation, down : Arg.down) =
    let
      (*fun on_rel kdrel = Arg.on_kind_sub_relation (kdrel, down)*)
      fun on_kdderiv kdderiv = transform_kinding_derivation (kdderiv, down)
    in
      case kdsub of
        KdSubDerivSub (kdrel, kdderiv1) =>
          let
            (*val (kdrel, up0) = on_rel kdrel*)
            val (kdderiv1, up1) = on_kdderiv kdderiv1
            val kdrel1 = extract_kdrel kdderiv1
            val kdrel_new = (tl (#1 kdrel1), case hd (#1 kdrel1) of BdKind kd => kd | _ => raise (Impossible "must be kind"), Passes.TermShift.shift_kind ~1 (#3 kdrel1))
          in
            (KdSubDerivSub (kdrel_new, kdderiv1), combine [up1])
          end
    end

  and transform_kind_sub_derivation (kdsub : kind_sub_derivation, down : Arg.down) =
    case Arg.transformer_kind_sub_derivation transform_kinding_derivation (kdsub, down) of
      SOME res => res
    | NONE => default_transform_kind_sub_derivation (kdsub, down)
end
