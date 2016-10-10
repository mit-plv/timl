functor TypingDerivationTransformPass(Arg:
sig
  type down
  type up

  val on_typing_relation : MicroTiML.typing_relation * down -> MicroTiML.typing_relation * up
  val on_kinding_relation : MicroTiML.kinding_relation * down -> MicroTiML.kinding_relation * up
  val on_proping_relation : MicroTiML.proping_relation * down -> MicroTiML.proping_relation * up

  val on_kind_wellformness_relation : MicroTiML.kind_wellformedness_relation * down -> MicroTiML.kind_wellformedness_relation * up
  val on_prop_wellformness_relation : MicroTiML.prop_wellformedness_relation * down -> MicroTiML.prop_wellformedness_relation * up

  val transformer_typing_derivation : (MicroTiML.typing_derivation * down -> MicroTiML.typing_derivation * up) * (MicroTiML.kinding_derivation * down -> MicroTiML.kinding_derivation * up) * (MicroTiML.proping_derivation * down -> MicroTiML.proping_derivation * up) * (MicroTiML.kind_wellformedness_derivation * down -> MicroTiML.kind_wellformedness_derivation * up) -> (MicroTiML.typing_derivation * down) -> (MicroTiML.typing_derivation * up) option
  val transformer_kinding_derivation : (MicroTiML.kinding_derivation * down -> MicroTiML.kinding_derivation * up) * (MicroTiML.proping_derivation * down -> MicroTiML.proping_derivation * up) * (MicroTiML.kind_wellformedness_derivation * down -> MicroTiML.kind_wellformedness_derivation * up) -> (MicroTiML.kinding_derivation * down) -> (MicroTiML.kinding_derivation * up) option
  val transformer_proping_derivation : (MicroTiML.proping_derivation * down) -> (MicroTiML.proping_derivation * up) option

  val transformer_kind_wellformness_derivation : (MicroTiML.kind_wellformedness_derivation * down -> MicroTiML.kind_wellformedness_derivation * up) * (MicroTiML.prop_wellformedness_derivation * down -> MicroTiML.prop_wellformedness_derivation * up) -> (MicroTiML.kind_wellformedness_derivation * down) -> (MicroTiML.kind_wellformedness_derivation * up) option
  val transformer_prop_wellformness_derivation : (MicroTiML.prop_wellformedness_derivation * down -> MicroTiML.prop_wellformedness_derivation * up) * (MicroTiML.kind_wellformedness_derivation * down -> MicroTiML.kind_wellformedness_derivation * up) * (MicroTiML.kinding_derivation * down -> MicroTiML.kinding_derivation * up) -> (MicroTiML.prop_wellformedness_derivation * down) -> (MicroTiML.prop_wellformedness_derivation * up) option

  val upward_base : up
  val combiner : (up * up) -> up
end
) =
struct
  open MicroTiML

  (* FIXME: reconstruct typing relation when sub-calls retun *)

  fun combine (ups : Arg.up list) = List.foldl Arg.combiner Arg.upward_base ups

  fun default_transform_typing_derivation (tyderiv : typing_derivation, down : Arg.down) =
    let
      fun on_rel tyrel = Arg.on_typing_relation (tyrel, down)
      fun on_tyderiv tyderiv = transform_typing_derivation (tyderiv, down)
      fun on_kdderiv kdderiv = transform_kinding_derivation (kdderiv, down)
      fun on_prderiv prderiv = transform_proping_derivation (prderiv, down)
      fun on_kdwf kdwf = transform_kind_wellformness_derivation (kdwf, down)
    in
      case tyderiv of
        TyDerivSub (tyrel, tyderiv1, prderiv2) =>
          let
            val (tyrel, up0) = on_rel tyrel
            val (tyderiv1, up1) = on_tyderiv tyderiv1
            val (prderiv2, up2) = on_prderiv prderiv2
          in
            (TyDerivSub (tyrel, tyderiv1, prderiv2), combine [up0, up1, up2])
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
            val (tyrel, up0) = on_rel tyrel
            val (tyderiv1, up1) = on_tyderiv tyderiv1
            val (tyderiv2, up2) = on_tyderiv tyderiv2
          in
            (TyDerivApp (tyrel, tyderiv1, tyderiv2), combine [up0, up1, up2])
          end
      | TyDerivAbs (tyrel, kdderiv1, tyderiv2) =>
          let
            val (tyrel, up0) = on_rel tyrel
            val (kdderiv1, up1) = on_kdderiv kdderiv1
            val (tyderiv2, up2) = on_tyderiv tyderiv2
          in
           (TyDerivAbs (tyrel, kdderiv1, tyderiv2), combine [up0, up1, up2])
          end
      | TyDerivRec (tyrel, kdderiv1, tyderiv2) =>
          let
            val (tyrel, up0) = on_rel tyrel
            val (kdderiv1, up1) = on_kdderiv kdderiv1
            val (tyderiv2, up2) = on_tyderiv tyderiv2
          in
            (TyDerivRec (tyrel, kdderiv1, tyderiv2), combine [up0, up1, up2])
          end
      | TyDerivPair (tyrel, tyderiv1, tyderiv2) =>
          let
            val (tyrel, up0) = on_rel tyrel
            val (tyderiv1, up1) = on_tyderiv tyderiv1
            val (tyderiv2, up2) = on_tyderiv tyderiv2
          in
            (TyDerivPair (tyrel, tyderiv1, tyderiv2), combine [up0, up1, up2])
          end
      | TyDerivFst (tyrel, tyderiv1) =>
          let
            val (tyrel, up0) = on_rel tyrel
            val (tyderiv1, up1) = on_tyderiv tyderiv1
          in
            (TyDerivFst (tyrel, tyderiv1), combine [up0, up1])
          end
      | TyDerivSnd (tyrel, tyderiv1) =>
          let
            val (tyrel, up0) = on_rel tyrel
            val (tyderiv1, up1) = on_tyderiv tyderiv1
          in
            (TyDerivSnd (tyrel, tyderiv1), combine [up0, up1])
          end
      | TyDerivInLeft (tyrel, kdderiv1, tyderiv2) =>
          let
            val (tyrel, up0) = on_rel tyrel
            val (kdderiv1, up1) = on_kdderiv kdderiv1
            val (tyderiv2, up2) = on_tyderiv tyderiv2
          in
            (TyDerivInLeft (tyrel, kdderiv1, tyderiv2), combine [up0, up1, up2])
          end
      | TyDerivInRight (tyrel, kdderiv1, tyderiv2) =>
          let
            val (tyrel, up0) = on_rel tyrel
            val (kdderiv1, up1) = on_kdderiv kdderiv1
            val (tyderiv2, up2) = on_tyderiv tyderiv2
          in
            (TyDerivInRight (tyrel, kdderiv1, tyderiv2), combine [up0, up1, up2])
          end
      | TyDerivCase (tyrel, tyderiv1, tyderiv2, tyderiv3) =>
          let
            val (tyrel, up0) = on_rel tyrel
            val (tyderiv1, up1) = on_tyderiv tyderiv1
            val (tyderiv2, up2) = on_tyderiv tyderiv2
            val (tyderiv3, up3) = on_tyderiv tyderiv3
          in
            (TyDerivCase (tyrel, tyderiv1, tyderiv2, tyderiv3), combine [up0, up1, up2, up3])
          end
      | TyDerivFold (tyrel, kdderiv1, tyderiv2) =>
          let
            val (tyrel, up0) = on_rel tyrel
            val (kdderiv1, up1) = on_kdderiv kdderiv1
            val (tyderiv2, up2) = on_tyderiv tyderiv2
          in
            (TyDerivFold (tyrel, kdderiv1, tyderiv2), combine [up0, up1, up2])
          end
      | TyDerivUnfold (tyrel, tyderiv1) =>
          let
            val (tyrel, up0) = on_rel tyrel
            val (tyderiv1, up1) = on_tyderiv tyderiv1
          in
            (TyDerivUnfold (tyrel, tyderiv1), combine [up0, up1])
          end
      | TyDerivPack (tyrel, kdderiv1, kdderiv2, tyderiv3) =>
          let
            val (tyrel, up0) = on_rel tyrel
            val (kdderiv1, up1) = on_kdderiv kdderiv1
            val (kdderiv2, up2) = on_kdderiv kdderiv2
            val (tyderiv3, up3) = on_tyderiv tyderiv3
          in
            (TyDerivPack (tyrel, kdderiv1, kdderiv2, tyderiv3), combine [up0, up1, up2, up3])
          end
      | TyDerivUnpack (tyrel, tyderiv1, tyderiv2) =>
          let
            val (tyrel, up0) = on_rel tyrel
            val (tyderiv1, up1) = on_tyderiv tyderiv1
            val (tyderiv2, up2) = on_tyderiv tyderiv2
          in
            (TyDerivUnpack (tyrel, tyderiv1, tyderiv2), combine [up0, up1, up2])
          end
      | TyDerivCstrAbs (tyrel, kdwf1, tyderiv2) =>
          let
            val (tyrel, up0) = on_rel tyrel
            val (kdwf1, up1) = on_kdwf kdwf1
            val (tyderiv2, up2) = on_tyderiv tyderiv2
          in
            (TyDerivCstrAbs (tyrel, kdwf1, tyderiv2), combine [up0, up1, up2])
          end
      | TyDerivCstrApp (tyrel, tyderiv1, kdderiv2) =>
          let
            val (tyrel, up0) = on_rel tyrel
            val (tyderiv1, up1) = on_tyderiv tyderiv1
            val (kdderiv2, up2) = on_kdderiv kdderiv2
          in
            (TyDerivCstrApp (tyrel, tyderiv1, kdderiv2), combine [up0, up1, up2])
          end
      | TyDerivBinOp (tyrel, tyderiv1, tyderiv2) =>
          let
            val (tyrel, up0) = on_rel tyrel
            val (tyderiv1, up1) = on_tyderiv tyderiv1
            val (tyderiv2, up2) = on_tyderiv tyderiv2
          in
            (TyDerivBinOp (tyrel, tyderiv1, tyderiv2), combine [up0, up1, up2])
          end
      | TyDerivArrayNew (tyrel, tyderiv1, tyderiv2) =>
          let
            val (tyrel, up0) = on_rel tyrel
            val (tyderiv1, up1) = on_tyderiv tyderiv1
            val (tyderiv2, up2) = on_tyderiv tyderiv2
          in
            (TyDerivArrayNew (tyrel, tyderiv1, tyderiv2), combine [up0, up1, up2])
          end
      | TyDerivArrayGet (tyrel, tyderiv1, tyderiv2, prderiv3) =>
          let
            val (tyrel, up0) = on_rel tyrel
            val (tyderiv1, up1) = on_tyderiv tyderiv1
            val (tyderiv2, up2) = on_tyderiv tyderiv2
            val (prderiv3, up3) = on_prderiv prderiv3
          in
            (TyDerivArrayGet (tyrel, tyderiv1, tyderiv2, prderiv3), combine [up0, up1, up2, up3])
          end
      | TyDerivArrayPut (tyrel, tyderiv1, tyderiv2, prderiv3, tyderiv4) =>
          let
            val (tyrel, up0) = on_rel tyrel
            val (tyderiv1, up1) = on_tyderiv tyderiv1
            val (tyderiv2, up2) = on_tyderiv tyderiv2
            val (prderiv3, up3) = on_prderiv prderiv3
            val (tyderiv4, up4) = on_tyderiv tyderiv4
          in
            (TyDerivArrayPut (tyrel, tyderiv1, tyderiv2, prderiv3, tyderiv4), combine [up0, up1, up2, up3, up4])
          end
      | TyDerivLet (tyrel, tyderiv2, tyderiv3) =>
          let
            val (tyrel, up0) = on_rel tyrel
            val (tyderiv2, up2) = on_tyderiv tyderiv2
            val (tyderiv3, up3) = on_tyderiv tyderiv3
          in
            (TyDerivLet (tyrel, tyderiv2, tyderiv3), combine [up0, up2, up3])
          end
      | TyDerivNever (tyrel, kdderiv1, prderiv2) =>
          let
            val (tyrel, up0) = on_rel tyrel
            val (kdderiv1, up1) = on_kdderiv kdderiv1
            val (prderiv2, up2) = on_prderiv prderiv2
          in
            (TyDerivNever (tyrel, kdderiv1, prderiv2), combine [up0, up1, up2])
          end
    end

  and transform_typing_derivation (tyderiv : typing_derivation, down : Arg.down) =
    case Arg.transformer_typing_derivation (transform_typing_derivation, transform_kinding_derivation, transform_proping_derivation, transform_kind_wellformness_derivation) (tyderiv, down) of
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
            val (kdrel, up0) = on_rel kdrel
            val (kdderiv1, up1) = on_kdderiv kdderiv1
            val (prderiv2, up2) = on_prderiv prderiv2
          in
            (KdDerivRefine (kdrel, kdderiv1, prderiv2), combine [up0, up1, up2])
          end
      | KdDerivBase (kdrel, kdderiv1) =>
          let
            val (kdrel, up0) = on_rel kdrel
            val (kdderiv1, up1) = on_kdderiv kdderiv1
          in
            (KdDerivBase (kdrel, kdderiv1), combine [up0, up1])
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
            val (kdrel, up0) = on_rel kdrel
            val (kdderiv1, up1) = on_kdderiv kdderiv1
          in
            (KdDerivUnOp (kdrel, kdderiv1), combine [up0, up1])
          end
      | KdDerivBinOp (kdrel, kdderiv1, kdderiv2) =>
          let
            val (kdrel, up0) = on_rel kdrel
            val (kdderiv1, up1) = on_kdderiv kdderiv1
            val (kdderiv2, up2) = on_kdderiv kdderiv2
          in
            (KdDerivBinOp (kdrel, kdderiv1, kdderiv2), combine [up0, up1, up2])
          end
      | KdDerivIte (kdrel, kdderiv1, kdderiv2, kdderiv3) =>
          let
            val (kdrel, up0) = on_rel kdrel
            val (kdderiv1, up1) = on_kdderiv kdderiv1
            val (kdderiv2, up2) = on_kdderiv kdderiv2
            val (kdderiv3, up3) = on_kdderiv kdderiv3
          in
            (KdDerivIte (kdrel, kdderiv1, kdderiv2, kdderiv3), combine [up0, up1, up2, up3])
          end
      | KdDerivTimeAbs (kdrel, kdderiv1) =>
          let
            val (kdrel, up0) = on_rel kdrel
            val (kdderiv1, up1) = on_kdderiv kdderiv1
          in
            (KdDerivTimeAbs (kdrel, kdderiv1), combine [up0, up1])
          end
      | KdDerivProd (kdrel, kdderiv1, kdderiv2) =>
          let
            val (kdrel, up0) = on_rel kdrel
            val (kdderiv1, up1) = on_kdderiv kdderiv1
            val (kdderiv2, up2) = on_kdderiv kdderiv2
          in
            (KdDerivProd (kdrel, kdderiv1, kdderiv2), combine [up0, up1, up2])
          end
      | KdDerivSum (kdrel, kdderiv1, kdderiv2) =>
          let
            val (kdrel, up0) = on_rel kdrel
            val (kdderiv1, up1) = on_kdderiv kdderiv1
            val (kdderiv2, up2) = on_kdderiv kdderiv2
          in
            (KdDerivSum (kdrel, kdderiv1, kdderiv2), combine [up0, up1, up2])
          end
      | KdDerivArrow (kdrel, kdderiv1, kdderiv2, kdderiv3) =>
          let
            val (kdrel, up0) = on_rel kdrel
            val (kdderiv1, up1) = on_kdderiv kdderiv1
            val (kdderiv2, up2) = on_kdderiv kdderiv2
            val (kdderiv3, up3) = on_kdderiv kdderiv3
          in
            (KdDerivArrow (kdrel, kdderiv1, kdderiv2, kdderiv3), combine [up0, up1, up2, up3])
          end
      | KdDerivApp (kdrel, kdderiv1, kdderiv2) =>
          let
            val (kdrel, up0) = on_rel kdrel
            val (kdderiv1, up1) = on_kdderiv kdderiv1
            val (kdderiv2, up2) = on_kdderiv kdderiv2
          in
            (KdDerivApp (kdrel, kdderiv1, kdderiv2), combine [up0, up1, up2])
          end
      | KdDerivAbs (kdrel, kdwf1, kdderiv2) =>
          let
            val (kdrel, up0) = on_rel kdrel
            val (kdwf1, up1) = on_kdwf kdwf1
            val (kdderiv2, up2) = on_kdderiv kdderiv2
          in
            (KdDerivAbs (kdrel, kdwf1, kdderiv2), combine [up0, up1, up2])
          end
      | KdDerivForall (kdrel, kdwf1, kdderiv2) =>
          let
            val (kdrel, up0) = on_rel kdrel
            val (kdwf1, up1) = on_kdwf kdwf1
            val (kdderiv2, up2) = on_kdderiv kdderiv2
          in
            (KdDerivForall (kdrel, kdwf1, kdderiv2), combine [up0, up1, up2])
          end
      | KdDerivExists (kdrel, kdwf1, kdderiv2) =>
          let
            val (kdrel, up0) = on_rel kdrel
            val (kdwf1, up1) = on_kdwf kdwf1
            val (kdderiv2, up2) = on_kdderiv kdderiv2
          in
            (KdDerivExists (kdrel, kdwf1, kdderiv2), combine [up0, up1, up2])
          end
      | KdDerivRec (kdrel, kdwf1, kdderiv2) =>
          let
            val (kdrel, up0) = on_rel kdrel
            val (kdwf1, up1) = on_kdwf kdwf1
            val (kdderiv2, up2) = on_kdderiv kdderiv2
          in
            (KdDerivRec (kdrel, kdwf1, kdderiv2), combine [up0, up1, up2])
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
            val (kdrel, up0) = on_rel kdrel
            val (kdderiv1, up1) = on_kdderiv kdderiv1
          in
            (KdDerivTypeNat (kdrel, kdderiv1), combine [up0, up1])
          end
      | KdDerivTypeArray (kdrel, kdderiv1, kdderiv2) =>
          let
            val (kdrel, up0) = on_rel kdrel
            val (kdderiv1, up1) = on_kdderiv kdderiv1
            val (kdderiv2, up2) = on_kdderiv kdderiv2
          in
            (KdDerivTypeArray (kdrel, kdderiv1, kdderiv2), combine [up0, up1, up2])
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
            val (kdrel, up0) = on_rel kdrel
            val (kdwf1, up1) = on_kdwf kdwf1
            val (prwf2, up2) = on_prwf prwf2
          in
            (KdWfDerivSubset (kdrel, kdwf1, prwf2), combine [up0, up1, up2])
          end
      | KdWfDerivProper kdrel =>
          let
            val (kdrel, up0) = on_rel kdrel
          in
            (KdWfDerivProper kdrel, combine [up0])
          end
      | KdWfDerivArrow (kdrel, kdwf1, kdwf2) =>
          let
            val (kdrel, up0) = on_rel kdrel
            val (kdwf1, up1) = on_kdwf kdwf1
            val (kdwf2, up2) = on_kdwf kdwf2
          in
            (KdWfDerivArrow (kdrel, kdwf1, kdwf2), combine [up0, up1, up2])
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
            val (prrel, up0) = on_rel prrel
            val (prwf1, up1) = on_prwf prwf1
            val (prwf2, up2) = on_prwf prwf2
          in
            (PrWfDerivBinConn (prrel, prwf1, prwf2), combine [up0, up1, up2])
          end
      | PrWfDerivNot (prrel, prwf1) =>
          let
            val (prrel, up0) = on_rel prrel
            val (prwf1, up1) = on_prwf prwf1
          in
            (PrWfDerivNot (prrel, prwf1), combine [up0, up1])
          end
      | PrWfDerivBinRel (prrel, kdderiv1, kdderiv2) =>
          let
            val (prrel, up0) = on_rel prrel
            val (kdderiv1, up1) = on_kdderiv kdderiv1
            val (kdderiv2, up2) = on_kdderiv kdderiv2
          in
            (PrWfDerivBinRel (prrel, kdderiv1, kdderiv2), combine [up0, up1, up2])
          end
      | PrWfDerivForall (prrel, kdwf1, prwf2) =>
          let
            val (prrel, up0) = on_rel prrel
            val (kdwf1, up1) = on_kdwf kdwf1
            val (prwf2, up2) = on_prwf prwf2
          in
            (PrWfDerivForall (prrel, kdwf1, prwf2), combine [up0, up1, up2])
          end
      | PrWfDerivExists (prrel, kdwf1, prwf2) =>
          let
            val (prrel, up0) = on_rel prrel
            val (kdwf1, up1) = on_kdwf kdwf1
            val (prwf2, up2) = on_prwf prwf2
          in
            (PrWfDerivExists (prrel, kdwf1, prwf2), combine [up0, up1, up2])
          end
    end

  and transform_prop_wellformness_derivation (prwf : prop_wellformedness_derivation, down : Arg.down) =
    case Arg.transformer_prop_wellformness_derivation (transform_prop_wellformness_derivation, transform_kind_wellformness_derivation, transform_kinding_derivation) (prwf, down) of
      SOME res => res
    | NONE => default_transform_prop_wellformness_derivation (prwf, down)
end
