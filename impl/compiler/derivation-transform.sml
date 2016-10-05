functor TypingDerivationTransformPass(Arg:
sig
  type down
  type up

  val on_typing_relation : MicroTiML.typing_relation * down -> MicroTiML.typing_relation
  val on_kinding_relation : MicroTiML.kinding_relation * down -> MicroTiML.kinding_relation
  val on_proping_relation : MicroTiML.proping_relation * down -> MicroTiML.proping_relation

  val on_kind_wellformness_relation : MicroTiML.kind_wellformedness_relation * down -> MicroTiML.kind_wellformedness_relation
  val on_prop_wellformness_relation : MicroTiML.prop_wellformedness_relation * down -> MicroTiML.prop_wellformedness_relation

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

  fun combine (ups : Arg.up list) = List.foldl Arg.combiner Arg.upward_base ups

  fun default_transform_typing_derivation (tyderiv : typing_derivation, down : Arg.down) =
    let
      fun on_rel tyrel = Arg.on_typing_relation (tyrel, down)
      fun on_tyderiv tyderiv = transform_typing_derivation (tyderiv, down)
      fun on_kdderiv kdderiv = transform_kinding_derivation (kdderiv, down)
      fun on_prderiv prderiv = transform_proping_derivation (prderiv, down)
    in
      case tyderiv of
        TyDerivVar tyrel => (TyDerivVar (on_rel tyrel), Arg.upward_base)
      | TyDerivInt tyrel => (TyDerivInt (on_rel tyrel), Arg.upward_base)
      | TyDerivNat tyrel => (TyDerivNat (on_rel tyrel), Arg.upward_base)
      | TyDerivUnit tyrel => (TyDerivUnit (on_rel tyrel), Arg.upward_base)
      | TyDerivApp (tyrel, tyderiv1, tyderiv2) =>
          let
            val (tyderiv1, up1) = on_tyderiv tyderiv1
            val (tyderiv2, up2) = on_tyderiv tyderiv2
          in
            (TyDerivApp (on_rel tyrel, tyderiv1, tyderiv2), combine [up1, up2])
          end
      | TyDerivAbs (tyrel, kdderiv1, tyderiv2) =>
          let
            val (kdderiv1, up1) = on_kdderiv kdderiv1
            val (tyderiv2, up2) = on_tyderiv tyderiv2
          in
           (TyDerivAbs (on_rel tyrel, kdderiv1, tyderiv2), combine [up1, up2])
          end
      | TyDerivRec (tyrel, kdderiv1, tyderiv2) =>
          let
            val (kdderiv1, up1) = on_kdderiv kdderiv1
            val (tyderiv2, up2) = on_tyderiv tyderiv2
          in
            (TyDerivRec (on_rel tyrel, kdderiv1, tyderiv2), combine [up1, up2])
          end
      | TyDerivPair (tyrel, tyderiv1, tyderiv2) =>
          let
            val (tyderiv1, up1) = on_tyderiv tyderiv1
            val (tyderiv2, up2) = on_tyderiv tyderiv2
          in
            (TyDerivPair (on_rel tyrel, tyderiv1, tyderiv2), combine [up1, up2])
          end
      | TyDerivFst (tyrel, tyderiv1) =>
          let
            val (tyderiv1, up1) = on_tyderiv tyderiv1
          in
            (TyDerivFst (on_rel tyrel, tyderiv1), combine [up1])
          end
      | TyDerivSnd (tyrel, tyderiv1) =>
          let
            val (tyderiv1, up1) = on_tyderiv tyderiv1
          in
            (TyDerivSnd (on_rel tyrel, tyderiv1), combine [up1])
          end
      | TyDerivInLeft (tyrel, kdderiv1, tyderiv2) =>
          let
            val (kdderiv1, up1) = on_kdderiv kdderiv1
            val (tyderiv2, up2) = on_tyderiv tyderiv2
          in
            (TyDerivInLeft (on_rel tyrel, kdderiv1, tyderiv2), combine [up1, up2])
          end
      | TyDerivInRight (tyrel, kdderiv1, tyderiv2) =>
          let
            val (kdderiv1, up1) = on_kdderiv kdderiv1
            val (tyderiv2, up2) = on_tyderiv tyderiv2
          in
            (TyDerivInRight (on_rel tyrel, kdderiv1, tyderiv2), combine [up1, up2])
          end
      | TyDerivCase (tyrel, tyderiv1, tyderiv2, tyderiv3) =>
          let
            val (tyderiv1, up1) = on_tyderiv tyderiv1
            val (tyderiv2, up2) = on_tyderiv tyderiv2
            val (tyderiv3, up3) = on_tyderiv tyderiv3
          in
            (TyDerivCase (on_rel tyrel, tyderiv1, tyderiv2, tyderiv3), combine [up1, up2, up3])
          end
      | TyDerivFold (tyrel, kdderiv1, tyderiv2) =>
          let
            val (kdderiv1, up1) = on_kdderiv kdderiv1
            val (tyderiv2, up2) = on_tyderiv tyderiv2
          in
            (TyDerivFold (on_rel tyrel, kdderiv1, tyderiv2), combine [up1, up2])
          end
      | TyDerivUnfold (tyrel, tyderiv1) =>
          let
            val (tyderiv1, up1) = on_tyderiv tyderiv1
          in
            (TyDerivUnfold (on_rel tyrel, tyderiv1), combine [up1])
          end
      | TyDerivPack (tyrel, kdderiv1, kdderiv2, tyderiv3) =>
          let
            val (kdderiv1, up1) = on_kdderiv kdderiv1
            val (kdderiv2, up2) = on_kdderiv kdderiv2
            val (tyderiv3, up3) = on_tyderiv tyderiv3
          in
            (TyDerivPack (on_rel tyrel, kdderiv1, kdderiv2, tyderiv3), combine [up1, up2, up3])
          end
      | TyDerivUnpack (tyrel, tyderiv1, tyderiv2) =>
          let
            val (tyderiv1, up1) = on_tyderiv tyderiv1
            val (tyderiv2, up2) = on_tyderiv tyderiv2
          in
            (TyDerivUnpack (on_rel tyrel, tyderiv1, tyderiv2), combine [up1, up2])
          end
      | TyDerivCstrAbs (tyrel, kdwf1, tyderiv2) =>
          let
            val (tyderiv2, up2) = on_tyderiv tyderiv2
          in
            (TyDerivCstrAbs (on_rel tyrel, kdwf1, tyderiv2), combine [up2])
          end
      | TyDerivCstrApp (tyrel, tyderiv1, kdderiv2) =>
          let
            val (tyderiv1, up1) = on_tyderiv tyderiv1
            val (kdderiv2, up2) = on_kdderiv kdderiv2
          in
            (TyDerivCstrApp (on_rel tyrel, tyderiv1, kdderiv2), combine [up1, up2])
          end
      | TyDerivBinOp (tyrel, tyderiv1, tyderiv2) =>
          let
            val (tyderiv1, up1) = on_tyderiv tyderiv1
            val (tyderiv2, up2) = on_tyderiv tyderiv2
          in
            (TyDerivBinOp (on_rel tyrel, tyderiv1, tyderiv2), combine [up1, up2])
          end
      | TyDerivArrayNew (tyrel, tyderiv1, tyderiv2) =>
          let
            val (tyderiv1, up1) = on_tyderiv tyderiv1
            val (tyderiv2, up2) = on_tyderiv tyderiv2
          in
            (TyDerivArrayNew (on_rel tyrel, tyderiv1, tyderiv2), combine [up1, up2])
          end
      | TyDerivArrayGet (tyrel, tyderiv1, tyderiv2, prderiv3) =>
          let
            val (tyderiv1, up1) = on_tyderiv tyderiv1
            val (tyderiv2, up2) = on_tyderiv tyderiv2
            val (prderiv3, up3) = on_prderiv prderiv3
          in
            (TyDerivArrayGet (on_rel tyrel, tyderiv1, tyderiv2, prderiv3), combine [up1, up2, up3])
          end
      | TyDerivArrayPut (tyrel, tyderiv1, tyderiv2, prderiv3, tyderiv4) =>
          let
            val (tyderiv1, up1) = on_tyderiv tyderiv1
            val (tyderiv2, up2) = on_tyderiv tyderiv2
            val (prderiv3, up3) = on_prderiv prderiv3
            val (tyderiv4, up4) = on_tyderiv tyderiv4
          in
            (TyDerivArrayPut (on_rel tyrel, tyderiv1, tyderiv2, prderiv3, tyderiv4), combine [up1, up2, up3, up4])
          end
      | TyDerivLet (tyrel, tyderiv1, tyderiv2) =>
          let
            val (tyderiv1, up1) = on_tyderiv tyderiv1
            val (tyderiv2, up2) = on_tyderiv tyderiv2
          in
            (TyDerivLet (on_rel tyrel, tyderiv1, tyderiv2), combine [up1, up2])
          end
      | TyDerivNever (tyrel, prderiv1) =>
          let
            val (prderiv1, up1) = on_prderiv prderiv1
          in
            (TyDerivNever (on_rel tyrel, prderiv1), combine [up1])
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
    in
      case kdderiv of
        KdDerivRefine (kdrel, kdderiv1, prderiv2) =>
          let
            val (kdderiv1, up1) = on_kdderiv kdderiv1
            val (prderiv2, up2) = on_prderiv prderiv2
          in
            (KdDerivRefine (on_rel kdrel, kdderiv1, prderiv2), combine [up1, up2])
          end
      | KdDerivVar kdrel => (KdDerivVar (on_rel kdrel), Arg.upward_base)
      | KdDerivNat kdrel => (KdDerivNat (on_rel kdrel), Arg.upward_base)
      | KdDerivTime kdrel => (KdDerivTime (on_rel kdrel), Arg.upward_base)
      | KdDerivUnit kdrel => (KdDerivUnit (on_rel kdrel), Arg.upward_base)
      | KdDerivTrue kdrel => (KdDerivTrue (on_rel kdrel), Arg.upward_base)
      | KdDerivFalse kdrel => (KdDerivFalse (on_rel kdrel), Arg.upward_base)
      | KdDerivUnOp (kdrel, kdderiv1) =>
          let
            val (kdderiv1, up1) = on_kdderiv kdderiv1
          in
            (KdDerivUnOp (on_rel kdrel, kdderiv1), combine [up1])
          end
      | KdDerivBinOp (kdrel, kdderiv1, kdderiv2) =>
          let
            val (kdderiv1, up1) = on_kdderiv kdderiv1
            val (kdderiv2, up2) = on_kdderiv kdderiv2
          in
            (KdDerivBinOp (on_rel kdrel, kdderiv1, kdderiv2), combine [up1, up2])
          end
      | KdDerivIte (kdrel, kdderiv1, kdderiv2, kdderiv3) =>
          let
            val (kdderiv1, up1) = on_kdderiv kdderiv1
            val (kdderiv2, up2) = on_kdderiv kdderiv2
            val (kdderiv3, up3) = on_kdderiv kdderiv3
          in
            (KdDerivIte (on_rel kdrel, kdderiv1, kdderiv2, kdderiv3), combine [up1, up2, up3])
          end
      | KdDerivTimeAbs (kdrel, kdderiv1) =>
          let
            val (kdderiv1, up1) = on_kdderiv kdderiv1
          in
            (KdDerivTimeAbs (on_rel kdrel, kdderiv1), combine [up1])
          end
      | KdDerivProd (kdrel, kdderiv1, kdderiv2) =>
          let
            val (kdderiv1, up1) = on_kdderiv kdderiv1
            val (kdderiv2, up2) = on_kdderiv kdderiv2
          in
            (KdDerivProd (on_rel kdrel, kdderiv1, kdderiv2), combine [up1, up2])
          end
      | KdDerivSum (kdrel, kdderiv1, kdderiv2) =>
          let
            val (kdderiv1, up1) = on_kdderiv kdderiv1
            val (kdderiv2, up2) = on_kdderiv kdderiv2
          in
            (KdDerivSum (on_rel kdrel, kdderiv1, kdderiv2), combine [up1, up2])
          end
      | KdDerivArrow (kdrel, kdderiv1, kdderiv2, kdderiv3) =>
          let
            val (kdderiv1, up1) = on_kdderiv kdderiv1
            val (kdderiv2, up2) = on_kdderiv kdderiv2
            val (kdderiv3, up3) = on_kdderiv kdderiv3
          in
            (KdDerivArrow (on_rel kdrel, kdderiv1, kdderiv2, kdderiv3), combine [up1, up2, up3])
          end
      | KdDerivApp (kdrel, kdderiv1, kdderiv2) =>
          let
            val (kdderiv1, up1) = on_kdderiv kdderiv1
            val (kdderiv2, up2) = on_kdderiv kdderiv2
          in
            (KdDerivApp (on_rel kdrel, kdderiv1, kdderiv2), combine [up1, up2])
          end
      | KdDerivAbs (kdrel, kdwf1, kdderiv2) =>
          let
            val (kdderiv2, up2) = on_kdderiv kdderiv2
          in
            (KdDerivAbs (on_rel kdrel, kdwf1, kdderiv2), combine [up2])
          end
      | KdDerivForall (kdrel, kdwf1, kdderiv2) =>
          let
            val (kdderiv2, up2) = on_kdderiv kdderiv2
          in
            (KdDerivForall (on_rel kdrel, kdwf1, kdderiv2), combine [up2])
          end
      | KdDerivExists (kdrel, kdwf1, kdderiv2) =>
          let
            val (kdderiv2, up2) = on_kdderiv kdderiv2
          in
            (KdDerivExists (on_rel kdrel, kdwf1, kdderiv2), combine [up2])
          end
      | KdDerivRec (kdrel, kdwf1, kdderiv2) =>
          let
            val (kdderiv2, up2) = on_kdderiv kdderiv2
          in
            (KdDerivRec (on_rel kdrel, kdwf1, kdderiv2), combine [up2])
          end
      | KdDerivTypeUnit kdrel => (KdDerivTypeUnit (on_rel kdrel), Arg.upward_base)
      | KdDerivTypeInt kdrel => (KdDerivTypeInt (on_rel kdrel), Arg.upward_base)
      | KdDerivTypeNat (kdrel, kdderiv1) =>
          let
            val (kdderiv1, up1) = on_kdderiv kdderiv1
          in
            (KdDerivTypeNat (on_rel kdrel, kdderiv1), combine [up1])
          end
      | KdDerivTypeArray (kdrel, kdderiv1, kdderiv2) =>
          let
            val (kdderiv1, up1) = on_kdderiv kdderiv1
            val (kdderiv2, up2) = on_kdderiv kdderiv2
          in
            (KdDerivTypeArray (on_rel kdrel, kdderiv1, kdderiv2), combine [up1, up2])
          end
    end

  and transform_kinding_derivation (kdderiv : kinding_derivation, down : Arg.down) =
    case Arg.transformer_kinding_derivation (transform_kinding_derivation, transform_proping_derivation, transform_kind_wellformness_derivation) (kdderiv, down) of
      SOME res => res
    | NONE => default_transform_kinding_derivation (kdderiv, down)

  and default_transform_proping_derivation (prderiv : proping_derivation, down : Arg.down) =
    case prderiv of
      PrDerivAdmit prrel => (PrDerivAdmit (Arg.on_proping_relation (prrel, down)), Arg.upward_base)

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
        KdWfDerivNat kdrel => (KdWfDerivNat (on_rel kdrel), Arg.upward_base)
      | KdWfDerivUnit kdrel => (KdWfDerivUnit (on_rel kdrel), Arg.upward_base)
      | KdWfDerivBool kdrel => (KdWfDerivBool (on_rel kdrel), Arg.upward_base)
      | KdWfDerivTimeFun kdrel => (KdWfDerivTimeFun (on_rel kdrel), Arg.upward_base)
      | KdWfDerivSubset (kdrel, kdwf1, prwf2) =>
          let
            val (kdwf1, up1) = on_kdwf kdwf1
            val (prwf2, up2) = on_prwf prwf2
          in
            (KdWfDerivSubset (on_rel kdrel, kdwf1, prwf2), combine [up1, up2])
          end
      | KdWfDerivProper kdrel => (KdWfDerivProper (on_rel kdrel), Arg.upward_base)
      | KdWfDerivArrow (kdrel, kdwf1, kdwf2) =>
          let
            val (kdwf1, up1) = on_kdwf kdwf1
            val (kdwf2, up2) = on_kdwf kdwf2
          in
            (KdWfDerivArrow (on_rel kdrel, kdwf1, kdwf2), combine [up1, up2])
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
        PrWfDerivTop prrel => (PrWfDerivTop (on_rel prrel), Arg.upward_base)
      | PrWfDerivBot prrel => (PrWfDerivBot (on_rel prrel), Arg.upward_base)
      | PrWfDerivBinConn (prrel, prwf1, prwf2) =>
          let
            val (prwf1, up1) = on_prwf prwf1
            val (prwf2, up2) = on_prwf prwf2
          in
            (PrWfDerivBinConn (on_rel prrel, prwf1, prwf2), combine [up1, up2])
          end
      | PrWfDerivNot (prrel, prwf1) =>
          let
            val (prwf1, up1) = on_prwf prwf1
          in
            (PrWfDerivNot (on_rel prrel, prwf1), combine [up1])
          end
      | PrWfDerivBinRel (prrel, kdderiv1, kdderiv2) =>
          let
            val (kdderiv1, up1) = on_kdderiv kdderiv1
            val (kdderiv2, up2) = on_kdderiv kdderiv2
          in
            (PrWfDerivBinRel (on_rel prrel, kdderiv1, kdderiv2), combine [up1, up2])
          end
      | PrWfDerivForall (prrel, kdwf1, prwf2) =>
          let
            val (kdwf1, up1) = on_kdwf kdwf1
            val (prwf2, up2) = on_prwf prwf2
          in
            (PrWfDerivForall (on_rel prrel, kdwf1, prwf2), combine [up1, up2])
          end
      | PrWfDerivExists (prrel, kdwf1, prwf2) =>
          let
            val (kdwf1, up1) = on_kdwf kdwf1
            val (prwf2, up2) = on_prwf prwf2
          in
            (PrWfDerivExists (on_rel prrel, kdwf1, prwf2), combine [up1, up2])
          end
    end

  and transform_prop_wellformness_derivation (prwf : prop_wellformedness_derivation, down : Arg.down) =
    case Arg.transformer_prop_wellformness_derivation (transform_prop_wellformness_derivation, transform_kind_wellformness_derivation, transform_kinding_derivation) (prwf, down) of
      SOME res => res
    | NONE => default_transform_prop_wellformness_derivation (prwf, down)
end
