structure MicroTiMLTest =
struct
  open Util
  open MicroTiML

  fun main (prog_name : string, args : string list) : int =
    let
      (*val fac_tm = TmRec (CstrForall (KdNat, CstrArrow (CstrTypeNat (CstrVar 0), CstrExists (KdNat, CstrTypeNat (CstrVar 0)), CstrBinOp (CstrBopMult, CstrTime "7.0", CstrUnOp (CstrUopNat2Time, CstrVar 0)))), TmCstrAbs (KdNat, TmAbs (CstrTypeNat (CstrVar 0), TmCase (TmApp (TmCstrApp (TmVar 5, CstrVar 1), TmVar 0), TmPack (CstrNat 1, TmNat 1), TmApp (TmVar 4, TmPair (TmPack (CstrVar 2, TmVar 1), TmApp (TmCstrApp (TmVar 3, CstrBinOp (CstrBopDiff, CstrVar 2, CstrNat 1)), TmApp (TmCstrApp (TmCstrApp (TmVar 5, CstrVar 2), CstrNat 1), TmPair (TmVar 1, TmNat 1)))))))))*)
      (*val _ = println (snd (Passes.Printer.transform_term ((*Passes.ANF.normalize_term*) fac_tm, ["mult", "minus", "is_zero"])))*)
      val bool_cstr = CstrAbs (KdBool, CstrSum (CstrExists (KdSubset (KdUnit, PrBinRel (PrRelEq, CstrVar 1, CstrTrue)), CstrTypeUnit), CstrExists (KdSubset (KdUnit, PrBinRel (PrRelEq, CstrVar 1, CstrFalse)), CstrTypeUnit)))
      val is_zero_ty = CstrForall (KdNat, CstrArrow (CstrTypeNat (CstrVar 0), CstrApp (bool_cstr, CstrBinOp (CstrBopEq, CstrVar 0, CstrNat 0)), CstrTime "1.0"))
      val minus_ty = CstrForall (KdNat, CstrForall (KdNat, CstrArrow (CstrProd (CstrTypeNat (CstrVar 1), CstrTypeNat (CstrVar 0)), CstrTypeNat (CstrBinOp (CstrBopDiff, CstrVar 1, CstrVar 0)), CstrTime "1.0")))
      val mult_ty = CstrArrow (CstrProd (CstrExists (KdNat, CstrTypeNat (CstrVar 0)), CstrExists (KdNat, CstrTypeNat (CstrVar 0))), CstrExists (KdNat, CstrTypeNat (CstrVar 0)), CstrTime "1.0")
      val fac_ty = CstrForall (KdNat, CstrArrow (CstrTypeNat (CstrVar 0), CstrExists (KdNat, CstrTypeNat (CstrVar 0)), CstrBinOp (CstrBopMult, CstrTime "7.0", CstrUnOp (CstrUopNat2Time, CstrVar 0))))
      val tm1 = TmPack (CstrNat 1, TmNat 1)
      val tm1_ctx = [BdType (CstrExists (KdSubset (KdUnit, PrBinRel (PrRelEq, CstrVar 1, CstrTrue)), CstrTypeUnit)), BdType (CstrTypeNat (CstrVar 0)), BdKind KdNat, BdType fac_ty, BdType mult_ty, BdType minus_ty, BdType is_zero_ty]
      val tm1_rel = (tm1_ctx, tm1, CstrExists (KdNat, CstrTypeNat (CstrVar 0)), CstrTime "0.0")
      val tm1_deriv = TyDerivPack (tm1_rel, KdDerivExists ((tm1_ctx, CstrExists (KdNat, CstrTypeNat (CstrVar 0)), KdProper), KdWfDerivNat (tm1_ctx, KdNat), KdDerivTypeNat ((BdKind KdNat :: tm1_ctx, CstrTypeNat (CstrVar 0), KdProper), KdDerivNat (tm1_ctx, CstrNat 1, KdNat))), KdDerivNat (tm1_ctx, CstrNat 1, KdNat), TyDerivNat (tm1_ctx, TmNat 1, CstrTypeNat (CstrNat 1), CstrTime "0.0"))
      val tm2 = TmPair (TmVar 1, TmNat 1)
      val tm2_ctx = [BdType (CstrExists (KdSubset (KdUnit, PrBinRel (PrRelEq, CstrVar 1, CstrFalse)), CstrTypeUnit)), BdType (CstrTypeNat (CstrVar 0)), BdKind KdNat, BdType fac_ty, BdType mult_ty, BdType minus_ty, BdType is_zero_ty]
      val tm2_rel = (tm2_ctx, tm2, CstrProd (CstrTypeNat (CstrVar 2), CstrTypeNat (CstrNat 1)), CstrTime "0.0")
      val tm2_deriv = TyDerivPair (tm2_rel, TyDerivVar (tm2_ctx, TmVar 1, CstrTypeNat (CstrVar 2), CstrTime "0.0"), TyDerivNat (tm2_ctx, TmNat 1, CstrTypeNat (CstrNat 1), CstrTime "0.0"))
      val tm3 = TmCstrApp (TmCstrApp (TmVar 5, CstrVar 2), CstrNat 1)
      val tm3_ctx = tm2_ctx
      val tm3_rel = (tm3_ctx, tm3, CstrArrow (CstrProd (CstrTypeNat (CstrVar 2), CstrTypeNat (CstrNat 1)), CstrTypeNat (CstrBinOp (CstrBopDiff, CstrVar 2, CstrNat 1)), CstrTime "1.0"), CstrTime "0.0")
      val tm3_deriv = TyDerivCstrApp (tm3_rel, TyDerivCstrApp ((tm3_ctx, TmCstrApp (TmVar 5, CstrVar 2), CstrForall (KdNat, CstrArrow (CstrProd (CstrTypeNat (CstrVar 3), CstrTypeNat (CstrVar 0)), CstrTypeNat (CstrBinOp (CstrBopDiff, CstrVar 3, CstrVar 0)), CstrTime "1.0")), CstrTime "0.0"), TyDerivVar (tm3_ctx, TmVar 5, minus_ty, CstrTime "0.0"), KdDerivVar (tm3_ctx, CstrVar 2, KdNat)), KdDerivNat (tm3_ctx, CstrNat 1, KdNat))
      val tm4 = TmApp (tm3, tm2)
      val tm4_ctx = tm3_ctx
      val tm4_rel = (tm4_ctx, tm4, CstrTypeNat (CstrBinOp (CstrBopDiff, CstrVar 2, CstrNat 1)), CstrTime "1.0")
      val tm4_deriv = TyDerivApp (tm4_rel, tm3_deriv, tm2_deriv)
      val tm5 = TmCstrApp (TmVar 3, CstrBinOp (CstrBopDiff, CstrVar 2, CstrNat 1))
      val tm5_ctx = tm4_ctx
      val tm5_rel = (tm5_ctx, tm5, CstrArrow (CstrTypeNat (CstrBinOp (CstrBopDiff, CstrVar 2, CstrNat 1)), CstrExists (KdNat, CstrTypeNat (CstrVar 0)), CstrBinOp (CstrBopMult, CstrTime "7.0", CstrUnOp (CstrUopNat2Time, CstrBinOp (CstrBopDiff, CstrVar 2, CstrNat 1)))), CstrTime "0.0")
      val tm5_deriv = TyDerivCstrApp (tm5_rel, TyDerivVar (tm5_ctx, TmVar 3, fac_ty, CstrTime "0.0"), KdDerivBinOp ((tm5_ctx, CstrBinOp (CstrBopDiff, CstrVar 2, CstrNat 1), KdNat), KdDerivVar (tm5_ctx, CstrVar 2, KdNat), KdDerivNat (tm5_ctx, CstrNat 1, KdNat)))
      val tm6 = TmApp (tm5, tm4)
      val tm6_ctx = tm5_ctx
      val tm6_rel = (tm6_ctx, tm6, CstrExists (KdNat, CstrTypeNat (CstrVar 0)), CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrTime "0.0", CstrTime "1.0"), CstrTime "1.0"), CstrBinOp (CstrBopMult, CstrTime "7.0", CstrUnOp (CstrUopNat2Time, CstrBinOp (CstrBopDiff, CstrVar 2, CstrNat 1)))))
      val tm6_deriv = TyDerivApp (tm6_rel, tm5_deriv, tm4_deriv)
      val tm7 = TmPack (CstrVar 2, TmVar 1)
      val tm7_ctx = tm6_ctx
      val tm7_rel = (tm7_ctx, tm7, CstrExists (KdNat, CstrTypeNat (CstrVar 0)), CstrTime "0.0")
      val tm7_deriv = TyDerivPack (tm7_rel, KdDerivExists ((tm7_ctx, CstrExists (KdNat, CstrTypeNat (CstrVar 0)), KdProper), KdWfDerivNat (tm7_ctx, KdNat), KdDerivTypeNat ((BdKind KdNat :: tm7_ctx, CstrTypeNat (CstrVar 0), KdProper), KdDerivVar (tm7_ctx, CstrVar 2, KdNat))), KdDerivVar (tm7_ctx, CstrVar 2, KdNat), TyDerivNat (tm7_ctx, TmVar 1, CstrTypeNat (CstrVar 2), CstrTime "0.0"))
      val tm8 = TmPair (tm7, tm6)
      val tm8_ctx = tm7_ctx
      val tm8_rel = (tm8_ctx, tm8, CstrProd (CstrExists (KdNat, CstrTypeNat (CstrVar 0)), CstrExists (KdNat, CstrTypeNat (CstrVar 0))), CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrTime "0.0", CstrTime "1.0"), CstrTime "1.0"), CstrBinOp (CstrBopMult, CstrTime "7.0", CstrUnOp (CstrUopNat2Time, CstrBinOp (CstrBopDiff, CstrVar 2, CstrNat 1)))))
      val tm8_deriv = TyDerivPair (tm8_rel, tm7_deriv, tm6_deriv)
      val tm9 = TmApp (TmVar 4, tm8)
      val tm9_ctx = tm8_ctx
      val tm9_rel = (tm9_ctx, tm9, CstrExists (KdNat, CstrTypeNat (CstrVar 0)), CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrTime "0.0", CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrTime "0.0", CstrTime "1.0"), CstrTime "1.0"), CstrBinOp (CstrBopMult, CstrTime "7.0", CstrUnOp (CstrUopNat2Time, CstrBinOp (CstrBopDiff, CstrVar 2, CstrNat 1))))), CstrTime "1.0"), CstrTime "1.0"))
      val tm9_deriv = TyDerivApp (tm9_rel, TyDerivVar (tm9_ctx, TmVar 4, mult_ty, CstrTime "0.0"), tm8_deriv)
      val tm10 = TmCstrApp (TmVar 5, CstrVar 1)
      val tm10_ctx = List.tl tm9_ctx
      val tm10_rel = (tm10_ctx, tm10, CstrArrow (CstrTypeNat (CstrVar 1), CstrApp (bool_cstr, CstrBinOp (CstrBopEq, CstrVar 1, CstrNat 0)), CstrTime "1.0"), CstrTime "0.0")
      val tm10_deriv = TyDerivCstrApp (tm10_rel, TyDerivVar (tm10_ctx, TmVar 5, is_zero_ty, CstrTime "0.0"), KdDerivVar (tm10_ctx, CstrVar 1, KdNat))
      val tm11 = TmApp (tm10, TmVar 0)
      val tm11_ctx = tm10_ctx
      val tm11_rel = (tm11_ctx, tm11, CstrApp (bool_cstr, CstrBinOp (CstrBopEq, CstrVar 1, CstrNat 0)), CstrTime "2.0")
      val tm11_deriv = TyDerivApp (tm11_rel, tm10_deriv, TyDerivVar (tm11_ctx, TmVar 0, CstrTypeNat (CstrVar 1), CstrTime "0.0"))
      val tm12 = TmCase (tm11, tm1, tm9)
      val tm12_ctx = tm11_ctx
      val tm12_rel = (tm12_ctx, tm12, CstrExists (KdNat, CstrTypeNat (CstrVar 0)), CstrBinOp (CstrBopMult, CstrTime "7.0", CstrUnOp (CstrUopNat2Time, CstrVar 1)))
      val tm12_deriv = TyDerivCase (tm12_rel, tm11_deriv, tm1_deriv, tm9_deriv)
      val tm13 = TmAbs (CstrTypeNat (CstrVar 0), tm11)
      val tm13_ctx = List.tl tm12_ctx
      val tm13_rel = (tm13_ctx, tm13, CstrArrow (CstrTypeNat (CstrVar 0), CstrExists (KdNat, CstrTypeNat (CstrVar 0)), CstrBinOp (CstrBopMult, CstrTime "7.0", CstrUnOp (CstrUopNat2Time, CstrVar 0))), CstrTime "0.0")
      val tm13_deriv = TyDerivAbs (tm13_rel, KdDerivArrow ((tm13_ctx, CstrArrow (CstrTypeNat (CstrVar 0), CstrExists (KdNat, CstrTypeNat (CstrVar 0)), CstrBinOp (CstrBopMult, CstrTime "7.0", CstrUnOp (CstrUopNat2Time, CstrVar 0))), KdProper), KdDerivTypeNat ((tm13_ctx, CstrTypeNat (CstrVar 0), KdProper), KdDerivVar (tm13_ctx, CstrVar 0, KdNat)), KdDerivExists ((tm13_ctx, CstrExists (KdNat, CstrTypeNat (CstrVar 0)), KdProper), KdWfDerivNat (tm13_ctx, KdNat), KdDerivVar (BdKind KdNat :: tm13_ctx, CstrVar 0, KdNat)), KdDerivBinOp ((tm13_ctx, CstrBinOp (CstrBopMult, CstrTime "7.0", CstrUnOp (CstrUopNat2Time, CstrVar 0)), KdTimeFun 0), KdDerivTime (tm13_ctx, CstrTime "7.0", KdTimeFun 0), KdDerivUnOp ((tm13_ctx, CstrUnOp (CstrUopNat2Time, CstrVar 0), KdTimeFun 0), KdDerivVar (tm13_ctx, CstrVar 0, KdNat)))), tm12_deriv)
      val tm14 = TmCstrAbs (KdNat, tm13)
      val tm14_ctx = List.tl tm13_ctx
      val tm14_rel = (tm14_ctx, tm14, fac_ty, CstrTime "0.0")
      val tm14_deriv = TyDerivCstrAbs (tm14_rel, KdWfDerivNat (tm14_ctx, KdNat), tm13_deriv)
      val tm15 = TmRec (fac_ty, tm14)
      val tm15_ctx = List.tl tm14_ctx
      val tm15_rel = (tm15_ctx, tm15, fac_ty, CstrTime "0.0")
      val tm15_deriv = TyDerivRec (tm15_rel, KdDerivForall ((tm15_ctx, fac_ty, KdProper), KdWfDerivNat (tm15_ctx, KdNat), KdDerivArrow ((BdKind KdNat :: tm15_ctx, CstrArrow (CstrTypeNat (CstrVar 0), CstrExists (KdNat, CstrTypeNat (CstrVar 0)), CstrBinOp (CstrBopMult, CstrTime "7.0", CstrUnOp (CstrUopNat2Time, CstrVar 0))), KdProper), KdDerivTypeNat ((BdKind KdNat :: tm15_ctx, CstrTypeNat (CstrVar 0), KdProper), KdDerivVar (BdKind KdNat :: tm15_ctx, CstrVar 0, KdNat)), KdDerivExists ((BdKind KdNat :: tm15_ctx, CstrExists (KdNat, CstrTypeNat (CstrVar 0)), KdProper), KdWfDerivNat (BdKind KdNat :: tm15_ctx, KdNat), KdDerivVar (BdKind KdNat :: BdKind KdNat :: tm15_ctx, CstrVar 0, KdNat)), KdDerivBinOp ((BdKind KdNat :: tm15_ctx, CstrBinOp (CstrBopMult, CstrTime "7.0", CstrUnOp (CstrUopNat2Time, CstrVar 0)), KdTimeFun 0), KdDerivTime (BdKind KdNat :: tm15_ctx, CstrTime "7.0", KdTimeFun 0), KdDerivUnOp ((BdKind KdNat :: tm15_ctx, CstrUnOp (CstrUopNat2Time, CstrVar 0), KdTimeFun 0), KdDerivVar (BdKind KdNat :: tm15_ctx, CstrVar 0, KdNat))))), tm14_deriv)
      val tm15_deriv_new = DerivationPasses.ANF.normalize_derivation tm15_deriv
      val tm15_rel_new = DerivationPasses.ANF.extract_tyrel tm15_deriv_new
      val _ = println (snd (Passes.Printer.transform_term (#2 tm15_rel_new, ["mult", "minus", "is_zero"])))
    in
      0
    end
end
