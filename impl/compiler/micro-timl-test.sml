structure MicroTiMLTest =
struct
  open Util
  open MicroTiML

  fun main (prog_name : string, args : string list) : int =
    let
      val list_cstr = CstrRec (KdArrow (KdProper, KdArrow (KdNat, KdProper)), CstrAbs (KdProper, CstrAbs (KdNat, CstrSum (CstrExists (KdSubset (KdUnit, PrBinRel (PrRelEq, CstrVar 1, CstrNat 0)), CstrTypeUnit), CstrExists (KdSubset (KdNat, PrBinRel (PrRelEq, CstrVar 1, CstrBinOp (CstrBopAdd, CstrVar 0, CstrNat 1))), CstrProd (CstrVar 2, CstrApp (CstrApp (CstrVar 3, CstrVar 2), CstrVar 0)))))))
      val hd_tm = TmCstrAbs (KdProper, TmCstrAbs (KdSubset (KdNat, PrBinRel (PrRelGt, CstrVar 0, CstrNat 0)), TmAbs (CstrApp (CstrApp (list_cstr, CstrVar 1), CstrVar 0), TmCase (TmUnfold (TmVar 0), TmNever, TmFst (TmVar 0)))))
      val _ = println (Passes.Printer.str_constr list_cstr)
      (*val _ = println (Passes.Printer.str_term (Passes.ANF.normalize_term hd_tm))*)
      val fac_tm = TmRec (CstrArrow (CstrExists (KdNat, CstrTypeNat (CstrVar 0)), CstrExists (KdNat, CstrTypeNat (CstrVar 0)), CstrTime "1.0"), TmAbs (CstrExists (KdNat, CstrTypeNat (CstrVar 0)), TmUnpack (TmVar 0, TmCase (TmApp (TmCstrApp (TmVar 6, CstrVar 1), TmVar 0), TmPack (CstrNat 1, TmNat 1), TmApp (TmVar 5, TmPair (TmVar 3, TmApp (TmVar 4, TmPack (CstrBinOp (CstrBopDiff, CstrVar 2, CstrNat 1), TmApp (TmCstrApp (TmCstrApp (TmVar 6, CstrVar 2), CstrNat 1), TmPair (TmVar 1, TmNat 1))))))))))
      val _ = println (snd (Passes.Printer.transform_term (Passes.ANF.normalize_term fac_tm, ["mult", "minus", "is_zero"])))
      val tmp_tm = TmLet (TmArrayNew (TmNat 5, TmInt 0), TmApp (TmVar 1, TmArrayPut (TmVar 0, TmNat 2, TmInt 3)))
      val _ = println (snd (Passes.Printer.transform_term (Passes.ANF.normalize_term tmp_tm, ["id"])))
    in
      0
    end
end
