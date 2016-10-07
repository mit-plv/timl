structure MicroTiMLChecker =
struct
  open MicroTiML
  open DerivationPasses
  open Passes.TermShift
  open Passes.TermSubstConstr

  exception CheckFail

  fun get_bind (ctx : context, i : int) =
    let
      val bd = List.nth (ctx, i)
    in
      case bd of
        BdType ty => BdType (shift_constr (i + 1) ty)
      | BdKind kd => BdKind (shift_kind (i + 1) kd)
    end

  fun assert b = if b then () else raise CheckFail

  fun check_kind_wellformness_derivation kdwf = true

  fun check_kinding_derivation kdderiv = true

  fun check_proping_derivation prderiv = true

  fun check_typing_derivation tyderiv =
    (case tyderiv of
      TyDerivSub ((ctx, tm, ty, ti), tyderiv1, prderiv2) =>
        let
          val _ = assert (check_typing_derivation tyderiv1)
          val _ = assert (check_proping_derivation prderiv2)
          val tyrel1 = ANF.extract_tyrel tyderiv1
          val prrel2 = ANF.extract_prrel prderiv2
          val _ = assert (#1 tyrel1 = ctx)
          val _ = assert (#2 tyrel1 = tm)
          val _ = assert (#3 tyrel1 = ty)
          val _ = assert (#1 prrel2 = ctx)
          val _ = assert (#2 prrel2 = PrBinRel (PrRelLe, #4 tyrel1, ti))
        in
          true
        end
    | TyDerivVar (ctx, TmVar x, ty, CstrTime "0.0") =>
        let
          val _ = assert (x >= 0 andalso x < List.length ctx)
          val _ = assert (get_bind (ctx, x) = BdType ty)
        in
          true
        end
    | TyDerivInt (ctx, TmInt i, CstrTypeInt, CstrTime "0.0") => true
    | TyDerivNat (ctx, TmNat n, CstrTypeNat (CstrNat m), CstrTime "0.0") =>
        let
          val _ = assert (n = m)
        in
          true
        end
    | TyDerivUnit (ctx, TmUnit, CstrTypeUnit, CstrTime "0.0") => true
    | TyDerivApp ((ctx, TmApp (tm1, tm2), ty, CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, ti1, ti2), CstrTime "1.0"), ti3)), tyderiv1, tyderiv2) =>
        let
          val _ = assert (check_typing_derivation tyderiv1)
          val _ = assert (check_typing_derivation tyderiv2)
          val tyrel1 = ANF.extract_tyrel tyderiv1
          val tyrel2 = ANF.extract_tyrel tyderiv2
          val _ = assert (#1 tyrel1 = ctx)
          val _ = assert (#2 tyrel1 = tm1)
          val _ = assert (#3 tyrel1 = CstrArrow (#3 tyrel2, ty, ti3))
          val _ = assert (#4 tyrel1 = ti1)
          val _ = assert (#1 tyrel2 = ctx)
          val _ = assert (#2 tyrel2 = tm2)
          val _ = assert (#4 tyrel2 = ti2)
        in
          true
        end
    | TyDerivAbs ((ctx, TmAbs (cstr1, tm2), ty, CstrTime "0.0"), kdderiv1, tyderiv2) =>
        let
          val _ = assert (check_kinding_derivation kdderiv1)
          val _ = assert (check_typing_derivation tyderiv2)
          val kdrel1 = ANF.extract_kdrel kdderiv1
          val tyrel2 = ANF.extract_tyrel tyderiv2
          val _ = assert (#1 kdrel1 = ctx)
          val _ = assert (#2 kdrel1 = cstr1)
          val _ = assert (#3 kdrel1 = KdProper)
          val _ = assert (#1 tyrel2 = BdType cstr1 :: ctx)
          val _ = assert (#2 tyrel2 = tm2)
          val _ = assert (ty = CstrArrow (cstr1, shift_constr ~1 (#3 tyrel2), shift_constr ~1 (#4 tyrel2)))
        in
          true
        end
    | TyDerivRec ((ctx, TmRec (cstr1, tm2), ty, CstrTime "0.0"), kdderiv1, tyderiv2) =>
        let
          val _ = assert (check_kinding_derivation kdderiv1)
          val _ = assert (check_typing_derivation tyderiv2)
          val kdrel1 = ANF.extract_kdrel kdderiv1
          val tyrel2 = ANF.extract_tyrel tyderiv2
          val _ = assert (cstr1 = ty)
          val _ = assert (#1 kdrel1 = ctx)
          val _ = assert (#2 kdrel1 = cstr1)
          val _ = assert (#3 kdrel1 = KdProper)
          val _ = assert (#1 tyrel2 = BdType cstr1 :: ctx)
          val _ = assert (#2 tyrel2 = tm2)
          val _ = assert (#3 tyrel2 = shift_constr 1 cstr1)
          val _ = assert (#4 tyrel2 = CstrTime "0.0")
        in
          true
        end
    | TyDerivPair ((ctx, TmPair (tm1, tm2), CstrProd (ty1, ty2), CstrBinOp (CstrBopAdd, ti1, ti2)), tyderiv1, tyderiv2) =>
        let
          val _ = assert (check_typing_derivation tyderiv1)
          val _ = assert (check_typing_derivation tyderiv2)
          val tyrel1 = ANF.extract_tyrel tyderiv1
          val tyrel2 = ANF.extract_tyrel tyderiv2
          val _ = assert (#1 tyrel1 = ctx)
          val _ = assert (#2 tyrel1 = tm1)
          val _ = assert (#3 tyrel1 = ty1)
          val _ = assert (#4 tyrel1 = ti1)
          val _ = assert (#1 tyrel2 = ctx)
          val _ = assert (#2 tyrel2 = tm2)
          val _ = assert (#3 tyrel2 = ty2)
          val _ = assert (#4 tyrel2 = ti2)
        in
          true
        end
    | TyDerivFst ((ctx, TmFst tm1, ty, ti), tyderiv1) =>
        let
          val _ = assert (check_typing_derivation tyderiv1)
          val tyrel1 = ANF.extract_tyrel tyderiv1
          val _ = assert (#1 tyrel1 = ctx)
          val _ = assert (#2 tyrel1 = tm1)
          val _ = assert (case (#3 tyrel1) of CstrProd (ty1, ty2) => ty = ty1 | _ => false)
          val _ = assert (#4 tyrel1 = ti)
        in
          true
        end
    | TyDerivSnd ((ctx, TmSnd tm1, ty, ti), tyderiv1) =>
        let
          val _ = assert (check_typing_derivation tyderiv1)
          val tyrel1 = ANF.extract_tyrel tyderiv1
          val _ = assert (#1 tyrel1 = ctx)
          val _ = assert (#2 tyrel1 = tm1)
          val _ = assert (case (#3 tyrel1) of CstrProd (ty1, ty2) => ty = ty2 | _ => false)
          val _ = assert (#4 tyrel1 = ti)
        in
          true
        end
    | TyDerivInLeft ((ctx, TmInLeft tm1, CstrSum (ty1, ty2), ti), kdderiv1, tyderiv2) =>
        let
          val _ = assert (check_kinding_derivation kdderiv1)
          val _ = assert (check_typing_derivation tyderiv2)
          val kdrel1 = ANF.extract_kdrel kdderiv1
          val tyrel2 = ANF.extract_tyrel tyderiv2
          val _ = assert (#1 kdrel1 = ctx)
          val _ = assert (#2 kdrel1 = ty2)
          val _ = assert (#3 kdrel1 = KdProper)
          val _ = assert (#1 tyrel2 = ctx)
          val _ = assert (#2 tyrel2 = tm1)
          val _ = assert (#3 tyrel2 = ty1)
          val _ = assert (#4 tyrel2 = ti)
        in
          true
        end
    | TyDerivInRight ((ctx, TmInRight tm1, CstrSum (ty1, ty2), ti), kdderiv1, tyderiv2) =>
        let
          val _ = assert (check_kinding_derivation kdderiv1)
          val _ = assert (check_typing_derivation tyderiv2)
          val kdrel1 = ANF.extract_kdrel kdderiv1
          val tyrel2 = ANF.extract_tyrel tyderiv2
          val _ = assert (#1 kdrel1 = ctx)
          val _ = assert (#2 kdrel1 = ty1)
          val _ = assert (#3 kdrel1 = KdProper)
          val _ = assert (#1 tyrel2 = ctx)
          val _ = assert (#2 tyrel2 = tm1)
          val _ = assert (#3 tyrel2 = ty2)
          val _ = assert (#4 tyrel2 = ti)
        in
          true
        end
    | TyDerivCase ((ctx, TmCase (tm1, tm2, tm3), ty, CstrBinOp (CstrBopAdd, ti1, CstrBinOp (CstrBopMax, ti2, ti3))), tyderiv1, tyderiv2, tyderiv3) =>
        let
          val _ = assert (check_typing_derivation tyderiv1)
          val _ = assert (check_typing_derivation tyderiv2)
          val _ = assert (check_typing_derivation tyderiv3)
          val tyrel1 = ANF.extract_tyrel tyderiv1
          val tyrel2 = ANF.extract_tyrel tyderiv2
          val tyrel3 = ANF.extract_tyrel tyderiv3
          val _ = case (#3 tyrel1) of
                    CstrSum (ty1, ty2) =>
                      let
                        val _ = assert (#1 tyrel1 = ctx)
                        val _ = assert (#2 tyrel1 = tm1)
                        val _ = assert (#4 tyrel1 = ti1)
                        val _ = assert (#1 tyrel2 = BdType ty1 :: ctx)
                        val _ = assert (#2 tyrel2 = tm2)
                        val _ = assert (#3 tyrel2 = shift_constr 1 ty)
                        val _ = assert (#4 tyrel2 = shift_constr 1 ti2)
                        val _ = assert (#1 tyrel3 = BdType ty2 :: ctx)
                        val _ = assert (#2 tyrel3 = tm3)
                        val _ = assert (#3 tyrel3 = shift_constr 1 ty)
                        val _ = assert (#4 tyrel3 = shift_constr 1 ti3)
                      in
                        ()
                      end
                  | _ => assert false
        in
          true
        end
    | TyDerivFold ((ctx, TmFold tm1, ty, ti), kdderiv1, tyderiv2) =>
        let
          val _ = assert (check_kinding_derivation kdderiv1)
          val _ = assert (check_typing_derivation tyderiv2)
          val kdrel1 = ANF.extract_kdrel kdderiv1
          val tyrel2 = ANF.extract_tyrel tyderiv2
          fun unfold_app ty1 rands =
            case ty1 of
              CstrApp (cstr1, cstr2) => unfold_app cstr1 (cstr2 :: rands)
            | _ => (ty1, rands)
          fun fold_app ty1 rands =
            case rands of
              [] => ty1
            | hd :: tl => fold_app (CstrApp (ty1, hd)) tl
          val (ty1, rands) = unfold_app ty []
          val _ = case ty1 of
                    CstrRec (kd1, ty_body) =>
                      let
                        val _ = assert (#1 kdrel1 = ctx)
                        val _ = assert (#2 kdrel1 = ty)
                        val _ = assert (#3 kdrel1 = KdProper)
                        val _ = assert (#1 tyrel2 = ctx)
                        val _ = assert (#2 tyrel2 = tm1)
                        val _ = assert (#3 tyrel2 = subst_constr_in_constr_top ty1 ty_body)
                        val _ = assert (#4 tyrel2 = ti)
                      in
                        ()
                      end
                  | _ => assert false
        in
          true
        end
    | TyDerivUnfold ((ctx, TmUnfold tm1, ty, ti), tyderiv1) =>
        let
          val _ = assert (check_typing_derivation tyderiv1)
          val tyrel1 = ANF.extract_tyrel tyderiv1
          fun unfold_app ty1 rands =
            case ty1 of
              CstrApp (cstr1, cstr2) => unfold_app cstr1 (cstr2 :: rands)
            | _ => (ty1, rands)
          fun fold_app ty1 rands =
            case rands of
              [] => ty1
            | hd :: tl => fold_app (CstrApp (ty1, hd)) tl
          val (ty1, rands) = unfold_app (#3 tyrel1) []
          val _ =
            case ty1 of
              CstrRec (kd1, ty_body) =>
                let
                  val _ = assert (#1 tyrel1 = ctx)
                  val _ = assert (#2 tyrel1 = tm1)
                  val _ = assert (#4 tyrel1 = ti)
                  val _ = assert (ty = fold_app (subst_constr_in_constr_top ty1 ty_body) rands)
                in
                  ()
                end
            | _ => assert false
        in
          true
        end
    | TyDerivPack ((ctx, TmPack (cstr1, tm2), ty as CstrExists (kd1, ty1), ti), kdderiv1, kdderiv2, tyderiv3) =>
        let
          val _ = assert (check_kinding_derivation kdderiv1)
          val _ = assert (check_kinding_derivation kdderiv2)
          val _ = assert (check_typing_derivation tyderiv3)
          val kdrel1 = ANF.extract_kdrel kdderiv1
          val kdrel2 = ANF.extract_kdrel kdderiv2
          val tyrel3 = ANF.extract_tyrel tyderiv3
          val _ = assert (#1 kdrel1 = ctx)
          val _ = assert (#2 kdrel1 = ty)
          val _ = assert (#3 kdrel1 = KdProper)
          val _ = assert (#1 kdrel2 = ctx)
          val _ = assert (#2 kdrel2 = cstr1)
          val _ = assert (#3 kdrel2 = kd1)
          val _ = assert (#1 tyrel3 = ctx)
          val _ = assert (#2 tyrel3 = tm2)
          val _ = assert (#3 tyrel3 = subst_constr_in_constr_top cstr1 ty1)
          val _ = assert (#4 tyrel3 = ti)
        in
          true
        end
    | TyDerivUnpack ((ctx, TmUnpack (tm1, tm2), ty2, CstrBinOp (CstrBopAdd, ti1, ti2)), tyderiv1, tyderiv2) =>
        let
          val _ = assert (check_typing_derivation tyderiv1)
          val _ = assert (check_typing_derivation tyderiv2)
          val tyrel1 = ANF.extract_tyrel tyderiv1
          val tyrel2 = ANF.extract_tyrel tyderiv2
          val _ =
            case (#3 tyrel1) of
              CstrExists (kd1, ty1) =>
                let
                  val _ = assert (#1 tyrel1 = ctx)
                  val _ = assert (#2 tyrel1 = tm1)
                  val _ = assert (#4 tyrel1 = ti1)
                  val _ = assert (#1 tyrel2 = BdType ty1 :: BdKind kd1 :: ctx)
                  val _ = assert (#2 tyrel2 = tm2)
                  val _ = assert (#3 tyrel2 = shift_constr 2 ty2)
                  val _ = assert (#4 tyrel2 = shift_constr 2 ti2)
                in
                  ()
                end
            | _ => assert false
        in
          true
        end
    | TyDerivCstrAbs ((ctx, TmCstrAbs (kd1, tm2), CstrForall (kd1', ty), CstrTime "0.0"), kdwf1, tyderiv2) =>
        let
          val _ = assert (check_kind_wellformness_derivation kdwf1)
          val _ = assert (check_typing_derivation tyderiv2)
          val kdwfrel1 = ANF.extract_kdwfrel kdwf1
          val tyrel2 = ANF.extract_tyrel tyderiv2
          val _ = assert (kd1 = kd1')
          val _ = assert (#1 kdwfrel1 = ctx)
          val _ = assert (#2 kdwfrel1 = kd1)
          val _ = assert (#1 tyrel2 = BdKind kd1 :: ctx)
          val _ = assert (#2 tyrel2 = tm2)
          val _ = assert (#3 tyrel2 = ty)
          val _ = assert (#4 tyrel2 = CstrTime "0.0")
        in
          true
        end
    | TyDerivCstrApp ((ctx, TmCstrApp (tm1, cstr2), ty, ti), tyderiv1, kdderiv2) =>
        let
          val _ = assert (check_typing_derivation tyderiv1)
          val _ = assert (check_kinding_derivation kdderiv2)
          val tyrel1 = ANF.extract_tyrel tyderiv1
          val kdrel2 = ANF.extract_kdrel kdderiv2
          val _ =
            case (#3 tyrel1) of
              CstrForall (kd1, ty_body) =>
                let
                  val _ = assert (#1 tyrel1 = ctx)
                  val _ = assert (#2 tyrel1 = tm1)
                  val _ = assert (#4 tyrel1 = ti)
                  val _ = assert (#1 kdrel2 = ctx)
                  val _ = assert (#2 kdrel2 = cstr2)
                  val _ = assert (#3 kdrel2 = kd1)
                  val _ = assert (ty = subst_constr_in_constr_top cstr2 ty_body)
                in
                  ()
                end
            | _ => assert false
        in
          true
        end
    | TyDerivBinOp ((ctx, TmBinOp (bop, tm1, tm2), ty, CstrBinOp (CstrBopAdd, ti1, ti2)), tyderiv1, tyderiv2) =>
        let
          val _ = assert (check_typing_derivation tyderiv1)
          val _ = assert (check_typing_derivation tyderiv2)
          val tyrel1 = ANF.extract_tyrel tyderiv1
          val tyrel2 = ANF.extract_tyrel tyderiv2
          val _ = assert (#1 tyrel1 = ctx)
          val _ = assert (#2 tyrel1 = tm1)
          val _ = assert ((#3 tyrel1, #3 tyrel2) = #2 (ANF.term_bin_op_to_constr bop))
          val _ = assert (#4 tyrel1 = ti1)
          val _ = assert (#1 tyrel2 = ctx)
          val _ = assert (#2 tyrel2 = tm2)
          val _ = assert (#4 tyrel2 = ti2)
          val _ = assert (ty = #1 (ANF.term_bin_op_to_constr bop))
        in
          true
        end
    | TyDerivArrayNew ((ctx, TmArrayNew (tm1, tm2), CstrTypeArray (cstr1, cstr2), CstrBinOp (CstrBopAdd, ti1, ti2)), tyderiv1, tyderiv2) =>
        let
          val _ = assert (check_typing_derivation tyderiv1)
          val _ = assert (check_typing_derivation tyderiv2)
          val tyrel1 = ANF.extract_tyrel tyderiv1
          val tyrel2 = ANF.extract_tyrel tyderiv2
          val _ = assert (#1 tyrel1 = ctx)
          val _ = assert (#2 tyrel1 = tm1)
          val _ = assert (#3 tyrel1 = CstrTypeNat cstr2)
          val _ = assert (#4 tyrel1 = ti1)
          val _ = assert (#1 tyrel2 = ctx)
          val _ = assert (#2 tyrel2 = tm2)
          val _ = assert (#3 tyrel2 = cstr1)
          val _ = assert (#4 tyrel2 = ti2)
        in
          true
        end
    | TyDerivArrayGet ((ctx, TmArrayGet (tm1, tm2), ty, CstrBinOp (CstrBopAdd, ti1, ti2)), tyderiv1, tyderiv2, prderiv3) =>
        let
          val _ = assert (check_typing_derivation tyderiv1)
          val _ = assert (check_typing_derivation tyderiv2)
          val _ = assert (check_proping_derivation prderiv3)
          val tyrel1 = ANF.extract_tyrel tyderiv1
          val tyrel2 = ANF.extract_tyrel tyderiv2
          val prrel3 = ANF.extract_prrel prderiv3
          val _ =
            case (#3 tyrel1, #3 tyrel2) of
              (CstrTypeArray (ty', j1), CstrTypeNat j2) =>
                let
                  val _ = assert (ty' = ty)
                  val _ = assert (#1 tyrel1 = ctx)
                  val _ = assert (#2 tyrel1 = tm1)
                  val _ = assert (#4 tyrel1 = ti1)
                  val _ = assert (#1 tyrel2 = ctx)
                  val _ = assert (#2 tyrel2 = tm2)
                  val _ = assert (#4 tyrel2 = ti2)
                  val _ = assert (#1 prrel3 = ctx)
                  val _ = assert (#2 prrel3 = PrBinRel (PrRelLt, j2, j1))
                in
                  ()
                end
            | _ => assert false
        in
          true
        end
    | TyDerivArrayPut ((ctx, TmArrayPut (tm1, tm2, tm3), CstrTypeUnit, CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, ti1, ti2), ti3)), tyderiv1, tyderiv2, prderiv3, tyderiv4) =>
        let
          val _ = assert (check_typing_derivation tyderiv1)
          val _ = assert (check_typing_derivation tyderiv2)
          val _ = assert (check_proping_derivation prderiv3)
          val _ = assert (check_typing_derivation tyderiv4)
          val tyrel1 = ANF.extract_tyrel tyderiv1
          val tyrel2 = ANF.extract_tyrel tyderiv2
          val prrel3 = ANF.extract_prrel prderiv3
          val tyrel4 = ANF.extract_tyrel tyderiv4
          val _ =
            case (#3 tyrel1, #3 tyrel2) of
              (CstrTypeArray (ty, j1), CstrTypeNat j2) =>
                let
                  val _ = assert (#1 tyrel1 = ctx)
                  val _ = assert (#2 tyrel1 = tm1)
                  val _ = assert (#4 tyrel1 = ti1)
                  val _ = assert (#1 tyrel2 = ctx)
                  val _ = assert (#2 tyrel2 = tm2)
                  val _ = assert (#4 tyrel2 = ti2)
                  val _ = assert (#1 tyrel4 = ctx)
                  val _ = assert (#2 tyrel4 = tm3)
                  val _ = assert (#3 tyrel4 = ty)
                  val _ = assert (#4 tyrel4 = ti3)
                  val _ = assert (#1 prrel3 = ctx)
                  val _ = assert (#2 prrel3 = PrBinRel (PrRelLt, j2, j1))
                in
                  ()
                end
            | _ => assert false
        in
          true
        end
    | TyDerivLet ((ctx, TmLet (tm1, tm2), ty2, CstrBinOp (CstrBopAdd, ti1, ti2)), tyderiv1, tyderiv2) =>
        let
          val _ = assert (check_typing_derivation tyderiv1)
          val _ = assert (check_typing_derivation tyderiv2)
          val tyrel1 = ANF.extract_tyrel tyderiv1
          val tyrel2 = ANF.extract_tyrel tyderiv2
          val _ = assert (#1 tyrel1 = ctx)
          val _ = assert (#2 tyrel1 = tm1)
          val _ = assert (#4 tyrel1 = ti1)
          val _ = assert (#1 tyrel2 = BdType (#3 tyrel1) :: ctx)
          val _ = assert (#2 tyrel2 = tm2)
          val _ = assert (#3 tyrel2 = shift_constr 1 ty2)
          val _ = assert (#4 tyrel2 = shift_constr 1 ti2)
        in
          true
        end
    | TyDerivNever ((ctx, TmNever, ty, CstrTime "0.0"), kdderiv1, prderiv2) =>
        let
          val _ = assert (check_kinding_derivation kdderiv1)
          val _ = assert (check_proping_derivation prderiv2)
          val kdrel1 = ANF.extract_kdrel kdderiv1
          val prrel2 = ANF.extract_prrel prderiv2
          val _ = assert (#1 kdrel1 = ctx)
          val _ = assert (#2 kdrel1 = ty)
          val _ = assert (#3 kdrel1 = KdProper)
          val _ = assert (#1 prrel2 = ctx)
          val _ = assert (#2 prrel2 = PrBot)
        in
          true
        end
    | _ => let val _ = assert false in true end)
      handle CheckFail => let val _ = println (snd (Passes.Printer.transform_term (#2 (ANF.extract_tyrel tyderiv), List.mapi (fn (i, _) => "%orz" ^ (str_int i)) (#1 (ANF.extract_tyrel tyderiv))))) in false end
end
