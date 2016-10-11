structure MicroTiMLChecker =
struct
  open MicroTiML
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

  fun check_type_equivalence_derivation tyeq =
    (case tyeq of
       TyEqDerivAssume (ctx, ty1, ty2) => true
     | _ =>
         let
           val _ = assert false
         in
           true
         end)
           handle CheckFail => false

  fun check_kind_wellformness_derivation kdwf =
    (case kdwf of
       KdWfDerivAssume (ctx, kd) => true
     | KdWfDerivNat (ctx, KdNat) => true
     | KdWfDerivBool (ctx, KdBool) => true
     | KdWfDerivUnit (ctx, KdUnit) => true
     | KdWfDerivTimeFun (ctx, KdTimeFun _) => true
     | KdWfDerivProper (ctx, KdProper) => true
     | KdWfDerivArrow ((ctx, KdArrow (kd1, kd2)), kdwf1, kdwf2) =>
         let
           val _ = assert (check_kind_wellformness_derivation kdwf1)
           val _ = assert (check_kind_wellformness_derivation kdwf2)
           val kdwfrel1 = extract_kdwfrel kdwf1
           val kdwfrel2 = extract_kdwfrel kdwf2
           val _ = assert (#1 kdwfrel1 = ctx)
           val _ = assert (#2 kdwfrel1 = kd1)
           val _ = assert (#1 kdwfrel2 = ctx)
           val _ = assert (#2 kdwfrel2 = kd2)
         in
           true
         end
     | KdWfDerivSubset ((ctx, KdSubset (kd1, pr2)), kdwf1, prwf2) =>
         let
           val _ = assert (check_kind_wellformness_derivation kdwf1)
           val _ = assert (check_prop_wellformness_derivation prwf2)
           val kdwfrel1 = extract_kdwfrel kdwf1
           val prwfrel2 = extract_prwfrel prwf2
           val _ = assert (#1 kdwfrel1 = ctx)
           val _ = assert (#2 kdwfrel1 = kd1)
           val _ = assert (#1 prwfrel2 = BdKind kd1 :: ctx)
           val _ = assert (#2 prwfrel2 = pr2)
         in
           true
         end
     | _ => let val _ = assert false in true end)
           handle CheckFail => false

  and check_prop_wellformness_derivation prwf =
    (case prwf of
       PrWfDerivTop (ctx, PrTop) => true
     | PrWfDerivBot (ctx, PrBot) => true
     | PrWfDerivBinConn ((ctx, PrBinConn (conn, pr1, pr2)), prwf1, prwf2) =>
         let
           val _ = assert (check_prop_wellformness_derivation prwf1)
           val _ = assert (check_prop_wellformness_derivation prwf2)
           val prwfrel1 = extract_prwfrel prwf1
           val prwfrel2 = extract_prwfrel prwf2
           val _ = assert (#1 prwfrel1 = ctx)
           val _ = assert (#2 prwfrel1 = pr1)
           val _ = assert (#1 prwfrel2 = ctx)
           val _ = assert (#2 prwfrel2 = pr2)
         in
           true
         end
     | PrWfDerivNot ((ctx, PrNot pr1), prwf1) =>
         let
           val _ = assert (check_prop_wellformness_derivation prwf1)
           val prwfrel1 = extract_prwfrel prwf1
           val _ = assert (#1 prwfrel1 = ctx)
           val _ = assert (#2 prwfrel1 = pr1)
         in
           true
         end
     | PrWfDerivForall ((ctx, PrForall (kd1, pr2)), kdwf1, prwf2) =>
         let
           val _ = assert (check_kind_wellformness_derivation kdwf1)
           val _ = assert (check_prop_wellformness_derivation prwf2)
           val kdwfrel1 = extract_kdwfrel kdwf1
           val prwfrel2 = extract_prwfrel prwf2
           val _ = assert (#1 kdwfrel1 = ctx)
           val _ = assert (#2 kdwfrel1 = kd1)
           val _ = assert (#1 prwfrel2 = BdKind kd1 :: ctx)
           val _ = assert (#2 prwfrel2 = pr2)
         in
           true
         end
     | PrWfDerivExists ((ctx, PrExists (kd1, pr2)), kdwf1, prwf2) =>
         let
           val _ = assert (check_kind_wellformness_derivation kdwf1)
           val _ = assert (check_prop_wellformness_derivation prwf2)
           val kdwfrel1 = extract_kdwfrel kdwf1
           val prwfrel2 = extract_prwfrel prwf2
           val _ = assert (#1 kdwfrel1 = ctx)
           val _ = assert (#2 kdwfrel1 = kd1)
           val _ = assert (#1 prwfrel2 = BdKind kd1 :: ctx)
           val _ = assert (#2 prwfrel2 = pr2)
         in
           true
         end
     | PrWfDerivBinRel ((ctx, PrBinRel (rel, cstr1, cstr2)), kdderiv1, kdderiv2) =>
         let
           val _ = assert (check_kinding_derivation kdderiv1)
           val _ = assert (check_kinding_derivation kdderiv2)
           val kdrel1 = extract_kdrel kdderiv1
           val kdrel2 = extract_kdrel kdderiv2
           val _ = assert (#1 kdrel1 = ctx)
           val _ = assert (#2 kdrel1 = cstr1)
           val _ = assert (#1 kdrel2 = ctx)
           val _ = assert (#2 kdrel2 = cstr2)
           val _ =
             case rel of
               PrRelBigO =>
                 (case (#3 kdrel1, #3 kdrel2) of
                   (KdTimeFun n1, KdTimeFun n2) => assert (n1 = n2)
                  | _ => assert false)
             | _ => assert (List.exists (fn x => x = (#3 kdrel1, #3 kdrel2)) (prop_bin_rel_to_kind rel))
         in
           true
         end
     | _ =>
         let
           val _ = assert false
         in
           true
         end)
           handle CheckFail => false

  and check_kinding_derivation kdderiv =
    (case kdderiv of
       KdDerivAssume (ctx, cstr, kd) => true
     | KdDerivRefine ((ctx, cstr, KdSubset (kd1, pr2)), kdderiv1, prderiv2) =>
         let
           val _ = assert (check_kinding_derivation kdderiv1)
           val _ = assert (check_proping_derivation prderiv2)
           val kdrel1 = extract_kdrel kdderiv1
           val prrel2 = extract_prrel prderiv2
           val _ = assert (#1 kdrel1 = ctx)
           val _ = assert (#2 kdrel1 = cstr)
           val _ = assert (#3 kdrel1 = kd1)
           val _ = assert (#1 prrel2 = BdKind kd1 :: ctx)
           val _ = assert (#2 prrel2 = pr2)
         in
           true
         end
     | KdDerivBase ((ctx, cstr, kd), kdderiv1) =>
         let
           val _ = assert (check_kinding_derivation kdderiv1)
           val kdrel1 = extract_kdrel kdderiv1
           val _ = assert (#1 kdrel1 = ctx)
           val _ = assert (#2 kdrel1 = cstr)
           fun inner_most kd =
             case kd of
               KdSubset (kd, _) => inner_most kd
             | _ => kd
           val _ = assert ((inner_most (#3 kdrel1)) = kd)
         in
           true
         end
     | KdDerivVar (ctx, CstrVar a, kd) =>
         let
           val _ = assert (a >= 0 andalso a < List.length ctx)
           val _ = assert (get_bind (ctx, a) = BdKind kd)
         in
           true
         end
     | KdDerivNat (ctx, CstrNat _, KdNat) => true
     | KdDerivTime (ctx, CstrTime _, KdTimeFun 0) => true
     | KdDerivUnit (ctx, CstrUnit, KdUnit) => true
     | KdDerivTrue (ctx, CstrTrue, KdBool) => true
     | KdDerivFalse (ctx, CstrFalse, KdBool) => true
     | KdDerivUnOp ((ctx, CstrUnOp (uop, cstr1), kd), kdderiv1) =>
         let
           val _ = assert (check_kinding_derivation kdderiv1)
           val kdrel1 = extract_kdrel kdderiv1
           val _ = assert (#1 kdrel1 = ctx)
           val _ = assert (#2 kdrel1 = cstr1)
           val (kdout, kdin) : kind * kind = cstr_un_op_to_kind uop
           val _ = assert (kd = kdout)
           val _ = assert (#3 kdrel1 = kdin)
         in
           true
         end
     | KdDerivBinOp ((ctx, CstrBinOp (bop, cstr1, cstr2), kd), kdderiv1, kdderiv2) =>
         let
           val _ = assert (check_kinding_derivation kdderiv1)
           val _ = assert (check_kinding_derivation kdderiv2)
           val kdrel1 = extract_kdrel kdderiv1
           val kdrel2 = extract_kdrel kdderiv2
           val _ = assert (#1 kdrel1 = ctx)
           val _ = assert (#2 kdrel1 = cstr1)
           val _ = assert (#1 kdrel2 = ctx)
           val _ = assert (#2 kdrel2 = cstr2)
           val _ =
             case bop of
               CstrBopTimeApp =>
                 let
                   val _ =
                     case (#3 kdrel1, #3 kdrel2, kd) of
                       (KdTimeFun n1, KdTimeFun 0, KdTimeFun n2) =>
                         let
                           val _ = assert (n2 + 1 = n1)
                         in
                           ()
                         end
                     | _ => assert false
                 in
                   ()
                 end
             | _ => assert (List.exists (fn (x : kind * (kind * kind)) => x = (kd, (#3 kdrel1, #3 kdrel2))) (cstr_bin_op_to_kind bop))
         in
           true
         end
     | KdDerivIte ((ctx, CstrIte (cstr1, cstr2, cstr3), kd), kdderiv1, kdderiv2, kdderiv3) =>
         let
           val _ = assert (check_kinding_derivation kdderiv1)
           val _ = assert (check_kinding_derivation kdderiv2)
           val _ = assert (check_kinding_derivation kdderiv3)
           val kdrel1 = extract_kdrel kdderiv1
           val kdrel2 = extract_kdrel kdderiv2
           val kdrel3 = extract_kdrel kdderiv3
           val _ = assert (#1 kdrel1 = ctx)
           val _ = assert (#2 kdrel1 = cstr1)
           val _ = assert (#3 kdrel1 = KdBool)
           val _ = assert (#1 kdrel2 = ctx)
           val _ = assert (#2 kdrel2 = cstr2)
           val _ = assert (#3 kdrel2 = kd)
           val _ = assert (#1 kdrel3 = ctx)
           val _ = assert (#2 kdrel3 = cstr3)
           val _ = assert (#3 kdrel3 = kd)
         in
           true
         end
     | KdDerivTimeAbs ((ctx, CstrTimeAbs cstr1, KdTimeFun n), kdderiv1) =>
         let
           val _ = assert (check_kinding_derivation kdderiv1)
           val kdrel1 = extract_kdrel kdderiv1
           val _ = assert (#1 kdrel1 = BdKind (KdTimeFun 0) :: ctx)
           val _ = assert (#2 kdrel1 = cstr1)
           val _ =
             case (#3 kdrel1) of
               KdTimeFun n1 => assert (n1 + 1 = n)
             | _ => assert false
         in
           true
         end
     | KdDerivProd ((ctx, CstrProd (cstr1, cstr2), KdProper), kdderiv1, kdderiv2) =>
         let
           val _ = assert (check_kinding_derivation kdderiv1)
           val _ = assert (check_kinding_derivation kdderiv2)
           val kdrel1 = extract_kdrel kdderiv1
           val kdrel2 = extract_kdrel kdderiv2
           val _ = assert (#1 kdrel1 = ctx)
           val _ = assert (#2 kdrel1 = cstr1)
           val _ = assert (#3 kdrel1 = KdProper)
           val _ = assert (#1 kdrel2 = ctx)
           val _ = assert (#2 kdrel2 = cstr2)
           val _ = assert (#3 kdrel2 = KdProper)
         in
           true
         end
     | KdDerivSum ((ctx, CstrSum (cstr1, cstr2), KdProper), kdderiv1, kdderiv2) =>
         let
           val _ = assert (check_kinding_derivation kdderiv1)
           val _ = assert (check_kinding_derivation kdderiv2)
           val kdrel1 = extract_kdrel kdderiv1
           val kdrel2 = extract_kdrel kdderiv2
           val _ = assert (#1 kdrel1 = ctx)
           val _ = assert (#2 kdrel1 = cstr1)
           val _ = assert (#3 kdrel1 = KdProper)
           val _ = assert (#1 kdrel2 = ctx)
           val _ = assert (#2 kdrel2 = cstr2)
           val _ = assert (#3 kdrel2 = KdProper)
         in
           true
         end
     | KdDerivArrow ((ctx, CstrArrow (ty1, ty2, ti), KdProper), kdderiv1, kdderiv2, kdderiv3) =>
         let
           val _ = assert (check_kinding_derivation kdderiv1)
           val _ = assert (check_kinding_derivation kdderiv2)
           val _ = assert (check_kinding_derivation kdderiv3)
           val kdrel1 = extract_kdrel kdderiv1
           val kdrel2 = extract_kdrel kdderiv2
           val kdrel3 = extract_kdrel kdderiv3
           val _ = assert (#1 kdrel1 = ctx)
           val _ = assert (#2 kdrel1 = ty1)
           val _ = assert (#3 kdrel1 = KdProper)
           val _ = assert (#1 kdrel2 = ctx)
           val _ = assert (#2 kdrel2 = ty2)
           val _ = assert (#3 kdrel2 = KdProper)
           val _ = assert (#1 kdrel3 = ctx)
           val _ = assert (#2 kdrel3 = ti)
           val _ = assert (#3 kdrel3 = KdTimeFun 0)
         in
           true
         end
     | KdDerivApp ((ctx, CstrApp (cstr1, cstr2), kd), kdderiv1, kdderiv2) =>
         let
           val _ = assert (check_kinding_derivation kdderiv1)
           val _ = assert (check_kinding_derivation kdderiv2)
           val kdrel1 = extract_kdrel kdderiv1
           val kdrel2 = extract_kdrel kdderiv2
           val _ = assert (#1 kdrel1 = ctx)
           val _ = assert (#2 kdrel1 = cstr1)
           val _ = assert (#3 kdrel1 = KdArrow (#3 kdrel2, kd))
           val _ = assert (#1 kdrel2 = ctx)
           val _ = assert (#2 kdrel2 = cstr2)
         in
           true
         end
     | KdDerivAbs ((ctx, CstrAbs (kd1, cstr2), kd), kdwf1, kdderiv2) =>
         let
           val _ = assert (check_kind_wellformness_derivation kdwf1)
           val _ = assert (check_kinding_derivation kdderiv2)
           val kdwfrel1 = extract_kdwfrel kdwf1
           val kdrel2 = extract_kdrel kdderiv2
           val _ = assert (#1 kdwfrel1 = ctx)
           val _ = assert (#2 kdwfrel1 = kd1)
           val _ = assert (#1 kdrel2 = BdKind kd1 :: ctx)
           val _ = assert (#2 kdrel2 = cstr2)
           val _ = assert (KdArrow (kd1, shift_kind ~1 (#3 kdrel2)) = kd)
         in
           true
         end
     | KdDerivForall ((ctx, CstrForall (kd1, cstr2), KdProper), kdwf1, kdderiv2) =>
         let
           val _ = assert (check_kind_wellformness_derivation kdwf1)
           val _ = assert (check_kinding_derivation kdderiv2)
           val kdwfrel1 = extract_kdwfrel kdwf1
           val kdrel2 = extract_kdrel kdderiv2
           val _ = assert (#1 kdwfrel1 = ctx)
           val _ = assert (#2 kdwfrel1 = kd1)
           val _ = assert (#1 kdrel2 = BdKind kd1 :: ctx)
           val _ = assert (#2 kdrel2 = cstr2)
           val _ = assert (#3 kdrel2 = KdProper)
         in
          true
         end
     | KdDerivExists ((ctx, CstrExists (kd1, cstr2), KdProper), kdwf1, kdderiv2) =>
         let
           val _ = assert (check_kind_wellformness_derivation kdwf1)
           val _ = assert (check_kinding_derivation kdderiv2)
           val kdwfrel1 = extract_kdwfrel kdwf1
           val kdrel2 = extract_kdrel kdderiv2
           val _ = assert (#1 kdwfrel1 = ctx)
           val _ = assert (#2 kdwfrel1 = kd1)
           val _ = assert (#1 kdrel2 = BdKind kd1 :: ctx)
           val _ = assert (#2 kdrel2 = cstr2)
           val _ = assert (#3 kdrel2 = KdProper)
         in
          true
         end
     | KdDerivRec ((ctx, CstrRec (kd1, cstr2), kd), kdwf1, kdderiv2) =>
         let
           val _ = assert (check_kind_wellformness_derivation kdwf1)
           val _ = assert (check_kinding_derivation kdderiv2)
           val kdwfrel1 = extract_kdwfrel kdwf1
           val kdrel2 = extract_kdrel kdderiv2
           val _ = assert (kd1 = kd)
           val _ = assert (#1 kdwfrel1 = ctx)
           val _ = assert (#2 kdwfrel1 = kd1)
           val _ = assert (#1 kdrel2 = BdKind kd1 :: ctx)
           val _ = assert (#2 kdrel2 = cstr2)
           val _ = assert (#3 kdrel2 = shift_kind 1 kd)
         in
          true
         end
     | KdDerivTypeInt (ctx, CstrTypeInt, KdProper) => true
     | KdDerivTypeUnit (ctx, CstrTypeUnit, KdProper) => true
     | KdDerivTypeNat ((ctx, CstrTypeNat cstr1, KdProper), kdderiv1) =>
         let
           val _ = assert (check_kinding_derivation kdderiv1)
           val kdrel1 = extract_kdrel kdderiv1
           val _ = assert (#1 kdrel1 = ctx)
           val _ = assert (#2 kdrel1 = cstr1)
           val _ = assert (#3 kdrel1 = KdNat)
         in
           true
         end
     | KdDerivTypeArray ((ctx, CstrTypeArray (cstr1, cstr2), KdProper), kdderiv1, kdderiv2) =>
         let
           val _ = assert (check_kinding_derivation kdderiv1)
           val _ = assert (check_kinding_derivation kdderiv2)
           val kdrel1 = extract_kdrel kdderiv1
           val kdrel2 = extract_kdrel kdderiv2
           val _ = assert (#1 kdrel1 = ctx)
           val _ = assert (#2 kdrel1 = cstr1)
           val _ = assert (#3 kdrel1 = KdProper)
           val _ = assert (#1 kdrel2 = ctx)
           val _ = assert (#2 kdrel2 = cstr2)
           val _ = assert (#3 kdrel2 = KdNat)
         in
           true
         end
     | _ =>
         let
           val _ = assert false
         in
           true
         end)
       handle CheckFail => let val _ = println (snd (Passes.Printer.transform_constr (#2 (extract_kdrel kdderiv), List.mapi (fn (i, _) => "%orz" ^ (str_int i)) (#1 (extract_kdrel kdderiv))))) in false end

  and check_proping_derivation prderiv = true

  and check_typing_derivation tyderiv =
    (case tyderiv of
      TyDerivSub ((ctx, tm, ty, ti), tyderiv1, tyeq2, prderiv3) =>
        let
          val _ = assert (check_typing_derivation tyderiv1)
          val _ = assert (check_type_equivalence_derivation tyeq2)
          val _ = assert (check_proping_derivation prderiv3)
          val tyrel1 = extract_tyrel tyderiv1
          val tyeqrel2 = extract_tyeqrel tyeq2
          val prrel3 = extract_prrel prderiv3
          val _ = assert (#1 tyrel1 = ctx)
          val _ = assert (#2 tyrel1 = tm)
          val _ = assert (#1 tyeqrel2 = ctx)
          val _ = assert (#2 tyeqrel2 = #3 tyrel1)
          val _ = assert (#3 tyeqrel2 = ty)
          (*val _ = println ("----> " ^ (snd (Passes.Printer.transform_constr (#3 tyrel1, List.mapi (fn (i, _) => "%orz" ^ (str_int i)) (#1 tyrel1)))) ^ "    " ^ (snd (Passes.Printer.transform_constr (ty, List.mapi (fn (i, _) => "%orz" ^ (str_int i)) ctx))))*)
          val _ = assert (#1 prrel3 = ctx)
          val _ = assert (#2 prrel3 = PrBinRel (PrRelLe, #4 tyrel1, ti))
          (*val _ = println ("----> " ^ (snd (Passes.Printer.transform_constr (#4 tyrel1, List.mapi (fn (i, _) => "%orz" ^ (str_int i)) (#1 tyrel1)))) ^ "    " ^ (snd (Passes.Printer.transform_constr (ti, List.mapi (fn (i, _) => "%orz" ^ (str_int i)) ctx))))*)
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
          val tyrel1 = extract_tyrel tyderiv1
          val tyrel2 = extract_tyrel tyderiv2
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
          val kdrel1 = extract_kdrel kdderiv1
          val tyrel2 = extract_tyrel tyderiv2
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
          val kdrel1 = extract_kdrel kdderiv1
          val tyrel2 = extract_tyrel tyderiv2
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
          val tyrel1 = extract_tyrel tyderiv1
          val tyrel2 = extract_tyrel tyderiv2
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
          val tyrel1 = extract_tyrel tyderiv1
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
          val tyrel1 = extract_tyrel tyderiv1
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
          val kdrel1 = extract_kdrel kdderiv1
          val tyrel2 = extract_tyrel tyderiv2
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
          val kdrel1 = extract_kdrel kdderiv1
          val tyrel2 = extract_tyrel tyderiv2
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
          val tyrel1 = extract_tyrel tyderiv1
          val tyrel2 = extract_tyrel tyderiv2
          val tyrel3 = extract_tyrel tyderiv3
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
                        (*val _ = assert (#2 tyrel3 = tm3)
                        val _ = assert (#3 tyrel3 = shift_constr 1 ty)
                        val _ = assert (#4 tyrel3 = shift_constr 1 ti3)*)
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
          val kdrel1 = extract_kdrel kdderiv1
          val tyrel2 = extract_tyrel tyderiv2
          fun unfold_app ty1 rands =
            case ty1 of
              CstrApp (cstr1, cstr2) => unfold_app cstr1 (cstr2 :: rands)
            | _ => (ty1, rands)
          fun fold_app ty1 rands =
            case rands of
              [] => ty1
            | hd :: tl => fold_app (subst_constr_in_constr_top hd (#2 (extract_cstr_abs ty1))) tl
          val (ty1, rands) = unfold_app ty []
          val _ = case ty1 of
                    CstrRec (kd1, ty_body) =>
                      let
                        val _ = assert (#1 kdrel1 = ctx)
                        val _ = assert (#2 kdrel1 = ty)
                        val _ = assert (#3 kdrel1 = KdProper)
                        val _ = assert (#1 tyrel2 = ctx)
                        val _ = assert (#2 tyrel2 = tm1)
                        val _ = assert (#3 tyrel2 = fold_app (subst_constr_in_constr_top ty1 ty_body) rands)
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
          val tyrel1 = extract_tyrel tyderiv1
          fun unfold_app ty1 rands =
            case ty1 of
              CstrApp (cstr1, cstr2) => unfold_app cstr1 (cstr2 :: rands)
            | _ => (ty1, rands)
          fun fold_app ty1 rands =
            case rands of
              [] => ty1
            | hd :: tl => fold_app (subst_constr_in_constr_top hd (#2 (extract_cstr_abs ty1))) tl
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
          val kdrel1 = extract_kdrel kdderiv1
          val kdrel2 = extract_kdrel kdderiv2
          val tyrel3 = extract_tyrel tyderiv3
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
          val tyrel1 = extract_tyrel tyderiv1
          val tyrel2 = extract_tyrel tyderiv2
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
          val kdwfrel1 = extract_kdwfrel kdwf1
          val tyrel2 = extract_tyrel tyderiv2
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
          val tyrel1 = extract_tyrel tyderiv1
          val kdrel2 = extract_kdrel kdderiv2
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
          val tyrel1 = extract_tyrel tyderiv1
          val tyrel2 = extract_tyrel tyderiv2
          val _ = assert (#1 tyrel1 = ctx)
          val _ = assert (#2 tyrel1 = tm1)
          val _ = assert ((#3 tyrel1, #3 tyrel2) = #2 (term_bin_op_to_constr bop))
          val _ = assert (#4 tyrel1 = ti1)
          val _ = assert (#1 tyrel2 = ctx)
          val _ = assert (#2 tyrel2 = tm2)
          val _ = assert (#4 tyrel2 = ti2)
          val _ = assert (ty = #1 (term_bin_op_to_constr bop))
        in
          true
        end
    | TyDerivArrayNew ((ctx, TmArrayNew (tm1, tm2), CstrTypeArray (cstr1, cstr2), CstrBinOp (CstrBopAdd, ti1, ti2)), tyderiv1, tyderiv2) =>
        let
          val _ = assert (check_typing_derivation tyderiv1)
          val _ = assert (check_typing_derivation tyderiv2)
          val tyrel1 = extract_tyrel tyderiv1
          val tyrel2 = extract_tyrel tyderiv2
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
          val tyrel1 = extract_tyrel tyderiv1
          val tyrel2 = extract_tyrel tyderiv2
          val prrel3 = extract_prrel prderiv3
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
          val tyrel1 = extract_tyrel tyderiv1
          val tyrel2 = extract_tyrel tyderiv2
          val prrel3 = extract_prrel prderiv3
          val tyrel4 = extract_tyrel tyderiv4
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
    | TyDerivLet ((ctx, TmLet (tm1, tm2), ty2, CstrBinOp (CstrBopAdd, ti1, ti2)), tyderiv2, tyderiv3) =>
        let
          val _ = assert (check_typing_derivation tyderiv2)
          val _ = assert (check_typing_derivation tyderiv3)
          val tyrel2 = extract_tyrel tyderiv2
          val tyrel3 = extract_tyrel tyderiv3
          val _ = assert (#1 tyrel2 = ctx)
          val _ = assert (#2 tyrel2 = tm1)
          val _ = assert (#4 tyrel2 = ti1)
          val _ = assert (#1 tyrel3 = BdType (#3 tyrel2) :: ctx)
          val _ = assert (#2 tyrel3 = tm2)
          val _ = assert (#3 tyrel3 = shift_constr 1 ty2)
          val _ = assert (#4 tyrel3 = shift_constr 1 ti2)
        in
          true
        end
    | TyDerivNever ((ctx, TmNever, ty, CstrTime "0.0"), kdderiv1, prderiv2) =>
        let
          val _ = assert (check_kinding_derivation kdderiv1)
          val _ = assert (check_proping_derivation prderiv2)
          val kdrel1 = extract_kdrel kdderiv1
          val prrel2 = extract_prrel prderiv2
          val _ = assert (#1 kdrel1 = ctx)
          val _ = assert (#2 kdrel1 = ty)
          val _ = assert (#3 kdrel1 = KdProper)
          val _ = assert (#1 prrel2 = ctx)
          val _ = assert (#2 prrel2 = PrBot)
        in
          true
        end
    | _ => let val _ = assert false in true end)
      handle CheckFail => let val _ = println (snd (Passes.Printer.transform_term (#2 (extract_tyrel tyderiv), List.mapi (fn (i, _) => "%orz" ^ (str_int i)) (#1 (extract_tyrel tyderiv))))) in false end
end
