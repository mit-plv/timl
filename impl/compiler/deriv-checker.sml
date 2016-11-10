functor DerivCheckerFun(MicroTiMLDef : SIG_MICRO_TIML_DEF) : SIG_DERIV_CHECKER =
struct
open Util
open List
infixr 0 $

structure MicroTiMLDef = MicroTiMLDef
open MicroTiMLDef
structure MicroTiMLUtil = MicroTiMLUtilFun(MicroTiMLDef)
open MicroTiMLUtil
structure AstTransformers = AstTransformersFun(MicroTiMLDef)
open AstTransformers

open PlainPrinter
open ShiftCstr
open SubstCstr

exception CheckFail

fun assert p = if p then () else raise CheckFail

fun check_proping pr =
  case pr of
      PrAdmit (kctx, p) =>
      let
          val () =
              case p of
                  PBinPred (PBTimeLe, _, _) =>
                  let
                      (*8val () = app (println o prefix "    " o str_kind) kctx
                      val () = println $ "ADMIT: " ^ str_prop p*)
                  in
                      ()
                  end
                | _ => ()
      in
          ()
      end

and check_kdeq ke = (
    case ke of
        KdEqKType (kctx, KType, KType) => ()
      | KdEqKArrow ((kctx, KArrow (k11, k12), KArrow (k21, k22)), ke1, ke2) =>
        let
            val () = check_kdeq ke1
            val () = check_kdeq ke2
            val jke1 = extract_judge_kdeq ke1
            val jke2 = extract_judge_kdeq ke2
            val () = assert (#1 jke1 = kctx)
            val () = assert (#2 jke1 = k11)
            val () = assert (#3 jke1 = k21)
            val () = assert (#1 jke2 = kctx)
            val () = assert (#2 jke2 = k12)
            val () = assert (#3 jke2 = k22)
        in
            ()
        end
      | KdEqBaseSort (kctx, KBaseSort b1, KBaseSort b2) => assert (b1 = b2)
      | KdEqSubset ((kctx, KSubset (k1, p1), KSubset (k2, p2)), ke, pr) =>
        let
            val () = check_kdeq ke
            val () = check_proping pr
            val jke = extract_judge_kdeq ke
            val jpr = extract_judge_proping pr
            val () = assert (#1 jke = kctx)
            val () = assert (#2 jke = k1)
            val () = assert (#3 jke = k2)
            val () = assert (#1 jpr = k1 :: kctx)
            val () = assert (#2 jpr = PBinConn (PBCIff, p1, p2))
        in
            ()
        end
      | _ => raise CheckFail)
                    handle CheckFail =>
                           let
                               val jke = extract_judge_kdeq ke
                           in
                               println $ "kdeq: " ^ str_kind (#2 jke) ^ " " ^ str_kind (#3 jke)
                           end

and check_kinding kd = (
    case kd of
        KdVar (kctx, CVar x, k) =>
        let
            val () = assert (k = shift_c_k (1 + x) 0 (nth (kctx, x)))
        in
            ()
        end
      | KdConst (kctx, CConst cn, k) => assert (k = const_kind cn)
      | KdBinOp ((kctx, CBinOp (opr, i1, i2), k), kd1, kd2) =>
        let
            val () = check_kinding kd1
            val () = check_kinding kd2
            val jkd1 = extract_judge_kinding kd1
            val jkd2 = extract_judge_kinding kd2
            val () = assert (#1 jkd1 = kctx)
            val () = assert (#2 jkd1 = i1)
            val () = assert (#3 jkd1 = cbinop_arg1_kind opr)
            val () = assert (#1 jkd2 = kctx)
            val () = assert (#2 jkd2 = i2)
            val () = assert (#3 jkd2 = cbinop_arg2_kind opr)
            val () = assert (k = cbinop_result_kind opr)
        in
            ()
        end
      | KdUnOp ((kctx, CUnOp (opr, i), k), kd) =>
        let
            val () = check_kinding kd
            val jkd = extract_judge_kinding kd
            val () = assert (#1 jkd = kctx)
            val () = assert (#2 jkd = i)
            val () = assert (#3 jkd = cunop_arg_kind opr)
            val () = assert (k = cunop_result_kind opr)
        in
            ()
        end
      | KdIte ((kctx, CIte (i1, i2, i3), k), kd1, kd2, kd3) =>
        let
            val () = check_kinding kd1
            val () = check_kinding kd2
            val () = check_kinding kd3
            val jkd1 = extract_judge_kinding kd1
            val jkd2 = extract_judge_kinding kd2
            val jkd3 = extract_judge_kinding kd3
            val () = assert (#1 jkd1 = kctx)
            val () = assert (#2 jkd1 = i1)
            val () = assert (#3 jkd1 = KBool)
            val () = assert (#1 jkd2 = kctx)
            val () = assert (#2 jkd2 = i2)
            val () = assert (#3 jkd2 = k)
            val () = assert (#1 jkd3 = kctx)
            val () = assert (#2 jkd3 = i3)
            val () = assert (#3 jkd3 = k)
        in
            ()
        end
      | KdArrow ((kctx, CArrow (t1, i, t2), KType), kd1, kd2, kd3) =>
        let
            val () = check_kinding kd1
            val () = check_kinding kd2
            val () = check_kinding kd3
            val jkd1 = extract_judge_kinding kd1
            val jkd2 = extract_judge_kinding kd2
            val jkd3 = extract_judge_kinding kd3
            val () = assert (#1 jkd1 = kctx)
            val () = assert (#2 jkd1 = t1)
            val () = assert (#3 jkd1 = KType)
            val () = assert (#1 jkd2 = kctx)
            val () = assert (#2 jkd2 = i)
            val () = assert (#3 jkd2 = KTime)
            val () = assert (#1 jkd3 = kctx)
            val () = assert (#2 jkd3 = t2)
            val () = assert (#3 jkd3 = KType)
        in
            ()
        end
      | KdAbs ((kctx, CAbs c, KArrow (k1, k2)), wk, kd) =>
        let
            val () = check_wfkind wk
            val () = check_kinding kd
            val jwk = extract_judge_wfkind wk
            val jkd = extract_judge_kinding kd
            val () = assert (#1 jwk = kctx)
            val () = assert (#2 jwk = k1)
            val () = assert (#1 jkd = k1 :: kctx)
            val () = assert (#2 jkd = c)
            val () = assert (#3 jkd = shift0_c_k k2)
        in
            ()
        end
      | KdApp ((kctx, CApp (c1, c2), k2), kd1, kd2) =>
        let
            val () = check_kinding kd1
            val () = check_kinding kd2
            val jkd1 = extract_judge_kinding kd1
            val jkd2 = extract_judge_kinding kd2
            val () = assert (#1 jkd1 = kctx)
            val () = assert (#2 jkd1 = c1)
            val () = assert (#3 jkd1 = KArrow (#3 jkd2, k2))
            val () = assert (#1 jkd2 = kctx)
            val () = assert (#2 jkd2 = c2)
        in
            ()
        end
      | KdTimeAbs ((kctx, CTimeAbs i, KBaseSort (BSTimeFun arity)), kd) =>
        let
            val () = check_kinding kd
            val jkd = extract_judge_kinding kd
            val () = assert (#1 jkd = KNat :: kctx)
            val () = assert (#2 jkd = i)
            val () = assert (#3 jkd = KTimeFun (arity - 1))
        in
            ()
        end
      | KdTimeApp ((kctx, CTimeApp (arity, c1, c2), KBaseSort (BSTimeFun arity')), kd1, kd2) =>
        let
            val () = check_kinding kd1
            val () = check_kinding kd2
            val jkd1 = extract_judge_kinding kd1
            val jkd2 = extract_judge_kinding kd2
            val () = assert (arity = arity')
            val () = assert (#1 jkd1 = kctx)
            val () = assert (#2 jkd1 = c1)
            val () = assert (#3 jkd1 = KTimeFun (arity + 1))
            val () = assert (#1 jkd2 = kctx)
            val () = assert (#2 jkd2 = c2)
            val () = assert (#3 jkd2 = KNat)
        in
            ()
        end
      | KdQuan ((kctx, CQuan (q, k, c), KType), wk, kd) =>
        let
            val () = check_wfkind wk
            val () = check_kinding kd
            val jwk = extract_judge_wfkind wk
            val jkd = extract_judge_kinding kd
            val () = assert (#1 jwk = kctx)
            val () = assert (#2 jwk = k)
            val () = assert (#1 jkd = k :: kctx)
            val () = assert (#2 jkd = c)
            val () = assert (#3 jkd = KType)
        in
            ()
        end
      | KdRec ((kctx, CRec (_, k, c), k'), wk, kd) =>
        let
            val () = check_wfkind wk
            val () = check_kinding kd
            val jwk = extract_judge_wfkind wk
            val jkd = extract_judge_kinding kd
            val () = assert (k = k')
            val () = assert (#1 jwk = kctx)
            val () = assert (#2 jwk = k)
            val () = assert (#1 jkd = k :: kctx)
            val () = assert (#2 jkd = c)
            val () = assert (#3 jkd = shift0_c_k k)
        in
            ()
        end
      | KdRef ((kctx, CRef t, KType), kd) =>
        let
            val () = check_kinding kd
            val jkd = extract_judge_kinding kd
            val () = assert (#1 jkd = kctx)
            val () = assert (#2 jkd = t)
            val () = assert (#3 jkd = KType)
        in
            ()
        end
      | KdEq ((kctx, c, k), kd, ke) =>
        let
            val () = check_kinding kd
            val () = check_kdeq ke
            val jkd = extract_judge_kinding kd
            val jke = extract_judge_kdeq ke
            val () = assert (#1 jkd = kctx)
            val () = assert (#2 jkd = c)
            val () = assert (#1 jke = kctx)
            val () = assert (#2 jke = k)
            val () = assert (#3 jke = #3 jkd)
        in
            ()
        end
      | KdAdmit (kctx, c, k) => ()
      | _ => raise CheckFail)
                       handle CheckFail =>
                              let
                                  val jkd = extract_judge_kinding kd
                              in
                                  println $ "kinding: " ^ str_cstr (#2 jkd) ^ " " ^ str_kind (#3 jkd)
                              end

and check_wfkind wk = (
    case wk of
        WfKdType (kctx, KType) => ()
      | WfKdArrow ((kctx, KArrow (k1, k2)), wk1, wk2) =>
        let
            val () = check_wfkind wk1
            val () = check_wfkind wk2
            val jwk1 = extract_judge_wfkind wk1
            val jwk2 = extract_judge_wfkind wk2
            val () = assert (#1 jwk1 = kctx)
            val () = assert (#2 jwk1 = k1)
            val () = assert (#1 jwk2 = kctx)
            val () = assert (#2 jwk2 = k2)
        in
            ()
        end
      | WfKdBaseSort (kctx, KBaseSort b) => ()
      | WfKdSubset ((kctx, KSubset (k, p)), wk, wp) =>
        let
            val () = check_wfkind wk
            val () = check_wfprop wp
            val jwk = extract_judge_wfkind wk
            val jwp = extract_judge_wfprop wp
            val () = assert (#1 jwk = kctx)
            val () = assert (#2 jwk = k)
            val () = assert (#1 jwp = k :: kctx)
            val () = assert (#2 jwp = p)
        in
            ()
        end
      | WfKdAdmit (kctx, k) => ()
      | _ => raise CheckFail)
                      handle CheckFail =>
                             let
                                 val jwk = extract_judge_wfkind wk
                             in
                                 println $ "wfkind: " ^ str_kind (#2 jwk)
                             end

and check_wfprop wp = (
    case wp of
        WfPropTrue (kctx, PTrue) => ()
      | WfPropFalse (kctx, PFalse) => ()
      | WfPropBinConn ((kctx, PBinConn (opr, p1, p2)), wp1, wp2) =>
        let
            val () = check_wfprop wp1
            val () = check_wfprop wp2
            val jwp1 = extract_judge_wfprop wp1
            val jwp2 = extract_judge_wfprop wp2
            val () = assert (#1 jwp1 = kctx)
            val () = assert (#2 jwp1 = p1)
            val () = assert (#1 jwp2 = kctx)
            val () = assert (#2 jwp2 = p2)
        in
            ()
        end
      | WfPropNot ((kctx, PNot p), wp) =>
        let
            val () = check_wfprop wp
            val jwp = extract_judge_wfprop wp
            val () = assert (#1 jwp = kctx)
            val () = assert (#2 jwp = p)
        in
            ()
        end
      | WfPropBinPred ((kctx, PBinPred (opr, i1, i2)), kd1, kd2) =>
        let
            val () = check_kinding kd1
            val () = check_kinding kd2
            val jkd1 = extract_judge_kinding kd1
            val jkd2 = extract_judge_kinding kd2
            val () = assert (#1 jkd1 = kctx)
            val () = assert (#2 jkd1 = i1)
            val () = assert (#3 jkd1 = binpred_arg1_kind opr)
            val () = assert (#1 jkd2 = kctx)
            val () = assert (#2 jkd2 = i2)
            val () = assert (#3 jkd2 = binpred_arg2_kind opr)
        in
            ()
        end
      | WfPropQuan ((kctx, PQuan (q, s, p)), wp) =>
        let
            val () = check_wfprop wp
            val jwp = extract_judge_wfprop wp
            val () = assert (#1 jwp = KBaseSort s :: kctx)
            val () = assert (#2 jwp = p)
        in
            ()
        end
      | _ => raise CheckFail)
                      handle CheckFail =>
                             let
                                 val jwp = extract_judge_wfprop wp
                             in
                                 println $ "wfprop: " ^ str_prop (#2 jwp)
                             end

and check_tyeq te = (
    case te of
        TyEqVar (kctx, CVar x, CVar x') => assert (x = x')
      | TyEqConst (kctx, CConst cn, CConst cn') => assert (cn = cn')
      | TyEqBinOp ((kctx, CBinOp (opr, t11, t12), CBinOp (opr', t21, t22)), te1, te2) =>
        let
            val () = check_tyeq te1
            val () = check_tyeq te2
            val jte1 = extract_judge_tyeq te1
            val jte2 = extract_judge_tyeq te2
            val () = assert (opr = opr')
            val () = assert (#1 jte1 = kctx)
            val () = assert (#2 jte1 = t11)
            val () = assert (#3 jte1 = t21)
            val () = assert (#1 jte2 = kctx)
            val () = assert (#2 jte2 = t12)
            val () = assert (#3 jte2 = t22)
        in
            ()
        end
      | TyEqUnOp ((kctx, CUnOp (opr, t1), CUnOp (opr', t2)), te) =>
        let
            val () = check_tyeq te
            val jte = extract_judge_tyeq te
            val () = assert (opr = opr')
            val () = assert (#1 jte = kctx)
            val () = assert (#2 jte = t1)
            val () = assert (#3 jte = t2)
        in
            ()
        end
      | TyEqNat ((kctx, i1, i2), kd1, kd2, pr) =>
        let
            val () = check_kinding kd1
            val () = check_kinding kd2
            val () = check_proping pr
            val jkd1 = extract_judge_kinding kd1
            val jkd2 = extract_judge_kinding kd2
            val jpr = extract_judge_proping pr
            val () = assert (#1 jkd1 = kctx)
            val () = assert (#2 jkd1 = i1)
            val () = assert (#3 jkd1 = KNat)
            val () = assert (#1 jkd2 = kctx)
            val () = assert (#2 jkd2 = i2)
            val () = assert (#3 jkd2 = KNat)
            val () = assert (#1 jpr = kctx)
            val () = assert (#2 jpr = PBinPred (PBNatEq, i1, i2))
        in
            ()
        end
      | TyEqIte ((kctx, CIte (t11, t12, t13), CIte (t21, t22, t23)), te1, te2, te3) =>
        let
            val () = check_tyeq te1
            val () = check_tyeq te2
            val () = check_tyeq te3
            val jte1 = extract_judge_tyeq te1
            val jte2 = extract_judge_tyeq te2
            val jte3 = extract_judge_tyeq te3
            val () = assert (#1 jte1 = kctx)
            val () = assert (#2 jte1 = t11)
            val () = assert (#3 jte1 = t21)
            val () = assert (#1 jte2 = kctx)
            val () = assert (#2 jte2 = t12)
            val () = assert (#3 jte2 = t22)
            val () = assert (#1 jte3 = kctx)
            val () = assert (#2 jte3 = t13)
            val () = assert (#3 jte3 = t23)
        in
            ()
        end
      | TyEqArrow ((kctx, CArrow (t11, i1, t12), CArrow (t21, i2, t22)), te1, pr, te2) =>
        let
            val () = check_tyeq te1
            val () = check_proping pr
            val () = check_tyeq te2
            val jte1 = extract_judge_tyeq te1
            val jpr = extract_judge_proping pr
            val jte2 = extract_judge_tyeq te2
            val () = assert (#1 jte1 = kctx)
            val () = assert (#2 jte1 = t11)
            val () = assert (#3 jte1 = t21)
            val () = assert (#1 jpr = kctx)
            val () = assert (#2 jpr = TEq (i1, i2))
            val () = assert (#1 jte2 = kctx)
            val () = assert (#2 jte2 = t12)
            val () = assert (#3 jte2 = t22)
        in
            ()
        end
      | TyEqApp ((kctx, CApp (c11, c12), CApp (c21, c22)), te1, te2) =>
        let
            val () = check_tyeq te1
            val () = check_tyeq te2
            val jte1 = extract_judge_tyeq te1
            val jte2 = extract_judge_tyeq te2
            val () = assert (#1 jte1 = kctx)
            val () = assert (#2 jte1 = c11)
            val () = assert (#3 jte1 = c21)
            val () = assert (#1 jte2 = kctx)
            val () = assert (#2 jte2 = c12)
            val () = assert (#3 jte2 = c22)
        in
            ()
        end
      | TyEqTimeApp ((kctx, CTimeApp (arity, c11, c12), CTimeApp (arity', c21, c22)), te1, te2) =>
        let
            val () = check_tyeq te1
            val () = check_tyeq te2
            val jte1 = extract_judge_tyeq te1
            val jte2 = extract_judge_tyeq te2
            val () = assert (arity = arity')
            val () = assert (#1 jte1 = kctx)
            val () = assert (#2 jte1 = c11)
            val () = assert (#3 jte1 = c21)
            val () = assert (#1 jte2 = kctx)
            val () = assert (#2 jte2 = c12)
            val () = assert (#3 jte2 = c22)
        in
            ()
        end
      | TyEqBeta ((kctx, CApp (t1, t2), t'), te1, te2, te3) =>
        let
            val () = check_tyeq te1
            val () = check_tyeq te2
            val () = check_tyeq te3
            val jte1 = extract_judge_tyeq te1
            val jte2 = extract_judge_tyeq te2
            val jte3 = extract_judge_tyeq te3
            val () =
                case (#3 jte1) of
                    CAbs t1' =>
                    let
                        val () = assert (#1 jte1 = kctx)
                        val () = assert (#2 jte1 = t1)
                        val () = assert (#1 jte2 = kctx)
                        val () = assert (#2 jte2 = t2)
                        val t2' = #3 jte2
                        val () = assert (#1 jte3 = kctx)
                        val () = assert (#2 jte3 = subst0_c_c t2' t1')
                        val () = assert (#3 jte3 = t')
                    in
                        ()
                    end
                  | _ => assert false
        in
            ()
        end
      | TyEqBetaRev ((kctx, t', CApp (t1, t2)), te1, te2, te3) =>
        let
            val () = check_tyeq te1
            val () = check_tyeq te2
            val () = check_tyeq te3
            val jte1 = extract_judge_tyeq te1
            val jte2 = extract_judge_tyeq te2
            val jte3 = extract_judge_tyeq te3
            val () =
                case (#2 jte1) of
                    CAbs t1' =>
                    let
                        val () = assert (#1 jte1 = kctx)
                        val () = assert (#3 jte1 = t1)
                        val () = assert (#1 jte2 = kctx)
                        val t2' = #2 jte2
                        val () = assert (#3 jte2 = t2)
                        val () = assert (#1 jte3 = kctx)
                        val () = assert (#2 jte3 = t')
                        val () = assert (#3 jte3 = subst0_c_c t2' t1')
                    in
                        ()
                    end
                  | _ => assert false
        in
            ()
        end
      | TyEqQuan ((kctx, CQuan (q, k1, t1), CQuan (q', k2, t2)), ke, te) =>
        let
            val () = check_kdeq ke
            val () = check_tyeq te
            val jke = extract_judge_kdeq ke
            val jte = extract_judge_tyeq te
            val () = assert (q = q')
            val () = assert (#1 jke = kctx)
            val () = assert (#2 jke = k1)
            val () = assert (#3 jke = k2)
            val () = assert (#1 jte = k1 :: kctx)
            val () = assert (#2 jte = t1)
            val () = assert (#3 jte = t2)
        in
            ()
        end
      | TyEqRec ((kctx, CRec (_, k1, t1), CRec (_, k2, t2)), ke, te) =>
        let
            val () = check_kdeq ke
            val () = check_tyeq te
            val jke = extract_judge_kdeq ke
            val jte = extract_judge_tyeq te
            val () = assert (#1 jke = kctx)
            val () = assert (#2 jke = k1)
            val () = assert (#3 jke = k2)
            val () = assert (#1 jte = k1 :: kctx)
            val () = assert (#2 jte = t1)
            val () = assert (#3 jte = t2)
        in
            ()
        end
      | TyEqRef ((kctx, CRef t1, CRef t2), te) =>
        let
            val () = check_tyeq te
            val jte = extract_judge_tyeq te
            val () = assert (#1 jte = kctx)
            val () = assert (#2 jte = t1)
            val () = assert (#3 jte = t2)
        in
            ()
        end
      | TyEqAbs ((kctx, t, t')) => assert (t = t')
      | TyEqTimeAbs ((kctx, t, t')) => assert (t = t')
      | _ => raise CheckFail)
                    handle CheckFail =>
                           let
                               val jte = extract_judge_tyeq te
                           in
                               println $ "tyeq:\n    " ^ str_cstr (#2 jte) ^ "\n    " ^ str_cstr (#3 jte)
                           end

and check_typing ty = (
    case ty of
        TyVar ((kctx, tctx), EVar x, t, T0) => assert (nth (tctx, x) = t)
      | TyApp ((ctx, EBinOp (EBApp, e1, e2), t2, CBinOp (CBTimeAdd, CBinOp (CBTimeAdd, CBinOp (CBTimeAdd, i1, i2), T1), i)), ty1, ty2) =>
        let
            val () = check_typing ty1
            val () = check_typing ty2
            val jty1 = extract_judge_typing ty1
            val jty2 = extract_judge_typing ty2
            val () = assert (#1 jty1 = ctx)
            val () = assert (#2 jty1 = e1)
            val () = assert (#3 jty1 = CArrow (#3 jty2, i, t2))
            val () = assert (#4 jty1 = i1)
            val () = assert (#1 jty2 = ctx)
            val () = assert (#2 jty2 = e2)
            val () = assert (#4 jty2 = i2)
        in
            ()
        end
      | TyAbs (((kctx, tctx), EAbs e, CArrow (t1, i, t2), T0), kd, ty) =>
        let
            val () = check_kinding kd
            val () = check_typing ty
            val jkd = extract_judge_kinding kd
            val jty = extract_judge_typing ty
            val () = assert (#1 jkd = kctx)
            val () = assert (#2 jkd = t1)
            val () = assert (#3 jkd = KType)
            val () = assert (#1 jty = (kctx, t1 :: tctx))
            val () = assert (#2 jty = e)
            val () = assert (#3 jty = t2)
            val () = assert (#4 jty = i)
        in
            ()
        end
      | TyAppC ((ctx as (kctx, tctx), EAppC (e, c), t, i), ty, kd) =>
        let
            val () = check_typing ty
            val () = check_kinding kd
            val jty = extract_judge_typing ty
            val jkd = extract_judge_kinding kd
            val () =
                case (#3 jty) of
                    CQuan (QuanForall, k, t') =>
                    let
                        val () = assert (#1 jty = ctx)
                        val () = assert (#2 jty = e)
                        val () = assert (#4 jty = i)
                        val () = assert (#1 jkd = kctx)
                        val () = assert (#2 jkd = c)
                        val () = assert (#3 jkd = k)
                        val () = assert (t = subst0_c_c c t')
                    in
                        ()
                    end
                  | _ => assert false
        in
            ()
        end
      | TyAbsC ((ctx as (kctx, tctx), EAbsC e, CQuan (QuanForall, k, t), T0), wk, ty) =>
        let
            val () = check_wfkind wk
            val () = check_typing ty
            val jwk = extract_judge_wfkind wk
            val jty = extract_judge_typing ty
            val () = assert (#1 jwk = kctx)
            val () = assert (#2 jwk = k)
            val () = assert (#1 jty = (k :: kctx, map shift0_c_c tctx))
            val () = assert (#2 jty = e)
            val () = assert (#3 jty = t)
            val () = assert (#4 jty = T0)
        in
            ()
        end
      | TyRec ((ctx as (kctx, tctx), ERec e, t, T0), kd, ty) =>
        let
            val () = check_kinding kd
            val () = check_typing ty
            val jkd = extract_judge_kinding kd
            val jty = extract_judge_typing ty
            val () = assert (#1 jkd = kctx)
            val () = assert (#2 jkd = t)
            val () = assert (#3 jkd = KType)
            val () = assert (#1 jty = (kctx, t :: tctx))
            val () = assert (#2 jty = e)
            val () = assert (#3 jty = t)
            val () = assert (#4 jty = T0)
        in
            ()
        end
      | TyFix ((ctx as (kctx, tctx), EFix (n, e), t, T0), kd, ty) =>
        let
            val () = check_kinding kd
            val () = check_typing ty
            val jkd = extract_judge_kinding kd
            val jty = extract_judge_typing ty
            val () = assert (#1 jkd = [])
            val () = assert (#2 jkd = t)
            val () = assert (#3 jkd = KType)
            fun unfold_CForalls t ks =
              case t of
                  CQuan (QuanForall, k, t) => unfold_CForalls t (k :: ks)
                | _ => (t, ks)
            val (it, ks) = unfold_CForalls t []
            val () = assert (n = length ks)
            val () =
                case it of
                    CArrow (t1, i, t2) =>
                    let
                        val () = assert (#1 jty = (ks, [t1, t]))
                        val () = assert (#2 jty = e)
                        val () = assert (#3 jty = t2)
                        val () = assert (#4 jty = i)
                    in
                        ()
                    end
                  | _ => assert false
        in
            ()
        end
      | TyFold ((ctx as (kctx, tctx), EUnOp (EUFold, e), t, i), kd, ty) =>
        let
            val () = check_kinding kd
            val () = check_typing ty
            val jkd = extract_judge_kinding kd
            val jty = extract_judge_typing ty
            fun unfold_CApps t cs =
              case t of
                  CApp (t, c) => unfold_CApps t (c :: cs)
                | _ => (t, cs)
            val (t1, cs) = unfold_CApps t []
            val () =
                case t1 of
                    CRec (_, k, t2) =>
                    let
                        val () = assert (#1 jkd = kctx)
                        val () = assert (#2 jkd = t)
                        val () = assert (#3 jkd = KType)
                        val () = assert (#1 jty = ctx)
                        val () = assert (#2 jty = e)
                        val () = assert (#3 jty = CApps (subst0_c_c t1 t2) cs)
                        val () = assert (#4 jty = i)
                    in
                        ()
                    end
                  | _ => assert false
        in
            ()
        end
      | TyUnfold ((ctx, EUnOp (EUUnfold, e), t', i), ty) =>
        let
            val () = check_typing ty
            val jty = extract_judge_typing ty
            fun unfold_CApps t cs =
              case t of
                  CApp (t, c) => unfold_CApps t (c :: cs)
                | _ => (t, cs)
            val (t, cs) = unfold_CApps (#3 jty) []
            val () =
                case t of
                    CRec (_, k, t1) =>
                    let
                        val () = assert (#1 jty = ctx)
                        val () = assert (#2 jty = e)
                        val () = assert (#4 jty = i)
                        val () = assert (t' = CApps (subst0_c_c t t1) cs)
                    in
                        ()
                    end
                  | _ => assert false
        in
            ()
        end
      | TyPack ((ctx as (kctx, tctx), EPack (c, e), CQuan (QuanExists, k, t1), i), kd1, kd2, ty) =>
        let
            val () = check_kinding kd1
            val () = check_kinding kd2
            val () = check_typing ty
            val jkd1 = extract_judge_kinding kd1
            val jkd2 = extract_judge_kinding kd2
            val jty = extract_judge_typing ty
            val () = assert (#1 jkd1 = kctx)
            val () = assert (#2 jkd1 = CExists (k, t1))
            val () = assert (#3 jkd1 = KType)
            val () = assert (#1 jkd2 = kctx)
            val () = assert (#2 jkd2 = c)
            val () = assert (#3 jkd2 = k)
            val () = assert (#1 jty = ctx)
            val () = assert (#2 jty = e)
            val () = assert (#3 jty = subst0_c_c c t1)
            val () = assert (#4 jty = i)
        in
            ()
        end
      | TyUnpack ((ctx as (kctx, tctx), EUnpack (e1, e2), t2, CBinOp (CBTimeAdd, i1, i2)), ty1, ty2) =>
        let
            val () = check_typing ty1
            val () = check_typing ty2
            val jty1 = extract_judge_typing ty1
            val jty2 = extract_judge_typing ty2
            val () =
                case (#3 jty1) of
                    CQuan (QuanExists, k, t) =>
                    let
                        val () = assert (#1 jty1 = ctx)
                        val () = assert (#2 jty1 = e1)
                        val () = assert (#4 jty1 = i1)
                        val () = assert (#1 jty2 = (k :: kctx, t :: map shift0_c_c tctx))
                        val () = assert (#2 jty2 = e2)
                        val () = assert (#3 jty2 = shift0_c_c t2)
                        val () = assert (#4 jty2 = shift0_c_c i2)
                    in
                        ()
                    end
                  | _ => assert false
        in
            ()
        end
      | TyConst (ctx, EConst cn, t, T0) => assert (t = const_type cn)
      | TyPair ((ctx, EBinOp (EBPair, e1, e2), CBinOp (CBTypeProd, t1, t2), CBinOp (CBTimeAdd, i1, i2)), ty1, ty2) =>
        let
            val () = check_typing ty1
            val () = check_typing ty2
            val jty1 = extract_judge_typing ty1
            val jty2 = extract_judge_typing ty2
            val () = assert (#1 jty1 = ctx)
            val () = assert (#2 jty1 = e1)
            val () = assert (#3 jty1 = t1)
            val () = assert (#4 jty1 = i1)
            val () = assert (#1 jty2 = ctx)
            val () = assert (#2 jty2 = e2)
            val () = assert (#3 jty2 = t2)
            val () = assert (#4 jty2 = i2)
        in
            ()
        end
      | TyProj ((ctx, EUnOp (EUProj p, e), t, i), ty) =>
        let
            val () = check_typing ty
            val jty = extract_judge_typing ty
            val () =
                case (#3 jty) of
                    CBinOp (CBTypeProd, t1, t2) =>
                    let
                        val () = assert (#1 jty = ctx)
                        val () = assert (#2 jty = e)
                        val () = assert (t = (case p of ProjFst => t1 | ProjSnd => t2))
                        val () = assert (#4 jty = i)
                    in
                        ()
                    end
                  | _ => assert false
        in
            ()
        end
      | TyInj ((ctx, EUnOp (EUInj inj, e), CBinOp (CBTypeSum, t1, t2), i), ty, kd) =>
        let
            val () = check_typing ty
            val () = check_kinding kd
            val jty = extract_judge_typing ty
            val jkd = extract_judge_kinding kd
            val () = assert (#1 jty = ctx)
            val () = assert (#2 jty = e)
            val () = assert (#3 jty = (case inj of InjInl => t1 | InjInr => t2))
            val () = assert (#4 jty = i)
            val () = assert (#1 jkd = fst ctx)
            val () = assert (#2 jkd = (case inj of InjInl => t2 | InjInr => t1))
            val () = assert (#3 jkd = KType)
        in
            ()
        end
      | TyCase ((ctx as (kctx, tctx), ECase (e, e1, e2), t, CBinOp (CBTimeAdd, i, CBinOp (CBTimeMax, i1, i2))), ty1, ty2, ty3) =>
        let
            val () = check_typing ty1
            val () = check_typing ty2
            val () = check_typing ty3
            val jty1 = extract_judge_typing ty1
            val jty2 = extract_judge_typing ty2
            val jty3 = extract_judge_typing ty3
            val () =
                case (#3 jty1) of
                    CBinOp (CBTypeSum, t1, t2) =>
                    let
                        val () = assert (#1 jty1 = ctx)
                        val () = assert (#2 jty1 = e)
                        val () = assert (#4 jty1 = i)
                        val () = assert (#1 jty2 = (kctx, t1 :: tctx))
                        val () = assert (#2 jty2 = e1)
                        val () = assert (#3 jty2 = t)
                        val () = assert (#4 jty2 = i1)
                        val () = assert (#1 jty3 = (kctx, t2 :: tctx))
                        val () = assert (#2 jty3 = e2)
                        val () = assert (#3 jty3 = t)
                        val () = assert (#4 jty3 = i2)
                    in
                        ()
                    end
                  | _ => assert false
        in
            ()
        end
      | TyNew ((ctx, EUnOp (EUNew, e), CRef t, i), ty) =>
        let
            val () = check_typing ty
            val jty = extract_judge_typing ty
            val () = assert (#1 jty = ctx)
            val () = assert (#2 jty = e)
            val () = assert (#3 jty = t)
            val () = assert (#4 jty = i)
        in
            ()
        end
      | TyRead ((ctx, EUnOp (EURead, e), t, i), ty) =>
        let
            val () = check_typing ty
            val jty = extract_judge_typing ty
            val () = assert (#1 jty = ctx)
            val () = assert (#2 jty = e)
            val () = assert (#3 jty = CRef t)
            val () = assert (#4 jty = i)
        in
            ()
        end
      | TyWrite ((ctx, EBinOp (EBWrite, e1, e2), CConst CCTypeUnit, CBinOp (CBTimeAdd, i1, i2)), ty1, ty2) =>
        let
            val () = check_typing ty1
            val () = check_typing ty2
            val jty1 = extract_judge_typing ty1
            val jty2 = extract_judge_typing ty2
            val () = assert (#1 jty1 = ctx)
            val () = assert (#2 jty1 = e1)
            val () = assert (#3 jty1 = CRef (#3 jty2))
            val () = assert (#4 jty1 = i1)
            val () = assert (#1 jty2 = ctx)
            val () = assert (#2 jty2 = e2)
            val () = assert (#4 jty2 = i2)
        in
            ()
        end
      | TySubTy ((ctx as (kctx, tctx), e, t2, i2), ty, te) =>
        let
            val () = check_typing ty
            val () = check_tyeq te
            val jty = extract_judge_typing ty
            val jte = extract_judge_tyeq te
            val () = assert (#1 jty = ctx)
            val () = assert (#2 jty = e)
            val () = assert (#1 jte = kctx)
            val () = assert (#2 jte = #3 jty)
            val () = assert (#3 jte = t2)
            val () = assert (#4 jty = i2)
        in
            ()
        end
      | TySubTi ((ctx as (kctx, tctx), e, t2, i2), ty, pr) =>
        let
            val () = check_typing ty
            val () = check_proping pr
            val jty = extract_judge_typing ty
            val jpr = extract_judge_proping pr
            val () = assert (#1 jty = ctx)
            val () = assert (#2 jty = e)
            val () = assert (#3 jty = t2)
            val () = assert (#1 jpr = kctx)
            val () = assert (#2 jpr = TLe (#4 jty, i2))
        in
            ()
        end
      | TyLet ((ctx as (kctx, tctx), ELet (e1, e2), t2, CBinOp (CBTimeAdd, i1, i2)), ty1, ty2) =>
        let
            val () = check_typing ty1
            val () = check_typing ty2
            val jty1 = extract_judge_typing ty1
            val jty2 = extract_judge_typing ty2
            val () = assert (#1 jty1 = ctx)
            val () = assert (#2 jty1 = e1)
            val () = assert (#4 jty1 = i1)
            val () = assert (#1 jty2 = (kctx, #3 jty1 :: tctx))
            val () = assert (#2 jty2 = e2)
            val () = assert (#3 jty2 = t2)
            val () = assert (#4 jty2 = i2)
        in
            ()
        end
      | TyHalt ((ctx, EHalt e, CTypeUnit, i), ty) =>
        let
            val () = check_typing ty
            val jty = extract_judge_typing ty
            val () = assert (#1 jty = ctx)
            val () = assert (#2 jty = e)
            val () = assert (#4 jty = i)
        in
            ()
        end
      | TyPrimBinOp ((ctx, EBinOp (EBPrim opr, e1, e2), t, CBinOp (CBTimeAdd, i1, i2)), ty1, ty2) =>
        let
            val () = check_typing ty1
            val () = check_typing ty2
            val jty1 = extract_judge_typing ty1
            val jty2 = extract_judge_typing ty2
            val () = assert (#1 jty1 = ctx)
            val () = assert (#2 jty1 = e1)
            val () = assert (#3 jty1 = pebinop_arg1_type opr)
            val () = assert (#4 jty1 = i1)
            val () = assert (#1 jty2 = ctx)
            val () = assert (#2 jty2 = e2)
            val () = assert (#3 jty2 = pebinop_arg2_type opr)
            val () = assert (#4 jty2 = i2)
            val () = assert (t = pebinop_result_type opr)
        in
            ()
        end
      | _ => raise CheckFail)
                      handle CheckFail =>
                             let
                                 val jty = extract_judge_typing ty
                             in
                                 println $ "typing: " ^ str_expr (#2 jty) ^ " " ^ str_cstr (#3 jty) ^ " " ^ str_cstr (#4 jty)
                             end
end
