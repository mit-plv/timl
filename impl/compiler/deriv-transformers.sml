functor DerivTransformers(Time : SIG_TIME) =
struct
  structure MicroTiML = MicroTiML(Time)
  open MicroTiML

  structure AstTransformers = AstTransformers(Time)
  open AstTransformers

  open Util

  infixr 0 $

  structure DerivChecker =
  struct
    exception CheckFail

    open ShiftCstr
    open SubstCstr
    open List

    open PlainPrinter

    fun assert p = if p then () else raise CheckFail

    fun check_proping _ = ()

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
        KdVar (kctx, CVar x, k) => assert (k = shift_c_k (1 + x) 0 (nth (kctx, x)))
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
      | KdRec ((kctx, CRec (k, c), k'), wk, kd) =>
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
      | TyEqNatEq ((kctx, i1, i2), pr) =>
          let
            val () = check_proping pr
            val jpr = extract_judge_proping pr
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
      | TyEqRec ((kctx, CRec (k1, t1), CRec (k2, t2)), ke, te) =>
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
          println $ "tyeq: " ^ str_cstr (#2 jte) ^ " " ^ str_cstr (#3 jte)
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
            val (t, ks) = unfold_CForalls t []
            val () = assert (n = length ks)
            val () =
              case t of
                CArrow (t1, i, t2) =>
                  let
                    val () = assert (#1 jty = (ks, [t1]))
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
                CRec (k, t2) =>
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
                CRec (k, t1) =>
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
      | TySub ((ctx as (kctx, tctx), e, t2, i2), ty, te, pr) =>
          let
            val () = check_typing ty
            val () = check_tyeq te
            val () = check_proping pr
            val jty = extract_judge_typing ty
            val jte = extract_judge_tyeq te
            val jpr = extract_judge_proping pr
            val () = assert (#1 jty = ctx)
            val () = assert (#2 jty = e)
            val () = assert (#1 jte = kctx)
            val () = assert (#2 jte = #3 jty)
            val () = assert (#3 jte = t2)
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
      | _ => raise CheckFail)
      handle CheckFail =>
        let
          val jty = extract_judge_typing ty
        in
          println $ "typing: " ^ str_expr (#2 jty) ^ " " ^ str_cstr (#3 jty) ^ " " ^ str_cstr (#4 jty)
        end
  end

  structure ShiftCtx =
  struct
    structure Helper = DerivGenericOnlyDownTransformer(
    struct
      open ShiftCstr
      open ShiftExpr
      open List

      val subst_c_c = SubstCstr.subst_c_c

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

    fun shift0_ctx_ty ctxd = shift_ctx_ty ctxd (0, 0)
    fun shift0_ctx_kd ctxd = shift_ctx_kd ctxd (0, 0)
    fun shift0_ctx_te ctxd = shift_ctx_te ctxd (0, 0)
  end

  structure DerivAssembler = DerivAssembler(
  struct
    val shift_c_k = ShiftCstr.shift_c_k
    val shift_c_c = ShiftCstr.shift_c_c

    val subst_c_c = SubstCstr.subst_c_c
  end)

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

      val shift_c_c = ShiftCstr.shift_c_c
      val shift_c_k = ShiftCstr.shift_c_k

      val subst_c_c = SubstCstr.subst_c_c

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

      val shift_c_c = ShiftCstr.shift_c_c
      val shift_c_k = ShiftCstr.shift_c_k

      val subst_c_c = SubstCstr.subst_c_c

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
  end

  structure CloConv =
  struct
    structure Helper = DerivGenericOnlyDownTransformer(
    struct
      type down = unit

      val shift_c_k = ShiftCstr.shift_c_k
      val shift_c_c = ShiftCstr.shift_c_c

      val subst_c_c = SubstCstr.subst_c_c

      fun add_kind (_, ()) = ()
      fun add_type (_, ()) = ()

      fun on_pr_leaf (pr, ()) = pr
      fun on_ke_leaf (ke, ()) = ke
      fun on_kd_leaf (kd, ()) = kd
      fun on_wk_leaf (wk, ()) = wk
      fun on_wp_leaf (wp, ()) = wp
      fun on_te_leaf (te, ()) = te
      fun on_ty_leaf (ty, ()) = ty

      fun transformer_typing (on_typing, on_kinding, on_wfkind, on_tyeq, on_proping) (ty, ()) =
        case ty of
          TyAbs (j, kd, ty) =>
            let
              val ty = on_typing (ty, ())
            in
              NONE
            end
        | _ => NONE

      fun transformer_proping _ = NONE
      fun transformer_kdeq _ _ = NONE
      fun transformer_kinding _ _ = NONE
      fun transformer_wfkind _ _ = NONE
      fun transformer_wfprop _ _ = NONE
      fun transformer_tyeq _ _ = NONE
    end)
  end

  structure ANF =
  struct
    open DerivAssembler

    open ShiftCstr
    open ShiftCtx
    open List

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
            val pr = PrAdmit (kctx, TLe (i, i))
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

    fun normalize_deriv ty = normalize ty (fn (ty, (kctxd, tctxd)) => ty)

    and normalize ty cont =
      case ty of
        TyVar j => cont (ty, ([], []))
      | TyApp (j, ty1, ty2) =>
          normalize_name ty1
            (fn (ty1, d1 as (kctxd1, tctxd1)) =>
               normalize_name (shift0_ctx_ty d1 ty2)
                 (fn (ty2, d2 as (kctxd2, tctxd2)) =>
                    let
                      val ty1 = shift0_ctx_ty d2 ty1
                    in
                      cont (TyApp (as_TyApp ty1 ty2, ty1, ty2), concat_ctx (d2, d1))
                    end))
      | TyAbs (j, kd, ty) =>
          let
            val ty = normalize_deriv ty
            val (t1, i, t2) = extract_c_arrow (#3 j)
            val jty = extract_judge_typing ty
            val te = gen_tyeq_refl (fst $ #1 jty) (#3 jty)
            val pr = PrAdmit (fst $ #1 jty, TLe (#4 jty, i))
            val ty = TySub (as_TySub ty te pr, ty, te, pr)
          in
            cont (TyAbs (as_TyAbs kd ty, kd, ty), ([], []))
          end
      | TyAppC (j, ty, kd) =>
          normalize_name ty
            (fn (ty, d as (kctxd, tctxd)) =>
               let
                 val kd = shift0_ctx_kd d kd
               in
                 cont (TyAppC (as_TyAppC ty kd, ty, kd), d)
               end)
      | TyAbsC (j, wk, ty) =>
          let
            val ty = normalize_deriv ty
          in
            cont (TyAbsC (as_TyAbsC wk ty, wk, ty), ([], []))
          end
      | TyRec (j, kd, ty) =>
          let
            val ty = normalize_deriv ty
          in
            cont (TyRec (as_TyRec kd ty, kd, ty), ([], []))
          end
      | TyFold (j, kd, ty) =>
          normalize_name ty
            (fn (ty, d as (kctxd, tctxd)) =>
               let
                 val kd = shift0_ctx_kd d kd
               in
                 cont (TyFold (as_TyFold kd ty, kd, ty), d)
               end)
      | TyUnfold (j, ty) =>
          normalize_name ty
            (fn (ty, d as (kctxd, tctxd)) => cont (TyUnfold (as_TyUnfold ty, ty), d))
      | TyPack (j, kd1, kd2, ty) =>
          normalize_name ty
            (fn (ty, d as (kctxd, tctxd)) =>
               let
                 val kd1 = shift0_ctx_kd d kd1
                 val kd2 = shift0_ctx_kd d kd2
               in
                 cont (TyPack (as_TyPack kd1 kd2 ty, kd1, kd2, ty), d)
               end)
      | TyUnpack (j, ty1, ty2) =>
          normalize ty1
            (fn (ty1, d1 as (kctxd1, tctxd1)) =>
               let
                 val jty1 = extract_judge_typing ty1
                 val (_, k, t) = extract_c_quan (#3 jty1)
                 val ty2 = shift_ctx_ty d1 (1, 1) ty2
                 val jty2 = extract_judge_typing ty2
                 val ty2 = normalize ty2 (fn (ty2, d2 as (kctxd2, tctxd2)) => cont (ty2, concat_ctx (d2, concat_ctx (([k], [t]), d1))))
                 val te2 = gen_tyeq_refl (fst $ #1 jty2) (#3 jty2)
                 val pr2 = PrAdmit (fst $ #1 jty2, TLe (#4 (extract_judge_typing ty2), #4 jty2))
                 val ty2 = TySub (as_TySub ty2 te2 pr2, ty2, te2, pr2)
               in
                 TyUnpack (as_TyUnpack ty1 ty2, ty1, ty2)
               end)
      | TyConst j => cont (ty, ([], []))
      | TyPair (j, ty1, ty2) =>
          normalize_name ty1
            (fn (ty1, d1 as (kctxd1, tctxd1)) =>
               normalize_name (shift0_ctx_ty d1 ty2)
                 (fn (ty2, d2 as (kctxd2, tctxd2)) =>
                    let
                      val ty1 = shift0_ctx_ty d2 ty1
                    in
                      cont (TyPair (as_TyPair ty1 ty2, ty1, ty2), concat_ctx (d2, d1))
                    end))
      | TyProj (j, ty) =>
          normalize_name ty
            (fn (ty, d as (kctxd, tctxd)) =>
               let
                 val (p, _) = extract_e_proj (#2 j)
               in
                 cont (TyProj (as_TyProj p ty, ty), d)
               end)
      | TyInj (j, ty, kd) =>
          normalize_name ty
            (fn (ty, d as (kctxd, tctxd)) =>
               let
                 val (inj, _) = extract_e_inj (#2 j)
                 val kd = shift0_ctx_kd d kd
               in
                 cont (TyInj (as_TyInj inj ty kd, ty, kd), d)
               end)
      | TyCase (j, ty1, ty2, ty3) =>
          normalize_name ty1
            (fn (ty1, d1 as (kctxd, tctxd)) =>
               let
                 val ty2 = shift_ctx_ty d1 (0, 1) ty2
                 val ty3 = shift_ctx_ty d1 (0, 1) ty3
                 val ty2 = normalize_deriv ty2
                 val ty3 = normalize_deriv ty3
                 val jty2 = extract_judge_typing ty2
                 val jty3 = extract_judge_typing ty3
               in
                 cont (TyCase (as_TyCase ty1 ty2 ty3, ty1, ty2, ty3), d1)
               end)
      | TyNew (j, ty) =>
          normalize_name ty
            (fn (ty, d as (kctxd, tctxd)) => cont (TyNew (as_TyNew ty, ty), d))
      | TyRead (j, ty) =>
          normalize_name ty
            (fn (ty, d as (kctxd, tctxd)) => cont (TyRead (as_TyRead ty, ty), d))
      | TyWrite (j, ty1, ty2) =>
          normalize_name ty1
            (fn (ty1, d1 as (kctxd1, tctxd1)) =>
               normalize_name (shift0_ctx_ty d1 ty2)
                 (fn (ty2, d2 as (kctxd2, tctxd2)) =>
                    let
                      val ty1 = shift0_ctx_ty d2 ty1
                      val jty1 = extract_judge_typing ty1
                      val tylet1 = TyConst (#1 jty1, EConst ECTT, CTypeUnit, T0)
                      val tylet2 = cont (TyVar ((fst $ #1 jty1, CTypeUnit :: (snd $ #1 jty1)), EVar 0, CTypeUnit, T0), concat_ctx (([], [CTypeUnit]), concat_ctx (d2, d1)))
                    in
                      TyLet (as_TyLet tylet1 tylet2, tylet1, tylet2)
                    end))
      | TyLet (j, ty1, ty2) =>
          normalize ty1
            (fn (ty1, d1 as (kctxd1, tctxd1)) =>
               let
                 val jty1 = extract_judge_typing ty1
                 val ty2 = shift_ctx_ty d1 (0, 1) ty2
                 val ty2 =
                   normalize ty2 (fn (ty2, d2 as (kctxd2, tctxd2)) => cont (ty2, concat_ctx (d2, concat_ctx (([], [#3 jty1]), d1))))
               in
                 TyLet (as_TyLet ty1 ty2, ty1, ty2)
               end)
      | TySub (j, ty, te, pr) =>
          normalize ty
            (fn (ty, d as (kctxd, tctxd)) =>
               let
                 val te = shift0_ctx_te d te
                 val jty = extract_judge_typing ty
                 val pr = PrAdmit (fst $ #1 jty, TLe (#4 jty, #4 jty))
               in
                 cont (TySub (as_TySub ty te pr, ty, te, pr), d)
               end)
      | TyFix (j, kd, ty) =>
          let
            val ty = normalize_deriv ty
          in
            cont (TyFix (as_TyFix (#1 j) kd ty, kd, ty), ([], []))
          end

    and normalize_name ty cont =
      normalize ty
        (fn (ty, d as (kctxd, tctxd)) =>
           let
             val jty = extract_judge_typing ty
           in
             if is_atomic (#2 jty) then
               cont (ty, d)
             else
               let
                 val t = #3 jty
                 val tylet1 = ty
                 val tylet2 = cont (TyVar ((fst $ #1 jty, t :: (snd $ #1 jty)), EVar 0, t, T0), concat_ctx (([], [t]), d))
               in
                 TyLet (as_TyLet tylet1 tylet2, tylet1, tylet2)
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
  end
end
