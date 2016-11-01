functor HoistedDerivCheckerFun(MicroTiMLHoistedDef : SIG_MICRO_TIML_HOISTED_DEF) =
struct
open Util
infixr 0 $

open MicroTiMLHoistedDef
structure DerivChecker = DerivCheckerFun(MicroTiMLDef)
open DerivChecker

fun check_atyping ty =
  (case ty of
       ATyVar ((fctx, kctx, tctx), AEVar x, t, T0) => assert (nth (tctx, x) = t)
     | ATyConst ((fctx, kctx, tctx), AEConst cn, t, T0) => assert (const_type cn = t)
     | ATyFuncPointer ((fctx, kctx, tctx), AEFuncPointer f, t, T0) => assert (nth (fctx, f) = t)
     | ATyPair ((ctx, AEPair (e1, e2), CBinOp (CBTypeProd, t1, t2), CBinOp (CBTimeAdd, i1, i2)), ty1, ty2) =>
       let
           val () = check_atyping ty1
           val () = check_atyping ty2
           val jty1 = extract_judge_atyping ty1
           val jty2 = extract_judge_atyping ty2
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
     | ATyAppC ((ctx as (fctx, kctx, tctx), AEAppC (e, c), t, i), ty, kd) =>
       let
           val () = check_atyping ty
           val () = check_kinding kd
           val jty = extract_judge_atyping ty
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
     | ATyAbsC ((ctx as (fctx, kctx, tctx), AEAbsC e, CQuan (QuanForall, k, t), T0), wk, ty) =>
       let
           val () = check_wfkind wk
           val () = check_atyping ty
           val jwk = extract_judge_wfkind wk
           val jty = extract_judge_atyping ty
           val () = assert (#1 jwk = kctx)
           val () = assert (#2 jwk = k)
           val () = assert (#1 jty = (fctx, k :: kctx, map shift0_c_c tctx))
           val () = assert (#2 jty = e)
           val () = assert (#3 jty = t)
           val () = assert (#4 jty = T0)
       in
           ()
       end
     | ATyPack ((ctx as (fctx, kctx, tctx), AEPack (c, e), CQuan (QuanExists, k, t1), i), kd1, kd2, ty) =>
       let
           val () = check_kinding kd1
           val () = check_kinding kd2
           val () = check_atyping ty
           val jkd1 = extract_judge_kinding kd1
           val jkd2 = extract_judge_kinding kd2
           val jty = extract_judge_atyping ty
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
     | ATySub ((ctx as (fctx, kctx, tctx), e, t2, i2), ty, te, pr) =>
       let
           val () = check_atyping ty
           val () = check_tyeq te
           val () = check_proping pr
           val jty = extract_judge_atyping ty
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
     | _ => assert false)

and check_ctyping ty =
    (case ty of
         CTyProj ((ctx as (fctx, kctx, tctx), CEUnOp (EUProj p, e), t, i), ty) =>
         let
             val () = check_atyping ty
             val jty = extract_judge_atyping ty
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
       | CTyInj ((ctx as (fctx, kctx, tctx), CEUnOp (EUInj inj, e), CBinOp (CBTypeSum, t1, t2), i), ty, kd) =>
         let
             val () = check_atyping ty
             val () = check_kinding kd
             val jty = extract_judge_atyping ty
             val jkd = extract_judge_kinding kd
             val () = assert (#1 jty = ctx)
             val () = assert (#2 jty = e)
             val () = assert (#3 jty = (case inj of InjInl => t1 | InjInr => t2))
             val () = assert (#4 jty = i)
             val () = assert (#1 jkd = kctx)
             val () = assert (#2 jkd = (case inj of InjInl => t2 | InjInr => t1))
             val () = assert (#3 jkd = KType)
         in
             ()
         end
       | CTyFold ((ctx as (fctx, kctx, tctx), CEUnOp (EUFold, e), t, i), kd, ty) =>
         let
             val () = check_kinding kd
             val () = check_atyping ty
             val jkd = extract_judge_kinding kd
             val jty = extract_judge_atyping ty
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
       | CTyUnfold ((ctx as (fctx, kctx, tctx), CEUnOp (EUUnfold, e), t', i), ty) =>
         let
             val () = check_atyping ty
             val jty = extract_judge_atyping ty
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
       | CTyNew ((ctx, CEUnOp (EUNew, e), CRef t, i), ty) =>
         let
             val () = check_atyping ty
             val jty = extract_judge_atyping ty
             val () = assert (#1 jty = ctx)
             val () = assert (#2 jty = e)
             val () = assert (#3 jty = t)
             val () = assert (#4 jty = i)
         in
             ()
         end
       | CTyRead ((ctx, CEUnOp (EURead, e), t, i), ty) =>
         let
             val () = check_atyping ty
             val jty = extract_judge_atyping ty
             val () = assert (#1 jty = ctx)
             val () = assert (#2 jty = e)
             val () = assert (#3 jty = CRef t)
             val () = assert (#4 jty = i)
         in
             ()
         end
       | CTyWrite ((ctx, CEBinOp (EBWrite, e1, e2), CConst CCTypeUnit, CBinOp (CBTimeAdd, i1, i2)), ty1, ty2) =>
         let
             val () = check_atyping ty1
             val () = check_atyping ty2
             val jty1 = extract_judge_atyping ty1
             val jty2 = extract_judge_atyping ty2
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
       | CTyAtom ((ctx, CEAtom e, t, i), ty) =>
         let
             val () = check_atyping ty
             val jty = extract_judge_atyping ty
             val () = assert (#1 jty = ctx)
             val () = assert (#2 jty = e)
             val () = assert (#3 jty = t)
             val () = assert (#4 jty = i)
         in
             ()
         end
       | CTySub ((ctx as (fctx, kctx, tctx), e, t2, i2), ty, te, pr) =>
         let
             val () = check_ctyping ty
             val () = check_tyeq te
             val () = check_proping pr
             val jty = extract_judge_ctyping ty
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
       | _ => assert false)

and check_htyping ty =
    (case ty of
         HTyLet ((ctx as (fctx, kctx, tctx), HELet (e1, e2), CBinOp (CBTimeAdd, i1, i2)), ty1, ty2) =>
         let
             val () = check_ctyping ty1
             val () = check_htyping ty2
             val jty1 = extract_judge_ctyping ty1
             val jty2 = extract_judge_htyping ty2
             val () = assert (#1 jty1 = ctx)
             val () = assert (#2 jty1 = e1)
             val () = assert (#4 jty1 = i1)
             val () = assert (#1 jty2 = (fctx, kctx, #3 jty1 :: tctx))
             val () = assert (#2 jty2 = e2)
             val () = assert (#3 jty2 = i2)
         in
             ()
         end
       | HTyUnpack ((ctx as (fctx, kctx, tctx), HEUnpack (e1, e2), CBinOp (CBTimeAdd, i1, i2)), ty1, ty2) =>
         let
             val () = check_atyping ty1
             val () = check_htyping ty2
             val jty1 = extract_judge_atyping ty1
             val jty2 = extract_judge_htyping ty2
             val () =
                 case (#3 jty1) of
                     CQuan (QuanExists, k, t) =>
                     let
                         val () = assert (#1 jty1 = ctx)
                         val () = assert (#2 jty1 = e1)
                         val () = assert (#4 jty1 = i1)
                         val () = assert (#1 jty2 = (fctx, k :: kctx, t :: map shift0_c_c tctx))
                         val () = assert (#2 jty2 = e2)
                         val () = assert (#3 jty2 = shift0_c_c i2)
                     in
                         ()
                     end
                   | _ => assert false
         in
             ()
         end
       | HTyApp ((ctx, HEApp (e1, e2), CBinOp (CBTimeAdd, CBinOp (CBTimeAdd, CBinOp (CBTimeAdd, i1, i2), T1), i)), ty1, ty2) =>
         let
             val () = check_atyping ty1
             val () = check_atyping ty2
             val jty1 = extract_judge_atyping ty1
             val jty2 = extract_judge_atyping ty2
             val () = assert (#1 jty1 = ctx)
             val () = assert (#2 jty1 = e1)
             val () = assert (#3 jty1 = CArrow (#3 jty2, i, CTypeUnit))
             val () = assert (#4 jty1 = i1)
             val () = assert (#1 jty2 = ctx)
             val () = assert (#2 jty2 = e2)
             val () = assert (#4 jty2 = i2)
         in
             ()
         end
       | HTyAppK ((ctx, HEApp (e1, e2), CBinOp (CBTimeAdd, CBinOp (CBTimeAdd, i1, i2), i)), ty1, ty2) =>
         let
             val () = check_atyping ty1
             val () = check_atyping ty2
             val jty1 = extract_judge_atyping ty1
             val jty2 = extract_judge_atyping ty2
             val () = assert (#1 jty1 = ctx)
             val () = assert (#2 jty1 = e1)
             val () = assert (#3 jty1 = CArrow (#3 jty2, i, CTypeUnit))
             val () = assert (#4 jty1 = i1)
             val () = assert (#1 jty2 = ctx)
             val () = assert (#2 jty2 = e2)
             val () = assert (#4 jty2 = i2)
         in
             ()
         end
       | HTyCase ((ctx as (fctx, kctx, tctx), HECase (e, e1, e2), CBinOp (CBTimeAdd, i, CBinOp (CBTimeMax, i1, i2))), ty1, ty2, ty3) =>
         let
             val () = check_atyping ty1
             val () = check_htyping ty2
             val () = check_htyping ty3
             val jty1 = extract_judge_atyping ty1
             val jty2 = extract_judge_htyping ty2
             val jty3 = extract_judge_htyping ty3
             val () =
                 case (#3 jty1) of
                     CBinOp (CBTypeSum, t1, t2) =>
                     let
                         val () = assert (#1 jty1 = ctx)
                         val () = assert (#2 jty1 = e)
                         val () = assert (#4 jty1 = i)
                         val () = assert (#1 jty2 = (fctx, kctx, t1 :: tctx))
                         val () = assert (#2 jty2 = e1)
                         val () = assert (#3 jty2 = i1)
                         val () = assert (#1 jty3 = (fctx, kctx, t2 :: tctx))
                         val () = assert (#2 jty3 = e2)
                         val () = assert (#3 jty3 = i2)
                     in
                         ()
                     end
                   | _ => assert false
         in
             ()
         end
       | HTyHalt ((ctx as (fctx, kctx, tctx), HEHalt e, i), ty) =>
         let
             val () = check_atyping ty
             val jty = extract_judge_atyping ty
             val () = assert (#1 jty = ctx)
             val () = assert (#2 jty = e)
             val () = assert (#4 jty = i)
         in
             ()
         end
       | HTySub ((ctx as (fctx, kctx, tctx), e, i2), ty, pr) =>
         let
             val () = check_htyping ty
             val () = check_proping pr
             val jty = extract_judge_htyping ty
             val jpr = extract_judge_proping pr
             val () = assert (#1 jty = ctx)
             val () = assert (#2 jty = e)
             val () = assert (#1 jpr = kctx)
             val () = assert (#2 jpr = TLe (#3 jty, i2))
         in
             ()
         end
       | _ => assert false)

and check_ftyping ty =
    (case ty of
         FTyFix ((fctx, FEFix (n, e), t), kd, ty) =>
         let
             val () = check_kinding kd
             val () = check_htyping ty
             val jkd = extract_judge_kinding kd
             val jty = extract_judge_htyping ty
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
                     CArrow (t1, i, CTypeUnit) =>
                     let
                         val () = assert (#1 jty = (fctx, ks, [t1, t]))
                         val () = assert (#2 jty = e)
                         val () = assert (#3 jty = i)
                     in
                         ()
                     end
                   | _ => assert false
         in
             ()
         end)

and check_program ty =
    (case ty of
         TyProgram ((Program (exprs, body), i), typings, ty) =>
         let
             val () = List.app check_ftyping typings
             val () = check_htyping ty
             val fctx = List.map (fn ty => #3 (extract_judge_ftyping ty)) typings
             val () = List.app (fn ty => assert ((#1 (extract_judge_ftyping ty)) = fctx)) typings
             val jty = extract_judge_htyping ty
             val () = assert (#1 jty = (fctx, [], []))
             val () = assert (#2 jty = body)
             val () = assert (#3 jty = i)
         in
             ()
         end)
end
