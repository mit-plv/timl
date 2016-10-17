functor MicroTiMLHoisted(Time : SIG_TIME) =
struct
  structure DerivChecker = DerivChecker(Time)
  open DerivChecker

  open Util

  infixr 0 $

  datatype atom_expr =
    AEVar of var
  | AEConst of expr_const
  | AEFuncPointer of nat

  and complex_expr =
    CEUnOp of expr_un_op * atom_expr
  | CEBinOp of expr_bin_op * atom_expr * atom_expr
  | CECase of atom_expr * hoisted_expr * hoisted_expr
  | CEAppC of atom_expr * cstr
  | CEPack of cstr * atom_expr
  | CEAtom of atom_expr

  and hoisted_expr =
    HELet of complex_expr * hoisted_expr
  | HEUnpack of complex_expr * hoisted_expr
  | HEComplex of complex_expr

  and func_expr =
    FEFix of nat * hoisted_expr

  type fctx = cstr list
  type ctx = fctx * kctx * tctx

  type atom_typing_judgement = ctx * atom_expr * cstr * cstr
  type complex_typing_judgement = ctx * complex_expr * cstr * cstr
  type hoisted_typing_judgement = ctx * hoisted_expr * cstr * cstr
  type func_typing_judgement = fctx * func_expr * cstr

  datatype atom_typing =
    ATyVar of atom_typing_judgement
  | ATyConst of atom_typing_judgement
  | ATyFuncPointer of atom_typing_judgement
  | ATySub of atom_typing_judgement * atom_typing * tyeq * proping

  and complex_typing =
    CTyProj of complex_typing_judgement * atom_typing
  | CTyInj of complex_typing_judgement * atom_typing * kinding
  | CTyFold of complex_typing_judgement * kinding * atom_typing
  | CTyUnfold of complex_typing_judgement * atom_typing
  | CTyNew of complex_typing_judgement * atom_typing
  | CTyRead of complex_typing_judgement * atom_typing
  | CTyApp of complex_typing_judgement * atom_typing * atom_typing
  | CTyPair of complex_typing_judgement * atom_typing * atom_typing
  | CTyWrite of complex_typing_judgement * atom_typing * atom_typing
  | CTyCase of complex_typing_judgement * atom_typing * hoisted_typing * hoisted_typing
  | CTyAppC of complex_typing_judgement * atom_typing * kinding
  | CTyPack of complex_typing_judgement * kinding * kinding * atom_typing
  | CTyAtom of complex_typing_judgement * atom_typing
  | CTySub of complex_typing_judgement * complex_typing * tyeq * proping

  and hoisted_typing =
    HTyLet of hoisted_typing_judgement * complex_typing * hoisted_typing
  | HTyUnpack of hoisted_typing_judgement * complex_typing * hoisted_typing
  | HTyComplex of hoisted_typing_judgement * complex_typing
  | HTySub of hoisted_typing_judgement * hoisted_typing * tyeq * proping

  and func_typing =
    FTyFix of func_typing_judgement * kinding * hoisted_typing

  datatype program =
    Program of func_expr list * hoisted_expr
  type program_judgement = program * cstr * cstr
  datatype program_typing =
    TyProgram of program_judgement * func_typing list * hoisted_typing

  fun CEApp (e1, e2) = CEBinOp (EBApp, e1, e2)
  fun CEFold e = CEUnOp (EUFold, e)
  fun CEUnfold e = CEUnOp (EUUnfold, e)
  fun CEPair (e1, e2) = CEBinOp (EBPair, e1, e2)
  fun CEProj (p, e) = CEUnOp (EUProj p, e)
  fun CEInj (inj, e) = CEUnOp (EUInj inj, e)
  fun CENew e = CEUnOp (EUNew, e)
  fun CERead e = CEUnOp (EURead, e)
  fun CEWrite (e1, e2) = CEBinOp (EBWrite, e1, e2)

  fun extract_judge_htyping ty =
    case ty of
      HTyLet (j, _, _) => j
    | HTyUnpack (j, _, _) => j
    | HTyComplex (j, _) => j
    | HTySub (j, _, _, _) => j

  fun extract_judge_atyping ty =
    case ty of
      ATyVar j => j
    | ATyConst j => j
    | ATyFuncPointer j => j
    | ATySub (j, _, _, _) => j

  fun extract_judge_ctyping ty =
    case ty of
      CTyProj (j, _) => j
    | CTyInj (j, _, _) => j
    | CTyFold (j, _, _) => j
    | CTyUnfold (j, _) => j
    | CTyNew (j, _) => j
    | CTyRead (j, _) => j
    | CTyApp (j, _, _) => j
    | CTyPair (j, _, _) => j
    | CTyWrite (j, _, _) => j
    | CTyCase (j, _, _, _) => j
    | CTyAppC (j, _, _) => j
    | CTyPack (j, _, _, _) => j
    | CTyAtom (j, _) => j
    | CTySub (j, _, _, _) => j

  fun extract_judge_ftyping ty =
    case ty of
      FTyFix (j, _, _) => j

  structure HoistedDerivChecker =
  struct
    fun check_atyping ty =
      (case ty of
         ATyVar ((fctx, kctx, tctx), AEVar x, t, T0) => assert (nth (tctx, x) = t)
       | ATyConst ((fctx, kctx, tctx), AEConst cn, t, T0) => assert (const_type cn = t)
       | ATyFuncPointer ((fctx, kctx, tctx), AEFuncPointer f, t, T0) => assert (nth (fctx, f) = t)
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
       | CTyApp ((ctx, CEBinOp (EBApp, e1, e2), t2, CBinOp (CBTimeAdd, CBinOp (CBTimeAdd, CBinOp (CBTimeAdd, i1, i2), T1), i)), ty1, ty2) =>
           let
             val () = check_atyping ty1
             val () = check_atyping ty2
             val jty1 = extract_judge_atyping ty1
             val jty2 = extract_judge_atyping ty2
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
       | CTyPair ((ctx, CEBinOp (EBPair, e1, e2), CBinOp (CBTypeProd, t1, t2), CBinOp (CBTimeAdd, i1, i2)), ty1, ty2) =>
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
       | CTyCase ((ctx as (fctx, kctx, tctx), CECase (e, e1, e2), t, CBinOp (CBTimeAdd, i, CBinOp (CBTimeMax, i1, i2))), ty1, ty2, ty3) =>
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
                   val () = assert (#3 jty2 = t)
                   val () = assert (#4 jty2 = i1)
                   val () = assert (#1 jty3 = (fctx, kctx, t2 :: tctx))
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
       | CTyAppC ((ctx as (fctx, kctx, tctx), CEAppC (e, c), t, i), ty, kd) =>
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
       | CTyPack ((ctx as (fctx, kctx, tctx), CEPack (c, e), CQuan (QuanExists, k, t1), i), kd1, kd2, ty) =>
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
         HTyLet ((ctx as (fctx, kctx, tctx), HELet (e1, e2), t2, CBinOp (CBTimeAdd, i1, i2)), ty1, ty2) =>
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
             val () = assert (#3 jty2 = t2)
             val () = assert (#4 jty2 = i2)
           in
             ()
           end
       | HTyUnpack ((ctx as (fctx, kctx, tctx), HEUnpack (e1, e2), t2, CBinOp (CBTimeAdd, i1, i2)), ty1, ty2) =>
           let
             val () = check_ctyping ty1
             val () = check_htyping ty2
             val jty1 = extract_judge_ctyping ty1
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
                   val () = assert (#3 jty2 = shift0_c_c t2)
                   val () = assert (#4 jty2 = shift0_c_c i2)
                 in
                   ()
                 end
               | _ => assert false
           in
             ()
           end
       | HTyComplex ((ctx, HEComplex e, t, i), ty) =>
           let
             val () = check_ctyping ty
             val jty = extract_judge_ctyping ty
             val () = assert (#1 jty = ctx)
             val () = assert (#2 jty = e)
             val () = assert (#3 jty = t)
             val () = assert (#4 jty = i)
           in
             ()
           end
       | HTySub ((ctx as (fctx, kctx, tctx), e, t2, i2), ty, te, pr) =>
           let
             val () = check_htyping ty
             val () = check_tyeq te
             val () = check_proping pr
             val jty = extract_judge_htyping ty
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
                 CArrow (t1, i, t2) =>
                 let
                   val () = assert (#1 jty = (fctx, ks, [t1, t]))
                   val () = assert (#2 jty = e)
                   val () = assert (#3 jty = t2)
                   val () = assert (#4 jty = i)
                 in
                   ()
                 end
               | _ => assert false
           in
             ()
           end)

    and check_program ty =
      (case ty of
         TyProgram ((Program (exprs, body), t, i), typings, ty) =>
           let
             val () = List.app check_ftyping typings
             val () = check_htyping ty
             val fctx = List.map (fn ty => #3 (extract_judge_ftyping ty)) typings
             val () = List.app (fn ty => assert ((#1 (extract_judge_ftyping ty)) = fctx)) typings
             val jty = extract_judge_htyping ty
             val () = assert (#1 jty = (fctx, [], []))
             val () = assert (#2 jty = body)
             val () = assert (#3 jty = t)
             val () = assert (#4 jty = i)
           in
             ()
           end)
  end

  structure Hoist =
  struct
    structure Helper =
    struct
      fun is_atom ty =
        case ty of
          TyVar _ => true
        | TyConst _ => true
        | TyFix _ => true
        | _ => false

      fun is_complex ty =
        is_atom ty orelse
        (case ty of
           TyApp _ => true
         | TyAppC _ => true
         | TyFold _ => true
         | TyUnfold _ => true
         | TyPack _ => true
         | TyPair _ => true
         | TyProj _ => true
         | TyInj _ => true
         | TyCase _ => true
         | TyNew _ => true
         | TyRead _ => true
         | TyWrite _ => true
         | _ => false)

      fun transform_typing_atom (ty : typing, funcs : func_typing list) =
        case ty of
          TyVar ((kctx, tctx), EVar x, t, i) => (ATyVar (([], kctx, tctx), AEVar x, t, i), funcs)
        | TyConst ((kctx, tctx), EConst cn, t, i) => (ATyConst (([], kctx, tctx), AEConst cn, t, i), funcs)
        | TyFix (((kctx, tctx), EFix (n, e), t, i), kd, ty) =>
            let
              val (ty, funcs) = transform_typing_hoisted (ty, funcs)
              val jty = extract_judge_htyping ty
            in
              (ATyFuncPointer (([], kctx, tctx), AEFuncPointer (length funcs), t, i), FTyFix (([], FEFix (n, #2 jty), t), kd, ty) :: funcs)
            end
        | TySub (((kctx, tctx), e, t, i), ty, te, pr) =>
            let
              val (ty, funcs) = transform_typing_atom (ty, funcs)
              val jty = extract_judge_atyping ty
            in
              (ATySub ((([], kctx, tctx), #2 jty, t, i), ty, te, pr), funcs)
            end
        | _ => raise (Impossible "transform_typing_atom")

      and transform_typing_complex (ty : typing, funcs : func_typing list) =
        case ty of
          TyApp (((kctx, tctx), EBinOp (EBApp, e1, e2), t, i), ty1, ty2) =>
            let
              val (ty1, funcs) = transform_typing_atom (ty1, funcs)
              val (ty2, funcs) = transform_typing_atom (ty2, funcs)
              val jty1 = extract_judge_atyping ty1
              val jty2 = extract_judge_atyping ty2
            in
              (CTyApp ((([], kctx, tctx), CEApp (#2 jty1, #2 jty2), t, i), ty1, ty2), funcs)
            end
        | TyAppC (((kctx, tctx), EAppC (e, c), t, i), ty, kd) =>
            let
              val (ty, funcs) = transform_typing_atom (ty, funcs)
              val jty = extract_judge_atyping ty
              val jkd = extract_judge_kinding kd
            in
              (CTyAppC ((([], kctx, tctx), CEAppC (#2 jty, #2 jkd), t, i), ty, kd), funcs)
            end
        | TyFold (((kctx, tctx), EUnOp (EUFold, e), t, i), kd, ty) =>
            let
              val (ty, funcs) = transform_typing_atom (ty, funcs)
              val jkd = extract_judge_kinding kd
              val jty = extract_judge_atyping ty
            in
              (CTyFold ((([], kctx, tctx), CEFold (#2 jty), t, i), kd, ty), funcs)
            end
        | TyUnfold (((kctx, tctx), EUnOp (EUUnfold, e), t, i), ty) =>
            let
              val (ty, funcs) = transform_typing_atom (ty, funcs)
              val jty = extract_judge_atyping ty
            in
              (CTyUnfold ((([], kctx, tctx), CEUnfold (#2 jty), t, i), ty), funcs)
            end
        | TyPack (((kctx, tctx), EPack (c, e), t, i), kd1, kd2, ty) =>
            let
              val (ty, funcs) = transform_typing_atom (ty, funcs)
              val jkd2 = extract_judge_kinding kd2
              val jty = extract_judge_atyping ty
            in
              (CTyPack ((([], kctx, tctx), CEPack (#2 jkd2, #2 jty), t, i), kd1, kd2, ty), funcs)
            end
        | TyPair (((kctx, tctx), EBinOp (EBPair, e1, e2), t, i), ty1, ty2) =>
            let
              val (ty1, funcs) = transform_typing_atom (ty1, funcs)
              val (ty2, funcs) = transform_typing_atom (ty2, funcs)
              val jty1 = extract_judge_atyping ty1
              val jty2 = extract_judge_atyping ty2
            in
              (CTyPair ((([], kctx, tctx), CEPair (#2 jty1, #2 jty2), t, i), ty1, ty2), funcs)
            end
        | TyProj (((kctx, tctx), EUnOp (EUProj p, e), t, i), ty) =>
            let
              val (ty, funcs) = transform_typing_atom (ty, funcs)
              val jty = extract_judge_atyping ty
            in
              (CTyProj ((([], kctx, tctx), CEProj (p, #2 jty), t, i), ty), funcs)
            end
        | TyInj (((kctx, tctx), EUnOp (EUInj inj, e), t, i), ty, kd) =>
            let
              val (ty, funcs) = transform_typing_atom (ty, funcs)
              val jty = extract_judge_atyping ty
            in
              (CTyInj ((([], kctx, tctx), CEInj (inj, #2 jty), t, i), ty, kd), funcs)
            end
        | TyCase (((kctx, tctx), ECase (e, e1, e2), t, i), ty, ty1, ty2) =>
            let
              val (ty, funcs) = transform_typing_atom (ty, funcs)
              val (ty1, funcs) = transform_typing_hoisted (ty1, funcs)
              val (ty2, funcs) = transform_typing_hoisted (ty2, funcs)
              val jty = extract_judge_atyping ty
              val jty1 = extract_judge_htyping ty1
              val jty2 = extract_judge_htyping ty2
            in
              (CTyCase ((([], kctx, tctx), CECase (#2 jty, #2 jty1, #2 jty2), t, i), ty, ty1, ty2), funcs)
            end
        | TyNew (((kctx, tctx), EUnOp (EUNew, e), t, i), ty) =>
            let
              val (ty, funcs) = transform_typing_atom (ty, funcs)
              val jty = extract_judge_atyping ty
            in
              (CTyNew ((([], kctx, tctx), CENew (#2 jty), t, i), ty), funcs)
            end
        | TyRead (((kctx, tctx), EUnOp (EURead, e), t, i), ty) =>
            let
              val (ty, funcs) = transform_typing_atom (ty, funcs)
              val jty = extract_judge_atyping ty
            in
              (CTyRead ((([], kctx, tctx), CERead (#2 jty), t, i), ty), funcs)
            end
        | TyWrite (((kctx, tctx), EBinOp (EBWrite, e1, e2), t, i), ty1, ty2) =>
            let
              val (ty1, funcs) = transform_typing_atom (ty1, funcs)
              val (ty2, funcs) = transform_typing_atom (ty2, funcs)
              val jty1 = extract_judge_atyping ty1
              val jty2 = extract_judge_atyping ty2
            in
              (CTyWrite ((([], kctx, tctx), CEWrite (#2 jty1, #2 jty2), t, i), ty1, ty2), funcs)
            end
        | TySub (((kctx, tctx), e, t, i), ty, te, pr) =>
            let
              val (ty, funcs) = transform_typing_complex (ty, funcs)
              val jty = extract_judge_ctyping ty
            in
              (CTySub ((([], kctx, tctx), #2 jty, t, i), ty, te, pr), funcs)
            end
        | _ =>
            if is_atom ty then
              let
                val (ty, funcs) = transform_typing_atom (ty, funcs)
                val jty = extract_judge_atyping ty
              in
                (CTyAtom ((#1 jty, CEAtom (#2 jty), #3 jty, #4 jty), ty), funcs)
              end
            else
              raise (Impossible "transform_typing_complex")

      and transform_typing_hoisted (ty : typing, funcs : func_typing list) =
        case ty of
          TyLet (((kctx, tctx), ELet (e1, e2), t, i), ty1, ty2) =>
            let
              val (ty1, funcs) = transform_typing_complex (ty1, funcs)
              val (ty2, funcs) = transform_typing_hoisted (ty2, funcs)
              val jty1 = extract_judge_ctyping ty1
              val jty2 = extract_judge_htyping ty2
            in
              (HTyLet ((([], kctx, tctx), HELet (#2 jty1, #2 jty2), t, i), ty1, ty2), funcs)
            end
        | TyUnpack (((kctx, tctx), EUnpack (e1, e2), t, i), ty1, ty2) =>
            let
              val (ty1, funcs) = transform_typing_complex (ty1, funcs)
              val (ty2, funcs) = transform_typing_hoisted (ty2, funcs)
              val jty1 = extract_judge_ctyping ty1
              val jty2 = extract_judge_htyping ty2
            in
              (HTyUnpack ((([], kctx, tctx), HEUnpack (#2 jty1, #2 jty2), t, i), ty1, ty2), funcs)
            end
        | TySub (((kctx, tctx), e, t, i), ty, te, pr) =>
            let
              val (ty, funcs) = transform_typing_hoisted (ty, funcs)
              val jty = extract_judge_htyping ty
            in
              (HTySub ((([], kctx, tctx), #2 jty, t, i), ty, te, pr), funcs)
            end
        | _ =>
            if is_complex ty then
              let
                val (ty, funcs) = transform_typing_complex (ty, funcs)
                val jty = extract_judge_ctyping ty
              in
                (HTyComplex ((#1 jty, HEComplex (#2 jty), #3 jty, #4 jty), ty), funcs)
              end
            else
              raise (Impossible "transform_typing_hoisted")

      fun set_fctx_atom fctx ty =
        case ty of
          ATyVar ((_, kctx, tctx), e, t, i) => ATyVar ((fctx, kctx, tctx), e, t, i)
        | ATyConst ((_, kctx, tctx), e, t, i) => ATyConst ((fctx, kctx, tctx), e, t, i)
        | ATyFuncPointer ((_, kctx, tctx), e, t, i) => ATyFuncPointer ((fctx, kctx, tctx), e, t, i)
        | ATySub (((_, kctx, tctx), e, t, i), ty, te, pr) => ATySub (((fctx, kctx, tctx), e, t, i), set_fctx_atom fctx ty, te, pr)

      and set_fctx_complex fctx ty =
        let
          fun replace ((_, kctx, tctx), e, t, i) = ((fctx, kctx, tctx), e, t, i)
          val on_atom = set_fctx_atom fctx
          val on_hoisted = set_fctx_hoisted fctx
          val on_complex = set_fctx_complex fctx
          fun inner ty =
            case ty of
              CTyProj (j, ty) => CTyProj (replace j, on_atom ty)
            | CTyInj (j, ty, kd) => CTyInj (replace j, on_atom ty, kd)
            | CTyFold (j, kd, ty) => CTyFold (replace j, kd, on_atom ty)
            | CTyUnfold (j, ty) => CTyUnfold (replace j, on_atom ty)
            | CTyNew (j, ty) => CTyNew (replace j, on_atom ty)
            | CTyRead (j, ty) => CTyRead (replace j, on_atom ty)
            | CTyApp (j, ty1, ty2) => CTyApp (replace j, on_atom ty1, on_atom ty2)
            | CTyPair (j, ty1, ty2) => CTyPair (replace j, on_atom ty1, on_atom ty2)
            | CTyWrite (j, ty1, ty2) => CTyWrite (replace j, on_atom ty1, on_atom ty2)
            | CTyCase (j, ty, ty1, ty2) => CTyCase (replace j, on_atom ty, on_hoisted ty1, on_hoisted ty2)
            | CTyAppC (j, ty, kd) => CTyAppC (replace j, on_atom ty, kd)
            | CTyPack (j, kd1, kd2, ty) => CTyPack (replace j, kd1, kd2, on_atom ty)
            | CTyAtom (j, ty) => CTyAtom (replace j, on_atom ty)
            | CTySub (j, ty, te, pr) => CTySub (replace j, on_complex ty, te, pr)
        in
          inner ty
        end

      and set_fctx_hoisted fctx ty =
        let
          fun replace ((_, kctx, tctx), e, t, i) = ((fctx, kctx, tctx), e, t, i)
          val on_complex = set_fctx_complex fctx
          val on_hoisted = set_fctx_hoisted fctx
          fun inner ty =
            case ty of
              HTyLet (j, ty1, ty2) => HTyLet (replace j, on_complex ty1, on_hoisted ty2)
            | HTyUnpack (j, ty1, ty2) => HTyUnpack (replace j, on_complex ty1, on_hoisted ty2)
            | HTyComplex (j, ty) => HTyComplex (replace j, on_complex ty)
            | HTySub (j, ty, te, kd) => HTySub (replace j, on_hoisted ty, te, kd)
        in
          inner ty
        end

      and set_fctx_func fctx ty =
        case ty of
          FTyFix ((_, e, t), kd, ty) => FTyFix ((fctx, e, t), kd, set_fctx_hoisted fctx ty)
    end

    fun hoist ty =
      let
        val (ty, funcs) = Helper.transform_typing_hoisted (ty, [])
        val funcs = List.rev funcs
        val fctx = List.map (fn func => #3 (extract_judge_ftyping func)) funcs
        val ty = Helper.set_fctx_hoisted fctx ty
        val funcs = List.map (Helper.set_fctx_func fctx) funcs
        val jty = extract_judge_htyping ty
        val program = Program (List.map (fn func => #2 (extract_judge_ftyping func)) funcs, #2 jty)
      in
        TyProgram ((program, #3 jty, #4 jty), funcs, ty)
      end
  end
end
