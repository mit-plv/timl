functor HoistedDerivTransformersFun(MicroTiMLHoistedDef : SIG_MICRO_TIML_HOISTED_DEF) =
struct
open Util
infixr 0 $

open MicroTiMLHoistedDef
open MicroTiMLDef
structure MicroTiMLUtil = MicroTiMLUtilFun(MicroTiMLDef)
open MicroTiMLUtil

structure Hoist =
struct
structure Helper =
struct
fun is_atom ty =
  case ty of
      TyVar _ => true
    | TyConst _ => true
    | TyFix _ => true
    | TyPair _ => true
    | TyAppC _ => true
    | TyAbsC _ => true
    | TyPack _ => true
    | _ => false

fun is_complex ty =
  is_atom ty orelse
  (case ty of
       TyProj _ => true
     | TyInj _ => true
     | TyFold _ => true
     | TyUnfold _ => true
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
    | TyPair (((kctx, tctx), EBinOp (EBPair, e1, e2), t, i), ty1, ty2) =>
      let
          val (ty1, funcs) = transform_typing_atom (ty1, funcs)
          val (ty2, funcs) = transform_typing_atom (ty2, funcs)
          val jty1 = extract_judge_atyping ty1
          val jty2 = extract_judge_atyping ty2
      in
          (ATyPair ((([], kctx, tctx), AEPair (#2 jty1, #2 jty2), t, i), ty1, ty2), funcs)
      end
    | TyAppC (((kctx, tctx), EAppC (e, c), t, i), ty, kd) =>
      let
          val (ty, funcs) = transform_typing_atom (ty, funcs)
          val jty = extract_judge_atyping ty
      in
          (ATyAppC ((([], kctx, tctx), AEAppC (#2 jty, c), t, i), ty, kd), funcs)
      end
    | TyAbsC (((kctx, tctx), EAbsC e, t, i), wk, ty) =>
      let
          val (ty, funcs) = transform_typing_atom (ty, funcs)
          val jty = extract_judge_atyping ty
      in
          (ATyAbsC ((([], kctx, tctx), AEAbsC (#2 jty), t, i), wk, ty), funcs)
      end
    | TyPack (((kctx, tctx), EPack (c, e), t, i), kd1, kd2, ty) =>
      let
          val (ty, funcs) = transform_typing_atom (ty, funcs)
          val jty = extract_judge_atyping ty
      in
          (ATyPack ((([], kctx, tctx), AEPack (c, #2 jty), t, i), kd1, kd2, ty), funcs)
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
        TyProj (((kctx, tctx), EUnOp (EUProj p, e), t, i), ty) =>
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
        TyLet (((kctx, tctx), ELet (e1, e2), CTypeUnit, i), ty1, ty2) =>
        let
            val (ty1, funcs) = transform_typing_complex (ty1, funcs)
            val (ty2, funcs) = transform_typing_hoisted (ty2, funcs)
            val jty1 = extract_judge_ctyping ty1
            val jty2 = extract_judge_htyping ty2
        in
            (HTyLet ((([], kctx, tctx), HELet (#2 jty1, #2 jty2), i), ty1, ty2), funcs)
        end
      | TyUnpack (((kctx, tctx), EUnpack (e1, e2), CTypeUnit, i), ty1, ty2) =>
        let
            val (ty1, funcs) = transform_typing_atom (ty1, funcs)
            val (ty2, funcs) = transform_typing_hoisted (ty2, funcs)
            val jty1 = extract_judge_atyping ty1
            val jty2 = extract_judge_htyping ty2
        in
            (HTyUnpack ((([], kctx, tctx), HEUnpack (#2 jty1, #2 jty2), i), ty1, ty2), funcs)
        end
      | TyApp (((kctx, tctx), EBinOp (EBApp, e1, e2), CTypeUnit, i), ty1, ty2) =>
        let
            val (ty1, funcs) = transform_typing_atom (ty1, funcs)
            val (ty2, funcs) = transform_typing_atom (ty2, funcs)
            val jty1 = extract_judge_atyping ty1
            val jty2 = extract_judge_atyping ty2
        in
            (HTyApp ((([], kctx, tctx), HEApp (#2 jty1, #2 jty2), i), ty1, ty2), funcs)
        end
      | TyAppK (((kctx, tctx), EBinOp (EBApp, e1, e2), CTypeUnit, i), ty1, ty2) =>
        let
            val (ty1, funcs) = transform_typing_atom (ty1, funcs)
            val (ty2, funcs) = transform_typing_atom (ty2, funcs)
            val jty1 = extract_judge_atyping ty1
            val jty2 = extract_judge_atyping ty2
        in
            (HTyAppK ((([], kctx, tctx), HEApp (#2 jty1, #2 jty2), i), ty1, ty2), funcs)
        end
      | TyCase (((kctx, tctx), ECase (e, e1, e2), CTypeUnit, i), ty, ty1, ty2) =>
        let
            val (ty, funcs) = transform_typing_atom (ty, funcs)
            val (ty1, funcs) = transform_typing_hoisted (ty1, funcs)
            val (ty2, funcs) = transform_typing_hoisted (ty2, funcs)
            val jty = extract_judge_atyping ty
            val jty1 = extract_judge_htyping ty1
            val jty2 = extract_judge_htyping ty2
        in
            (HTyCase ((([], kctx, tctx), HECase (#2 jty, #2 jty1, #2 jty2), i), ty, ty1, ty2), funcs)
        end
      | TyHalt (((kctx, tctx), EHalt e, CTypeUnit, i), ty) =>
        let
            val (ty, funcs) = transform_typing_atom (ty, funcs)
            val jty = extract_judge_atyping ty
        in
            (HTyHalt ((([], kctx, tctx), HEHalt (#2 jty), i), ty), funcs)
        end
      | TySub (((kctx, tctx), e, CTypeUnit, i), ty, te, pr) =>
        let
            val (ty, funcs) = transform_typing_hoisted (ty, funcs)
            val jty = extract_judge_htyping ty
        in
            (HTySub ((([], kctx, tctx), #2 jty, i), ty, pr), funcs)
        end
      | _ => raise (Impossible "transform_typing_hoisted")

fun set_fctx_atom fctx ty =
  let
      fun replace ((_, kctx, tctx), e, t, i) = ((fctx, kctx, tctx), e, t, i)
      val on_atom = set_fctx_atom fctx
      fun inner ty =
        case ty of
            ATyVar j => ATyVar (replace j)
          | ATyConst j => ATyConst (replace j)
          | ATyFuncPointer j => ATyFuncPointer (replace j)
          | ATyPair (j, ty1, ty2) => ATyPair (replace j, on_atom ty1, on_atom ty2)
          | ATyAppC (j, ty, kd) => ATyAppC (replace j, on_atom ty, kd)
          | ATyAbsC (j, wk, ty) => ATyAbsC (replace j, wk, on_atom ty)
          | ATyPack (j, kd1, kd2, ty) => ATyPack (replace j, kd1, kd2, on_atom ty)
          | ATySub (j, ty, te, pr) => ATySub (replace j, on_atom ty, te, pr)
  in
      inner ty
  end

and set_fctx_complex fctx ty =
    let
        fun replace ((_, kctx, tctx), e, t, i) = ((fctx, kctx, tctx), e, t, i)
        val on_atom = set_fctx_atom fctx
        val on_complex = set_fctx_complex fctx
        fun inner ty =
          case ty of
              CTyProj (j, ty) => CTyProj (replace j, on_atom ty)
            | CTyInj (j, ty, kd) => CTyInj (replace j, on_atom ty, kd)
            | CTyFold (j, kd, ty) => CTyFold (replace j, kd, on_atom ty)
            | CTyUnfold (j, ty) => CTyUnfold (replace j, on_atom ty)
            | CTyNew (j, ty) => CTyNew (replace j, on_atom ty)
            | CTyRead (j, ty) => CTyRead (replace j, on_atom ty)
            | CTyWrite (j, ty1, ty2) => CTyWrite (replace j, on_atom ty1, on_atom ty2)
            | CTyAtom (j, ty) => CTyAtom (replace j, on_atom ty)
            | CTySub (j, ty, te, pr) => CTySub (replace j, on_complex ty, te, pr)
    in
        inner ty
    end

and set_fctx_hoisted fctx ty =
    let
        fun replace ((_, kctx, tctx), e, i) = ((fctx, kctx, tctx), e, i)
        val on_atom = set_fctx_atom fctx
        val on_complex = set_fctx_complex fctx
        val on_hoisted = set_fctx_hoisted fctx
        fun inner ty =
          case ty of
              HTyLet (j, ty1, ty2) => HTyLet (replace j, on_complex ty1, on_hoisted ty2)
            | HTyUnpack (j, ty1, ty2) => HTyUnpack (replace j, on_atom ty1, on_hoisted ty2)
            | HTyApp (j, ty1, ty2) => HTyApp (replace j, on_atom ty1, on_atom ty2)
            | HTyAppK (j, ty1, ty2) => HTyAppK (replace j, on_atom ty1, on_atom ty2)
            | HTyCase (j, ty, ty1, ty2) => HTyCase (replace j, on_atom ty, on_hoisted ty1, on_hoisted ty2)
            | HTyHalt (j, ty) => HTyHalt (replace j, on_atom ty)
            | HTySub (j, ty, pr) => HTySub (replace j, on_hoisted ty, pr)
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
      TyProgram ((program, #3 jty), funcs, ty)
  end
end
end
