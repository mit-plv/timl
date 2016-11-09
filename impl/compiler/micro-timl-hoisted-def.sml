functor MicroTiMLHoistedDefFun(MicroTiMLDef : SIG_MICRO_TIML_DEF) : SIG_MICRO_TIML_HOISTED_DEF =
struct
open List
open Util
infixr 0 $

structure MicroTiMLDef = MicroTiMLDef
open MicroTiMLDef
structure MicroTiMLUtil = MicroTiMLUtilFun(MicroTiMLDef)
open MicroTiMLUtil
structure AstTransformers = AstTransformersFun(MicroTiMLDef)
open AstTransformers

datatype atom_expr =
         AEVar of var
         | AEConst of expr_const
         | AEFuncPointer of int
         | AEPair of atom_expr * atom_expr
         | AEAppC of atom_expr * cstr
         | AEPack of cstr * atom_expr

     and complex_expr =
         CEUnOp of expr_un_op * atom_expr
         | CEBinOp of expr_bin_op * atom_expr * atom_expr
         | CEAtom of atom_expr

     and hoisted_expr =
         HELet of complex_expr * hoisted_expr
         | HEUnpack of atom_expr * hoisted_expr
         | HEApp of atom_expr * atom_expr
         | HECase of atom_expr * hoisted_expr * hoisted_expr
         | HEHalt of atom_expr

     and func_expr =
         FEFix of int * hoisted_expr

type fctx = cstr list
type ctx = fctx * kctx * tctx

type atom_typing_judgement = ctx * atom_expr * cstr * cstr
type complex_typing_judgement = ctx * complex_expr * cstr * cstr
type hoisted_typing_judgement = ctx * hoisted_expr * cstr
type func_typing_judgement = fctx * func_expr * cstr

datatype atom_typing =
         ATyVar of atom_typing_judgement
         | ATyConst of atom_typing_judgement
         | ATyFuncPointer of atom_typing_judgement
         | ATyPair of atom_typing_judgement * atom_typing * atom_typing
         | ATyAppC of atom_typing_judgement * atom_typing * kinding
         | ATyPack of atom_typing_judgement * kinding * kinding * atom_typing
         | ATySubTy of atom_typing_judgement * atom_typing * tyeq
         | ATySubTi of atom_typing_judgement * atom_typing * proping

     and complex_typing =
         CTyProj of complex_typing_judgement * atom_typing
         | CTyInj of complex_typing_judgement * atom_typing * kinding
         | CTyFold of complex_typing_judgement * kinding * atom_typing
         | CTyUnfold of complex_typing_judgement * atom_typing
         | CTyNew of complex_typing_judgement * atom_typing
         | CTyRead of complex_typing_judgement * atom_typing
         | CTyWrite of complex_typing_judgement * atom_typing * atom_typing
         | CTyAtom of complex_typing_judgement * atom_typing
         | CTySubTy of complex_typing_judgement * complex_typing * tyeq
         | CTySubTi of complex_typing_judgement * complex_typing * proping

     and hoisted_typing =
         HTyLet of hoisted_typing_judgement * complex_typing * hoisted_typing
         | HTyUnpack of hoisted_typing_judgement * atom_typing * hoisted_typing
         | HTyApp of hoisted_typing_judgement * atom_typing * atom_typing
         | HTyAppK of hoisted_typing_judgement * atom_typing * atom_typing
         | HTyCase of hoisted_typing_judgement * atom_typing * hoisted_typing * hoisted_typing
         | HTyHalt of hoisted_typing_judgement * atom_typing
         | HTySubTi of hoisted_typing_judgement * hoisted_typing * proping

     and func_typing =
         FTyFix of func_typing_judgement * kinding * hoisted_typing

datatype program =
         Program of func_expr list * hoisted_expr
type program_typing_judgement = program * cstr
datatype program_typing =
         TyProgram of program_typing_judgement * func_typing list * hoisted_typing

fun CEProj (p, e) = CEUnOp (EUProj p, e)
fun CEInj (inj, e) = CEUnOp (EUInj inj, e)
fun CEFold e = CEUnOp (EUFold, e)
fun CEUnfold e = CEUnOp (EUUnfold, e)
fun CENew e = CEUnOp (EUNew, e)
fun CERead e = CEUnOp (EURead, e)
fun CEWrite (e1, e2) = CEBinOp (EBWrite, e1, e2)

fun extract_judge_ptyping ty =
  case ty of
      TyProgram (j, _, _) => j

fun extract_judge_htyping ty =
  case ty of
      HTyLet (j, _, _) => j
    | HTyUnpack (j, _, _) => j
    | HTyApp (j, _, _) => j
    | HTyAppK (j, _, _) => j
    | HTyCase (j, _, _, _) => j
    | HTyHalt (j, _) => j
    | HTySubTi (j, _, _) => j

fun extract_judge_atyping ty =
  case ty of
      ATyVar j => j
    | ATyConst j => j
    | ATyFuncPointer j => j
    | ATyPair (j, _, _) => j
    | ATyAppC (j, _, _) => j
    | ATyPack (j, _, _, _) => j
    | ATySubTy (j, _, _) => j
    | ATySubTi (j, _, _) => j

fun extract_judge_ctyping ty =
  case ty of
      CTyProj (j, _) => j
    | CTyInj (j, _, _) => j
    | CTyFold (j, _, _) => j
    | CTyUnfold (j, _) => j
    | CTyNew (j, _) => j
    | CTyRead (j, _) => j
    | CTyWrite (j, _, _) => j
    | CTyAtom (j, _) => j
    | CTySubTy (j, _, _) => j
    | CTySubTi (j, _, _) => j

fun extract_judge_ftyping ty =
  case ty of
      FTyFix (j, _, _) => j

structure PP = PlainPrinter

fun str_atom_expr e =
  case e of
      AEVar x => "&" ^ str_int x
    | AEConst cn => str_expr_const cn
    | AEFuncPointer f => "FUN" ^ str_int f
    | AEPair (e1, e2) => "<" ^ str_atom_expr e1 ^ " , " ^ str_atom_expr e2 ^ ">"
    | AEAppC (e, c) => str_atom_expr e ^ "[" ^ PP.str_cstr c ^ "]"
    | AEPack (c, e) => "pack[" ^ (* PP.str_cstr c *) "_" ^ " , " ^ str_atom_expr e ^ "]"

fun str_complex_expr e =
  case e of
      CEUnOp (opr, e) => "(" ^ str_expr_un_op opr ^ " " ^ str_atom_expr e ^ ")"
    | CEBinOp (opr, e1, e2) => "(" ^ str_atom_expr e1 ^ " " ^ str_expr_bin_op opr ^ " " ^ str_atom_expr e2 ^ ")"
    | CEAtom e => str_atom_expr e

fun str_hoisted_expr tab e =
  case e of
      HELet (e1, e2) => (prefix tab $ "let = " ^ str_complex_expr e1 ^ " in\n") ^ str_hoisted_expr tab e2
    | HEUnpack (e1, e2) => (prefix tab $ "unpack = " ^ str_atom_expr e1 ^ " in\n") ^ str_hoisted_expr tab e2
    | HEApp (e1, e2) => prefix tab $ str_atom_expr e1 ^ "(" ^ str_atom_expr e2 ^ ")\n"
    | HECase (e, e1, e2) => (prefix tab $ "case " ^ str_atom_expr e ^ " of\n") ^ str_hoisted_expr (tab ^ "  ") e1 ^ (prefix tab "else\n") ^ str_hoisted_expr (tab ^ "  ") e2
    | HEHalt e => prefix tab $ "halt(" ^ str_atom_expr e ^ ")\n"

fun str_func_expr num e =
  case e of
      FEFix (cnt, e) => "FUN" ^ str_int num ^ "(" ^ str_int cnt ^ "):\n" ^ str_hoisted_expr "  " e

fun str_program p =
  case p of
      Program (funcs, body) => (foldli (fn (i, func, str) => str ^ str_func_expr i func) "" funcs) ^ "main:\n" ^ str_hoisted_expr "  " body

structure Hoist =
struct
fun is_atom ty =
  case ty of
      TyVar _ => true
    | TyConst _ => true
    | TyFix _ => true
    | TyPair _ => true
    | TyAppC _ => true
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
    | TyPack (((kctx, tctx), EPack (c, e), t, i), kd1, kd2, ty) =>
      let
          val (ty, funcs) = transform_typing_atom (ty, funcs)
          val jty = extract_judge_atyping ty
      in
          (ATyPack ((([], kctx, tctx), AEPack (c, #2 jty), t, i), kd1, kd2, ty), funcs)
      end
    | TySubTy (((kctx, tctx), e, t, i), ty, te) =>
      let
          val (ty, funcs) = transform_typing_atom (ty, funcs)
          val jty = extract_judge_atyping ty
      in
          (ATySubTy ((([], kctx, tctx), #2 jty, t, i), ty, te), funcs)
      end
    | TySubTi (((kctx, tctx), e, t, i), ty, pr) =>
      let
          val (ty, funcs) = transform_typing_atom (ty, funcs)
          val jty = extract_judge_atyping ty
      in
          (ATySubTi ((([], kctx, tctx), #2 jty, t, i), ty, pr), funcs)
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
      | TySubTy (((kctx, tctx), e, t, i), ty, te) =>
        let
            val (ty, funcs) = transform_typing_complex (ty, funcs)
            val jty = extract_judge_ctyping ty
        in
            (CTySubTy ((([], kctx, tctx), #2 jty, t, i), ty, te), funcs)
        end
      | TySubTi (((kctx, tctx), e, t, i), ty, pr) =>
        let
            val (ty, funcs) = transform_typing_complex (ty, funcs)
            val jty = extract_judge_ctyping ty
        in
            (CTySubTi ((([], kctx, tctx), #2 jty, t, i), ty, pr), funcs)
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
      | TySubTy (((kctx, tctx), e, CTypeUnit, i), ty, te) =>
        let
            val (ty, funcs) = transform_typing_hoisted (ty, funcs)
        in
            (ty, funcs)
        end
      | TySubTi (((kctx, tctx), e, CTypeUnit, i), ty, pr) =>
        let
            val (ty, funcs) = transform_typing_hoisted (ty, funcs)
            val jty = extract_judge_htyping ty
        in
            (HTySubTi ((([], kctx, tctx), #2 jty, i), ty, pr), funcs)
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
          | ATyPack (j, kd1, kd2, ty) => ATyPack (replace j, kd1, kd2, on_atom ty)
          | ATySubTy (j, ty, te) => ATySubTy (replace j, on_atom ty, te)
          | ATySubTi (j, ty, pr) => ATySubTi (replace j, on_atom ty, pr)
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
            | CTySubTy (j, ty, te) => CTySubTy (replace j, on_complex ty, te)
            | CTySubTi (j, ty, pr) => CTySubTi (replace j, on_complex ty, pr)
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
            | HTySubTi (j, ty, pr) => HTySubTi (replace j, on_hoisted ty, pr)
    in
        inner ty
    end

and set_fctx_func fctx ty =
    case ty of
        FTyFix ((_, e, t), kd, ty) => FTyFix ((fctx, e, t), kd, set_fctx_hoisted fctx ty)
end

fun hoist_deriv ty =
  let
      val (ty, funcs) = Hoist.transform_typing_hoisted (ty, [])
      val funcs = List.rev funcs
      val fctx = List.map (fn func => #3 (extract_judge_ftyping func)) funcs
      val ty = Hoist.set_fctx_hoisted fctx ty
      val funcs = List.map (Hoist.set_fctx_func fctx) funcs
      val jty = extract_judge_htyping ty
      val program = Program (List.map (fn func => #2 (extract_judge_ftyping func)) funcs, #2 jty)
  in
      TyProgram ((program, #3 jty), funcs, ty)
  end
end
