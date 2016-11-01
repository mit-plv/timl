signature SIG_MICRO_TIML_HOISTED_DEF =
sig
    structure MicroTiMLDef : SIG_MICRO_TIML_DEF

    datatype atom_expr =
             AEVar of MicroTiMLDef.var
             | AEConst of MicroTiMLDef.expr_const
             | AEFuncPointer of int
             | AEPair of atom_expr * atom_expr
             | AEAppC of atom_expr * MicroTiMLDef.cstr
             | AEAbsC of atom_expr
             | AEPack of MicroTiMLDef.cstr * atom_expr

         and complex_expr =
             CEUnOp of MicroTiMLDef.expr_un_op * atom_expr
             | CEBinOp of MicroTiMLDef.expr_bin_op * atom_expr * atom_expr (* no app or pair *)
             | CEAtom of atom_expr

         and hoisted_expr =
             HELet of complex_expr * hoisted_expr
             | HEUnpack of atom_expr * hoisted_expr
             | HEApp of atom_expr * atom_expr
             | HECase of atom_expr * hoisted_expr * hoisted_expr
             | HEHalt of atom_expr

         and func_expr =
             FEFix of int * hoisted_expr

    type fctx = MicroTiMLDef.cstr list
    type ctx = fctx * MicroTiMLDef.kctx * MicroTiMLDef.tctx

    type atom_typing_judgement = ctx * atom_expr * MicroTiMLDef.cstr * MicroTiMLDef.cstr
    type complex_typing_judgement = ctx * complex_expr * MicroTiMLDef.cstr * MicroTiMLDef.cstr
    type hoisted_typing_judgement = ctx * hoisted_expr * MicroTiMLDef.cstr
    type func_typing_judgement = fctx * func_expr * MicroTiMLDef.cstr

    datatype atom_typing =
             ATyVar of atom_typing_judgement
             | ATyConst of atom_typing_judgement
             | ATyFuncPointer of atom_typing_judgement
             | ATyPair of atom_typing_judgement * atom_typing * atom_typing
             | ATyAppC of atom_typing_judgement * atom_typing * MicroTiMLDef.kinding
             | ATyAbsC of atom_typing_judgement * MicroTiMLDef.wfkind * atom_typing
             | ATyPack of atom_typing_judgement * MicroTiMLDef.kinding * MicroTiMLDef.kinding * atom_typing
             | ATySub of atom_typing_judgement * atom_typing * MicroTiMLDef.tyeq * MicroTiMLDef.proping

         and complex_typing =
             CTyProj of complex_typing_judgement * atom_typing
             | CTyInj of complex_typing_judgement * atom_typing * MicroTiMLDef.kinding
             | CTyFold of complex_typing_judgement * MicroTiMLDef.kinding * atom_typing
             | CTyUnfold of complex_typing_judgement * atom_typing
             | CTyNew of complex_typing_judgement * atom_typing
             | CTyRead of complex_typing_judgement * atom_typing
             | CTyWrite of complex_typing_judgement * atom_typing * atom_typing
             | CTyAtom of complex_typing_judgement * atom_typing
             | CTySub of complex_typing_judgement * complex_typing * MicroTiMLDef.tyeq * MicroTiMLDef.proping

         and hoisted_typing =
             HTyLet of hoisted_typing_judgement * complex_typing * hoisted_typing
             | HTyUnpack of hoisted_typing_judgement * atom_typing * hoisted_typing
             | HTyApp of hoisted_typing_judgement * atom_typing * atom_typing
             | HTyAppK of hoisted_typing_judgement * atom_typing * atom_typing
             | HTyCase of hoisted_typing_judgement * atom_typing * hoisted_typing * hoisted_typing
             | HTyHalt of hoisted_typing_judgement * atom_typing
             | HTySub of hoisted_typing_judgement * hoisted_typing * MicroTiMLDef.proping

         and func_typing =
             FTyFix of func_typing_judgement * MicroTiMLDef.kinding * hoisted_typing

    datatype program =
             Program of func_expr list * hoisted_expr
    type program_typing_judgement = program * MicroTiMLDef.cstr
    datatype program_typing =
             TyProgram of program_typing_judgement * func_typing list * hoisted_typing

    val CEProj : MicroTiMLDef.projector * atom_expr -> complex_expr
    val CEInj : MicroTiMLDef.injector * atom_expr -> complex_expr
    val CEFold : atom_expr -> complex_expr
    val CEUnfold : atom_expr -> complex_expr
    val CENew : atom_expr -> complex_expr
    val CERead : atom_expr -> complex_expr
    val CEWrite : atom_expr * atom_expr -> complex_expr

    val extract_judge_ptyping : program_typing -> program_typing_judgement
    val extract_judge_htyping : hoisted_typing -> hoisted_typing_judgement
    val extract_judge_atyping : atom_typing -> atom_typing_judgement
    val extract_judge_ctyping : complex_typing -> complex_typing_judgement
    val extract_judge_ftyping : func_typing -> func_typing_judgement

    val str_atom_expr : atom_expr -> string
    val str_complex_expr : complex_expr -> string
    val str_hoisted_expr : string -> hoisted_expr -> string
    val str_func_expr : int -> func_expr -> string
    val str_program : program -> string
end

functor MicroTiMLHoistedDefFun(MicroTiMLDef : SIG_MICRO_TIML_DEF) : SIG_MICRO_TIML_HOISTED_DEF =
struct
open List
open Util
infixr 0 $

structure MicroTiMLDef = MicroTiMLDef
structure AstTransformers = AstTransformersFun(MicroTiMLDef)
open MicroTiMLDef
open AstTransformers

datatype atom_expr =
         AEVar of var
         | AEConst of expr_const
         | AEFuncPointer of int
         | AEPair of atom_expr * atom_expr
         | AEAppC of atom_expr * cstr
         | AEAbsC of atom_expr
         | AEPack of cstr * atom_expr

     and complex_expr =
         CEUnOp of expr_un_op * atom_expr
         | CEBinOp of expr_bin_op * atom_expr * atom_expr (* no app or pair *)
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
         | ATyAbsC of atom_typing_judgement * wfkind * atom_typing
         | ATyPack of atom_typing_judgement * kinding * kinding * atom_typing
         | ATySub of atom_typing_judgement * atom_typing * tyeq * proping

     and complex_typing =
         CTyProj of complex_typing_judgement * atom_typing
         | CTyInj of complex_typing_judgement * atom_typing * kinding
         | CTyFold of complex_typing_judgement * kinding * atom_typing
         | CTyUnfold of complex_typing_judgement * atom_typing
         | CTyNew of complex_typing_judgement * atom_typing
         | CTyRead of complex_typing_judgement * atom_typing
         | CTyWrite of complex_typing_judgement * atom_typing * atom_typing
         | CTyAtom of complex_typing_judgement * atom_typing
         | CTySub of complex_typing_judgement * complex_typing * tyeq * proping

     and hoisted_typing =
         HTyLet of hoisted_typing_judgement * complex_typing * hoisted_typing
         | HTyUnpack of hoisted_typing_judgement * atom_typing * hoisted_typing
         | HTyApp of hoisted_typing_judgement * atom_typing * atom_typing
         | HTyAppK of hoisted_typing_judgement * atom_typing * atom_typing
         | HTyCase of hoisted_typing_judgement * atom_typing * hoisted_typing * hoisted_typing
         | HTyHalt of hoisted_typing_judgement * atom_typing
         | HTySub of hoisted_typing_judgement * hoisted_typing * proping

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
    | HTySub (j, _, _) => j

fun extract_judge_atyping ty =
  case ty of
      ATyVar j => j
    | ATyConst j => j
    | ATyFuncPointer j => j
    | ATyPair (j, _, _) => j
    | ATyAppC (j, _, _) => j
    | ATyAbsC (j, _, _) => j
    | ATyPack (j, _, _, _) => j
    | ATySub (j, _, _, _) => j

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
    | CTySub (j, _, _, _) => j

fun extract_judge_ftyping ty =
  case ty of
      FTyFix (j, _, _) => j

structure PU = PrinterUtil
structure PP = PlainPrinter

fun str_atom_expr e =
  case e of
      AEVar x => "&" ^ str_int x
    | AEConst cn => PU.str_expr_const cn
    | AEFuncPointer f => "FUN" ^ str_int f
    | AEPair (e1, e2) => "<" ^ str_atom_expr e1 ^ " , " ^ str_atom_expr e2 ^ ">"
    | AEAppC (e, c) => str_atom_expr e ^ "[" ^ PP.str_cstr c ^ "]"
    | AEAbsC e => "(idxfn => " ^ str_atom_expr e ^ ")"
    | AEPack (c, e) => "pack[" ^ PP.str_cstr c ^ " , " ^ str_atom_expr e ^ "]"

fun str_complex_expr e =
  case e of
      CEUnOp (opr, e) => "(" ^ PU.str_expr_un_op opr ^ " " ^ str_atom_expr e ^ ")"
    | CEBinOp (opr, e1, e2) => "(" ^ str_atom_expr e1 ^ " " ^ PU.str_expr_bin_op opr ^ " " ^ str_atom_expr e2 ^ ")"
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
end
