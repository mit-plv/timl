functor MicroTiMLHoisted(Time : SIG_TIME) =
struct
  structure DerivTransformers = DerivTransformers(Time)
  open DerivTransformers

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
  type func_typing_judgement = func_expr * cstr

  datatype atom_typing =
    ATyVar of atom_typing_judgement
  | ATyConst of atom_typing_judgement
  | ATyFuncPointer of atom_typing_judgement

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

  and hoisted_typing =
    HTyLet of hoisted_typing_judgement * complex_typing * hoisted_typing
  | HTyUnpack of hoisted_typing_judgement * complex_typing * hoisted_typing
  | HTyComplex of hoisted_typing_judgement * complex_typing
  | HTySub of hoisted_typing_judgement * hoisted_typing * tyeq * proping

  and func_typing =
    FTyFix of func_typing_judgement * kinding * hoisted_typing

  type program = func_expr list * hoisted_expr
  type program_typing = func_typing list * hoisted_typing
end
