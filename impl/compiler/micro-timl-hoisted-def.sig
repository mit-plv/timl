signature SIG_MICRO_TIML_HOISTED_DEF =
sig
    structure MicroTiMLDef : SIG_MICRO_TIML_DEF

    datatype atom_expr =
             AEVar of MicroTiMLDef.var
             | AEConst of MicroTiMLDef.expr_const
             | AEFuncPointer of int
             | AEPair of atom_expr * atom_expr
             | AEAppC of atom_expr * MicroTiMLDef.cstr
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
             | ATyPack of atom_typing_judgement * MicroTiMLDef.kinding * MicroTiMLDef.kinding * atom_typing
             | ATySubTy of atom_typing_judgement * atom_typing * MicroTiMLDef.tyeq
             | ATySubTi of atom_typing_judgement * atom_typing * MicroTiMLDef.proping

         and complex_typing =
             CTyProj of complex_typing_judgement * atom_typing
             | CTyInj of complex_typing_judgement * atom_typing * MicroTiMLDef.kinding
             | CTyFold of complex_typing_judgement * MicroTiMLDef.kinding * atom_typing
             | CTyUnfold of complex_typing_judgement * atom_typing
             | CTyNew of complex_typing_judgement * atom_typing
             | CTyRead of complex_typing_judgement * atom_typing
             | CTyWrite of complex_typing_judgement * atom_typing * atom_typing
             | CTyAtom of complex_typing_judgement * atom_typing
             | CTySubTy of complex_typing_judgement * complex_typing * MicroTiMLDef.tyeq
             | CTySubTi of complex_typing_judgement * complex_typing * MicroTiMLDef.proping

         and hoisted_typing =
             HTyLet of hoisted_typing_judgement * complex_typing * hoisted_typing
             | HTyUnpack of hoisted_typing_judgement * atom_typing * hoisted_typing
             | HTyApp of hoisted_typing_judgement * atom_typing * atom_typing
             | HTyCase of hoisted_typing_judgement * atom_typing * hoisted_typing * hoisted_typing
             | HTyHalt of hoisted_typing_judgement * atom_typing
             | HTySubTi of hoisted_typing_judgement * hoisted_typing * MicroTiMLDef.proping

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

    val hoist_deriv : MicroTiMLDef.typing -> program_typing
end
