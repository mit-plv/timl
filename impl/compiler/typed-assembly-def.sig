signature SIG_TYPED_ASSEMBLY_DEF =
sig
    structure MicroTiMLHoistedDef : SIG_MICRO_TIML_HOISTED_DEF
    structure MicroTiMLDef : SIG_MICRO_TIML_DEF

    type register = int
    type location = int

    datatype word_value =
             WVLoc of location
           | WVConst of MicroTiMLDef.expr_const

    datatype small_value =
             SVReg of register
             | SVWord of word_value
             | SVAppC of small_value * MicroTiMLDef.cstr
             | SVPack of MicroTiMLDef.cstr * small_value

    datatype instr =
             INewpair of register * small_value * small_value
             | IProj of MicroTiMLDef.projector * register * register
             | IInj of MicroTiMLDef.injector * register * small_value
             | IFold of register * small_value
             | IUnfold of register * small_value
             | IPrimBinOp of MicroTiMLDef.prim_expr_bin_op * register * register * small_value
             | IMove of register * small_value
             | IUnpack of register * small_value
             | IBranchSum of register * small_value

    datatype fin_instr =
             FIJump of small_value
           | FIHalt

    type instr_block = instr list * fin_instr

    datatype heap_value =
             HVCode of int * instr_block

    datatype program =
             Program of heap_value list * instr_block

    type hctx = heap_value list
    type ctx = hctx * MicroTiMLDef.kctx * MicroTiMLDef.tctx

    type small_value_typing_judgement = ctx * small_value * MicroTiMLDef.cstr
    type instr_typing_judgement = ctx * instr_block * MicroTiMLDef.cstr

    datatype small_value_typing =
         SVTyReg of small_value_typing_judgement
         | SVTyWord of small_value_typing_judgement
         | SVTyAppC of small_value_typing_judgement * small_value_typing * MicroTiMLDef.kinding
         | SVTyPack of small_value_typing_judgement * MicroTiMLDef.kinding * MicroTiMLDef.kinding * small_value_typing

    datatype instr_typing =
             InsTyNewpair of instr_typing_judgement * small_value_typing * small_value_typing * instr_typing
             | InsTyProj of instr_typing_judgement * small_value_typing * instr_typing
             | InsTyInj of instr_typing_judgement * small_value_typing * MicroTiMLDef.kinding * instr_typing
             | InsTyFold of instr_typing_judgement * MicroTiMLDef.kinding * small_value_typing * instr_typing
             | InsTyUnfold of instr_typing_judgement * small_value_typing * instr_typing
             | InsTyPrimBinOp of instr_typing_judgement * small_value_typing * small_value_typing * instr_typing
             | InsTyMove of instr_typing_judgement * small_value_typing * instr_typing
             | InsTyUnpack of instr_typing_judgement * small_value_typing * instr_typing
             | InsTyBranchSum of instr_typing_judgement * small_value_typing * small_value_typing * instr_typing
             | InsTyJump of instr_typing_judgement * small_value_typing
             | InsTyHalt of instr_typing_judgement * small_value_typing

    type heap_value_typing_judgement = hctx * heap_value * MicroTiMLDef.cstr
    type program_typing_judgement = program * MicroTiMLDef.cstr

    datatype heap_value_typing =
             HVTyCode of heap_value_typing_judgement * MicroTiMLDef.kinding * instr_typing

    datatype program_typing =
             TyProgram of program_typing_judgement * heap_value_typing list * instr_typing
end
