functor TypedAssemblyDefFun(MicroTiMLHoistedDef : SIG_MICRO_TIML_HOISTED_DEF) : SIG_TYPED_ASSEMBLY_DEF =
struct
open List
open Util
infixr 0 $

structure MicroTiMLHoistedDef = MicroTiMLHoistedDef
open MicroTiMLHoistedDef
open MicroTiMLDef

type tal_register = int
type tal_location = int
type tal_var = int

datatype tal_cstr =
         TCVar of tal_var
         | TCConst of cstr_const
         | TCBinOp of cstr_bin_op * tal_cstr * tal_cstr
         | TCIte of tal_cstr * tal_cstr * tal_cstr
         | TCTimeAbs of tal_cstr
         | TCTimeApp of int * tal_cstr * tal_cstr
         | TCArrow of tal_cstr list * tal_cstr
         | TCAbs of tal_cstr
         | TCApp of tal_cstr * tal_cstr
         | TCQuan of quan * tal_kind * tal_cstr
         | TCRec of string * tal_kind * tal_cstr
         | TCRef of tal_cstr
         | TCUnOp of cstr_un_op * tal_cstr

     and tal_kind =
         TKType
         | TKArrow of tal_kind * tal_kind
         | TKBaseSort of sort
         | TKSubset of tal_kind * tal_prop

     and tal_prop =
         TPTrue
         | TPFalse
         | TPBinConn of prop_bin_conn * tal_prop * tal_prop
         | TPNot of tal_prop
         | TPBinPred of prop_bin_pred * tal_cstr * tal_cstr
         | TPQuan of quan * sort * tal_prop

datatype tal_word =
         TWLoc of tal_location
         | TWConst of expr_const
         | TWAppC of tal_word * tal_cstr
         | TWPack of tal_cstr * tal_word

datatype tal_value =
         TVReg of tal_register
         | TVWord of tal_word
         | TVAppC of tal_value * tal_cstr
         | TVPack of tal_cstr * tal_value

datatype tal_instr =
         TINewpair of tal_register * tal_register * tal_register
         | TIProj of projector * tal_register * tal_register
         | TIInj of injector * tal_register
         | TIFold of tal_register
         | TIUnfold of tal_register
         | TINewref of tal_register * tal_register
         | TIDeref of tal_register * tal_register
         | TISetref of tal_register * tal_register
         | TIPrimBinOp of prim_expr_bin_op * tal_register * tal_register * tal_register
         | TIMove of tal_register * tal_value
         | TIUnpack of tal_register * tal_value
         | TICase of tal_register * tal_value

datatype tal_control =
         TCJump of tal_value
         | TCHalt of tal_cstr

type tal_block = tal_instr list * tal_control

datatype tal_heap =
         THCode of int * tal_block
         | THPair of tal_word * tal_word
         | THWord of tal_word

datatype tal_program =
         TProgram of tal_heap list * tal_word list * tal_block

type tal_hctx = tal_heap list
type tal_kctx = tal_kind list
type tal_tctx = tal_cstr list
type tal_ctx = tal_hctx * tal_kctx * tal_tctx

type tal_proping_judgement = tal_kctx * tal_prop

datatype tal_proping =
         TPrAdmit of tal_proping_judgement

type tal_kdeq_judgement = tal_kctx * tal_kind * tal_kind

datatype tal_kdeq =
         TKdEqKType of tal_kdeq_judgement
         | TKdEqKArrow of tal_kdeq_judgement * tal_kdeq * tal_kdeq
         | TKdEqBaseSort of tal_kdeq_judgement
         | TKdEqSubset of tal_kdeq_judgement * tal_kdeq * tal_proping

type tal_kinding_judgement = tal_kctx * tal_cstr * tal_kind
type tal_wfkind_judgement = tal_kctx * tal_kind
type tal_wfprop_judgement = tal_kctx * tal_prop

datatype tal_kinding =
         TKdVar of tal_kinding_judgement
         | TKdConst of tal_kinding_judgement
         | TKdBinOp of tal_kinding_judgement * tal_kinding * tal_kinding
         | TKdIte of tal_kinding_judgement * tal_kinding * tal_kinding * tal_kinding
         | TKdArrow of tal_kinding_judgement * tal_kinding list * tal_kinding
         | TKdAbs of tal_kinding_judgement * tal_wfkind * tal_kinding
         | TKdApp of tal_kinding_judgement * tal_kinding * tal_kinding
         | TKdTimeAbs of tal_kinding_judgement * tal_kinding
         | TKdTimeApp of tal_kinding_judgement * tal_kinding * tal_kinding
         | TKdQuan of tal_kinding_judgement * tal_wfkind * tal_kinding
         | TKdRec of tal_kinding_judgement * tal_kinding
         | TKdEq of tal_kinding_judgement * tal_kinding * tal_kdeq
         | TKdUnOp of tal_kinding_judgement * tal_kinding
         | TKdAdmit of tal_kinding_judgement

     and tal_wfkind =
         TWfKdType of tal_wfkind_judgement
         | TWfKdArrow of tal_wfkind_judgement * tal_wfkind * tal_wfkind
         | TWfKdBaseSort of tal_wfkind_judgement
         | TWfKdSubset of tal_wfkind_judgement * tal_wfkind * tal_wfprop
         | TWfKdAdmit of tal_wfkind_judgement

     and tal_wfprop =
         TWfPropTrue of tal_wfprop_judgement
         | TWfPropFalse of tal_wfprop_judgement
         | TWfPropBinConn of tal_wfprop_judgement * tal_wfprop * tal_wfprop
         | TWfPropNot of tal_wfprop_judgement * tal_wfprop
         | TWfPropBinPred of tal_wfprop_judgement * tal_kinding * tal_kinding
         | TWfPropQuan of tal_wfprop_judgement * tal_wfprop

type tal_tyeq_judgement = tal_kctx * tal_cstr * tal_cstr

datatype tal_tyeq =
         TTyEqVar of tal_tyeq_judgement
         | TTyEqConst of tal_tyeq_judgement
         | TTyEqBinOp of tal_tyeq_judgement * tal_tyeq * tal_tyeq
         | TTyEqIte of tal_tyeq_judgement * tal_tyeq * tal_tyeq * tal_tyeq
         | TTyEqArrow of tal_tyeq_judgement * tal_tyeq list * tal_proping
         | TTyEqApp of tal_tyeq_judgement * tal_tyeq * tal_tyeq
         | TTyEqTimeApp of tal_tyeq_judgement * tal_tyeq * tal_tyeq
         | TTyEqBeta of tal_tyeq_judgement * tal_tyeq * tal_tyeq * tal_tyeq
         | TTyEqBetaRev of tal_tyeq_judgement * tal_tyeq * tal_tyeq * tal_tyeq
         | TTyEqQuan of tal_tyeq_judgement * tal_kdeq * tal_tyeq
         | TTyEqRec of tal_tyeq_judgement * tal_kdeq * tal_tyeq
         | TTyEqRef of tal_tyeq_judgement * tal_tyeq
         | TTyEqAbs of tal_tyeq_judgement
         | TTyEqTimeAbs of tal_tyeq_judgement
         | TTyEqUnOp of tal_tyeq_judgement * tal_tyeq
         | TTyEqNat of tal_tyeq_judgement * tal_kinding * tal_kinding * tal_proping

type tal_word_typing_judgement = (tal_hctx * tal_kctx) * tal_word * tal_cstr

datatype tal_word_typing =
         TWTyLoc of tal_word_typing_judgement
         | TWTyConst of tal_word_typing_judgement
         | TWTyAppC of tal_word_typing_judgement * tal_word_typing * tal_kinding
         | TWTyPack of tal_word_typing_judgement * tal_kinding * tal_kinding * tal_word_typing
         | TWTySub of tal_word_typing_judgement * tal_word_typing * tal_tyeq

type tal_value_typing_judgement = tal_ctx * tal_value * tal_cstr

datatype tal_value_typing =
         TVTyReg of tal_value_typing_judgement
         | TVTyWord of tal_value_typing_judgement * tal_word_typing
         | TVTyAppC of tal_value_typing_judgement * tal_value_typing * tal_kinding
         | TVTyPack of tal_value_typing_judgement * tal_kinding * tal_kinding * tal_value_typing
         | TVTySub of tal_value_typing_judgement * tal_value_typing * tal_tyeq

type tal_instr_typing_judgement = tal_ctx * tal_block * tal_cstr

datatype tal_instr_typing =
         TITyNewpair of tal_instr_typing_judgement * tal_value_typing * tal_value_typing * tal_instr_typing
         | TITyProj of tal_instr_typing_judgement * tal_value_typing * tal_instr_typing
         | TITyInj of tal_instr_typing_judgement * tal_value_typing * tal_kinding * tal_instr_typing
         | TITyFold of tal_instr_typing_judgement * tal_kinding * tal_value_typing * tal_instr_typing
         | TITyUnfold of tal_instr_typing_judgement * tal_value_typing * tal_instr_typing
         | TITyNewref of tal_instr_typing_judgement * tal_value_typing * tal_instr_typing
         | TITyDeref of tal_instr_typing_judgement * tal_value_typing * tal_instr_typing
         | TITySetref of tal_instr_typing_judgement * tal_value_typing * tal_value_typing * tal_instr_typing
         | TITyPrimBinOp of tal_instr_typing_judgement * tal_value_typing * tal_value_typing * tal_instr_typing
         | TITyMove of tal_instr_typing_judgement * tal_value_typing * tal_instr_typing
         | TITyUnpack of tal_instr_typing_judgement * tal_value_typing * tal_instr_typing
         | TITyCase of tal_instr_typing_judgement * tal_value_typing * tal_instr_typing * tal_value_typing
         | TITyJump of tal_instr_typing_judgement * tal_value_typing
         | TITyHalt of tal_instr_typing_judgement * tal_value_typing
         | TITySub of tal_instr_typing_judgement * tal_instr_typing * tal_proping

type tal_heap_typing_judgement = tal_hctx * tal_heap * tal_cstr

datatype tal_heap_typing =
         THTyCode of tal_heap_typing_judgement * tal_kinding * tal_instr_typing
         | THTyPair of tal_heap_typing_judgement * tal_word_typing * tal_word_typing
         | THTyWord of tal_heap_typing_judgement * tal_word_typing

type tal_program_typing_judgement = tal_program * tal_cstr

datatype tal_program_typing =
         TPTyProgram of tal_heap_typing list * tal_word_typing list * tal_instr_typing
end
