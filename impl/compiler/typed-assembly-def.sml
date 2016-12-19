functor TypedAssemblyDefFun(MicroTiMLHoistedDef : SIG_MICRO_TIML_HOISTED_DEF) : SIG_TYPED_ASSEMBLY_DEF =
struct
open List
open Util
infixr 0 $

structure MicroTiMLHoistedDef = MicroTiMLHoistedDef
open MicroTiMLHoistedDef
open MicroTiMLDef
structure MicroTiMLUtil = MicroTiMLUtilFun(MicroTiMLDef)
open MicroTiMLUtil

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
         | TCRec of tal_kind * tal_cstr
         | TCTypeNat of tal_cstr
         | TCTypeArr of tal_cstr * tal_cstr
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
         | TWFold of tal_word
         | TWInj of injector * tal_word

datatype tal_value =
         TVReg of tal_register
         | TVWord of tal_word
         | TVAppC of tal_value * tal_cstr
         | TVPack of tal_cstr * tal_value
         | TVFold of tal_value
         | TVInj of injector * tal_value

datatype tal_instr =
         TINewpair of tal_register * tal_register * tal_register
         | TIProj of projector * tal_register * tal_register
         | TIInj of injector * tal_register
         | TIFold of tal_register
         | TIUnfold of tal_register
         | TINewarray of tal_register * tal_register * tal_register
         | TILoad of tal_register * tal_register * tal_register
         | TIStore of tal_register * tal_register * tal_register
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

type tal_hctx = tal_cstr list
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
         | TKdRec of tal_kinding_judgement * tal_wfkind * tal_kinding
         | TKdTypeNat of tal_kinding_judgement * tal_kinding
         | TKdTypeArr of tal_kinding_judgement * tal_kinding * tal_kinding
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
         | TTyEqTimeApp of tal_tyeq_judgement
         | TTyEqBeta of tal_tyeq_judgement
         | TTyEqBetaRev of tal_tyeq_judgement
         | TTyEqQuan of tal_tyeq_judgement * tal_kdeq * tal_tyeq
         | TTyEqRec of tal_tyeq_judgement * tal_kdeq * tal_tyeq
         | TTyEqTypeNat of tal_tyeq_judgement * tal_proping
         | TTyEqTypeArr of tal_tyeq_judgement * tal_tyeq * tal_proping
         | TTyEqAbs of tal_tyeq_judgement
         | TTyEqTimeAbs of tal_tyeq_judgement
         | TTyEqUnOp of tal_tyeq_judgement * tal_tyeq
         | TTyEqNat of tal_tyeq_judgement * tal_proping
         | TTyEqTime of tal_tyeq_judgement * tal_proping
         | TTyEqTrans of tal_tyeq_judgement * tal_tyeq * tal_tyeq

type tal_word_typing_judgement = (tal_hctx * tal_kctx) * tal_word * tal_cstr

datatype tal_word_typing =
         TWTyLoc of tal_word_typing_judgement
         | TWTyConst of tal_word_typing_judgement
         | TWTyAppC of tal_word_typing_judgement * tal_word_typing * tal_kinding
         | TWTyPack of tal_word_typing_judgement * tal_kinding * tal_kinding * tal_word_typing
         | TWTyFold of tal_word_typing_judgement * tal_kinding * tal_word_typing
         | TWTyInj of tal_word_typing_judgement * tal_word_typing * tal_kinding
         | TWTySub of tal_word_typing_judgement * tal_word_typing * tal_tyeq
         | TWTyLocAdmit of tal_word_typing_judgement

type tal_value_typing_judgement = tal_ctx * tal_value * tal_cstr

datatype tal_value_typing =
         TVTyReg of tal_value_typing_judgement
         | TVTyWord of tal_value_typing_judgement * tal_word_typing
         | TVTyAppC of tal_value_typing_judgement * tal_value_typing * tal_kinding
         | TVTyPack of tal_value_typing_judgement * tal_kinding * tal_kinding * tal_value_typing
         | TVTyFold of tal_value_typing_judgement * tal_kinding * tal_value_typing
         | TVTyInj of tal_value_typing_judgement * tal_value_typing * tal_kinding
         | TVTySub of tal_value_typing_judgement * tal_value_typing * tal_tyeq

type tal_instr_typing_judgement = tal_ctx * tal_block * tal_cstr

datatype tal_instr_typing =
         TITyNewpair of tal_instr_typing_judgement * tal_value_typing * tal_value_typing * tal_instr_typing
         | TITyProj of tal_instr_typing_judgement * tal_value_typing * tal_instr_typing
         | TITyInj of tal_instr_typing_judgement * tal_value_typing * tal_kinding * tal_instr_typing
         | TITyFold of tal_instr_typing_judgement * tal_kinding * tal_value_typing * tal_instr_typing
         | TITyUnfold of tal_instr_typing_judgement * tal_value_typing * tal_instr_typing
         | TITyNewarray of tal_instr_typing_judgement * tal_value_typing * tal_value_typing * tal_instr_typing
         | TITyLoad of tal_instr_typing_judgement * tal_value_typing * tal_value_typing * tal_proping * tal_instr_typing
         | TITyStore of tal_instr_typing_judgement * tal_value_typing * tal_value_typing * tal_proping * tal_value_typing * tal_instr_typing
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
         TPTyProgram of tal_program_typing_judgement * tal_heap_typing list * tal_word_typing list * tal_instr_typing

val TKUnit = TKBaseSort BSUnit
val TKBool = TKBaseSort BSBool
val TKNat = TKBaseSort BSNat
fun TKTimeFun arity = TKBaseSort (BSTimeFun arity)
val TKTime = TKTimeFun 0

fun TTconst r = TCConst (CCTime r)
val TT0 = TTconst Time.Time0
val TT1 = TTconst Time.Time1
fun TTadd (c1, c2) = TCBinOp (CBTimeAdd, c1, c2)
fun TTminus (c1, c2) = TCBinOp (CBTimeMinus, c1, c2)
fun TTmult (c1, c2) = TCBinOp (CBTimeMult, c1, c2)
fun TTmax (c1, c2) = TCBinOp (CBTimeMax, c1, c2)

fun TTfromNat c = TCUnOp (CUNat2Time, c)

fun TPAnd (p1, p2) = TPBinConn (PBCAnd, p1, p2)
fun TPOr (p1, p2) = TPBinConn (PBCOr, p1, p2)
fun TPImply (p1, p2) = TPBinConn (PBCImply, p1, p2)
fun TPIff (p1, p2) = TPBinConn (PBCIff, p1, p2)

fun TCForall (k, c) = TCQuan (QuanForall, k, c)
fun TCExists (k, c) = TCQuan (QuanExists, k, c)

val TCTypeUnit = TCConst CCTypeUnit
val TCTypeInt = TCConst CCTypeInt

fun TCProd (c1, c2) = TCBinOp (CBTypeProd, c1, c2)
fun TCSum (c1, c2) = TCBinOp (CBTypeSum, c1, c2)

fun TTLe (c1, c2) = TPBinPred (PBTimeLe, c1, c2)
fun TTEq (c1, c2) = TPBinPred (PBTimeEq, c1, c2)

fun TCNat n = TCConst (CCIdxNat n)

fun TCApps t cs =
  case cs of
      [] => t
    | c :: cs => TCApps (TCApp (t, c)) cs

val TBSTime = BSTimeFun 0

fun const_tal_kind cn =
  case cn of
      CCIdxTT => TKUnit
    | CCIdxTrue => TKBool
    | CCIdxFalse => TKBool
    | CCIdxNat _ => TKNat
    | CCTime _ => TKTime
    | CCTypeUnit => TKType
    | CCTypeInt => TKType

fun const_tal_type cn =
  case cn of
      ECTT => TCTypeUnit
    | ECInt _ => TCTypeInt
    | ECNat n => TCTypeNat (TCNat n)

fun cbinop_arg1_tal_kind opr =
  case opr of
      CBTimeAdd => TKTime
    | CBTimeMinus => TKTime
    | CBTimeMult => TKTime
    | CBTimeMax => TKTime
    | CBTimeMin => TKTime
    | CBNatAdd => TKNat
    | CBNatMinus => TKNat
    | CBNatMult => TKNat
    | CBTypeProd => TKType
    | CBTypeSum => TKType

fun cbinop_arg2_tal_kind opr =
  case opr of
      CBTimeAdd => TKTime
    | CBTimeMinus => TKTime
    | CBTimeMult => TKTime
    | CBTimeMax => TKTime
    | CBTimeMin => TKTime
    | CBNatAdd => TKNat
    | CBNatMinus => TKNat
    | CBNatMult => TKNat
    | CBTypeProd => TKType
    | CBTypeSum => TKType

fun cbinop_result_tal_kind opr =
  case opr of
      CBTimeAdd => TKTime
    | CBTimeMinus => TKTime
    | CBTimeMult => TKTime
    | CBTimeMax => TKTime
    | CBTimeMin => TKTime
    | CBNatAdd => TKNat
    | CBNatMinus => TKNat
    | CBNatMult => TKNat
    | CBTypeProd => TKType
    | CBTypeSum => TKType

fun cunop_arg_tal_kind opr =
  case opr of
      CUCeil => TKTime
    | CUFloor => TKTime
    | CULog _ => TKTime
    | CUDiv _ => TKTime
    | CUNat2Time => TKNat
    | CUBool2Nat => TKBool

fun cunop_result_tal_kind opr =
  case opr of
      CUCeil => TKNat
    | CUFloor => TKNat
    | CULog _ => TKTime
    | CUDiv _ => TKTime
    | CUNat2Time => TKTime
    | CUBool2Nat => TKNat

fun binpred_arg1_tal_kind opr =
  case opr of
      PBTimeLe => TKTime
    | PBTimeLt => TKTime
    | PBTimeEq => TKTime
    | PBTimeGe => TKTime
    | PBTimeGt => TKTime
    | PBBigO n => TKTimeFun n
    | PBNatLe => TKNat
    | PBNatLt => TKNat
    | PBNatEq => TKNat
    | PBNatGe => TKNat
    | PBNatGt => TKNat

fun binpred_arg2_tal_kind opr =
  case opr of
      PBTimeLe => TKTime
    | PBTimeLt => TKTime
    | PBTimeEq => TKTime
    | PBTimeGe => TKTime
    | PBTimeGt => TKTime
    | PBBigO n => TKTimeFun n
    | PBNatLe => TKNat
    | PBNatLt => TKNat
    | PBNatEq => TKNat
    | PBNatGe => TKNat
    | PBNatGt => TKNat

fun pebinop_arg1_tal_type opr =
  case opr of
      PEBIntAdd => TCTypeInt

fun pebinop_arg2_tal_type opr =
  case opr of
      PEBIntAdd => TCTypeInt

fun pebinop_result_tal_type opr =
  case opr of
      PEBIntAdd => TCTypeInt

fun update_tal_tctx r t tctx =
  let
      fun inner r tctx =
        if r = 0 then t :: (if null tctx then [] else tl tctx)
        else (if null tctx then TCTypeUnit else hd tctx) :: (inner (r - 1) (if null tctx then [] else tl tctx))
  in
      inner r tctx
  end

fun extract_judge_tal_proping pr =
  case pr of
      TPrAdmit j => j

fun extract_judge_tal_kdeq ke =
  case ke of
      TKdEqKType j => j
    | TKdEqKArrow (j, _, _) => j
    | TKdEqBaseSort j => j
    | TKdEqSubset (j, _, _) => j

fun extract_judge_tal_kinding kd =
  case kd of
      TKdVar j => j
    | TKdConst j => j
    | TKdBinOp (j, _, _) => j
    | TKdIte (j, _, _, _) => j
    | TKdArrow (j, _, _) => j
    | TKdAbs (j, _, _) => j
    | TKdApp (j, _, _) => j
    | TKdTimeAbs (j, _) => j
    | TKdTimeApp (j, _, _) => j
    | TKdQuan (j, _, _) => j
    | TKdRec (j, _, _) => j
    | TKdEq (j, _, _) => j
    | TKdUnOp (j, _) => j
    | TKdTypeNat (j, _) => j
    | TKdTypeArr (j, _, _) => j
    | TKdAdmit j => j

fun extract_judge_tal_wfkind wk =
  case wk of
      TWfKdType j => j
    | TWfKdArrow (j, _, _) => j
    | TWfKdBaseSort j => j
    | TWfKdSubset (j, _, _) => j
    | TWfKdAdmit j => j

fun extract_judge_tal_wfprop wp =
  case wp of
      TWfPropTrue j => j
    | TWfPropFalse j => j
    | TWfPropBinConn (j, _, _) => j
    | TWfPropNot (j, _) => j
    | TWfPropBinPred (j, _, _) => j
    | TWfPropQuan (j, _) => j

fun extract_judge_tal_tyeq te =
  case te of
      TTyEqVar j => j
    | TTyEqConst j => j
    | TTyEqBinOp (j, _, _) => j
    | TTyEqIte (j, _, _, _) => j
    | TTyEqArrow (j, _, _) => j
    | TTyEqApp (j, _, _) => j
    | TTyEqTimeApp j => j
    | TTyEqBeta j => j
    | TTyEqBetaRev j => j
    | TTyEqQuan (j, _, _) => j
    | TTyEqRec (j, _, _) => j
    | TTyEqAbs j => j
    | TTyEqTimeAbs j => j
    | TTyEqUnOp (j, _) => j
    | TTyEqTrans (j, _, _) => j
    | TTyEqTypeNat (j, _) => j
    | TTyEqTypeArr (j, _, _) => j
    | TTyEqNat (j, _) => j
    | TTyEqTime (j, _) => j

fun extract_judge_tal_word_typing wty =
  case wty of
      TWTyLoc j => j
    | TWTyConst j => j
    | TWTyAppC (j, _, _) => j
    | TWTyPack (j, _, _, _) => j
    | TWTyFold (j, _, _) => j
    | TWTyInj (j, _, _) => j
    | TWTySub (j, _, _) => j
    | TWTyLocAdmit j => j

fun extract_judge_tal_value_typing vty =
  case vty of
      TVTyReg j => j
    | TVTyWord (j, _) => j
    | TVTyAppC (j, _, _) => j
    | TVTyPack (j, _, _, _) => j
    | TVTyFold (j, _, _) => j
    | TVTyInj (j, _, _) => j
    | TVTySub (j, _, _) => j

fun extract_judge_tal_instr_typing ity =
  case ity of
      TITyNewpair (j, _, _, _) => j
    | TITyProj (j, _, _) => j
    | TITyInj (j, _, _, _) => j
    | TITyFold (j, _, _, _) => j
    | TITyUnfold (j, _, _) => j
    | TITyNewarray (j, _, _, _) => j
    | TITyLoad (j, _, _, _, _) => j
    | TITyStore (j, _, _, _, _, _) => j
    | TITyPrimBinOp (j, _, _, _) => j
    | TITyMove (j, _, _) => j
    | TITyUnpack (j, _, _) => j
    | TITyCase (j, _, _, _) => j
    | TITyJump (j, _) => j
    | TITyHalt (j, _) => j
    | TITySub (j, _, _) => j

fun extract_judge_tal_heap_typing hty =
  case hty of
      THTyCode (j, _, _) => j
    | THTyPair (j, _, _) => j
    | THTyWord (j, _) => j

fun extract_judge_tal_program_typing pty =
  case pty of
      TPTyProgram (j, _, _, _) => j

fun extract_tal_p_bin_conn (TPBinConn a) = a
  | extract_tal_p_bin_conn _ = raise (Impossible "extract_tal_p_bin_conn")

fun extract_tal_p_bin_pred (TPBinPred a) = a
  | extract_tal_p_bin_pred _ = raise (Impossible "extract_tal_p_bin_pred")

fun extract_tal_k_arrow (TKArrow a) = a
  | extract_tal_k_arrow _ = raise (Impossible "extract_tal_k_arrow")

fun extract_tal_k_time_fun (TKBaseSort (BSTimeFun arity)) = arity
  | extract_tal_k_time_fun _ = raise (Impossible "extract_tal_k_time_fun")

fun extract_tal_c_quan (TCQuan a) = a
  | extract_tal_c_quan _ = raise (Impossible "extract_tal_c_quan")

fun extract_tal_c_arrow (TCArrow a) = a
  | extract_tal_c_arrow _ = raise (Impossible "extract_tal_c_arrow")

fun extract_tal_c_abs (TCAbs a) = a
  | extract_tal_c_abs _ = raise (Impossible "extract_tal_c_abs")

fun extract_tal_c_prod (TCBinOp (CBTypeProd, t1, t2)) = (t1, t2)
  | extract_tal_c_prod _ = raise (Impossible "extract_tal_c_prod")

fun extract_tal_c_rec (TCRec a) = a
  | extract_tal_c_rec _ = raise (Impossible "extract_tal_c_rec")

fun extract_tal_c_sum (TCBinOp (CBTypeSum, t1, t2)) = (t1, t2)
  | extract_tal_c_sum _ = raise (Impossible "extract_tal_c_sum")

fun extract_tal_v_reg (TVReg r) = r
  | extract_tal_v_reg _ = raise (Impossible "extract_tal_v_reg")

fun str_tal_cstr c =
  case c of
      TCVar x => "$" ^ str_int x
    | TCConst cn => str_cstr_const cn
    | TCBinOp (opr, c1, c2) => "(" ^ str_tal_cstr c1 ^ " " ^ str_cstr_bin_op opr ^ " " ^ str_tal_cstr c2 ^ ")"
    | TCIte (i1, i2, i3) => "(" ^ str_tal_cstr i1 ^ " ? " ^ str_tal_cstr i2 ^ " : " ^ str_tal_cstr i3 ^ ")"
    | TCTimeAbs i => "(fn => " ^ str_tal_cstr i ^ ")"
    | TCTimeApp (arity, c1, c2) => "(" ^ str_tal_cstr c1 ^ " " ^ str_tal_cstr c2 ^ ")"
    | TCArrow (ts, i) => "(" ^ "REG" ^ " -- " ^ str_tal_cstr i ^ " --> void )"
    | TCAbs t => "(fn => " ^ str_tal_cstr t ^ ")"
    | TCApp (c1, c2) => "(" ^ str_tal_cstr c1 ^ " " ^ str_tal_cstr c2 ^ ")"
    | TCQuan (q, k, c) => "(" ^ str_quan q ^ " " ^ str_tal_kind k ^ " : " ^ str_tal_cstr c ^ ")"
    | TCTypeNat c => "nat(" ^ str_tal_cstr c ^ ")"
    | TCTypeArr (c1, c2) => "arr(" ^ str_tal_cstr c1 ^ ", " ^ str_tal_cstr c2 ^ ")"
    | TCRec (k, t) => "REC_TYPE" (* "(rec " ^ str_tal_kind k ^ " => " ^ str_tal_cstr t ^ ")" *)
    | TCUnOp (opr, c) => "(" ^ str_cstr_un_op opr ^ " " ^ str_tal_cstr c ^ ")"

and str_tal_kind k =
  case k of
      TKType => "*"
    | TKArrow (k1, k2) => "(" ^ str_tal_kind k1 ^ " => " ^ str_tal_kind k2 ^ ")"
    | TKBaseSort b => str_sort b
    | TKSubset (k, p) => "{" ^ str_tal_kind k ^ " | " ^ str_tal_prop p ^ "}"

and str_tal_prop p =
    case p of
        TPTrue => "true"
      | TPFalse => "false"
      | TPBinConn (opr, p1, p2) => "(" ^ str_tal_prop p1 ^ " " ^ str_prop_bin_conn opr ^ " " ^ str_tal_prop p2 ^ ")"
      | TPNot p => "(not" ^ str_tal_prop p ^ ")"
      | TPBinPred (opr, i1, i2) => "(" ^ str_tal_cstr i1 ^ " " ^ str_prop_bin_pred opr ^ " " ^ str_tal_cstr i2 ^ ")"
      | TPQuan (q, b, p) => "(" ^ str_quan q ^ " " ^ str_sort b ^ " : " ^ str_tal_prop p ^ ")"

fun str_tal_word w =
  case w of
      TWLoc loc => "LOC:" ^ str_int loc
    | TWConst cn => str_expr_const cn
    | TWAppC (w, c) => str_tal_word w ^ "[" ^ str_tal_cstr c ^ "]"
    | TWFold w => "(fold" ^ str_tal_word w ^ ")"
    | TWInj (inj, w) => "(" ^ str_injector inj ^ " " ^ str_tal_word w ^ ")"
    | TWPack (c, w) => "pack[" ^ "_" ^ " , " ^ str_tal_word w ^ "]"

fun str_tal_value v =
  case v of
      TVReg reg => "REG:" ^ str_int reg
    | TVWord w => str_tal_word w
    | TVAppC (v, c) => str_tal_value v ^ "[" ^ str_tal_cstr c ^ "]"
    | TVFold v => "(fold" ^ str_tal_value v ^ ")"
    | TVInj (inj, v) => "(" ^ str_injector inj ^ " " ^ str_tal_value v ^ ")"
    | TVPack (c, v) => "pack[" ^ "_" ^ " , " ^ str_tal_value v ^ "]"

fun str_tal_instr i =
  case i of
      TINewpair (rd, rs, rt) => "newpair " ^ str_tal_value (TVReg rd) ^ ", " ^ str_tal_value (TVReg rs) ^ ", " ^ str_tal_value (TVReg rt)
    | TIProj (p, rd, rs) => (case p of ProjFst => "ldfst "
                                    | ProjSnd => "ldsnd ") ^ str_tal_value (TVReg rd) ^ ", " ^ str_tal_value (TVReg rs)
    | TIInj (inj, rd) => (case inj of InjInl => "inl "
                                   | InjInr => "inr ") ^ str_tal_value (TVReg rd)
    | TIFold rd => "fold " ^ str_tal_value (TVReg rd)
    | TIUnfold rd => "unfold " ^ str_tal_value (TVReg rd)
    | TINewarray (rd, rs, rt) => "newarray " ^ str_tal_value (TVReg rd) ^ ", " ^ str_tal_value (TVReg rs) ^ ", " ^ str_tal_value (TVReg rt)
    | TILoad (rd, rs, rt) => "load " ^ str_tal_value (TVReg rd) ^ ", " ^ str_tal_value (TVReg rs) ^ "(" ^ str_tal_value (TVReg rt) ^ ")"
    | TIStore (rd, rs, rt) => "store " ^ str_tal_value (TVReg rd) ^ "(" ^ str_tal_value (TVReg rs) ^ "), " ^ str_tal_value (TVReg rt)
    | TIPrimBinOp (opr, rd, rs, rt) => (case opr of
                                           PEBIntAdd => "addi "
                                      ) ^ str_tal_value (TVReg rd) ^ ", " ^ str_tal_value (TVReg rs) ^ ", " ^ str_tal_value (TVReg rt)
    | TIMove (rd, v) => "move " ^ str_tal_value (TVReg rd) ^ ", " ^ str_tal_value v
    | TIUnpack (rd, v) => "unpack " ^ str_tal_value (TVReg rd) ^ ", " ^ str_tal_value v
    | TICase (rd, v) => "case " ^ str_tal_value (TVReg rd) ^ ", " ^ str_tal_value v

fun str_tal_control c =
  case c of
      TCJump v => "jump " ^ str_tal_value v
    | TCHalt c => "halt[" ^ str_tal_cstr c ^ "]"

fun str_tal_block (ins, fin) =
  (foldl (fn (i, s) => s ^ "  " ^ str_tal_instr i ^ "\n") "" ins) ^ ("  " ^ str_tal_control fin ^ "\n")

fun str_tal_heap h =
  case h of
      THWord w => "  " ^ str_tal_word w ^ "\n"
    | THPair (w1, w2) => "  " ^ "(" ^ str_tal_word w1 ^ " , " ^ str_tal_word w2 ^ ")" ^ "\n"
    | THCode (n, blk) => "  (" ^ str_int n ^ " cstr parameter(s)" ^ ")\n" ^ str_tal_block blk

fun str_tal_program p =
  case p of
      TProgram (heaps, _, main) =>
      (foldli (fn (i, h, s) => s ^ "LOC:" ^ str_int i ^ ":\n" ^ str_tal_heap h) "" heaps) ^ "MAIN:\n" ^ str_tal_block main
end

functor TALCstrGenericTransformerFun(
    structure TypedAssemblyDef : SIG_TYPED_ASSEMBLY_DEF
    structure Action :
    sig
        type down
        type up

        val upward_base : up
        val combiner : up * up -> up

        val add_tal_kind : TypedAssemblyDef.tal_kind option * down -> down

        val transformer_tal_cstr : (TypedAssemblyDef.tal_cstr * down -> TypedAssemblyDef.tal_cstr * up) * (TypedAssemblyDef.tal_kind * down -> TypedAssemblyDef.tal_kind * up) -> TypedAssemblyDef.tal_cstr * down -> (TypedAssemblyDef.tal_cstr * up) option
        val transformer_tal_kind : (TypedAssemblyDef.tal_kind * down -> TypedAssemblyDef.tal_kind * up) * (TypedAssemblyDef.tal_prop * down -> TypedAssemblyDef.tal_prop * up) -> TypedAssemblyDef.tal_kind * down -> (TypedAssemblyDef.tal_kind * up) option
        val transformer_tal_prop : (TypedAssemblyDef.tal_prop * down -> TypedAssemblyDef.tal_prop * up) * (TypedAssemblyDef.tal_cstr * down -> TypedAssemblyDef.tal_cstr * up) -> TypedAssemblyDef.tal_prop * down -> (TypedAssemblyDef.tal_prop * up) option
    end) =
struct
open List
open Util
infixr 0 $

structure TypedAssemblyDef = TypedAssemblyDef
open TypedAssemblyDef

open Action

val combine = foldl combiner upward_base

fun default_transform_tal_cstr (c, down) =
  case c of
      TCVar x => (TCVar x, upward_base)
    | TCConst cn => (TCConst cn, upward_base)
    | TCBinOp (opr, c1, c2) =>
      let
          val (c1, up1) = transform_tal_cstr (c1, down)
          val (c2, up2) = transform_tal_cstr (c2, down)
      in
          (TCBinOp (opr, c1, c2), combine [up1, up2])
      end
    | TCIte (i1, i2, i3) =>
      let
          val (i1, up1) = transform_tal_cstr (i1, down)
          val (i2, up2) = transform_tal_cstr (i2, down)
          val (i3, up3) = transform_tal_cstr (i3, down)
      in
          (TCIte (i1, i2, i3), combine [up1, up2, up3])
      end
    | TCTimeAbs i =>
      let
          val (i, up1) = transform_tal_cstr (i, add_tal_kind (SOME TKTime, down))
      in
          (TCTimeAbs i, combine [up1])
      end
    | TCTimeApp (arity, c1, c2) =>
      let
          val (c1, up1) = transform_tal_cstr (c1, down)
          val (c2, up2) = transform_tal_cstr (c2, down)
      in
          (TCTimeApp (arity, c1, c2), combine [up1, up2])
      end
    | TCArrow (ts, i) =>
      let
          val (ts, ups) = ListPair.unzip $ map (fn t => transform_tal_cstr (t, down)) ts
          val (i, up2) = transform_tal_cstr (i, down)
      in
          (TCArrow (ts, i), combine $ ups @ [up2])
      end
    | TCAbs t =>
      let
          val (t, up1) = transform_tal_cstr (t, add_tal_kind (NONE, down))
      in
          (TCAbs t, combine [up1])
      end
    | TCApp (c1, c2) =>
      let
          val (c1, up1) = transform_tal_cstr (c1, down)
          val (c2, up2) = transform_tal_cstr (c2, down)
      in
          (TCApp (c1, c2), combine [up1, up2])
      end
    | TCQuan (q, k, c) =>
      let
          val (k, up1) = transform_tal_kind (k, down)
          val (c, up2) = transform_tal_cstr (c, add_tal_kind (SOME k, down))
      in
          (TCQuan (q, k, c), combine [up1, up2])
      end
    | TCRec (k, t) =>
      let
          val (k, up1) = transform_tal_kind (k, down)
          val (t, up2) = transform_tal_cstr (t, add_tal_kind (SOME k, down))
      in
          (TCRec (k, t), combine [up1, up2])
      end
    | TCTypeNat c =>
      let
          val (c, up1) = transform_tal_cstr (c, down)
      in
          (TCTypeNat c, combine [up1])
      end
    | TCTypeArr (c1, c2) =>
      let
          val (c1, up1) = transform_tal_cstr (c1, down)
          val (c2, up2) = transform_tal_cstr (c2, down)
      in
          (TCTypeArr (c1, c2), combine [up1, up2])
      end
    | TCUnOp (opr, c) =>
      let
          val (c, up1) = transform_tal_cstr (c, down)
      in
          (TCUnOp (opr, c), combine [up1])
      end

and transform_tal_cstr (c, down) =
    case transformer_tal_cstr (transform_tal_cstr, transform_tal_kind) (c, down) of
        SOME res => res
      | NONE => default_transform_tal_cstr (c, down)

and default_transform_tal_kind (k, down) =
    case k of
        TKType => (TKType, upward_base)
      | TKArrow (k1, k2) =>
        let
            val (k1, up1) = transform_tal_kind (k1, down)
            val (k2, up2) = transform_tal_kind (k2, down)
        in
            (TKArrow (k1, k2), combine [up1, up2])
        end
      | TKBaseSort b => (TKBaseSort b, upward_base)
      | TKSubset (k, p) =>
        let
            val (k, up1) = transform_tal_kind (k, down)
            val (p, up2) = transform_tal_prop (p, add_tal_kind (SOME k, down))
        in
            (TKSubset (k, p), combine [up1, up2])
        end

and transform_tal_kind (k, down) =
    case transformer_tal_kind (transform_tal_kind, transform_tal_prop) (k, down) of
        SOME res => res
      | NONE => default_transform_tal_kind (k, down)

and default_transform_tal_prop (p, down) =
    case p of
        TPTrue => (TPTrue, upward_base)
      | TPFalse => (TPFalse, upward_base)
      | TPBinConn (opr, p1, p2) =>
        let
            val (p1, up1) = transform_tal_prop (p1, down)
            val (p2, up2) = transform_tal_prop (p2, down)
        in
            (TPBinConn (opr, p1, p2), combine [up1, up2])
        end
      | TPNot p =>
        let
            val (p, up1) = transform_tal_prop (p, down)
        in
            (TPNot p, combine [up1])
        end
      | TPBinPred (opr, i1, i2) =>
        let
            val (i1, up1) = transform_tal_cstr (i1, down)
            val (i2, up2) = transform_tal_cstr (i2, down)
        in
            (TPBinPred (opr, i1, i2), combine [up1, up2])
        end
      | TPQuan (q, b, p) =>
        let
            val (p, up1) = transform_tal_prop (p, add_tal_kind (SOME (TKBaseSort b), down))
        in
            (TPQuan (q, b, p), combine [up1])
        end

and transform_tal_prop (p, down) =
    case transformer_tal_prop (transform_tal_prop, transform_tal_cstr) (p, down) of
        SOME res => res
      | NONE => default_transform_tal_prop (p, down)
end

functor TALCstrGenericOnlyDownTransformerFun(
    structure TypedAssemblyDef : SIG_TYPED_ASSEMBLY_DEF
    structure Action :
    sig
        type down

        val add_tal_kind : TypedAssemblyDef.tal_kind option * down -> down

        val transformer_tal_cstr : (TypedAssemblyDef.tal_cstr * down -> TypedAssemblyDef.tal_cstr) * (TypedAssemblyDef.tal_kind * down -> TypedAssemblyDef.tal_kind) -> TypedAssemblyDef.tal_cstr * down -> TypedAssemblyDef.tal_cstr option
        val transformer_tal_kind : (TypedAssemblyDef.tal_kind * down -> TypedAssemblyDef.tal_kind) * (TypedAssemblyDef.tal_prop * down -> TypedAssemblyDef.tal_prop) -> TypedAssemblyDef.tal_kind * down -> TypedAssemblyDef.tal_kind option
        val transformer_tal_prop : (TypedAssemblyDef.tal_prop * down -> TypedAssemblyDef.tal_prop) * (TypedAssemblyDef.tal_cstr * down -> TypedAssemblyDef.tal_cstr) -> TypedAssemblyDef.tal_prop * down -> TypedAssemblyDef.tal_prop option
    end) =
struct
open List
open Util
infixr 0 $

structure TypedAssemblyDef = TypedAssemblyDef
open TypedAssemblyDef

open Action

structure Transformer = TALCstrGenericTransformerFun(
    structure TypedAssemblyDef = TypedAssemblyDef
    structure Action =
    struct
    type down = down
    type up = unit

    val upward_base = ()
    fun combiner ((), ()) = ()

    val add_tal_kind = add_tal_kind

    fun transformer_tal_cstr (on_cstr, on_kind) =
      let
          val on_cstr_no_up = fst o on_cstr
          val on_kind_no_up = fst o on_kind
      in
          Option.map (fn c => (c, ())) o Action.transformer_tal_cstr (on_cstr_no_up, on_kind_no_up)
      end

    fun transformer_tal_kind (on_kind, on_prop) =
      let
          val on_kind_no_up = fst o on_kind
          val on_prop_no_up = fst o on_prop
      in
          Option.map (fn k => (k, ())) o Action.transformer_tal_kind (on_kind_no_up, on_prop_no_up)
      end

    fun transformer_tal_prop (on_prop, on_cstr) =
      let
          val on_prop_no_up = fst o on_prop
          val on_cstr_no_up = fst o on_cstr
      in
          Option.map (fn p => (p, ())) o Action.transformer_tal_prop (on_prop_no_up, on_cstr_no_up)
      end
    end)

val transform_tal_cstr = fst o Transformer.transform_tal_cstr
val transform_tal_kind = fst o Transformer.transform_tal_kind
val transform_tal_prop = fst o Transformer.transform_tal_prop
end

functor TALCstrTransformersFun(TypedAssemblyDef : SIG_TYPED_ASSEMBLY_DEF) =
struct
open List
open Util
infixr 0 $

structure TypedAssemblyDef = TypedAssemblyDef
open TypedAssemblyDef

structure ShiftTALCstr =
struct
structure CstrHelper = TALCstrGenericOnlyDownTransformerFun(
    structure TypedAssemblyDef = TypedAssemblyDef
    structure Action =
    struct
    type down = int * int

    fun add_tal_kind (_, (d, ctx)) = (d, ctx + 1)

    fun transformer_tal_cstr (on_cstr, on_kind) (c, (d, ctx)) =
      case c of
          TCVar x => SOME (if x >= ctx then TCVar (x + d) else TCVar x)
        | _ => NONE

    fun transformer_tal_kind _ _ = NONE
    fun transformer_tal_prop _ _ = NONE
    end)

fun shift_tal_c_c d ctx c = CstrHelper.transform_tal_cstr (c, (d, ctx))
fun shift_tal_c_k d ctx k = CstrHelper.transform_tal_kind (k, (d, ctx))
fun shift_tal_c_p d ctx p = CstrHelper.transform_tal_prop (p, (d, ctx))

val shift0_tal_c_c = shift_tal_c_c 1 0
val shift0_tal_c_k = shift_tal_c_k 1 0
val shift0_tal_c_p = shift_tal_c_p 1 0
end

structure SubstTALCstr =
struct
open ShiftTALCstr

structure CstrHelper = TALCstrGenericOnlyDownTransformerFun(
    structure TypedAssemblyDef = TypedAssemblyDef
    structure Action =
    struct
    type down = tal_cstr * int

    fun add_tal_kind (_, (to, who)) = (shift0_tal_c_c to, who + 1)

    fun transformer_tal_cstr (on_cstr, on_kind) (c, (to, who)) =
      case c of
          TCVar x => SOME (if x = who then to else if x < who then TCVar x else TCVar (x - 1))
        | _ => NONE

    fun transformer_tal_kind _ _ = NONE
    fun transformer_tal_prop _ _ = NONE
    end)

fun subst_tal_c_c to who c = CstrHelper.transform_tal_cstr (c, (to, who))
fun subst_tal_c_k to who k = CstrHelper.transform_tal_kind (k, (to, who))
fun subst_tal_c_p to who p = CstrHelper.transform_tal_prop (p, (to, who))

fun subst0_tal_c_c to = subst_tal_c_c to 0
fun subst0_tal_c_k to = subst_tal_c_k to 0
fun subst0_tal_c_p to = subst_tal_c_p to 0
end
end

functor TALDerivAssemblerFun(TypedAssemblyDef : SIG_TYPED_ASSEMBLY_DEF) =
struct
open List
open Util
infixr 0 $

structure TypedAssemblyDef = TypedAssemblyDef
open TypedAssemblyDef
open MicroTiMLHoistedDef
open MicroTiMLDef
structure TALCstrTransformers = TALCstrTransformersFun(TypedAssemblyDef)
open TALCstrTransformers

open ShiftTALCstr
open SubstTALCstr

exception AssembleFail of string

fun assert b msg =
  if b then () else (println $ "AssembleFail: " ^ msg; raise AssembleFail msg)

fun as_TPrAdmit kctx p =
  let
      (* val () = println $ str_tal_prop p *)
  in
      TPrAdmit (kctx, p)
  end

fun as_TKdEqKType kctx =
  TKdEqKType (kctx, TKType, TKType)

fun as_TKdEqKArrow ke1 ke2 =
  let
      val (kctx1, k11, k12) = extract_judge_tal_kdeq ke1
      val (kctx2, k21, k22) = extract_judge_tal_kdeq ke2
      val () = assert (kctx1 = kctx2) "TKdEqKArrow 1"
  in
      TKdEqKArrow ((kctx1, TKArrow (k11, k21), TKArrow (k12, k22)), ke1, ke2)
  end

fun as_TKdEqBaseSort kctx b =
  TKdEqBaseSort (kctx, TKBaseSort b, TKBaseSort b)

fun as_TKdEqSubset ke pr =
  let
      val (kctx1, k11, k12) = extract_judge_tal_kdeq ke
      val (kctx2, p2) = extract_judge_tal_proping pr
      val () = assert (k11 :: kctx1 = kctx2) "TKdEqSubset 1"
      val (opr2, p21, p22) = extract_tal_p_bin_conn p2
      val () = assert (opr2 = PBCIff) "TKdEqSubset 2"
  in
      TKdEqSubset ((kctx1, TKSubset (k11, p21), TKSubset (k12, p22)), ke, pr)
  end

fun as_TKdVar kctx x =
  TKdVar (kctx, TCVar x, shift_tal_c_k (1 + x) 0 (nth (kctx, x)))

fun as_TKdConst kctx cn =
  TKdConst (kctx, TCConst cn, const_tal_kind cn)

fun as_TKdBinOp opr kd1 kd2 =
  let
      val (kctx1, c1, k1) = extract_judge_tal_kinding kd1
      val (kctx2, c2, k2) = extract_judge_tal_kinding kd2
      val () = assert (kctx1 = kctx2) "TKdBinOp 1"
      val () = assert (k1 = cbinop_arg1_tal_kind opr) "TKdBinOp 2"
      val () = assert (k2 = cbinop_arg2_tal_kind opr) "TKdBinOp 3"
  in
      TKdBinOp ((kctx1, TCBinOp (opr, c1, c2), cbinop_result_tal_kind opr), kd1, kd2)
  end

fun as_TKdIte kd1 kd2 kd3 =
  let
      val (kctx1, c1, k1) = extract_judge_tal_kinding kd1
      val (kctx2, c2, k2) = extract_judge_tal_kinding kd2
      val (kctx3, c3, k3) = extract_judge_tal_kinding kd3
      val () = assert (kctx1 = kctx2) "TKdIte 1"
      val () = assert (kctx1 = kctx3) "TKdIte 2"
      val () = assert (k1 = TKBool) "TKdIte 3"
      val () = assert (k2 = k3) "TKdIte 4"
  in
      TKdIte ((kctx1, TCIte (c1, c2, c3), k2), kd1, kd2, kd3)
  end

fun as_TKdArrow kds kd =
  let
      val jkds = map extract_judge_tal_kinding kds
      val (kctx2, i2, k2) = extract_judge_tal_kinding kd
      val () = assert (k2 = TKTime) "TKdArrow 1"
      val () = assert (all (fn (kctx1, _, k1) => kctx1 = kctx2 andalso k1 = TKType) jkds) "TKdArrow 2"
  in
      TKdArrow ((kctx2, TCArrow (map (fn (_, t1, _) => t1) jkds, i2), TKType), kds, kd)
  end

fun as_TKdAbs wk kd =
  let
      val (kctx1, k1) = extract_judge_tal_wfkind wk
      val (kctx2, c1, k2) = extract_judge_tal_kinding kd
      val () = assert (k1 :: kctx1 = kctx2) "TKdAbs 1"
  in
      TKdAbs ((kctx1, TCAbs c1, TKArrow (k1, shift_tal_c_k ~1 0 k2)), wk, kd) (* TODO *)
  end

fun as_TKdApp kd1 kd2 =
  let
      val (kctx1, c1, k1) = extract_judge_tal_kinding kd1
      val (kctx2, c2, k2) = extract_judge_tal_kinding kd2
      val () = assert (kctx1 = kctx2) "TKdApp 1"
      val (k11, k12) = extract_tal_k_arrow k1
      val () = assert (k11 = k2) "TKdApp 2"
  in
      TKdApp ((kctx1, TCApp (c1, c2), k12), kd1, kd2)
  end

fun as_TKdTimeAbs kd =
  let
      val (kctx, c, k) = extract_judge_tal_kinding kd
      val () = assert (hd kctx = TKNat) "TKdTimeAbs 1"
      val arity = extract_tal_k_time_fun k
  in
      TKdTimeAbs ((tl kctx, TCTimeAbs c, TKTimeFun (arity + 1)), kd)
  end

fun as_TKdTimeApp kd1 kd2 =
  let
      val (kctx1, c1, k1) = extract_judge_tal_kinding kd1
      val (kctx2, c2, k2) = extract_judge_tal_kinding kd2
      val () = assert (kctx1 = kctx2) "TKdTimeApp 1"
      val () = assert (k2 = TKNat) "TKdTimeApp 2"
      val arity = extract_tal_k_time_fun k1
      val () = assert (arity > 0) "TKdTimeApp 3"
  in
      TKdTimeApp ((kctx1, TCTimeApp (arity - 1, c1, c2), TKTimeFun (arity - 1)), kd1, kd2)
  end

fun as_TKdQuan q wk kd =
  let
      val (kctx1, k1) = extract_judge_tal_wfkind wk
      val (kctx2, c2, k2) = extract_judge_tal_kinding kd
      val () = assert (k1 :: kctx1 = kctx2) "TKdQuan 1"
      val () = assert (k2 = TKType) "TKdQuan 2"
  in
      TKdQuan ((kctx1, TCQuan (q, k1, c2), TKType), wk, kd)
  end

fun as_TKdRec wk kd =
  let
      val (kctx1, k1) = extract_judge_tal_wfkind wk
      val (kctx2, c2, k2) = extract_judge_tal_kinding kd
      val () = assert (k1 :: kctx1 = kctx2) "TKdRec 1"
      val () = assert (k1 = shift_tal_c_k ~1 0 k2) "TKdRec 2"
  in
      TKdRec ((kctx1, TCRec (k1, c2), k1), wk, kd)
  end

fun as_TKdTypeNat kd =
  let
      val (kctx, c, k) = extract_judge_tal_kinding kd
      val () = assert (k = TKNat) "TKdTypeNat 1"
  in
      TKdTypeNat ((kctx, TCTypeNat c, TKType), kd)
  end

fun as_TKdTypeArr kd1 kd2 =
  let
      val (kctx1, c1, k1) = extract_judge_tal_kinding kd1
      val (kctx2, c2, k2) = extract_judge_tal_kinding kd2
      val () = assert (kctx1 = kctx2) "TKdTypeArr 1"
      val () = assert (k1 = TKType) "TKdTypeArr 2"
      val () = assert (k2 = TKNat) "TKdTypeArr 3"
  in
      TKdTypeArr ((kctx1, TCTypeArr (c1, c2), TKType), kd1, kd2)
  end

fun as_TKdEq kd ke =
  let
      val (kctx1, c1, k1) = extract_judge_tal_kinding kd
      val (kctx2, k21, k22) = extract_judge_tal_kdeq ke
      val () = assert (kctx1 = kctx2) "TKdEq 1"
      val () = assert (k1 = k21) "TKdEq 2"
  in
      TKdEq ((kctx1, c1, k22), kd, ke)
  end

fun as_TKdUnOp opr kd =
  let
      val (kctx, c, k) = extract_judge_tal_kinding kd
      val () = assert (k = cunop_arg_tal_kind opr) "TKdUnOp 1"
  in
      TKdUnOp ((kctx, TCUnOp (opr, c), cunop_result_tal_kind opr), kd)
  end

fun as_TKdAdmit kctx c k =
  TKdAdmit (kctx, c, k)

fun as_TWfKdType kctx =
  TWfKdType (kctx, TKType)

fun as_TWfKdArrow wk1 wk2 =
  let
      val (kctx1, k1) = extract_judge_tal_wfkind wk1
      val (kctx2, k2) = extract_judge_tal_wfkind wk2
      val () = assert (kctx1 = kctx2) "TWfKdArrow 1"
  in
      TWfKdArrow ((kctx1, TKArrow (k1, k2)), wk1, wk2)
  end

fun as_TWfKdBasesort kctx b =
  TWfKdBaseSort (kctx, TKBaseSort b)

fun as_TWfKdSubset wk wp =
  let
      val (kctx1, k1) = extract_judge_tal_wfkind wk
      val (kctx2, p2) = extract_judge_tal_wfprop wp
      val () = assert (k1 :: kctx1 = kctx2) "TWfKdSubset 1"
  in
      TWfKdSubset ((kctx1, TKSubset (k1, p2)), wk, wp)
  end

fun as_TWfKdAdmit kctx k =
  TWfKdAdmit (kctx, k)

fun as_TWfPropTrue kctx =
  TWfPropTrue (kctx, TPTrue)

fun as_TWfPropFalse kctx =
  TWfPropFalse (kctx, TPFalse)

fun as_TWfPropBinConn opr wp1 wp2 =
  let
      val (kctx1, p1) = extract_judge_tal_wfprop wp1
      val (kctx2, p2) = extract_judge_tal_wfprop wp2
      val () = assert (kctx1 = kctx2) "TWfPropBinConn 1"
  in
      TWfPropBinConn ((kctx1, TPBinConn (opr, p1, p2)), wp1, wp2)
  end

fun as_TWfPropNot wp =
  let
      val (kctx, p) = extract_judge_tal_wfprop wp
  in
      TWfPropNot ((kctx, TPNot p), wp)
  end

fun as_TWfPropBinPred opr kd1 kd2 =
  let
      val (kctx1, c1, k1) = extract_judge_tal_kinding kd1
      val (kctx2, c2, k2) = extract_judge_tal_kinding kd2
      val () = assert (kctx1 = kctx2) "TWfPropBinPred 1"
      val () = assert (k1 = binpred_arg1_tal_kind opr) "TWfPropBinPred 2"
      val () = assert (k2 = binpred_arg2_tal_kind opr) "TWfPropBinPred 3"
  in
      TWfPropBinPred ((kctx1, TPBinPred (opr, c1, c2)), kd1, kd2)
  end

fun as_TWfPropQuan q b wp =
  let
      val (kctx, p) = extract_judge_tal_wfprop wp
  in
      TWfPropQuan ((tl kctx, TPQuan (q, b, p)), wp)
  end

fun as_TTyEqVar kctx x =
  TTyEqVar (kctx, TCVar x, TCVar x)

fun as_TTyEqConst kctx cn =
  TTyEqConst (kctx, TCConst cn, TCConst cn)

fun as_TTyEqBinOp opr te1 te2 =
  let
      val (kctx1, t11, t12) = extract_judge_tal_tyeq te1
      val (kctx2, t21, t22) = extract_judge_tal_tyeq te2
      val () = assert (kctx1 = kctx2) "TTyEqBinOp 1"
  in
      TTyEqBinOp ((kctx1, TCBinOp (opr, t11, t21), TCBinOp (opr, t12, t22)), te1, te2)
  end

fun as_TTyEqIte te1 te2 te3 =
  let
      val (kctx1, t11, t12) = extract_judge_tal_tyeq te1
      val (kctx2, t21, t22) = extract_judge_tal_tyeq te2
      val (kctx3, t31, t32) = extract_judge_tal_tyeq te3
      val () = assert (kctx1 = kctx2) "TTyEqIte 1"
      val () = assert (kctx1 = kctx3) "TTyEqIte 2"
  in
      TTyEqIte ((kctx1, TCIte (t11, t21, t31), TCIte (t12, t22, t32)), te1, te2, te3)
  end

fun as_TTyEqArrow tes pr =
  let
      val jtes = map extract_judge_tal_tyeq tes
      val (kctx2, p2) = extract_judge_tal_proping pr
      val () = assert (all (fn (kctx1, _, _) => kctx1 = kctx2) jtes) "TTyEqArrow 1"
      val (opr2, i21, i22) = extract_tal_p_bin_pred p2
      val () = assert (opr2 = PBTimeEq) "TTyEqArrow 2"
  in
      TTyEqArrow ((kctx2, TCArrow (map (fn (_, t1, _) => t1) jtes, i21), TCArrow (map (fn (_, _, t2) => t2) jtes, i22)), tes, pr)
  end

fun as_TTyEqApp te1 te2 =
  let
      val (kctx1, t11, t12) = extract_judge_tal_tyeq te1
      val (kctx2, t21, t22) = extract_judge_tal_tyeq te2
      val () = assert (kctx1 = kctx2) "TTyEqApp 1"
  in
      TTyEqApp ((kctx1, TCApp (t11, t21), TCApp (t12, t22)), te1, te2)
  end

fun as_TTyEqBeta kctx t1 t2 = TTyEqBeta (kctx, TCApp (TCAbs t1, t2), subst0_tal_c_c t2 t1)

fun as_TTyEqBetaRev kctx t1 t2 = TTyEqBetaRev (kctx, subst0_tal_c_c t2 t1, TCApp (TCAbs t1, t2))

fun as_TTyEqQuan q ke te =
  let
      val (kctx1, k11, k12) = extract_judge_tal_kdeq ke
      val (kctx2, t21, t22) = extract_judge_tal_tyeq te
      val () = assert (k11 :: kctx1 = kctx2) "TTyEqQuan 1"
  in
      TTyEqQuan ((kctx1, TCQuan (q, k11, t21), TCQuan (q, k12, t22)), ke, te)
  end

fun as_TTyEqRec ke te =
  let
      val (kctx1, k11, k12) = extract_judge_tal_kdeq ke
      val (kctx2, t21, t22) = extract_judge_tal_tyeq te
      val () = assert (k11 :: kctx1 = kctx2) "TTyEqRec 1"
  in
      TTyEqRec ((kctx1, TCRec (k11, t21), TCRec (k12, t22)), ke, te)
  end

fun as_TTyEqTypeNat pr =
  let
      val (kctx, p) = extract_judge_tal_proping pr
      val (opr, i1, i2) = extract_tal_p_bin_pred p
      val () = assert (opr = PBNatEq) "TTyEqTypeNat 1"
  in
      TTyEqTypeNat ((kctx, TCTypeNat i1, TCTypeNat i2), pr)
  end

fun as_TTyEqTypeArr te pr =
  let
      val (kctx1, t1, t2) = extract_judge_tal_tyeq te
      val (kctx2, p) = extract_judge_tal_proping pr
      val () = assert (kctx1 = kctx2) "TTyEqTypeArr 1"
      val (opr, i1, i2) = extract_tal_p_bin_pred p
      val () = assert (opr = PBNatEq) "TTyEqTypeArr 2"
  in
      TTyEqTypeArr ((kctx1, TCTypeArr (t1, i1), TCTypeArr (t2, i2)), te, pr)
  end

fun as_TTyEqAbs kctx t = TTyEqAbs (kctx, TCAbs t, TCAbs t)

fun as_TTyEqTimeAbs kctx i = TTyEqTimeAbs (kctx, TCTimeAbs i, TCTimeAbs i)

fun as_TTyEqTimeApp kctx arity c1 c2 = TTyEqTimeApp (kctx, TCTimeApp (arity, c1, c2), TCTimeApp (arity, c1, c2))

fun as_TTyEqTrans te1 te2 =
  let
      val (kctx1, t11, t12) = extract_judge_tal_tyeq te1
      val (kctx2, t21, t22) = extract_judge_tal_tyeq te2
      val () = assert (kctx1 = kctx2) "TTyEqTrans 1"
      val () = assert (t12 = t21) "TTyEqTrans 2"
  in
      TTyEqTrans ((kctx1, t11, t22), te1, te2)
  end

fun as_TTyEqUnOp opr te =
  let
      val (kctx, t1, t2) = extract_judge_tal_tyeq te
  in
      TTyEqUnOp ((kctx, TCUnOp (opr, t1), TCUnOp (opr, t2)), te)
  end

fun as_TTyEqNat pr =
  let
      val (kctx, p) = extract_judge_tal_proping pr
      val (opr, i1, i2) = extract_tal_p_bin_pred p
      val () = assert (opr = PBNatEq) "TTyEqNat 1"
  in
      TTyEqNat ((kctx, i1, i2), pr)
  end

fun as_TTyEqTime pr =
  let
      val (kctx, p) = extract_judge_tal_proping pr
      val (opr, i1, i2) = extract_tal_p_bin_pred p
      val () = assert (opr = PBTimeEq) "TTyEqTime 1"
  in
      TTyEqTime ((kctx, i1, i2), pr)
  end

fun as_TWTyLoc hctx kctx l =
  TWTyLoc ((hctx, kctx), TWLoc l, nth (hctx, l))

fun as_TWTyConst hctx kctx cn =
  TWTyConst ((hctx, kctx), TWConst cn, const_tal_type cn)

fun as_TWTyAppC wty kd =
  let
      val ((hctx1, kctx1), w1, t1) = extract_judge_tal_word_typing wty
      val (kctx2, c2, k2) = extract_judge_tal_kinding kd
      val () = assert (kctx1 = kctx2) "TWTyAppC"
      val (q11, k12, t13) = extract_tal_c_quan t1
      val () = assert (q11 = QuanForall) "TWTyAppC"
      val () = assert (k12 = k2) "TWTyAppC"
  in
      TWTyAppC (((hctx1, kctx1), TWAppC (w1, c2), subst0_tal_c_c c2 t13), wty, kd)
  end

fun as_TWTyPack kd1 kd2 wty =
  let
      val (kctx1, c1, k1) = extract_judge_tal_kinding kd1
      val (kctx2, c2, k2) = extract_judge_tal_kinding kd2
      val ((hctx3, kctx3), w3, t3) = extract_judge_tal_word_typing wty
      val () = assert (kctx1 = kctx2) "TWTyPack"
      val () = assert (kctx1 = kctx3) "TWTyPack"
      val () = assert (k1 = TKType) "TWTyPack"
      val (q11, k12, t13) = extract_tal_c_quan c1
      val () = assert (q11 = QuanExists) "TWTyPack"
      val () = assert (k12 = k2) "TWTyPack"
      val () = assert (subst0_tal_c_c c2 t13 = t3) "TWTyPack"
  in
      TWTyPack (((hctx3, kctx3), TWPack (c2, w3), c1), kd1, kd2, wty)
  end

fun as_TWTySub wty te =
  let
      val ((hctx1, kctx1), w1, t1) = extract_judge_tal_word_typing wty
      val (kctx2, t21, t22) = extract_judge_tal_tyeq te
      val () = assert (kctx1 = kctx2) "TWTySub"
      val () = assert (t21 = t1) "TWTySub"
  in
      TWTySub (((hctx1, kctx1), w1, t22), wty, te)
  end

fun as_TWTyLocAdmit hctx kctx l t = TWTyLocAdmit ((hctx, kctx), TWLoc l, t)

fun as_TVTyReg hctx kctx tctx r =
  TVTyReg ((hctx, kctx, tctx), TVReg r, nth (tctx, r))

fun as_TVTyWord tctx wty =
  let
      val ((hctx, kctx), w, t) = extract_judge_tal_word_typing wty
  in
      TVTyWord (((hctx, kctx, tctx), TVWord w, t), wty)
  end

fun as_TVTyAppC vty kd =
  let
      val ((hctx1, kctx1, tctx1), v1, t1) = extract_judge_tal_value_typing vty
      val (kctx2, c2, k2) = extract_judge_tal_kinding kd
      val () = assert (kctx1 = kctx2) "TVTyAppC"
      val (q11, k12, t13) = extract_tal_c_quan t1
      val () = assert (q11 = QuanForall) "TVTyAppC"
      val () = assert (k12 = k2) "TVTyAppC"
  in
      TVTyAppC (((hctx1, kctx1, tctx1), TVAppC (v1, c2), subst0_tal_c_c c2 t13), vty, kd)
  end

fun as_TVTyPack kd1 kd2 vty =
  let
      val (kctx1, c1, k1) = extract_judge_tal_kinding kd1
      val (kctx2, c2, k2) = extract_judge_tal_kinding kd2
      val ((hctx3, kctx3, tctx3), v3, t3) = extract_judge_tal_value_typing vty
      val () = assert (kctx1 = kctx2) "TVTyPack"
      val () = assert (kctx1 = kctx3) "TVTyPack"
      val () = assert (k1 = TKType) "TVTyPack"
      val (q11, k12, t13) = extract_tal_c_quan c1
      val () = assert (q11 = QuanExists) "TVTyPack"
      val () = assert (k12 = k2) "TVTyPack"
      val () = assert (subst0_tal_c_c c2 t13 = t3) "TVTyPack"
  in
      TVTyPack (((hctx3, kctx3, tctx3), TVPack (c2, v3), c1), kd1, kd2, vty)
  end

fun as_TVTySub vty te =
  let
      val ((hctx1, kctx1, tctx1), v1, t1) = extract_judge_tal_value_typing vty
      val (kctx2, t21, t22) = extract_judge_tal_tyeq te
      val () = assert (kctx1 = kctx2) "TVTySub"
      val () = assert (t21 = t1) "TVTySub"
  in
      TVTySub (((hctx1, kctx1, tctx1), v1, t22), vty, te)
  end

fun as_TITyNewpair rd vty1 vty2 ity =
  let
      val ((hctx1, kctx1, tctx1), v1, t1) = extract_judge_tal_value_typing vty1
      val ((hctx2, kctx2, tctx2), v2, t2) = extract_judge_tal_value_typing vty2
      val ((hctx3, kctx3, tctx3), (ins3, fin3), i3) = extract_judge_tal_instr_typing ity
      val () = assert ((hctx1, kctx1, tctx1) = (hctx2, kctx2, tctx2)) "TITyNewpair"
      val () = assert (hctx3 = hctx1) "TITyNewpair"
      val () = assert (kctx3 = kctx1) "TITyNewpair"
      val () = assert (update_tal_tctx rd (TCProd (t1, t2)) tctx1 = tctx3) "TITyNewpair"
      val rs = extract_tal_v_reg v1
      val rt = extract_tal_v_reg v2
  in
      TITyNewpair (((hctx1, kctx1, tctx1), (TINewpair (rd, rs, rt) :: ins3, fin3), TTadd (TT1, i3)), vty1, vty2, ity)
  end

fun as_TITyProj p rd vty ity =
  let
      val ((hctx1, kctx1, tctx1), v1, t1) = extract_judge_tal_value_typing vty
      val ((hctx2, kctx2, tctx2), (ins2, fin2), i2) = extract_judge_tal_instr_typing ity
      val () = assert (hctx2 = hctx1) "TITyProj"
      val () = assert (kctx2 = kctx1) "TITyProj"
      val (t11, t12) = extract_tal_c_prod t1
      val () = assert (update_tal_tctx rd (case p of ProjFst => t11
                                                   | ProjSnd => t12) tctx1 = tctx2) "TITyProj"
      val rs = extract_tal_v_reg v1
  in
      TITyProj (((hctx1, kctx1, tctx1), (TIProj (p, rd, rs) :: ins2, fin2), TTadd (TT1, i2)), vty, ity)
  end

fun as_TITyInj inj vty kd ity =
  let
      val ((hctx1, kctx1, tctx1), v1, t1) = extract_judge_tal_value_typing vty
      val (kctx2, t2, k2) = extract_judge_tal_kinding kd
      val ((hctx3, kctx3, tctx3), (ins3, fin3), i3) = extract_judge_tal_instr_typing ity
      val () = assert (kctx2 = kctx1) "TITyInj"
      val () = assert (hctx3 = hctx1) "TITyInj"
      val () = assert (kctx3 = kctx1) "TITyInj"
      val () = assert (k2 = TKType) "TITyInj"
      val rd = extract_tal_v_reg v1
      val () = assert (update_tal_tctx rd (case inj of InjInl => TCSum (t1, t2)
                                                     | InjInr => TCSum (t2, t1)) tctx1 = tctx3) "TITyInj"
  in
      TITyInj (((hctx1, kctx1, tctx1), (TIInj (inj, rd) :: ins3, fin3), TTadd (TT1, i3)), vty, kd, ity)
  end

fun as_TITyFold kd vty ity =
  let
      val (kctx1, t1, k1) = extract_judge_tal_kinding kd
      val ((hctx2, kctx2, tctx2), v2, t2) = extract_judge_tal_value_typing vty
      val ((hctx3, kctx3, tctx3), (ins3, fin3), i3) = extract_judge_tal_instr_typing ity
      val () = assert (kctx1 = kctx2) "TITyFold"
      val () = assert (hctx3 = hctx2) "TITyFold"
      val () = assert (kctx3 = kctx2) "TITyFold"
      val () = assert (k1 = TKType) "TITyFold"
      fun unwrap_TCApp t cs =
        case t of
            TCApp (c1, c2) => unwrap_TCApp c1 (c2 :: cs)
          | _ => (t, cs)
      val (t11, cs12) = unwrap_TCApp t1 []
      val (k111, t111) = extract_tal_c_rec t11
      val () = assert (t2 = TCApps (subst0_tal_c_c t11 t111) cs12) "TITyFold"
      val rd = extract_tal_v_reg v2
      val () = assert (update_tal_tctx rd t1 tctx2 = tctx3) "TITyFold"
  in
      TITyFold (((hctx2, kctx2, tctx2), (TIFold rd :: ins3, fin3), TTadd (TT1, i3)), kd, vty, ity)
  end

fun as_TITyUnfold vty ity =
  let
      val ((hctx1, kctx1, tctx1), v1, t1) = extract_judge_tal_value_typing vty
      val ((hctx2, kctx2, tctx2), (ins2, fin2), i2) = extract_judge_tal_instr_typing ity
      val () = assert (hctx2 = hctx1) "TITyUnfold"
      val () = assert (kctx2 = kctx1) "TITyUnfold"
      fun unwrap_TCApp t cs =
        case t of
            TCApp (c1, c2) => unwrap_TCApp c1 (c2 :: cs)
          | _ => (t, cs)
      val (t11, cs12) = unwrap_TCApp t1 []
      val (k111, t111) = extract_tal_c_rec t11
      val rd = extract_tal_v_reg v1
      val () = assert (update_tal_tctx rd (TCApps (subst0_tal_c_c t11 t111) cs12) tctx1 = tctx2) "TITyUnfold"
  in
      TITyUnfold (((hctx1, kctx1, tctx1), (TIUnfold rd :: ins2, fin2), TTadd (TT1, i2)), vty, ity)
  end

(* fun as_TITyNewref rd vty ity = *)
(*   let *)
(*       val ((hctx1, kctx1, tctx1), v1, t1) = extract_judge_tal_value_typing vty *)
(*       val ((hctx2, kctx2, tctx2), (ins2, fin2), i2) = extract_judge_tal_instr_typing ity *)
(*       val () = assert (hctx2 = hctx1) "TITyNewref" *)
(*       val () = assert (kctx2 = kctx1) "TITyNewref" *)
(*       val () = assert (update_tal_tctx rd (TCRef t1) tctx1 = tctx2) "TITyNewref" *)
(*       val rs = extract_tal_v_reg v1 *)
(*   in *)
(*       TITyNewref (((hctx1, kctx1, tctx1), (TINewref (rd, rs) :: ins2, fin2), TTadd (TT1, i2)), vty, ity) *)
(*   end *)

(* fun as_TITyDeref rd vty ity = *)
(*   let *)
(*       val ((hctx1, kctx1, tctx1), v1, t1) = extract_judge_tal_value_typing vty *)
(*       val ((hctx2, kctx2, tctx2), (ins2, fin2), i2) = extract_judge_tal_instr_typing ity *)
(*       val () = assert (hctx2 = hctx1) "TITyDeref" *)
(*       val () = assert (kctx2 = kctx1) "TITyDeref" *)
(*       val t11 = extract_tal_c_ref t1 *)
(*       val () = assert (update_tal_tctx rd t11 tctx1 = tctx2) "TITyDeref" *)
(*       val rs = extract_tal_v_reg v1 *)
(*   in *)
(*       TITyDeref (((hctx1, kctx1, tctx1), (TIDeref (rd, rs) :: ins2, fin2), TTadd (TT1, i2)), vty, ity) *)
(*   end *)

(* fun as_TITySetref vty1 vty2 ity = *)
(*   let *)
(*       val ((hctx1, kctx1, tctx1), v1, t1) = extract_judge_tal_value_typing vty1 *)
(*       val ((hctx2, kctx2, tctx2), v2, t2) = extract_judge_tal_value_typing vty2 *)
(*       val ((hctx3, kctx3, tctx3), (ins3, fin3), i3) = extract_judge_tal_instr_typing ity *)
(*       val () = assert ((hctx1, kctx1, tctx1) = (hctx2, kctx2, tctx2)) "TITySetref" *)
(*       val () = assert (hctx3 = hctx1) "TITySetref" *)
(*       val () = assert (kctx3 = kctx1) "TITySetref" *)
(*       val () = assert (tctx3 = tctx1) "TITySetref" *)
(*       val () = assert (t1 = TCRef t2) "TITySetref" *)
(*       val rd = extract_tal_v_reg v1 *)
(*       val rs = extract_tal_v_reg v2 *)
(*   in *)
(*       TITySetref (((hctx1, kctx1, tctx1), (TISetref (rd, rs) :: ins3, fin3), TTadd (TT1, i3)), vty1, vty2, ity) *)
(*   end *)

fun as_TITyPrimBinOp opr rd vty1 vty2 ity =
  let
      val ((hctx1, kctx1, tctx1), v1, t1) = extract_judge_tal_value_typing vty1
      val ((hctx2, kctx2, tctx2), v2, t2) = extract_judge_tal_value_typing vty2
      val ((hctx3, kctx3, tctx3), (ins3, fin3), i3) = extract_judge_tal_instr_typing ity
      val () = assert ((hctx1, kctx1, tctx1) = (hctx2, kctx2, tctx2)) "TITyPrimBinOp"
      val () = assert (hctx3 = hctx1) "TITyPrimBinOp"
      val () = assert (kctx3 = kctx1) "TITyPrimBinOp"
      val () = assert (t1 = pebinop_arg1_tal_type opr) "TITyPrimBinOp"
      val () = assert (t2 = pebinop_arg2_tal_type opr) "TITyPrimBinOp"
      val () = assert (update_tal_tctx rd (pebinop_result_tal_type opr) tctx1 = tctx3) "TITyPrimBinOp"
      val rs = extract_tal_v_reg v1
      val rt = extract_tal_v_reg v2
  in
      TITyPrimBinOp (((hctx1, kctx1, tctx1), (TIPrimBinOp (opr, rd, rs, rt) :: ins3, fin3), TTadd (TT1, i3)), vty1, vty2, ity)
  end

fun as_TITyMove rd vty ity =
  let
      val ((hctx1, kctx1, tctx1), v1, t1) = extract_judge_tal_value_typing vty
      val ((hctx2, kctx2, tctx2), (ins2, fin2), i2) = extract_judge_tal_instr_typing ity
      val () = assert (hctx2 = hctx1) "TITyMove"
      val () = assert (kctx2 = kctx1) "TITyMove"
      val () = assert (update_tal_tctx rd t1 tctx1 = tctx2) "TITyMove"
  in
      TITyMove (((hctx1, kctx1, tctx1), (TIMove (rd, v1) :: ins2, fin2), TTadd (TT1, i2)), vty, ity)
  end

fun as_TITyUnpack rd vty ity =
  let
      val ((hctx1, kctx1, tctx1), v1, t1) = extract_judge_tal_value_typing vty
      val ((hctx2, kctx2, tctx2), (ins2, fin2), i2) = extract_judge_tal_instr_typing ity
      val () = assert (hctx2 = hctx1) "TITyUnpack"
      val (q11, k12, t13) = extract_tal_c_quan t1
      val () = assert (q11 = QuanExists) "TITyUnpack"
      val () = assert (kctx2 = k12 :: kctx1) "TITyUnpack"
      val () = assert (update_tal_tctx rd t13 (map shift0_tal_c_c tctx1) = tctx2) "TITyUnpack"
  in
      TITyUnpack (((hctx1, kctx1, tctx1), (TIUnpack (rd, v1) :: ins2, fin2), TTadd (TT1, shift_tal_c_c ~1 0 i2)), vty, ity)
  end

fun as_TITyCase vty1 ity vty2 =
  let
      val ((hctx1, kctx1, tctx1), v1, t1) = extract_judge_tal_value_typing vty1
      val ((hctx2, kctx2, tctx2), (ins2, fin2), i2) = extract_judge_tal_instr_typing ity
      val ((hctx3, kctx3, tctx3), v3, t3) = extract_judge_tal_value_typing vty2
      val () = assert ((hctx1, kctx1, tctx1) = (hctx3, kctx3, tctx3)) "TITyCase"
      val () = assert (hctx2 = hctx1) "TITyCase"
      val () = assert (kctx2 = kctx1) "TITyCase"
      val (t11, t12) = extract_tal_c_sum t1
      val r = extract_tal_v_reg v1
      val () = assert (update_tal_tctx r t11 tctx1 = tctx2) "TITyCase"
      val (tctx31, i32) = extract_tal_c_arrow t3
      val () = assert (List.take (tl (update_tal_tctx r t12 tctx1), length tctx31) = tctx31) "TITyCase"
  in
      TITyCase (((hctx1, kctx1, tctx1), (TICase (r, v3) :: ins2, fin2), TTadd (TT1, TTmax (i2, i32))), vty1, ity, vty2)
  end

fun as_TITyJump vty =
  let
      val ((hctx, kctx, tctx), v, t) = extract_judge_tal_value_typing vty
      val (tctx1, i2) = extract_tal_c_arrow t
      val () = assert (List.take (tl tctx, length tctx1) = tctx1) "TITyJump"
  in
      TITyJump (((hctx, kctx, tctx), ([], TCJump v), TTadd (TT1, i2)), vty)
  end

fun as_TITyHalt vty =
  let
      val ((hctx, kctx, tctx), v, t) = extract_judge_tal_value_typing vty
      val () = assert (v = TVReg 1) "TITyHalt"
  in
      TITyHalt (((hctx, kctx, tctx), ([], TCHalt t), TT1), vty)
  end

fun as_TITySub ity pr =
  let
      val ((hctx1, kctx1, tctx1), (ins1, fin1), i1) = extract_judge_tal_instr_typing ity
      val (kctx2, p2) = extract_judge_tal_proping pr
      val () = assert (kctx1 = kctx2) "TITySub"
      val (opr, i21, i22) = extract_tal_p_bin_pred p2
      val () = assert (opr = PBTimeLe) "TITySub"
      val () = assert (i21 = i1) "TITySub"
  in
      TITySub (((hctx1, kctx1, tctx1), (ins1, fin1), i22), ity, pr)
  end

fun as_THTyCode kd ity =
  let
      val (kctx1, t1, k1) = extract_judge_tal_kinding kd
      val ((hctx2, kctx2, tctx2), (ins2, fin2), i2) = extract_judge_tal_instr_typing ity
      val () = assert (kctx1 = []) "THTyCode"
      val () = assert (k1 = TKType) "THTyCode"
      fun unwrap_TCForall t ks =
        case t of
            TCQuan (QuanForall, k, t) => unwrap_TCForall t (k :: ks)
          | _ => (t, ks)
      val (t11, ks12) = unwrap_TCForall t1 []
      val () = assert (kctx2 = ks12) "THTyCode"
      val (tctx111, i112) = extract_tal_c_arrow t11
      val () = assert (t1 :: tctx111 = tctx2) "THTyCode"
      val () = assert (i112 = i2) "THTyCode"
  in
      THTyCode ((hctx2, THCode (length kctx2, (ins2, fin2)), t1), kd, ity)
  end

fun as_THTyPair wty1 wty2 =
  let
      val ((hctx1, kctx1), w1, t1) = extract_judge_tal_word_typing wty1
      val ((hctx2, kctx2), w2, t2) = extract_judge_tal_word_typing wty2
      val () = assert (hctx1 = hctx2) "THTyPair"
      val () = assert (kctx1 = []) "THTyPair"
      val () = assert (kctx2 = []) "THTyPair"
  in
      THTyPair ((hctx1, THPair (w1, w2), TCProd (t1, t2)), wty1, wty2)
  end

fun as_THTyWord wty =
  let
      val ((hctx, kctx), w, t) = extract_judge_tal_word_typing wty
      val () = assert (kctx = []) "THTyWord"
  in
      THTyWord ((hctx, THWord w, t), wty)
  end

fun as_TPTyProgram htys wtys ity =
  let
      val jhtys = map extract_judge_tal_heap_typing htys
      val jwtys = map extract_judge_tal_word_typing wtys
      val ((hctx3, kctx3, tctx3), (ins3, fin3), i3) = extract_judge_tal_instr_typing ity
      val () = assert (hctx3 = map (fn (_, _, t) => t) jhtys) "TPTyProgram"
      val () = assert (kctx3 = []) "TPTyProgram"
      val () = assert (hd tctx3 = TCTypeUnit) "TPTyProgram"
      val () = assert (tl tctx3 = map (fn (_, _, t) => t) jwtys) "TPTyProgram"
      val () = assert (all (fn (hctx, _, _) => hctx = hctx3) jhtys) "TPTyProgram"
      val () = assert (all (fn ((hctx, kctx), _, _) => hctx = hctx3 andalso kctx = []) jwtys) "TPTyProgram"
  in
      TPTyProgram ((TProgram (map (fn (_, h, _) => h) jhtys, map (fn (_, w, _) => w) jwtys, (ins3, fin3)), i3), htys, wtys, ity)
  end
end

functor CodeGenPassFun(TypedAssemblyDef : SIG_TYPED_ASSEMBLY_DEF) =
struct
open List
open Util
infixr 0 $

structure TypedAssemblyDef = TypedAssemblyDef
open TypedAssemblyDef
open MicroTiMLHoistedDef
structure TALDerivAssembler = TALDerivAssemblerFun(TypedAssemblyDef)
open TALDerivAssembler

fun transform_cstr c =
  case c of
      CVar x => TCVar x
    | CConst cn => TCConst cn
    | CBinOp (opr, c1, c2) => TCBinOp (opr, transform_cstr c1, transform_cstr c2)
    | CIte (i1, i2, i3) => TCIte (transform_cstr i1, transform_cstr i2, transform_cstr i3)
    | CTimeAbs c => TCTimeAbs (transform_cstr c)
    | CTimeApp (arity, c1, c2) => TCTimeApp (arity, transform_cstr c1, transform_cstr c2)
    | CArrow (t1, i, t2) => TCArrow ([transform_cstr t1], transform_cstr i)
    | CAbs c => TCAbs (transform_cstr c)
    | CApp (c1, c2) => TCApp (transform_cstr c1, transform_cstr c2)
    | CQuan (q, k, c) => TCQuan (q, transform_kind k, transform_cstr c)
    | CRec (k, c) => TCRec (transform_kind k, transform_cstr c)
    | CTypeNat c => TCTypeNat (transform_cstr c)
    | CTypeArr (c1, c2) => TCTypeArr (transform_cstr c1, transform_cstr c2)
    | CUnOp (opr, c) => TCUnOp (opr, transform_cstr c)

and transform_kind k =
    case k of
        KType => TKType
      | KArrow (k1, k2) => TKArrow (transform_kind k1, transform_kind k2)
      | KBaseSort b => TKBaseSort b
      | KSubset (k, p) => TKSubset (transform_kind k, transform_prop p)

and transform_prop p =
    case p of
        PTrue => TPTrue
      | PFalse => TPFalse
      | PBinConn (opr, p1, p2) => TPBinConn (opr, transform_prop p1, transform_prop p2)
      | PNot p => TPNot (transform_prop p)
      | PBinPred (opr, i1, i2) => TPBinPred (opr, transform_cstr i1, transform_cstr i2)
      | PQuan (q, b, p) => TPQuan (q, b, transform_prop p)

fun transform_proping (pr, kctx) =
  case pr of
      PrAdmit (_, p) => as_TPrAdmit kctx (transform_prop p)

fun transform_kdeq (ke, kctx) =
  case ke of
      KdEqKType _ => as_TKdEqKType kctx
    | KdEqKArrow (_, ke1, ke2) => as_TKdEqKArrow (transform_kdeq (ke1, kctx)) (transform_kdeq (ke2, kctx))
    | KdEqBaseSort (_, KBaseSort b, _) => as_TKdEqBaseSort kctx b
    | KdEqSubset (_, ke1, pr2) =>
      let
          val ke1 = transform_kdeq (ke1, kctx)
          val (_, k11, _) = extract_judge_tal_kdeq ke1
          val pr2 = transform_proping (pr2, k11 :: kctx)
      in
          as_TKdEqSubset ke1 pr2
      end
    | _ => raise (Impossible "transform_kdeq")

fun transform_kinding (kd, kctx) =
  case kd of
      KdVar (_, CVar x, _) => as_TKdVar kctx x
    | KdConst (_, CConst cn, _) => as_TKdConst kctx cn
    | KdBinOp ((_, CBinOp (opr, _, _), _), kd1, kd2) => as_TKdBinOp opr (transform_kinding (kd1, kctx)) (transform_kinding (kd2, kctx))
    | KdIte (_, kd1, kd2, kd3) => as_TKdIte (transform_kinding (kd1, kctx)) (transform_kinding (kd2, kctx)) (transform_kinding (kd3, kctx))
    | KdArrow (_, kd1, kd2, kd3) => as_TKdArrow [transform_kinding (kd1, kctx)] (transform_kinding (kd2, kctx))
    | KdAbs (_, wk1, kd2) =>
      let
          val wk1 = transform_wfkind (wk1, kctx)
          val (_, k1) = extract_judge_tal_wfkind wk1
          val kd2 = transform_kinding (kd2, k1 :: kctx)
      in
          as_TKdAbs wk1 kd2
      end
    | KdApp (_, kd1, kd2) => as_TKdApp (transform_kinding (kd1, kctx)) (transform_kinding (kd2, kctx))
    | KdTimeAbs (_, kd) => as_TKdTimeAbs (transform_kinding (kd, TKNat :: kctx))
    | KdTimeApp (_, kd1, kd2) => as_TKdTimeApp (transform_kinding (kd1, kctx)) (transform_kinding (kd2, kctx))
    | KdQuan ((_, CQuan (q, _, _), _), wk1, kd2) =>
      let
          val wk1 = transform_wfkind (wk1, kctx)
          val (_, k1) = extract_judge_tal_wfkind wk1
          val kd2 = transform_kinding (kd2, k1 :: kctx)
      in
          as_TKdQuan q wk1 kd2
      end
    | KdRec (_, wk1, kd2) =>
      let
          val wk1 = transform_wfkind (wk1, kctx)
          val (_, k1) = extract_judge_tal_wfkind wk1
          val kd2 = transform_kinding (kd2, k1 :: kctx)
      in
          as_TKdRec wk1 kd2
      end
    | KdEq (_, kd1, ke2) => as_TKdEq (transform_kinding (kd1, kctx)) (transform_kdeq (ke2, kctx))
    | KdUnOp ((_, CUnOp (opr, _), _), kd) => as_TKdUnOp opr (transform_kinding (kd, kctx))
    | KdAdmit (_, c, k) => as_TKdAdmit kctx (transform_cstr c) (transform_kind k)
    | _ => raise (Impossible "transform_kinding")

and transform_wfkind (wk, kctx) =
    case wk of
        WfKdType (_, _) => as_TWfKdType kctx
      | WfKdArrow (_, wk1, wk2) => as_TWfKdArrow (transform_wfkind (wk1, kctx)) (transform_wfkind (wk2, kctx))
      | WfKdBaseSort (_, KBaseSort b) => as_TWfKdBasesort kctx b
      | WfKdSubset (_, wk1, wp2) =>
        let
            val wk1 = transform_wfkind (wk1, kctx)
            val (_, k1) = extract_judge_tal_wfkind wk1
            val wp2 = transform_wfprop (wp2, k1 :: kctx)
        in
            as_TWfKdSubset wk1 wp2
        end
      | WfKdAdmit (_, k) => as_TWfKdAdmit kctx (transform_kind k)
      | _ => raise (Impossible "transform_wfkind")

and transform_wfprop (wp, kctx) =
  case wp of
      WfPropTrue _ => as_TWfPropTrue kctx
    | WfPropFalse _ => as_TWfPropFalse kctx
    | WfPropBinConn ((_, PBinConn (opr, _, _)), wp1, wp2) => as_TWfPropBinConn opr (transform_wfprop (wp1, kctx)) (transform_wfprop (wp2, kctx))
    | WfPropNot (_, wp) => as_TWfPropNot (transform_wfprop (wp, kctx))
    | WfPropBinPred ((_, PBinPred (opr, _, _)), kd1, kd2) => as_TWfPropBinPred opr (transform_kinding (kd1, kctx)) (transform_kinding (kd2, kctx))
    | WfPropQuan ((_, PQuan (q, b, _)), wp) => as_TWfPropQuan q b (transform_wfprop (wp, TKBaseSort b :: kctx))
    | _ => raise (Impossible "transform_wfprop")

fun transform_tyeq (te, kctx) =
  case te of
      TyEqVar (_, CVar x, _) => as_TTyEqVar kctx x
    | TyEqConst (_, CConst cn, _) => as_TTyEqConst kctx cn
    | TyEqBinOp ((_, CBinOp (opr, _, _), _), te1, te2) => as_TTyEqBinOp opr (transform_tyeq (te1, kctx)) (transform_tyeq (te2, kctx))
    | TyEqIte (_, te1, te2, te3) => as_TTyEqIte (transform_tyeq (te1, kctx)) (transform_tyeq (te2, kctx)) (transform_tyeq (te3, kctx))
    | TyEqArrow (_, te1, pr2, te3) => as_TTyEqArrow [transform_tyeq (te1, kctx)] (transform_proping (pr2, kctx))
    | TyEqApp (_, te1, te2) => as_TTyEqApp (transform_tyeq (te1, kctx)) (transform_tyeq (te2, kctx))
    | TyEqQuan ((_, CQuan (q, _, _), _), ke1, te2) =>
      let
          val ke1 = transform_kdeq (ke1, kctx)
          val (_, k11, _) = extract_judge_tal_kdeq ke1
          val te2 = transform_tyeq (te2, k11 :: kctx)
      in
          as_TTyEqQuan q ke1 te2
      end
    | TyEqRec (_, ke1, te2) =>
      let
          val ke1 = transform_kdeq (ke1, kctx)
          val (_, k11, _) = extract_judge_tal_kdeq ke1
          val te2 = transform_tyeq (te2, k11 :: kctx)
      in
          as_TTyEqRec ke1 te2
      end
    | TyEqAbs (_, t1, _) => as_TTyEqAbs kctx (transform_cstr t1)
    | TyEqTimeAbs (_, t1, _) => as_TTyEqTimeAbs kctx (transform_cstr t1)
    | TyEqUnOp ((_, CUnOp (opr, _), _), te) => as_TTyEqUnOp opr (transform_tyeq (te, kctx))
    | TyEqNat (_, pr) => as_TTyEqNat (transform_proping (pr, kctx))
    | _ => raise (Impossible "transform_tyeq")

fun fresh_reg tctx = length tctx

fun transform_atom_typing kctx tctx env aty =
  case aty of
      ATyVar (_, AEVar x, _, _) => as_TVTyReg [] kctx tctx $ nth (env, x)
    | ATyConst (_, AEConst cn, _, _) => as_TVTyWord tctx (as_TWTyConst [] kctx cn)
    | ATyFuncPointer (_, AEFuncPointer l, t, _) => as_TVTyWord tctx (as_TWTyLocAdmit [] kctx l (transform_cstr t))
    | ATyAppC (_, aty1, kd2) => as_TVTyAppC (transform_atom_typing kctx tctx env aty1) (transform_kinding (kd2, kctx))
    | ATyPack (_, kd1, kd2, aty3) => as_TVTyPack (transform_kinding (kd1, kctx)) (transform_kinding (kd2, kctx)) (transform_atom_typing kctx tctx env aty3)
    | ATySubTy (_, aty1, te2) => as_TVTySub (transform_atom_typing kctx tctx env aty1) (transform_tyeq (te2, kctx))
    | ATySubTi (_, aty1, _) => transform_atom_typing kctx tctx env aty1
    | _ => raise (Impossible "transform_atom_typing")

fun transform_hoisted_typing heap_base kctx tctx env hty =
  case hty of
      HTyHalt (_, aty) =>
      let
          val vty = transform_atom_typing kctx tctx env aty
          val (_, _, t) = extract_judge_tal_value_typing vty
          val tctx1 = update_tal_tctx 1 t tctx
          val ity1 = as_TITyHalt (as_TVTyReg [] kctx tctx1 1)
          val ity = as_TITyMove 1 vty ity1
      in
          ([], heap_base, ity)
      end
    | HTyApp (_, aty1, aty2) =>
      let
          val vty1 = transform_atom_typing kctx tctx env aty1
          val rd =
              let
                  val tmp_rd = fresh_reg tctx
              in
                  if tmp_rd = 1 then 2 else tmp_rd
              end
          val (_, _, t1) = extract_judge_tal_value_typing vty1
          val tctx1 = update_tal_tctx rd t1 tctx
          val vty2 = transform_atom_typing kctx tctx1 env aty2
          val (_, _, t2) = extract_judge_tal_value_typing vty2
          val tctx2 = update_tal_tctx 1 t2 tctx1
          val ity2 = as_TITyJump (as_TVTyReg [] kctx tctx2 rd)
          val ity1 = as_TITyMove 1 vty2 ity2
          val ity = as_TITyMove rd vty1 ity1
      in
          ([], heap_base, ity)
      end
    | HTySubTi (_, hty1, pr2) =>
      let
          val (htys, heap_next, ity) = transform_hoisted_typing heap_base kctx tctx env hty1
          val (_, _, ori_i) = extract_judge_tal_instr_typing ity
          val pr2 = transform_proping (pr2, kctx)
          val (_, _, as_i) = extract_tal_p_bin_pred (snd $ extract_judge_tal_proping pr2)
      in
          (htys, heap_next, as_TITySub ity (as_TPrAdmit kctx (TTLe (ori_i, as_i)))) (* FIXME: time annotations *)
      end
    | HTyUnpack (_, aty1, hty2) =>
      let
          val vty1 = transform_atom_typing kctx tctx env aty1
          val rd = fresh_reg tctx
          val (_, _, t1) = extract_judge_tal_value_typing vty1
          val (_, k11, t12) = extract_tal_c_quan t1
          val kctx1 = k11 :: kctx
          val tctx1 = update_tal_tctx rd t12 (map shift0_tal_c_c tctx)
          val (heaps1, heap_next, ity1) = transform_hoisted_typing heap_base kctx1 tctx1 (rd :: env) hty2
          val ity = as_TITyUnpack rd vty1 ity1
      in
          (heaps1, heap_next, ity)
      end
    | HTyCase (_, aty1, hty2, hty3) =>
      let
          val vty1 = transform_atom_typing kctx tctx env aty1
          val rd = fresh_reg tctx
          val (_, _, t1) = extract_judge_tal_value_typing vty1
          val (t11, t12) = extract_tal_c_sum t1
          val tctx1 = update_tal_tctx rd t1 tctx
          val (heaps2, heap_next_mid, ity2) = transform_hoisted_typing heap_base kctx (update_tal_tctx rd t11 tctx1) (rd :: env) hty2
          val dummy_i = transform_cstr $ #3 (extract_judge_htyping hty3) (* FIXME: time annotations *)
          val dummy_t =
              let
                  val t1 = TCArrow (tl (update_tal_tctx rd t12 tctx1), dummy_i)
              in
                  foldl (fn (k, t) => TCForall (k, t)) t1 kctx
              end
          val (heaps3, heap_next, ity3) = transform_hoisted_typing heap_next_mid kctx (update_tal_tctx 0 dummy_t (update_tal_tctx rd t12 tctx1)) (rd :: env) hty3
          val ity3 = as_TITySub ity3 (as_TPrAdmit kctx (TTLe (#3 (extract_judge_tal_instr_typing ity3), dummy_i)))
          val new_loc = heap_next
          val heap_next = heap_next + 1
          val (new_loc_ty, new_heap_ty) =
              let
                  val t_loc = dummy_t
                  val wty1 = as_TWTyLocAdmit [] kctx new_loc t_loc
                  val vty1 = as_TVTyWord tctx1 wty1
                  val new_loc_ty = foldri (fn (i, _, vty) =>
                            let
                                val (_, _, t) = extract_judge_tal_value_typing vty
                                val (_, k, _) = extract_tal_c_quan t
                                val kd = as_TKdVar kctx i
                            in
                                as_TVTyAppC vty kd
                            end) vty1 kctx
                  val new_heap_ty = as_THTyCode (as_TKdAdmit [] t_loc TKType) ity3 (* FIXME: kinding admit *)
              in
                  (new_loc_ty, new_heap_ty)
              end
          val ity1 = as_TITyCase (as_TVTyReg [] kctx tctx1 rd) ity2 new_loc_ty
          val ity = as_TITyMove rd vty1 ity1
      in
          (heaps2 @ heaps3 @ [new_heap_ty], heap_next, ity)
      end
    | HTyLet (_, cty1, hty2) =>
      let
          fun inner cty1 tes =
            case cty1 of
                CTyProj ((_, CEUnOp (EUProj p, _), _, _), aty1) =>
                let
                    val vty1 = transform_atom_typing kctx tctx env aty1
                    val rs = fresh_reg tctx
                    val (_, _, t1) = extract_judge_tal_value_typing vty1
                    val tctx1 = update_tal_tctx rs t1 tctx
                    val rd = fresh_reg tctx1
                    val (t11, t12) = extract_tal_c_prod t1
                    val tctx2 = update_tal_tctx rd (case p of ProjFst => t11
                                                            | ProjSnd => t12) tctx1
                    val vty_rd = foldl (fn (te, vty) => as_TVTySub vty te) (as_TVTyReg [] kctx tctx2 rd) tes
                    val (_, _, t_rd) = extract_judge_tal_value_typing vty_rd
                    val tctx3 = update_tal_tctx rd t_rd tctx2
                    val (heaps3, heap_next, ity3) = transform_hoisted_typing heap_base kctx tctx3 (rd :: env) hty2
                    val ity2 = as_TITyMove rd vty_rd ity3
                    val ity1 = as_TITyProj p rd (as_TVTyReg [] kctx tctx1 rs) ity2
                    val ity = as_TITyMove rs vty1 ity1
                in
                    (heaps3, heap_next, ity)
                end
              | CTyPair (_, aty1, aty2) =>
                let
                    val vty1 = transform_atom_typing kctx tctx env aty1
                    val rs = fresh_reg tctx
                    val (_, _, t1) = extract_judge_tal_value_typing vty1
                    val tctx1 = update_tal_tctx rs t1 tctx
                    val vty2 = transform_atom_typing kctx tctx1 env aty2
                    val rt = fresh_reg tctx1
                    val (_, _, t2) = extract_judge_tal_value_typing vty2
                    val tctx2 = update_tal_tctx rt t2 tctx1
                    val rd = fresh_reg tctx2
                    val tctx3 = update_tal_tctx rd (TCProd (t1, t2)) tctx2
                    val vty_rd = foldl (fn (te, vty) => as_TVTySub vty te) (as_TVTyReg [] kctx tctx3 rd) tes
                    val (_, _, t_rd) = extract_judge_tal_value_typing vty_rd
                    val tctx4 = update_tal_tctx rd t_rd tctx3
                    val (heaps4, heap_next, ity4) = transform_hoisted_typing heap_base kctx tctx4 (rd :: env) hty2
                    val ity3 = as_TITyMove rd vty_rd ity4
                    val ity2 = as_TITyNewpair rd (as_TVTyReg [] kctx tctx2 rs) (as_TVTyReg [] kctx tctx2 rt) ity3
                    val ity1 = as_TITyMove rt vty2 ity2
                    val ity = as_TITyMove rs vty1 ity1
                in
                    (heaps4, heap_next, ity)
                end
              | CTyInj ((_, CEUnOp (EUInj inj, _), _, _), aty1, kd2) =>
                let
                    val vty1 = transform_atom_typing kctx tctx env aty1
                    val rd = fresh_reg tctx
                    val (_, _, t1) = extract_judge_tal_value_typing vty1
                    val tctx1 = update_tal_tctx rd t1 tctx
                    val kd2 = transform_kinding (kd2, kctx)
                    val (_, t2, _) = extract_judge_tal_kinding kd2
                    val tctx2 = update_tal_tctx rd (case inj of InjInl => TCSum (t1, t2)
                                                              | InjInr => TCSum (t2, t1)) tctx1
                    val vty_rd = foldl (fn (te, vty) => as_TVTySub vty te) (as_TVTyReg [] kctx tctx2 rd) tes
                    val (_, _, t_rd) = extract_judge_tal_value_typing vty_rd
                    val tctx3 = update_tal_tctx rd t_rd tctx2
                    val (heaps3, heap_next, ity3) = transform_hoisted_typing heap_base kctx tctx3 (rd :: env) hty2
                    val ity2 = as_TITyMove rd vty_rd ity3
                    val ity1 = as_TITyInj inj (as_TVTyReg [] kctx tctx1 rd) kd2 ity2
                    val ity = as_TITyMove rd vty1 ity1
                in
                    (heaps3, heap_next, ity)
                end
              | CTyFold (_, kd1, aty2) =>
                let
                    val vty2 = transform_atom_typing kctx tctx env aty2
                    val rd = fresh_reg tctx
                    val (_, _, t2) = extract_judge_tal_value_typing vty2
                    val tctx1 = update_tal_tctx rd t2 tctx
                    val kd1 = transform_kinding (kd1, kctx)
                    val (_, t1, _) = extract_judge_tal_kinding kd1
                    val tctx2 = update_tal_tctx rd t1 tctx1
                    val vty_rd = foldl (fn (te, vty) => as_TVTySub vty te) (as_TVTyReg [] kctx tctx2 rd) tes
                    val (_, _, t_rd) = extract_judge_tal_value_typing vty_rd
                    val tctx3 = update_tal_tctx rd t_rd tctx2
                    val (heaps3, heap_next, ity3) = transform_hoisted_typing heap_base kctx tctx3 (rd :: env) hty2
                    val ity2 = as_TITyMove rd vty_rd ity3
                    val ity1 = as_TITyFold kd1 (as_TVTyReg [] kctx tctx1 rd) ity2
                    val ity = as_TITyMove rd vty2 ity1
                in
                    (heaps3, heap_next, ity)
                end
              | CTyUnfold (_, aty1) =>
                let
                    val vty1 = transform_atom_typing kctx tctx env aty1
                    val rd = fresh_reg tctx
                    val (_, _, t1) = extract_judge_tal_value_typing vty1
                    val tctx1 = update_tal_tctx rd t1 tctx
                    fun unwrap_TCApp t cs =
                      case t of
                          TCApp (c1, c2) => unwrap_TCApp c1 (c2 :: cs)
                        | _ => (t, cs)
                    val (t11, cs12) = unwrap_TCApp t1 []
                    val (k111, t111) = extract_tal_c_rec t11
                    val tctx2 = update_tal_tctx rd (TCApps (subst0_tal_c_c t11 t111) cs12) tctx1
                    val vty_rd = foldl (fn (te, vty) => as_TVTySub vty te) (as_TVTyReg [] kctx tctx2 rd) tes
                    val (_, _, t_rd) = extract_judge_tal_value_typing vty_rd
                    val tctx3 = update_tal_tctx rd t_rd tctx2
                    val (heaps3, heap_next, ity3) = transform_hoisted_typing heap_base kctx tctx3 (rd :: env) hty2
                    val ity2 = as_TITyMove rd vty_rd ity3
                    val ity1 = as_TITyUnfold (as_TVTyReg [] kctx tctx1 rd) ity2
                    val ity = as_TITyMove rd vty1 ity1
                in
                    (heaps3, heap_next, ity)
                end
              (* | CTyNew (_, aty1) => *)
              (*   let *)
              (*       val vty1 = transform_atom_typing kctx tctx env aty1 *)
              (*       val rs = fresh_reg tctx *)
              (*       val (_, _, t1) = extract_judge_tal_value_typing vty1 *)
              (*       val tctx1 = update_tal_tctx rs t1 tctx *)
              (*       val rd = fresh_reg tctx1 *)
              (*       val tctx2 = update_tal_tctx rd (TCRef t1) tctx1 *)
              (*       val vty_rd = foldl (fn (te, vty) => as_TVTySub vty te) (as_TVTyReg [] kctx tctx2 rd) tes *)
              (*       val (_, _, t_rd) = extract_judge_tal_value_typing vty_rd *)
              (*       val tctx3 = update_tal_tctx rd t_rd tctx2 *)
              (*       val (heaps3, heap_next, ity3) = transform_hoisted_typing heap_base kctx tctx3 (rd :: env) hty2 *)
              (*       val ity2 = as_TITyMove rd vty_rd ity3 *)
              (*       val ity1 = as_TITyNewref rd (as_TVTyReg [] kctx tctx1 rs) ity2 *)
              (*       val ity = as_TITyMove rs vty1 ity1 *)
              (*   in *)
              (*       (heaps3, heap_next, ity) *)
              (*   end *)
              (* | CTyRead (_, aty1) => *)
              (*   let *)
              (*       val vty1 = transform_atom_typing kctx tctx env aty1 *)
              (*       val rs = fresh_reg tctx *)
              (*       val (_, _, t1) = extract_judge_tal_value_typing vty1 *)
              (*       val tctx1 = update_tal_tctx rs t1 tctx *)
              (*       val rd = fresh_reg tctx *)
              (*       val tctx2 = update_tal_tctx rd (extract_tal_c_ref t1) tctx1 *)
              (*       val vty_rd = foldl (fn (te, vty) => as_TVTySub vty te) (as_TVTyReg [] kctx tctx2 rd) tes *)
              (*       val (_, _, t_rd) = extract_judge_tal_value_typing vty_rd *)
              (*       val tctx3 = update_tal_tctx rd t_rd tctx2 *)
              (*       val (heaps3, heap_next, ity3) = transform_hoisted_typing heap_base kctx tctx3 (rd :: env) hty2 *)
              (*       val ity2 = as_TITyMove rd vty_rd ity3 *)
              (*       val ity1 = as_TITyDeref rd (as_TVTyReg [] kctx tctx1 rs) ity2 *)
              (*       val ity = as_TITyMove rs vty1 ity1 *)
              (*   in *)
              (*       (heaps3, heap_next, ity) *)
              (*   end *)
              (* | CTyWrite (_, aty1, aty2) => *)
              (*   let *)
              (*       val vty1 = transform_atom_typing kctx tctx env aty1 *)
              (*       val rd = fresh_reg tctx *)
              (*       val (_, _, t1) = extract_judge_tal_value_typing vty1 *)
              (*       val tctx1 = update_tal_tctx rd t1 tctx *)
              (*       val vty2 = transform_atom_typing kctx tctx1 env aty2 *)
              (*       val rs = fresh_reg tctx1 *)
              (*       val (_, _, t2) = extract_judge_tal_value_typing vty2 *)
              (*       val tctx2 = update_tal_tctx rs t2 tctx1 *)
              (*       val (heaps3, heap_next, ity3) = transform_hoisted_typing heap_base kctx tctx2 (~1 :: env) hty2 (* CPS should eliminate the use of result of a writing *) *)
              (*       val ity2 = as_TITySetref (as_TVTyReg [] kctx tctx2 rd) (as_TVTyReg [] kctx tctx2 rs) ity3 *)
              (*       val ity1 = as_TITyMove rs vty2 ity2 *)
              (*       val ity = as_TITyMove rd vty1 ity1 *)
              (*   in *)
              (*       (heaps3, heap_next, ity) *)
              (*   end *)
              | CTyPrimBinOp ((_, CEBinOp (EBPrim opr, _, _), _, _), aty1, aty2) =>
                let
                    val vty1 = transform_atom_typing kctx tctx env aty1
                    val rs = fresh_reg tctx
                    val (_, _, t1) = extract_judge_tal_value_typing vty1
                    val tctx1 = update_tal_tctx rs t1 tctx
                    val vty2 = transform_atom_typing kctx tctx1 env aty2
                    val rt = fresh_reg tctx1
                    val (_, _, t2) = extract_judge_tal_value_typing vty2
                    val tctx2 = update_tal_tctx rt t2 tctx1
                    val rd = fresh_reg tctx2
                    val tctx3 = update_tal_tctx rd (pebinop_result_tal_type opr) tctx2
                    val vty_rd = foldl (fn (te, vty) => as_TVTySub vty te) (as_TVTyReg [] kctx tctx3 rd) tes
                    val (_, _, t_rd) = extract_judge_tal_value_typing vty_rd
                    val tctx4 = update_tal_tctx rd t_rd tctx3
                    val (heaps4, heap_next, ity4) = transform_hoisted_typing heap_base kctx tctx4 (rd :: env) hty2
                    val ity3 = as_TITyMove rd vty_rd ity4
                    val ity2 = as_TITyPrimBinOp opr rd (as_TVTyReg [] kctx tctx2 rs) (as_TVTyReg [] kctx tctx2 rt) ity3
                    val ity1 = as_TITyMove rt vty2 ity2
                    val ity = as_TITyMove rs vty1 ity1
                in
                    (heaps4, heap_next, ity)
                end
              | CTyAtom (_, aty1) =>
                let
                    val vty1 = foldl (fn (te, vty) => as_TVTySub vty te) (transform_atom_typing kctx tctx env aty1) tes
                    val rd = fresh_reg tctx
                    val (_, _, t1) = extract_judge_tal_value_typing vty1
                    val tctx1 = update_tal_tctx rd t1 tctx
                    val (heaps1, heap_next, ity1) = transform_hoisted_typing heap_base kctx tctx1 (rd :: env) hty2
                    val ity = as_TITyMove rd vty1 ity1
                in
                    (heaps1, heap_next, ity)
                end
              | CTySubTy (_, cty1, te2) =>
                let
                    val te2 = transform_tyeq (te2, kctx)
                in
                    inner cty1 (te2 :: tes)
                end
              | CTySubTi (_, cty1, _) => inner cty1 tes
              | _ => raise (Impossible "transform_hoisted_typing")
      in
          inner cty1 []
      end

fun transform_func_typing heap_base fty =
  case fty of
      FTyFix (_, kd1, hty2) =>
      let
          val kd1 = transform_kinding (kd1, [])
          val (_, t_out, _) = extract_judge_tal_kinding kd1
          fun unwrap_TCForall kd wks =
            case kd of
                TKdQuan ((_, TCQuan (QuanForall, _, _), _), wk, kd) => unwrap_TCForall kd (wk :: wks)
              | TKdEq _ => raise (Impossible "not supported")
              | TKdAdmit (kctx, TCQuan (QuanForall, k, c), _) => unwrap_TCForall (as_TKdAdmit (k :: kctx) c TKType) (as_TWfKdAdmit kctx k :: wks)
              | _ => (kd, wks)
          val (kd11, wks12) = unwrap_TCForall kd1 []
          val kctx = map (snd o extract_judge_tal_wfkind) wks12
          val (_, t_self, _) = extract_judge_tal_kinding kd11
          val (t_reg, i_self) = extract_tal_c_arrow t_self
          val tctx = t_out :: t_reg
          val env = [1, 0]
          val (heaps, heap_next, ity) = transform_hoisted_typing heap_base kctx tctx env hty2
      in
          (heaps, heap_next, as_THTyCode kd1 ity)
      end

fun set_hctx_word_typing hctx wty =
  let
      fun inner wty =
        case wty of
            TWTyLoc ((_, kctx), TWLoc loc, _) => as_TWTyLoc hctx kctx loc
          | TWTyConst ((_, kctx), TWConst cn, _) => as_TWTyConst hctx kctx cn
          | TWTyAppC (_, wty1, kd2) => as_TWTyAppC (inner wty1) kd2
          | TWTyPack (_, kd1, kd2, wty3) => as_TWTyPack kd1 kd2 (inner wty3)
          | TWTySub (_, wty1, te2) => as_TWTySub (inner wty1) te2
          | TWTyLocAdmit ((_, kctx), TWLoc loc, _) => as_TWTyLoc hctx kctx loc
          | _ => raise (Impossible "set_hctx_word_typing")
  in
      inner wty
  end

fun set_hctx_value_typing hctx vty =
  let
      val on_wty = set_hctx_word_typing hctx
      fun inner vty =
        case vty of
            TVTyReg ((_, kctx, tctx), TVReg reg, _) => as_TVTyReg hctx kctx tctx reg
          | TVTyWord (((_, _, tctx), _, _), wty) => as_TVTyWord tctx (on_wty wty)
          | TVTyAppC (_, vty1, kd2) => as_TVTyAppC (inner vty1) kd2
          | TVTyPack (_, kd1, kd2, vty3) => as_TVTyPack kd1 kd2 (inner vty3)
          | TVTySub (_, vty1, te2) => as_TVTySub (inner vty1) te2
          | _ => raise (Impossible "set_hctx_value_typing")
  in
      inner vty
  end

fun set_hctx_instr_typing hctx ity =
  let
      val on_vty = set_hctx_value_typing hctx
      fun inner ity =
        case ity of
            TITyNewpair ((_, (TINewpair (rd, _, _) :: _, _), _), vty1, vty2, ity3) => as_TITyNewpair rd (on_vty vty1) (on_vty vty2) (inner ity3)
          | TITyProj ((_, (TIProj (p, rd, _) :: _, _), _), vty1, ity2) => as_TITyProj p rd (on_vty vty1) (inner ity2)
          | TITyInj ((_, (TIInj (inj, _) :: _, _), _), vty1, kd2, ity3) => as_TITyInj inj (on_vty vty1) kd2 (inner ity3)
          | TITyFold ((_, (TIFold _ :: _, _), _), kd1, vty2, ity3) => as_TITyFold kd1 (on_vty vty2) (inner ity3)
          | TITyUnfold ((_, (TIUnfold _ :: _, _), _), vty1, ity2) => as_TITyUnfold (on_vty vty1) (inner ity2)
          (* | TITyNewref ((_, (TINewref (rd, _) :: _, _), _), vty1, ity2) => as_TITyNewref rd (on_vty vty1) (inner ity2) *)
          (* | TITyDeref ((_, (TIDeref (rd, _) :: _, _), _), vty1, ity2) => as_TITyDeref rd (on_vty vty1) (inner ity2) *)
          (* | TITySetref ((_, (TISetref _ :: _, _), _), vty1, vty2, ity3) => as_TITySetref (on_vty vty1) (on_vty vty2) (inner ity3) *)
          | TITyPrimBinOp ((_, (TIPrimBinOp (opr, rd, _, _) :: _, _), _), vty1, vty2, ity3) => as_TITyPrimBinOp opr rd (on_vty vty1) (on_vty vty2) (inner ity3)
          | TITyMove ((_, (TIMove (rd, _) :: _, _), _), vty1, ity2) => as_TITyMove rd (on_vty vty1) (inner ity2)
          | TITyUnpack ((_, (TIUnpack (rd, _) :: _, _), _), vty1, ity2) => as_TITyUnpack rd (on_vty vty1) (inner ity2)
          | TITyCase ((_, (TICase _ :: _, _), _), vty1, ity2, vty3) => as_TITyCase (on_vty vty1) (inner ity2) (on_vty vty3)
          | TITyJump (_, vty) => as_TITyJump (on_vty vty)
          | TITyHalt (_, vty) => as_TITyHalt (on_vty vty)
          | TITySub (_, ity1, pr2) => as_TITySub (inner ity1) pr2
          | _ => raise (Impossible "set_hctx_instr_typing")
  in
      inner ity
  end

fun set_hctx_heap_typing hctx hty =
  let
      val on_ity = set_hctx_instr_typing hctx
      val on_wty = set_hctx_word_typing hctx
      fun inner hty =
        case hty of
            THTyCode (_, kd1, ity2) => as_THTyCode kd1 (on_ity ity2)
          | THTyPair (_, wty1, wty2) => as_THTyPair (on_wty wty1) (on_wty wty2)
          | THTyWord (_, wty) => as_THTyWord (on_wty wty)
  in
      inner hty
  end

fun transform_program_typing ty =
  case ty of
      TyProgram (_, ftys, hty_main) =>
      let
          val root_len = length ftys
          val (heaps, heap_next, rev_htys) = foldl (fn (fty, (heaps, heap_next, rev_htys)) =>
                                                       let
                                                           val (heaps_d, heap_next_d, hty) = transform_func_typing heap_next fty
                                                       in
                                                           (heaps @ heaps_d, heap_next_d, hty :: rev_htys)
                                                       end) ([], root_len, []) ftys
          val htys = rev rev_htys
          val (heaps_d, _, ity_main) = transform_hoisted_typing heap_next [] [TCTypeUnit] [] hty_main
          val whole_heaps = htys @ heaps @ heaps_d
          val hctx = map (fn hty => #3 (extract_judge_tal_heap_typing hty)) whole_heaps
          val ity_main = set_hctx_instr_typing hctx ity_main
          val whole_heaps = map (set_hctx_heap_typing hctx) whole_heaps
      in
          as_TPTyProgram whole_heaps [] ity_main
      end

val code_gen_deriv = transform_program_typing
end
