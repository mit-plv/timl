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
         | TCRec of tal_kind * tal_cstr
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
         | TTyEqNat of tal_tyeq_judgement * tal_proping

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

fun TTfromNat c = TCUnOp (CUNat2Time, c)

fun TPAnd (p1, p2) = TPBinConn (PBCAnd, p1, p2)
fun TPOr (p1, p2) = TPBinConn (PBCOr, p1, p2)
fun TPImply (p1, p2) = TPBinConn (PBCImply, p1, p2)
fun TPIff (p1, p2) = TPBinConn (PBCIff, p1, p2)

fun TTmax (c1, c2) = TCBinOp (CBTimeMax, c1, c2)

fun TCForall (k, c) = TCQuan (QuanForall, k, c)
fun TCExists (k, c) = TCQuan (QuanExists, k, c)

val TCTypeUnit = TCConst CCTypeUnit

fun TCProd (c1, c2) = TCBinOp (CBTypeProd, c1, c2)
fun TCSum (c1, c2) = TCBinOp (CBTypeSum, c1, c2)

fun TTLe (c1, c2) = TPBinPred (PBTimeLe, c1, c2)
fun TTEq (c1, c2) = TPBinPred (PBTimeEq, c1, c2)

val TCTypeInt = TCConst CCTypeInt
fun TCNat n = TCConst (CCIdxNat n)

fun TCApps t cs =
  case cs of
      [] => t
    | c :: cs => TCApps (TCApp (t, c)) cs

val TBSTime = BSTimeFun 0

fun const_tal_kind cn =
  case cn of
      CCIdxTT => TKUnit
    | CCIdxNat _ => TKNat
    | CCTime _ => TKTime
    | CCTypeUnit => TKType
    | CCTypeInt => TKType

fun const_tal_type cn =
  case cn of
      ECTT => TCTypeUnit
    | ECInt _ => TCTypeInt

fun cbinop_arg1_tal_kind opr =
  case opr of
      CBTimeAdd => TKTime
    | CBTimeMinus => TKTime
    | CBTimeMult => TKTime
    | CBTimeMax => TKTime
    | CBTypeProd => TKType
    | CBTypeSum => TKType
    | CBNatAdd => TKNat

fun cbinop_arg2_tal_kind opr =
  case opr of
      CBTimeAdd => TKTime
    | CBTimeMinus => TKTime
    | CBTimeMult => TKTime
    | CBTimeMax => TKTime
    | CBTypeProd => TKType
    | CBTypeSum => TKType
    | CBNatAdd => TKNat

fun cbinop_result_tal_kind opr =
  case opr of
      CBTimeAdd => TKTime
    | CBTimeMinus => TKTime
    | CBTimeMult => TKTime
    | CBTimeMax => TKTime
    | CBTypeProd => TKType
    | CBTypeSum => TKType
    | CBNatAdd => TKNat

fun cunop_arg_tal_kind opr =
  case opr of
      CUNat2Time => TKNat

fun cunop_result_tal_kind opr =
  case opr of
      CUNat2Time => TKTime

fun binpred_arg1_tal_kind opr =
  case opr of
      PBTimeLe => TKTime
    | PBTimeEq => TKTime
    | PBBigO n => TKTimeFun n
    | PBNatEq => TKNat

fun binpred_arg2_tal_kind opr =
  case opr of
      PBTimeLe => TKTime
    | PBTimeEq => TKTime
    | PBBigO n => TKTimeFun n
    | PBNatEq => TKNat

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

structure TALUtil =
struct
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
    | TTyEqTimeApp (j, _, _) => j
    | TTyEqBeta (j, _, _, _) => j
    | TTyEqBetaRev (j, _, _, _) => j
    | TTyEqQuan (j, _, _) => j
    | TTyEqRec (j, _, _) => j
    | TTyEqRef (j, _) => j
    | TTyEqAbs j => j
    | TTyEqTimeAbs j => j
    | TTyEqUnOp (j, _) => j
    | TTyEqNat (j, _) => j

fun extract_judge_tal_word_typing wty =
  case wty of
      TWTyLoc j => j
    | TWTyConst j => j
    | TWTyAppC (j, _, _) => j
    | TWTyPack (j, _, _, _) => j
    | TWTySub (j, _, _) => j

fun extract_judge_tal_value_typing vty =
  case vty of
      TVTyReg j => j
    | TVTyWord (j, _) => j
    | TVTyAppC (j, _, _) => j
    | TVTyPack (j, _, _, _) => j
    | TVTySub (j, _, _) => j

fun extract_judge_tal_instr_typing ity =
  case ity of
      TITyNewpair (j, _, _, _) => j
    | TITyProj (j, _, _) => j
    | TITyInj (j, _, _, _) => j
    | TITyFold (j, _, _, _) => j
    | TITyUnfold (j, _, _) => j
    | TITyNewref (j, _, _) => j
    | TITyDeref (j, _, _) => j
    | TITySetref (j, _, _, _) => j
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

fun extract_tal_c_ref (TCRef a) = a
  | extract_tal_c_ref _ = raise (Impossible "extract_tal_c_ref")

fun extract_tal_c_sum (TCBinOp (CBTypeSum, t1, t2)) = (t1, t2)
  | extract_tal_c_sum _ = raise (Impossible "extract_tal_c_sum")

fun extract_tal_v_reg (TVReg r) = r
  | extract_tal_v_reg _ = raise (Impossible "extract_tal_v_reg")
end

functor TALCstrGenericTransformer(
    Action:
    sig
        type down
        type up

        val upward_base : up
        val combiner : up * up -> up

        val add_tal_kind : tal_kind option * down -> down

        val transformer_tal_cstr : (tal_cstr * down -> tal_cstr * up) * (tal_kind * down -> tal_kind * up) -> tal_cstr * down -> (tal_cstr * up) option
        val transformer_tal_kind : (tal_kind * down -> tal_kind * up) * (tal_prop * down -> tal_prop * up) -> tal_kind * down -> (tal_kind * up) option
        val transformer_tal_prop : (tal_prop * down -> tal_prop * up) * (tal_cstr * down -> tal_cstr * up) -> tal_prop * down -> (tal_prop * up) option
    end) =
struct
val combine = foldl Action.combiner Action.upward_base

fun default_transform_tal_cstr (c, down) =
  case c of
      TCVar x => (TCVar x, Action.upward_base)
    | TCConst cn => (TCConst cn, Action.upward_base)
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
          val (i, up1) = transform_tal_cstr (i, Action.add_tal_kind (SOME TKTime, down))
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
          val (t, up1) = transform_tal_cstr (t, Action.add_tal_kind (NONE, down))
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
          val (c, up2) = transform_tal_cstr (c, Action.add_tal_kind (SOME k, down))
      in
          (TCQuan (q, k, c), combine [up1, up2])
      end
    | TCRec (k, t) =>
      let
          val (k, up1) = transform_tal_kind (k, down)
          val (t, up2) = transform_tal_cstr (t, Action.add_tal_kind (SOME k, down))
      in
          (TCRec (k, t), combine [up1, up2])
      end
    | TCRef t =>
      let
          val (t, up1) = transform_tal_cstr (t, down)
      in
          (TCRef t, combine [up1])
      end
    | TCUnOp (opr, c) =>
      let
          val (c, up1) = transform_tal_cstr (c, down)
      in
          (TCUnOp (opr, c), combine [up1])
      end

and transform_tal_cstr (c, down) =
    case Action.transformer_tal_cstr (transform_tal_cstr, transform_tal_kind) (c, down) of
        SOME res => res
      | NONE => default_transform_tal_cstr (c, down)

and default_transform_tal_kind (k, down) =
    case k of
        TKType => (TKType, Action.upward_base)
      | TKArrow (k1, k2) =>
        let
            val (k1, up1) = transform_tal_kind (k1, down)
            val (k2, up2) = transform_tal_kind (k2, down)
        in
            (TKArrow (k1, k2), combine [up1, up2])
        end
      | TKBaseSort b => (TKBaseSort b, Action.upward_base)
      | TKSubset (k, p) =>
        let
            val (k, up1) = transform_tal_kind (k, down)
            val (p, up2) = transform_tal_prop (p, Action.add_tal_kind (SOME k, down))
        in
            (TKSubset (k, p), combine [up1, up2])
        end

and transform_tal_kind (k, down) =
    case Action.transformer_tal_kind (transform_tal_kind, transform_tal_prop) (k, down) of
        SOME res => res
      | NONE => default_transform_tal_kind (k, down)

and default_transform_tal_prop (p, down) =
    case p of
        TPTrue => (TPTrue, Action.upward_base)
      | TPFalse => (TPFalse, Action.upward_base)
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
            val (p, up1) = transform_tal_prop (p, Action.add_tal_kind (SOME (TKBaseSort b), down))
        in
            (TPQuan (q, b, p), combine [up1])
        end

and transform_tal_prop (p, down) =
    case Action.transformer_tal_prop (transform_tal_prop, transform_tal_cstr) (p, down) of
        SOME res => res
      | NONE => default_transform_tal_prop (p, down)
end

functor TALCstrGenericOnlyDownTransformer(
    Action:
    sig
        type down

        val add_tal_kind : tal_kind option * down -> down

        val transformer_tal_cstr : (tal_cstr * down -> tal_cstr) * (tal_kind * down -> tal_kind) -> tal_cstr * down -> tal_cstr option
        val transformer_tal_kind : (tal_kind * down -> tal_kind) * (tal_prop * down -> tal_prop) -> tal_kind * down -> tal_kind option
        val transformer_tal_prop : (tal_prop * down -> tal_prop) * (tal_cstr * down -> tal_cstr) -> tal_prop * down -> tal_prop option
    end) =
struct
structure Transformer = TALCstrGenericTransformer(
    struct
    type down = Action.down
    type up = unit

    val upward_base = ()
    fun combiner ((), ()) = ()

    val add_tal_kind = Action.add_tal_kind

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

structure ShiftTALCstr =
struct
structure CstrHelper = TALCstrGenericOnlyDownTransformer(
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

structure CstrHelper = TALCstrGenericOnlyDownTransformer(
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

structure TALDerivAssembler =
struct
open ShiftTALCstr
open SubstTALCstr
open TALUtil

exception AssembleFail of string

fun assert b msg =
  if b then () else raise AssembleFail msg

fun as_TPrAdmit kctx p =
  TPrAdmit (kctx, p)

fun as_TKdEqKType kctx =
  TKdEqKType (kctx, TKType, TKType)

fun as_TKdEqKArrow ke1 ke2 =
  let
      val (kctx1, k11, k12) = extract_judge_tal_kdeq ke1
      val (kctx2, k21, k22) = extract_judge_tal_kdeq ke2
      val () = assert (kctx1 = kctx2) "TKdEqKArrow"
  in
      TKdEqKArrow ((kctx1, TKArrow (k11, k21), TKArrow (k12, k22)), ke1, ke2)
  end

fun as_TKdEqBaseSort kctx b =
  TKdEqBaseSort (kctx, TKBaseSort b, TKBaseSort b)

fun as_TKdEqSubset ke pr =
  let
      val (kctx1, k11, k12) = extract_judge_tal_kdeq ke
      val (kctx2, p2) = extract_judge_tal_proping pr
      val () = assert (k11 :: kctx1 = kctx2) "TKdEqSubset"
      val (opr2, p21, p22) = extract_tal_p_bin_conn p2
      val () = assert (opr2 = PBCIff) "TKdEqSubset"
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
      val () = assert (kctx1 = kctx2) "TKdBinOp"
      val () = assert (k1 = cbinop_arg1_tal_kind opr) "TKdBinOp"
      val () = assert (k2 = cbinop_arg2_tal_kind opr) "TKdBinOp"
  in
      TKdBinOp ((kctx1, TCBinOp (opr, c1, c2), cbinop_result_tal_kind opr), kd1, kd2)
  end

fun as_TKdIte kd1 kd2 kd3 =
  let
      val (kctx1, c1, k1) = extract_judge_tal_kinding kd1
      val (kctx2, c2, k2) = extract_judge_tal_kinding kd2
      val (kctx3, c3, k3) = extract_judge_tal_kinding kd3
      val () = assert (kctx1 = kctx2) "TKdIte"
      val () = assert (kctx1 = kctx3) "TKdIte"
      val () = assert (k1 = TKBool) "TKdIte"
      val () = assert (k2 = k3) "TKdIte"
  in
      TKdIte ((kctx1, TCIte (c1, c2, c3), k2), kd1, kd2, kd3)
  end

fun as_TKdArrow kds kd =
  let
      val jkds = map extract_judge_tal_kinding kds
      val (kctx2, i2, k2) = extract_judge_tal_kinding kd
      val () = assert (k2 = TKTime) "TKdArrow"
      val () = assert (all (fn (kctx1, _, k1) => kctx1 = kctx2 andalso k1 = TKType) jkds) "TKdArrow"
  in
      TKdArrow ((kctx2, TCArrow (map (fn (_, t1, _) => t1) jkds, i2), TKType), kds, kd)
  end

fun as_TKdAbs wk kd =
  let
      val (kctx1, k1) = extract_judge_tal_wfkind wk
      val (kctx2, c1, k2) = extract_judge_tal_kinding kd
      val () = assert (k1 :: kctx1 = kctx2) "TKdAbs"
  in
      TKdAbs ((kctx1, TCAbs c1, TKArrow (k1, shift_tal_c_k ~1 0 k2)), wk, kd)
  end

fun as_TKdApp kd1 kd2 =
  let
      val (kctx1, c1, k1) = extract_judge_tal_kinding kd1
      val (kctx2, c2, k2) = extract_judge_tal_kinding kd2
      val () = assert (kctx1 = kctx2) "TKdApp"
      val (k11, k12) = extract_tal_k_arrow k1
      val () = assert (k11 = k2) "TKdApp"
  in
      TKdApp ((kctx1, TCApp (c1, c2), k12), kd1, kd2)
  end

fun as_TKdTimeAbs kd =
  let
      val (kctx, c, k) = extract_judge_tal_kinding kd
      val arity = extract_tal_k_time_fun k
  in
      TKdTimeAbs ((tl kctx, TCTimeAbs c, TKTimeFun (arity + 1)), kd)
  end

fun as_TKdTimeApp kd1 kd2 =
  let
      val (kctx1, c1, k1) = extract_judge_tal_kinding kd1
      val (kctx2, c2, k2) = extract_judge_tal_kinding kd2
      val () = assert (kctx1 = kctx2) "TKdTimeApp"
      val () = assert (k2 = TKNat) "TKdTimeApp"
      val arity = extract_tal_k_time_fun k1
  in
      TKdTimeApp ((kctx1, TCTimeApp (arity - 1, c1, c2), TKTimeFun (arity - 1)), kd1, kd2)
  end

fun as_TKdQuan q wk kd =
  let
      val (kctx1, k1) = extract_judge_tal_wfkind wk
      val (kctx2, c2, k2) = extract_judge_tal_kinding kd
      val () = assert (k1 :: kctx1 = kctx2) "TKdQuan"
      val () = assert (k2 = TKType) "TKdQuan"
  in
      TKdQuan ((kctx1, TCQuan (q, k1, c2), TKType), wk, kd)
  end

fun as_TKdRec wk kd =
  let
      val (kctx1, k1) = extract_judge_tal_wfkind wk
      val (kctx2, c2, k2) = extract_judge_tal_kinding kd
      val () = assert (k1 :: kctx1 = kctx2) "TKdRec"
      val () = assert (k1 = shift_tal_c_k ~1 0 k2) "TKdRec"
  in
      TKdRec ((kctx1, TCRec (k1, c2), k1), wk, kd)
  end

fun as_TKdEq kd ke =
  let
      val (kctx1, c1, k1) = extract_judge_tal_kinding kd
      val (kctx2, k21, k22) = extract_judge_tal_kdeq ke
      val () = assert (kctx1 = kctx2) "TKdEq"
      val () = assert (k1 = k22) "TKdEq"
  in
      TKdEq ((kctx1, c1, k21), kd, ke)
  end

fun as_TKdUnOp opr kd =
  let
      val (kctx, c, k) = extract_judge_tal_kinding kd
      val () = assert (k = cunop_arg_tal_kind opr) "TKdUnOp"
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
      val () = assert (kctx1 = kctx2) "TWfKdArrow"
  in
      TWfKdArrow ((kctx1, TKArrow (k1, k2)), wk1, wk2)
  end

fun as_TWfKdBasesort kctx b =
  TWfKdBaseSort (kctx, TKBaseSort b)

fun as_TWfKdSubset wk wp =
  let
      val (kctx1, k1) = extract_judge_tal_wfkind wk
      val (kctx2, p2) = extract_judge_tal_wfprop wp
      val () = assert (k1 :: kctx1 = kctx2) "TWfKdSubset"
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
      val () = assert (kctx1 = kctx2) "TWfPropBinConn"
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
      val () = assert (kctx1 = kctx2) "TWfPropBinPred"
      val () = assert (k1 = binpred_arg1_tal_kind opr) "TWfPropBinPred"
      val () = assert (k2 = binpred_arg2_tal_kind opr) "TWfPropBinPred"
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
      val () = assert (kctx1 = kctx2) "TTyEqBinOp"
  in
      TTyEqBinOp ((kctx1, TCBinOp (opr, t11, t21), TCBinOp (opr, t12, t22)), te1, te2)
  end

fun as_TTyEqIte te1 te2 te3 =
  let
      val (kctx1, t11, t12) = extract_judge_tal_tyeq te1
      val (kctx2, t21, t22) = extract_judge_tal_tyeq te2
      val (kctx3, t31, t32) = extract_judge_tal_tyeq te3
      val () = assert (kctx1 = kctx2) "TTyEqIte"
      val () = assert (kctx1 = kctx3) "TTyEqIte"
  in
      TTyEqIte ((kctx1, TCIte (t11, t21, t31), TCIte (t12, t22, t32)), te1, te2, te3)
  end

fun as_TTyEqArrow tes pr =
  let
      val jtes = map extract_judge_tal_tyeq tes
      val (kctx2, p2) = extract_judge_tal_proping pr
      val () = assert (all (fn (kctx1, _, _) => kctx1 = kctx2) jtes) "TTyEqArrow"
      val (opr2, i21, i22) = extract_tal_p_bin_pred p2
      val () = assert (opr2 = PBTimeEq) "TTyEqArrow"
  in
      TTyEqArrow ((kctx2, TCArrow (map (fn (_, t1, _) => t1) jtes, i21), TCArrow (map (fn (_, _, t2) => t2) jtes, i22)), tes, pr)
  end

fun as_TTyEqApp te1 te2 =
  let
      val (kctx1, t11, t12) = extract_judge_tal_tyeq te1
      val (kctx2, t21, t22) = extract_judge_tal_tyeq te2
      val () = assert (kctx1 = kctx2) "TTyEqApp"
  in
      TTyEqApp ((kctx1, TCApp (t11, t21), TCApp (t12, t22)), te1, te2)
  end

fun as_TTyEqTimeApp arity te1 te2 =
  let
      val (kctx1, t11, t12) = extract_judge_tal_tyeq te1
      val (kctx2, t21, t22) = extract_judge_tal_tyeq te2
      val () = assert (kctx1 = kctx2) " TTyEqTimeApp"
  in
      TTyEqTimeApp ((kctx1, TCTimeApp (arity, t11, t21), TCTimeApp (arity, t12, t22)), te1, te2)
  end

fun as_TTyEqBeta te1 te2 te3 =
  let
      val (kctx1, t11, t12) = extract_judge_tal_tyeq te1
      val (kctx2, t21, t22) = extract_judge_tal_tyeq te2
      val (kctx3, t31, t32) = extract_judge_tal_tyeq te3
      val () = assert (kctx1 = kctx2) "TTyEqBeta"
      val () = assert (kctx1 = kctx3) "TTyEqBeta"
      val t12_body = extract_tal_c_abs t12
      val () = assert (subst0_tal_c_c t22 t12_body = t31) "TTyEqBeta"
  in
      TTyEqBeta ((kctx1, TCApp (t11, t21), t32), te1, te2, te3)
  end

fun as_TTyEqBetaRev te1 te2 te3 =
  let
      val (kctx1, t11, t12) = extract_judge_tal_tyeq te1
      val (kctx2, t21, t22) = extract_judge_tal_tyeq te2
      val (kctx3, t31, t32) = extract_judge_tal_tyeq te3
      val () = assert (kctx1 = kctx2) "TTyEqBetaRev"
      val () = assert (kctx1 = kctx3) "TTyEqBetaRev"
      val t11_body = extract_tal_c_abs t11
      val () = assert (subst0_tal_c_c t21 t11_body = t32) "TTyEqBetaRev"
  in
      TTyEqBetaRev ((kctx1, t31, TCApp (t12, t22)), te1, te2, te3)
  end

fun as_TTyEqQuan q ke te =
  let
      val (kctx1, k11, k12) = extract_judge_tal_kdeq ke
      val (kctx2, t21, t22) = extract_judge_tal_tyeq te
      val () = assert (k11 :: kctx1 = kctx2) "TTyEqQuan"
  in
      TTyEqQuan ((kctx1, TCQuan (q, k11, t21), TCQuan (q, k12, t22)), ke, te)
  end

fun as_TTyEqRec ke te =
  let
      val (kctx1, k11, k12) = extract_judge_tal_kdeq ke
      val (kctx2, t21, t22) = extract_judge_tal_tyeq te
      val () = assert (k11 :: kctx1 = kctx2) "TTyEqRec"
  in
      TTyEqRec ((kctx1, TCRec (k11, t21), TCRec (k12, t22)), ke, te)
  end

fun as_TTyEqRef te =
  let
      val (kctx, t1, t2) = extract_judge_tal_tyeq te
  in
      TTyEqRef ((kctx, TCRef t1, TCRef t2), te)
  end

fun as_TTyEqAbs kctx c =
  case c of
      TCAbs _ => TTyEqAbs (kctx, c, c)
    | _ => raise (AssembleFail "TTyEqAbs")

fun as_TTyEqTimeAbs kctx c =
  case c of
      TCTimeAbs _ => TTyEqTimeAbs (kctx, c, c)
    | _ => raise (AssembleFail "TTyEqTimeAbs")

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
      val () = assert (opr = PBNatEq) "TTyEqNat"
  in
      TTyEqNat ((kctx, i1, i2), pr)
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

fun as_TITyNewref rd vty ity =
  let
      val ((hctx1, kctx1, tctx1), v1, t1) = extract_judge_tal_value_typing vty
      val ((hctx2, kctx2, tctx2), (ins2, fin2), i2) = extract_judge_tal_instr_typing ity
      val () = assert (hctx2 = hctx1) "TITyNewref"
      val () = assert (kctx2 = kctx1) "TITyNewref"
      val () = assert (update_tal_tctx rd (TCRef t1) tctx1 = tctx2) "TITyNewref"
      val rs = extract_tal_v_reg v1
  in
      TITyNewref (((hctx1, kctx1, tctx1), (TINewref (rd, rs) :: ins2, fin2), TTadd (TT1, i2)), vty, ity)
  end

fun as_TITyDeref rd vty ity =
  let
      val ((hctx1, kctx1, tctx1), v1, t1) = extract_judge_tal_value_typing vty
      val ((hctx2, kctx2, tctx2), (ins2, fin2), i2) = extract_judge_tal_instr_typing ity
      val () = assert (hctx2 = hctx1) "TITyDeref"
      val () = assert (kctx2 = kctx1) "TITyDeref"
      val t11 = extract_tal_c_ref t1
      val () = assert (update_tal_tctx rd t11 tctx1 = tctx2) "TITyDeref"
      val rs = extract_tal_v_reg v1
  in
      TITyDeref (((hctx1, kctx1, tctx1), (TIDeref (rd, rs) :: ins2, fin2), TTadd (TT1, i2)), vty, ity)
  end

fun as_TITySetref vty1 vty2 ity =
  let
      val ((hctx1, kctx1, tctx1), v1, t1) = extract_judge_tal_value_typing vty1
      val ((hctx2, kctx2, tctx2), v2, t2) = extract_judge_tal_value_typing vty2
      val ((hctx3, kctx3, tctx3), (ins3, fin3), i3) = extract_judge_tal_instr_typing ity
      val () = assert ((hctx1, kctx1, tctx1) = (hctx2, kctx2, tctx2)) "TITySetref"
      val () = assert (hctx3 = hctx1) "TITySetref"
      val () = assert (kctx3 = kctx1) "TITySetref"
      val () = assert (tctx3 = tctx1) "TITySetref"
      val () = assert (t1 = TCRef t2) "TITySetref"
      val rd = extract_tal_v_reg v1
      val rs = extract_tal_v_reg v2
  in
      TITySetref (((hctx1, kctx1, tctx1), (TISetref (rd, rs) :: ins3, fin3), TTadd (TT1, i3)), vty1, vty2, ity)
  end

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
      val () = assert (List.take (update_tal_tctx r t12 tctx1, length tctx31) = tctx31) "TITyCase"
  in
      TITyCase (((hctx1, kctx1, tctx1), (TICase (r, v1) :: ins2, fin2), TTadd (TT1, TTmax (i2, i32))), vty1, ity, vty2)
  end

fun as_TITyJump vty =
  let
      val ((hctx, kctx, tctx), v, t) = extract_judge_tal_value_typing vty
      val (tctx1, i2) = extract_tal_c_arrow t
      val () = assert (List.take (tctx, length tctx1) = tctx1) "TITyJump"
  in
      TITyJump (((hctx, kctx, tctx), ([], TCJump v), TTadd (TT1, i2)), vty)
  end

fun as_TITyHalt vty =
  let
      val ((hctx, kctx, tctx), v, t) = extract_judge_tal_value_typing vty
      val () = assert (v = TVReg 0) "TITyHalt"
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
      val () = assert (tctx111 = tctx2) "THTyCode"
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
      val () = assert (tctx3 = map (fn (_, _, t) => t) jwtys) "TPTyProgram"
      val () = assert (all (fn (hctx, _, _) => hctx = hctx3) jhtys) "TPTyProgram"
      val () = assert (all (fn ((hctx, kctx), _, _) => hctx = hctx3 andalso kctx = []) jwtys) "TPTyProgram"
  in
      TPTyProgram ((TProgram (map (fn (_, h, _) => h) jhtys, map (fn (_, w, _) => w) jwtys, (ins3, fin3)), i3), htys, wtys, ity)
  end
end

structure InstrSelect =
struct
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
    | CRef c => TCRef (transform_cstr c)
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

fun transform_atom_typing hctx kctx tctx env aty =
  case aty of
      ATyVar (_, AEVar x, _, _) => ([], tctx, as_TVTyReg hctx kctx tctx $ nth (env, x))
    | ATyConst (_, AEConst cn, _, _) => ([], tctx, as_TVTyWord tctx (as_TWTyConst hctx kctx cn))
    | ATyFuncPointer (_, AEFuncPointer l, _, _) => ([], tctx, as_TVTyWord tctx (as_TWTyLoc hctx kctx l))
    | _ => raise (Impossible "transform_atom_typing")
end
end
