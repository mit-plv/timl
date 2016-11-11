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

fun cbinop_result_tal_kind opr =
  case opr of
      CBTimeAdd => TKTime
    | CBTimeMinus => TKTime
    | CBTimeMult => TKTime
    | CBTimeMax => TKTime
    | CBTypeProd => TKType
    | CBTypeSum => TKType
    | CBNatAdd => TKNat

fun cunop_result_tal_kind opr =
  case opr of
      CUNat2Time => TKTime

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
    | TTyEqNat (j, _, _, _) => j

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
    | TCRec (name, k, t) =>
      let
          val (k, up1) = transform_tal_kind (k, down)
          val (t, up2) = transform_tal_cstr (t, Action.add_tal_kind (SOME k, down))
      in
          (TCRec (name, k, t), combine [up1, up2])
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

fun as_TKdEqKArrow ke1 ke2 =
  let
      val jke1 = extract_judge_tal_kdeq ke1
      val jke2 = extract_judge_tal_kdeq ke2
  in
      TKdEqKArrow ((#1 jke1, TKArrow (#2 jke1, #2 jke2), TKArrow (#3 jke1, #3 jke2)), ke1, ke2)
  end

fun as_TKdEqSubset ke pr =
  let
      val jke = extract_judge_tal_kdeq ke
      val jpr = extract_judge_tal_proping pr
      val (_, p1, p2) = extract_tal_p_bin_conn (#2 jpr)
  in
      TKdEqSubset ((#1 jke, TKSubset (#2 jke, p1), TKSubset (#3 jke, p2)), ke, pr)
  end

fun as_TKdBinOp opr kd1 kd2 =
  let
      val jkd1 = extract_judge_tal_kinding kd1
      val jkd2 = extract_judge_tal_kinding kd2
  in
      TKdBinOp ((#1 jkd1, TCBinOp (opr, #2 jkd1, #2 jkd2), cbinop_result_tal_kind opr), kd1, kd2)
  end

fun as_TKdIte kd1 kd2 kd3 =
  let
      val jkd1 = extract_judge_tal_kinding kd1
      val jkd2 = extract_judge_tal_kinding kd2
      val jkd3 = extract_judge_tal_kinding kd3
  in
      TKdIte ((#1 jkd1, TCIte (#2 jkd1, #2 jkd2, #2 jkd3), #3 jkd2), kd1, kd2, kd3)
  end

fun as_TKdArrow kds kd =
  let
      val jkds = map extract_judge_tal_kinding kds
      val jkd = extract_judge_tal_kinding kd
  in
      TKdArrow ((#1 jkd, TCArrow (map (fn (_, t, _) => t) jkds, #2 jkd), TKType), kds, kd)
  end

fun as_TKdAbs wk kd =
  let
      val jwk = extract_judge_tal_wfkind wk
      val jkd = extract_judge_tal_kinding kd
  in
      TKdAbs ((#1 jwk, TCAbs (#2 jkd), TKArrow (#2 jwk, shift_tal_c_k ~1 0 (#3 jkd))), wk, kd)
  end

fun as_TKdApp kd1 kd2 =
  let
      val jkd1 = extract_judge_tal_kinding kd1
      val jkd2 = extract_judge_tal_kinding kd2
      val (k1, k2) = extract_tal_k_arrow (#3 jkd1)
  in
      TKdApp ((#1 jkd1, TCApp (#2 jkd1, #2 jkd2), k2), kd1, kd2)
  end

fun as_TKdTimeAbs kd =
  let
      val jkd = extract_judge_tal_kinding kd
      val arity = extract_tal_k_time_fun (#3 jkd)
  in
      TKdTimeAbs ((tl $ #1 jkd, TCTimeAbs (#2 jkd), TKTimeFun (arity + 1)), kd)
  end

fun as_TKdTimeApp kd1 kd2 =
  let
      val jkd1 = extract_judge_tal_kinding kd1
      val jkd2 = extract_judge_tal_kinding kd2
      val arity = extract_tal_k_time_fun (#3 jkd1)
  in
      TKdTimeApp ((#1 jkd1, TCTimeApp (arity - 1, #2 jkd1, #2 jkd2), TKTimeFun (arity - 1)), kd1, kd2)
  end

fun as_TKdQuan q wk kd =
  let
      val jwk = extract_judge_tal_wfkind wk
      val jkd = extract_judge_tal_kinding kd
  in
      TKdQuan ((#1 jwk, TCQuan (q, #2 jwk, #2 jkd), TKType), wk, kd)
  end

fun as_TKdRec name wk kd =
  let
      val jwk = extract_judge_tal_wfkind wk
      val jkd = extract_judge_tal_kinding kd
  in
      TKdRec ((#1 jwk, TCRec (name, #2 jwk, #2 jkd), #2 jwk), wk, kd)
  end

fun as_TKdEq kd ke =
  let
      val jkd = extract_judge_tal_kinding kd
      val jke = extract_judge_tal_kdeq ke
  in
      TKdEq ((#1 jkd, #2 jkd, #2 jke), kd, ke)
  end

fun as_TKdUnOp opr kd =
  let
      val jkd = extract_judge_tal_kinding kd
  in
      TKdUnOp ((#1 jkd, TCUnOp (opr, #2 jkd), cunop_result_tal_kind opr), kd)
  end

fun as_TWfKdArrow wk1 wk2 =
  let
      val jwk1 = extract_judge_tal_wfkind wk1
      val jwk2 = extract_judge_tal_wfkind wk2
  in
      TWfKdArrow ((#1 jwk1, TKArrow (#2 jwk1, #2 jwk2)), wk1, wk2)
  end

fun as_TWfKdSubset wk wp =
  let
      val jwk = extract_judge_tal_wfkind wk
      val jwp = extract_judge_tal_wfprop wp
  in
      TWfKdSubset ((#1 jwk, TKSubset (#2 jwk, #2 jwp)), wk, wp)
  end

fun as_TWfPropBinConn opr wp1 wp2 =
  let
      val jwp1 = extract_judge_tal_wfprop wp1
      val jwp2 = extract_judge_tal_wfprop wp2
  in
      TWfPropBinConn ((#1 jwp1, TPBinConn (opr, #2 jwp1, #2 jwp2)), wp1, wp2)
  end

fun as_TWfPropNot wp =
  let
      val jwp = extract_judge_tal_wfprop wp
  in
      TWfPropNot ((#1 jwp, TPNot (#2 jwp)), wp)
  end

fun as_TWfPropBinPred opr kd1 kd2 =
  let
      val jkd1 = extract_judge_tal_kinding kd1
      val jkd2 = extract_judge_tal_kinding kd2
  in
      TWfPropBinPred ((#1 jkd1, TPBinPred (opr, #2 jkd1, #2 jkd2)), kd1, kd2)
  end

fun as_TWfPropQuan q b wp =
  let
      val jwp = extract_judge_tal_wfprop wp
  in
      TWfPropQuan ((tl $ #1 jwp, TPQuan (q, b, #2 jwp)), wp)
  end

fun as_TTyEqBinOp opr te1 te2 =
  let
      val jte1 = extract_judge_tal_tyeq te1
      val jte2 = extract_judge_tal_tyeq te2
  in
      TTyEqBinOp ((#1 jte1, TCBinOp (opr, #2 jte1, #2 jte2), TCBinOp (opr, #3 jte1, #3 jte2)), te1, te2)
  end

fun as_TTyEqIte te1 te2 te3 =
  let
      val jte1 = extract_judge_tal_tyeq te1
      val jte2 = extract_judge_tal_tyeq te2
      val jte3 = extract_judge_tal_tyeq te3
  in
      TTyEqIte ((#1 jte1, TCIte (#2 jte1, #2 jte2, #2 jte3), TCIte (#3 jte1, #3 jte2, #3 jte3)), te1, te2, te3)
  end

fun as_TTyEqArrow tes pr =
  let
      val jtes = map extract_judge_tal_tyeq tes
      val jpr = extract_judge_tal_proping pr
      val (_, i1, i2) = extract_tal_p_bin_pred (#2 jpr)
  in
      TTyEqArrow ((#1 jpr, TCArrow (map (fn (_, t1, _) => t1) jtes, i1), TCArrow (map (fn (_, _, t2) => t2) jtes, i2)), tes, pr)
  end

fun as_TTyEqApp te1 te2 =
  let
      val jte1 = extract_judge_tal_tyeq te1
      val jte2 = extract_judge_tal_tyeq te2
  in
      TTyEqApp ((#1 jte1, TCApp (#2 jte1, #2 jte2), TCApp (#3 jte1, #3 jte2)), te1, te2)
  end

fun as_TTyEqTimeApp arity te1 te2 =
  let
      val jte1 = extract_judge_tal_tyeq te1
      val jte2 = extract_judge_tal_tyeq te2
  in
      TTyEqTimeApp ((#1 jte1, TCTimeApp (arity, #2 jte1, #2 jte2), TCTimeApp (arity, #3 jte1, #3 jte2)), te1, te2)
  end

fun as_TTyEqBeta te1 te2 te3 =
  let
      val jte1 = extract_judge_tal_tyeq te1
      val jte2 = extract_judge_tal_tyeq te2
      val jte3 = extract_judge_tal_tyeq te3
  in
      TTyEqBeta ((#1 jte1, TCApp (#2 jte1, #2 jte2), #3 jte3), te1, te2, te3)
  end

fun as_TTyEqBetaRev te1 te2 te3 =
  let
      val jte1 = extract_judge_tal_tyeq te1
      val jte2 = extract_judge_tal_tyeq te2
      val jte3 = extract_judge_tal_tyeq te3
  in
      TTyEqBetaRev ((#1 jte1, #2 jte3, TCApp (#3 jte1, #3 jte2)), te1, te2, te3)
  end

fun as_TTyEqQuan q ke te =
  let
      val jke = extract_judge_tal_kdeq ke
      val jte = extract_judge_tal_tyeq te
  in
      TTyEqQuan ((#1 jke, TCQuan (q, #2 jke, #2 jte), TCQuan (q, #3 jke, #3 jte)), ke, te)
  end

fun as_TTyEqRec name1 name2 ke te =
  let
      val jke = extract_judge_tal_kdeq ke
      val jte = extract_judge_tal_tyeq te
  in
      TTyEqRec ((#1 jke, TCRec (name1, #2 jke, #2 jte), TCRec (name2, #3 jke, #3 jte)), ke, te)
  end

fun as_TTyEqRef te =
  let
      val jte = extract_judge_tal_tyeq te
  in
      TTyEqRef ((#1 jte, TCRef (#2 jte), TCRef (#3 jte)), te)
  end

fun as_TTyEqUnOp opr te =
  let
      val jte = extract_judge_tal_tyeq te
  in
      TTyEqUnOp ((#1 jte, TCUnOp (opr, #2 jte), TCUnOp (opr, #3 jte)), te)
  end

fun as_TTyEqNat kd1 kd2 pr =
  let
      val jpr = extract_judge_tal_proping pr
      val (_, i1, i2) = extract_tal_p_bin_pred (#2 jpr)
  in
      TTyEqNat ((#1 jpr, i1, i2), kd1, kd2, pr)
  end

fun as_TWTyAppC wty kd =
  let
      val jwty = extract_judge_tal_word_typing wty
      val jkd = extract_judge_tal_kinding kd
      val (_, k, t) = extract_tal_c_quan (#3 jwty)
  in
      TWTyAppC ((#1 jwty, TWAppC (#2 jwty, #2 jkd), subst0_tal_c_c (#2 jkd) t), wty, kd)
  end

fun as_TWTyPack kd1 kd2 wty =
  let
      val jkd1 = extract_judge_tal_kinding kd1
      val jkd2 = extract_judge_tal_kinding kd2
      val jwty = extract_judge_tal_word_typing wty
  in
      TWTyPack ((#1 jwty, TWPack (#2 jkd2, #2 jwty), #2 jkd1), kd1, kd2, wty)
  end

fun as_TWTySub wty te =
  let
      val jwty = extract_judge_tal_word_typing wty
      val jte = extract_judge_tal_tyeq te
  in
      TWTySub ((#1 jwty, #2 jwty, #3 jte), wty, te)
  end

fun as_TVTyWord tctx wty =
  let
      val jwty = extract_judge_tal_word_typing wty
  in
      TVTyWord (((fst $ #1 jwty, snd $ #1 jwty, tctx), TVWord (#2 jwty), #3 jwty), wty)
  end

fun as_TVTyAppC vty kd =
  let
      val jvty = extract_judge_tal_value_typing vty
      val jkd = extract_judge_tal_kinding kd
      val (_, k, t) = extract_tal_c_quan (#3 jvty)
  in
      TVTyAppC ((#1 jvty, TVAppC (#2 jvty, #2 jkd), subst0_tal_c_c (#2 jkd) t), vty, kd)
  end

fun as_TVTyPack kd1 kd2 vty =
  let
      val jkd1 = extract_judge_tal_kinding kd1
      val jkd2 = extract_judge_tal_kinding kd2
      val jvty = extract_judge_tal_value_typing vty
  in
      TVTyPack ((#1 jvty, TVPack (#2 jkd2, #2 jvty), #2 jkd1), kd1, kd2, vty)
  end

fun as_TVTySub vty te =
  let
      val jvty = extract_judge_tal_value_typing vty
      val jte = extract_judge_tal_tyeq te
  in
      TVTySub ((#1 jvty, #2 jvty, #3 jte), vty, te)
  end

fun as_TITyNewpair rd vty1 vty2 ity =
  let
      val jvty1 = extract_judge_tal_value_typing vty1
      val jvty2 = extract_judge_tal_value_typing vty2
      val jity = extract_judge_tal_instr_typing ity
      val rs = extract_tal_v_reg (#2 jvty1)
      val rt = extract_tal_v_reg (#2 jvty2)
  in
      TITyNewpair ((#1 jvty1, (TINewpair (rd, rs, rt) :: fst (#2 jity), snd (#2 jity)), TTadd (TT1, #3 jity)), vty1, vty2, ity)
  end

fun as_TITyProj p rd vty ity =
  let
      val jvty = extract_judge_tal_value_typing vty
      val jity = extract_judge_tal_instr_typing ity
      val rs = extract_tal_v_reg (#2 jvty)
  in
      TITyProj ((#1 jvty, (TIProj (p, rd, rs) :: fst (#2 jity), snd (#2 jity)), TTadd (TT1, #3 jity)), vty, ity)
  end

fun as_TITyInj inj vty kd ity =
  let
      val jvty = extract_judge_tal_value_typing vty
      val jkd = extract_judge_tal_kinding kd
      val jity = extract_judge_tal_instr_typing ity
      val rd = extract_tal_v_reg (#2 jvty)
  in
      TITyInj ((#1 jvty, (TIInj (inj, rd) :: fst (#2 jity), snd (#2 jity)), TTadd (TT1, #3 jity)), vty, kd, ity)
  end

fun as_TITyFold kd vty ity =
  let
      val jkd = extract_judge_tal_kinding kd
      val jvty = extract_judge_tal_value_typing vty
      val jity = extract_judge_tal_instr_typing ity
      val rd = extract_tal_v_reg (#2 jvty)
  in
      TITyFold ((#1 jvty, (TIFold rd :: fst (#2 jity), snd (#2 jity)), TTadd (TT1, #3 jity)), kd, vty, ity)
  end

fun as_TITyUnfold vty ity =
  let
      val jvty = extract_judge_tal_value_typing vty
      val jity = extract_judge_tal_instr_typing ity
      val rd = extract_tal_v_reg (#2 jvty)
  in
      TITyUnfold ((#1 jvty, (TIUnfold rd :: fst (#2 jity), snd (#2 jity)), TTadd (TT1, #3 jity)), vty, ity)
  end

fun as_TITyNewref rd vty ity =
  let
      val jvty = extract_judge_tal_value_typing vty
      val jity = extract_judge_tal_instr_typing ity
      val rs = extract_tal_v_reg (#2 jvty)
  in
      TITyNewref ((#1 jvty, (TINewref (rd, rs) :: fst (#2 jity), snd (#2 jity)), TTadd (TT1, #3 jity)), vty, ity)
  end

fun as_TITyDeref rd vty ity =
  let
      val jvty = extract_judge_tal_value_typing vty
      val jity = extract_judge_tal_instr_typing ity
      val rs = extract_tal_v_reg (#2 jvty)
  in
      TITyDeref ((#1 jvty, (TIDeref (rd, rs) :: fst (#2 jity), snd (#2 jity)), TTadd (TT1, #3 jity)), vty, ity)
  end

fun as_TITySetref vty1 vty2 ity =
  let
      val jvty1 = extract_judge_tal_value_typing vty1
      val jvty2 = extract_judge_tal_value_typing vty2
      val jity = extract_judge_tal_instr_typing ity
      val rd = extract_tal_v_reg (#2 jvty1)
      val rs = extract_tal_v_reg (#2 jvty2)
  in
      TITySetref ((#1 jvty1, (TISetref (rd, rs) :: fst (#2 jity), snd (#2 jity)), TTadd (TT1, #3 jity)), vty1, vty2, ity)
  end

fun as_TITyPrimBinOp opr rd vty1 vty2 ity =
  let
      val jvty1 = extract_judge_tal_value_typing vty1
      val jvty2 = extract_judge_tal_value_typing vty2
      val jity = extract_judge_tal_instr_typing ity
      val rs = extract_tal_v_reg (#2 jvty1)
      val rt = extract_tal_v_reg (#2 jvty2)
  in
      TITyPrimBinOp ((#1 jvty1, (TIPrimBinOp (opr, rd, rs, rt) :: fst (#2 jity), snd (#2 jity)), TTadd (TT1, #3 jity)), vty1, vty2, ity)
  end

fun as_TITyMove rd vty ity =
  let
      val jvty = extract_judge_tal_value_typing vty
      val jity = extract_judge_tal_instr_typing ity
  in
      TITyMove ((#1 jvty, (TIMove (rd, #2 jvty) :: fst (#2 jity), snd (#2 jity)), TTadd (TT1, #3 jity)), vty, ity)
  end

fun as_TITyUnpack rd vty ity =
  let
      val jvty = extract_judge_tal_value_typing vty
      val jity = extract_judge_tal_instr_typing ity
  in
      TITyUnpack ((#1 jvty, (TIUnpack (rd, #2 jvty) :: fst (#2 jity), snd (#2 jity)), TTadd (TT1, shift_tal_c_c ~1 0 $ #3 jity)), vty, ity)
  end

fun as_TITyCase vty1 ity vty2 =
  let
      val jvty1 = extract_judge_tal_value_typing vty1
      val jity = extract_judge_tal_instr_typing ity
      val jvty2 = extract_judge_tal_value_typing vty2
      val r = extract_tal_v_reg (#2 jvty1)
      val (_, i) = extract_tal_c_arrow (#3 jvty2)
  in
      TITyCase ((#1 jvty1, (TICase (r, #2 jvty2) :: fst (#2 jity), snd (#2 jity)), TTadd (TT1, TTmax (#3 jity, i))), vty1, ity, vty2)
  end

fun as_TITyJump vty =
  let
      val jvty = extract_judge_tal_value_typing vty
      val (_, i) = extract_tal_c_arrow (#3 jvty)
  in
      TITyJump ((#1 jvty, ([], TCJump (#2 jvty)), TTadd (TT1, i)), vty)
  end

fun as_TITyHalt vty =
  let
      val jvty = extract_judge_tal_value_typing vty
  in
      TITyHalt ((#1 jvty, ([], TCHalt (#3 jvty)), TT1), vty)
  end

fun as_THTyCode kd ity =
  let
      val jkd = extract_judge_tal_kinding kd
      val jity = extract_judge_tal_instr_typing ity
  in
      THTyCode ((#1 (#1 jity), THCode (length $ #2 (#1 jity), #2 jity), #2 jkd), kd, ity)
  end

fun as_THTyPair wty1 wty2 =
  let
      val jwty1 = extract_judge_tal_word_typing wty1
      val jwty2 = extract_judge_tal_word_typing wty2
  in
      THTyPair ((#1 (#1 jwty1), THPair (#2 jwty1, #2 jwty2), TCProd (#3 jwty1, #3 jwty2)), wty1, wty2)
  end

fun as_THTyWord wty =
  let
      val jwty = extract_judge_tal_word_typing wty
  in
      THTyWord ((#1 (#1 jwty), THWord (#2 jwty), #3 jwty), wty)
  end

fun as_TPTyProgram htys wtys ity =
  let
      val jhtys = map extract_judge_tal_heap_typing htys
      val jwtys = map extract_judge_tal_word_typing wtys
      val jity = extract_judge_tal_instr_typing ity
  in
      TPTyProgram ((TProgram (map (fn (_, h, _) => h) jhtys, map (fn (_, w, _) => w) jwtys, #2 jity), #3 jity), htys, wtys, ity)
  end
end

structure InstrSelect =
struct
end
end
