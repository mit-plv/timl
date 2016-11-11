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

val TKTime = TKBaseSort (BSTimeFun 0)

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
    | TKdRec (j, _) => j
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

fun extract_tal_p_bin_conn (TPBinConn a) = a
  | extract_tal_p_bin_conn _ = raise (Impossible "extract_tal_p_bin_conn")
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

structure TALDerivAssembler =
struct
open ShiftTALCstr
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
end
end
