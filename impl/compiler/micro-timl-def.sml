signature SIG_TIME =
sig
    eqtype time_type

    val Time0 : time_type
    val Time1 : time_type

    val str_time : time_type -> string
end

signature SIG_NAT =
sig
    eqtype nat_type

    val str_nat : nat_type -> string
end

signature SIG_MICRO_TIML_DEF =
sig
    structure Time : SIG_TIME
    structure Nat : SIG_NAT

    datatype cstr_const =
             CCIdxTT
             | CCIdxNat of Nat.nat_type
             | CCTime of Time.time_type
             | CCTypeUnit
             | CCTypeInt

    datatype cstr_bin_op =
             CBTimeAdd
             | CBTimeMinus
             | CBTimeMax
             | CBTypeProd
             | CBTypeSum
             | CBNatAdd

    datatype cstr_un_op =
             CUNat2Time

    datatype quan =
             QuanForall
           | QuanExists

    type var = int

    datatype prop_bin_conn =
             PBCAnd
             | PBCOr
             | PBCImply
             | PBCIff

    datatype prop_bin_pred =
             PBTimeLe
             | PBTimeEq
             | PBBigO of int
             | PBNatEq

    datatype sort =
             BSNat
             | BSUnit
             | BSBool
             | BSTimeFun of int

    datatype cstr =
             CVar of var
             | CConst of cstr_const
             | CBinOp of cstr_bin_op * cstr * cstr
             | CIte of cstr * cstr * cstr
             | CTimeAbs of cstr
             | CTimeApp of int * cstr * cstr
             | CArrow of cstr * cstr * cstr
             | CAbs of cstr
             | CApp of cstr * cstr
             | CQuan of quan * kind * cstr
             | CRec of kind * cstr
             | CRef of cstr
             | CUnOp of cstr_un_op * cstr

         and kind =
             KType
             | KArrow of kind * kind
             | KBaseSort of sort
             | KSubset of kind * prop

         and prop =
             PTrue
             | PFalse
             | PBinConn of prop_bin_conn * prop * prop
             | PNot of prop
             | PBinPred of prop_bin_pred * cstr * cstr
             | PQuan of quan * sort * prop

    val KUnit : kind
    val KBool : kind
    val KNat : kind
    val KTimeFun : int -> kind
    val KTime : kind

    val Tconst : Time.time_type -> cstr
    val T0 : cstr
    val T1 : cstr
    val Tadd : cstr * cstr -> cstr
    val Tminus : cstr * cstr -> cstr

    val TfromNat : cstr -> cstr

    val PAnd : prop * prop -> prop
    val POr : prop * prop -> prop
    val PImply : prop * prop -> prop
    val PIff : prop * prop -> prop

    val Tmax : cstr * cstr -> cstr

    val CForall : kind * cstr -> cstr
    val CExists : kind * cstr -> cstr

    val CTypeUnit : cstr

    val CProd : cstr * cstr -> cstr
    val CSum : cstr * cstr -> cstr

    val TLe : cstr * cstr -> prop
    val TEq : cstr * cstr -> prop

    val CInt : cstr
    val CNat : Nat.nat_type -> cstr

    val CApps : cstr -> cstr list -> cstr

    val const_kind : cstr_const -> kind
    val cbinop_arg1_kind : cstr_bin_op -> kind
    val cbinop_arg2_kind : cstr_bin_op -> kind
    val cbinop_result_kind : cstr_bin_op -> kind
    val cunop_arg_kind : cstr_un_op -> kind
    val cunop_result_kind : cstr_un_op -> kind
    val binpred_arg1_kind : prop_bin_pred -> kind
    val binpred_arg2_kind : prop_bin_pred -> kind

    type kctx = kind list

    val BSTime : sort

    type kdeq_judgement = kctx * kind * kind
    type proping_judgement = kctx * prop

    datatype proping =
             PrAdmit of proping_judgement

    datatype kdeq =
             KdEqKType of kdeq_judgement
             | KdEqKArrow of kdeq_judgement * kdeq * kdeq
             | KdEqBaseSort of kdeq_judgement
             | KdEqSubset of kdeq_judgement * kdeq * proping

    type kinding_judgement = kctx * cstr * kind
    type wfkind_judgement = kctx * kind
    type wfprop_judgement = kctx * prop

    datatype kinding =
             KdVar of kinding_judgement
             | KdConst of kinding_judgement
             | KdBinOp of kinding_judgement * kinding * kinding
             | KdIte of kinding_judgement * kinding * kinding * kinding
             | KdArrow of kinding_judgement * kinding * kinding * kinding
             | KdAbs of kinding_judgement * wfkind * kinding
             | KdApp of kinding_judgement * kinding * kinding
             | KdTimeAbs of kinding_judgement * kinding
             | KdTimeApp of kinding_judgement * kinding * kinding
             | KdQuan of kinding_judgement * wfkind * kinding
             | KdRec of kinding_judgement * wfkind * kinding
             | KdRef of kinding_judgement * kinding
             | KdEq of kinding_judgement * kinding * kdeq
             | KdUnOp of kinding_judgement * kinding
             | KdAdmit of kinding_judgement

         and wfkind =
             WfKdType of wfkind_judgement
             | WfKdArrow of wfkind_judgement * wfkind * wfkind
             | WfKdBaseSort of wfkind_judgement
             | WfKdSubset of wfkind_judgement * wfkind * wfprop
             | WfKdAdmit of wfkind_judgement

         and wfprop =
             WfPropTrue of wfprop_judgement
             | WfPropFalse of wfprop_judgement
             | WfPropBinConn of wfprop_judgement * wfprop * wfprop
             | WfPropNot of wfprop_judgement * wfprop
             | WfPropBinPred of wfprop_judgement * kinding * kinding
             | WfPropQuan of wfprop_judgement * wfprop

    type tyeq_judgement = kctx * cstr * cstr

    datatype tyeq =
             TyEqVar of tyeq_judgement
             | TyEqConst of tyeq_judgement
             | TyEqBinOp of tyeq_judgement * tyeq * tyeq
             | TyEqIte of tyeq_judgement * tyeq * tyeq * tyeq
             | TyEqArrow of tyeq_judgement * tyeq * proping * tyeq
             | TyEqApp of tyeq_judgement * tyeq * tyeq
             | TyEqTimeApp of tyeq_judgement * tyeq * tyeq
             | TyEqBeta of tyeq_judgement * tyeq * tyeq * tyeq
             | TyEqBetaRev of tyeq_judgement * tyeq * tyeq * tyeq
             | TyEqQuan of tyeq_judgement * kdeq * tyeq
             | TyEqRec of tyeq_judgement * kdeq * tyeq
             | TyEqRef of tyeq_judgement * tyeq
             | TyEqAbs of tyeq_judgement
             | TyEqTimeAbs of tyeq_judgement
             | TyEqUnOp of tyeq_judgement * tyeq
             | TyEqNatEq of tyeq_judgement * proping

    datatype expr_const =
             ECTT
             | ECInt of int

    datatype prim_expr_bin_op =
             PEBIntAdd

    datatype projector =
             ProjFst
             | ProjSnd

    datatype injector =
             InjInl
           | InjInr

    type tctx = cstr list
    type ctx = kctx * tctx

    datatype expr_un_op =
             EUProj of projector
             | EUInj of injector
             | EUFold
             | EUUnfold
             | EUNew
             | EURead

    datatype expr_bin_op =
             EBPrim of prim_expr_bin_op
             | EBApp
             | EBPair
             | EBWrite

    datatype expr =
             EVar of var
             | EConst of expr_const
             | EUnOp of expr_un_op * expr
             | EBinOp of expr_bin_op * expr * expr
             | ECase of expr * expr * expr
             | EAbs of expr
             | ERec of expr
             | EAbsC of expr
             | EAppC of expr * cstr
             | EPack of cstr * expr
             | EUnpack of expr * expr
             | EHalt of expr
             | ELet of expr * expr
             | EFix of int * expr

    val EProj : projector * expr -> expr
    val EInj : injector * expr -> expr
    val EFold : expr -> expr
    val EUnfold : expr -> expr
    val ENew : expr -> expr
    val ERead : expr -> expr

    val EApp : expr * expr -> expr
    val EPair : expr * expr -> expr
    val EWrite : expr * expr -> expr

    val const_type : expr_const -> cstr

    type typing_judgement = ctx * expr * cstr * cstr

    datatype typing =
             TyVar of typing_judgement
             | TyApp of typing_judgement * typing * typing
             | TyAbs of typing_judgement * kinding * typing
             | TyAppC of typing_judgement * typing * kinding
             | TyAbsC of typing_judgement * wfkind * typing
             | TyRec of typing_judgement * kinding * typing
             | TyFold of typing_judgement * kinding * typing
             | TyUnfold of typing_judgement * typing
             | TyPack of typing_judgement * kinding * kinding * typing
             | TyUnpack of typing_judgement * typing * typing
             | TyConst of typing_judgement
             | TyPair of typing_judgement * typing * typing
             | TyProj of typing_judgement * typing
             | TyInj of typing_judgement * typing * kinding
             | TyCase of typing_judgement * typing * typing * typing
             | TyNew of typing_judgement * typing
             | TyRead of typing_judgement * typing
             | TyWrite of typing_judgement * typing * typing
             | TySub of typing_judgement * typing * tyeq * proping
             | TyHalt of typing_judgement * typing
             | TyAppK of typing_judgement * typing * typing
             | TyLet of typing_judgement * typing * typing
             | TyFix of typing_judgement * kinding * typing
end

functor MicroTiMLDefFun(
    structure Time : SIG_TIME
    structure Nat : SIG_NAT) : SIG_MICRO_TIML_DEF =
struct
open Util

structure Time = Time
open Time
structure Nat = Nat
open Nat

datatype cstr_const =
         CCIdxTT
         | CCIdxNat of nat_type
         | CCTime of time_type
         | CCTypeUnit
         | CCTypeInt

datatype cstr_bin_op =
         CBTimeAdd
         | CBTimeMinus
         | CBTimeMax
         | CBTypeProd
         | CBTypeSum
         | CBNatAdd

datatype cstr_un_op =
         CUNat2Time

datatype quan =
         QuanForall
       | QuanExists

type var = int

datatype prop_bin_conn =
         PBCAnd
         | PBCOr
         | PBCImply
         | PBCIff

datatype prop_bin_pred =
         PBTimeLe
         | PBTimeEq
         | PBBigO of int
         | PBNatEq

datatype sort =
         BSNat
         | BSUnit
         | BSBool
         | BSTimeFun of int

datatype cstr =
         CVar of var
         | CConst of cstr_const
         | CBinOp of cstr_bin_op * cstr * cstr
         | CIte of cstr * cstr * cstr
         | CTimeAbs of cstr
         | CTimeApp of int * cstr * cstr
         | CArrow of cstr * cstr * cstr
         | CAbs of cstr
         | CApp of cstr * cstr
         | CQuan of quan * kind * cstr
         | CRec of kind * cstr
         | CRef of cstr
         | CUnOp of cstr_un_op * cstr

     and kind =
         KType
         | KArrow of kind * kind
         | KBaseSort of sort
         | KSubset of kind * prop

     and prop =
         PTrue
         | PFalse
         | PBinConn of prop_bin_conn * prop * prop
         | PNot of prop
         | PBinPred of prop_bin_pred * cstr * cstr
         | PQuan of quan * sort * prop

val KUnit = KBaseSort BSUnit
val KBool = KBaseSort BSBool
val KNat = KBaseSort BSNat
fun KTimeFun arity = KBaseSort (BSTimeFun arity)
val KTime = KTimeFun 0

fun Tconst r = CConst (CCTime r)
val T0 = Tconst Time0
val T1 = Tconst Time1
fun Tadd (c1, c2) = CBinOp (CBTimeAdd, c1, c2)
fun Tminus (c1, c2) = CBinOp (CBTimeMinus, c1, c2)

fun TfromNat c = CUnOp (CUNat2Time, c)

fun PAnd (p1, p2) = PBinConn (PBCAnd, p1, p2)
fun POr (p1, p2) = PBinConn (PBCOr, p1, p2)
fun PImply (p1, p2) = PBinConn (PBCImply, p1, p2)
fun PIff (p1, p2) = PBinConn (PBCIff, p1, p2)

fun Tmax (c1, c2) = CBinOp (CBTimeMax, c1, c2)

fun CForall (k, c) = CQuan (QuanForall, k, c)
fun CExists (k, c) = CQuan (QuanExists, k, c)

val CTypeUnit = CConst CCTypeUnit

fun CProd (c1, c2) = CBinOp (CBTypeProd, c1, c2)
fun CSum (c1, c2) = CBinOp (CBTypeSum, c1, c2)

fun TLe (c1, c2) = PBinPred (PBTimeLe, c1, c2)
fun TEq (c1, c2) = PBinPred (PBTimeEq, c1, c2)

val CInt = CConst CCTypeInt
fun CNat n = CConst (CCIdxNat n)

fun CApps t cs =
  case cs of
      [] => t
    | c :: cs => CApps (CApp (t, c)) cs

fun const_kind cn =
  case cn of
      CCIdxTT => KUnit
    | CCIdxNat _ => KNat
    | CCTime _ => KTime
    | CCTypeUnit => KType
    | CCTypeInt => KType

fun cbinop_arg1_kind opr =
  case opr of
      CBTimeAdd => KTime
    | CBTimeMinus => KTime
    | CBTimeMax => KTime
    | CBTypeProd => KType
    | CBTypeSum => KType
    | CBNatAdd => KNat

fun cbinop_arg2_kind opr =
  case opr of
      CBTimeAdd => KTime
    | CBTimeMinus => KTime
    | CBTimeMax => KTime
    | CBTypeProd => KType
    | CBTypeSum => KType
    | CBNatAdd => KNat

fun cbinop_result_kind opr =
  case opr of
      CBTimeAdd => KTime
    | CBTimeMinus => KTime
    | CBTimeMax => KTime
    | CBTypeProd => KType
    | CBTypeSum => KType
    | CBNatAdd => KNat

fun cunop_arg_kind opr =
  case opr of
      CUNat2Time => KNat

fun cunop_result_kind opr =
  case opr of
      CUNat2Time => KTime

fun binpred_arg1_kind opr =
  case opr of
      PBTimeLe => KTime
    | PBTimeEq => KTime
    | PBBigO n => KTimeFun n
    | PBNatEq => KNat

fun binpred_arg2_kind opr =
  case opr of
      PBTimeLe => KTime
    | PBTimeEq => KTime
    | PBBigO n => KTimeFun n
    | PBNatEq => KNat

type kctx = kind list

val BSTime = BSTimeFun 0

type kdeq_judgement = kctx * kind * kind
type proping_judgement = kctx * prop

datatype proping =
         PrAdmit of proping_judgement

datatype kdeq =
         KdEqKType of kdeq_judgement
         | KdEqKArrow of kdeq_judgement * kdeq * kdeq
         | KdEqBaseSort of kdeq_judgement
         | KdEqSubset of kdeq_judgement * kdeq * proping

type kinding_judgement = kctx * cstr * kind
type wfkind_judgement = kctx * kind
type wfprop_judgement = kctx * prop

datatype kinding =
         KdVar of kinding_judgement
         | KdConst of kinding_judgement
         | KdBinOp of kinding_judgement * kinding * kinding
         | KdIte of kinding_judgement * kinding * kinding * kinding
         | KdArrow of kinding_judgement * kinding * kinding * kinding
         | KdAbs of kinding_judgement * wfkind * kinding
         | KdApp of kinding_judgement * kinding * kinding
         | KdTimeAbs of kinding_judgement * kinding
         | KdTimeApp of kinding_judgement * kinding * kinding
         | KdQuan of kinding_judgement * wfkind * kinding
         | KdRec of kinding_judgement * wfkind * kinding
         | KdRef of kinding_judgement * kinding
         | KdEq of kinding_judgement * kinding * kdeq
         | KdUnOp of kinding_judgement * kinding
         | KdAdmit of kinding_judgement

     and wfkind =
         WfKdType of wfkind_judgement
         | WfKdArrow of wfkind_judgement * wfkind * wfkind
         | WfKdBaseSort of wfkind_judgement
         | WfKdSubset of wfkind_judgement * wfkind * wfprop
         | WfKdAdmit of wfkind_judgement

     and wfprop =
         WfPropTrue of wfprop_judgement
         | WfPropFalse of wfprop_judgement
         | WfPropBinConn of wfprop_judgement * wfprop * wfprop
         | WfPropNot of wfprop_judgement * wfprop
         | WfPropBinPred of wfprop_judgement * kinding * kinding
         | WfPropQuan of wfprop_judgement * wfprop

type tyeq_judgement = kctx * cstr * cstr

datatype tyeq =
         TyEqVar of tyeq_judgement
         | TyEqConst of tyeq_judgement
         | TyEqBinOp of tyeq_judgement * tyeq * tyeq
         | TyEqIte of tyeq_judgement * tyeq * tyeq * tyeq
         | TyEqArrow of tyeq_judgement * tyeq * proping * tyeq
         | TyEqApp of tyeq_judgement * tyeq * tyeq
         | TyEqTimeApp of tyeq_judgement * tyeq * tyeq
         | TyEqBeta of tyeq_judgement * tyeq * tyeq * tyeq
         | TyEqBetaRev of tyeq_judgement * tyeq * tyeq * tyeq
         | TyEqQuan of tyeq_judgement * kdeq * tyeq
         | TyEqRec of tyeq_judgement * kdeq * tyeq
         | TyEqRef of tyeq_judgement * tyeq
         | TyEqAbs of tyeq_judgement
         | TyEqTimeAbs of tyeq_judgement
         | TyEqUnOp of tyeq_judgement * tyeq
         | TyEqNatEq of tyeq_judgement * proping

datatype expr_const =
         ECTT
         | ECInt of int

datatype prim_expr_bin_op =
         PEBIntAdd

datatype projector =
         ProjFst
         | ProjSnd

datatype injector =
         InjInl
       | InjInr

type tctx = cstr list
type ctx = kctx * tctx

datatype expr_un_op =
         EUProj of projector
         | EUInj of injector
         | EUFold
         | EUUnfold
         | EUNew
         | EURead

datatype expr_bin_op =
         EBPrim of prim_expr_bin_op
         | EBApp
         | EBPair
         | EBWrite

datatype expr =
         EVar of var
         | EConst of expr_const
         | EUnOp of expr_un_op * expr
         | EBinOp of expr_bin_op * expr * expr
         | ECase of expr * expr * expr
         | EAbs of expr
         | ERec of expr
         | EAbsC of expr
         | EAppC of expr * cstr
         | EPack of cstr * expr
         | EUnpack of expr * expr
         | EHalt of expr
         | ELet of expr * expr
         | EFix of int * expr

fun EProj (p, e) = EUnOp (EUProj p, e)
fun EInj (c, e) = EUnOp (EUInj c, e)
fun EFold e = EUnOp (EUFold, e)
fun EUnfold e = EUnOp (EUUnfold, e)
fun ENew e = EUnOp (EUNew, e)
fun ERead e = EUnOp (EURead, e)

fun EApp (e1, e2) = EBinOp (EBApp, e1, e2)
fun EPair (e1, e2) = EBinOp (EBPair, e1, e2)
fun EWrite (e1, e2) = EBinOp (EBWrite, e1, e2)

fun const_type cn =
  case cn of
      ECTT => CTypeUnit
    | ECInt _ => CInt

type typing_judgement = ctx * expr * cstr * cstr

datatype typing =
         TyVar of typing_judgement
         | TyApp of typing_judgement * typing * typing
         | TyAbs of typing_judgement * kinding * typing
         | TyAppC of typing_judgement * typing * kinding
         | TyAbsC of typing_judgement * wfkind * typing
         | TyRec of typing_judgement * kinding * typing
         | TyFold of typing_judgement * kinding * typing
         | TyUnfold of typing_judgement * typing
         | TyPack of typing_judgement * kinding * kinding * typing
         | TyUnpack of typing_judgement * typing * typing
         | TyConst of typing_judgement
         | TyPair of typing_judgement * typing * typing
         | TyProj of typing_judgement * typing
         | TyInj of typing_judgement * typing * kinding
         | TyCase of typing_judgement * typing * typing * typing
         | TyNew of typing_judgement * typing
         | TyRead of typing_judgement * typing
         | TyWrite of typing_judgement * typing * typing
         | TySub of typing_judgement * typing * tyeq * proping
         | TyHalt of typing_judgement * typing
         | TyAppK of typing_judgement * typing * typing
         | TyLet of typing_judgement * typing * typing
         | TyFix of typing_judgement * kinding * typing
end

functor MicroTiMLUtilFun(MicroTiMLDef : SIG_MICRO_TIML_DEF) =
struct
open Util
open MicroTiMLDef

fun extract_judge_kdeq ke =
  case ke of
      KdEqKType j => j
    | KdEqKArrow (j, _, _) => j
    | KdEqBaseSort j => j
    | KdEqSubset (j, _, _) => j

fun extract_judge_proping pr =
  case pr of
      PrAdmit j => j

fun extract_judge_kinding kd =
  case kd of
      KdVar j => j
    | KdConst j => j
    | KdBinOp (j, _, _) => j
    | KdIte (j, _, _, _) => j
    | KdArrow (j, _, _, _) => j
    | KdAbs (j, _, _) => j
    | KdApp (j, _, _) => j
    | KdTimeAbs (j, _) => j
    | KdTimeApp (j, _, _) => j
    | KdQuan (j, _, _) => j
    | KdRec (j, _, _) => j
    | KdRef (j, _) => j
    | KdEq (j, _, _) => j
    | KdUnOp (j, _) => j
    | KdAdmit j => j

fun extract_judge_wfkind wk =
  case wk of
      WfKdType j => j
    | WfKdArrow (j, _, _) => j
    | WfKdBaseSort j => j
    | WfKdSubset (j, _, _) => j
    | WfKdAdmit j => j

fun extract_judge_wfprop wp =
  case wp of
      WfPropTrue j => j
    | WfPropFalse j => j
    | WfPropBinConn (j, _, _) => j
    | WfPropNot (j, _) => j
    | WfPropBinPred (j, _, _) => j
    | WfPropQuan (j, _) => j

fun extract_judge_tyeq te =
  case te of
      TyEqVar j => j
    | TyEqConst j => j
    | TyEqBinOp (j, _, _) => j
    | TyEqIte (j, _, _, _) => j
    | TyEqArrow (j, _, _, _) => j
    | TyEqApp (j, _, _) => j
    | TyEqTimeApp (j, _, _) => j
    | TyEqBeta (j, _, _, _) => j
    | TyEqBetaRev (j, _, _, _) => j
    | TyEqQuan (j, _, _) => j
    | TyEqRec (j, _, _) => j
    | TyEqRef (j, _) => j
    | TyEqAbs j => j
    | TyEqTimeAbs j => j
    | TyEqUnOp (j, _) => j
    | TyEqNatEq (j, _) => j

fun extract_judge_typing ty =
  case ty of
      TyVar j => j
    | TyApp (j, _, _) => j
    | TyAbs (j, _, _) => j
    | TyAppC (j, _, _) => j
    | TyAbsC (j, _, _) => j
    | TyRec (j, _, _) => j
    | TyFold (j, _, _) => j
    | TyUnfold (j, _) => j
    | TyPack (j, _, _, _) => j
    | TyUnpack (j, _, _) => j
    | TyConst j => j
    | TyPair (j, _, _) => j
    | TyProj (j, _) => j
    | TyInj (j, _, _) => j
    | TyCase (j, _, _, _) => j
    | TyNew (j, _) => j
    | TyRead (j, _) => j
    | TyWrite (j, _, _) => j
    | TySub (j, _, _, _) => j
    | TyHalt (j, _) => j
    | TyAppK (j, _, _) => j
    | TyLet (j, _, _) => j
    | TyFix (j, _, _) => j

fun extract_p_bin_conn (PBinConn a) = a
  | extract_p_bin_conn _ = raise (Impossible "extract_p_bin_conn")

fun extract_p_quan (PQuan a) = a
  | extract_p_quan _ = raise (Impossible "extract_p_quan")

fun extract_p_bin_pred (PBinPred a) = a
  | extract_p_bin_pred _ = raise (Impossible "extract_p_bin_pred")

fun extract_c_quan (CQuan a) = a
  | extract_c_quan _ = raise (Impossible "extract_c_quan")

fun extract_c_bin_op (CBinOp a) = a
  | extract_c_bin_op _ = raise (Impossible "extract_c_bin_op")

fun extract_c_un_op (CUnOp a) = a
  | extract_c_un_op _ = raise (Impossible "extract_c_un_op")

fun extract_c_time_app (CTimeApp a) = a
  | extract_c_time_app _ = raise (Impossible "extract_c_time_app")

fun extract_c_arrow (CArrow a) = a
  | extract_c_arrow _ = raise (Impossible "extract_c_arrow")

fun extract_c_sum (CBinOp (CBTypeSum, c1, c2)) = (c1, c2)
  | extract_c_sum _ = raise (Impossible "extract_c_sum")

fun extract_c_prod (CBinOp (CBTypeProd, c1, c2)) = (c1, c2)
  | extract_c_prod _ = raise (Impossible "extract_c_prod")

fun extract_c_rec (CRec a) = a
  | extract_c_rec _ = raise (Impossible "extract_c_rec")

fun extract_c_abs (CAbs a) = a
  | extract_c_abs _ = raise (Impossible "extract_c_abs")

fun extract_c_ref (CRef a) = a
  | extract_c_ref _ = raise (Impossible "extract_c_ref")

fun extract_k_time_fun (KBaseSort (BSTimeFun a)) = a
  | extract_k_time_fun _ = raise (Impossible "extract_k_time_fun")

fun extract_k_arrow (KArrow a) = a
  | extract_k_arrow _ = raise (Impossible "extract_k_arrow")

fun extract_e_inj (EUnOp (EUInj c, e)) = (c, e)
  | extract_e_inj _ = raise (Impossible "extract_e_inj")

fun extract_e_proj (EUnOp (EUProj p, e)) = (p, e)
  | extract_e_proj _ = raise (Impossible "extract_e_proj")

fun extract_e_abs (EAbs a) = a
  | extract_e_abs _ = raise (Impossible "extract_e_abs")

fun extract_e_abs_c (EAbsC a) = a
  | extract_e_abs_c _ = raise (Impossible "extract_e_abs_c")
end
