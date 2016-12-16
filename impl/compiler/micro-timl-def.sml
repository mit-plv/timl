functor MicroTiMLDefFun(
    structure Time : SIG_TIME
    structure Nat : SIG_NAT) :> SIG_MICRO_TIML_DEF =
struct
open Util

structure Time = Time
open Time
structure Nat = Nat
open Nat

datatype cstr_const =
         CCIdxTT
         | CCIdxTrue
         | CCIdxFalse
         | CCIdxNat of nat_type
         | CCTime of time_type
         | CCTypeUnit
         | CCTypeInt

datatype cstr_bin_op =
         CBTimeAdd
         | CBTimeMinus
         | CBTimeMult
         | CBTimeMax
         | CBTimeMin
         | CBNatAdd
         | CBNatMinus
         | CBNatMult
         | CBTypeProd
         | CBTypeSum

datatype cstr_un_op =
         CUCeil
         | CUFloor
         | CULog of int
         | CUDiv of int
         | CUNat2Time
         | CUBool2Nat

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
         | PBTimeLt
         | PBTimeEq
         | PBTimeGe
         | PBTimeGt
         | PBBigO of int
         | PBNatLe
         | PBNatLt
         | PBNatEq
         | PBNatGe
         | PBNatGt

datatype sort =
         BSNat
         | BSUnit
         | BSBool
         | BSTimeFun of int

datatype cstr =
         CVar of var
         | CConst of cstr_const
         | CUnOp of cstr_un_op * cstr
         | CBinOp of cstr_bin_op * cstr * cstr
         | CIte of cstr * cstr * cstr
         | CTimeAbs of cstr
         | CTimeApp of int * cstr * cstr
         | CArrow of cstr * cstr * cstr
         | CAbs of cstr
         | CApp of cstr * cstr
         | CQuan of quan * kind * cstr
         | CRec of kind * cstr
         | CTypeNat of cstr
         | CTypeArr of cstr * cstr

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
fun Tmult (c1, c2) = CBinOp (CBTimeMult, c1, c2)
fun Tmax (c1, c2) = CBinOp (CBTimeMax, c1, c2)
fun Tmin (c1, c2) = CBinOp (CBTimeMin, c1, c2)
fun TfromNat c = CUnOp (CUNat2Time, c)

fun PAnd (p1, p2) = PBinConn (PBCAnd, p1, p2)
fun POr (p1, p2) = PBinConn (PBCOr, p1, p2)
fun PImply (p1, p2) = PBinConn (PBCImply, p1, p2)
fun PIff (p1, p2) = PBinConn (PBCIff, p1, p2)

fun CForall (k, c) = CQuan (QuanForall, k, c)
fun CExists (k, c) = CQuan (QuanExists, k, c)

val CTypeUnit = CConst CCTypeUnit
val CTypeInt = CConst CCTypeInt

fun CProd (c1, c2) = CBinOp (CBTypeProd, c1, c2)
fun CSum (c1, c2) = CBinOp (CBTypeSum, c1, c2)

fun TLe (c1, c2) = PBinPred (PBTimeLe, c1, c2)
fun TEq (c1, c2) = PBinPred (PBTimeEq, c1, c2)

fun NLt (c1, c2) = PBinPred (PBNatLt, c1, c2)
fun NEq (c1, c2) = PBinPred (PBNatEq, c1, c2)

fun CNat n = CConst (CCIdxNat n)

fun CApps t cs =
  case cs of
      [] => t
    | c :: cs => CApps (CApp (t, c)) cs

fun const_kind cn =
  case cn of
      CCIdxTT => KUnit
    | CCIdxTrue => KBool
    | CCIdxFalse => KBool
    | CCIdxNat n => KNat
    | CCTime r => KTime
    | CCTypeUnit => KType
    | CCTypeInt => KType

fun cbinop_arg1_kind opr =
  case opr of
      CBTimeAdd => KTime
    | CBTimeMinus => KTime
    | CBTimeMult => KTime
    | CBTimeMax => KTime
    | CBTimeMin => KTime
    | CBNatAdd => KNat
    | CBNatMinus => KNat
    | CBNatMult => KNat
    | CBTypeProd => KType
    | CBTypeSum => KType

fun cbinop_arg2_kind opr =
  case opr of
      CBTimeAdd => KTime
    | CBTimeMinus => KTime
    | CBTimeMult => KTime
    | CBTimeMax => KTime
    | CBTimeMin => KTime
    | CBNatAdd => KNat
    | CBNatMinus => KNat
    | CBNatMult => KNat
    | CBTypeProd => KType
    | CBTypeSum => KType

fun cbinop_result_kind opr =
  case opr of
      CBTimeAdd => KTime
    | CBTimeMinus => KTime
    | CBTimeMult => KTime
    | CBTimeMax => KTime
    | CBTimeMin => KTime
    | CBNatAdd => KNat
    | CBNatMinus => KNat
    | CBNatMult => KNat
    | CBTypeProd => KType
    | CBTypeSum => KType

fun cunop_arg_kind opr =
  case opr of
      CUCeil => KTime
    | CUFloor => KTime
    | CULog _ => KTime
    | CUDiv _ => KTime
    | CUNat2Time => KNat
    | CUBool2Nat => KBool

fun cunop_result_kind opr =
  case opr of
      CUCeil => KNat
    | CUFloor => KNat
    | CULog _ => KTime
    | CUDiv _ => KTime
    | CUNat2Time => KTime
    | CUBool2Nat => KNat

fun binpred_arg1_kind opr =
  case opr of
      PBTimeLe => KTime
    | PBTimeLt => KTime
    | PBTimeEq => KTime
    | PBTimeGe => KTime
    | PBTimeGt => KTime
    | PBBigO n => KTimeFun n
    | PBNatLe => KNat
    | PBNatLt => KNat
    | PBNatEq => KNat
    | PBNatGe => KNat
    | PBNatGt => KNat

fun binpred_arg2_kind opr =
  case opr of
      PBTimeLe => KTime
    | PBTimeLt => KTime
    | PBTimeEq => KTime
    | PBTimeGe => KTime
    | PBTimeGt => KTime
    | PBBigO n => KTimeFun n
    | PBNatLe => KNat
    | PBNatLt => KNat
    | PBNatEq => KNat
    | PBNatGe => KNat
    | PBNatGt => KNat

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
         | KdEqSubsetElimLeft of kdeq_judgement * proping
         | KdEqSubsetElimRight of kdeq_judgement * proping

type kinding_judgement = kctx * cstr * kind
type wfkind_judgement = kctx * kind
type wfprop_judgement = kctx * prop

datatype kinding =
         KdVar of kinding_judgement
         | KdConst of kinding_judgement
         | KdUnOp of kinding_judgement * kinding
         | KdBinOp of kinding_judgement * kinding * kinding
         | KdIte of kinding_judgement * kinding * kinding * kinding
         | KdTimeAbs of kinding_judgement * kinding
         | KdTimeApp of kinding_judgement * kinding * kinding
         | KdArrow of kinding_judgement * kinding * kinding * kinding
         | KdAbs of kinding_judgement * wfkind * kinding
         | KdApp of kinding_judgement * kinding * kinding
         | KdQuan of kinding_judgement * wfkind * kinding
         | KdRec of kinding_judgement * wfkind * kinding
         | KdTypeNat of kinding_judgement * kinding
         | KdTypeArr of kinding_judgement * kinding * kinding
         | KdEq of kinding_judgement * kinding * kdeq
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
         | TyEqUnOp of tyeq_judgement * tyeq
         | TyEqBinOp of tyeq_judgement * tyeq * tyeq
         | TyEqIte of tyeq_judgement * tyeq * tyeq * tyeq
         | TyEqTimeAbs of tyeq_judgement
         | TyEqTimeApp of tyeq_judgement
         | TyEqArrow of tyeq_judgement * tyeq * proping * tyeq
         | TyEqAbs of tyeq_judgement
         | TyEqApp of tyeq_judgement * tyeq * tyeq
         | TyEqBeta of tyeq_judgement
         | TyEqBetaRev of tyeq_judgement
         | TyEqQuan of tyeq_judgement * kdeq * tyeq
         | TyEqRec of tyeq_judgement * kdeq * tyeq
         | TyEqTypeNat of tyeq_judgement * proping
         | TyEqTypeArr of tyeq_judgement * tyeq * proping
         | TyEqTrans of tyeq_judgement * tyeq * tyeq
         | TyEqNat of tyeq_judgement * proping
         | TyEqTime of tyeq_judgement * proping

datatype expr_const =
         ECTT
         | ECInt of int
         | ECNat of nat_type

datatype prim_expr_bin_op =
         PEBIntAdd

fun pebinop_arg1_type opr =
  case opr of
      PEBIntAdd => CTypeInt

fun pebinop_arg2_type opr =
  case opr of
      PEBIntAdd => CTypeInt

fun pebinop_result_type opr =
  case opr of
      PEBIntAdd => CTypeInt

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

datatype expr_bin_op =
         EBPrim of prim_expr_bin_op
         | EBApp
         | EBPair
         | EBNew
         | EBRead

datatype expr_tri_op =
         ETWrite

datatype expr =
         EVar of var
         | EConst of expr_const
         | EUnOp of expr_un_op * expr
         | EBinOp of expr_bin_op * expr * expr
         | ETriOp of expr_tri_op * expr * expr * expr
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

fun EPrim opr (e1, e2) = EBinOp (EBPrim opr, e1, e2)
fun EApp (e1, e2) = EBinOp (EBApp, e1, e2)
fun EPair (e1, e2) = EBinOp (EBPair, e1, e2)
fun ENew (e1, e2) = EBinOp (EBNew, e1, e2)
fun ERead (e1, e2) = EBinOp (EBRead, e1, e2)

fun EWrite (e1, e2, e3) = ETriOp (ETWrite, e1, e2, e3)

datatype value =
         VConst of expr
         | VPair of expr * value * value
         | VInj of expr * value
         | VAbs of expr
         | VAbsC of expr
         | VPack of expr * value
         | VFold of expr * value

fun EFst e = EProj (ProjFst, e)
fun ESnd e = EProj (ProjSnd, e)
fun EInl e = EInj (InjInl, e)
fun EInr e = EInj (InjInr, e)

val ETT = EConst ECTT
fun EInt i = EConst (ECInt i)
fun ENat n = EConst (ECNat n)

fun const_type cn =
  case cn of
      ECTT => CTypeUnit
    | ECInt _ => CTypeInt
    | ECNat n => CTypeNat (CNat n)

type typing_judgement = ctx * expr * cstr * cstr

datatype typing =
         TyVar of typing_judgement
         | TyApp of typing_judgement * typing * typing
         | TyAbs of typing_judgement * kinding * typing
         | TyAppC of typing_judgement * typing * kinding
         | TyAbsC of typing_judgement * wfkind * value * typing
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
         | TyNew of typing_judgement * typing * typing
         | TyRead of typing_judgement * typing * typing * proping
         | TyWrite of typing_judgement * typing * typing * proping * typing
         | TySubTy of typing_judgement * typing * tyeq
         | TySubTi of typing_judgement * typing * proping
         | TyHalt of typing_judgement * typing
         | TyLet of typing_judgement * typing * typing
         | TyFix of typing_judgement * kinding * typing
         | TyPrimBinOp of typing_judgement * typing * typing
end
