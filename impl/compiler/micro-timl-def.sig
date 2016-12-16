signature SIG_TIME =
sig
    eqtype time_type

    val Time0 : time_type
    val Time1 : time_type

    val from_string : string -> time_type
    val str_time : time_type -> string
end

signature SIG_NAT =
sig
    eqtype nat_type

    val from_int : int -> nat_type
    val str_nat : nat_type -> string
end

signature SIG_MICRO_TIML_DEF =
sig
    structure Time : SIG_TIME
    structure Nat : SIG_NAT

    datatype cstr_const =
             CCIdxTT
             | CCIdxTrue (* new *)
             | CCIdxFalse (* new *)
             | CCIdxNat of Nat.nat_type
             | CCTime of Time.time_type
             | CCTypeUnit
             | CCTypeInt

    datatype cstr_bin_op =
             CBTimeAdd
             | CBTimeMinus
             | CBTimeMult (* new *)
             | CBTimeMax
             | CBTimeMin (* new *)
             | CBNatAdd (* new *)
             | CBNatMinus (* new *)
             | CBNatMult (* new *)
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
             | PBTimeLt (* new *)
             | PBTimeEq
             | PBTimeGe (* new *)
             | PBTimeGt (* new *)
             | PBBigO of int
             | PBNatLe (* new *)
             | PBNatLt (* new *)
             | PBNatEq (* new *)
             | PBNatGe (* new *)
             | PBNatGt (* new *)

    datatype sort =
             BSNat
             | BSUnit
             | BSBool
             | BSTimeFun of int

    datatype cstr =
             CVar of var
             | CConst of cstr_const
             | CUnOp of cstr_un_op * cstr (* new *)
             | CBinOp of cstr_bin_op * cstr * cstr
             | CIte of cstr * cstr * cstr
             | CTimeAbs of cstr
             | CTimeApp of int * cstr * cstr
             | CArrow of cstr * cstr * cstr
             | CAbs of cstr
             | CApp of cstr * cstr
             | CQuan of quan * kind * cstr
             | CRec of kind * cstr
             | CTypeNat of cstr (* new *)
             | CTypeArr of cstr * cstr (* new & CRef removed *)

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
    val Tmult : cstr * cstr -> cstr (* new *)
    val Tmax : cstr * cstr -> cstr
    val Tmin : cstr * cstr -> cstr (* new *)
    val TfromNat : cstr -> cstr (* new *)

    val PAnd : prop * prop -> prop
    val POr : prop * prop -> prop
    val PImply : prop * prop -> prop
    val PIff : prop * prop -> prop

    val CForall : kind * cstr -> cstr
    val CExists : kind * cstr -> cstr

    val CTypeUnit : cstr
    val CTypeInt : cstr (* rename CInt to CTypeInt *)

    val CProd : cstr * cstr -> cstr
    val CSum : cstr * cstr -> cstr

    val TLe : cstr * cstr -> prop
    val TEq : cstr * cstr -> prop

    val NLt : cstr * cstr -> prop (* new helper *)
    val NEq : cstr * cstr -> prop (* new helper *)

    val CNat : Nat.nat_type -> cstr (* new helper *)

    val CApps : cstr -> cstr list -> cstr

    val const_kind : cstr_const -> kind
    val cbinop_arg1_kind : cstr_bin_op -> kind
    val cbinop_arg2_kind : cstr_bin_op -> kind
    val cbinop_result_kind : cstr_bin_op -> kind
    val cunop_arg_kind : cstr_un_op -> kind (* new *)
    val cunop_result_kind : cstr_un_op -> kind (* new *)
    val binpred_arg1_kind : prop_bin_pred -> kind
    val binpred_arg2_kind : prop_bin_pred -> kind

    type kctx = kind list

    val BSTime : sort

    type kdeq_judgement = kctx * kind * kind
    type proping_judgement = kctx * prop

    datatype proping =
             PrAdmit of proping_judgement (* cannot interpret; just admit *)

    datatype kdeq =
             KdEqKType of kdeq_judgement
             | KdEqKArrow of kdeq_judgement * kdeq * kdeq
             | KdEqBaseSort of kdeq_judgement
             | KdEqSubset of kdeq_judgement * kdeq * proping
             | KdEqSubsetElimLeft of kdeq_judgement * proping (* new *)
             | KdEqSubsetElimRight of kdeq_judgement * proping (* new *)

    type kinding_judgement = kctx * cstr * kind
    type wfkind_judgement = kctx * kind
    type wfprop_judgement = kctx * prop

    datatype kinding =
             KdVar of kinding_judgement
             | KdConst of kinding_judgement
             | KdUnOp of kinding_judgement * kinding (* new *)
             | KdBinOp of kinding_judgement * kinding * kinding
             | KdIte of kinding_judgement * kinding * kinding * kinding
             | KdTimeAbs of kinding_judgement * kinding
             | KdTimeApp of kinding_judgement * kinding * kinding
             | KdArrow of kinding_judgement * kinding * kinding * kinding
             | KdAbs of kinding_judgement * wfkind * kinding
             | KdApp of kinding_judgement * kinding * kinding
             | KdQuan of kinding_judgement * wfkind * kinding
             | KdRec of kinding_judgement * wfkind * kinding
             | KdTypeNat of kinding_judgement * kinding (* new *)
             | KdTypeArr of kinding_judgement * kinding * kinding (* new & KdRef removed *)
             | KdEq of kinding_judgement * kinding * kdeq
             | KdAdmit of kinding_judgement (* TODO: eliminate this rule *)

         and wfkind =
             WfKdType of wfkind_judgement
             | WfKdArrow of wfkind_judgement * wfkind * wfkind
             | WfKdBaseSort of wfkind_judgement
             | WfKdSubset of wfkind_judgement * wfkind * wfprop
             | WfKdAdmit of wfkind_judgement (* TODO: eliminate this rule *)

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
             | TyEqUnOp of tyeq_judgement * tyeq (* new *)
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
             | TyEqTypeNat of tyeq_judgement * proping (* new *)
             | TyEqTypeArr of tyeq_judgement * tyeq * proping (* new & TyEqRef removed *)
             | TyEqTrans of tyeq_judgement * tyeq * tyeq
             | TyEqNat of tyeq_judgement * proping (* new *)
             | TyEqTime of tyeq_judgement * proping (* new *)

    datatype expr_const =
             ECTT
             | ECInt of int
             | ECNat of Nat.nat_type (* new *)

    datatype prim_expr_bin_op =
             PEBIntAdd

    val pebinop_arg1_type : prim_expr_bin_op -> cstr
    val pebinop_arg2_type : prim_expr_bin_op -> cstr
    val pebinop_result_type : prim_expr_bin_op -> cstr

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
             | ETriOp of expr_tri_op * expr * expr * expr (* new *)
             | ECase of expr * expr * expr
             | EAbs of expr
             | ERec of expr
             | EAbsC of expr
             | EAppC of expr * cstr
             | EPack of cstr * expr
             | EUnpack of expr * expr
             | EHalt of expr (* new, introduced in CPS *)
             | ELet of expr * expr (* new, introduced in CPS *)
             | EFix of int * expr (* new, introduced in CloConv *)

    val EProj : projector * expr -> expr
    val EInj : injector * expr -> expr
    val EFold : expr -> expr
    val EUnfold : expr -> expr

    val EPrim : prim_expr_bin_op -> expr * expr -> expr
    val EApp : expr * expr -> expr
    val EPair : expr * expr -> expr
    val ENew : expr * expr -> expr
    val ERead : expr * expr -> expr

    val EWrite : expr * expr * expr -> expr

    datatype value =
             VConst of expr
             | VPair of expr * value * value
             | VInj of expr * value
             | VAbs of expr
             | VAbsC of expr
             | VPack of expr * value
             | VFold of expr * value

    val EFst : expr -> expr
    val ESnd : expr -> expr
    val EInl : expr -> expr
    val EInr : expr -> expr

    val ETT : expr
    val EInt : int -> expr
    val ENat : Nat.nat_type -> expr

    val const_type : expr_const -> cstr

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
             | TySubTy of typing_judgement * typing * tyeq (* new : split from TySub *)
             | TySubTi of typing_judgement * typing * proping (* new : split from TySub *)
             | TyHalt of typing_judgement * typing (* new, introduced in CPS *)
             | TyLet of typing_judgement * typing * typing (* new *)
             | TyFix of typing_judgement * kinding * typing (* new, introduced in CloConv *)
             | TyPrimBinOp of typing_judgement * typing * typing (* new *)
end
