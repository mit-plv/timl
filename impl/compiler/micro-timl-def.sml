signature SIG_TIME =
sig
  type time_type

  val Time0 : time_type
  val Time1 : time_type

  val str_time : time_type -> string
end

functor MicroTiML(Time : SIG_TIME) =
struct
  open Util

  infixr 0 $

  type time_type = Time.time_type

  val Time0 = Time.Time0
  val Time1 = Time.Time1

  type nat = int

  datatype cstr_const =
    CCIdxTT
  | CCIdxNat of nat
  | CCTime of time_type
  | CCTypeUnit
  | CCTypeInt

  datatype cstr_bin_op =
    CBTimeAdd
  | CBTimeMinus
  | CBTimeMax
  | CBTypeProd
  | CBTypeSum

  datatype quan =
    QuanForall
  | QuanExists

  type var = nat

  datatype prop_bin_conn =
    PBCAnd
  | PBCOr
  | PBCImply
  | PBCIff

  datatype prop_bin_pred =
    PBTimeLe
  | PBTimeEq
  | PBBigO of nat

  datatype sort =
    BSNat
  | BSUnit
  | BSBool
  | BSTimeFun of nat

  datatype cstr =
    CVar of var
  | CConst of cstr_const
  | CBinOp of cstr_bin_op * cstr * cstr
  | CIte of cstr * cstr * cstr
  | CTimeAbs of cstr
  | CTimeApp of nat * cstr * cstr
  | CArrow of cstr * cstr * cstr
  | CAbs of cstr
  | CApp of cstr * cstr
  | CQuan of quan * kind * cstr
  | CRec of kind * cstr
  | CRef of cstr

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

  fun cbinop_arg2_kind opr =
    case opr of
      CBTimeAdd => KTime
    | CBTimeMinus => KTime
    | CBTimeMax => KTime
    | CBTypeProd => KType
    | CBTypeSum => KType

  fun cbinop_result_kind opr =
    case opr of
      CBTimeAdd => KTime
    | CBTimeMinus => KTime
    | CBTimeMax => KTime
    | CBTypeProd => KType
    | CBTypeSum => KType

  fun binpred_arg1_kind opr =
    case opr of
      PBTimeLe => KTime
    | PBTimeEq => KTime
    | PBBigO n => KTimeFun n

  fun binpred_arg2_kind opr =
    case opr of
      PBTimeLe => KTime
    | PBTimeEq => KTime
    | PBBigO n => KTimeFun n

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

  and wfkind =
    WfKdType of wfkind_judgement
  | WfKdArrow of wfkind_judgement * wfkind * wfkind
  | WfKdBaseSort of wfkind_judgement
  | WfKdSubset of wfkind_judgement * wfkind * wfprop

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

  fun EProj (p, e) = EUnOp (EUProj p, e)
  fun EInj (c, e) = EUnOp (EUInj c, e)
  fun EFold e = EUnOp (EUFold, e)
  fun EUnfold e = EUnOp (EUUnfold, e)
  fun ENew e = EUnOp (EUNew, e)
  fun ERead e = EUnOp (EURead, e)

  fun EApp (e1, e2) = EBinOp (EBApp, e1, e2)
  fun EPair (e1, e2) = EBinOp (EBPair, e1, e2)
  fun EWrite (e1, e2) = EBinOp (EBWrite, e1, e2)

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

  fun extract_judge_wfkind wk =
    case wk of
      WfKdType j => j
    | WfKdArrow (j, _, _) => j
    | WfKdBaseSort j => j
    | WfKdSubset (j, _, _) => j

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

  functor AstGenericTransformer(Action:
  sig
    type down
    type up

    val upward_base : up
    val combiner : up * up -> up

    val add_kind : kind option * down -> down
    val add_type : cstr option * down -> down

    val transformer_cstr : (cstr * down -> cstr * up) * (kind * down -> kind * up) -> cstr * down -> (cstr * up) option
    val transformer_kind : (kind * down -> kind * up) * (prop * down -> prop * up) -> kind * down -> (kind * up) option
    val transformer_prop : (prop * down -> prop * up) * (cstr * down -> cstr * up) -> prop * down -> (prop * up) option
    val transformer_expr : (expr * down -> expr * up) * (cstr * down -> cstr * up) -> expr * down -> (expr * up) option
  end) =
  struct
    open List

    val combine = foldl Action.combiner Action.upward_base

    fun default_transform_cstr (c, down) =
      case c of
        CVar x => (CVar x, Action.upward_base)
      | CConst cn =>  (CConst cn, Action.upward_base)
      | CBinOp (opr, c1, c2) =>
          let
            val (c1, up1) = transform_cstr (c1, down)
            val (c2, up2) = transform_cstr (c2, down)
          in
            (CBinOp (opr, c1, c2), combine [up1, up2])
          end
      | CIte (i1, i2, i3) =>
          let
            val (i1, up1) = transform_cstr (i1, down)
            val (i2, up2) = transform_cstr (i2, down)
            val (i3, up3) = transform_cstr (i3, down)
          in
            (CIte (i1, i2, i3), combine [up1, up2, up3])
          end
      | CTimeAbs i =>
          let
            val (i, up1) = transform_cstr (i, Action.add_kind (SOME KTime, down))
          in
            (CTimeAbs i, combine [up1])
          end
      | CTimeApp (arity, c1, c2) =>
          let
            val (c1, up1) = transform_cstr (c1, down)
            val (c2, up2) = transform_cstr (c2, down)
          in
            (CTimeApp (arity, c1, c2), combine [up1, up2])
          end
      | CArrow (t1, i, t2) =>
          let
            val (t1, up1) = transform_cstr (t1, down)
            val (i, up2) = transform_cstr (i, down)
            val (t2, up3) = transform_cstr (t2, down)
          in
            (CArrow (t1, i, t2), combine [up1, up2, up3])
          end
      | CAbs t =>
          let
            val (t, up1) = transform_cstr (t, Action.add_kind (NONE, down))
          in
            (CAbs t, combine [up1])
          end
      | CApp (c1, c2) =>
          let
            val (c1, up1) = transform_cstr (c1, down)
            val (c2, up2) = transform_cstr (c2, down)
          in
            (CApp (c1, c2), combine [up1, up2])
          end
      | CQuan (q, k, c) =>
          let
            val (k, up1) = transform_kind (k, down)
            val (c, up2) = transform_cstr (c, Action.add_kind (SOME k, down))
          in
            (CQuan (q, k, c), combine [up1, up2])
          end
      | CRec (k, t) =>
          let
            val (k, up1) = transform_kind (k, down)
            val (t, up2) = transform_cstr (t, Action.add_kind (SOME k, down))
          in
            (CRec (k, t), combine [up1, up2])
          end
      | CRef t =>
          let
            val (t, up1) = transform_cstr (t, down)
          in
            (CRef t, combine [up1])
          end

    and transform_cstr (c, down) =
      case Action.transformer_cstr (transform_cstr, transform_kind) (c, down) of
        SOME res => res
      | NONE => default_transform_cstr (c, down)

    and default_transform_kind (k, down) =
      case k of
        KType => (KType, Action.upward_base)
      | KArrow (k1, k2) =>
          let
            val (k1, up1) = transform_kind (k1, down)
            val (k2, up2) = transform_kind (k2, down)
          in
            (KArrow (k1, k2), combine [up1, up2])
          end
      | KBaseSort b => (KBaseSort b, Action.upward_base)
      | KSubset (k, p) =>
          let
            val (k, up1) = transform_kind (k, down)
            val (p, up2) = transform_prop (p, Action.add_kind (SOME k, down))
          in
            (KSubset (k, p), combine [up1, up2])
          end

    and transform_kind (k, down) =
      case Action.transformer_kind (transform_kind, transform_prop) (k, down) of
        SOME res => res
      | NONE => default_transform_kind (k, down)

    and default_transform_prop (p, down) =
      case p of
        PTrue => (PTrue, Action.upward_base)
      | PFalse => (PFalse, Action.upward_base)
      | PBinConn (opr, p1, p2) =>
          let
            val (p1, up1) = transform_prop (p1, down)
            val (p2, up2) = transform_prop (p2, down)
          in
            (PBinConn (opr, p1, p2), combine [up1, up2])
          end
      | PNot p =>
          let
            val (p, up1) = transform_prop (p, down)
          in
            (PNot p, combine [up1])
          end
      | PBinPred (opr, i1, i2) =>
          let
            val (i1, up1) = transform_cstr (i1, down)
            val (i2, up2) = transform_cstr (i2, down)
          in
            (PBinPred (opr, i1, i2), combine [up1, up2])
          end
      | PQuan (q, b, p) =>
          let
            val (p, up1) = transform_prop (p, Action.add_kind (SOME (KBaseSort b), down))
          in
            (PQuan (q, b, p), combine [up1])
          end

    and transform_prop (p, down) =
      case Action.transformer_prop (transform_prop, transform_cstr) (p, down) of
        SOME res => res
      | NONE => default_transform_prop (p, down)

    and default_transform_expr (e, down) =
      case e of
        EVar x => (EVar x, Action.upward_base)
      | EConst cn => (EConst cn, Action.upward_base)
      | EUnOp (opr, e) =>
          let
            val (e, up1) = transform_expr (e, down)
          in
            (EUnOp (opr, e), combine [up1])
          end
      | EBinOp (opr, e1, e2) =>
          let
            val (e1, up1) = transform_expr (e1, down)
            val (e2, up2) = transform_expr (e2, down)
          in
            (EBinOp (opr, e1, e2), combine [up1, up2])
          end
      | ECase (e, e1, e2) =>
          let
            val (e, up1) = transform_expr (e, down)
            val (e1, up2) = transform_expr (e1, Action.add_type (NONE, down))
            val (e2, up3) = transform_expr (e2, Action.add_type (NONE, down))
          in
            (ECase (e, e1, e2), combine [up1, up2, up3])
          end
      | EAbs e =>
          let
            val (e, up1) = transform_expr (e, Action.add_type (NONE, down))
          in
            (EAbs e, combine [up1])
          end
      | ERec e =>
          let
            val (e, up1) = transform_expr (e, Action.add_type (NONE, down))
          in
            (ERec e, combine [up1])
          end
      | EAbsC e =>
          let
            val (e, up1) = transform_expr (e, Action.add_kind (NONE, down))
          in
            (EAbsC e, combine [up1])
          end
      | EAppC (e, c) =>
          let
            val (e, up1) = transform_expr (e, down)
            val (c, up2) = transform_cstr (c, down)
          in
            (EAppC (e, c), combine [up1, up2])
          end
      | EPack (c, e) =>
          let
            val (c, up1) = transform_cstr (c, down)
            val (e, up2) = transform_expr (e, down)
          in
            (EPack (c, e), combine [up1, up2])
          end
      | EUnpack (e1, e2) =>
          let
            val (e1, up1) = transform_expr (e1, down)
            val (e2, up2) = transform_expr (e2, Action.add_type (NONE, Action.add_kind (NONE, down)))
          in
            (EUnpack (e1, e2), combine [up1, up2])
          end

    and transform_expr (e, down) =
      case Action.transformer_expr (transform_expr, transform_cstr) (e, down) of
        SOME res => res
      | NONE => default_transform_expr (e, down)
  end

  functor AstGenericOnlyDownTransformer(Action:
  sig
    type down

    val add_kind : kind option * down -> down
    val add_type : cstr option * down -> down

    val transformer_cstr : (cstr * down -> cstr) * (kind * down -> kind) -> cstr * down -> cstr option
    val transformer_kind : (kind * down -> kind) * (prop * down -> prop) -> kind * down -> kind option
    val transformer_prop : (prop * down -> prop) * (cstr * down -> cstr) -> prop * down -> prop option
    val transformer_expr : (expr * down -> expr) * (cstr * down -> cstr) -> expr * down -> expr option
  end) =
  struct
    structure Transformer = AstGenericTransformer(
    struct
      type down = Action.down
      type up = unit

      val upward_base = ()
      fun combiner ((), ()) = ()

      val add_kind = Action.add_kind
      val add_type = Action.add_type

      fun transformer_cstr (on_cstr, on_kind) =
        let
          val on_cstr_no_up = fst o on_cstr
          val on_kind_no_up = fst o on_kind
        in
          Option.map (fn c => (c, ())) o Action.transformer_cstr (on_cstr_no_up, on_kind_no_up)
        end

      fun transformer_kind (on_kind, on_prop) =
        let
          val on_kind_no_up = fst o on_kind
          val on_prop_no_up = fst o on_prop
        in
          Option.map (fn k => (k, ())) o Action.transformer_kind (on_kind_no_up, on_prop_no_up)
        end

      fun transformer_prop (on_prop, on_cstr) =
        let
          val on_prop_no_up = fst o on_prop
          val on_cstr_no_up = fst o on_cstr
        in
          Option.map (fn p => (p, ())) o Action.transformer_prop (on_prop_no_up, on_cstr_no_up)
        end

      fun transformer_expr (on_expr, on_cstr) =
        let
          val on_expr_no_up = fst o on_expr
          val on_cstr_no_up = fst o on_cstr
        in
          Option.map (fn e => (e, ())) o Action.transformer_expr (on_expr_no_up, on_cstr_no_up)
        end
    end)

    val transform_cstr = fst o Transformer.transform_cstr
    val transform_kind = fst o Transformer.transform_kind
    val transform_prop = fst o Transformer.transform_prop
    val transform_expr = fst o Transformer.transform_expr
  end

  functor AstGenericOnlyUpTransformer(Action:
  sig
    type up

    val upward_base : up
    val combiner : up * up -> up

    val transformer_cstr : (cstr -> cstr * up) * (kind -> kind * up) -> cstr -> (cstr * up) option
    val transformer_kind : (kind -> kind * up) * (prop -> prop * up) -> kind -> (kind * up) option
    val transformer_prop : (prop -> prop * up) * (cstr -> cstr * up) -> prop -> (prop * up) option
    val transformer_expr : (expr -> expr * up) * (cstr -> cstr * up) -> expr -> (expr * up) option
  end) =
  struct
    structure Transformer = AstGenericTransformer(
    struct
      type down = unit
      type up = Action.up

      val upward_base = Action.upward_base
      val combiner = Action.combiner

      fun add_kind (_, ()) = ()
      fun add_type (_, ()) = ()

      fun transformer_cstr (on_cstr, on_kind) =
        let
          val on_cstr_no_down = on_cstr o (fn c => (c, ()))
          val on_kind_no_down = on_kind o (fn k => (k, ()))
        in
          Action.transformer_cstr (on_cstr_no_down, on_kind_no_down) o fst
        end

      fun transformer_kind (on_kind, on_prop) =
        let
          val on_kind_no_down = on_kind o (fn k => (k, ()))
          val on_prop_no_down = on_prop o (fn p => (p, ()))
        in
          Action.transformer_kind (on_kind_no_down, on_prop_no_down) o fst
        end

      fun transformer_prop (on_prop, on_cstr) =
        let
          val on_prop_no_down = on_prop o (fn p => (p, ()))
          val on_cstr_no_down = on_cstr o (fn c => (c, ()))
        in
          Action.transformer_prop (on_prop_no_down, on_cstr_no_down) o fst
        end

      fun transformer_expr (on_expr, on_cstr) =
        let
          val on_expr_no_down = on_expr o (fn e => (e, ()))
          val on_cstr_no_down = on_cstr o (fn c => (c, ()))
        in
          Action.transformer_expr (on_expr_no_down, on_cstr_no_down) o fst
        end
    end)

    val transform_cstr = Transformer.transform_cstr o (fn c => (c, ()))
    val transform_kind = Transformer.transform_kind o (fn k => (k, ()))
    val transform_prop = Transformer.transform_prop o (fn p => (p, ()))
    val transform_expr = Transformer.transform_expr o (fn e => (e, ()))
  end

  functor DerivGenericTransformer(Action:
  sig
    type down
    type up

    val upward_base : up
    val combiner : up * up -> up

    val add_kind : (kind * down) -> down
    val add_type : (cstr * down) -> down

    val on_pr_leaf : proping_judgement * down -> proping_judgement * up
    val on_ke_leaf : kdeq_judgement * down -> kdeq_judgement * up
    val on_kd_leaf : kinding_judgement * down -> kinding_judgement * up
    val on_wk_leaf : wfkind_judgement * down -> wfkind_judgement * up
    val on_wp_leaf : wfprop_judgement * down -> wfprop_judgement * up
    val on_te_leaf : tyeq_judgement * down -> tyeq_judgement * up
    val on_ty_leaf : typing_judgement * down -> typing_judgement * up

    val shift_c_c : int -> int -> cstr -> cstr
    val shift_c_k : int -> int -> kind -> kind

    val subst_c_c : int -> cstr -> cstr -> cstr

    val transformer_proping : proping * down -> (proping * up) option
    val transformer_kdeq : (kdeq * down -> kdeq * up) * (proping * down -> proping * up) -> kdeq * down -> (kdeq * up) option
    val transformer_kinding : (kinding * down -> kinding * up) * (wfkind * down -> wfkind * up) * (kdeq * down -> kdeq * up)
      -> kinding * down -> (kinding * up) option
    val transformer_wfkind : (wfkind * down -> wfkind * up) * (wfprop * down -> wfprop * up) -> wfkind * down -> (wfkind * up) option
    val transformer_wfprop : (wfprop * down -> wfprop * up) * (kinding * down -> kinding * up) -> wfprop * down -> (wfprop * up) option
    val transformer_tyeq : (tyeq * down -> tyeq * up) * (proping * down -> proping * up) * (kdeq * down -> kdeq * up)
      -> tyeq * down -> (tyeq * up) option
    val transformer_typing : (typing * down -> typing * up) * (kinding * down -> kinding * up) * (wfkind * down -> wfkind * up)
      * (tyeq * down -> tyeq * up) * (proping * down -> proping * up) -> typing * down -> (typing * up) option
  end) =
  struct
    open List

    val combine = foldl Action.combiner Action.upward_base

    fun as_KdEqKArrow ke1 ke2 =
      let
        val jke1 = extract_judge_kdeq ke1
        val jke2 = extract_judge_kdeq ke2
      in
        (#1 jke1, KArrow (#2 jke1, #2 jke2), KArrow (#3 jke1, #3 jke2))
      end

    fun as_KdEqKSubset ke pr =
      let
        val jke = extract_judge_kdeq ke
        val jpr = extract_judge_proping pr
        val (_, p1, p2) = extract_p_bin_conn (#2 jpr)
      in
        (#1 jke, KSubset (#2 jke, p1), KSubset (#3 jke, p2))
      end

    fun as_WfPropQuan q b wp =
      let
        val jwp = extract_judge_wfprop wp
      in
        (tl $ #1 jwp, PQuan (q, b, #2 jwp))
      end

    fun as_WfPropBinPred opr kd1 kd2 =
      let
        val jkd1 = extract_judge_kinding kd1
        val jkd2 = extract_judge_kinding kd2
      in
        (#1 jkd1, PBinPred (opr, #2 jkd1, #2 jkd2))
      end

    fun as_WfPropNot wp =
      let
        val jwp = extract_judge_wfprop wp
      in
        (#1 jwp, PNot (#2 jwp))
      end

    fun as_WfPropBinConn opr wp1 wp2 =
      let
        val jwp1 = extract_judge_wfprop wp1
        val jwp2 = extract_judge_wfprop wp2
      in
        (#1 jwp1, PBinConn (opr, #2 jwp1, #2 jwp2))
      end

    fun as_WfKdSubset wk wp =
      let
        val jwk = extract_judge_wfkind wk
        val jwp = extract_judge_wfprop wp
      in
        (#1 jwk, KSubset (#2 jwk, #2 jwp))
      end

    fun as_WfKdArrow wk1 wk2 =
      let
        val jwk1 = extract_judge_wfkind wk1
        val jwk2 = extract_judge_wfkind wk2
      in
        (#1 jwk1, KArrow (#2 jwk1, #2 jwk2))
      end

    fun as_KdEq kd ke =
      let
        val jkd = extract_judge_kinding kd
        val jke = extract_judge_kdeq ke
      in
        (#1 jkd, #2 jkd, #2 jke)
      end

    fun as_KdRef kd =
      let
        val jkd = extract_judge_kinding kd
      in
        (#1 jkd, CRef (#2 jkd), KType)
      end

    fun as_KdRec wk kd =
      let
        val jwk = extract_judge_wfkind wk
        val jkd = extract_judge_kinding kd
      in
        (#1 jwk, CRec (#2 jwk, #2 jkd), #2 jwk)
      end

    fun as_KdQuan q wk kd =
      let
        val jwk = extract_judge_wfkind wk
        val jkd = extract_judge_kinding kd
      in
        (#1 jwk, CQuan (q, #2 jwk, #2 jkd), KType)
      end

    fun as_KdTimeApp kd1 kd2 =
      let
        val jkd1 = extract_judge_kinding kd1
        val arity = extract_k_time_fun (#3 jkd1)
        val jkd2 = extract_judge_kinding kd2
      in
        (#1 jkd1, CTimeApp (arity - 1, #2 jkd1, #2 jkd2), KTimeFun (arity - 1))
      end

    fun as_KdTimeAbs kd =
      let
        val jkd = extract_judge_kinding kd
        val arity = extract_k_time_fun (#3 jkd)
      in
        (tl $ #1 jkd, CTimeAbs (#2 jkd), KTimeFun (arity + 1))
      end

    fun as_KdApp kd1 kd2 =
      let
        val jkd1 = extract_judge_kinding kd1
        val jkd2 = extract_judge_kinding kd2
        val (k1, k2) = extract_k_arrow (#3 jkd1)
      in
        (#1 jkd1, CApp (#2 jkd1, #2 jkd2), k2)
      end

    fun as_KdAbs wk kd =
      let
        val jwk = extract_judge_wfkind wk
        val jkd = extract_judge_kinding kd
      in
        (#1 jwk, CAbs (#2 jkd), KArrow (#2 jwk, Action.shift_c_k ~1 0 (#3 jkd)))
      end

    fun as_KdArrow kd1 kd2 kd3 =
      let
        val jkd1 = extract_judge_kinding kd1
        val jkd2 = extract_judge_kinding kd2
        val jkd3 = extract_judge_kinding kd3
      in
        (#1 jkd1, CArrow (#2 jkd1, #2 jkd2, #2 jkd3), KType)
      end

    fun as_KdIte kd1 kd2 kd3 =
      let
        val jkd1 = extract_judge_kinding kd1
        val jkd2 = extract_judge_kinding kd2
        val jkd3 = extract_judge_kinding kd3
      in
        (#1 jkd1, CIte (#2 jkd1, #2 jkd2, #2 jkd3), #3 jkd2)
      end

    fun as_KdBinOp opr kd1 kd2 =
      let
        val jkd1 = extract_judge_kinding kd1
        val jkd2 = extract_judge_kinding kd2
      in
        (#1 jkd1, CBinOp (opr, #2 jkd1, #2 jkd2), cbinop_result_kind opr)
      end

    fun as_TyEqRef te =
      let
        val jte = extract_judge_tyeq te
      in
        (#1 jte, CRef (#2 jte), CRef (#3 jte))
      end

    fun as_TyEqRec ke te =
      let
        val jke = extract_judge_kdeq ke
        val jte = extract_judge_tyeq te
      in
       (#1 jke, CRec (#2 jke, #2 jte), CRec (#3 jke, #3 jte))
      end

    fun as_TyEqBetaRev te1 te2 te3 =
      let
        val jte1 = extract_judge_tyeq te1
        val jte2 = extract_judge_tyeq te2
        val jte3 = extract_judge_tyeq te3
      in
        (#1 jte1, #2 jte3, CApp (#3 jte1, #3 jte2))
      end

    fun as_TyEqBeta te1 te2 te3 =
      let
        val jte1 = extract_judge_tyeq te1
        val jte2 = extract_judge_tyeq te2
        val jte3 = extract_judge_tyeq te3
      in
        (#1 jte1, CApp (#2 jte1, #2 jte2), #3 jte3)
      end

    fun as_TyEqTimeApp arity te1 te2 =
      let
        val jte1 = extract_judge_tyeq te1
        val jte2 = extract_judge_tyeq te2
      in
        (#1 jte1, CTimeApp (arity, #2 jte1, #2 jte2), CTimeApp (arity, #3 jte1, #3 jte2))
      end

    fun as_TyEqQuan q ke te =
      let
        val jke = extract_judge_kdeq ke
        val jte = extract_judge_tyeq te
      in
        (#1 jke, CQuan (q, #2 jke, #2 jte), CQuan (q, #3 jke, #3 jte))
      end

    fun as_TyEqApp te1 te2 =
      let
        val jte1 = extract_judge_tyeq te1
        val jte2 = extract_judge_tyeq te2
      in
        (#1 jte1, CApp (#2 jte1, #2 jte2), CApp (#3 jte1, #3 jte2))
      end

    fun as_TyEqArrow te1 pr te2 =
      let
        val jte1 = extract_judge_tyeq te1
        val jpr = extract_judge_proping pr
        val jte2 = extract_judge_tyeq te2
        val (_, i1, i2) = extract_p_bin_pred (#2 jpr)
      in
        (#1 jte1, CArrow (#2 jte1, i1, #2 jte2), CArrow (#3 jte1, i2, #3 jte2))
      end

    fun as_TyEqIte te1 te2 te3 =
      let
        val jte1 = extract_judge_tyeq te1
        val jte2 = extract_judge_tyeq te2
        val jte3 = extract_judge_tyeq te3
      in
        (#1 jte1, CIte (#2 jte1, #2 jte2, #2 jte3), CIte (#3 jte1, #3 jte2, #3 jte3))
      end

    fun as_TyEqBinOp opr te1 te2 =
      let
        val jte1 = extract_judge_tyeq te1
        val jte2 = extract_judge_tyeq te2
      in
        (#1 jte1, CBinOp (opr, #2 jte1, #2 jte2), CBinOp (opr, #3 jte1, #3 jte2))
      end

    fun as_TyApp ty1 ty2 =
      let
        val jty1 = extract_judge_typing ty1
        val jty2 = extract_judge_typing ty2
        val (t1, i, t2) = extract_c_arrow (#3 jty1)
      in
        (#1 jty1, EApp (#2 jty1, #2 jty2), t2, Tadd (Tadd (Tadd (#4 jty1, #4 jty2), T1), i))
      end

    fun as_TyAbs kd ty =
      let
        val jkd = extract_judge_kinding kd
        val jty = extract_judge_typing ty
      in
        ((#1 jkd, tl o snd $ #1 jty), EAbs (#2 jty), CArrow (#2 jkd, #4 jty, #3 jty), T0)
      end

    fun as_TySub ty te pr =
      let
        val jty = extract_judge_typing ty
        val jte = extract_judge_tyeq te
        val jpr = extract_judge_proping pr
        val (_, i1, i2) = extract_p_bin_pred (#2 jpr)
      in
        (#1 jty, #2 jty, #3 jte, i2)
      end

    fun as_TyWrite ty1 ty2 =
      let
        val jty1 = extract_judge_typing ty1
        val jty2 = extract_judge_typing ty2
      in
        (#1 jty1, EWrite (#2 jty1, #2 jty2), CTypeUnit, Tadd (#4 jty1, #4 jty2))
      end

    fun as_TyRead ty =
      let
        val jty = extract_judge_typing ty
        val t = extract_c_ref (#3 jty)
      in
        (#1 jty, ERead (#2 jty), t, #4 jty)
      end

    fun as_TyNew ty =
      let
        val jty = extract_judge_typing ty
      in
        (#1 jty, ENew (#2 jty), CRef (#3 jty), #4 jty)
      end

    fun as_TyCase ty1 ty2 ty3 =
      let
        val jty1 = extract_judge_typing ty1
        val jty2 = extract_judge_typing ty2
        val jty3 = extract_judge_typing ty3
      in
        (#1 jty1, ECase (#2 jty1, #2 jty2, #2 jty3), #3 jty2, Tadd (#4 jty1, Tmax (#4 jty2, #4 jty3)))
      end

    fun as_TyInj inj ty kd =
      let
        val jty = extract_judge_typing ty
        val jkd = extract_judge_kinding kd
      in
        (#1 jty, EInj (inj, #2 jty), case inj of InjInl => CSum (#3 jty, #2 jkd) | InjInr => CSum (#2 jkd, #3 jty), #4 jty)
      end

    fun as_TyProj p ty =
      let
        val jty = extract_judge_typing ty
        val (t1, t2) = extract_c_prod (#3 jty)
      in
        (#1 jty, EProj (p, #2 jty), case p of ProjFst => t1 | ProjSnd => t2, #4 jty)
      end

    fun as_TyPair ty1 ty2 =
      let
        val jty1 = extract_judge_typing ty1
        val jty2 = extract_judge_typing ty2
      in
        (#1 jty1, EPair (#2 jty1, #2 jty2), CProd (#3 jty1, #3 jty2), Tadd (#4 jty1, #4 jty2))
      end

    fun as_TyUnpack ty1 ty2 =
      let
        val jty1 = extract_judge_typing ty1
        val jty2 = extract_judge_typing ty2
      in
        (#1 jty1, EUnpack (#2 jty1, #2 jty2), Action.shift_c_c ~1 0 (#3 jty2), Tadd (#4 jty1, Action.shift_c_c ~1 0 (#4 jty2)))
      end

    fun as_TyPack kd1 kd2 ty =
      let
        val jkd1 = extract_judge_kinding kd1
        val jkd2 = extract_judge_kinding kd2
        val jty = extract_judge_typing ty
      in
        (#1 jty, EPack (#2 jkd2, #2 jty), #2 jkd1, #4 jty)
      end

    fun as_TyUnfold ty =
      let
        val jty = extract_judge_typing ty
        fun unfold_CApps t cs =
          case t of
            CApp (t, c) => unfold_CApps t (c :: cs)
          | _ => (t, cs)
        val (t, cs) = unfold_CApps (#3 jty) []
        val (k, t1) = extract_c_rec t
      in
        (#1 jty, EUnfold (#2 jty), CApps (Action.subst_c_c 0 t t1) cs, #4 jty)
      end

    fun as_TyFold kd ty =
      let
        val jkd = extract_judge_kinding kd
        val jty = extract_judge_typing ty
      in
        (#1 jty, EFold (#2 jty), #2 jkd, #4 jty)
      end

    fun as_TyRec kd ty =
      let
        val jkd = extract_judge_kinding kd
        val jty = extract_judge_typing ty
      in
        ((#1 jkd, tl o snd $ #1 jty), ERec (#2 jty), #3 jty, T0)
      end

    fun as_TyAbsC wk ty =
      let
        val jwk = extract_judge_wfkind wk
        val jty = extract_judge_typing ty
      in
        ((#1 jwk, map (Action.shift_c_c ~1 0) o snd $ #1 jty), EAbsC (#2 jty), CForall (#2 jwk, #3 jty), T0)
      end

    fun as_TyAppC ty kd =
      let
        val jty = extract_judge_typing ty
        val jkd = extract_judge_kinding kd
        val (_, k, t) = extract_c_quan (#3 jty)
      in
        (#1 jty, EAppC (#2 jty, #2 jkd), Action.subst_c_c 0 (#2 jkd) t, #4 jty)
      end

    fun default_transform_proping (pr, down) =
      case pr of
        PrAdmit judge =>
          let
            val (judge, up) = Action.on_pr_leaf (judge, down)
          in
            (PrAdmit judge, combine [up])
          end

    and transform_proping (pr, down) =
      case Action.transformer_proping (pr, down) of
        SOME res => res
      | NONE => default_transform_proping (pr, down)

    and default_transform_kdeq (ke, down) =
      case ke of
        KdEqKType judge =>
          let
            val (judge, up) = Action.on_ke_leaf (judge, down)
          in
            (KdEqKType judge, combine [up])
          end
      | KdEqKArrow (judge, ke1, ke2) =>
          let
            val (ke1, up1) = transform_kdeq (ke1, down)
            val (ke2, up2) = transform_kdeq (ke2, down)
          in
            (KdEqKArrow (as_KdEqKArrow ke1 ke2, ke1, ke2), combine [up1, up2])
          end
      | KdEqBaseSort judge =>
          let
            val (judge, up) = Action.on_ke_leaf (judge, down)
          in
            (KdEqBaseSort judge, combine [up])
          end
      | KdEqSubset (judge, ke, pr) =>
          let
            val (ke, up1) = transform_kdeq (ke, down)
            val jke = extract_judge_kdeq ke
            val (pr, up2) = transform_proping (pr, Action.add_kind (#2 jke, down))
          in
            (KdEqSubset (as_KdEqKSubset ke pr, ke, pr), combine [up1, up2])
          end

    and transform_kdeq (ke, down) =
      case Action.transformer_kdeq (transform_kdeq, transform_proping) (ke, down) of
        SOME res => res
      | NONE => default_transform_kdeq (ke, down)

    and default_transform_kinding (kd, down) =
      case kd of
        KdVar judge =>
          let
            val (judge, up) = Action.on_kd_leaf (judge, down)
          in
            (KdVar judge, combine [up])
          end
      | KdConst judge =>
          let
            val (judge, up) = Action.on_kd_leaf (judge, down)
          in
            (KdConst judge, combine [up])
          end
      | KdBinOp (judge, kd1, kd2) =>
          let
            val (kd1, up1) = transform_kinding (kd1, down)
            val (kd2, up2) = transform_kinding (kd2, down)
            val (opr, _, _) = extract_c_bin_op (#2 judge)
          in
            (KdBinOp (as_KdBinOp opr kd1 kd2, kd1, kd2), combine [up1, up2])
          end
      | KdIte (judge, kd1, kd2, kd3) =>
          let
            val (kd1, up1) = transform_kinding (kd1, down)
            val (kd2, up2) = transform_kinding (kd2, down)
            val (kd3, up3) = transform_kinding (kd3, down)
          in
            (KdIte (as_KdIte kd1 kd2 kd3, kd1, kd2, kd3), combine [up1, up2, up3])
          end
      | KdArrow (judge, kd1, kd2, kd3) =>
          let
            val (kd1, up1) = transform_kinding (kd1, down)
            val (kd2, up2) = transform_kinding (kd2, down)
            val (kd3, up3) = transform_kinding (kd3, down)
          in
            (KdArrow (as_KdArrow kd1 kd2 kd3, kd1, kd2, kd3), combine [up1, up2, up3])
          end
      | KdAbs (judge, wk, kd) =>
          let
            val (wk, up1) = transform_wfkind (wk, down)
            val jwk = extract_judge_wfkind wk
            val (kd, up2) = transform_kinding (kd, Action.add_kind (#2 jwk, down))
          in
            (KdAbs (as_KdAbs wk kd, wk, kd), combine [up1, up2])
          end
      | KdApp (judge, kd1, kd2) =>
          let
            val (kd1, up1) = transform_kinding (kd1, down)
            val (kd2, up2) = transform_kinding (kd2, down)
          in
            (KdApp (as_KdApp kd1 kd2, kd1, kd2), combine [up1, up2])
          end
      | KdTimeAbs (judge, kd) =>
          let
            val (kd, up1) = transform_kinding (kd, Action.add_kind (KNat, down))
          in
            (KdTimeAbs (as_KdTimeAbs kd, kd), combine [up1])
          end
      | KdTimeApp (judge, kd1, kd2) =>
          let
            val (kd1, up1) = transform_kinding (kd1, down)
            val (kd2, up2) = transform_kinding (kd2, down)
          in
            (KdTimeApp (as_KdTimeApp kd1 kd2, kd1, kd2), combine [up1, up2])
          end
      | KdQuan (judge, wk, kd) =>
          let
            val (wk, up1) = transform_wfkind (wk, down)
            val jwk = extract_judge_wfkind wk
            val (kd, up2) = transform_kinding (kd, Action.add_kind (#2 jwk, down))
            val (q, _, _) = extract_c_quan (#2 judge)
          in
            (KdQuan (as_KdQuan q wk kd, wk, kd), combine [up1, up2])
          end
      | KdRec (judge, wk, kd) =>
          let
            val (wk, up1) = transform_wfkind (wk, down)
            val jwk = extract_judge_wfkind wk
            val (kd, up2) = transform_kinding (kd, Action.add_kind (#2 jwk, down))
          in
            (KdRec (as_KdRec wk kd, wk, kd), combine [up1, up2])
          end
      | KdRef (judge, kd) =>
          let
            val (kd, up1) = transform_kinding (kd, down)
          in
            (KdRef (as_KdRef kd, kd), combine [up1])
          end
      | KdEq (judge, kd, ke) =>
          let
            val (kd, up1) = transform_kinding (kd, down)
            val (ke, up2) = transform_kdeq (ke, down)
          in
            (KdEq (as_KdEq kd ke, kd, ke), combine [up1, up2])
          end

    and transform_kinding (kd, down) =
      case Action.transformer_kinding (transform_kinding, transform_wfkind, transform_kdeq) (kd, down) of
        SOME res => res
      | NONE => default_transform_kinding (kd, down)

    and default_transform_wfkind (wk, down) =
      case wk of
        WfKdType judge =>
          let
            val (judge, up) = Action.on_wk_leaf (judge, down)
          in
            (WfKdType judge, combine [up])
          end
      | WfKdArrow (judge, wk1, wk2) =>
          let
            val (wk1, up1) = transform_wfkind (wk1, down)
            val (wk2, up2) = transform_wfkind (wk2, down)
          in
            (WfKdArrow (as_WfKdArrow wk1 wk2, wk1, wk2), combine [up1, up2])
          end
      | WfKdBaseSort judge =>
          let
            val (judge, up) = Action.on_wk_leaf (judge, down)
          in
            (WfKdBaseSort judge, combine [up])
          end
      | WfKdSubset (judge, wk, wp) =>
          let
            val (wk, up1) = transform_wfkind (wk, down)
            val jwk = extract_judge_wfkind wk
            val (wp, up2) = transform_wfprop (wp, Action.add_kind (#2 jwk, down))
          in
            (WfKdSubset (as_WfKdSubset wk wp, wk, wp), combine [up1, up2])
          end

    and transform_wfkind (wk, down) =
      case Action.transformer_wfkind (transform_wfkind, transform_wfprop) (wk, down) of
        SOME res => res
      | NONE => default_transform_wfkind (wk, down)

    and default_transform_wfprop (wp, down) =
      case wp of
        WfPropTrue judge =>
          let
            val (judge, up) = Action.on_wp_leaf (judge, down)
          in
            (WfPropTrue judge, combine [up])
          end
      | WfPropFalse judge =>
          let
            val (judge, up) = Action.on_wp_leaf (judge, down)
          in
            (WfPropFalse judge, combine [up])
          end
      | WfPropBinConn (judge, wp1, wp2) =>
          let
            val (wp1, up1) = transform_wfprop (wp1, down)
            val (wp2, up2) = transform_wfprop (wp2, down)
            val (opr, _, _) = extract_p_bin_conn (#2 judge)
          in
            (WfPropBinConn (as_WfPropBinConn opr wp1 wp2, wp1, wp2), combine [up1, up2])
          end
      | WfPropNot (judge, wp) =>
          let
            val (wp, up1) = transform_wfprop (wp, down)
          in
            (WfPropNot (as_WfPropNot wp, wp), combine [up1])
          end
      | WfPropBinPred (judge, kd1, kd2) =>
          let
            val (kd1, up1) = transform_kinding (kd1, down)
            val (kd2, up2) = transform_kinding (kd2, down)
            val (opr, _, _) = extract_p_bin_pred (#2 judge)
          in
            (WfPropBinPred (as_WfPropBinPred opr kd1 kd2, kd1, kd2), combine [up1, up2])
          end
      | WfPropQuan (judge, wp) =>
          let
            val (q, b, _) = extract_p_quan (#2 judge)
            val (wp, up1) = transform_wfprop (wp, Action.add_kind (KBaseSort b, down))
          in
            (WfPropQuan (as_WfPropQuan q b wp, wp), combine [up1])
          end

    and transform_wfprop (wp, down) =
      case Action.transformer_wfprop (transform_wfprop, transform_kinding) (wp, down) of
        SOME res => res
      | NONE => default_transform_wfprop (wp, down)

    and default_transform_tyeq (te, down) =
      case te of
        TyEqVar judge =>
          let
            val (judge, up) = Action.on_te_leaf (judge, down)
          in
            (TyEqVar judge, combine [up])
          end
      | TyEqConst judge =>
          let
            val (judge, up) = Action.on_te_leaf (judge, down)
          in
            (TyEqConst judge, combine [up])
          end
      | TyEqBinOp (judge, te1, te2) =>
          let
            val (te1, up1) = transform_tyeq (te1, down)
            val (te2, up2) = transform_tyeq (te2, down)
            val (opr, _, _) = extract_c_bin_op (#2 judge)
          in
            (TyEqBinOp (as_TyEqBinOp opr te1 te2, te1, te2), combine [up1, up2])
          end
      | TyEqIte (judge, te1, te2, te3) =>
          let
            val (te1, up1) = transform_tyeq (te1, down)
            val (te2, up2) = transform_tyeq (te2, down)
            val (te3, up3) = transform_tyeq (te3, down)
          in
            (TyEqIte (as_TyEqIte te1 te2 te3, te1, te2, te3), combine [up1, up2, up3])
          end
      | TyEqArrow (judge, te1, pr, te2) =>
          let
            val (te1, up1) = transform_tyeq (te1, down)
            val (pr, up2) = transform_proping (pr, down)
            val (te2, up3) = transform_tyeq (te2, down)
          in
            (TyEqArrow (as_TyEqArrow te1 pr te2, te1, pr, te2), combine [up1, up2, up3])
          end
      | TyEqApp (judge, te1, te2) =>
          let
            val (te1, up1) = transform_tyeq (te1, down)
            val (te2, up2) = transform_tyeq (te2, down)
          in
            (TyEqApp (as_TyEqApp te1 te2, te1, te2), combine [up1, up2])
          end
      | TyEqTimeApp (judge, te1, te2) =>
          let
            val (te1, up1) = transform_tyeq (te1, down)
            val (te2, up2) = transform_tyeq (te2, down)
            val (arity, _, _) = extract_c_time_app (#2 judge)
          in
            (TyEqTimeApp (as_TyEqTimeApp arity te1 te2, te1, te2), combine [up1, up2])
          end
      | TyEqBeta (judge, te1, te2, te3) =>
          let
            val (te1, up1) = transform_tyeq (te1, down)
            val (te2, up2) = transform_tyeq (te2, down)
            val (te3, up3) = transform_tyeq (te3, down)
          in
            (TyEqBeta (as_TyEqBeta te1 te2 te3, te1, te2, te3), combine [up1, up2, up3])
          end
      | TyEqBetaRev (judge, te1, te2, te3) =>
          let
            val (te1, up1) = transform_tyeq (te1, down)
            val (te2, up2) = transform_tyeq (te2, down)
            val (te3, up3) = transform_tyeq (te3, down)
          in
            (TyEqBetaRev (as_TyEqBetaRev te1 te2 te3, te1, te2, te3), combine [up1, up2, up3])
          end
      | TyEqQuan (judge, ke, te) =>
          let
            val (ke, up1) = transform_kdeq (ke, down)
            val jke = extract_judge_kdeq ke
            val (te, up2) = transform_tyeq (te, Action.add_kind (#2 jke, down))
            val (q, _, _) = extract_c_quan (#2 judge)
          in
            (TyEqQuan (as_TyEqQuan q ke te, ke, te), combine [up1, up2])
          end
      | TyEqRec (judge, ke, te) =>
          let
            val (ke, up1) = transform_kdeq (ke, down)
            val jke = extract_judge_kdeq ke
            val (te, up2) = transform_tyeq (te, Action.add_kind (#2 jke, down))
          in
            (TyEqRec (as_TyEqRec ke te, ke, te), combine [up1, up2])
          end
      | TyEqRef (judge, te) =>
          let
            val (te, up1) = transform_tyeq (te, down)
          in
            (TyEqRef (as_TyEqRef te, te), combine [up1])
          end
      | TyEqAbs judge =>
          let
            val (judge, up) = Action.on_te_leaf (judge, down)
          in
            (TyEqAbs judge, combine [up])
          end
      | TyEqTimeAbs judge =>
          let
            val (judge, up) = Action.on_te_leaf (judge, down)
          in
            (TyEqTimeAbs judge, combine [up])
          end

    and transform_tyeq (te, down) =
      case Action.transformer_tyeq (transform_tyeq, transform_proping, transform_kdeq) (te, down) of
        SOME res => res
      | NONE => default_transform_tyeq (te, down)

    and default_transform_typing (ty, down) =
      case ty of
        TyVar judge =>
          let
            val (judge, up) = Action.on_ty_leaf (judge, down)
          in
            (TyVar judge, combine [up])
          end
      | TyApp (judge, ty1, ty2) =>
          let
            val (ty1, up1) = transform_typing (ty1, down)
            val (ty2, up2) = transform_typing (ty2, down)
          in
            (TyApp (as_TyApp ty1 ty2, ty1, ty2), combine [up1, up2])
          end
      | TyAbs (judge, kd, ty) =>
          let
            val (kd, up1) = transform_kinding (kd, down)
            val jkd = extract_judge_kinding kd
            val (ty, up2) = transform_typing (ty, Action.add_type (#2 jkd, down))
          in
            (TyAbs (as_TyAbs kd ty, kd, ty), combine [up1, up2])
          end
      | TyAppC (judge, ty, kd) =>
          let
            val (ty, up1) = transform_typing (ty, down)
            val (kd, up2) = transform_kinding (kd, down)
          in
            (TyAppC (as_TyAppC ty kd, ty, kd), combine [up1, up2])
          end
      | TyAbsC (judge, wk, ty) =>
          let
            val (wk, up1) = transform_wfkind (wk, down)
            val jwk = extract_judge_wfkind wk
            val (ty, up2) = transform_typing (ty, Action.add_kind (#2 jwk, down))
          in
            (TyAbsC (as_TyAbsC wk ty, wk, ty), combine [up1, up2])
          end
      | TyRec (judge, kd, ty) =>
          let
            val (kd, up1) = transform_kinding (kd, down)
            val jkd = extract_judge_kinding kd
            val (ty, up2) = transform_typing (ty, Action.add_type (#2 jkd, down))
          in
            (TyRec (as_TyRec kd ty, kd, ty), combine [up1, up2])
          end
      | TyFold (judge, kd, ty) =>
          let
            val (kd, up1) = transform_kinding (kd, down)
            val (ty, up2) = transform_typing (ty, down)
          in
            (TyFold (as_TyFold kd ty, kd, ty), combine [up1, up2])
          end
      | TyUnfold (judge, ty) =>
          let
            val (ty, up1) = transform_typing (ty, down)
          in
            (TyUnfold (as_TyUnfold ty, ty), combine [up1])
          end
      | TyPack (judge, kd1, kd2, ty) =>
          let
            val (kd1, up1) = transform_kinding (kd1, down)
            val (kd2, up2) = transform_kinding (kd2, down)
            val (ty, up3) = transform_typing (ty, down)
          in
            (TyPack (as_TyPack kd1 kd2 ty, kd1, kd2, ty), combine [up1, up2, up3])
          end
      | TyUnpack (judge, ty1, ty2) =>
          let
            val (ty1, up1) = transform_typing (ty1, down)
            val jty1 = extract_judge_typing ty1
            val (_, k, t) = extract_c_quan (#3 jty1)
            val (ty2, up2) = transform_typing (ty2, Action.add_type (t, Action.add_kind (k, down)))
          in
            (TyUnpack (as_TyUnpack ty1 ty2, ty1, ty2), combine [up1, up2])
          end
      | TyConst judge =>
          let
            val (judge, up) = Action.on_ty_leaf (judge, down)
          in
            (TyConst judge, combine [up])
          end
      | TyPair (judge, ty1, ty2) =>
          let
            val (ty1, up1) = transform_typing (ty1, down)
            val (ty2, up2) = transform_typing (ty2, down)
          in
            (TyPair (as_TyPair ty1 ty2, ty1, ty2), combine [up1, up2])
          end
      | TyProj (judge, ty) =>
          let
            val (ty, up1) = transform_typing (ty, down)
            val (p, _) = extract_e_proj (#2 judge)
          in
            (TyProj (as_TyProj p ty, ty), combine [up1])
          end
      | TyInj (judge, ty, kd) =>
          let
            val (ty, up1) = transform_typing (ty, down)
            val (kd, up2) = transform_kinding (kd, down)
            val (inj, _) = extract_e_inj (#2 judge)
          in
            (TyInj (as_TyInj inj ty kd, ty, kd), combine [up1, up2])
          end
      | TyCase (judge, ty1, ty2, ty3) =>
          let
            val (ty1, up1) = transform_typing (ty1, down)
            val jty1 = extract_judge_typing ty1
            val (t1, t2) = extract_c_sum (#3 jty1)
            val (ty2, up2) = transform_typing (ty2, Action.add_type (t1, down))
            val (ty3, up3) = transform_typing (ty3, Action.add_type (t2, down))
          in
            (TyCase (as_TyCase ty1 ty2 ty3, ty1, ty2, ty3), combine [up1, up2, up3])
          end
      | TyNew (judge, ty) =>
          let
            val (ty, up1) = transform_typing (ty, down)
          in
            (TyNew (as_TyNew ty, ty), combine [up1])
          end
      | TyRead (judge, ty) =>
          let
            val (ty, up1) = transform_typing (ty, down)
          in
            (TyRead (as_TyRead ty, ty), combine [up1])
          end
      | TyWrite (judge, ty1, ty2) =>
          let
            val (ty1, up1) = transform_typing (ty1, down)
            val (ty2, up2) = transform_typing (ty2, down)
          in
            (TyWrite (as_TyWrite ty1 ty2, ty1, ty2), combine [up1, up2])
          end
      | TySub (judge, ty, te, pr) =>
          let
            val (ty, up1) = transform_typing (ty, down)
            val (te, up2) = transform_tyeq (te, down)
            val (pr, up3) = transform_proping (pr, down)
          in
            (TySub (as_TySub ty te pr, ty, te, pr), combine [up1, up2, up3])
          end

    and transform_typing (ty, down) =
      case Action.transformer_typing (transform_typing, transform_kinding, transform_wfkind, transform_tyeq, transform_proping)
        (ty, down) of
        SOME res => res
      | NONE => default_transform_typing (ty, down)
  end
end
