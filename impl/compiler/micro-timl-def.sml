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
  fun Tadd c1 c2 = CBinOp (CBTimeAdd, c1, c2)
  fun Tminus c1 c2 = CBinOp (CBTimeMinus, c1, c2)

  fun PAnd p1 p2 = PBinConn (PBCAnd, p1, p2)
  fun POr p1 p2 = PBinConn (PBCOr, p1, p2)
  fun PImply p1 p2 = PBinConn (PBCImply, p1, p2)
  fun PIff p1 p2 = PBinConn (PBCIff, p1, p2)

  fun Tmax c1 c2 = CBinOp (CBTimeMax, c1, c2)

  fun CForall k c = CQuan (QuanForall, k, c)
  fun CExists k c = CQuan (QuanExists, k, c)

  val CTypeUnit = CConst CCTypeUnit

  fun CProd c1 c2 = CBinOp (CBTypeProd, c1, c2)
  fun CSum c1 c2 = CBinOp (CBTypeSum, c1, c2)

  fun TLe c1 c2 = PBinPred (PBTimeLe, c1, c2)
  fun TEq c1 c2 = PBinPred (PBTimeEq, c1, c2)

  val CInt = CConst CCTypeInt

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

  fun EProj p e = EUnOp (EUProj p, e)
  fun EInj c e = EUnOp (EUInj c, e)
  fun EFold e = EUnOp (EUFold, e)
  fun EUnfold e = EUnOp (EUUnfold, e)
  fun ENew e = EUnOp (EUNew, e)
  fun ERead e = EUnOp (EURead, e)

  fun EApp e1 e2 = EBinOp (EBApp, e1, e2)
  fun EPair e1 e2 = EBinOp (EBPair, e1, e2)
  fun EWrite e1 e2 = EBinOp (EBWrite, e1, e2)

  type typing_judgement = ctx * expr * cstr * cstr

  datatype value =
    VConst of expr
  | VPair of expr * value * value
  | VInj of expr * value
  | VAbs of expr
  | VAbsC of expr
  | VPack of expr * value
  | VFold of expr * value

  datatype typing =
    TyVar of typing_judgement
  | TyApp of typing_judgement * typing * typing
  | TyAbs of typing_judgement * kinding * typing
  | TyAppC of typing_judgement * typing * kinding
  | TyAbsC of typing_judgement * value * wfkind * typing
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

  fun extract_p_bin_conn (PBinConn a) = a
    | extract_p_bin_conn _ = raise (Impossible "extract_p_bin_conn")

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

    val transformer_proping : proping * down -> (proping * up) option
    val transformer_kdeq : (kdeq * down -> kdeq * up) * (proping * down -> proping * up) -> kdeq * down -> (kdeq * up) option
  end) =
  struct
    open List

    val combine = foldl Action.combiner Action.upward_base

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

    (*and default_transform_kinding (kd, down) =
      case kd of
        KdVar judge =>
          let
            val (judge, up) = on_kd_leaf (judge, down)
          in
            (KdVar judge, combine [up])
          end
      | KdConst judge =>
          let
            val (judge, up) = on_kd_leaf (judge, down)
          in
            (KdConst judge, combine [up])
          end
      | KdBinOp (judge, kd1, kd2) =>
          let
            val (kd1, up1) = transform_kinding (kd1, down)
            val (kd2, up2) = transform_kinding (kd2, down)
          in
            (KdBinOp (?, kd1, kd2), combine [up1, up2])
          end
      | KdIte (judge, kd1, kd2, kd3) =>
          let
            val (kd1, up1) = transform_kinding (kd1, down)
            val (kd2, up2) = transform_kinding (kd2, down)
            val (kd3, up3) = transform_kinding (kd3, down)
          in
            (KdIte (?, kd1, kd2, kd3), combine [up1, up2, up3])
          end
      | KdArrow (judge, kd1, kd2, kd3) =>
          let
            val (kd1, up1) = transform_kinding (kd1, down)
            val (kd2, up2) = transform_kinding (kd2, down)
            val (kd3, up3) = transform_kinding (kd3, down)
          in
            (KdArrow (?, kd1, kd2, kd3), combine [up1, up2, up3])
          end
      | KdAbs (judge, wk, kd) =>
          let
            val (wk, up1) = transform_wfkind (wf, down)
            val (kd, up2) = transform_kinding (kd, Action.add_kind (?, down))
          in
            (KdAbs (?, wk, kd), combine [up1, up2])
          end
      | KdApp (judge, kd1, kd2) =>
          let
            val (kd1, up1) = transform_kinding (kd1, down)
            val (kd2, up2) = transform_kinding (kd2, down)
          in
            (KdApp (?, kd1, kd2), combine [up1, up2])
          end
      | KdTimeAbs (judge, kd) =>
          let
            val (kd, up1) = transform_kinding (kd, Action.add_kind (KNat, down))
          in
            (KdTimeAbs (?, kd), combine [up1])
          end
      | KdTimeApp (judge, kd1, kd2) =>
          let
            val (kd1, up1) = transform_kinding (kd1, down)
            val (kd2, up2) = transform_kinding (kd2, down)
          in
            (KdTimeApp (?, kd1, kd2), combine [up1, up2])
          end
      | KdQuan (judge, wk, kd) =>
          let
            val (wk, up1) = transform_wfkind (wk, down)
            val (kd, up2) = transform_kinding (kd, Action.add_kind (?, down))
          in
            (KdQuan (?, wk, kd), combine [up1, up2])
          end
      | KdRec (judge, wk, kd) =>
          let
            val (wk, up1) = transform_wfkind (wk, down)
            val (kd, up2) = transform_kinding (kd, Action.add_kind (?, down))
          in
            (KdRec (?, wk, kd), combine [up1, up2])
          end
      | KdRef (judge, kd) =>
          let
            val (kd, up1) = transform_kinding (kd, down)
          in
            (KdRef (?, kd), combine [up1])
          end
      | KdEq (judge, kd, ke) =>
          let
            val (kd, up1) = transform_kinding (kd, down)
            val (ke, up2) = transform_kdeq (ke, down)
          in
            (KdEq (?, kd, ke), combine [up1, up2])
          end

    and transform_kinding (kd, down) =
      case Action.transformer_kinding (transform_kinding, transform_wfkind, transform_kdeq) (kd, down) of
        SOME res => res
      | NONE => default_transform_kinding (kd, down)*)
  end
end
