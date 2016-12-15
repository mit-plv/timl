functor CstrGenericTransformerFun(
    structure MicroTiMLDef : SIG_MICRO_TIML_DEF
    structure Action :
              sig
                  type down
                  type up

                  val upward_base : up
                  val combiner : up * up -> up

                  val add_kind : MicroTiMLDef.kind option * down -> down

                  val transformer_cstr : (MicroTiMLDef.cstr * down -> MicroTiMLDef.cstr * up) * (MicroTiMLDef.kind * down -> MicroTiMLDef.kind * up) -> MicroTiMLDef.cstr * down -> (MicroTiMLDef.cstr * up) option
                  val transformer_kind : (MicroTiMLDef.kind * down -> MicroTiMLDef.kind * up) * (MicroTiMLDef.prop * down -> MicroTiMLDef.prop * up) -> MicroTiMLDef.kind * down -> (MicroTiMLDef.kind * up) option
                  val transformer_prop : (MicroTiMLDef.prop * down -> MicroTiMLDef.prop * up) * (MicroTiMLDef.cstr * down -> MicroTiMLDef.cstr * up) -> MicroTiMLDef.prop * down -> (MicroTiMLDef.prop * up) option
              end) : SIG_CSTR_GENERIC_TRANSFORMER =
struct
open List
open Util
infixr 0 $

structure MicroTiMLDef = MicroTiMLDef
open MicroTiMLDef
structure MicroTiMLUtil = MicroTiMLUtilFun(MicroTiMLDef)
open MicroTiMLUtil

open Action

val combine = foldl combiner upward_base

fun default_transform_cstr (c, down) =
  case c of
      CVar x => (CVar x, upward_base)
    | CConst cn =>  (CConst cn, upward_base)
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
          val (i, up1) = transform_cstr (i, add_kind (SOME KTime, down))
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
          val (t, up1) = transform_cstr (t, add_kind (NONE, down))
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
          val (c, up2) = transform_cstr (c, add_kind (SOME k, down))
      in
          (CQuan (q, k, c), combine [up1, up2])
      end
    | CRec (k, t) =>
      let
          val (k, up1) = transform_kind (k, down)
          val (t, up2) = transform_cstr (t, add_kind (SOME k, down))
      in
          (CRec (k, t), combine [up1, up2])
      end
    | CUnOp (opr, c) =>
      let
          val (c, up1) = transform_cstr (c, down)
      in
          (CUnOp (opr, c), combine [up1])
      end
    | CTypeNat c =>
      let
          val (c, up1) = transform_cstr (c, down)
      in
          (CTypeNat c, combine [up1])
      end
    | CTypeArr (c1, c2) =>
      let
          val (c1, up1) = transform_cstr (c1, down)
          val (c2, up2) = transform_cstr (c2, down)
      in
          (CTypeArr (c1, c2), combine [up1, up2])
      end

and transform_cstr (c, down) =
    case transformer_cstr (transform_cstr, transform_kind) (c, down) of
        SOME res => res
      | NONE => default_transform_cstr (c, down)

and default_transform_kind (k, down) =
    case k of
        KType => (KType, upward_base)
      | KArrow (k1, k2) =>
        let
            val (k1, up1) = transform_kind (k1, down)
            val (k2, up2) = transform_kind (k2, down)
        in
            (KArrow (k1, k2), combine [up1, up2])
        end
      | KBaseSort b => (KBaseSort b, upward_base)
      | KSubset (k, p) =>
        let
            val (k, up1) = transform_kind (k, down)
            val (p, up2) = transform_prop (p, add_kind (SOME k, down))
        in
            (KSubset (k, p), combine [up1, up2])
        end

and transform_kind (k, down) =
    case transformer_kind (transform_kind, transform_prop) (k, down) of
        SOME res => res
      | NONE => default_transform_kind (k, down)

and default_transform_prop (p, down) =
    case p of
        PTrue => (PTrue, upward_base)
      | PFalse => (PFalse, upward_base)
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
            val (p, up1) = transform_prop (p, add_kind (SOME (KBaseSort b), down))
        in
            (PQuan (q, b, p), combine [up1])
        end

and transform_prop (p, down) =
    case transformer_prop (transform_prop, transform_cstr) (p, down) of
        SOME res => res
      | NONE => default_transform_prop (p, down)
end

functor ExprGenericTransformerFun(
    structure MicroTiMLDef : SIG_MICRO_TIML_DEF
    structure Action :
              sig
                  type kdown
                  type tdown
                  type down = kdown * tdown
                  type up

                  val upward_base : up
                  val combiner : up * up -> up

                  val add_kind : MicroTiMLDef.kind option * down -> down
                  val add_type : MicroTiMLDef.cstr option * tdown -> tdown

                  val transform_cstr : MicroTiMLDef.cstr * kdown -> MicroTiMLDef.cstr * up

                  val transformer_expr : (MicroTiMLDef.expr * down -> MicroTiMLDef.expr * up) -> MicroTiMLDef.expr * down -> (MicroTiMLDef.expr * up) option
              end) : SIG_EXPR_GENERIC_TRANSFORMER =
struct
open List
open Util
infixr 0 $

structure MicroTiMLDef = MicroTiMLDef
open MicroTiMLDef
structure MicroTiMLUtil = MicroTiMLUtilFun(MicroTiMLDef)
open MicroTiMLUtil

open Action

val combine = foldl combiner upward_base

fun default_transform_expr (e, down as (kdown, tdown)) =
    case e of
        EVar x => (EVar x, upward_base)
      | EConst cn => (EConst cn, upward_base)
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
            val (e1, up2) = transform_expr (e1, (kdown, add_type (NONE, tdown)))
            val (e2, up3) = transform_expr (e2, (kdown, add_type (NONE, tdown)))
        in
            (ECase (e, e1, e2), combine [up1, up2, up3])
        end
      | EAbs e =>
        let
            val (e, up1) = transform_expr (e, (kdown, add_type (NONE, tdown)))
        in
            (EAbs e, combine [up1])
        end
      | ERec e =>
        let
            val (e, up1) = transform_expr (e, (kdown, add_type (NONE, tdown)))
        in
            (ERec e, combine [up1])
        end
      | EAbsC e =>
        let
            val (e, up1) = transform_expr (e, add_kind (NONE, down))
        in
            (EAbsC e, combine [up1])
        end
      | EAppC (e, c) =>
        let
            val (e, up1) = transform_expr (e, down)
            val (c, up2) = transform_cstr (c, kdown)
        in
            (EAppC (e, c), combine [up1, up2])
        end
      | EPack (c, e) =>
        let
            val (c, up1) = transform_cstr (c, kdown)
            val (e, up2) = transform_expr (e, down)
        in
            (EPack (c, e), combine [up1, up2])
        end
      | EUnpack (e1, e2) =>
        let
            val (e1, up1) = transform_expr (e1, down)
            val (e2, up2) = transform_expr (e2, let val (kdown, tdown) = add_kind (NONE, down) in (kdown, add_type (NONE, tdown)) end)
        in
            (EUnpack (e1, e2), combine [up1, up2])
        end
      | EHalt e =>
        let
            val (e, up1) = transform_expr (e, down)
        in
            (EHalt e, combine [up1])
        end
      | ELet (e1, e2) =>
        let
            val (e1, up1) = transform_expr (e1, down)
            val (e2, up2) = transform_expr (e2, (kdown, add_type (NONE, tdown)))
        in
            (ELet (e1, e2), combine [up1, up2])
        end
      | EFix (n, e) => (EFix (n, e), upward_base)
      | ETriOp (opr, e1, e2, e3) =>
        let
            val (e1, up1) = transform_expr (e1, down)
            val (e2, up2) = transform_expr (e2, down)
            val (e3, up3) = transform_expr (e3, down)
        in
            (ETriOp (opr, e1, e2, e3), combine [up1, up2, up3])
        end

and transform_expr (e, down) =
    case transformer_expr transform_expr (e, down) of
        SOME res => res
      | NONE => default_transform_expr (e, down)
end

functor CstrGenericOnlyDownTransformerFun(
    structure MicroTiMLDef : SIG_MICRO_TIML_DEF
    structure Action :
              sig
                  type down

                  val add_kind : MicroTiMLDef.kind option * down -> down

                  val transformer_cstr : (MicroTiMLDef.cstr * down -> MicroTiMLDef.cstr) * (MicroTiMLDef.kind * down -> MicroTiMLDef.kind) -> MicroTiMLDef.cstr * down -> MicroTiMLDef.cstr option
                  val transformer_kind : (MicroTiMLDef.kind * down -> MicroTiMLDef.kind) * (MicroTiMLDef.prop * down -> MicroTiMLDef.prop) -> MicroTiMLDef.kind * down -> MicroTiMLDef.kind option
                  val transformer_prop : (MicroTiMLDef.prop * down -> MicroTiMLDef.prop) * (MicroTiMLDef.cstr * down -> MicroTiMLDef.cstr) -> MicroTiMLDef.prop * down -> MicroTiMLDef.prop option
              end) : SIG_CSTR_GENERIC_ONLY_DOWN_TRANSFORMER =
struct
open List
open Util
infixr 0 $

structure MicroTiMLDef = MicroTiMLDef
open MicroTiMLDef

open Action

structure Transformer = CstrGenericTransformerFun(
    structure MicroTiMLDef = MicroTiMLDef
    structure Action =
    struct
    type down = down
    type up = unit

    val upward_base = ()
    fun combiner ((), ()) = ()

    val add_kind = add_kind

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
    end)

val transform_cstr = fst o Transformer.transform_cstr
val transform_kind = fst o Transformer.transform_kind
val transform_prop = fst o Transformer.transform_prop
end

functor ExprGenericOnlyDownTransformerFun(
    structure MicroTiMLDef : SIG_MICRO_TIML_DEF
    structure Action :
              sig
                  type kdown
                  type tdown
                  type down = kdown * tdown

                  val add_kind : MicroTiMLDef.kind option * down -> down
                  val add_type : MicroTiMLDef.cstr option * tdown -> tdown

                  val transform_cstr : MicroTiMLDef.cstr * kdown -> MicroTiMLDef.cstr

                  val transformer_expr : (MicroTiMLDef.expr * down -> MicroTiMLDef.expr) -> MicroTiMLDef.expr * down -> MicroTiMLDef.expr option
              end) : SIG_EXPR_GENERIC_ONLY_DOWN_TRANSFORMER =
struct
open List
open Util
infixr 0 $

structure MicroTiMLDef = MicroTiMLDef
open MicroTiMLDef

open Action

structure Transformer = ExprGenericTransformerFun(
    structure MicroTiMLDef = MicroTiMLDef
    structure Action =
    struct
    type kdown = kdown
    type tdown = tdown
    type down = down
    type up = unit

    val upward_base = ()
    fun combiner ((), ()) = ()

    val add_kind = add_kind
    val add_type = add_type

    val transform_cstr = (fn c => (c, ())) o transform_cstr

    fun transformer_expr on_expr =
      let
          val on_expr_no_up = fst o on_expr
      in
          Option.map (fn e => (e, ())) o Action.transformer_expr on_expr_no_up
      end
    end)

val transform_expr = fst o Transformer.transform_expr
end

functor AstTransformersFun(MicroTiMLDef : SIG_MICRO_TIML_DEF) : SIG_AST_TRANSFORMERS =
struct
open List
open Util
infixr 0 $

open MicroTiMLDef
structure MicroTiMLUtil = MicroTiMLUtilFun(MicroTiMLDef)
open MicroTiMLUtil

structure PlainPrinter =
struct
fun str_cstr c =
  case c of
      CVar x => "$" ^ str_int x
    | CConst cn => str_cstr_const cn
    | CBinOp (opr, c1, c2) => "(" ^ str_cstr c1 ^ " " ^ str_cstr_bin_op opr ^ " " ^ str_cstr c2 ^ ")"
    | CIte (i1, i2, i3) => "(" ^ str_cstr i1 ^ " ? " ^ str_cstr i2 ^ " : " ^ str_cstr i3 ^ ")"
    | CTimeAbs i => "(fn => " ^ str_cstr i ^ ")"
    | CTimeApp (arity, c1, c2) => "(" ^ str_cstr c1 ^ " " ^ str_cstr c2 ^ ")"
    | CArrow (t1, i, t2) => "(" ^ str_cstr t1 ^ " -- " ^ str_cstr i ^ " --> " ^ str_cstr t2 ^ ")"
    | CAbs t => "(fn => " ^ str_cstr t ^ ")"
    | CApp (c1, c2) => "(" ^ str_cstr c1 ^ " " ^ str_cstr c2 ^ ")"
    | CQuan (q, k, c) => "(" ^ str_quan q ^ " " ^ str_kind k ^ " : " ^ str_cstr c ^ ")"
    | CRec (k, t) => "REC_TYPE" (* "(rec " ^ str_kind k ^ " => " ^ str_cstr t ^ ")" *)
    | CUnOp (opr, c) => "(" ^ str_cstr_un_op opr ^ " " ^ str_cstr c ^ ")"
    | CTypeNat c => "nat(" ^ str_cstr c ^ ")"
    | CTypeArr (c1, c2) => "arr(" ^ str_cstr c1 ^ ", " ^ str_cstr c2 ^ ")"

and str_kind k =
  case k of
      KType => "*"
    | KArrow (k1, k2) => "(" ^ str_kind k1 ^ " => " ^ str_kind k2 ^ ")"
    | KBaseSort b => str_sort b
    | KSubset (k, p) => "{" ^ str_kind k ^ " | " ^ str_prop p ^ "}"

and str_prop p =
    case p of
        PTrue => "true"
      | PFalse => "false"
      | PBinConn (opr, p1, p2) => "(" ^ str_prop p1 ^ " " ^ str_prop_bin_conn opr ^ " " ^ str_prop p2 ^ ")"
      | PNot p => "(not" ^ str_prop p ^ ")"
      | PBinPred (opr, i1, i2) => "(" ^ str_cstr i1 ^ " " ^ str_prop_bin_pred opr ^ " " ^ str_cstr i2 ^ ")"
      | PQuan (q, b, p) => "(" ^ str_quan q ^ " " ^ str_sort b ^ " : " ^ str_prop p ^ ")"

fun str_expr e =
  case e of
      EVar x => "&" ^ str_int x
    | EConst cn => str_expr_const cn
    | EUnOp (opr, e) => "(" ^ str_expr_un_op opr ^ " " ^ str_expr e ^ ")"
    | EBinOp (opr, e1, e2) => "(" ^ str_expr e1 ^ " " ^ str_expr_bin_op opr ^ " " ^ str_expr e2 ^ ")"
    | ECase (e, e1, e2) => "(case " ^ str_expr e ^ " " ^ str_expr e1 ^ " " ^ str_expr e2 ^ ")"
    | EAbs e => "(fn => " ^ str_expr e ^ ")"
    | ERec e => "(rec => " ^ str_expr e ^ ")"
    | EAbsC e => "(idxfn => " ^ str_expr e ^ ")"
    | EAppC (e, c) => str_expr e ^ "[" ^ str_cstr c ^ "]"
    | EPack (c, e) => "<" ^ (* str_cstr c *) "_" ^ " | " ^ str_expr e ^ ">"
    | EUnpack (e1, e2) => "(unpack " ^ str_expr e1 ^ " in " ^ str_expr e2 ^ ")"
    | EHalt e => "(halt " ^ str_expr e ^ ")"
    | ELet (e1, e2) => "(let = " ^ str_expr e1 ^ " in " ^ str_expr e2 ^ ")"
    | EFix (n, e) => "(fix [" ^ str_int n ^ "] => " ^ str_expr e ^ ")"
    | ETriOp (opr, e1, e2, e3) => "(" ^ str_expr_tri_op opr ^ " " ^ str_expr e1 ^ " " ^ str_expr e2 ^ " " ^ str_expr e3 ^ ")"
end

structure ShiftCstr =
struct
structure CstrHelper = CstrGenericOnlyDownTransformerFun(
    structure MicroTiMLDef = MicroTiMLDef
    structure Action =
    struct
    type down = int * int

    fun add_kind (_, (d, ctx)) = (d, ctx + 1)

    fun transformer_cstr (on_cstr, on_kind) (c, (d, ctx)) =
      case c of
          CVar x => SOME (if x >= ctx then CVar (x + d) else CVar x)
        | _ => NONE

    fun transformer_kind _ _ = NONE
    fun transformer_prop _ _ = NONE
    end)

structure ExprHelper = ExprGenericOnlyDownTransformerFun(
    structure MicroTiMLDef = MicroTiMLDef
    structure Action =
    struct
    type kdown = int * int
    type tdown = unit
    type down = kdown * tdown

    fun add_kind (_, ((d, ctx), ())) = ((d, ctx + 1), ())
    fun add_type (_, ()) = ()

    val transform_cstr = CstrHelper.transform_cstr

    fun transformer_expr _ _ = NONE
    end)

fun shift_c_c d ctx c = CstrHelper.transform_cstr (c, (d, ctx))
fun shift_c_k d ctx k = CstrHelper.transform_kind (k, (d, ctx))
fun shift_c_p d ctx p = CstrHelper.transform_prop (p, (d, ctx))
fun shift_c_e d ctx e = ExprHelper.transform_expr (e, ((d, ctx), ()))

val shift0_c_c = shift_c_c 1 0
val shift0_c_k = shift_c_k 1 0
val shift0_c_p = shift_c_p 1 0
val shift0_c_e = shift_c_e 1 0
end

structure ShiftExpr =
struct
structure ExprHelper = ExprGenericOnlyDownTransformerFun(
    structure MicroTiMLDef = MicroTiMLDef
    structure Action =
    struct
    type kdown = unit
    type tdown = int * int
    type down = kdown * tdown

    fun add_kind (_, ((), (d, ctx))) = ((), (d, ctx))
    fun add_type (_, (d, ctx)) = (d, ctx + 1)

    fun transform_cstr (c, kdown) = c

    fun transformer_expr on_expr (e, ((), (d, ctx))) =
      case e of
          EVar x => SOME (if x >= ctx then EVar (x + d) else EVar x)
        | _ => NONE
    end)

fun shift_e_e d ctx e = ExprHelper.transform_expr (e, ((), (d, ctx)))

val shift0_e_e = shift_e_e 1 0
end

structure SubstCstr =
struct
open ShiftCstr

structure CstrHelper = CstrGenericOnlyDownTransformerFun(
    structure MicroTiMLDef = MicroTiMLDef
    structure Action =
    struct
    type down = cstr * int

    fun add_kind (_, (to, who)) = (shift0_c_c to, who + 1)

    fun transformer_cstr (on_cstr, on_kind) (c, (to, who)) =
      case c of
          CVar x => SOME (if x = who then to else if x < who then CVar x else CVar (x - 1))
        | _ => NONE

    fun transformer_kind _ _ = NONE
    fun transformer_prop _ _ = NONE
    end)

structure ExprHelper = ExprGenericOnlyDownTransformerFun(
    structure MicroTiMLDef = MicroTiMLDef
    structure Action =
    struct
    type kdown = cstr * int
    type tdown = unit
    type down = kdown * tdown

    fun add_kind (_, ((to, who), ())) = ((shift0_c_c to, who + 1), ())
    fun add_type (_, ()) = ()

    val transform_cstr = CstrHelper.transform_cstr

    fun transformer_expr _ _ = NONE
    end)

fun subst_c_c to who c = CstrHelper.transform_cstr (c, (to, who))
fun subst_c_k to who k = CstrHelper.transform_kind (k, (to, who))
fun subst_c_p to who p = CstrHelper.transform_prop (p, (to, who))
fun subst_c_e to who e = ExprHelper.transform_expr (e, ((to, who), ()))

fun subst0_c_c to = subst_c_c to 0
fun subst0_c_k to = subst_c_k to 0
fun subst0_c_p to = subst_c_p to 0
fun subst0_c_e to = subst_c_e to 0
end

structure SubstExpr =
struct
open ShiftCstr
open ShiftExpr

structure ExprHelper = ExprGenericOnlyDownTransformerFun(
    structure MicroTiMLDef = MicroTiMLDef
    structure Action =
    struct
    type kdown = unit
    type tdown = expr * int
    type down = kdown * tdown

    fun add_kind (_, ((), (to, who))) = ((), (shift0_c_e to, who))
    fun add_type (_, (to, who)) = (shift0_e_e to, who + 1)

    fun transform_cstr (c, kdown) = c

    fun transformer_expr on_expr (e, ((), (to, who))) =
      case e of
          EVar x => SOME (if x = who then to else if x < who then EVar x else EVar (x - 1))
        | _ => NONE
    end)

fun subst_e_e to who e = ExprHelper.transform_expr (e, ((), (to, who)))

fun subst0_e_e to = subst_e_e to 0
end

structure DirectSubstCstr =
struct
open ShiftCstr

structure CstrHelper = CstrGenericOnlyDownTransformerFun(
    structure MicroTiMLDef = MicroTiMLDef
    structure Action =
    struct
    type down = cstr * int

    fun add_kind (_, (to, who)) = (shift0_c_c to, who + 1)

    fun transformer_cstr (on_cstr, on_kind) (c, (to, who)) =
      case c of
          CVar x => SOME (if x = who then to else CVar x)
        | _ => NONE

    fun transformer_kind _ _ = NONE
    fun transformer_prop _ _ = NONE
    end)

structure ExprHelper = ExprGenericOnlyDownTransformerFun(
    structure MicroTiMLDef = MicroTiMLDef
    structure Action =
    struct
    type kdown = cstr * int
    type tdown = unit
    type down = kdown *  tdown

    fun add_kind (_, ((to, who), ())) = ((shift0_c_c to, who + 1), ())
    fun add_type (_, ()) = ()

    val transform_cstr = CstrHelper.transform_cstr

    fun transformer_expr _ _ = NONE
    end)

fun dsubst_c_c to who c = CstrHelper.transform_cstr (c, (to, who))
fun dsubst_c_k to who k = CstrHelper.transform_kind (k, (to, who))
fun dsubst_c_p to who p = CstrHelper.transform_prop (p, (to, who))
fun dsubst_c_e to who e = ExprHelper.transform_expr (e, ((to, who), ()))

fun dsubst0_c_c to = dsubst_c_c to 0
fun dsubst0_c_k to = dsubst_c_k to 0
fun dsubst0_c_p to = dsubst_c_p to 0
fun dsubst0_c_e to = dsubst_c_e to 0
end

structure DirectSubstExpr =
struct
structure ExprHelper = ExprGenericOnlyDownTransformerFun(
    structure MicroTiMLDef = MicroTiMLDef
    structure Action =
    struct
    type kdown = unit
    type tdown = expr * int
    type down = kdown * tdown

    open ShiftCstr
    open ShiftExpr

    fun add_kind (_, ((), (to, who))) = ((), (shift0_c_e to, who))
    fun add_type (_, (to, who)) = (shift0_e_e to, who + 1)

    fun transform_cstr (c, kdown) = c

    fun transformer_expr on_expr (e, ((), (to, who))) =
      case e of
          EVar x => SOME (if x = who then to else EVar x)
        | _ => NONE
    end)

fun dsubst_e_e to who e = ExprHelper.transform_expr (e, ((), (to, who)))

fun dsubst0_e_e to = dsubst_e_e to 0
end

structure FVUtil =
struct
fun unique_merge (ls1, ls2) =
  case (ls1, ls2) of
      ([], ls2) => ls2
    | (ls1, []) => ls1
    | (x1 :: s1, x2 :: s2) =>
      if x1 = x2 then
          x1 :: unique_merge (s1, s2)
      else
          if x1 < x2 then
              x1 :: unique_merge (s1, ls2)
          else
              x2 :: unique_merge (ls1, s2)
end

structure FVCstr =
struct
open List
open FVUtil

structure CstrHelper = CstrGenericTransformerFun(
    structure MicroTiMLDef = MicroTiMLDef
    structure Action =
    struct
    type down = int
    type up = int list

    val upward_base = []
    val combiner = unique_merge

    fun add_kind (_, ctx) = ctx + 1

    fun transformer_cstr (on_cstr, on_kind) (c, ctx) =
      case c of
          CVar x => SOME (c, if x >= ctx then [x - ctx] else [])
        | _ => NONE

    fun transformer_kind _ _ = NONE
    fun transformer_prop _ _ = NONE
    end)

structure ExprHelper = ExprGenericTransformerFun(
    structure MicroTiMLDef = MicroTiMLDef
    structure Action =
    struct
    type kdown = int
    type tdown = unit
    type down = kdown * tdown
    type up = int list

    val upward_base = []
    val combiner = unique_merge

    fun add_kind (_, (ctx, ())) = (ctx + 1, ())
    fun add_type (_, ()) = ()

    val transform_cstr = CstrHelper.transform_cstr

    fun transformer_expr _ _ = NONE
    end)

fun free_vars_c_c d c = #2 (CstrHelper.transform_cstr (c, d))
fun free_vars_c_k d k = #2 (CstrHelper.transform_kind (k, d))
fun free_vars_c_p d p = #2 (CstrHelper.transform_prop (p, d))
fun free_vars_c_e d e = #2 (ExprHelper.transform_expr (e, (d, ())))

val free_vars0_c_c = free_vars_c_c 0
val free_vars0_c_k = free_vars_c_k 0
val free_vars0_c_p = free_vars_c_p 0
val free_vars0_c_e = free_vars_c_e 0
end

structure FVExpr =
struct
open List
open FVUtil

structure ExprHelper = ExprGenericTransformerFun(
    structure MicroTiMLDef = MicroTiMLDef
    structure Action =
    struct
    type kdown = unit
    type tdown = int
    type down = kdown * tdown
    type up = int list

    val upward_base = []
    val combiner = unique_merge

    fun add_kind (_, ((), ctx)) = ((), ctx)
    fun add_type (_, ctx) = ctx + 1

    fun transform_cstr (c, kdown) = (c, [])

    fun transformer_expr on_expr (e, ((), ctx)) =
      case e of
          EVar x => SOME (EVar x, if x >= ctx then [x - ctx] else [])
        | _ => NONE
    end)

fun free_vars_e_e d e = #2 (ExprHelper.transform_expr (e, ((), d)))

val free_vars0_e_e = free_vars_e_e 0
end
end
