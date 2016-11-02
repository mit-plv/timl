functor AstTransformersFun(MicroTiMLDef : SIG_MICRO_TIML_DEF) : SIG_AST_TRANSFORMERS =
struct
open Util
infixr 0 $

structure MicroTiMLDef = MicroTiMLDef
open MicroTiMLDef
structure MicroTiMLUtil = MicroTiMLUtilFun(MicroTiMLDef)
open MicroTiMLUtil

functor AstGenericTransformer(
    Action:
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
    | CUnOp (opr, c) =>
      let
          val (c, up1) = transform_cstr (c, down)
      in
          (CUnOp (opr, c), combine [up1])
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
      | EHalt e =>
        let
            val (e, up1) = transform_expr (e, down)
        in
            (EHalt e, combine [up1])
        end
      | ELet (e1, e2) =>
        let
            val (e1, up1) = transform_expr (e1, down)
            val (e2, up2) = transform_expr (e2, Action.add_type (NONE, down))
        in
            (ELet (e1, e2), combine [up1, up2])
        end
      | EFix (n, e) => raise (Impossible "EFix transformer not implemented")

and transform_expr (e, down) =
    case Action.transformer_expr (transform_expr, transform_cstr) (e, down) of
        SOME res => res
      | NONE => default_transform_expr (e, down)
end

functor AstGenericOnlyDownTransformer(
    Action:
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

functor AstGenericOnlyUpTransformer(
    Action:
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

structure PlainPrinter =
struct
structure Helper = AstGenericOnlyUpTransformer(
    struct
    type up = string

    val upward_base = ""
    fun combiner (up1, up2) = up1 ^ up2

    fun transformer_cstr (on_cstr, on_kind) c =
      let
          val str_cstr = snd o on_cstr
          val str_kind = snd o on_kind
          val res =
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
                | CRec (k, t) => "(rec " ^ str_kind k ^ " => " ^ str_cstr t ^ ")"
                | CRef t => "(ref " ^ str_cstr t ^ ")"
                | CUnOp (opr, c) => "(" ^ str_cstr_un_op opr ^ " " ^ str_cstr c ^ ")"
      in
          SOME (c, res)
      end

    fun transformer_kind (on_kind, on_prop) k =
      let
          val str_kind = snd o on_kind
          val str_prop = snd o on_prop
          val res =
              case k of
                  KType => "*"
                | KArrow (k1, k2) => "(" ^ str_kind k1 ^ " => " ^ str_kind k2 ^ ")"
                | KBaseSort b => str_sort b
                | KSubset (k, p) => "{" ^ str_kind k ^ " | " ^ str_prop p ^ "}"
      in
          SOME (k, res)
      end

    fun transformer_prop (on_prop, on_cstr) p =
      let
          val str_prop = snd o on_prop
          val str_cstr = snd o on_cstr
          val res =
              case p of
                  PTrue => "true"
                | PFalse => "false"
                | PBinConn (opr, p1, p2) => "(" ^ str_prop p1 ^ " " ^ str_prop_bin_conn opr ^ " " ^ str_prop p2 ^ ")"
                | PNot p => "(not" ^ str_prop p ^ ")"
                | PBinPred (opr, i1, i2) => "(" ^ str_cstr i1 ^ " " ^ str_prop_bin_pred opr ^ " " ^ str_cstr i2 ^ ")"
                | PQuan (q, b, p) => "(" ^ str_quan q ^ " " ^ str_sort b ^ " : " ^ str_prop p ^ ")"
      in
          SOME (p, res)
      end

    fun transformer_expr (on_expr, on_cstr) e =
      let
          val str_expr = snd o on_expr
          val str_cstr = snd o on_cstr
          val res =
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
                | EPack (c, e) => "<" ^ str_cstr c ^ " | " ^ str_expr e ^ ">"
                | EUnpack (e1, e2) => "(unpack " ^ str_expr e1 ^ " in " ^ str_expr e2 ^ ")"
                | EHalt e => "(halt " ^ str_expr e ^ ")"
                | ELet (e1, e2) => "(let = " ^ str_expr e1 ^ " in " ^ str_expr e2 ^ ")"
                | EFix (n, e) => "(fix [" ^ str_int n ^ "] => " ^ str_expr e ^ ")"
      in
          SOME (e, res)
      end
    end)

val str_cstr = snd o Helper.transform_cstr
val str_kind = snd o Helper.transform_kind
val str_prop = snd o Helper.transform_prop
val str_expr = snd o Helper.transform_expr
end

structure ShiftCstr =
struct
structure Helper = AstGenericOnlyDownTransformer(
    struct
    type down = int * int

    fun add_kind (_, (d, ctx)) = (d, ctx + 1)
    fun add_type (_, (d, ctx)) = (d, ctx)

    fun transformer_cstr (on_cstr, on_kind) (c, (d, ctx)) =
      case c of
          CVar x => SOME (if x >= ctx then CVar (x + d) else CVar x)
        | _ => NONE

    fun transformer_expr (on_expr, on_cstr) (e, (d, ctx)) =
      case e of
          EFix (n, e) => SOME (EFix (n, e))
        | _ => NONE

    fun transformer_kind _ _ = NONE
    fun transformer_prop _ _ = NONE
    end)

fun shift_c_c d ctx c = Helper.transform_cstr (c, (d, ctx))
fun shift_c_k d ctx k = Helper.transform_kind (k, (d, ctx))
fun shift_c_p d ctx p = Helper.transform_prop (p, (d, ctx))
fun shift_c_e d ctx e = Helper.transform_expr (e, (d, ctx))

val shift0_c_c = shift_c_c 1 0
val shift0_c_k = shift_c_k 1 0
val shift0_c_p = shift_c_p 1 0
val shift0_c_e = shift_c_e 1 0
end

structure ShiftExpr =
struct
structure Helper = AstGenericOnlyDownTransformer(
    struct
    type down = int * int

    fun add_kind (_, (d, ctx)) = (d, ctx)
    fun add_type (_, (d, ctx)) = (d, ctx + 1)

    fun transformer_expr (on_expr, on_cstr) (e, (d, ctx)) =
      case e of
          EVar x => SOME (if x >= ctx then EVar (x + d) else EVar x)
        | EFix (n, e) => SOME (EFix (n, e))
        | _ => NONE

    fun transformer_cstr _ _ = NONE
    fun transformer_kind _ _ = NONE
    fun transformer_prop _ _ = NONE
    end)

fun shift_e_e d ctx e = Helper.transform_expr (e, (d, ctx))

val shift0_e_e = shift_e_e 1 0
end

structure SubstCstr =
struct
structure Helper = AstGenericOnlyDownTransformer(
    struct
    type down = cstr * int

    open ShiftCstr

    fun add_kind (_, (to, who)) = (shift0_c_c to, who + 1)
    fun add_type (_, (to, who)) = (to, who)

    fun transformer_cstr (on_cstr, on_kind) (c, (to, who)) =
      case c of
          CVar x => SOME (if x = who then to else if x < who then CVar x else CVar (x - 1))
        | _ => NONE

    fun transformer_expr (on_expr, on_cstr) (e, (to, who)) =
      case e of
          EFix (n, e) => SOME (EFix (n, e))
        | _ => NONE

    fun transformer_kind _ _ = NONE
    fun transformer_prop _ _ = NONE
    end)

fun subst_c_c to who c = Helper.transform_cstr (c, (to, who))
fun subst_c_k to who k = Helper.transform_kind (k, (to, who))
fun subst_c_p to who p = Helper.transform_prop (p, (to, who))
fun subst_c_e to who e = Helper.transform_expr (e, (to, who))

fun subst0_c_c to = subst_c_c to 0
fun subst0_c_k to = subst_c_k to 0
fun subst0_c_p to = subst_c_p to 0
fun subst0_c_e to = subst_c_e to 0
end

structure SubstExpr =
struct
structure Helper = AstGenericOnlyDownTransformer(
    struct
    type down = expr * int

    open ShiftCstr
    open ShiftExpr

    fun add_kind (_, (to, who)) = (shift0_c_e to, who)
    fun add_type (_, (to, who)) = (shift0_e_e to, who + 1)

    fun transformer_expr (on_expr, on_cstr) (e, (to, who)) =
      case e of
          EVar x => SOME (if x = who then to else if x < who then EVar x else EVar (x - 1))
        | EFix (n, e) => SOME (EFix (n, e))
        | _ => NONE

    fun transformer_cstr _ _ = NONE
    fun transformer_kind _ _ = NONE
    fun transformer_prop _ _ = NONE
    end)

fun subst_e_e to who e = Helper.transform_expr (e, (to, who))

fun subst0_e_e to = subst_e_e to 0
end

structure DirectSubstCstr =
struct
structure Helper = AstGenericOnlyDownTransformer(
    struct
    type down = cstr * int

    open ShiftCstr

    fun add_kind (_, (to, who)) = (shift0_c_c to, who + 1)
    fun add_type (_, (to, who)) = (to, who)

    fun transformer_cstr (on_cstr, on_kind) (c, (to, who)) =
      case c of
          CVar x => SOME (if x = who then to else CVar x)
        | _ => NONE

    fun transformer_expr (on_expr, on_cstr) (e, (to, who)) =
      case e of
          EFix (n, e) => SOME (EFix (n, e))
        | _ => NONE

    fun transformer_kind _ _ = NONE
    fun transformer_prop _ _ = NONE
    end)

fun dsubst_c_c to who c = Helper.transform_cstr (c, (to, who))
fun dsubst_c_k to who k = Helper.transform_kind (k, (to, who))
fun dsubst_c_p to who p = Helper.transform_prop (p, (to, who))
fun dsubst_c_e to who e = Helper.transform_expr (e, (to, who))

fun dsubst0_c_c to = dsubst_c_c to 0
fun dsubst0_c_k to = dsubst_c_k to 0
fun dsubst0_c_p to = dsubst_c_p to 0
fun dsubst0_c_e to = dsubst_c_e to 0
end

structure DirectSubstExpr =
struct
structure Helper = AstGenericOnlyDownTransformer(
    struct
    type down = expr * int

    open ShiftCstr
    open ShiftExpr

    fun add_kind (_, (to, who)) = (shift0_c_e to, who)
    fun add_type (_, (to, who)) = (shift0_e_e to, who + 1)

    fun transformer_expr (on_expr, on_cstr) (e, (to, who)) =
      case e of
          EVar x => SOME (if x = who then to else EVar x)
        | EFix (n, e) => SOME (EFix (n, e))
        | _ => NONE

    fun transformer_cstr _ _ = NONE
    fun transformer_kind _ _ = NONE
    fun transformer_prop _ _ = NONE
    end)

fun dsubst_e_e to who e = Helper.transform_expr (e, (to, who))

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
structure Helper = AstGenericTransformer(
    struct
    open List
    open FVUtil

    type down = int
    type up = int list

    val upward_base = []
    val combiner = unique_merge

    fun add_kind (_, ctx) = ctx + 1
    fun add_type (_, ctx) = ctx

    fun transformer_cstr (on_cstr, on_kind) (c, ctx) =
      case c of
          CVar x => SOME (c, if x >= ctx then [x - ctx] else [])
        | _ => NONE

    fun transformer_expr (on_expr, on_cstr) (e, ctx) =
      case e of
          EFix (n, e) => SOME (EFix (n, e), [])
        | _ => NONE

    fun transformer_kind _ _ = NONE
    fun transformer_prop _ _ = NONE
    end)

fun free_vars_c_c d c = #2 (Helper.transform_cstr (c, d))
fun free_vars_c_k d k = #2 (Helper.transform_kind (k, d))
fun free_vars_c_p d p = #2 (Helper.transform_prop (p, d))
fun free_vars_c_e d e = #2 (Helper.transform_expr (e, d))

val free_vars0_c_c = free_vars_c_c 0
val free_vars0_c_k = free_vars_c_k 0
val free_vars0_c_p = free_vars_c_p 0
val free_vars0_c_e = free_vars_c_e 0
end

structure FVExpr =
struct
structure Helper = AstGenericTransformer(
    struct
    open List
    open FVUtil

    type down = int
    type up = int list

    val upward_base = []
    val combiner = unique_merge

    fun add_kind (_, ctx) = ctx
    fun add_type (_, ctx) = ctx + 1

    fun transformer_expr (on_expr, on_cstr) (e, ctx) =
      case e of
          EVar x => SOME (EVar x, if x >= ctx then [x - ctx] else [])
        | EFix (n, e) => SOME (EFix (n, e), [])
        | _ => NONE

    fun transformer_cstr _ _ = NONE
    fun transformer_kind _ _ = NONE
    fun transformer_prop _ _ = NONE
    end)

fun free_vars_e_e d e = #2 (Helper.transform_expr (e, d))

val free_vars0_e_e = free_vars_e_e 0
end
end
