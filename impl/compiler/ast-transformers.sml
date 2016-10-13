functor AstTransformers(Time : SIG_TIME) =
struct
  structure MicroTiML = MicroTiML(Time)
  open MicroTiML

  open Util

  structure PrinterUtil =
  struct
    val str_time = Time.str_time

    fun str_cstr_const cn =
      case cn of
        CCIdxTT => "tt"
      | CCIdxNat n => str_int n
      | CCTime r => str_time r
      | CCTypeUnit => "Unit"
      | CCTypeInt => "Int"

    fun str_cstr_bin_op opr =
      case opr of
        CBTimeAdd => "+"
      | CBTimeMinus => "-"
      | CBTimeMax => "max"
      | CBTypeProd => "*"
      | CBTypeSum => "+"

    fun str_quan q =
      case q of
        QuanForall => "forall"
      | QuanExists => "exists"

    fun str_sort b =
      case b of
        BSNat => "nat"
      | BSUnit => "unit"
      | BSBool => "bool"
      | BSTimeFun arity => "time_fun(" ^ str_int arity ^ ")"

    fun str_prop_bin_conn opr =
      case opr of
        PBCAnd => "/\\"
      | PBCOr => "\\/"
      | PBCImply => "->"
      | PBCIff => "<->"

    fun str_prop_bin_pred opr =
      case opr of
        PBTimeLe => "<="
      | PBTimeEq => "="
      | PBBigO arity => "BigO"

    fun str_expr_const cn =
      case cn of
        ECTT => "()"
      | ECInt i => str_int i

    fun str_projector p =
      case p of
        ProjFst => "fst"
      | ProjSnd => "snd"

    fun str_injectror inj =
      case inj of
        InjInl => "inl"
      | InjInr => "inr"

    fun str_expr_un_op opr =
      case opr of
        EUProj p => str_projector p
      | EUInj inj => str_injectror inj
      | EUFold => "fold"
      | EUUnfold => "unfold"
      | EUNew => "new"
      | EURead => "read"

    fun str_prim_expr_bin_op opr =
      case opr of
        PEBIntAdd => "+"

    fun str_expr_bin_op opr =
      case opr of
        EBPrim opr => str_prim_expr_bin_op opr
      | EBApp => ""
      | EBPair => ","
      | EBWrite => ":="
  end

  structure PlainPrinter =
  struct
    structure Helper = AstGenericOnlyUpTransformer(
    struct
      type up = string

      val upward_base = ""
      fun combiner (up1, up2) = up1 ^ up2

      open PrinterUtil

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

      fun transformer_kind _ _ = NONE
      fun transformer_prop _ _ = NONE
      fun transformer_expr _ _ = NONE
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

      fun transformer_kind _ _ = NONE
      fun transformer_prop _ _ = NONE
      fun transformer_expr _ _ = NONE
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

  structure SubstEXpr =
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
        | _ => NONE

      fun transformer_cstr _ _ = NONE
      fun transformer_kind _ _ = NONE
      fun transformer_prop _ _ = NONE
    end)

    fun subst_e_e to who e = Helper.transform_expr (e, (to, who))

    fun subst0_e_e to = subst_e_e to 0
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

      fun transformer_kind _ _ = NONE
      fun transformer_prop _ _ = NONE
      fun transformer_expr _ _ = NONE
    end)

    fun free_vars_c_c c = Helper.transform_cstr (c, 0)
    fun free_vars_c_k k = Helper.transform_kind (k, 0)
    fun free_vars_c_p p = Helper.transform_prop (p, 0)
    fun free_vars_c_e e = Helper.transform_expr (e, 0)
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
          EVar x => SOME (e, if x >= ctx then [x - ctx] else [])
        | _ => NONE

      fun transformer_cstr _ _ = NONE
      fun transformer_kind _ _ = NONE
      fun transformer_prop _ _ = NONE
    end)

    fun free_vars_e_e e = Helper.transform_expr (e, 0)
  end
end
