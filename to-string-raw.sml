functor ToStringRawFn (structure Expr : IDX_TYPE_EXPR
                                          where type Idx.base_sort = BaseSorts.base_sort
                                            and type Type.base_type = BaseTypes.base_type
                       sharing type Expr.Type.bsort = Expr.Idx.bsort
                       val str_raw_var : Expr.var -> string
                       val str_uvar_i : ('bsort -> string) * ('idx -> string) -> ('bsort, 'idx) Expr.Idx.uvar_i -> string
                       val str_uvar_mt : ('sort -> string) * ('kind -> string) * ('mtype -> string) -> ('sort, 'kind, 'mtype) Expr.Type.uvar_mt -> string
                      ) = struct

open Expr
open Idx
open Type
open Util
open BaseSorts
open BaseTypes
open Operators
open Bind
       
fun str_raw_option f a = case a of SOME a => sprintf "SOME ($)" [f a] | NONE => "NONE"

fun str_raw_name (s, _) = s

fun str_raw_bind f (Bind (_, a)) = sprintf "Bind ($)" [f a]

fun str_raw_bs b =
  case b of
      Base s => sprintf "Base ($)" [str_b s]
    | BSArrow (s1, s2) => sprintf "BSArrow ($, $)" [str_raw_bs s1, str_raw_bs s2]
    | UVarBS u => "UVarBS"

fun str_raw_i i =
  case i of
      VarI x => sprintf "VarI ($)" [str_raw_var x]
    | IConst (c, _) => sprintf "IConst ($)" [str_idx_const c]
    | UnOpI (opr, i, _) => sprintf "UnOpI ($, $)" [str_idx_un_op opr, str_raw_i i]
    | BinOpI (opr, i1, i2) => sprintf "BinOpI ($, $, $)" [str_idx_bin_op opr, str_raw_i i1, str_raw_i i2]
    | Ite (i1, i2, i3, _) => sprintf "Ite ($, $, $)" [str_raw_i i1, str_raw_i i2, str_raw_i i3]
    | IAbs (b, bind, _) => sprintf "IAbs ($, $)" [str_raw_bs b, str_raw_bind str_raw_i bind]
    | UVarI (u, _) => str_uvar_i (str_raw_bs, str_raw_i) u

fun str_raw_s s =
  case s of
      Basic (b, _) => sprintf "Basic ($)" [str_raw_bs b]
    | _ => "<sort>"
                    
fun str_raw_k k = "<kind>"

fun str_raw_mt (t : mtype) : string =
  case t of
      Arrow (t1, i, t2) => sprintf "Arrow ($, $, $)" [str_raw_mt t1, str_raw_i i, str_raw_mt t2]
    | TyNat (i, _) => sprintf "TyNat ($))" [str_raw_i i]
    | TyArray (t, i) => sprintf "TyArray ($, $)" [str_raw_mt t, str_raw_i i]
    | Unit _ => "Unit"
    | Prod (t1, t2) => sprintf "Prod ($, $)" [str_raw_mt t1, str_raw_mt t2]
    | UniI (s, bind, _) => sprintf "UniI ($, $)" ["<sort>", str_raw_bind str_raw_mt bind]
    | MtVar x => sprintf "MtVar ($)" [str_raw_var x]
    | MtApp (t1, t2) => sprintf "MtApp ($, $)" [str_raw_mt t1, str_raw_mt t2]
    | MtAbs (k, bind, _) => sprintf "MtAbs ($, $)" ["<kind>", str_raw_bind str_raw_mt bind]
    | MtAppI (t, i) => sprintf "MtAppI ($, $)" [str_raw_mt t, str_raw_i i]
    | MtAbsI (s, bind, _) => sprintf "MtAbsI ($, $)" ["<sort>", str_raw_bind str_raw_mt bind]
    | BaseType (bt, _) => sprintf "BaseType ($)" [str_bt bt]
    | UVar (u, _) => sprintf "UVar ($)" [str_uvar_mt (str_raw_bs, str_raw_k, str_raw_mt) u]
    | TDatatype (dt, _) => "TDatatype (...)"

fun str_raw_t (t : ty) : string =
  case t of
      Mono t => str_raw_mt t
    | Uni (t, _) => sprintf "Uni ($)" [str_raw_bind str_raw_t t]

fun str_raw_e e =
  case e of
      EAppConstr _ => "AppConstr (...)"
    | EBinOp _ => "BinOp (...)"
    | EEI (opr, e, i) => sprintf "EEI ($, $, $)" [str_expr_EI opr, str_raw_e e, str_raw_i i]
    | _ => "<exp>"

end
