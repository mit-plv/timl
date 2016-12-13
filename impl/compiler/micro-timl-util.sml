functor MicroTiMLUtilFun(MicroTiMLDef : SIG_MICRO_TIML_DEF) : SIG_MICRO_TIML_UTIL =
struct
open Util

structure MicroTiMLDef = MicroTiMLDef
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
    | TyEqBeta j => j
    | TyEqBetaRev j => j
    | TyEqQuan (j, _, _) => j
    | TyEqRec (j, _, _) => j
    | TyEqRef (j, _) => j
    | TyEqAbs j => j
    | TyEqTimeAbs j => j
    | TyEqTimeApp j => j
    | TyEqTrans (j, _, _) => j
    | TyEqUnOp (j, _) => j
    | TyEqNat (j, _) => j

fun extract_expr_value v =
  case v of
      VConst e => e
    | VPair (e, _, _) => e
    | VInj (e, _) => e
    | VAbs e => e
    | VAbsC e => e
    | VPack (e, _) => e
    | VFold (e, _) => e
    | VLoc e => e

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
    | TyLoc j => j
    | TySubTy (j, _, _) => j
    | TySubTi (j, _, _) => j
    | TyHalt (j, _) => j
    | TyLet (j, _, _) => j
    | TyFix (j, _, _) => j
    | TyPrimBinOp (j, _, _) => j

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

fun extract_e_prim_bin_op (EBinOp (EBPrim opr, e1, e2)) = (opr, e1, e2)
  | extract_e_prim_bin_op _ = raise (Impossible "extract_e_prim_bin_op")

val str_time = Time.str_time
val str_nat = Nat.str_nat

fun str_cstr_const cn =
  case cn of
      CCIdxTT => "tt"
    | CCIdxNat n => str_nat n
    | CCTime r => str_time r
    | CCTypeUnit => "Unit"
    | CCTypeInt => "Int"

fun str_cstr_bin_op opr =
  case opr of
      CBTimeAdd => "+"
    | CBTimeMinus => "-"
    | CBTimeMult => "*"
    | CBTimeMax => "max"
    | CBTypeProd => "*"
    | CBTypeSum => "+"
    | CBNatAdd => "+"

fun str_cstr_un_op opr =
  case opr of
      CUNat2Time => "nat2time"

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
    | PBNatEq => "="

fun str_expr_const cn =
  case cn of
      ECTT => "()"
    | ECInt i => str_int i

fun str_projector p =
  case p of
      ProjFst => "fst"
    | ProjSnd => "snd"

fun str_injector inj =
  case inj of
      InjInl => "inl"
    | InjInr => "inr"

fun str_expr_un_op opr =
  case opr of
      EUProj p => str_projector p
    | EUInj inj => str_injector inj
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
