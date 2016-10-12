structure MicroTiML =
struct
  open Util

  type nat = int
  type var = nat
  type time = string
  type loc = nat

  datatype constr =
    CstrVar of var (* constructor variable: index/type *)
  | CstrNat of nat (* index :: Nat *)
  | CstrTime of time (* index :: TimeFun 0 *)
  | CstrUnit (* index :: Unit *)
  | CstrTrue (* index :: Bool *)
  | CstrFalse (* index :: Bool *)
  | CstrUnOp of constr_un_op * constr (* index *)
  | CstrBinOp of constr_bin_op * constr * constr (* index *)
  | CstrIte of constr * constr * constr (* index *)
  | CstrTimeAbs of constr (* index :: TimeFun _ *)
  | CstrProd of constr * constr (* type :: * *)
  | CstrSum of constr * constr (* type :: * *)
  | CstrArrow of constr * constr * constr (* type :: * *)
  | CstrApp of constr * constr (* type-level application *)
  | CstrAbs of kind * constr (* type-level abstraction *)
  | CstrForall of kind * constr (* type :: *, universal *)
  | CstrExists of kind * constr (* type :: *, existential *)
  | CstrRec of kind * constr (* type :: *, recursive *)
  | CstrTypeUnit (* type :: * *)
  | CstrTypeInt (* type :: * *)
  | CstrTypeNat of constr (* type :: * *)
  | CstrTypeArray of constr * constr (* type :: * *)

  and constr_un_op =
    CstrUopCeil
  | CstrUopFloor
  | CstrUopNeg
  | CstrUopLog of nat (* greater than 1 *)
  | CstrUopDiv of nat (* greater thant 0 *)
  | CstrUopNat2Time
  | CstrUopBool2Nat

  and constr_bin_op =
    CstrBopAdd
  | CstrBopDiff
  | CstrBopMult
  | CstrBopExp
  | CstrBopMax
  | CstrBopMin
  | CstrBopTimeApp
  | CstrBopAnd
  | CstrBopOr
  | CstrBopEq
  | CstrBopLe
  | CstrBopLt
  | CstrBopGe
  | CstrBopGt

  and prop =
    PrTop
  | PrBot
  | PrBinConn of prop_bin_conn * prop * prop
  | PrNot of prop
  | PrBinRel of prop_bin_rel * constr * constr
  | PrForall of kind * prop
  | PrExists of kind * prop

  and prop_bin_conn =
    PrConnConj
  | PrConnDisj
  | PrConnImply
  | PrConnEquiv

  and prop_bin_rel =
    PrRelEq
  | PrRelLe
  | PrRelLt
  | PrRelGe
  | PrRelGt
  | PrRelBigO

  and kind =
    KdNat (* for index *)
  | KdUnit (* for index *)
  | KdBool (* for index *)
  | KdTimeFun of nat (* for index *)
  | KdSubset of kind * prop (* for index *)
  | KdProper (* for type *)
  | KdArrow of kind * kind (* for type-level functions *)

  and term =
    TmVar of var
  | TmInt of int
  | TmNat of nat
  | TmUnit
  | TmApp of term * term
  | TmAbs of constr * term
  | TmRec of constr * term
  | TmPair of term * term
  | TmFst of term
  | TmSnd of term
  | TmInLeft of term
  | TmInRight of term
  | TmCase of term * term * term
  | TmFold of term
  | TmUnfold of term
  | TmPack of constr * term
  | TmUnpack of term * term
  | TmCstrAbs of kind * term
  | TmCstrApp of term * constr
  | TmBinOp of term_bin_op * term * term
  | TmArrayNew of term * term
  | TmArrayGet of term * term
  | TmArrayPut of term * term * term
  | TmLet of term * term
  | TmNever

  and term_bin_op =
    TmBopIntAdd
  | TmBopIntMul

  fun str_term_bin_op TmBopIntAdd = "+"
    | str_term_bin_op TmBopIntMul = "*"

  fun str_prop_bin_conn conn =
    case conn of
      PrConnConj => "/\\"
    | PrConnDisj => "\\/"
    | PrConnImply => "=>"
    | PrConnEquiv => "<=>"

  fun str_prop_bin_rel rel =
    case rel of
      PrRelEq => "="
    | PrRelLe => "<="
    | PrRelLt => "<"
    | PrRelGe => ">="
    | PrRelGt => ">"
    | PrRelBigO => "BigO"

  fun str_constr_bin_op bop =
    case bop of
      CstrBopAdd => "+"
    | CstrBopDiff => "-"
    | CstrBopMult => "*"
    | CstrBopExp => "exp"
    | CstrBopMax => "max"
    | CstrBopMin => "min"
    | CstrBopTimeApp => "TimeApp"
    | CstrBopAnd => "and"
    | CstrBopOr => "or"
    | CstrBopEq => "=?"
    | CstrBopLe => "<=?"
    | CstrBopLt => "<?"
    | CstrBopGe => ">=?"
    | CstrBopGt => ">?"

  fun str_constr_un_op uop =
    case uop of
      CstrUopCeil => "ceil"
    | CstrUopFloor => "floor"
    | CstrUopNeg => "~"
    | CstrUopLog b => "log_" ^ str_int b
    | CstrUopDiv b => "div/" ^ str_int b
    | CstrUopNat2Time => "nat2time"
    | CstrUopBool2Nat => "bool2nat"

  datatype bind =
    BdKind of kind
  | BdType of constr
  type context = bind list

  type prop_wellformedness_relation = context * prop
  type kind_wellformedness_relation = context * kind
  type type_equivalence_relation = context * constr * constr
  type kind_equivalence_relation = context * kind * kind
  type kind_sub_relation = context * kind * kind
  type kinding_relation = context * constr * kind
  type proping_relation = context * prop
  type typing_relation = context * term * constr * constr

  datatype kind_wellformedness_derivation =
    KdWfDerivAssume of kind_wellformedness_relation
  | KdWfDerivNat of kind_wellformedness_relation
  | KdWfDerivUnit of kind_wellformedness_relation
  | KdWfDerivBool of kind_wellformedness_relation
  | KdWfDerivTimeFun of kind_wellformedness_relation
  | KdWfDerivSubset of kind_wellformedness_relation * kind_wellformedness_derivation * prop_wellformedness_derivation
  | KdWfDerivProper of kind_wellformedness_relation
  | KdWfDerivArrow of kind_wellformedness_relation * kind_wellformedness_derivation * kind_wellformedness_derivation

  and prop_wellformedness_derivation =
    PrWfDerivTop of prop_wellformedness_relation
  | PrWfDerivBot of prop_wellformedness_relation
  | PrWfDerivBinConn of prop_wellformedness_relation * prop_wellformedness_derivation * prop_wellformedness_derivation
  | PrWfDerivNot of prop_wellformedness_relation * prop_wellformedness_derivation
  | PrWfDerivBinRel of prop_wellformedness_relation * kinding_derivation * kinding_derivation
  | PrWfDerivForall of prop_wellformedness_relation * kind_wellformedness_derivation * prop_wellformedness_derivation
  | PrWfDerivExists of prop_wellformedness_relation * kind_wellformedness_derivation * prop_wellformedness_derivation

  and type_equivalence_derivation =
    TyEqDerivAssume of type_equivalence_relation
  | TyEqDerivTypeUnit of type_equivalence_relation
  | TyEqDerivTypeInt of type_equivalence_relation
  | TyEqDerivTypeNat of type_equivalence_relation * proping_derivation
  | TyEqDerivTypeArray of type_equivalence_relation * type_equivalence_derivation * proping_derivation
  | TyEqDerivArrow of type_equivalence_relation * type_equivalence_derivation * type_equivalence_derivation * proping_derivation
  | TyEqDerivProd of type_equivalence_relation * type_equivalence_derivation * type_equivalence_derivation
  | TyEqDerivSum of type_equivalence_relation * type_equivalence_derivation * type_equivalence_derivation
  | TyEqDerivForall of type_equivalence_relation * kind_equivalence_derivation * type_equivalence_derivation
  | TyEqDerivExists of type_equivalence_relation * kind_equivalence_derivation * type_equivalence_derivation
  | TyEqDerivRec of type_equivalence_relation * kind_equivalence_derivation * type_equivalence_derivation
  | TyEqDerivAbs of type_equivalence_relation * kind_equivalence_derivation * type_equivalence_derivation
  | TyEqDerivApp of type_equivalence_relation * type_equivalence_derivation * type_equivalence_derivation
  | TyEqDerivIndex of type_equivalence_relation * proping_derivation

  and kind_equivalence_derivation =
    KdEqDerivBiSub of kind_equivalence_relation * kind_sub_derivation * kind_sub_derivation

  and kind_sub_derivation =
    KdSubDerivSub of kind_sub_relation * kinding_derivation

  and kinding_derivation =
    KdDerivAssume of kinding_relation
  | KdDerivRefine of kinding_relation * kinding_derivation * proping_derivation
  | KdDerivBase of kinding_relation * kinding_derivation
  | KdDerivVar of kinding_relation
  | KdDerivNat of kinding_relation
  | KdDerivTime of kinding_relation
  | KdDerivUnit of kinding_relation
  | KdDerivTrue of kinding_relation
  | KdDerivFalse of kinding_relation
  | KdDerivUnOp of kinding_relation * kinding_derivation
  | KdDerivBinOp of kinding_relation * kinding_derivation * kinding_derivation
  | KdDerivIte of kinding_relation * kinding_derivation * kinding_derivation * kinding_derivation
  | KdDerivTimeAbs of kinding_relation * kinding_derivation
  | KdDerivProd of kinding_relation * kinding_derivation * kinding_derivation
  | KdDerivSum of kinding_relation * kinding_derivation * kinding_derivation
  | KdDerivArrow of kinding_relation * kinding_derivation * kinding_derivation * kinding_derivation
  | KdDerivApp of kinding_relation * kinding_derivation * kinding_derivation
  | KdDerivAbs of kinding_relation * kind_wellformedness_derivation * kinding_derivation
  | KdDerivForall of kinding_relation * kind_wellformedness_derivation * kinding_derivation
  | KdDerivExists of kinding_relation * kind_wellformedness_derivation * kinding_derivation
  | KdDerivRec of kinding_relation * kind_wellformedness_derivation * kinding_derivation
  | KdDerivTypeUnit of kinding_relation
  | KdDerivTypeInt of kinding_relation
  | KdDerivTypeNat of kinding_relation * kinding_derivation
  | KdDerivTypeArray of kinding_relation * kinding_derivation * kinding_derivation

  and proping_derivation =
    PrDerivAdmit of proping_relation

  datatype typing_derivation =
    TyDerivSub of typing_relation * typing_derivation * type_equivalence_derivation * proping_derivation
  | TyDerivVar of typing_relation
  | TyDerivInt of typing_relation
  | TyDerivNat of typing_relation
  | TyDerivUnit of typing_relation
  | TyDerivApp of typing_relation * typing_derivation * typing_derivation
  | TyDerivAbs of typing_relation * kinding_derivation * typing_derivation
  | TyDerivRec of typing_relation * kinding_derivation * typing_derivation
  | TyDerivPair of typing_relation * typing_derivation * typing_derivation
  | TyDerivFst of typing_relation * typing_derivation
  | TyDerivSnd of typing_relation * typing_derivation
  | TyDerivInLeft of typing_relation * kinding_derivation * typing_derivation
  | TyDerivInRight of typing_relation * kinding_derivation * typing_derivation
  | TyDerivCase of typing_relation * typing_derivation * typing_derivation * typing_derivation
  | TyDerivFold of typing_relation * kinding_derivation * typing_derivation
  | TyDerivUnfold of typing_relation * typing_derivation
  | TyDerivPack of typing_relation * kinding_derivation * kinding_derivation * typing_derivation
  | TyDerivUnpack of typing_relation * typing_derivation * typing_derivation
  | TyDerivCstrAbs of typing_relation * kind_wellformedness_derivation * typing_derivation
  | TyDerivCstrApp of typing_relation * typing_derivation * kinding_derivation
  | TyDerivBinOp of typing_relation * typing_derivation * typing_derivation
  | TyDerivArrayNew of typing_relation * typing_derivation * typing_derivation
  | TyDerivArrayGet of typing_relation * typing_derivation * typing_derivation * proping_derivation
  | TyDerivArrayPut of typing_relation * typing_derivation * typing_derivation * proping_derivation * typing_derivation
  | TyDerivLet of typing_relation * typing_derivation * typing_derivation
  | TyDerivNever of typing_relation * kinding_derivation * proping_derivation

  fun is_value tm =
    case tm of
      TmVar _ => true
    | TmInt _ => true
    | TmNat _ => true
    | TmUnit => true
    | TmAbs _ => true
    | TmRec _ => true
    | TmCstrAbs _ => true
    (*| TmFold tm1 => is_value tm1
    | TmUnfold tm1 => is_value tm1
    | TmPack (cstr1, tm2) => is_value tm2
    | TmCstrApp (tm1, cstr2) => is_value tm1*)
    | TmNever => true
    | _ => false

  fun extract_tyeqrel tyeq =
    case tyeq of
      TyEqDerivAssume rel => rel
    | TyEqDerivAbs (rel, _, _) => rel
    | TyEqDerivRec (rel, _, _) => rel
    | TyEqDerivForall (rel, _, _) => rel
    | TyEqDerivExists (rel, _, _) => rel
    | TyEqDerivTypeInt rel => rel
    | TyEqDerivTypeUnit rel => rel
    | TyEqDerivTypeNat (rel, _) => rel
    | TyEqDerivTypeArray (rel, _, _) => rel
    | TyEqDerivProd (rel, _, _) => rel
    | TyEqDerivSum (rel, _, _) => rel
    | TyEqDerivArrow (rel, _, _, _) => rel
    | TyEqDerivApp (rel, _, _) => rel
    | TyEqDerivIndex (rel, _) => rel

  fun extract_kdeqrel kdeq =
    case kdeq of
      KdEqDerivBiSub (rel, _, _) => rel

  fun extract_kdwfrel kdwf =
    case kdwf of
      KdWfDerivAssume rel => rel
    | KdWfDerivNat rel => rel
    | KdWfDerivUnit rel => rel
    | KdWfDerivBool rel => rel
    | KdWfDerivTimeFun rel => rel
    | KdWfDerivSubset (rel, _, _) => rel
    | KdWfDerivProper rel => rel
    | KdWfDerivArrow (rel, _, _) => rel

  fun extract_prwfrel prwf =
    case prwf of
      PrWfDerivTop rel => rel
    | PrWfDerivBot rel => rel
    | PrWfDerivBinConn (rel, _, _) => rel
    | PrWfDerivNot (rel, _) => rel
    | PrWfDerivBinRel (rel, _, _) => rel
    | PrWfDerivForall (rel, _, _) => rel
    | PrWfDerivExists (rel, _, _) => rel

  fun extract_prrel prderiv =
    case prderiv of
      PrDerivAdmit rel => rel

  fun extract_kdsubrel kdsub =
    case kdsub of
      KdSubDerivSub (rel, _) => rel

  fun extract_tyrel tyderiv =
    case tyderiv of
      TyDerivSub (rel, _, _, _) => rel
    | TyDerivVar rel => rel
    | TyDerivInt rel => rel
    | TyDerivNat rel => rel
    | TyDerivUnit rel => rel
    | TyDerivApp (rel, _, _) => rel
    | TyDerivAbs (rel, _, _) => rel
    | TyDerivRec (rel, _, _) => rel
    | TyDerivPair (rel, _, _) => rel
    | TyDerivFst (rel, _) => rel
    | TyDerivSnd (rel, _) => rel
    | TyDerivInLeft (rel, _, _) => rel
    | TyDerivInRight (rel, _, _) => rel
    | TyDerivCase (rel, _, _, _) => rel
    | TyDerivFold (rel, _, _) => rel
    | TyDerivUnfold (rel, _) => rel
    | TyDerivPack (rel, _, _, _) => rel
    | TyDerivUnpack (rel, _, _) => rel
    | TyDerivCstrAbs (rel, _, _) => rel
    | TyDerivCstrApp (rel, _, _) => rel
    | TyDerivBinOp (rel, _, _) => rel
    | TyDerivArrayNew (rel, _, _) => rel
    | TyDerivArrayGet (rel, _, _, _) => rel
    | TyDerivArrayPut (rel, _, _, _, _) => rel
    | TyDerivLet (rel, _, _) => rel
    | TyDerivNever (rel, _, _) => rel

  fun extract_kdrel kdderiv =
    case kdderiv of
      KdDerivAssume rel => rel
    | KdDerivRefine (rel, _, _) => rel
    | KdDerivBase (rel, _) => rel
    | KdDerivVar rel => rel
    | KdDerivNat rel => rel
    | KdDerivTime rel => rel
    | KdDerivUnit rel => rel
    | KdDerivTrue rel => rel
    | KdDerivFalse rel => rel
    | KdDerivUnOp (rel, _) => rel
    | KdDerivBinOp (rel, _, _) => rel
    | KdDerivIte (rel, _, _, _) => rel
    | KdDerivTimeAbs (rel, _) => rel
    | KdDerivProd (rel, _, _) => rel
    | KdDerivSum (rel, _, _) => rel
    | KdDerivArrow (rel, _, _, _) => rel
    | KdDerivAbs (rel, _, _) => rel
    | KdDerivApp (rel, _, _) => rel
    | KdDerivForall (rel, _, _) => rel
    | KdDerivExists (rel, _, _) => rel
    | KdDerivRec (rel, _, _) => rel
    | KdDerivTypeUnit rel => rel
    | KdDerivTypeInt rel => rel
    | KdDerivTypeNat (rel, _) => rel
    | KdDerivTypeArray (rel, _, _) => rel

  fun extract_cstr_arrow (CstrArrow r) = r
    | extract_cstr_arrow _ = raise (Impossible "not a cstr arrow")

  fun extract_cstr_prod (CstrProd r) = r
    | extract_cstr_prod _ = raise (Impossible "not a cstr prod")

  fun extract_cstr_sum (CstrSum r) = r
    | extract_cstr_sum _ = raise (Impossible "not a cstr sum")

  fun extract_cstr_rec (CstrRec r) = r
    | extract_cstr_rec _ = raise (Impossible "not a cstr rec")

  fun extract_cstr_forall (CstrForall r) = r
    | extract_cstr_forall _ = raise (Impossible "not a cstr forall")

  fun extract_cstr_exists (CstrExists r) = r
    | extract_cstr_exists _ = raise (Impossible "not a cstr exists")

  fun extract_cstr_abs (CstrAbs r) = r
    | extract_cstr_abs _ = raise (Impossible "not a cstr abs")

  fun extract_cstr_type_nat (CstrTypeNat r) = r
    | extract_cstr_type_nat _ = raise (Impossible "not a cstr type nat")

  fun extract_cstr_type_array (CstrTypeArray r) = r
    | extract_cstr_type_array _ = raise (Impossible "not a cstr type array")

  fun extract_cstr_bin_op (CstrBinOp r) = r
    | extract_cstr_bin_op _ = raise (Impossible "not a cstr bin op")

  fun extract_cstr_un_op (CstrUnOp r) = r
    | extract_cstr_un_op _ = raise (Impossible "not a cstr un op")

  fun extract_tm_abs (TmAbs r) = r
    | extract_tm_abs _ = raise (Impossible "not a tm abs")

  fun extract_tm_rec (TmRec r) = r
    | extract_tm_rec _ = raise (Impossible "not a tm rec")

  fun extract_tm_cstr_abs (TmCstrAbs r) = r
    | extract_tm_cstr_abs _ = raise (Impossible "not a tm cstr abs")

  fun extract_tm_bin_op (TmBinOp r) = r
    | extract_tm_bin_op _ = raise (Impossible "not a tm bin op")

  fun extract_pr_bin_rel (PrBinRel r) = r
    | extract_pr_bin_rel _ = raise (Impossible "not a pr bin rel")

  fun extract_pr_bin_conn (PrBinConn r) = r
    | extract_pr_bin_conn _ = raise (Impossible "not a pr bin conn")

  fun extract_kd_time_fun (KdTimeFun n) = n
    | extract_kd_time_fun _ = raise (Impossible "not a kd time fun")

  fun extract_kd_arrow (KdArrow r) = r
    | extract_kd_arrow _ = raise (Impossible "not a kd arrow")

  fun term_bin_op_to_constr bop =
    case bop of
      TmBopIntAdd => (CstrTypeInt, (CstrTypeInt, CstrTypeInt))
    | TmBopIntMul => (CstrTypeInt, (CstrTypeInt, CstrTypeInt))

  fun cstr_un_op_to_kind uop =
    case uop of
      CstrUopDiv _ => (KdTimeFun 0, KdTimeFun 0)
    | CstrUopLog _ => (KdTimeFun 0, KdTimeFun 0)
    | CstrUopNeg => (KdTimeFun 0, KdTimeFun 0)
    | CstrUopCeil => (KdTimeFun 0, KdTimeFun 0)
    | CstrUopFloor => (KdTimeFun 0, KdTimeFun 0)
    | CstrUopBool2Nat => (KdNat, KdBool)
    | CstrUopNat2Time => (KdTimeFun 0, KdNat)

  fun cstr_bin_op_to_kind bop =
    case bop of
      CstrBopOr => [(KdBool, (KdBool, KdBool))]
    | CstrBopEq => [(KdBool, (KdNat, KdNat)), (KdBool, (KdBool, KdBool)), (KdBool, (KdUnit, KdUnit))]
    | CstrBopGe => [(KdBool, (KdNat, KdNat)), (KdBool, (KdTimeFun 0, KdTimeFun 0))]
    | CstrBopGt => [(KdBool, (KdNat, KdNat)), (KdBool, (KdTimeFun 0, KdTimeFun 0))]
    | CstrBopLe => [(KdBool, (KdNat, KdNat)), (KdBool, (KdTimeFun 0, KdTimeFun 0))]
    | CstrBopLt => [(KdBool, (KdNat, KdNat)), (KdBool, (KdTimeFun 0, KdTimeFun 0))]
    | CstrBopAdd => [(KdNat, (KdNat, KdNat)), (KdTimeFun 0, (KdTimeFun 0, KdTimeFun 0))]
    | CstrBopAnd => [(KdBool, (KdBool, KdBool))]
    | CstrBopExp => [(KdNat, (KdNat, KdNat))]
    | CstrBopDiff => [(KdNat, (KdNat, KdNat)), (KdTimeFun 0, (KdTimeFun 0, KdTimeFun 0))]
    | CstrBopMult => [(KdNat, (KdNat, KdNat)), (KdTimeFun 0, (KdTimeFun 0, KdTimeFun 0))]
    | CstrBopMax => [(KdNat, (KdNat, KdNat)), (KdTimeFun 0, (KdTimeFun 0, KdTimeFun 0))]
    | CstrBopMin => [(KdNat, (KdNat, KdNat)), (KdTimeFun 0, (KdTimeFun 0, KdTimeFun 0))]
    | CstrBopTimeApp => []

  fun prop_bin_rel_to_kind rel =
    case rel of
      PrRelEq => [(KdBool, KdBool), (KdNat, KdNat), (KdUnit, KdUnit), (KdTimeFun 0, KdTimeFun 0)]
    | PrRelLe => [(KdNat, KdNat), (KdTimeFun 0, KdTimeFun 0)]
    | PrRelLt => [(KdNat, KdNat), (KdTimeFun 0, KdTimeFun 0)]
    | PrRelGe => [(KdNat, KdNat), (KdTimeFun 0, KdTimeFun 0)]
    | PrRelGt => [(KdNat, KdNat), (KdTimeFun 0, KdTimeFun 0)]
    | PrRelBigO => []
end
