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
  type kinding_relation = context * constr * kind
  type proping_relation = context * prop
  type typing_relation = context * term * constr * constr

  datatype kind_wellformedness_derivation =
    KdWfDerivNat of kind_wellformedness_relation
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

  and kinding_derivation =
    KdDerivRefine of kinding_relation * kinding_derivation * proping_derivation
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
    TyDerivSub of typing_relation * typing_derivation * proping_derivation
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
end
