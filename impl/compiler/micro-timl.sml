structure MicroTiML =
struct
  exception TODO

  type nat = int
  type var = nat
  type time = string
  type loc = nat

  datatype constr =
    CstrVar of var
  | CstrNat of nat
  | CstrTime of time
  | CstrUnit
  | CstrTrue
  | CstrFalse
  | CstrUnOp of constr_un_op * constr
  | CstrBinOp of constr_bin_op * constr * constr
  | CstrIte of constr * constr * constr
  | CstrTimeAbs of constr
  | CstrProd of constr * constr
  | CstrSum of constr * constr
  | CstrArrow of constr * constr * constr
  | CstrApp of constr * constr
  | CstrAbs of kind * constr
  | CstrForall of kind * constr
  | CstrExists of kind * constr
  | CstrRec of kind * constr
  | CstrTypeUnit
  | CstrTypeInt
  | CstrTypeNat of constr
  | CstrTypeArr of constr * constr

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
    KdNat
  | KdUnit
  | KdBool
  | KdTimeFun of nat
  | KdSubset of kind * prop
  | KdProper
  | KdArrow of kind * kind

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
  | TmIdxAbs of kind * term
  | TmIdxApp of term * constr
  | TmBinOp of term_bin_op * term * term
  | TmArrayNew of term * term
  | TmArrayGet of term * term
  | TmArrayPut of term * term * term

  and term_bin_op =
    TmBopIntAdd
  | TmBopIntMul

  type kcontext = kind list
  type tcontext = constr list
  type context = kcontext * tcontext
end
