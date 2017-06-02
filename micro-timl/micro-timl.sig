signature MICRO_TIML = sig

  structure Idx : IDX
  type var
  type ('anno, 't) ibind
  type ('anno, 't) tbind
  type ('anno, 't) ebind

  (* kind *)
  datatype kind =
           KType
           | KArrow of Idx.bsort * kind
           | KArrowT of kind * kind

  (* type constants *)
  datatype ty_const =
           TCUnit
           | TCInt
           | TCEmpty

  (* binary type constructors *)
  datatype ty_bin_op =
           TBProd
           | TBSum

  (* type *)
  datatype ty =
           TVar of var
           | TConst of ty_const
           | TBinOp of ty_bin_op * ty * ty
           | TArrow of ty * Idx.idx * ty
           | TAbsI of (Idx.bsort, ty) ibind
           | TAppI of ty * Idx.idx
           | TQuan of unit Operators.quan * (kind, ty) tbind
           | TQuanI of unit Operators.quan * (Idx.sort, ty) ibind
           | TRec of (kind, ty) tbind
           | TNat of Idx.idx
           | TArr of ty * Idx.idx
           | TAbsT of (kind, ty) tbind
           | TAppT of ty * ty

  type loc = int
               
  (* projector for product type *)
  datatype projector =
           ProjFst
           | ProjSnd

  (* injector for sum type *)
  datatype injector =
           InjInl
           | InjInr

  (* unary term operators *)
  datatype expr_un_op =
           EUProj of projector
           | EUInj of injector
           | EUFold
           | EUUnfold

  (* primitive binary term operators *)
  datatype prim_expr_bin_op =
           PEBIntAdd
           | PEBIntMult

  (* binary term operators *)
  datatype expr_bin_op =
           EBPrim of prim_expr_bin_op
           | EBApp
           | EBPair
           | EBNew 
           | EBRead 
           | EBNatAdd

  (* term *)
  datatype expr =
           EVar of var
           | EConst of Operators.expr_const
           | ELoc of loc
           | EUnOp of expr_un_op * expr
           | EBinOp of expr_bin_op * expr * expr
           | EWrite of expr * expr * expr
           | ECase of expr * expr * expr
           | EAbs of (unit, expr) ebind
           | ERec of (unit, expr) ebind
           | EAbsT of (unit, expr) tbind
           | EAppT of expr * ty
           | EAbsI of (Idx.sort, expr) ibind
           | EAppI of expr * Idx.idx
           | EPack of ty * expr
           | EUnpack of expr * (unit, (unit, expr) ebind) tbind
           | EPackI of Idx.idx * expr
           | EUnpackI of expr * (unit, (unit, expr) ebind) ibind
           | EAscTime of expr * Idx.idx (* time ascription *)
           | EAscType of expr * ty (* type ascription *)
           | ENever of ty

end
