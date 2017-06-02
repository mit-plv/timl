signature BINDERS = sig
  type 't ibind
  type 't tbind
  type 't ebind
  type ('anno, 't) ibind_anno
  type ('anno, 't) tbind_anno
  type ('anno, 't) ebind_anno
end

signature MICRO_TIML = sig

  structure Binders : BINDERS

  (* The following definitions use type variables instead of abstract types to enable universal mappings between different AST instantiations. *)
                   
  (* kind *)
  datatype 'bsort kind =
           KType
           | KArrow of 'bsort * 'bsort kind
           | KArrowT of 'bsort kind * 'bsort kind

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
  datatype ('var, 'bsort, 'idx, 'sort) ty =
           TVar of 'var
           | TConst of ty_const
           | TBinOp of ty_bin_op * ('var, 'bsort, 'idx, 'sort) ty * ('var, 'bsort, 'idx, 'sort) ty
           | TArrow of ('var, 'bsort, 'idx, 'sort) ty * 'idx * ('var, 'bsort, 'idx, 'sort) ty
           | TAbsI of ('bsort, ('var, 'bsort, 'idx, 'sort) ty) Binders.ibind_anno
           | TAppI of ('var, 'bsort, 'idx, 'sort) ty * 'idx
           | TQuan of unit Operators.quan * ('bsort kind, ('var, 'bsort, 'idx, 'sort) ty) Binders.tbind_anno
           | TQuanI of unit Operators.quan * ('sort, ('var, 'bsort, 'idx, 'sort) ty) Binders.ibind_anno
           | TRec of ('bsort kind, ('var, 'bsort, 'idx, 'sort) ty) Binders.tbind_anno
           | TNat of 'idx
           | TArr of ('var, 'bsort, 'idx, 'sort) ty * 'idx
           | TAbsT of ('bsort kind, ('var, 'bsort, 'idx, 'sort) ty) Binders.tbind_anno
           | TAppT of ('var, 'bsort, 'idx, 'sort) ty * ('var, 'bsort, 'idx, 'sort) ty

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
  datatype ('var, 'bsort, 'idx, 'sort) expr =
           EVar of 'var
           | EConst of Operators.expr_const
           | ELoc of loc
           | EUnOp of expr_un_op * ('var, 'bsort, 'idx, 'sort) expr
           | EBinOp of expr_bin_op * ('var, 'bsort, 'idx, 'sort) expr * ('var, 'bsort, 'idx, 'sort) expr
           | EWrite of ('var, 'bsort, 'idx, 'sort) expr * ('var, 'bsort, 'idx, 'sort) expr * ('var, 'bsort, 'idx, 'sort) expr
           | ECase of ('var, 'bsort, 'idx, 'sort) expr * ('var, 'bsort, 'idx, 'sort) expr Binders.ebind * ('var, 'bsort, 'idx, 'sort) expr Binders.ebind
           | EAbs of ('var, 'bsort, 'idx, 'sort) expr Binders.ebind
           | ERec of ('var, 'bsort, 'idx, 'sort) expr Binders.ebind
           | EAbsT of ('var, 'bsort, 'idx, 'sort) expr Binders.tbind
           | EAppT of ('var, 'bsort, 'idx, 'sort) expr * ('var, 'bsort, 'idx, 'sort) ty
           | EAbsI of ('sort, ('var, 'bsort, 'idx, 'sort) expr) Binders.ibind_anno
           | EAppI of ('var, 'bsort, 'idx, 'sort) expr * 'idx
           | EPack of ('var, 'bsort, 'idx, 'sort) ty * ('var, 'bsort, 'idx, 'sort) expr
           | EUnpack of ('var, 'bsort, 'idx, 'sort) expr * ('var, 'bsort, 'idx, 'sort) expr Binders.ebind Binders.tbind
           | EPackI of 'idx * ('var, 'bsort, 'idx, 'sort) expr
           | EUnpackI of ('var, 'bsort, 'idx, 'sort) expr * ('var, 'bsort, 'idx, 'sort) expr Binders.ebind Binders.ibind
           | EAscTime of ('var, 'bsort, 'idx, 'sort) expr * 'idx (* time ascription *)
           | EAscType of ('var, 'bsort, 'idx, 'sort) expr * ('var, 'bsort, 'idx, 'sort) ty (* type ascription *)
           | ENever of ('var, 'bsort, 'idx, 'sort) ty

end
