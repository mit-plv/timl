structure MicroTiML = struct

open Region
type name = string * region
open Namespaces
                       
open Binders
open Operators

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
         | TAbsI of ('bsort, ('var, 'bsort, 'idx, 'sort) ty) ibind_anno
         | TAppI of ('var, 'bsort, 'idx, 'sort) ty * 'idx
         | TQuan of unit Operators.quan * ('bsort kind, ('var, 'bsort, 'idx, 'sort) ty) tbind_anno
         | TQuanI of unit Operators.quan * ('sort, ('var, 'bsort, 'idx, 'sort) ty) ibind_anno
         | TRec of ('bsort kind, ('var, 'bsort, 'idx, 'sort) ty) tbind_anno
         | TNat of 'idx
         | TArr of ('var, 'bsort, 'idx, 'sort) ty * 'idx
         | TAbsT of ('bsort kind, ('var, 'bsort, 'idx, 'sort) ty) tbind_anno
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
datatype 'ty expr_un_op =
         EUProj of projector
         | EUInj of injector * 'ty
         | EUFold of 'ty
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
datatype ('var, 'idx, 'sort, 'kind, 'ty) expr =
         EVar of 'var
         | EConst of Operators.expr_const
         | ELoc of loc
         | EUnOp of 'ty expr_un_op * ('var, 'idx, 'sort, 'kind, 'ty) expr
         | EBinOp of expr_bin_op * ('var, 'idx, 'sort, 'kind, 'ty) expr * ('var, 'idx, 'sort, 'kind, 'ty) expr
         | EWrite of ('var, 'idx, 'sort, 'kind, 'ty) expr * ('var, 'idx, 'sort, 'kind, 'ty) expr * ('var, 'idx, 'sort, 'kind, 'ty) expr
         | ECase of ('var, 'idx, 'sort, 'kind, 'ty) expr * ('var, 'idx, 'sort, 'kind, 'ty) expr ebind * ('var, 'idx, 'sort, 'kind, 'ty) expr ebind
         | EAbs of ('ty, ('var, 'idx, 'sort, 'kind, 'ty) expr) ebind_anno
         | ERec of ('ty, ('var, 'idx, 'sort, 'kind, 'ty) expr) ebind_anno
         | EAbsT of ('kind, ('var, 'idx, 'sort, 'kind, 'ty) expr) tbind_anno
         | EAppT of ('var, 'idx, 'sort, 'kind, 'ty) expr * 'ty
         | EAbsI of ('sort, ('var, 'idx, 'sort, 'kind, 'ty) expr) ibind_anno
         | EAppI of ('var, 'idx, 'sort, 'kind, 'ty) expr * 'idx
         | EPack of 'ty * 'ty * ('var, 'idx, 'sort, 'kind, 'ty) expr
         | EUnpack of ('var, 'idx, 'sort, 'kind, 'ty) expr * ('var, 'idx, 'sort, 'kind, 'ty) expr ebind tbind
         | EPackI of 'ty * 'idx * ('var, 'idx, 'sort, 'kind, 'ty) expr
         | EUnpackI of ('var, 'idx, 'sort, 'kind, 'ty) expr * ('var, 'idx, 'sort, 'kind, 'ty) expr ebind ibind
         | EAscTime of ('var, 'idx, 'sort, 'kind, 'ty) expr * 'idx (* time ascription *)
         | EAscType of ('var, 'idx, 'sort, 'kind, 'ty) expr * 'ty (* type ascription *)
         | ENever of 'ty
         | ELet of ('var, 'idx, 'sort, 'kind, 'ty) expr * ('var, 'idx, 'sort, 'kind, 'ty) expr ebind

end
