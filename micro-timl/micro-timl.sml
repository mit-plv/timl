functor MicroTiMLFn (Idx : IDX) =
struct

open Idx
open Operators
       
(* kind *)
datatype kind =
         KType
       | KArrow of bsort * kind
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
       | TArrow of ty * idx * ty
       | TAbsI of bsort * ty
       | TAppI of ty * bsort * idx
       | TQuan of unit quan * kind * ty
       | TQuanI of unit quan * sort * ty
       | TRec of kind * ty
       | TNat of idx
       | TArr of ty * idx
       | TAbsT of kind * ty
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
         | EConst of expr_const
         | ELoc of loc
         | EUnOp of expr_un_op * expr
         | EBinOp of expr_bin_op * expr * expr
         | EWrite of expr * expr * expr
         | ECase of expr * expr * expr
         | EAbs of expr
         | ERec of expr
         | EAbsT of expr
         | EAppT of expr * ty
         | EAbsI of sort * expr
         | EAppI of expr * idx
         | EPack of ty * expr
         | EUnpack of expr * expr
         | EPackI of idx * expr
         | EUnpackI of expr * expr
         | EAscTime of expr * idx (* time ascription *)
         | EAscType of expr * ty (* type ascription *)
         | ENever of ty

end
