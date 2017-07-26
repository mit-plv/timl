signature EXPR_SIMP_PARAMS = sig
type var
type cvar
type mod_id
type idx
type sort
type mtype
type ptrn_constr_tag
type ptrn = (cvar * ptrn_constr_tag, mtype) Pattern.ptrn
type ty
type kind
end

functor ExprSimpFn (Params : EXPR_SIMP_PARAMS) = struct

open Params

type return = mtype option * idx option
                                 
datatype stbind = 
         SortingST of Namespaces.iname Unbound.binder * sort Unbound.outer
         | TypingST of ptrn

type scoping_ctx = Namespaces.iname Unbound.binder list * Namespaces.tname Unbound.binder list * Namespaces.cname Unbound.binder list * Namespaces.ename Unbound.binder list
                                                                                                                                                         
datatype expr =
	 EVar of var * bool(*explicit index arguments (EIA)*)
         | EConst of Operators.expr_const * Region.region
         | EUnOp of Operators.expr_un_op * expr * Region.region
         | EBinOp of Operators.bin_op * expr * expr
	 | ETriOp of Operators.tri_op * expr * expr * expr
         | EEI of Operators.expr_EI * expr * idx
         | EET of Operators.expr_ET * expr * mtype
         | ET of Operators.expr_T * mtype * Region.region
	 | EAbs of (ptrn, expr) Unbound.bind
	 | EAbsI of (sort, expr) Binders.ibind_anno * Region.region
	 | EAppConstr of (cvar * bool) * mtype list * idx list * expr * (int * mtype) option
	 | ECase of expr * return * (ptrn, expr) Unbound.bind list * Region.region
	 | ELet of return * (decl Unbound.tele, expr) Unbound.bind * Region.region

     and decl =
         DVal of Namespaces.ename Unbound.binder * (Namespaces.tname Unbound.binder list, expr) Unbound.bind Unbound.outer * Region.region Unbound.outer
         | DValPtrn of ptrn * expr Unbound.outer * Region.region Unbound.outer
         | DRec of Namespaces.ename Unbound.binder * (Namespaces.tname Unbound.binder list * stbind Unbound.tele Unbound.rebind, (mtype * idx) * expr) Unbound.bind Unbound.inner * Region.region Unbound.outer
         | DIdxDef of Namespaces.iname Unbound.binder * sort Unbound.outer * idx Unbound.outer
         | DAbsIdx2 of Namespaces.iname Unbound.binder * sort Unbound.outer * idx Unbound.outer
         | DAbsIdx of (Namespaces.iname Unbound.binder * sort Unbound.outer * idx Unbound.outer) * decl Unbound.tele Unbound.rebind * Region.region Unbound.outer
         | DTypeDef of Namespaces.tname Unbound.binder * mtype Unbound.outer
         | DOpen of mod_id Unbound.outer * scoping_ctx option

type name = string * Region.region
                       
datatype spec =
         SpecVal of name * ty
         | SpecIdx of name * sort
         | SpecType of name * kind
         | SpecTypeDef of name * mtype
                                   
type sgn = spec list * Region.region
(* datatype sgn = *)
(*          SigComponents of spec list * Region.region *)
(*          | SigVar of id *)
(*          | SigWhere of sgn * (id * mtype) *)

(* and sig_comp = *)
(*     ScSpec of name * spec * Region.region *)
(* | ScModSpec of name * sgn *)
(* | Include of sgn *)

datatype mod =
         ModComponents of (* mod_comp *)decl list * Region.region
         (* | ModProjectible of mod_id *)
         | ModSeal of mod * sgn
         | ModTransparentAsc of mod * sgn
(* | ModFunctorApp of id * mod (* list *) *)
                                        
(* and mod_comp = *)
(*     McDecl of decl *)
(* | McModBind of name * mod *)

datatype top_bind =
         TopModBind of mod
         (* | TopSigBind of name * sgn *)
         (* | TopModSpec of name * sgn *)
         | TopFunctorBind of (name * sgn) (* list *) * mod
         | TopFunctorApp of mod_id * mod_id (* list *)

type prog = (name * top_bind) list

end
