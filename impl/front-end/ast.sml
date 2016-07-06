structure Ast = struct
open Region
open Operators
       
type id = string * region

type long_id = id option * id
                             
datatype idx = 
	 VarI of long_id
	 | ConstIN of int * region
	 | ConstIT of string * region
         (* | UnOpI of idx_un_op * idx * region *)
	 | BinOpI of idx_bin_op * idx * idx * region
	 | TTI of region
         | TimeAbs of id list * idx * region
         | DivI of idx * (int * region) * region

datatype prop =
	 ConstP of string * region
         | Not of prop * region
	 | BinConn of bin_conn * prop * prop * region
	 | BinPred of bin_pred * idx * idx * region

datatype bsort =
         Base of id
         | TimeFun of string * int * region

datatype sort =
	 Basic of bsort
	 | Subset of bsort * id * prop * region
         | BigOSort of string * int * idx * region

datatype quan =
	 Forall

datatype abs = 
	 Fn
	 | Rec

     and tbind =
         Sorting of id * sort * region

fun sortings (ids, s, r) = map (fn id => Sorting (id, s, r)) ids
                               
datatype ty =
	 VarT of long_id
	 | Arrow of ty * idx * ty * region
	 | Prod of ty * ty * region
	 | Quan of quan * tbind list * ty * region
	 | AppTT of ty * ty * region
	 | AppTI of ty * idx * region

fun get_region_long_id (m, (_, r)) =
    case m of
        NONE => r
      | SOME (_, r1) => combine_region r1 r

fun get_region_t t =
    case t of
        VarT x => get_region_long_id x
      | Arrow (_, _, _, r) => r
      | Prod (_, _, r) => r
      | Quan (_, _, _, r) => r
      | AppTT (_, _, r) => r
      | AppTI (_, _, r) => r

type constr_core = ty * ty option
type constr_decl = id * tbind list * constr_core option * region

datatype ptrn =
	 ConstrP of (long_id * bool) * string list * ptrn option * region
         | TupleP of ptrn list * region
         | AliasP of id * ptrn * region
         | AnnoP of ptrn * ty * region

fun get_region_pn pn =
    case pn of
        ConstrP (_, _, _, r) => r
      | TupleP (_, r) => r
      | AliasP (_, _, r) => r
      | AnnoP (_, _, r) => r

datatype bind =
	 Typing of ptrn
	 | TBind of tbind

type return = ty option * idx option
type datatype_def = string * string list * sort list * constr_decl list * region
              
datatype exp = 
	 Var of long_id * bool
         | Tuple of exp list * region
         | Abs of bind list * return * exp * region
         | App of exp * exp * region
         | AppI of exp * idx * region
         | Case of exp * return * (ptrn * exp) list * region
         | Ascription of exp * ty * region
         | AscriptionTime of exp * idx * region
         | Let of return * decl list * exp * region
         | Const of int * region
         | ConstNat of int * region
         | BinOp of bin_op * exp * exp * region

     and decl =
         Val of id list * ptrn * exp * region
         | Rec of id list * id * bind list * return * exp * region
         | Datatype of datatype_def
         | IdxDef of id * sort option * idx
         | AbsIdx2 of id * sort option * idx
         | AbsIdx of id * sort option * idx option * decl list * region
         | TypeDef of id * ty
       | Open of id

fun short_id id = ((NONE, id), false)
fun PShortVar (x, r) = ConstrP (short_id (x, r), [], NONE, r)
fun EIte (e, e1, e2, r) = Case (e, (NONE, NONE), [(PShortVar ("true", r), e1), (PShortVar ("false", r), e2)], r)
fun EShortVar id = Var (short_id id)
fun ECons (e1, e2, r) = App (EShortVar ("Cons", r), Tuple ([e1, e2], r), r)
fun PCons (pn1, pn2, r) = ConstrP (short_id ("Cons", r), [], SOME (TupleP ([pn1, pn2], r)), r)
fun ENil r = EShortVar ("Nil", r)
fun EList (es, r) = foldr (fn (e, acc) => ECons (e, acc, r)) (ENil r) es
fun PNil r = PShortVar ("Nil", r)
fun PList (pns, r) = foldr (fn (pn, acc) => PCons (pn, acc, r)) (PNil r) pns
                               
type name = id
              
datatype spec =
         SpecVal of name * name list * ty * region
         | SpecDatatype of datatype_def
         | SpecIdx of name * sort
         | SpecType of name list * sort list * region
         | SpecTypeDef of name * ty
                                   
datatype sgn =
         SigComponents of spec list * region

datatype mod =
         ModComponents of decl list * region
         | ModSeal of mod * sgn
         | ModTransparentAscription of mod * sgn
                                               
datatype top_bind =
         TopModBind of name * mod
         | TopFunctorBind of name * (name * sgn) * mod
         | TopFunctorApp of name * id * id

type prog = top_bind list

(* datatype sig_anno = *)
(*          Seal of sgn *)
(*          | Transparent of sgn *)

(* fun add_sig_anno m sg = *)
(*     case sg of *)
(*         NONE => m *)
(*       | SOME sg => *)
(*         case sg of *)
(*             Seal sg => ModSeal (m, sg) *)
(*           | Transparent sg => ModTransparentAscription (m, sg) *)

type reporter = string * pos * pos -> unit

fun underscore r = (NONE, ("_", r))

end

