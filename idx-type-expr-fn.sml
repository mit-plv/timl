(* This functor is just an assembly of functionalities from many other modules, a Swiss-Army-knife kind of thing. *)

signature IDX_TYPE_EXPR_PARAMS = sig
  type v
  structure UVarI : UVAR_I
  structure UVarT :  UVAR_T
  type ptrn_constr_tag
end
                          
functor IdxTypeExprFn (Params : IDX_TYPE_EXPR_PARAMS) = struct
open Params
open UVarI
open UVarT
open BaseSorts
open BaseTypes
open Util
open LongId
open Operators
open Region
open Bind

infixr 0 $

type id = v * region
type name = string * region
type long_id = v long_id

structure IdxOfExpr = IdxFn (structure UVarI = UVarI
                             type base_sort = base_sort
                             type var = long_id
                             type name = name
                             type region = region
                             type 'idx exists_anno = ('idx -> unit) option
                            )
structure Idx = IdxOfExpr
open Idx

structure TypeOfExpr = TypeFn (structure Idx = Idx
                         structure UVarT = UVarT
                         type base_type = base_type
                            )
structure Type = TypeOfExpr
open Type

structure IdxUtil = IdxUtilFn (Idx)
open IdxUtil

structure TypeUtil = TypeUtilFn (Type)
open TypeUtil

type cvar = var
              
open Pattern

structure ExprCore = ExprFn (
  type var = var
  type cvar = var
  type mod_id = name
  type idx = idx
  type sort = sort
  type mtype = mtype
  val get_constr_names = get_constr_names
  type ptrn_constr_tag = ptrn_constr_tag
  type ty = ty
  type kind = kind
)

open ExprCore

structure ExprUtil = ExprUtilFn (ExprCore)
open ExprUtil
       
(* some shorthands *)

val STime = Basic (Base Time, dummy)
val SNat = Basic (Base Nat, dummy)
val SBool = Basic (Base BoolSort, dummy)
val SUnit = Basic (Base UnitSort, dummy)

val Type = (0, [])

(* notations *)
         
infix 9 %@
infix 8 %^
infix 7 %*
infix 6 %+ 
infix 4 %<=
infix 4 %>=
infix 4 %=
infixr 3 /\
infixr 2 \/
infixr 1 -->
infix 1 <->
        
(* useful functions *)

open Bind
       
val VarT = MtVar
fun constr_type (VarT : int LongId.long_id -> mtype) shiftx_long_id ((family, tbinds) : mtype constr_info) = 
  let
    val (tname_kinds, ibinds) = unfold_binds tbinds
    val tnames = map fst tname_kinds
    val (ns, (t, is)) = unfold_binds ibinds
    val ts = map (fn x => VarT (ID (x, dummy))) $ rev $ range $ length tnames
    val t2 = AppV (shiftx_long_id 0 (length tnames) family, ts, is, dummy)
    val t = Arrow (t, T0 dummy, t2)
    val t = foldr (fn ((name, s), t) => UniI (s, Bind (name, t), dummy)) t ns
    val t = Mono t
    val t = foldr (fn (name, t) => Uni (Bind (name, t), dummy)) t tnames
  in
    t
  end

(* region calculations *)

fun get_region_long_id id =
  case id of
      ID x => snd x
    | QID (m, x) => combine_region (snd m) (snd x)
                                         
fun set_region_long_id id r =
  case id of
      ID (x, _) => ID (x, r)
    | QID ((m, _), (x, _)) => QID ((m, r), (x, r))

structure IdxGetRegion = IdxGetRegionFn (structure Idx = Idx
                                         val get_region_var = get_region_long_id
                                         val set_region_var = set_region_long_id)
open IdxGetRegion
       
structure TypeGetRegion = TypeGetRegionFn (structure Type = Type
                                           val get_region_var = get_region_long_id
                                           val get_region_i = get_region_i)
open TypeGetRegion
       
structure ExprGetRegion = ExprGetRegionFn (structure Expr = ExprCore
                                           val get_region_var = get_region_long_id
                                           val get_region_cvar = get_region_long_id
                                           val get_region_i = get_region_i
                                           val get_region_mt = get_region_mt
                                          )
open ExprGetRegion

(* mlton needs these lines *)                                         
structure Idx = IdxOfExpr
open Idx
structure Type = TypeOfExpr
open Type
       
end

(* Test that the result of [ExprFun] matches some signatures. We don't use a signature ascription because signature ascription (transparent or opaque) hides components that are not in the signature. SML should have a "signature check" kind of ascription. *)
functor TestIdxTypeExprFnSignatures (Params : IDX_TYPE_EXPR_PARAMS) = struct
structure M : IDX = IdxTypeExprFn (Params)
structure M2 : TYPE = IdxTypeExprFn (Params)
structure M3 : EXPR = IdxTypeExprFn (Params)
structure M4 : IDX_TYPE_EXPR = IdxTypeExprFn (Params)
end
