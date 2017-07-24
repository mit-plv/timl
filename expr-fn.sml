signature EXPR_PARAMS = sig
  type v
  structure UVarI : UVAR_I
  structure UVarT :  UVAR_T
  type ptrn_constr_tag
end
                          
functor ExprFn (Params : EXPR_PARAMS) = struct
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

open Pattern

type cvar = long_id

type ptrn = (cvar * ptrn_constr_tag, mtype) ptrn

type return = mtype option * idx option
                                 
datatype stbind = 
         SortingST of iname binder * sort outer
         | TypingST of ptrn

type scoping_ctx = iname binder list * tname binder list * cname binder list * ename binder list
     
datatype expr =
	 EVar of long_id * bool(*explicit index arguments (EIA)*)
         | EConst of expr_const * region
         | EUnOp of expr_un_op * expr * region
         | EBinOp of bin_op * expr * expr
	 | ETriOp of tri_op * expr * expr * expr
         | EEI of expr_EI * expr * idx
         | EET of expr_ET * expr * mtype
         | ET of expr_T * mtype * region
	 | EAbs of (ptrn, expr) bind
	 | EAbsI of (sort, expr) ibind_anno * region
	 | EAppConstr of (long_id * bool) * mtype list * idx list * expr * (int * mtype) option
	 | ECase of expr * return * (ptrn, expr) bind list * region
	 | ELet of return * (decl tele, expr) bind * region

     and decl =
         DVal of ename binder * (tname binder list, expr) bind outer * region outer
         | DValPtrn of ptrn * expr outer * region outer
         | DRec of ename binder * (tname binder list * stbind tele rebind, (mtype * idx) * expr) bind inner * region outer
         | DIdxDef of iname binder * sort outer * idx outer
         | DAbsIdx2 of iname binder * sort outer * idx outer
         | DAbsIdx of (iname binder * sort outer * idx outer) * decl tele rebind * region outer
         | DTypeDef of tname binder * mtype outer
         | DOpen of mod_id outer * scoping_ctx option

datatype spec =
         SpecVal of name * ty
         | SpecIdx of name * sort
         | SpecType of name * kind
         | SpecTypeDef of name * mtype
                                   
type sgn = spec list * region
(* datatype sgn = *)
(*          SigComponents of spec list * region *)
(*          | SigVar of id *)
(*          | SigWhere of sgn * (id * mtype) *)

(* and sig_comp = *)
(*     ScSpec of name * spec * region *)
(* | ScModSpec of name * sgn *)
(* | Include of sgn *)

datatype mod =
         ModComponents of (* mod_comp *)decl list * region
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
         | TopFunctorApp of name * name (* list *)

type prog = (name * top_bind) list

structure IdxUtil = IdxUtilFn (structure Idx = Idx
                               val dummy = dummy
                              )
open IdxUtil

(* some shorthands *)

val STime = Basic (Base Time, dummy)
val SNat = Basic (Base Nat, dummy)
val SBool = Basic (Base BoolSort, dummy)
val SUnit = Basic (Base UnitSort, dummy)

val Type = (0, [])

fun ETT r = EConst (ECTT, r)
fun EConstInt (n, r) = EConst (ECInt n, r)
fun EConstNat (n, r) = EConst (ECNat n, r)
fun EFst (e, r) = EUnOp (EUFst, e, r)
fun ESnd (e, r) = EUnOp (EUSnd, e, r)
fun EApp (e1, e2) = EBinOp (EBApp, e1, e2)
fun EPair (e1, e2) = EBinOp (EBPair, e1, e2)
fun EAppI (e, i) = EEI (EEIAppI, e, i)
fun EAppIs (f, args) = foldl (swap EAppI) f args
fun EAppT (e, i) = EET (EETAppT, e, i)
fun EAppTs (f, args) = foldl (swap EAppT) f args
fun EAsc (e, t) = EET (EETAsc, e, t)
fun EAscTime (e, i) = EEI (EEIAscTime, e, i)
fun ENever (t, r) = ET (ETNever, t, r)
fun EBuiltin (t, r) = ET (ETBuiltin, t, r)
  
(* notations *)
         
infixr 0 $

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
       
fun collect_EAppI e =
  case e of
      EEI (opr, e, i) =>
      (case opr of
           EEIAppI =>
             let 
               val (e, is) = collect_EAppI e
             in
               (e, is @ [i])
             end
         | _ => (e, [])
      )
    | _ => (e, [])

fun collect_EAppT e =
  case e of
      EET (opr, e, i) =>
      (case opr of
           EETAppT =>
           let 
             val (e, is) = collect_EAppT e
           in
             (e, is @ [i])
           end
         | _ => (e, [])
      )
    | _ => (e, [])

fun collect_BSArrow b =
  case b of
      Base _ => ([], b)
    | BSArrow (a, b) =>
      let
        val (args, ret) = collect_BSArrow b
      in
        (a :: args, ret)
      end
    | UVarBS u => ([], b)

fun combine_BSArrow (args, b) = foldr BSArrow b args
                    
fun is_IApp_UVarI i =
  let
    val (f, args) = collect_IApp i
  in
    case f of
        UVarI (x, r) => SOME ((x, r), args)
      | _ => NONE
  end
    
fun collect_SApp s =
  case s of
      SApp (s, i) =>
      let 
        val (s, is) = collect_SApp s
      in
        (s, is @ [i])
      end
    | _ => (s, [])
             
fun is_SApp_UVarS s =
  let
    val (f, args) = collect_SApp s
  in
    case f of
        UVarS (x, r) => SOME ((x, r), args)
      | _ => NONE
  end
    
fun collect_MtAppI t =
  case t of
      MtAppI (t, i) =>
      let 
        val (f, args) = collect_MtAppI t
      in
        (f, args @ [i])
      end
    | _ => (t, [])
             
fun collect_MtApp t =
  case t of
      MtApp (t1, t2) =>
      let 
        val (f, args) = collect_MtApp t1
      in
        (f, args @ [t2])
      end
    | _ => (t, [])
             
fun is_MtApp_UVar t =
  let
    val (t, t_args) = collect_MtApp t
    val (t, i_args) = collect_MtAppI t
  in
    case t of
        UVar (x, r) => SOME ((x, r), i_args, t_args)
      | _ => NONE
  end
    
fun is_AppV t =
  let
    val (t, i_args) = collect_MtAppI t
    val (t, t_args) = collect_MtApp t
  in
    case t of
        MtVar x => SOME (x, t_args, i_args)
      | _ => NONE
  end
    
fun IApps f args = foldl (fn (arg, f) => BinOpI (IApp, f, arg)) f args
fun SApps f args = foldl (fn (arg, f) => SApp (f, arg)) f args
fun MtAppIs f args = foldl (fn (arg, f) => MtAppI (f, arg)) f args
fun MtApps f args = foldl (fn (arg, f) => MtApp (f, arg)) f args
fun SAbsMany (ctx, s, r) = foldl (fn ((name, s_arg), s) => SAbs (s_arg, Bind ((name, r), s), r)) s ctx
fun IAbsMany (ctx, i, r) = foldl (fn ((name, b), i) => IAbs (b, Bind ((name, r), i), r)) i ctx
fun MtAbsMany (ctx, t, r) = foldl (fn ((name, k), t) => MtAbs (k, Bind ((name, r), t), r)) t ctx
fun MtAbsIMany (ctx, t, r) = foldl (fn ((name, s), t) => MtAbsI (s, Bind ((name, r), t), r)) t ctx
                                 
fun AppVar (x, is) = MtAppIs (MtVar x) is
fun AppV (x, ts, is, r) = MtAppIs (MtApps (MtVar x) ts) is

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

fun get_constr_inames (core : mtype constr_core) =
  let
    val (name_sorts, _) = unfold_binds core
  in
    map fst $ map fst name_sorts
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
(* mlton needs these two lines *)                                         
structure Idx = IdxOfExpr
open Idx

fun get_region_binder (Binder (_, (_, r))) = r
                                             
fun get_region_pn pn = 
  case pn of
      ConstrP (_, _, _, Outer r) => r
    | VarP name => get_region_binder name
    | PairP (pn1, pn2) => combine_region (get_region_pn pn1) (get_region_pn pn2)
    | TTP (Outer r) => r
    | AliasP (_, _, Outer r) => r
    | AnnoP (pn, Outer t) => combine_region (get_region_pn pn) (get_region_mt t)

fun get_region_bind fp ft bind =
  let
    val (p, t) = Unbound.unBind bind
  in
    combine_region (fp p) (ft t)
  end
    
fun get_region_e e = 
  case e of
      EVar (x, _) => get_region_long_id x
    | EConst (_, r) => r
    | EUnOp (_, _, r) => r
    | EBinOp (_, e1, e2) => combine_region (get_region_e e1) (get_region_e e2)
    | ETriOp (_, e1, _, e3) => combine_region (get_region_e e1) (get_region_e e3)
    | EEI (_, e, i) => combine_region (get_region_e e) (get_region_i i)
    | EET (_, e, t) => combine_region (get_region_e e) (get_region_mt t)
    | ET (_, _, r) => r
    | EAbs bind => get_region_bind get_region_pn get_region_e bind
    | EAbsI (_, r) => r
    | EAppConstr ((x, _), _, _, e, _) => combine_region (get_region_long_id x) (get_region_e e)
    | ECase (_, _, _, r) => r
    | ELet (_, _, r) => r
                                              
fun get_region_rule (pn, e) = combine_region (get_region_pn pn) (get_region_e e)

fun get_region_dec dec =
  case dec of
      DVal (_, _, Outer r) => r
    | DValPtrn (_, _, Outer r) => r
    | DRec (_, _, Outer r) => r
    | DIdxDef (name, _, Outer i) => combine_region (get_region_binder name) (get_region_i i)
    | DAbsIdx2 (name, _, Outer i) => combine_region (get_region_binder name) (get_region_i i)
    | DAbsIdx (_, _, Outer r) => r
    | DTypeDef (name, Outer t) => combine_region (get_region_binder name) (get_region_mt t)
    | DOpen (Outer (_, r), _) => r

fun get_region_sig (_, r) = r

fun get_region_m m =
  case m of
      ModComponents (_, r) => r
    | ModSeal (m, sg) => combine_region (get_region_m m) (get_region_sig sg)
    | ModTransparentAsc (m, sg) => combine_region (get_region_m m) (get_region_sig sg)

fun is_value (e : expr) : bool =
  case e of
      EVar _ => true
    | EConst (c, _) =>
      (case c of
           ECTT => true
         | ECNat _ => true
         | ECInt _ => true
      )
    | EUnOp (opr, e, _) =>
      (case opr of
           EUFst => false
         | EUSnd => false
      )
    | EBinOp (opr, e1, e2) =>
      (case opr of
           EBApp => false
         | EBPair => is_value e1 andalso is_value e2
         | EBNew => false
         | EBRead => false
         | EBAdd => false
      )
    | ETriOp _ => false
    | EEI (opr, e, i) =>
      (case opr of
           EEIAppI => false
         | EEIAscTime => false
      )
    | EET (opr, e, t) =>
      (case opr of
           EETAppT => false
         | EETAsc => false
      )
    | ET (opr, t, _) =>
      (case opr of
           ETNever => true
         | ETBuiltin => true
      )
    | EAbs _ => true
    | EAbsI _ => true
    | ELet _ => false
    | EAppConstr (_, _, _, e, _) => is_value e
    | ECase _ => false

fun ptrn_names pn : string list * string list =
  case pn of
      ConstrP (_, inames, pn, _) =>
      let
        val inames = map binder2str inames
        (* val () = println "ConstrP" *)
        val (inames', enames) = ptrn_names pn
      in
        (inames' @ rev inames, enames)
      end
    | VarP name =>
      let
        (* val () = println $ sprintf "VarP: $" [name] *)
      in
        ([], [binder2str name])
      end
    | PairP (pn1, pn2) =>
      let val (inames1, enames1) = ptrn_names pn1
          val (inames2, enames2) = ptrn_names pn2
      in
        (inames2 @ inames1, enames2 @ enames1)
      end
    | TTP _ =>
      ([], [])
    | AliasP (name, pn, _) =>
      let val (inames, enames) = ptrn_names pn
      in
        (inames, enames @ [binder2str name])
      end
    | AnnoP (pn, t) => ptrn_names pn

end

(* Test that the result of [ExprFun] matches some signatures. We don't use a signature ascription because signature ascription (transparent or opaque) hides components that are not in the signature. SML should have a "signature check" kind of ascription. *)
functor TestExprFnSignatures (Params : EXPR_PARAMS) = struct
structure M : IDX = ExprFn (Params)
structure M2 : TYPE = ExprFn (Params)
structure M3 : EXPR = ExprFn (Params)
end
