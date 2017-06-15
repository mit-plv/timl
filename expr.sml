structure BaseSorts = struct
open Util
(* basic index sort *)
datatype base_sort =
         Nat
         | Time
	 | BoolSort
	 | UnitSort

fun str_b (s : base_sort) : string = 
  case s of
      Nat => "Nat"
    | Time => "Time"
    | BoolSort => "Bool"
    | UnitSort => "Unit"
end

structure BaseTypes = struct
datatype base_type =
         Int
fun eq_base_type (t : base_type, t') = t = t'
        
fun str_bt bt =
  case bt of
      Int => "int"

end

signature EXPR_PARAMS = sig
  structure Var : VAR
  structure UVarI : UVAR_I
  structure UVarT : UVAR_T
  type ptrn_constr_tag
end
                          
functor ExprFn (Params : EXPR_PARAMS) = struct
open Params
open Var
open BaseSorts
open BaseTypes
open Util
open Operators
open UVarI
open UVarT
open Region
open Bind

type id = var * region
type name = string * region

(* Curve out a fragment of module expression that is not a full component list ('struct' in ML) that involves types and terms, to avoid making everything mutually dependent. (This means I can't do module substitution because the result may not be expressible.) It coincides with the concept 'projectible' or 'determinate'. *)
type mod_projectible = name
type long_id = mod_projectible option * id
                         
structure Idx = IdxFn (structure UVarI = UVarI
                       type base_sort = base_sort
                       type var = long_id
                       type name = name
                       type region = region
                       type 'idx exists_anno = ('idx -> unit) option
                      )
open Idx

structure Type = TypeFn (structure Idx = Idx
                         structure UVarT = UVarT
                         type base_type = base_type
                        )
open Type

open Pattern

type ptrn = (long_id * ptrn_constr_tag, mtype, name, region) ptrn

type return = mtype option * idx option
                                 
datatype stbind = 
         SortingST of name * sort
         | TypingST of ptrn

type scoping_ctx = string list * string list * string list * string list
     
datatype expr =
	 Var of long_id * bool(*explicit index arguments (EIA)*)
         | EConst of expr_const * region
         | EUnOp of expr_un_op * expr * region
         | BinOp of bin_op * expr * expr
	 | TriOp of tri_op * expr * expr * expr
         | EEI of expr_EI * expr * idx
         | ET of expr_T * mtype * region
	 | Abs of ptrn * expr
	 | AbsI of sort * (name * expr) ibind * region
	 | AppConstr of (long_id * bool) * idx list * expr
	 | Case of expr * return * (ptrn * expr) list * region
	 | Let of return * decl list * expr * region
	 | Ascription of expr * mtype


     and decl =
         Val of name list * ptrn * expr * region
         | Rec of name list * name * (stbind list * ((mtype * idx) * expr)) * region
	 | Datatype of mtype datatype_def * region
         | IdxDef of name * sort * idx
         | AbsIdx2 of name * sort * idx
         | AbsIdx of (name * sort * idx) * decl list * region
         | TypeDef of name * mtype
         | Open of mod_projectible * scoping_ctx option

datatype spec =
         SpecVal of name * ty
         | SpecDatatype of mtype datatype_def * region
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
         (* | ModProjectible of mod_projectible *)
         | ModSeal of mod * sgn
         | ModTransparentAscription of mod * sgn
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

fun TT r = EConst (ECTT, r)
fun ConstInt (n, r) = EConst (ECInt n, r)
fun ConstNat (n, r) = EConst (ECNat n, r)
fun Fst (e, r) = EUnOp (EUFst, e, r)
fun Snd (e, r) = EUnOp (EUSnd, e, r)
fun App (e1, e2) = BinOp (EBApp, e1, e2)
fun Pair (e1, e2) = BinOp (EBPair, e1, e2)
fun AppI (e, i) = EEI (EEIAppI, e, i)
fun AscriptionTime (e, i) = EEI (EEIAscriptionTime, e, i)
fun Never (t, r) = ET (ETNever, t, r)
fun Builtin (t, r) = ET (ETBuiltin, t, r)
  
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
                      
fun collect_UniI t =
  case t of
      UniI (s, Bind ((name, _), t), _) =>
      let val (binds, t) = collect_UniI t
      in
        ((name, s) :: binds, t)
      end
    | _ => ([], t)

fun collect_Uni t =
  case t of
      Uni (Bind (name, t), _) =>
      let val (names, t) = collect_Uni t
      in
        (name :: names, t)
      end
    | Mono t => ([], t)

fun collect_AppI e =
  case e of
      EEI (EBAppI, e, i) =>
      let 
        val (e, is) = collect_AppI e
      in
        (e, is @ [i])
      end
    | _ => (e, [])

fun collect_BinOpI_left opr i =
  case i of
      BinOpI (opr', i1, i2) =>
      if opr' = opr then
        collect_BinOpI_left opr i1 @ [i2]
      else [i]
    | _ => [i]
             
fun collect_Pair e =
  case e of
      BinOp (EBPair, e1, e2) =>
      collect_Pair e1 @ [e2]
    | _ => [e]
             
fun collect_BinOpI opr i =
  case i of
      BinOpI (opr', i1, i2) =>
      if opr' = opr then
        collect_BinOpI opr i1 @ collect_BinOpI opr i2
      else [i]
    | _ => [i]
             
fun collect_BinConn opr i =
  case i of
      BinConn (opr', i1, i2) =>
      if opr' = opr then
        collect_BinConn opr i1 @ collect_BinConn opr i2
      else [i]
    | _ => [i]
             
fun collect_IApp i =
  case collect_BinOpI_left IApp i of
      f :: args => (f, args)
    | [] => raise Impossible "collect_IApp(): null"
                  
val collect_AddI_left = collect_BinOpI_left AddI
                                            
val collect_AddI = collect_BinOpI AddI
val collect_MultI = collect_BinOpI MultI
                                   
val collect_And = collect_BinConn And

fun combine_AddI zero is = foldl' (fn (i, acc) => acc %+ i) zero is
fun combine_AddI_Time is = combine_AddI (T0 dummy) is
fun combine_AddI_Nat is = combine_AddI (N0 dummy) is
fun combine_AddI_nonempty i is = combine_AddI_Time (i :: is)
fun combine_MultI is = foldl' (fn (i, acc) => acc %* i) (T1 dummy) is
                              
fun collect_IAbs i =
  case i of
      IAbs (b, Bind ((name, _), i), _) =>
      let
        val (bs_names, i) = collect_IAbs i
      in
        ((b, name) :: bs_names, i)
      end
    | _ => ([], i)

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

type 'mtype constr = var(*family*) * (unit, string, 'mtype constr_core) tbinds
(* type 'mtype constr = var(*family*) * string list(*type argument names*) * 'mtype constr_core *)
val VarT = MtVar
fun constr_type VarT shiftx_long_id ((family, tbinds) : mtype constr) = 
  let
    val (tname_kinds, ibinds) = unfold_binds tbinds
    val tnames = map fst tname_kinds
    val (ns, (t, is)) = unfold_binds ibinds
    val ts = map (fn x => VarT (NONE, (x, dummy))) $ rev $ range $ length tnames
    val t2 = AppV (shiftx_long_id 0 (length tnames) family, ts, is, dummy)
    val t = Arrow (t, T0 dummy, t2)
    val t = foldr (fn ((name, s), t) => UniI (s, Bind ((name, dummy), t), dummy)) t ns
    val t = Mono t
    val t = foldr (fn (name, t) => Uni (Bind ((name, dummy), t), dummy)) t tnames
  in
    t
  end

fun get_constr_inames (core : mtype constr_core) =
  let
    val (name_sorts, _) = unfold_binds core
  in
    map fst name_sorts
  end
                                 
(* equality test *)
    
fun eq_option eq (a, a') =
  case (a, a') of
      (SOME v, SOME v') => eq (v, v')
    | (NONE, NONE) => true
    | _ => false

fun eq_id ((x, _), (x', _)) =
  eq_v (x, x')

fun eq_name ((s, _) : name, (s', _)) = s = s'
  
fun eq_long_id ((m, x) : long_id, (m', x')) =
  eq_option eq_name (m, m') andalso eq_id (x, x')
                                        
fun eq_bs bs bs' =
  case bs of
      Base b =>
      (case bs' of Base b' => b = b' | _ => false)
    | BSArrow (s1, s2) =>
      (case bs' of
           BSArrow (s1', s2') => eq_bs s1 s1' andalso eq_bs s2 s2'
         | _ => false
      )
    | UVarBS u => (case bs' of UVarBS u' => eq_uvar_bs (u, u') | _ => false)

fun eq_i i i' =
  let
    fun loop i i' =
      case i of
          VarI x => (case i' of VarI x' => eq_long_id (x, x') | _ => false)
        | IConst (c, _) => (case i' of IConst (c', _) => c = c' | _ => false)
        | UnOpI (opr, i, _) => (case i' of UnOpI (opr', i', _) => opr = opr' andalso loop i i' | _ => false)
        | BinOpI (opr, i1, i2) => (case i' of BinOpI (opr', i1', i2') => opr = opr' andalso loop i1 i1' andalso loop i2 i2' | _ => false)
        | Ite (i1, i2, i3, _) => (case i' of Ite (i1', i2', i3', _) => loop i1 i1' andalso loop i2 i2' andalso loop i3 i3' | _ => false)
        | IAbs (b, Bind (_, i), _) => (case i' of IAbs (b', Bind (_, i'), _) => eq_bs b b' andalso loop i i'
                                                | _ => false)
        | UVarI (u, _) => (case i' of UVarI (u', _) => eq_uvar_i (u, u') | _ => false)
  in
    loop i i'
  end

fun eq_quan q q' =
  case q of
      Forall => (case q' of Forall => true | Exists _ => false)
    | Exists _ => (case q' of Forall => false | Exists _ => true)
                    
fun eq_p p p' =
  case p of
      PTrueFalse (b, _) => (case p' of PTrueFalse (b', _) => b = b' | _ => false)
    | BinConn (opr, p1, p2) => (case p' of BinConn (opr', p1', p2') => opr = opr' andalso eq_p p1 p1' andalso eq_p p2 p2' | _ => false)
    | BinPred (opr, i1, i2) => (case p' of BinPred (opr', i1', i2') => opr = opr' andalso eq_i i1 i1' andalso eq_i i2 i2' | _ => false)
    | Not (p, _) => (case p' of Not (p', _) => eq_p p p' | _ => false)
    | Quan (q, bs, Bind (_, p), _) => (case p' of Quan (q', bs', Bind (_, p'), _) => eq_quan q q' andalso eq_bs bs bs' andalso eq_p p p' | _ => false)

fun eq_s s s' =
  case s of
      Basic (b, _) =>
      (case s' of
           Basic (b', _) => eq_bs b b'
         | _ => false
      )
    | Subset ((b, _), Bind (_, p), _) =>
      (case s' of
           Subset ((b', _), Bind (_, p'), _) => eq_bs b b' andalso eq_p p p'
         | _ => false
      )
    | UVarS (x, _) =>
      (case s' of
           UVarS (x', _) => eq_uvar_s (x, x')
         | _ => false
      )
    | SAbs (s1, Bind (_, s), _) =>
      (case s' of
           SAbs (s1', Bind (_, s'), _) => eq_bs s1 s1' andalso eq_s s s'
         | _ => false
      )
    | SApp (s, i) =>
      (case s' of
           SApp (s', i') => eq_s s s' andalso eq_i i i'
         | _ => false
      )
                                                             
fun eq_ls eq (ls1, ls2) = length ls1 = length ls2 andalso List.all eq $ zip (ls1, ls2)
                                                              
fun eq_k ((n, sorts) : kind) (n', sorts') =
  n = n' andalso eq_ls (uncurry eq_bs) (sorts, sorts')
  
fun eq_mt t t' = 
    case t of
	Arrow (t1, i, t2) =>
        (case t' of
	     Arrow (t1', i', t2') => eq_mt t1 t1' andalso eq_i i i' andalso eq_mt t2 t2'
           | _ => false
        )
      | TyNat (i, r) =>
        (case t' of
             TyNat (i', _) => eq_i i i'
           | _ => false
        )
      | TyArray (t, i) =>
        (case t' of
             TyArray (t', i') => eq_mt t t' andalso eq_i i i'
           | _ => false
        )
      | Unit r =>
        (case t' of
             Unit _ => true
           | _ => false
        )
      | Prod (t1, t2) =>
        (case t' of
             Prod (t1', t2') => eq_mt t1 t1' andalso eq_mt t2 t2'
           | _ => false
        )
      | UniI (s, Bind (_, t), r) =>
        (case t' of
             UniI (s', Bind (_, t'), _) => eq_s s s' andalso eq_mt t t'
           | _ => false
        )
      | MtVar x =>
        (case t' of
             MtVar x' => eq_long_id (x, x')
           | _ => false
        )
      | MtAbs (k, Bind (_, t), r) =>
        (case t' of
             MtAbs (k', Bind (_, t'), _) => eq_k k k' andalso eq_mt t t'
           | _ => false
        )
      | MtApp (t1, t2) =>
        (case t' of
             MtApp (t1', t2') => eq_mt t1 t1' andalso eq_mt t2 t2'
           | _ => false
        )
      | MtAbsI (s, Bind (_, t), r) =>
        (case t' of
             MtAbsI (s', Bind (_, t'), _) => eq_bs s s' andalso eq_mt t t'
           | _ => false
        )
      | MtAppI (t, i) =>
        (case t' of
             MtAppI (t', i') => eq_mt t t' andalso eq_i i i'
           | _ => false
        )
      | BaseType (a : base_type, r) =>
        (case t' of
             BaseType (a' : base_type, _)  => eq_base_type (a, a')
           | _ => false
        )
      | UVar (x, _) =>
        (case t' of
             UVar (x', _) => eq_uvar_mt (x, x')
           | _ => false
        )
      | TDatatype _ => raise Unimpl "eq_mt()/TDatatype"

(* pretty-printers *)

type scontext = string list
type kcontext = string list 
type ccontext = string list
type tcontext = string list
type context = scontext * kcontext * ccontext * tcontext
type sigcontext = (string * context) list
                                     
fun is_time_fun b =
  case b of
      Base Time => SOME 0
    | BSArrow (Base Nat, b) =>
      opt_bind (is_time_fun b) (fn n => opt_return $ 1 + n)
    | _ => NONE
             
fun str_bs (s : bsort) =
  case s of
      Base s => str_b s
    | BSArrow (s1, s2) =>
      let
        fun default () = sprintf "($ => $)" [str_bs s1, str_bs s2]
      in
        case is_time_fun s of
            SOME n => if n = 0 then "Time" else sprintf "(Fun $)" [str_int n]
          | NONE => default ()
      end
    | UVarBS u => str_uvar_bs str_bs u

fun str_raw_option f a = case a of SOME a => sprintf "SOME ($)" [f a] | NONE => "NONE"

fun str_raw_id (x, _) = str_raw_v x

fun str_raw_name (s, _) = s

fun str_raw_long_id (m, x) = sprintf "($, $)" [str_raw_option str_raw_name m, str_raw_id x]
                       
fun str_raw_bind f (Bind (_, a)) = sprintf "Bind ($)" [f a]

fun str_raw_bs b =
  case b of
      Base s => sprintf "Base ($)" [str_b s]
    | BSArrow (s1, s2) => sprintf "BSArrow ($, $)" [str_raw_bs s1, str_raw_bs s2]
    | UVarBS u => "UVarBS"

fun str_raw_i i =
  case i of
      VarI x => sprintf "VarI ($)" [str_raw_long_id x]
    | IConst (c, _) => sprintf "IConst ($)" [str_idx_const c]
    | UnOpI (opr, i, _) => sprintf "UnOpI ($, $)" [str_idx_un_op opr, str_raw_i i]
    | BinOpI (opr, i1, i2) => sprintf "BinOpI ($, $, $)" [str_idx_bin_op opr, str_raw_i i1, str_raw_i i2]
    | Ite (i1, i2, i3, _) => sprintf "Ite ($, $, $)" [str_raw_i i1, str_raw_i i2, str_raw_i i3]
    | IAbs (b, bind, _) => sprintf "IAbs ($, $)" [str_bs b, str_raw_bind str_raw_i bind]
    | UVarI (u, _) => str_uvar_i (str_bs, str_raw_i) u

fun str_raw_s s =
  case s of
      Basic (b, _) => sprintf "Basic ($)" [str_bs b]
    | _ => "<sort>"
                    
fun str_raw_k k = "<kind>"

fun str_raw_mt (t : mtype) : string =
  case t of
      Arrow (t1, i, t2) => sprintf "Arrow ($, $, $)" [str_raw_mt t1, str_raw_i i, str_raw_mt t2]
    | TyNat (i, _) => sprintf "TyNat ($))" [str_raw_i i]
    | TyArray (t, i) => sprintf "TyArray ($, $)" [str_raw_mt t, str_raw_i i]
    | Unit _ => "Unit"
    | Prod (t1, t2) => sprintf "Prod ($, $)" [str_raw_mt t1, str_raw_mt t2]
    | UniI (s, bind, _) => sprintf "UniI ($, $)" ["<sort>", str_raw_bind str_raw_mt bind]
    | MtVar x => sprintf "MtVar ($)" [str_raw_long_id x]
    | MtApp (t1, t2) => sprintf "MtApp ($, $)" [str_raw_mt t1, str_raw_mt t2]
    | MtAbs (k, bind, _) => sprintf "MtAbs ($, $)" ["<kind>", str_raw_bind str_raw_mt bind]
    | MtAppI (t, i) => sprintf "MtAppI ($, $)" [str_raw_mt t, str_raw_i i]
    | MtAbsI (s, bind, _) => sprintf "MtAbsI ($, $)" ["<sort>", str_raw_bind str_raw_mt bind]
    | BaseType (bt, _) => sprintf "BaseType ($)" [str_bt bt]
    | UVar (u, _) => sprintf "UVar ($)" [str_uvar_mt (str_raw_bs, str_raw_k, str_raw_mt) u]
    | TDatatype (dt, _) => "TDatatype (...)"

fun str_raw_t (t : ty) : string =
  case t of
      Mono t => str_raw_mt t
    | Uni (t, _) => sprintf "Uni ($)" [str_raw_bind str_raw_t t]

fun str_expr_EI opr =
  case opr of
      EEIAppI => "EEIAppI"
    | EEIAscriptionTime => "EEIAscTime"

fun str_raw_e e =
  case e of
      AppConstr _ => "AppConstr (...)"
    | BinOp _ => "BinOp (...)"
    | EEI (opr, e, i) => sprintf "EEI ($, $, $)" [str_expr_EI opr, str_raw_e e, str_raw_i i]
    | _ => "<exp>"

fun str_i gctx ctx (i : idx) : string =
  let
    val str_i = str_i gctx
  in
    (* case is_IApp_UVarI i of *)
    (*     SOME ((x, _), args) => sprintf "($ ...)" [str_uvar_i (str_bs, str_i []) x] *)
    (*   | NONE => *)
    case i of
        VarI x => str_long_id #1 gctx ctx x
      | IConst (c, _) => str_idx_const c
      | UnOpI (opr, i, _) =>
        (case opr of
             IUDiv n => sprintf "($ / $)" [str_i ctx i, str_int n]
           | IUExp s => sprintf "($ ^ $)" [str_i ctx i, s]
           | _ => sprintf "($ $)" [str_idx_un_op opr, str_i ctx i]
        )
      | BinOpI (opr, i1, i2) =>
        (case opr of
             IApp =>
             let
               val (f, is) = collect_IApp i
               val is = f :: is
             in
               sprintf "($)" [join " " $ map (str_i ctx) $ is]
             end
           | AddI =>
             let
               val is = collect_AddI_left i
             in
               sprintf "($)" [join " + " $ map (str_i ctx) is]
             end
           | _ => sprintf "($ $ $)" [str_i ctx i1, str_idx_bin_op opr, str_i ctx i2]
        )
      | Ite (i1, i2, i3, _) => sprintf "(ite $ $ $)" [str_i ctx i1, str_i ctx i2, str_i ctx i3]
      | IAbs _ =>
        let
          val (bs_names, i) = collect_IAbs i
          val names = map snd bs_names
        in
          sprintf "(fn $ => $)" [join " " $ map (fn (b, name) => sprintf "($ : $)" [name, str_bs b]) bs_names, str_i (rev names @ ctx) i]
        end
      (* | IAbs ((name, _), i, _) => sprintf "(fn $ => $)" [name, str_i (name :: ctx) i] *)
      | UVarI (u, _) => str_uvar_i (str_bs, str_i []) u
  end

fun str_p gctx ctx p =
  let
    val str_p = str_p gctx
  in
    case p of
        PTrueFalse (b, _) => str_bool b
      | Not (p, _) => sprintf "(~ $)" [str_p ctx p]
      | BinConn (opr, p1, p2) => sprintf "($ $ $)" [str_p ctx p1, str_bin_conn opr, str_p ctx p2]
      (* | BinPred (BigO, i1, i2) => sprintf "($ $ $)" [str_bin_pred BigO, str_i ctx i1, str_i ctx i2] *)
      | BinPred (opr, i1, i2) => sprintf "($ $ $)" [str_i gctx ctx i1, str_bin_pred opr, str_i gctx ctx i2]
      | Quan (q, bs, Bind ((name, _), p), _) => sprintf "($ ($ : $) $)" [str_quan q, name, str_bs bs, str_p (name :: ctx) p]
  end

fun str_s gctx ctx (s : sort) : string =
  let
    val str_s = str_s gctx
  in
    (* case is_SApp_UVarS s of *)
    (*     SOME ((x, _), args) => sprintf "($ ...)" [str_uvar_s (str_s []) x] *)
    (*   | NONE => *)
    case s of
        Basic (bs, _) => str_bs bs
      | Subset ((bs, _), Bind ((name, _), p), _) =>
        let
          fun default () = sprintf "{ $ : $ | $ }" [name, str_bs bs, str_p gctx (name :: ctx) p]
        in
          case (is_time_fun bs, p) of
              (SOME arity, BinPred (BigO, VarI x, i2)) =>
              if str_long_id #1 gctx (name :: ctx) x = name then
                sprintf "BigO $ $" [str_int arity, str_i gctx (name :: ctx) i2]
              else
                default ()
            | _ => default ()
        end
      | UVarS (u, _) => str_uvar_s (str_s []) u
      | SAbs (s1, Bind ((name, _), s), _) =>
        sprintf "(fn $ : $ => $)" [name, str_bs s1, str_s (name :: ctx) s]
      | SApp (s, i) => sprintf "($ $)" [str_s ctx s, str_i gctx ctx i]
  end

datatype 'a bind = 
         KindingT of string
         | SortingT of string * 'a

fun collect_Uni_UniI t =
  let
    val (tnames, t) = collect_Uni t
    val tnames = map fst tnames
    val (binds, t) = collect_UniI t
  in
    (map KindingT tnames @ map SortingT binds, t)
  end

fun str_tbinds gctx ctx binds =
  let
    fun f (bind, (acc, (sctx, kctx))) =
      case bind of
          KindingT name => (KindingT name :: acc, (sctx, name :: kctx))
        | SortingT (name, s) => (SortingT (name, str_s gctx sctx s) :: acc, (name :: sctx, kctx))
    val (binds, ctx) = foldl f ([], ctx) binds
    val binds = rev binds
  in
    (binds, ctx)
  end
    
fun str_sortings gctx ctx binds =
  let val (binds, ctx) = str_tbinds gctx (ctx, []) (map SortingT binds)
      fun f bind = case bind of SortingT p => p | _ => raise Impossible "str_tbinds shouldn't return Kinding"
      val binds = map f binds
  in
    (binds, fst ctx)
  end

(* val str_Type = "*" *)
val str_Type = "Type"
                 
fun str_k ((n, sorts) : kind) : string =
  if n = 0 andalso null sorts then str_Type
  else
    sprintf "($$$)" [if n = 0 then "" else join " => " (repeat n str_Type) ^ " => ", if null sorts then "" else join " => " (map str_bs sorts) ^ " => ", str_Type]

fun str_mt gctx (ctx as (sctx, kctx)) (t : mtype) : string =
  let
    val str_mt = str_mt gctx
    fun collect_MtAppI_or_MtApp t =
      case t of
          MtAppI (t, i) =>
          let 
            val (f, args) = collect_MtAppI_or_MtApp t
          in
            (f, args @ [inl i])
          end
        | MtApp (t, arg) =>
          let 
            val (f, args) = collect_MtAppI_or_MtApp t
          in
            (f, args @ [inr arg])
          end
        | _ => (t, [])
    fun map_sum (f_l, f_r) a =
      case a of
          inl v => f_l v
        | inr v => f_r v
    fun str_apps t = 
      let
        val (f, args) = collect_MtAppI_or_MtApp t
      in
        sprintf "($$)" [str_mt ctx f, join_prefix " " $ map (map_sum (str_i gctx sctx, str_mt ctx)) $ args]
      end
    fun collect_MtAbsI_or_MtAbs t =
      case t of
          MtAbsI (s, Bind ((name, _), t), _) =>
          let
            val (binds, t) = collect_MtAbsI_or_MtAbs t
          in
            ((inl s, name) :: binds, t)
          end
        | MtAbs (k, Bind ((name, _), t), _) =>
          let
            val (binds, t) = collect_MtAbsI_or_MtAbs t
          in
            ((inr k, name) :: binds, t)
          end
        | _ => ([], t)
    fun str_abs t =
      let
        val (binds, t) = collect_MtAbsI_or_MtAbs t
        (* val () = println $ str_int (length binds) *)
        fun iter ((c, name), (acc, (sctx, kctx))) =
          case c of
              inl s => (sprintf "{$ : $}" [name, str_bs s(* "..." *)] :: acc, (name :: sctx, kctx))
            | inr k => (sprintf "[$ : $]" [name, str_k k] :: acc, (sctx, name :: kctx))
        val (binds, (sctx, kctx)) = foldl iter ([], (sctx, kctx)) binds
        val binds = rev binds
        (* val () = println $ str_int (length binds) *)
        val t = str_mt (sctx, kctx) t
      in
        sprintf "(fn$ => $)" [join_prefix " " binds, t]
      end
  in
    (* case is_MtApp_UVar t of *)
    (*     SOME ((x, _), i_args, t_args) => sprintf "($ ...)" [str_uvar_mt (str_raw_bs, str_raw_k, str_mt ([], [])) x] *)
    (*   | NONE => *)
    case t of
        Arrow (t1, d, t2) =>
        if eq_i d (T0 dummy) then
          sprintf "($ -> $)" [str_mt ctx t1, str_mt ctx t2]
        else
          sprintf "($ -- $ --> $)" [str_mt ctx t1, str_i gctx sctx d, str_mt ctx t2]
      | TyNat (i, _) => sprintf "(nat $)" [str_i gctx sctx i]
      | TyArray (t, i) => sprintf "(arr $ $)" [str_mt ctx t, str_i gctx sctx i]
      | Unit _ => "unit"
      | Prod (t1, t2) => sprintf "($ * $)" [str_mt ctx t1, str_mt ctx t2]
      | UniI _ =>
        let
          val (binds, t) = collect_UniI t
        in
          str_uni gctx ctx (map SortingT binds, t)
        end
      | MtVar x => str_long_id #2 gctx kctx x
      | MtApp (t1, t2) =>
      (* sprintf "($ $)" [str_mt ctx t1, str_mt ctx t2] *)
        str_apps t
      | MtAbs _ =>
      (* sprintf "(fn [$ : $] => $)" [name, str_k gctx sctx k, str_mt (sctx, name :: kctx) t] *)
        str_abs t
      | MtAppI _ =>
      (* sprintf "($ {$})" [str_mt ctx t, str_i gctx sctx i] *)
        str_apps t
      | MtAbsI _ =>
        (* sprintf "(fn {$ : $} => $)" [name, str_s gctx sctx s, str_mt (name :: sctx, kctx) t] *)
        str_abs t
      | BaseType (bt, _) => str_bt bt
      | UVar (u, r) =>
        let
          fun str_region ((left, right) : region) = sprintf "($,$)-($,$)" [str_int (#line left), str_int (#col left), str_int (#line right), str_int (max (#col right) 0)]
        in
          (* (surround "[" "] " $ str_region r) ^ *) str_uvar_mt (str_raw_bs, str_raw_k, str_mt ([], [])) u
        end
      | TDatatype (dt, _) => "(datatype ...)"
  end

and str_uni gctx ctx (binds, t) =
    let 
      val (binds, ctx) = str_tbinds gctx ctx binds
      fun f bind =
        case bind of
            KindingT name => name
          | SortingT (name, s) => sprintf "{$ : $}" [name, s]
      val binds = map f binds
    in
      sprintf "(forall$, $)" [join_prefix " " binds, str_mt gctx ctx t]
    end
      
fun str_t gctx (ctx as (sctx, kctx)) (t : ty) : string =
  case t of
      Mono t => str_mt gctx ctx t
    | Uni _ => str_uni gctx ctx (collect_Uni_UniI t)

fun ptrn_names pn : string list * string list =
  case pn of
      ConstrP (_, inames, pn, _) =>
      let 
        (* val () = println "ConstrP" *)
        val (inames', enames) = ptrn_names pn
      in
        (inames' @ rev inames, enames)
      end
    | VarP (name, _) =>
      let
        (* val () = println $ sprintf "VarP: $" [name] *)
      in
        ([], [name])
      end
    | PairP (pn1, pn2) =>
      let val (inames1, enames1) = ptrn_names pn1
          val (inames2, enames2) = ptrn_names pn2
      in
        (inames2 @ inames1, enames2 @ enames1)
      end
    | TTP _ =>
      ([], [])
    | AliasP ((name, _), pn, _) =>
      let val (inames, enames) = ptrn_names pn
      in
        (inames, enames @ [name])
      end
    | AnnoP (pn, t) => ptrn_names pn

fun decorate_var eia s = (if eia then "@" else "") ^ s
                                                       
fun str_pn gctx (ctx as (sctx, kctx, cctx)) pn =
  let
    val str_pn = str_pn gctx
  in
    case pn of
        ConstrP (((x, _), eia), inames, pn, _) => sprintf "$$$" [decorate_var eia $ str_long_id #3 gctx cctx x, join_prefix " " $ map (surround "{" "}") inames, " " ^ str_pn ctx pn]
      | VarP (name, _) => name
      | PairP (pn1, pn2) => sprintf "($, $)" [str_pn ctx pn1, str_pn ctx pn2]
      | TTP _ => "()"
      | AliasP ((name, _), pn, _) => sprintf "$ as $" [name, str_pn ctx pn]
      | AnnoP (pn, t) => sprintf "($ : $)" [str_pn ctx pn, str_mt gctx (sctx, kctx) t]
  end

fun str_return gctx (skctx as (sctx, _)) return =
  case return of
      (NONE, NONE) => ""
    | (SOME t, NONE) => sprintf "return $ " [str_mt gctx skctx t]
    | (NONE, SOME d) => sprintf "return using $ " [str_i gctx sctx d]
    | (SOME t, SOME d) => sprintf "return $ using $ " [str_mt gctx skctx t, str_i gctx sctx d]

fun add_sorting name (sctx, kctx, cctx, tctx) = (name :: sctx, kctx, cctx, tctx)
fun add_kinding name (sctx, kctx, cctx, tctx) = (sctx, name :: kctx, cctx, tctx)
fun add_typing name (sctx, kctx, cctx, tctx) = (sctx, kctx, cctx, name :: tctx)
fun add_ctx (sctxd, kctxd, cctxd, tctxd) (sctx, kctx, cctx, tctx) =
  (sctxd @ sctx, kctxd @ kctx, cctxd @ cctx, tctxd @ tctx)
    
fun str_e gctx (ctx as (sctx, kctx, cctx, tctx)) (e : expr) : string =
  let
    val str_e = str_e gctx
    fun add_t name (sctx, kctx, cctx, tctx) = (sctx, kctx, cctx, name :: tctx) 
    val skctx = (sctx, kctx) 
  in
    case e of
	Var (x, b) => decorate_var b $ str_long_id #4 gctx tctx x
      | EConst (c, _) =>
        (case c of
             ECTT => "()"
           | ECInt n => str_int n
           | ECNat n => sprintf "#$" [str_int n]
        )
      | EUnOp (opr, e, _) =>
        (case opr of
             EUFst => sprintf "(fst $)" [str_e ctx e]
           | EUSnd => sprintf "(snd $)" [str_e ctx e]
        )
      | BinOp (opr, e1, e2) =>
        (case opr of
             EBApp => sprintf "($ $)" [str_e ctx e1, str_e ctx e2]
           | EBPair =>
             let
               val es = collect_Pair e
             in
               sprintf "($)" [join ", " $ map (str_e ctx) es]
             end
           | New => sprintf "(new $ $)" [str_e ctx e1, str_e ctx e2]
           | Read => sprintf "(read $ $)" [str_e ctx e1, str_e ctx e2]
           | Add => sprintf "($ $ $)" [str_e ctx e1, str_bin_op opr, str_e ctx e2]
        )
      | TriOp (Write, e1, e2, e3) => sprintf "(write $ $ $)" [str_e ctx e1, str_e ctx e2, str_e ctx e3]
      | EEI (opr, e, i) =>
        (case opr of
           EEIAppI => sprintf "($ {$})" [str_e ctx e, str_i gctx sctx i]
          | EEIAscriptionTime => sprintf "($ |> $)" [str_e ctx e, str_i gctx sctx i]
        )
      | ET (opr, t, _) =>
        (case opr of
             ETNever => sprintf "(never [$])" [str_mt gctx skctx t]
           | ETBuiltin => sprintf "(builtin [$])" [str_mt gctx skctx t]
        )
      | Abs (pn, e) => 
        let 
          val (inames, enames) = ptrn_names pn
          val pn = str_pn gctx (sctx, kctx, cctx) pn
          val ctx = (inames @ sctx, kctx, cctx, enames @ tctx)
	  val e = str_e ctx e
        in
          sprintf "(fn $ => $)" [pn, e]
        end
      | AbsI (s, Bind ((name, _), e), _) => sprintf "(fn {$ : $} => $)" [name, str_s gctx sctx s, str_e (name :: sctx, kctx, cctx, tctx) e]
      | Let (return, decls, e, _) => 
        let
          val return = str_return gctx (sctx, kctx) return
          val (decls, ctx) = str_decls gctx ctx decls
        in
          sprintf "let $$ in $ end" [return, join_prefix " " decls, str_e ctx e]
        end
      | Ascription (e, t) => sprintf "($ : $)" [str_e ctx e, str_mt gctx skctx t]
      | AppConstr ((x, b), is, e) => sprintf "($$ $)" [decorate_var b $ str_long_id #3 gctx cctx x, (join "" o map (prefix " ") o map (fn i => sprintf "{$}" [str_i gctx sctx i])) is, str_e ctx e]
      | Case (e, return, rules, _) => sprintf "(case $ $of $)" [str_e ctx e, str_return gctx skctx return, join " | " (map (str_rule gctx ctx) rules)]
  end

and str_decls gctx (ctx as (sctx, kctx, cctx, tctx)) decls =
    let
      fun f (decl, (acc, ctx)) =
        let val (s, ctx) = str_decl gctx ctx decl
        in
          (s :: acc, ctx)
        end
      val (decls, ctx) = foldl f ([], ctx) decls
      val decls = rev decls
    in
      (decls, ctx)
    end
      
and str_decl gctx (ctx as (sctx, kctx, cctx, tctx)) decl =
    let
      val str_decl = str_decl gctx
    in
      case decl of
          Val (tnames, pn, e, _) =>
          let 
            val ctx' as (sctx', kctx', cctx', _) = (sctx, (rev o map fst) tnames @ kctx, cctx, tctx)
            val tnames = (join "" o map (fn nm => sprintf " [$]" [nm]) o map fst) tnames
            val (inames, enames) = ptrn_names pn
            val pn = str_pn gctx (sctx', kctx', cctx') pn
            val e = str_e gctx ctx' e
	    val ctx = (inames @ sctx, kctx, cctx, enames @ tctx)
          in
            (sprintf "val$ $ = $" [tnames, pn, e], ctx)
          end
        | Rec (tnames, (name, _), (binds, ((t, d), e)), _) =>
          let 
	    val ctx as (sctx, kctx, cctx, tctx) = (sctx, kctx, cctx, name :: tctx)
            val ctx_ret = ctx
            val ctx as (sctx, kctx, cctx, tctx) = (sctx, (rev o map fst) tnames @ kctx, cctx, tctx)
            val tnames = (join "" o map (fn nm => sprintf " [$]" [nm]) o map fst) tnames
            fun f (bind, (binds, ctx as (sctx, kctx, cctx, tctx))) =
              case bind of
                  SortingST ((name, _), s) => 
                  (sprintf "{$ : $}" [name, str_s gctx sctx s] :: binds, (name :: sctx, kctx, cctx, tctx))
                | TypingST pn =>
                  let
                    val (inames, enames) = ptrn_names pn
                  in
                    (str_pn gctx (sctx, kctx, cctx) pn :: binds, (inames @ sctx, kctx, cctx, enames @ tctx))
                  end
            val (binds, ctx as (sctx, kctx, cctx, tctx)) = foldl f ([], ctx) binds
            val binds = rev binds
            val binds = (join "" o map (prefix " ")) binds
            val t = str_mt gctx (sctx, kctx) t
            val d = str_i gctx sctx d
            val e = str_e gctx ctx e
          in
            (sprintf "rec$ $$ : $ |> $ = $" [tnames, name, binds, t, d, e], ctx_ret)
          end
        | Datatype (Bind (name, tbinds), _) =>
          let
            val (tname_kinds, (sorts, constrs)) = unfold_binds tbinds
            val tnames = map fst tname_kinds
            val str_tnames = (join_prefix " " o rev) tnames
            fun str_constr_decl (cname, ibinds, _) =
              let 
                val (name_sorts, (t, idxs)) = unfold_binds ibinds
                val (name_sorts, sctx') = str_sortings gctx sctx name_sorts
                val name_sorts = map (fn (nm, s) => sprintf "$ : $" [nm, s]) name_sorts
              in
                sprintf "$ of$ $ ->$$ $" [cname, (join_prefix " " o map (surround "{" "}")) name_sorts, str_mt gctx (sctx', rev tnames @ name :: kctx) t, (join_prefix " " o map (surround "{" "}" o str_i gctx sctx') o rev) idxs, str_tnames, name]
              end
            val s = sprintf "datatype$$ $ = $" [(join_prefix " " o map (surround "{" "}" o str_bs) o rev) sorts, str_tnames, name, join " | " (map str_constr_decl constrs)]
            val cnames = map #1 constrs
            val ctx = (sctx, name :: kctx, rev cnames @ cctx, tctx)
          in
            (s, ctx)
          end
        | IdxDef ((name, r), s, i) =>
          (sprintf "idx $ : $ = $" [name, str_s gctx sctx s, str_i gctx sctx i], (name :: sctx, kctx, cctx, tctx))
        | AbsIdx2 ((name, r), s, i) =>
          (sprintf "absidx $ : $ = $" [name, str_s gctx sctx s, str_i gctx sctx i], (name :: sctx, kctx, cctx, tctx))
        | AbsIdx (((name, r1), s, i), decls, _) =>
          let
            val ctx' = (name :: sctx, kctx, cctx, tctx)
            val (decls, ctx') = str_decls gctx ctx' decls
          in
            (sprintf "absidx $ : $ = $ with$ end" [name, str_s gctx sctx s, str_i gctx sctx i, join_prefix " " decls], ctx')
          end
        | TypeDef ((name, _), t) =>
          (sprintf "type $ = $" [name, str_mt gctx (sctx, kctx) t], add_kinding name ctx)
        | Open ((m, r), _) =>
          let
            val (m, ctxd) = lookup_module gctx m
            val ctx = add_ctx ctxd ctx
          in
            (sprintf "open $" [m], ctx)
          end
    end
      
and str_rule gctx (ctx as (sctx, kctx, cctx, tctx)) (pn, e) =
    let val (inames, enames) = ptrn_names pn
	val ctx' = (inames @ sctx, kctx, cctx, enames @ tctx)
    in
      sprintf "$ => $" [str_pn gctx (sctx, kctx, cctx) pn, str_e gctx ctx' e]
    end

(* region calculations *)

fun get_region_long_id (m, (_, r)) =
  case m of
      NONE => r
    | SOME (_, r1) => combine_region r1 r

fun set_region_long_id (m, (x, _)) r = (Option.map (fn (m, _) => (m, r)) m, (x, r))
                                         
fun get_region_i i =
  case i of
      VarI x => get_region_long_id x
    | IConst (_, r) => r
    | UnOpI (_, _, r) => r
    | BinOpI (_, i1, i2) => combine_region (get_region_i i1) (get_region_i i2)
    | Ite (_, _, _, r) => r
    | IAbs (_, _, r) => r
    | UVarI (_, r) => r

fun set_region_i i r =
  case i of
      VarI x => VarI $ set_region_long_id x r
    | IConst (a, _) => IConst (a, r)
    | UnOpI (opr, i, _) => UnOpI (opr, i, r)
    | BinOpI (opr, i1, i2) => BinOpI (opr, set_region_i i1 r, set_region_i i2 r)
    | Ite (i1, i2, i3, _) => Ite (i1, i2, i3, r)
    | IAbs (name, i, _) => IAbs (name, i, r)
    | UVarI (a, _) => UVarI (a, r)

fun get_region_p p = 
  case p of
      PTrueFalse (_, r) => r
    | Not (_, r) => r
    | BinConn (_, p1, p2) => combine_region (get_region_p p1) (get_region_p p2)
    | BinPred (_, i1, i2) => combine_region (get_region_i i1) (get_region_i i2)
    | Quan (_, _, _, r) => r

fun set_region_p p r = 
  case p of
      PTrueFalse (b, _) => PTrueFalse (b, r)
    | Not (p, _) => Not (p, r)
    | BinConn (opr, p1, p2) => BinConn (opr, set_region_p p1 r, set_region_p p2 r)
    | BinPred (opr, i1, i2) => BinPred (opr, set_region_i i1 r, set_region_i i2 r)
    | Quan (q, bs, bind, _) => Quan (q, bs, bind, r)

fun get_region_s s = 
  case s of
      Basic (_, r) => r
    | Subset (_, _, r) => r
    | UVarS (_, r) => r
    | SAbs (_, _, r) => r
    | SApp (s, i) => combine_region (get_region_s s) (get_region_i i)

fun get_region_mt t = 
  case t of
      Arrow (t1, d, t2) => combine_region (get_region_mt t1) (get_region_mt t2)
    | TyNat (_, r) => r
    | TyArray (t, i) => combine_region (get_region_mt t) (get_region_i i)
    | Unit r => r
    | Prod (t1, t2) => combine_region (get_region_mt t1) (get_region_mt t2)
    | UniI (_, _, r) => r
    | MtVar y => get_region_long_id y
    | MtApp (t1, t2) => combine_region (get_region_mt t1) (get_region_mt t2)
    | MtAbs (_, _, r) => r
    | MtAppI (t, i) => combine_region (get_region_mt t) (get_region_i i)
    | MtAbsI (_, _, r) => r
    | BaseType (_, r) => r
    | UVar (_, r) => r
    | TDatatype (_, r) => r

fun get_region_t t = 
  case t of
      Mono t => get_region_mt t
    | Uni (_, r) => r

fun get_region_pn pn = 
  case pn of
      ConstrP (_, _, _, r) => r
    | VarP (_, r) => r
    | PairP (pn1, pn2) => combine_region (get_region_pn pn1) (get_region_pn pn2)
    | TTP r => r
    | AliasP (_, _, r) => r
    | AnnoP (pn, t) => combine_region (get_region_pn pn) (get_region_mt t)

fun get_region_e e = 
  case e of
      Var (x, _) => get_region_long_id x
    | EConst (_, r) => r
    | EUnOp (_, _, r) => r
    | BinOp (_, e1, e2) => combine_region (get_region_e e1) (get_region_e e2)
    | TriOp (_, e1, _, e3) => combine_region (get_region_e e1) (get_region_e e3)
    | EEI (_, e, i) => combine_region (get_region_e e) (get_region_i i)
    | ET (_, _, r) => r
    | Abs (pn, e) => combine_region (get_region_pn pn) (get_region_e e)
    | AbsI (_, _, r) => r
    | AppConstr ((x, _), _, e) => combine_region (get_region_long_id x) (get_region_e e)
    | Case (_, _, _, r) => r
    | Let (_, _, _, r) => r
    | Ascription (e, t) => combine_region (get_region_e e) (get_region_mt t)
                                              
fun get_region_rule (pn, e) = combine_region (get_region_pn pn) (get_region_e e)

fun get_region_dec dec =
  case dec of
      Val (_, _, _, r) => r
    | Rec (_, _, _, r) => r
    | Datatype (_, r) => r
    | IdxDef ((_, r), _, i) => combine_region r (get_region_i i)
    | AbsIdx2 ((_, r), _, i) => combine_region r (get_region_i i)
    | AbsIdx (_, _, r) => r
    | TypeDef ((_, r), t) => combine_region r $ get_region_mt t
    | Open ((_, r), _) => r

fun get_region_sig (_, r) = r

fun get_region_m m =
  case m of
      ModComponents (_, r) => r
    | ModSeal (m, sg) => combine_region (get_region_m m) (get_region_sig sg)
    | ModTransparentAscription (m, sg) => combine_region (get_region_m m) (get_region_sig sg)

fun is_value (e : expr) : bool =
  case e of
      Var _ => true
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
    | BinOp (opr, e1, e2) =>
      (case opr of
           EBApp => false
         | EBPair => is_value e1 andalso is_value e2
         | New => false
         | Read => false
         | Add => false
      )
    | TriOp _ => false
    | EEI (opr, e, i) =>
      (case opr of
           EEIAppI => false
         | EEIAscriptionTime => false
      )
    | ET (opr, t, _) =>
      (case opr of
           ETNever => true
         | ETBuiltin => true
      )
    | Abs _ => true
    | AbsI _ => true
    | Let _ => false
    | Ascription _ => false
    | AppConstr (_, _, e) => is_value e
    | Case _ => false

datatype ('var, 'prop) hyp = 
         VarH of 'var
         | PropH of 'prop
                      
fun append_hyps_vc hs vc = mapFst (fn hs' => hs' @ hs) vc
fun add_hyp_vc h vc = append_hyps_vc [h] vc
fun append_hyps hs vcs = map (append_hyps_vc hs) vcs
fun add_hyp h vcs = append_hyps [h] vcs
                                
fun prop2vc p =
  let
  in
    case p of
        Quan (Forall, bs, Bind ((name, r), p), r_all) =>
        let
          val vc = prop2vc p
          val vc = add_hyp_vc (VarH (name, (bs, r_all))) vc
        in
          vc
        end
      | BinConn (Imply, p1, p) =>
        let
          val vc = prop2vc p
          val vc = add_hyp_vc (PropH p1) vc
        in
          vc
        end
      | _ => ([], p)
  end

structure Subst = struct
open Util
open ShiftUtil
       
infixr 0 $

open LongIdUtil
       
fun on_e_ibind f x n (Bind (name, b) : ('a * 'b) ibind) = Bind (name, f x n b)
                                                               
fun on_e_e on_v =
  let
    fun f x n b =
      case b of
	  Var (y, b) => Var (on_v_long_id on_v x n y, b)
        | EConst _ => b
	| EUnOp (opr, e, r) => EUnOp (opr, f x n e, r)
	| BinOp (opr, e1, e2) => BinOp (opr, f x n e1, f x n e2)
	| TriOp (opr, e1, e2, e3) => TriOp (opr, f x n e1, f x n e2, f x n e3)
	| EEI (opr, e, i) => EEI (opr, f x n e, i)
	| ET (opr, t, r) => ET (opr, t, r)
	| Abs (pn, e) =>
          Abs (pn, f (x + (length $ snd $ ptrn_names pn)) n e)
	| AbsI (s, bind, r) => AbsI (s, on_e_ibind f x n bind, r)
	| Let (return, decs, e, r) =>
	  let 
	    val (decs, m) = f_decls x n decs
	  in
	    Let (return, decs, f (x + m) n e, r)
	  end
	| Ascription (e, t) => Ascription (f x n e, t)
	| AppConstr (cx, is, e) => AppConstr (cx, is, f x n e)
	| Case (e, return, rules, r) => Case (f x n e, return, map (f_rule x n) rules, r)

    and f_decls x n decs =
	let 
          fun g (dec, (acc, m)) =
	    let
	      val (dec, m') = f_dec (x + m) n dec
	    in
	      (dec :: acc, m' + m)
	    end
	  val (decs, m) = foldl g ([], 0) decs
	  val decs = rev decs
	in
          (decs, m)
        end

    and f_dec x n dec =
	case dec of
	    Val (tnames, pn, e, r) => 
	    let 
              val (_, enames) = ptrn_names pn 
	    in
              (Val (tnames, pn, f x n e, r), length enames)
            end
          | Rec (tnames, name, (binds, ((t, d), e)), r) => 
            let
              fun g (bind, m) =
                case bind of
                    SortingST _ => m
                  | TypingST pn =>
	            let 
                      val (_, enames) = ptrn_names pn 
	            in
                      m + length enames
                    end
              val m = foldl g 0 binds
              val e = f (x + 1 + m) n e
            in
              (Rec (tnames, name, (binds, ((t, d), e)), r), 1)
            end
          | Datatype a => (Datatype a, 0)
          | IdxDef a => (IdxDef a, 0)
          | AbsIdx2 a => (AbsIdx2 a, 0)
          | AbsIdx (a, decls, r) => 
            let
              val (decls, m) = f_decls x n decls
            in
              (AbsIdx (a, decls, r), m)
            end
          | TypeDef (name, t) => (TypeDef (name, t), 0)
          | Open (m, octx) =>
            case octx of
                NONE => raise Impossible "ctx can't be NONE"
              | SOME ctx => (Open (m, octx), length $ #4 ctx)

    and f_rule x n (pn, e) =
	let 
          val (_, enames) = ptrn_names pn 
	in
	  (pn, f (x + length enames) n e)
	end
  in
    f
  end

fun shiftx_long_id x n b = on_v_long_id shiftx_v x n b
val forget_v = forget_v ForgetError
fun forget_long_id x n b = on_v_long_id forget_v x n b
                                        
structure LongIdShift = struct
type var = long_id
val shiftx_var = shiftx_long_id
val forget_var = forget_long_id
end

structure IdxShift = IdxShiftFn (structure Idx = Idx
                                 structure ShiftableVar = LongIdShift)
open IdxShift
                                        
structure TypeShift = TypeShiftFn (structure Type = Type
                                  structure ShiftableVar = LongIdShift
                                  structure ShiftableIdx = IdxShift
                                 )
open TypeShift
                                        
(* shift *)

fun shiftx_id x n (y, r) = (shiftx_v x n y, r)
                             
(* shift_e_e *)
fun shiftx_e_e x n b = on_e_e shiftx_v x n b
fun shift_e_e b = shiftx_e_e 0 1 b

fun shiftx_i_c x n ((family, tbinds) : mtype constr) : mtype constr =
  (family,
   on_i_tbinds return3 (on_i_constr_core shiftx_i_i shiftx_i_s shiftx_i_mt) x n tbinds)

fun shift_i_c b = shiftx_i_c 0 1 b

fun shiftx_t_c x n (((m, family), tbinds) : mtype constr) : mtype constr =
  ((m, shiftx_id x n family),
   on_t_tbinds return3 (on_t_constr_core shiftx_t_mt) x n tbinds)
fun shift_t_c b = shiftx_t_c 0 1 b

(* forget *)

fun forget_e_e x n b = on_e_e forget_v x n b
                              
fun try_forget f a =
  SOME (f a) handle ForgetError _ => NONE

(* ToDo: just a hack now *)
fun forget_above_i_i x b = forget_i_i x 100000000 b

(* subst *)

exception Error of string

(* if it has the module name part, don't substitute, because this is not the variable you are targeting *)
fun substx_long_id (constr : long_id -> 'a) x (get_v : unit -> 'a) (long_id as (m, (y, r))) =
  case m of
      NONE => substx_v (fn x => constr (NONE, (x, r))) x get_v y
    | SOME _ => constr long_id
                       
(* mimic type class *)
type 'a shiftable = {
  shift_i : int -> 'a -> 'a,
  shift_t : int -> 'a -> 'a
}
(* todo: split [shiftable] to [ishiftable] and [tshiftable], or ultimately get rid of it aftering changing to lazy shifting *)                      

fun substx_pair (f1, f2) d x v (b1, b2) = (f1 d x v b1, f2 d x v b2)
fun substx_list f d x v b = map (f d x v) b
                            
fun substx_i_ibind f d x v (Bind (name, inner) : ('name * 'b) ibind) =
  Bind (name, f (d + 1) (x + 1) v inner)
       
fun substx_i_tbind f d x v (Bind (name, inner) : ('name * 'b) tbind) =
  Bind (name, f d x v inner)

fun substx_binds substx_bind f_cls f d x v b =
  let
    val substx_binds = substx_binds substx_bind f_cls f
  in
    case b of
        BindNil a => BindNil (f d x v a)
      | BindCons (cls, bind) => BindCons (f_cls d x v cls, substx_bind substx_binds d x v bind)
  end

fun substx_i_ibinds f_cls f d x v (b : ('classifier, 'name, 'inner) ibinds) = substx_binds substx_i_ibind f_cls f d x v b
                                                                                           
fun substx_i_tbinds f_cls f d x v (b : ('classifier, 'name, 'inner) tbinds) = substx_binds substx_i_tbind f_cls f d x v b
                                                                                           
(* depth [d] is used for shifting value [v] *)
local
  fun f d(*depth*) x v b =
    case b of
	VarI y => substx_long_id VarI x (fn () => shiftx_i_i 0 d v) y
      | IConst c => IConst c
      | UnOpI (opr, i, r) => UnOpI (opr, f d x v i, r)
      | BinOpI (opr, d1, d2) => BinOpI (opr, f d x v d1, f d x v d2)
      | Ite (i1, i2, i3, r) => Ite (f d x v i1, f d x v i2, f d x v i3, r)
      | IAbs (b, bind, r) => IAbs (b, substx_i_ibind f d x v bind, r)
      | UVarI a => b
in
val substx_i_i = f
fun subst_i_i v b = substx_i_i 0 0 v b
end

local
  fun f d x v b =
    case b of
	PTrueFalse b => PTrueFalse b
      | Not (p, r) => Not (f d x v p, r)
      | BinConn (opr,p1, p2) => BinConn (opr, f d x v p1, f d x v p2)
      | BinPred (opr, d1, d2) => BinPred (opr, substx_i_i d x v d1, substx_i_i d x v d2)
      | Quan (q, bs, bind, r) => Quan (q, bs, substx_i_ibind f d x v bind, r)
in
val substx_i_p = f
fun subst_i_p (v : idx) (b : prop) : prop = substx_i_p 0 0 v b
end

local
  fun f d x v b =
    case b of
	Basic s => Basic s
      | Subset (b, bind, r) => Subset (b, substx_i_ibind substx_i_p d x v bind, r)
      | UVarS a => b
      | SAbs (b, bind, r) => SAbs (b, substx_i_ibind f d x v bind, r)
      | SApp (s, i) => SApp (f d x v s, substx_i_i d x v i)
in
val substx_i_s = f
fun subst_i_s (v : idx) (b : sort) : sort = substx_i_s 0 0 v b
end

local
  fun f d x v b =
    case b of
	Arrow (t1, i, t2) => Arrow (f d x v t1, substx_i_i d x v i, f d x v t2)
      | TyNat (i, r) => TyNat (substx_i_i d x v i, r)
      | TyArray (t, i) => TyArray (f d x v t, substx_i_i d x v i)
      | Unit r => Unit r
      | Prod (t1, t2) => Prod (f d x v t1, f d x v t2)
      | UniI (s, bind, r) => UniI (substx_i_s d x v s, substx_i_ibind f d x v bind, r)
      | MtVar y => MtVar y
      | MtApp (t1, t2) => MtApp (f d x v t1, f d x v t2)
      | MtAbs (k, bind, r) => MtAbs (k, substx_i_tbind f d x v bind, r)
      | MtAppI (t, i) => MtAppI (f d x v t, substx_i_i d x v i)
      | MtAbsI (b, bind, r) => MtAbsI (b, substx_i_ibind f d x v bind, r)
      | BaseType a => BaseType a
      | UVar a => b
      | TDatatype (dt, r) =>
        let
          fun on_constr d x v b = substx_i_ibinds substx_i_s (substx_pair (f, substx_list substx_i_i)) d x v b
          fun on_constr_decl d x v (name, c, r) = (name, on_constr d x v c, r)
          val dt = substx_i_tbind (substx_i_tbinds return4 (substx_pair (return4, substx_list on_constr_decl))) d x v dt
        in
          TDatatype (dt, r)
        end
in
val substx_i_mt = f
fun subst_i_mt (v : idx) (b : mtype) : mtype = substx_i_mt 0 0 v b
end

local
  fun f d x v b =
    case b of
	Mono t => Mono (substx_i_mt d x v t)
      | Uni (bind, r) => Uni (substx_i_tbind f d x v bind, r)
in
val substx_i_t = f
fun subst_i_t (v : idx) (b : ty) : ty = substx_i_t 0 0 v b
end

fun substx_t_ibind f (di, dt) x v (Bind (name, inner) : ('name * 'b) ibind) =
  Bind (name, f (di + 1, dt) x v inner)

fun substx_t_tbind f (di, dt) x v (Bind (name, inner) : ('name * 'b) tbind) =
  Bind (name, f (di, dt + 1) (x + 1) v inner)
       
fun substx_t_ibinds f_cls f d x v (b : ('classifier, 'name, 'inner) ibinds) = substx_binds substx_t_ibind f_cls f d x v b
(* fun substx_t_ibinds f_cls f d x v b = *)
  (* case b of *)
  (*     BindNil a => BindNil (f d x v a) *)
(*   | BindCons (cls, bind) => BindCons (f_cls d x v cls, substx_t_ibind (substx_t_ibinds f_cls f) d x v bind) *)
                                                                                           
fun substx_t_tbinds f_cls f d x v (b : ('classifier, 'name, 'inner) tbinds) = substx_binds substx_t_tbind f_cls f d x v b
(* fun substx_t_tbinds f_cls f d x v b = *)
(*   case b of *)
(*       BindNil a => BindNil (f d x v a) *)
(*     | BindCons (cls, bind) => BindCons (f_cls d x v cls, substx_t_tbind (substx_t_tbinds f_cls f) d x v bind) *)


local
  fun f d x v (b : mtype) : mtype =
    case b of
	Arrow (t1, i, t2) => Arrow (f d x v t1, i, f d x v t2)
      | TyNat (i, r) => TyNat (i, r)
      | TyArray (t, i) => TyArray (f d x v t, i)
      | Unit r => Unit r
      | Prod (t1, t2) => Prod (f d x v t1, f d x v t2)
      | UniI (s, bind, r) => UniI (s, substx_t_ibind f d x v bind, r)
      | MtVar y =>
        substx_long_id MtVar x (fn () => shiftx_i_mt 0 (fst d) $ shiftx_t_mt 0 (snd d) v) y
      | MtAbs (k, bind, r) => MtAbs (k, substx_t_tbind f d x v bind, r)
      | MtApp (t1, t2) => MtApp (f d x v t1, f d x v t2)
      | MtAbsI (s, bind, r) => MtAbsI (s, substx_t_ibind f d x v bind, r)
      | MtAppI (t, i) => MtAppI (f d x v t, i)
      | BaseType a => BaseType a
      | UVar a => b
      | TDatatype (dt, r) =>
        let
          fun on_constr d x v b = substx_t_ibinds return4 (substx_pair (f, return4)) d x v b
          fun on_constr_decl d x v (name, c, r) = (name, on_constr d x v c, r)
          val dt = substx_t_tbind (substx_t_tbinds return4 (substx_pair (return4, substx_list on_constr_decl))) d x v dt
        in
          TDatatype (dt, r)
        end
in
val substx_t_mt = f
fun subst_t_mt (v : mtype) (b : mtype) : mtype = substx_t_mt (0, 0) 0 v b
fun subst_is_mt is t =
  fst (foldl (fn (i, (t, x)) => (substx_i_mt x x i t, x - 1)) (t, length is - 1) is)
fun subst_ts_mt vs b =
  fst (foldl (fn (v, (b, x)) => (substx_t_mt (0, x) x v b, x - 1)) (b, length vs - 1) vs)
end

fun substx_t_t d x (v : mtype) (b : ty) : ty =
  case b of
      Mono t => Mono (substx_t_mt d x v t)
    | Uni (bind, r) => Uni (substx_t_tbind substx_t_t d x v bind, r)
fun subst_t_t v b =
  substx_t_t (0, 0) 0 v b

(* VC operations *)

fun hyps2ctx hs = List.mapPartial (fn h => case h of VarH (name, _) => SOME name | _ => NONE) hs

fun str_hyps_conclu gctx (hyps, p) =
  let 
    fun g (h, (hyps, ctx)) =
      case h of
          VarH ((name, _), (bs, _)) => (sprintf "$ : $" [name, str_bs bs] :: hyps, name :: ctx)
        | PropH p => (str_p gctx ctx p :: hyps, ctx)
    val (hyps, ctx) = foldr g ([], []) hyps
    val hyps = rev hyps
    val p = str_p gctx ctx p
  in
    hyps @
    ["==============="] @
    [p]
  end 

fun shiftx_hyp x n hyp =
  case hyp of
      VarH _ => hyp
    | PropH p => PropH (shiftx_i_p x n p)
                       
fun shiftx_hyps x n hyps =
  case hyps of
      [] => hyps
    | hyp :: hyps =>
      let
        val d = case hyp of
                    VarH _ => 1
                  | PropH _ => 0
      in
        shiftx_hyp x n hyp :: shiftx_hyps (x + d) n hyps
      end

(* find something about [x] in [hyps]. [x] is expressed as being in the innermost of [hyps] (so [x] can see all variables in [hyps]). *)
fun find_hyp forget shift pred x hyps =
  let
    exception Error
    fun runError m _ =
      SOME (m ())
      handle
      Error => NONE
      | ForgetError _ => NONE
    fun do_forget hyp x =
      case hyp of
          VarH _ => forget x
        | PropH _ => x
    fun do_shift hyp (p as (y, hyps)) =
      case hyp of
          VarH _ => (shift y, shiftx_hyps 0 1 hyps)
        | PropH _ => p
    fun loop x hyps () =
      let
        val (hyp, hyps) = case hyps of hyp :: hyps => (hyp, hyps) | [] => raise Error
        val x = do_forget hyp x
      in
        case pred x hyps hyp of
            SOME y => do_shift hyp (y, hyps)
          | NONE => do_shift hyp (loop x hyps ())
      end
  in
    runError (loop x hyps) ()
  end
    
end
                    
structure Simp = struct

local
  open Subst
  val changed = ref false
  fun unset () = changed := false
  fun set () = changed := true
  fun mark a = (set (); a)
  fun passi i =
    let
      (* val () = println $ str_i [] [] i *)
      fun r () = get_region_i i
    in
      case i of
	  BinOpI (opr, i1, i2) =>
          let
            fun def () = BinOpI (opr, passi i1, passi i2)
          in
            case opr of
	        MaxI =>
	        if eq_i i1 i2 then
                  mark i1
	        else if eq_i i1 (T0 dummy) orelse eq_i i1 (ConstIN (0, dummy)) then
                  mark i2
	        else if eq_i i2 (T0 dummy) orelse eq_i i2 (ConstIN (0, dummy)) then
                  mark i1
	        else
                  (case (i1, i2) of
                       (BinOpI (opr, i1, i2), BinOpI (opr', i1', i2')) =>
                       if opr = opr' then
                         if opr = AddI orelse opr = MultI then
                           if eq_i i1 i1' then
                             mark $ BinOpI (opr, i1, BinOpI (MaxI, i2, i2'))
                           else if eq_i i2 i2' then
                             mark $ BinOpI (opr, BinOpI (MaxI, i1, i1'), i2)
                           else def ()
                         else if opr = IApp then
                           if eq_i i1 i1' then
                             mark $ BinOpI (opr, i1, BinOpI (MaxI, i2, i2'))
                           else def ()
                         else def ()
                       else def ()
                     | _ => def ()
                  )
	      | MinI =>
	        if eq_i i1 i2 then
                  mark i1
	        else
		  def ()
	      | AddI => 
	        if eq_i i1 (T0 dummy) orelse eq_i i1 (ConstIN (0, dummy)) then
                  mark i2
	        else if eq_i i2 (T0 dummy) orelse eq_i i2 (ConstIN (0, dummy)) then
                  mark i1
	        else
                  let
                    val is = collect_AddI i
                    val (i', is) = case is of
                                       i :: is => (i, is)
                                     | [] => raise Impossible "passi/AddI"
                    val i' = combine_AddI_nonempty i' is
                  in
		    if eq_i i' i then
                      def ()
                    else
                      mark i'
                  end
	      | MultI => 
	        if eq_i i1 (T0 dummy) then
                  mark $ T0 $ r ()
	        else if eq_i i2 (T0 dummy) then
                  mark $ T0 $ r ()
	        else if eq_i i1 (T1 dummy) then
                  mark i2
	        else if eq_i i2 (T1 dummy) then
                  mark i1
	        else
                  (case (i1, i2) of
                       (IConst (ICNat n1, _), IConst (ICNat n2, _)) =>
                       mark $ ConstIN (n1 * n2, r ())
                     | _ =>
                       let
                         val i2s = collect_AddI i2
                         fun pred i =
                           case i of
                               IConst (ICNat _, _) => SOME i
                             | UnOpI (B2n, _, _) => SOME i
                             | _ => NONE
                       in
                         case partitionOptionFirst pred i2s of
                             SOME (i2, rest) =>
                             let
                               val ret = i1 %* i2
                               val ret =
                                   case rest of
                                       [] => ret
                                     | hd :: rest => ret %+ i1 %* combine_AddI_nonempty hd rest
                             in
                               if eq_i ret i then
                                 def ()
                               else
                                 mark ret
                             end
                           | NONE => def ()
                       end
                  )
              | IApp =>
                (case (* passi *) i1 of
                     IAbs (_, Bind (_, body), _) =>
                     (* passi $ *) mark $ subst_i_i (passi i2) body
		   | _ => def ()
                )
              | EqI =>
                if eq_i i1 i2 then
                  mark $ TrueI $ r ()
                else def ()
              | AndI =>
                if eq_i i1 (TrueI dummy) then
                  mark i2
                else if eq_i i2 (TrueI dummy) then
                  mark i1
                else if eq_i i1 (FalseI dummy) then
                  mark $ FalseI $ r ()
                else if eq_i i2 (FalseI dummy) then
                  mark $ FalseI $ r ()
                else
                  def ()
              | ExpNI =>
                let
                  val r = r ()
                  fun exp i n =
                    if n > 0 then
                      exp i (n-1) %* i
                    else
                      N1 r
                in
                  case i2 of
                      IConst (ICNat n, _) => exp i1 n
                    | UnOpI (B2n, i, _) => Ite (i, i1, N1 r, r)
                    | _ =>
                      let
                        val i2s = collect_AddI i2
                        fun pred i =
                          case i of
                              IConst (ICNat _, _) => SOME i
                            | UnOpI (B2n, _, _) => SOME i
                            | _ => NONE
                      in
                        case partitionOptionFirst pred i2s of
                            SOME (i2, rest) => mark $ i1 %^ i2 %* i1 %^ combine_AddI_Nat rest
                          | NONE => def ()
                      end
                end
              | LtI =>
                def ()
              | GeI =>
                def ()
              | BoundedMinusI =>
                def ()
          end
        | Ite (i, i1, i2, r) =>
          if eq_i i (TrueI dummy) then
            mark i1
          else if eq_i i (FalseI dummy) then
            mark i2
          else
            Ite (passi i, passi i1, passi i2, r)
        | UnOpI (opr, i, r) =>
          let
            fun default () = UnOpI (opr, passi i, r)
          in
            case opr of
                IUDiv n => DivI (passi i, (n, r))
              | IUExp s => ExpI (passi i, (s, r))
              | ToReal =>
                (case i of
                     BinOpI (AddI, i1, i2) =>
                     mark $ BinOpI (AddI, UnOpI (ToReal, i1, r), UnOpI (ToReal, i2, r))
                   | BinOpI (MultI, i1, i2) =>
                     mark $ BinOpI (MultI, UnOpI (ToReal, i1, r), UnOpI (ToReal, i2, r))
                   | _ => default ()
                )
              | Neg =>
                (case i of
                     IConst (ICBool b, r) => mark $ IConst (ICBool (not b), r)
                   | _ => default ()
                )
              | B2n =>
                (case i of
                     IConst (ICBool b, r) => mark $ IConst (ICNat (b2i b), r)
                   | _ => default ()
                )
              | _ => default ()
          end
        | IConst _ => i
        | IAbs (b, Bind (name, i), r) =>
          IAbs (b, Bind (name, passi i), r)
        | VarI _ => i
        | UVarI _ => i
    end
      
  fun passp p =
    let
      fun r () = get_region_p p
                              (* val () = println $ str_p [] [] p *)
    in
      case p of
	  BinConn (opr, p1, p2) =>
          let
            fun def () = BinConn (opr, passp p1, passp p2) 
          in
            case opr of
                And =>
	        if eq_p p1 (True dummy) then
                  mark p2
	        else if eq_p p2 (True dummy) then
                  mark p1
	        else
	          def ()
              | Or =>
	        if eq_p p1 (False dummy) then
                  mark p2
	        else if eq_p p2 (False dummy) then
                  mark p1
	        else
	          def ()
              | Imply =>
	        if eq_p p1 (True dummy) then
                  mark p2
                else if eq_p p2 (True dummy) then
                  mark $ True $ r ()
                else
                  (case p1 of
                       BinConn (And, p1a, p1b) =>
                       mark $ (p1a --> p1b --> p2)
                     | _ => def ()
                  )
              | _ => def ()
          end
	| BinPred (opr, i1, i2) =>
          let
            fun def () = BinPred (opr, passi i1, passi i2)
          in
            case opr of 
                EqP => if eq_i i1 i2 then
                         mark $ True $ r ()
                       else def ()
              | LeP => if eq_i i1 i2 orelse eq_i i1 (T0 dummy) then
                         mark $ True $ r ()
                       else def ()
              | _ => def ()
          end
        | Not (p, r) => Not (passp p, r)
        | p_all as Quan (q, bs, Bind (name, p), r_all) =>
          let
            fun def () = Quan (q, bs, Bind (name, passp p), r_all)
            fun try_forget_p p =
              let
                fun def () = try_forget (forget_i_p 0 1) p
              in
                case p of
                    BinConn (Imply, BinPred (BigO, VarI (NONE, (x, _)), f), p) =>
                    if var2int x = 0 then
                      (* ignore this variable if the only thing mentioning it is a BigO premise *)
                      (case (try_forget (forget_i_p 0 1) p, try_forget (forget_i_i 0 1) f) of
                           (SOME p, SOME _) => SOME p
                         | _ => def ()
                      )
                    else def ()
                  | _ => def ()
              end                          
          in
            case q of
                Forall =>
                (case try_forget_p p of
                     SOME p => (set (); p)
                   | _ =>
                     (* try subst if there is a equality premise *)
                     let
                       fun collect_Imply_Forall p =
                         let
                           fun loop (acc, p) =
                             case p of
                                 BinConn (Imply, p1, p2) =>
                                 loop (map PropH (rev $ collect_And p1) @ acc, p2)
                               | Quan (Forall, bs, Bind (name, p), r) =>
                                 loop (VarH (name, (bs, r)) :: acc, p)
                               | _ => (acc, p)
                           val (hyps, conclu) = loop ([], p)
                           val hyps = rev hyps
                         in
                           (hyps, conclu)
                         end
                       fun combine_Imply_Forall hyps conclu =
                         let
                           fun iter (h, conclu) =
                             case h of
                                 PropH p =>
                                 p --> conclu
                               | VarH (name, (bs, r))  =>
                                 Quan (Forall, bs, Bind (name, conclu), r)
                         in
                           foldr iter conclu hyps
                         end
                       val (hyps, conclu) = collect_Imply_Forall p
                       val hyps = rev hyps
                       val binds_len = length $ hyps2ctx hyps
                       (* test whether [p] is [VarI x = _] or [_ = VarI x] *)
                       fun is_var_equals x p =
                         let
                           fun find_var (i1, i2) =
                             if eq_i i1 (VarI (NONE, (int2var x, dummy))) then
                               SOME (forget_i_i x 1 i2) handle ForgetError _ => NONE
                             else NONE
                         in
                           case p of
                               BinPred (EqP, i1, i2) => firstSuccess find_var [(i1, i2), (i2, i1)]
                             | _ => NONE
                         end
                       fun foldr_hyps shift1 shift2 f init hyps =
                         let
                           fun iter (h, (x, acc)) =
                             case h of
                                 VarH _ => (shift1 x, Option.map shift2 acc)
                               | PropH p =>
                                 case acc of
                                     SOME _ => (x, acc)
                                   | NONE => (x, f x p)
                         in
                           snd $ foldr iter (init, NONE) hyps
                         end
                     in
                       case foldr_hyps (fn x => var2int (shiftx_v 0 1 (int2var x))) shift_i_i is_var_equals 0 hyps of
                           SOME i =>
                           (let
                             val x = binds_len
                             val ctxn = map fst $ hyps2ctx hyps
                             (* val () = println $ sprintf "Substing for $ with $" [str_v (ctxn @ [fst name]) x, str_i ctxn i] *)
                             (* val () = app println $ str_hyps_conclu (hyps @ [VarH (name, (bs, r_all))], conclu) @ [""]  *)
                             val conclu = substx_i_p 0 x i conclu
                             fun subst_hyp n p =
                               let
                                 val x = var2int $ forget_v 0 n (int2var x)
                                 val p =
                                     case try_forget (forget_i_p x 1) p of
                                         NONE =>
                                         let
                                           val i = forget_i_i 0 n i
                                         in
                                           substx_i_p 0 x i p
                                         end
                                       | SOME p => p
                               in
                                 p
                               end
                             fun foldl_hyps f hyps =
                               let
                                 fun iter (h, (n, acc)) =
                                   case h of
                                       VarH _ => (n + 1, h :: acc)
                                     | PropH p => (n, PropH (f n p) :: acc)
                               in
                                 rev $ snd $ foldl iter (0, []) hyps
                               end
                             val hyps = foldl_hyps subst_hyp hyps
                             (* val () = app println $ str_hyps_conclu (hyps, conclu) @ [""]  *)
                             val ret = combine_Imply_Forall (rev hyps) conclu
                           in
                             mark ret
                           end
                            handle ForgetError _ => def ()
                           )
                         | NONE => def ()
                     end
                )
              | Exists ins =>
                (* for unconstrained Time evar, infer it to be 0 *)
                let
                  (* val () = println $ str_p [] [] p_all *)
                  val p = passp p
                  (* val () = println $ str_bs bs *)
                  fun base_sort_default_idx b =
                    case b of
                        Nat =>
                        N0 dummy
                      | Time =>
                        T0 dummy
                      | BoolSort =>
                        FalseI dummy
                      | UnitSort =>
                        TTI dummy
                  fun bsort_default_idx bs =
                    case bs of
                        Base b => SOME $ base_sort_default_idx b
                      | BSArrow (a, b) =>
                        opt_bind (bsort_default_idx b)
                                 (fn i => opt_return $ IAbs (a, Bind (("__dummy_default", dummy), i), dummy))
                      | _ => NONE
                  val inferred =
                      opt_bind
                        (try_forget (forget_i_p 0 1) p)
                        (fn p =>
                            opt_bind
                              (bsort_default_idx bs)
                              (fn i =>
                                  opt_return (p, i)))
                in
                  case inferred of
                      SOME (p, v) =>
                      let
                        val () = set ()
                        (* val () = println "before" *)
                        val () = case ins of
                                     SOME f => f v
                                   | NONE => ()
                                               (* val () = println "after" *)
                      in
                        p
                      end
                    | _ =>
                      let
                        val ps = collect_And p
                        val (irrelevant, relevant) = partitionOption (try_forget (forget_i_p 0 1)) ps
                      in
                        case relevant of
                            [] => def ()
                          | _ => combine_And $ Quan (q, bs, Bind (name, combine_And relevant), r_all) :: irrelevant
                      end
                end
          end
	| PTrueFalse _ => p
    end
      
  fun until_unchanged f a = 
    let fun loop a =
	  let
            val _ = unset ()
            (* val () = println "before f()" *)
            val a = f a
                      (* val () = println "after f()" *)
          in
	    if !changed then loop a
	    else a
	  end
    in
      loop a
    end
in
val simp_i = until_unchanged passi
fun simp_i_with_plugin plugin i =
  let
    fun iter i =
      let
        val i = plugin set i
        val i = passi i
      in
        i
      end
    val i = until_unchanged iter i
  in
    i      
  end
fun simp_p p =
  let
    (* val () = println $ "Before simp_p: " ^ str_p [] [] p *)
    val p = until_unchanged passp p
                            (* val () = println $ "After simp_p:  " ^ str_p [] [] p *)
                            (* val () = println "" *)
  in
    p      
  end
fun simp_p_with_plugin plugin p =
  let
    fun iter p =
      let
        val p = plugin set p
        val p = passp p
      in
        p
      end
    val p = until_unchanged iter p
  in
    p      
  end
    
end

fun simp_vc (ctx, ps, p, r) = (ctx, map simp_p ps, simp_p p, r)

fun simp_bind f (Bind (name, inner)) = Bind (name, f inner)
fun simp_binds f_cls f binds =
  case binds of
      BindNil a => BindNil (f a)
    | BindCons (cls, bind) => BindCons (f_cls cls, simp_bind (simp_binds f_cls f) bind)

fun simp_s s =
  case s of
      Basic b => Basic b
    | Subset (b, bind, r) => Subset (b, simp_bind simp_p bind, r)
    | UVarS u => UVarS u
    | SAbs (b, bind, r) => SAbs (b, simp_bind simp_s bind, r)
    | SApp (s, i) =>
      let
        val s = simp_s s
        val i = simp_i i
      in
        case s of
            SAbs (_, Bind (_, s), _) => simp_s (Subst.subst_i_s i s)
          | _ => SApp (s, i)
      end

fun simp_mt t =
  case t of
      Arrow (t1, d, t2) => Arrow (simp_mt t1, simp_i d, simp_mt t2)
    | TyNat (i, r) => TyNat (simp_i i, r)
    | TyArray (t, i) => TyArray (simp_mt t, simp_i i)
    | Unit r => Unit r
    | Prod (t1, t2) => Prod (simp_mt t1, simp_mt t2)
    | UniI (s, bind, r) => UniI (simp_s s, simp_bind simp_mt bind, r)
    | BaseType a => BaseType a
    | UVar u => UVar u
    | MtVar x => MtVar x
    | MtAbs (k, bind, r) => MtAbs (k, simp_bind simp_mt bind, r)
    | MtApp (t1, t2) => MtApp (simp_mt t1, simp_mt t2)
    | MtAbsI (b, bind, r) => MtAbsI (b, simp_bind simp_mt bind, r)
    | MtAppI (t, i) =>
      let
        val t = simp_mt t
        val i = simp_i i
      in
        case t of
            MtAbsI (_, Bind (_, t), _) => simp_mt (Subst.subst_i_mt i t)
          | _ => MtAppI (t, i)
      end
    | TDatatype (dt, r) =>
      let
        fun simp_constr c = simp_binds simp_s (mapPair (simp_mt, map simp_i)) c
        fun simp_constr_decl ((name, c, r) : mtype constr_decl) : mtype constr_decl = (name, simp_constr c, r)
        val dt = simp_bind (simp_binds id (mapPair (id, map simp_constr_decl))) dt
      in
        TDatatype (dt, r)
      end

fun simp_t t =
  case t of
      Mono t => Mono (simp_mt t)
    | Uni (Bind (name, t), r) => Uni (Bind (name, simp_t t), r)

end

structure VC = struct
open Gctx
open List
open Util
open Region
open Subst
open Simp
       
infixr 1 -->
infixr 0 $
         
fun uniquefy_ls names = foldr (fn (name, acc) => find_unique acc name :: acc) [] names
                              
fun uniquefy ctx p =
    case p of
        Quan (q, bs, Bind ((name, r), p), r_all) =>
        let
            val name = find_unique ctx name
        in
            Quan (q, bs, Bind ((name, r), uniquefy (name :: ctx) p), r_all)
        end
      | Not (p, r) => Not (uniquefy ctx p, r)
      | BinConn (opr, p1, p2) => BinConn (opr, uniquefy ctx p1, uniquefy ctx p2)
      | BinPred _ => p
      | PTrueFalse _ => p

type vc = (string * bsort, prop) hyp list * prop

fun str_vc show_region filename ((hyps, p) : vc) =
    let 
        val region = if show_region then 
                         [str_region "" filename (get_region_p p)] 
                     else []
        fun g (h, (hyps, ctx)) =
            case h of
                VarH (name, bs) => (sprintf "$ : $" [name, str_bs bs] :: hyps, name :: ctx)
              | PropH p => (str_p empty ctx p :: hyps, ctx)
        val (hyps, ctx) = foldr g ([], []) hyps
        val hyps = rev hyps
        val p = str_p empty ctx p
    in
        region @
        (self_compose 2 indent) (hyps @
                           ["==============="] @
                           [p])
    end 

fun simp_hyp h =
    case h of
        VarH a => VarH a
      | PropH p => PropH (simp_p p)

fun simp_vc ((hyps, p) : vc) : vc =
    let
      val hyps = map simp_hyp hyps
      val p = simp_p p
    in
      (hyps, p)
    end

fun prop2vcs p : vc list =
    let
    in
        case p of
            Quan (Forall, bs, Bind ((name, r), p), r_all) =>
            let
                val ps = prop2vcs p
                val ps = add_hyp (VarH (name, bs)) ps
            in
                ps
            end
          | BinConn (Imply, p1, p) =>
            let
                val ps = prop2vcs p
                val ps = add_hyp (PropH p1) ps
            in
                ps
            end
          | BinConn (And, p1, p2) =>
            prop2vcs p1 @ prop2vcs p2
          | _ => [([], p)]
    end

fun vc2prop ((hs, p) : vc) =
    foldl (fn (h, p) => case h of VarH (name, b) => Quan (Forall, b, Bind ((name, dummy), p), get_region_p p) | PropH p1 => p1 --> p) p hs

fun simp_vc_vcs (vc : vc) : vc list = prop2vcs $ simp_p $ vc2prop $ vc
          
end
                 
(* collect module references *)
structure CollectMod = struct
open Util

infixr 0 $

fun on_ibind f acc (Bind (_, b) : ('a * 'b) ibind) = f acc b

fun on_long_id acc (m, _) = (option2list $ Option.map fst m) @ acc
fun collect_mod_long_id b = on_long_id [] b
  
local
  fun f acc b =
    case b of
	VarI x => on_long_id acc x
      | IConst _ => acc
      | UnOpI (opr, i, r) => f acc i
      | BinOpI (opr, i1, i2) => 
        let
          val acc = f acc i1
          val acc = f acc i2
        in
          acc
        end
      | Ite (i1, i2, i3, r) =>
        let
          val acc = f acc i1
          val acc = f acc i2
          val acc = f acc i3
        in
          acc
        end
      | IAbs (b, bind, r) =>
        on_ibind f acc bind
      | UVarI a => acc
in
val on_i = f
fun collect_mod_i b = f [] b
end

local
  fun f acc b =
    case b of
	PTrueFalse _ => acc
      | Not (p, r) => f acc p
      | BinConn (opr,p1, p2) =>
        let
          val acc = f acc p1
          val acc = f acc p2
        in
          acc
        end
      | BinPred (opr, i1, i2) => 
        let
          val acc = on_i acc i1
          val acc = on_i acc i2
        in
          acc
        end
      | Quan (q, bs, bind, r) => on_ibind f acc bind
in
val on_p = f
fun collect_mod_p b = f [] b
end

local
  fun f acc b =
    case b of
	Basic s => acc
      | Subset (b, bind, r) => on_ibind on_p acc bind
      | UVarS a => acc
      | SAbs (s, bind, r) => on_ibind f acc bind
      | SApp (s, i) =>
        let
          val acc = f acc s
          val acc = on_i acc i
        in
          acc
        end
in
val on_s = f
fun collect_mod_s b = f [] b
end

fun on_tbind f acc (Bind (_, b) : ('a * 'b) tbind) = f acc b

fun on_list f acc b = foldl (fn (b, acc) => f acc b) acc b
fun on_pair (f, g) acc (a, b) =
  let
    val acc = f acc a
    val acc = g acc b
  in
    acc
  end
  
fun on_mt acc b =
  let
    val f = on_mt
  in
    case b of
	Arrow (t1, i, t2) =>
        let
          val acc = f acc t1
          val acc = on_i acc i
          val acc = f acc t2
        in
          acc
        end
      | TyNat (i, _) => on_i acc i
      | TyArray (t, i) =>
        let
          val acc = f acc t
          val acc = on_i acc i
        in
          acc
        end
      | Unit _ => acc
      | Prod (t1, t2) =>
        let
          val acc = f acc t1
          val acc = f acc t2
        in
          acc
        end
      | UniI (s, bind, _) =>
        let
          val acc = on_s acc s
          val acc = on_ibind f acc bind
        in
          acc
        end
      | MtVar x => on_long_id acc x
      | MtApp (t1, t2) =>
        let
          val acc = f acc t1
          val acc = f acc t2
        in
          acc
        end
      | MtAbs (k, bind, _) => on_tbind f acc bind
      | MtAppI (t, i) =>
        let
          val acc = f acc t
          val acc = on_i acc i
        in
          acc
        end
      | MtAbsI (b, bind, r) => on_ibind f acc bind
      | BaseType _ => acc
      | UVar _ => acc
      | TDatatype dt => on_datatype acc dt
  end
    
and on_constr_core acc ibinds =
  let
    val (ns, (t, is)) = unfold_binds ibinds
    val acc = on_list on_s acc $ map snd ns
    val acc = on_mt acc t
    val acc = on_list on_i acc is
  in
    acc
  end
    
and on_datatype acc (Bind (_, tbinds), r) =
    let
      val (_, (_, constr_decls)) = unfold_binds tbinds
      fun on_constr_decl acc (name, core, r) = on_constr_core acc core
      val acc = on_list on_constr_decl acc constr_decls
    in
      acc
    end
    
fun collect_mod_mt b = on_mt [] b
fun collect_mod_constr_core b = on_constr_core [] b
    
local
  fun f acc b =
    case b of
	Mono t => on_mt acc t
      | Uni (bind, r) => on_tbind f acc bind
in
val on_t = f
fun collect_mod_t b = f [] b
end

fun on_option f acc a =
  case a of
      SOME a => f acc a
    | NONE => acc
                
local
  fun f acc b =
    case b of
	ConstrP (((x, _), eia), inames, pn, r) =>
        let
          val acc = on_long_id acc x
          val acc = f acc pn
        in
          acc
        end
      | VarP name => acc
      | PairP (pn1, pn2) =>
        let
          val acc = f acc pn1
          val acc = f acc pn2
        in
          acc
        end
      | TTP r => acc
      | AliasP (name, pn, r) => f acc pn
      | AnnoP (pn, t) =>
        let
          val acc = f acc pn
          val acc = on_mt acc t
        in
          acc
        end
in
val on_ptrn = f
fun collect_mod_ptrn b = f [] b
end

fun on_return x = on_pair (on_option on_mt, on_option on_i) x
                      
local
  fun f acc b =
      case b of
	  Var (x, _) => collect_mod_long_id x @ acc
	| EConst c => acc
	| EUnOp (opr, e, r) => f acc e
	| BinOp (opr, e1, e2) =>
          let
            val acc = f acc e1
            val acc = f acc e2
          in
            acc
          end
	| TriOp (opr, e1, e2, e3) =>
          let
            val acc = f acc e1
            val acc = f acc e2
            val acc = f acc e3
          in
            acc
          end
	| EEI (opr, e, i) =>
          let
            val acc = f acc e
            val acc = on_i acc i
          in
            acc
          end
	| ET (opr, t, r) => on_mt acc t
	| Abs (pn, e) =>
          let
            val acc = on_ptrn acc pn
            val acc = f acc e
          in
            acc
          end
	| AbsI (s, Bind (name, e), r) =>
          let
            val acc = on_s acc s
            val acc = f acc e
          in
            acc
          end
	| Ascription (e, t) =>
          let
            val acc = f acc e
            val acc = on_mt acc t
          in
            acc
          end
	| AppConstr ((x, ie), is, e) =>
          let
            val acc = on_long_id acc x
            val acc = on_list on_i acc is
            val acc = f acc e
          in
            acc
          end
	| Case (e, return, rules, r) =>
          let
            val acc = f acc e
            val acc = on_return acc return
            val on_rule = on_pair (on_ptrn, f)
            val acc = on_list on_rule acc rules
          in
            acc
          end
	| Let (return, decls, e, r) =>
          let
            val acc = on_return acc return
            val acc = on_list on_decl acc decls
            val acc = f acc e
          in
            acc
          end

  and on_decl acc b =
      case b of
          Val (tnames, pn, e, r) =>
          let 
            val acc = on_ptrn acc pn
            val acc = f acc e
          in
            acc
          end
        | Rec (tnames, (name, r1), (binds, ((t, i), e)), r) =>
          let
            fun on_stbind acc b =
              case b of
                  SortingST (name, s) => on_s acc s
                | TypingST pn => on_ptrn acc pn
            val acc = on_list on_stbind acc binds
            val acc = on_mt acc t
            val acc = on_i acc i
            val acc = f acc e
          in
            acc
          end
        | Datatype a => on_datatype acc a
        | IdxDef ((name, r), s, i) =>
          let 
            val acc = on_s acc s
            val acc = on_i acc i
          in
            acc
          end
        | AbsIdx2 ((name, r), s, i) =>
          let 
            val acc = on_s acc s
            val acc = on_i acc i
          in
            acc
          end
        | AbsIdx (((name, r1), s, i), decls, r) =>
          let 
            val acc = on_s acc s
            val acc = on_i acc i
            val acc = on_list on_decl acc decls
          in
            acc
          end
        | TypeDef ((name, r), t) => on_mt acc t
        | Open ((m, r), _) => m :: acc

in
val on_e = f
fun collect_mod_e b = f [] b
val on_decl = on_decl
end

fun on_k acc b = on_list on_s acc $ snd b
fun collect_mod_k b = on_k [] b
  
local
  fun f acc b =
    case b of
        SpecVal (name, t) => on_t acc t
      | SpecIdx (name, s) => on_s acc s
      | SpecType (name, k) => []
      | SpecTypeDef (name, t) => on_mt acc t
      | SpecDatatype a => on_datatype acc a
in
val on_spec = f
fun collect_mod_spec b = f [] b
end

fun on_sgn acc b = on_list on_spec acc $ fst b

local
  fun f acc b =
    case b of
        ModComponents (comps, r) => on_list on_decl acc comps
      | ModSeal (m, sg) =>
        let 
          val acc = f acc m
          val acc = on_sgn acc sg
        in
          acc
        end
      | ModTransparentAscription (m, sg) =>
        let 
          val acc = f acc m
          val acc = on_sgn acc sg
        in
          acc
        end
in
val on_mod = f
fun collect_mod_mod b = f [] b
end

fun on_top_bind acc b =
  case b of
      TopModBind m => on_mod acc m
    | TopFunctorBind (((arg_name, r2), arg), m) =>
      let 
        val acc = on_sgn acc arg
        val acc2 = diff op= (on_mod [] m) [arg_name]
        val acc = acc2 @ acc
      in
        acc
      end
    | TopFunctorApp ((functor_name, _), (arg_name, _)) => arg_name :: functor_name :: acc

fun on_prog acc b =
  let
    fun iter (((name, r), b), acc) =
      let
        val acc = diff op= acc [name]
        val acc = on_top_bind acc b
      in
        acc
      end
    val acc2 = foldr iter [] b
    val acc = acc2 @ acc
  in
    acc
  end

fun collect_mod_prog b = on_prog [] b

fun collect_mod_constr (family, tbinds) =
  let
    val (_, ibinds) = unfold_binds tbinds
  in
    collect_mod_constr_core ibinds
  end
                          
end
                         
end

(* Test that the result of [ExprFun] matches some signatures. We don't use a signature ascription because signature ascription (transparent or opaque) hides components that are not in the signature. SML should have a "signature check" kind of ascription. *)
functor TestExprFnSignatures (Params : EXPR_PARAMS) = struct
structure M : IDX = ExprFn (Params)
structure M2 : TYPE = ExprFn (Params)
end

structure StringVar = struct
open Util
type var = string
type name_context = string list * string list * string list * string list
type global_name_context = name_context Gctx.map
                                        
fun str_v ctx x : string = x
fun str_raw_v x = x
      
fun lookup_module gctx m = (m, ([], [], [], []))
                             
fun str_long_id sel gctx ctx (m, x) =
  let
    val m = default "" (Option.map (suffix "." o fst) m)
    val x = str_v ctx (fst x)
  in
    m ^ x
  end
    
fun eq_v (x : var, y) = x = y
                              
fun shiftx_v x n y = y
fun forget_v ForgetError x n y =  y
fun substx_v Var x v y = raise Impossible "Can't do StringVar.substx_v()"

fun int2var x = raise Impossible "StringVar.int2var()"
fun var2int x = raise Impossible "StringVar.var2int()"
end

structure IntVar = struct
open Util
open ShiftUtil
open Gctx
type var = int
type name_context = string list * string list * string list * string list
type global_name_context = name_context Gctx.map
                                        
fun str_v ctx x : string =
  (* sprintf "%$" [str_int x] *)
  case nth_error ctx x of
      SOME name => name
    | NONE => "unbound_" ^ str_int x
                                   
fun str_raw_v x = str_int x
                    
fun str_id ctx (x, _) =
  str_v ctx x
        
fun lookup_module gctx m =
  case nth_error2 gctx m of
      SOME (name, ctx) => (name, ctx)
    | NONE => ("unbound_module_" ^ m, ([], [], [], []))
                
fun str_long_id sel gctx ctx (m, x) =
  let
    val (mod_name, ctx) =
        case m of
            SOME (m, _) =>
            let
              val (name, ctx) = lookup_module gctx m
              val name = name ^ "."
              val ctx = sel ctx
            in
              (name, ctx)
            end
          | NONE => ("", ctx)
    val x = str_id ctx x
  in
    mod_name ^ x
  end
    
fun eq_v (x : var, y) = x = y

val shiftx_v = shiftx_int
val forget_v = forget_int
                 
fun substx_v Var x v y =
  if y = x then
    v ()
  else if y > x then
    Var (y - 1)
  else
    Var y

fun int2var x = x
fun var2int x = x
                  
end

structure Underscore = struct
type 'bsort uvar_bs = unit
type ('bsort, 'idx) uvar_i = unit
type ('bsort, 'sort) uvar_s = unit
type ('sort, 'kind, 'mtype) uvar_mt = unit
fun str_uvar_bs _ _ = "_"
fun str_uvar_s _ _ = "_"
fun str_uvar_i _ _ = "_"
fun str_uvar_mt _ _ = "_"
fun eq_uvar_i (_, _) = false
fun eq_uvar_bs (_, _) = false
fun eq_uvar_s (_, _) = false
fun eq_uvar_mt (_, _) = false
end

structure NamefulExpr = ExprFn (structure Var = StringVar
                                structure UVarI = Underscore
                                structure UVarT = Underscore
                                type ptrn_constr_tag = unit
                               )
structure UnderscoredExpr = ExprFn (structure Var = IntVar
                                    structure UVarI = Underscore
                                    structure UVarT = Underscore
                                    type ptrn_constr_tag = unit
                                   )

