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
open LongId
open Operators
open UVarI
open UVarT
open Region
open Bind

type id = var * region
type name = string * region
type long_id = var long_id

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
       
fun collect_UniI t =
  case t of
      UniI (s, Bind (name, t), _) =>
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

fun collect_Pair e =
  case e of
      EBinOp (EBPair, e1, e2) =>
      collect_Pair e1 @ [e2]
    | _ => [e]
             
fun collect_IApp i =
  case collect_BinOpI_left IApp i of
      f :: args => (f, args)
    | [] => raise Impossible "collect_IApp(): null"
                  
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
                                 
(* equality test *)
    
fun eq_option eq (a, a') =
  case (a, a') of
      (SOME v, SOME v') => eq (v, v')
    | (NONE, NONE) => true
    | _ => false

fun eq_id ((x, _), (x', _)) =
  eq_v (x, x')

fun eq_name ((s, _) : name, (s', _)) = s = s'
  
val eq_long_id = fn a => eq_long_id eq_id a
                                        
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

val str_raw_long_id = fn a => str_raw_long_id str_raw_v a
                       
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

fun str_raw_e e =
  case e of
      EAppConstr _ => "AppConstr (...)"
    | EBinOp _ => "BinOp (...)"
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
    val binds = map (mapFst fst) binds
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
          val binds = map (mapFst fst) binds
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

fun decorate_var eia s = (if eia then "@" else "") ^ s
                                                       
fun str_pn gctx (ctx as (sctx, kctx, cctx)) pn =
  let
    val str_pn = str_pn gctx
  in
    case pn of
        ConstrP (Outer ((x, _), eia), inames, pn, _) => sprintf "$$$" [decorate_var eia $ str_long_id #3 gctx cctx x, join_prefix " " $ map (surround "{" "}" o binder2str) inames, " " ^ str_pn ctx pn]
      | VarP name => binder2str name
      | PairP (pn1, pn2) => sprintf "($, $)" [str_pn ctx pn1, str_pn ctx pn2]
      | TTP _ => "()"
      | AliasP (name, pn, _) => sprintf "$ as $" [binder2str name, str_pn ctx pn]
      | AnnoP (pn, Outer t) => sprintf "($ : $)" [str_pn ctx pn, str_mt gctx (sctx, kctx) t]
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
	EVar (x, b) => decorate_var b $ str_long_id #4 gctx tctx x
      | EConst (c, _) => str_expr_const c
      | EUnOp (opr, e, _) => sprintf "($ $)" [str_expr_un_op opr, str_e ctx e]
      | EBinOp (opr, e1, e2) =>
        (case opr of
             EBApp => sprintf "($ $)" [str_e ctx e1, str_e ctx e2]
           | EBPair =>
             let
               val es = collect_Pair e
             in
               sprintf "($)" [join ", " $ map (str_e ctx) es]
             end
           | EBNew => sprintf "(new $ $)" [str_e ctx e1, str_e ctx e2]
           | EBRead => sprintf "(read $ $)" [str_e ctx e1, str_e ctx e2]
           | EBAdd => sprintf "($ $ $)" [str_e ctx e1, str_bin_op opr, str_e ctx e2]
        )
      | ETriOp (Write, e1, e2, e3) => sprintf "(write $ $ $)" [str_e ctx e1, str_e ctx e2, str_e ctx e3]
      | EEI (opr, e, i) =>
        (case opr of
           EEIAppI => sprintf "($ {$})" [str_e ctx e, str_i gctx sctx i]
          | EEIAscTime => sprintf "($ |> $)" [str_e ctx e, str_i gctx sctx i]
        )
      | EET (opr, e, t) =>
        (case opr of
             EETAppT => sprintf "($ {$})" [str_e ctx e, str_mt gctx skctx t]
           | EETAsc => sprintf "($ : $)" [str_e ctx e, str_mt gctx skctx t]
        )
      | ET (opr, t, _) =>
        (case opr of
             ETNever => sprintf "(never [$])" [str_mt gctx skctx t]
           | ETBuiltin => sprintf "(builtin [$])" [str_mt gctx skctx t]
        )
      | EAbs bind => 
        let
          val (pn, e) = Unbound.unBind bind
          val (inames, enames) = ptrn_names pn
          val pn = str_pn gctx (sctx, kctx, cctx) pn
          val ctx = (inames @ sctx, kctx, cctx, enames @ tctx)
	  val e = str_e ctx e
        in
          sprintf "(fn $ => $)" [pn, e]
        end
      | EAbsI (bind, _) =>
        let
          val ((name, s), e) = unBindAnno bind
          val name = Name2str name
        in
          sprintf "(fn {$ : $} => $)" [name, str_s gctx sctx s, str_e (name :: sctx, kctx, cctx, tctx) e]
        end
      | ELet (return, bind, _) => 
        let
          val (decls, e) = Unbound.unBind bind
          val decls = unTeles decls
          val return = str_return gctx (sctx, kctx) return
          val (decls, ctx) = str_decls gctx ctx decls
        in
          sprintf "let $$ in $ end" [return, join_prefix " " decls, str_e ctx e]
        end
      | EAppConstr ((x, b), ts, is, e, _) =>
        sprintf "([$]$$ $)" [
          decorate_var b $ str_long_id #3 gctx cctx x,
          (join "" o map (prefix " ") o map (fn t => sprintf "{$}" [str_mt gctx skctx t])) ts,
          (join "" o map (prefix " ") o map (fn i => sprintf "{$}" [str_i gctx sctx i])) is,
          str_e ctx e]
      | ECase (e, return, rules, _) => sprintf "(case $ $of $)" [str_e ctx e, str_return gctx skctx return, join " | " (map (str_rule gctx ctx) rules)]
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
          DVal (name, Outer bind, _) =>
          let
            val pn = VarP name
            val (tnames, e) = Unbound.unBind bind
            val tnames = map binder2str tnames
            val ctx' as (sctx', kctx', cctx', _) = (sctx, rev tnames @ kctx, cctx, tctx)
            val tnames = (join "" o map (fn nm => sprintf " [$]" [nm])) tnames
            val (inames, enames) = ptrn_names pn
            val pn = str_pn gctx (sctx', kctx', cctx') pn
            val e = str_e gctx ctx' e
	    val ctx = (inames @ sctx, kctx, cctx, enames @ tctx)
          in
            (sprintf "val$ $ = $" [tnames, pn, e], ctx)
          end
        | DValPtrn (pn, Outer e, _) =>
          let
            val (inames, enames) = ptrn_names pn
            val e = str_e gctx ctx e
            val pn = str_pn gctx (sctx, kctx, cctx) pn
	    val ctx = (inames @ sctx, kctx, cctx, enames @ tctx)
          in
            (sprintf "val $ = $" [pn, e], ctx)
          end
        | DRec (name, bind, _) =>
          let
            val name = binder2str name
            val ((tnames, Rebind binds), ((t, d), e)) = Unbound.unBind $ unInner bind
            val binds = unTeles binds
            val tnames = map binder2str tnames
	    val ctx as (sctx, kctx, cctx, tctx) = (sctx, kctx, cctx, name :: tctx)
            val ctx_ret = ctx
            val ctx as (sctx, kctx, cctx, tctx) = (sctx, rev tnames @ kctx, cctx, tctx)
            val tnames = (join "" o map (fn nm => sprintf " [$]" [nm])) tnames
            fun f (bind, (binds, ctx as (sctx, kctx, cctx, tctx))) =
              case bind of
                  SortingST (name, Outer s) =>
                  let
                    val name = binder2str name
                  in
                    (sprintf "{$ : $}" [name, str_s gctx sctx s] :: binds, (name :: sctx, kctx, cctx, tctx))
                  end
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
        | DIdxDef (name, Outer s, Outer i) =>
          let
            val name = binder2str name
          in
            (sprintf "idx $ : $ = $" [name, str_s gctx sctx s, str_i gctx sctx i], (name :: sctx, kctx, cctx, tctx))
          end
        | DAbsIdx2 (name, Outer s, Outer i) =>
          let
            val name = binder2str name
          in
            (sprintf "absidx $ : $ = $" [name, str_s gctx sctx s, str_i gctx sctx i], (name :: sctx, kctx, cctx, tctx))
          end
        | DAbsIdx ((name, Outer s, Outer i), Rebind decls, _) =>
          let
            val name = binder2str name
            val decls = unTeles decls
            val ctx' = (name :: sctx, kctx, cctx, tctx)
            val (decls, ctx') = str_decls gctx ctx' decls
          in
            (sprintf "absidx $ : $ = $ with$ end" [name, str_s gctx sctx s, str_i gctx sctx i, join_prefix " " decls], ctx')
          end
        | DTypeDef (name, Outer t) =>
          (case t of
               TDatatype (Bind (name, tbinds), _) =>
               let
                 val name = fst name
                 val (tname_kinds, (sorts, constrs)) = unfold_binds tbinds
                 val tnames = map fst $ map fst tname_kinds
                 val str_tnames = (join_prefix " " o rev) tnames
                 fun str_constr_decl ((cname, _), ibinds, _) =
                   let 
                     val (name_sorts, (t, idxs)) = unfold_binds ibinds
                     val name_sorts = map (mapFst fst) name_sorts
                     val (name_sorts, sctx') = str_sortings gctx sctx name_sorts
                     val name_sorts = map (fn (nm, s) => sprintf "$ : $" [nm, s]) name_sorts
                   in
                     sprintf "$ of$ $ ->$$ $" [cname, (join_prefix " " o map (surround "{" "}")) name_sorts, str_mt gctx (sctx', rev tnames @ name :: kctx) t, (join_prefix " " o map (surround "{" "}" o str_i gctx sctx') o rev) idxs, str_tnames, name]
                   end
                 val s = sprintf "datatype$$ $ = $" [(join_prefix " " o map (surround "{" "}" o str_bs) o rev) sorts, str_tnames, name, join " | " (map str_constr_decl constrs)]
                 val cnames = map fst $ map #1 constrs
                 val ctx = (sctx, name :: kctx, rev cnames @ cctx, tctx)
               in
                 (s, ctx)
               end
             | _ =>
               let
                 val name = binder2str name
               in
                 (sprintf "type $ = $" [name, str_mt gctx (sctx, kctx) t], add_kinding name ctx)
               end
          )
        | DOpen (Outer (m, r), _) =>
          let
            val (m, ctxd) = lookup_module gctx m
            val ctx = add_ctx ctxd ctx
          in
            (sprintf "open $" [m], ctx)
          end
    end
      
and str_rule gctx (ctx as (sctx, kctx, cctx, tctx)) bind =
    let
      val (pn, e) = Unbound.unBind bind
      val (inames, enames) = ptrn_names pn
      val ctx' = (inames @ sctx, kctx, cctx, enames @ tctx)
    in
      sprintf "$ => $" [str_pn gctx (sctx, kctx, cctx) pn, str_e gctx ctx' e]
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

open Hyp
       
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
                                        
fun shiftx_id x n (y, r) = (shiftx_v x n y, r)
                             
(* ToDo: just a hack now *)
fun forget_above_i_i x b = forget_i_i x 100000000 b

(* subst *)

exception Error of string

(* mimic type class *)
(* type 'a shiftable = { *)
(*   shift_i : int -> 'a -> 'a, *)
(*   shift_t : int -> 'a -> 'a *)
(* } *)
(* todo: split [shiftable] to [ishiftable] and [tshiftable], or ultimately get rid of it aftering changing to lazy shifting *)                      

fun substx_pair (f1, f2) d x v (b1, b2) = (f1 d x v b1, f2 d x v b2)
fun substx_list f d x v b = map (f d x v) b

open Bind
       
(* fun substx_i_ibind f d x v (Bind (name, inner) : ('name * 'b) ibind) = *)
(*   Bind (name, f (d + 1) (x + 1) v inner) *)
       
(* fun substx_i_tbind f d x v (Bind (name, inner) : ('name * 'b) tbind) = *)
(*   Bind (name, f d x v inner) *)

(* fun substx_binds substx_bind f_cls f d x v b = *)
(*   let *)
(*     val substx_binds = substx_binds substx_bind f_cls f *)
(*   in *)
(*     case b of *)
(*         BindNil a => BindNil (f d x v a) *)
(*       | BindCons (cls, bind) => BindCons (f_cls d x v cls, substx_bind substx_binds d x v bind) *)
(*   end *)

(* fun substx_i_ibinds f_cls f d x v (b : ('classifier, 'name, 'inner) ibinds) = substx_binds substx_i_ibind f_cls f d x v b *)
                                                                                           
(* fun substx_i_tbinds f_cls f d x v (b : ('classifier, 'name, 'inner) tbinds) = substx_binds substx_i_tbind f_cls f d x v b *)

val substx_long_id = fn a => substx_long_id substx_v a
                                                                                           
fun visit_VarI (d, x, v) env y =
  let
    val x = x + env
    val d = d + env
  in
    substx_long_id VarI x (fn () => shiftx_i_i 0 d v) y
  end

val subst_i_params = visit_VarI
                     
structure IdxSubst = IdxSubstFn (Idx)
open IdxSubst
                                        
fun substx_i_i a = subst_i_i_fn subst_i_params a
fun substx_i_p a = subst_i_p_fn subst_i_params a
fun substx_i_s a = subst_i_s_fn subst_i_params a
      
(* local *)
(*   fun f d(*depth*) x v b = *)
(*     case b of *)
(* 	VarI y => substx_long_id VarI x (fn () => shiftx_i_i 0 d v) y *)
(*       | IConst c => IConst c *)
(*       | UnOpI (opr, i, r) => UnOpI (opr, f d x v i, r) *)
(*       | BinOpI (opr, d1, d2) => BinOpI (opr, f d x v d1, f d x v d2) *)
(*       | Ite (i1, i2, i3, r) => Ite (f d x v i1, f d x v i2, f d x v i3, r) *)
(*       | IAbs (b, bind, r) => IAbs (b, substx_i_ibind f d x v bind, r) *)
(*       | UVarI a => b *)
(* in *)
(* val substx_i_i = f *)
(* end *)

(* local *)
(*   fun f d x v b = *)
(*     case b of *)
(* 	PTrueFalse b => PTrueFalse b *)
(*       | Not (p, r) => Not (f d x v p, r) *)
(*       | BinConn (opr,p1, p2) => BinConn (opr, f d x v p1, f d x v p2) *)
(*       | BinPred (opr, d1, d2) => BinPred (opr, substx_i_i d x v d1, substx_i_i d x v d2) *)
(*       | Quan (q, bs, bind, r) => Quan (q, bs, substx_i_ibind f d x v bind, r) *)
(* in *)
(* val substx_i_p = f *)
(* end *)

(* local *)
(*   fun f d x v b = *)
(*     case b of *)
(* 	Basic s => Basic s *)
(*       | Subset (b, bind, r) => Subset (b, substx_i_ibind substx_i_p d x v bind, r) *)
(*       | UVarS a => b *)
(*       | SAbs (b, bind, r) => SAbs (b, substx_i_ibind f d x v bind, r) *)
(*       | SApp (s, i) => SApp (f d x v s, substx_i_i d x v i) *)
(* in *)
(* val substx_i_s = f *)
(* end *)

fun subst_i_i v b = substx_i_i 0 0 v b
fun subst_i_p (v : idx) (b : prop) : prop = substx_i_p 0 0 v b
fun subst_i_s (v : idx) (b : sort) : sort = substx_i_s 0 0 v b

(* local *)
(*   fun f d x v b = *)
(*     case b of *)
(* 	Arrow (t1, i, t2) => Arrow (f d x v t1, substx_i_i d x v i, f d x v t2) *)
(*       | TyNat (i, r) => TyNat (substx_i_i d x v i, r) *)
(*       | TyArray (t, i) => TyArray (f d x v t, substx_i_i d x v i) *)
(*       | Unit r => Unit r *)
(*       | Prod (t1, t2) => Prod (f d x v t1, f d x v t2) *)
(*       | UniI (s, bind, r) => UniI (substx_i_s d x v s, substx_i_ibind f d x v bind, r) *)
(*       | MtVar y => MtVar y *)
(*       | MtApp (t1, t2) => MtApp (f d x v t1, f d x v t2) *)
(*       | MtAbs (k, bind, r) => MtAbs (k, substx_i_tbind f d x v bind, r) *)
(*       | MtAppI (t, i) => MtAppI (f d x v t, substx_i_i d x v i) *)
(*       | MtAbsI (b, bind, r) => MtAbsI (b, substx_i_ibind f d x v bind, r) *)
(*       | BaseType a => BaseType a *)
(*       | UVar a => b *)
(*       | TDatatype (Abs dt, r) => *)
(*         let *)
(*           fun on_constr d x v b = substx_i_ibinds substx_i_s (substx_pair (f, substx_list substx_i_i)) d x v b *)
(*           fun on_constr_decl d x v (name, c, r) = (name, on_constr d x v c, r) *)
(*           val dt = Bind $ from_Unbound dt *)
(*           val Bind dt = substx_i_tbind (substx_i_tbinds return4 (substx_pair (return4, substx_list on_constr_decl))) d x v dt *)
(*           val dt = to_Unbound dt *)
(*         in *)
(*           TDatatype (Abs dt, r) *)
(*         end *)
(* in *)
(* val substx_i_mt = f *)
(* end *)

(* local *)
(*   fun f d x v b = *)
(*     case b of *)
(* 	Mono t => Mono (substx_i_mt d x v t) *)
(*       | Uni (bind, r) => Uni (substx_i_tbind f d x v bind, r) *)
(* in *)
(* val substx_i_t = f *)
(* end *)

structure TypeSubst = TypeSubstFn (Type)
open TypeSubst

fun substx_i_mt a = subst_i_mt_fn (substx_i_i, substx_i_s) a
fun substx_i_t a = subst_i_t_fn (substx_i_i, substx_i_s) a
fun subst_i_mt (v : idx) (b : mtype) : mtype = substx_i_mt 0 0 v b
fun subst_i_t (v : idx) (b : ty) : ty = substx_i_t 0 0 v b

(* fun substx_t_ibind f (di, dt) x v (Bind (name, inner) : ('name * 'b) ibind) = *)
(*   Bind (name, f (di + 1, dt) x v inner) *)

(* fun substx_t_tbind f (di, dt) x v (Bind (name, inner) : ('name * 'b) tbind) = *)
(*   Bind (name, f (di, dt + 1) (x + 1) v inner) *)
       
(* fun substx_t_ibinds f_cls f d x v (b : ('classifier, 'name, 'inner) ibinds) = substx_binds substx_t_ibind f_cls f d x v b *)
(* (* fun substx_t_ibinds f_cls f d x v b = *) *)
(*   (* case b of *) *)
(*   (*     BindNil a => BindNil (f d x v a) *) *)
(* (*   | BindCons (cls, bind) => BindCons (f_cls d x v cls, substx_t_ibind (substx_t_ibinds f_cls f) d x v bind) *) *)
                                                                                           
(* fun substx_t_tbinds f_cls f d x v (b : ('classifier, 'name, 'inner) tbinds) = substx_binds substx_t_tbind f_cls f d x v b *)
(* (* fun substx_t_tbinds f_cls f d x v b = *) *)
(* (*   case b of *) *)
(* (*       BindNil a => BindNil (f d x v a) *) *)
(* (*     | BindCons (cls, bind) => BindCons (f_cls d x v cls, substx_t_tbind (substx_t_tbinds f_cls f) d x v bind) *) *)

(* local *)
(*   fun f d x v (b : mtype) : mtype = *)
(*     case b of *)
(* 	Arrow (t1, i, t2) => Arrow (f d x v t1, i, f d x v t2) *)
(*       | TyNat (i, r) => TyNat (i, r) *)
(*       | TyArray (t, i) => TyArray (f d x v t, i) *)
(*       | Unit r => Unit r *)
(*       | Prod (t1, t2) => Prod (f d x v t1, f d x v t2) *)
(*       | UniI (s, bind, r) => UniI (s, substx_t_ibind f d x v bind, r) *)
(*       | MtVar y => *)
(*         substx_long_id MtVar x (fn () => shiftx_i_mt 0 (fst d) $ shiftx_t_mt 0 (snd d) v) y *)
(*       | MtAbs (k, bind, r) => MtAbs (k, substx_t_tbind f d x v bind, r) *)
(*       | MtApp (t1, t2) => MtApp (f d x v t1, f d x v t2) *)
(*       | MtAbsI (s, bind, r) => MtAbsI (s, substx_t_ibind f d x v bind, r) *)
(*       | MtAppI (t, i) => MtAppI (f d x v t, i) *)
(*       | BaseType a => BaseType a *)
(*       | UVar a => b *)
(*       | TDatatype (Abs dt, r) => *)
(*         let *)
(*           fun on_constr d x v b = substx_t_ibinds return4 (substx_pair (f, return4)) d x v b *)
(*           fun on_constr_decl d x v (name, c, r) = (name, on_constr d x v c, r) *)
(*           val dt = Bind $ from_Unbound dt *)
(*           val Bind dt = substx_t_tbind (substx_t_tbinds return4 (substx_pair (return4, substx_list on_constr_decl))) d x v dt *)
(*           val dt = to_Unbound dt *)
(*         in *)
(*           TDatatype (Abs dt, r) *)
(*         end *)
(* in *)
(* val substx_t_mt = f *)
(* end *)

(* fun substx_t_t d x (v : mtype) (b : ty) : ty = *)
(*   case b of *)
(*       Mono t => Mono (substx_t_mt d x v t) *)
(*     | Uni (bind, r) => Uni (substx_t_tbind substx_t_t d x v bind, r) *)
                           
fun visit_MtVar (d, x, v) env y =
  let
    fun add_depth (di, dt) (di', dt') = (idepth_add (di, di'), tdepth_add (dt, dt'))
    fun get_di (di, dt) = di
    fun get_dt (di, dt) = dt
    val x = x + unTDepth (get_dt env)
    val (di, dt) = add_depth d env
  in
    substx_long_id MtVar x (fn () => shiftx_i_mt 0 (unIDepth di) $ shiftx_t_mt 0 (unTDepth dt) v) y
  end
    
val subst_t_params = visit_MtVar

fun substx_t_mt a = unuse_idepth_tdepth (subst_t_mt_fn subst_t_params) a
      
fun substx_t_t a = unuse_idepth_tdepth (subst_t_t_fn subst_t_params) a
      
fun subst_t_mt (v : mtype) (b : mtype) : mtype = substx_t_mt (0, 0) 0 v b
                                                             
fun subst_t_t v b = substx_t_t (0, 0) 0 v b

fun subst_is_mt is t =
  fst (foldl (fn (i, (t, x)) => (substx_i_mt x x i t, x - 1)) (t, length is - 1) is)
fun subst_ts_mt vs b =
  fst (foldl (fn (v, (b, x)) => (substx_t_mt (0, x) x v b, x - 1)) (b, length vs - 1) vs)
      
(* VC operations *)

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

open Subst

end

(* Test that the result of [ExprFun] matches some signatures. We don't use a signature ascription because signature ascription (transparent or opaque) hides components that are not in the signature. SML should have a "signature check" kind of ascription. *)
functor TestExprFnSignatures (Params : EXPR_PARAMS) = struct
structure M : IDX = ExprFn (Params)
structure M2 : TYPE = ExprFn (Params)
structure M3 : EXPR = ExprFn (Params)
end
