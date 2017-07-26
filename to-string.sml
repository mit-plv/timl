signature CAN_TO_STRING = sig
  type var
  type idx
  include UVAR_I
  include UVAR_T
  val str_raw_var : var -> string
  val str_var : (ToStringUtil.context -> string list) -> ToStringUtil.global_context -> string list -> var -> string
  val lookup_module : ToStringUtil.global_context -> string -> string * ToStringUtil.context
  val str_uvar_bs : ('a -> string) -> 'a uvar_bs -> string
  val str_uvar_i : ('bsort -> string) * ('idx -> string) -> ('bsort, 'idx) uvar_i -> string
  val str_uvar_s : ('sort -> string) -> ('bsort, 'sort) uvar_s -> string
  val str_uvar_mt : ('sort -> string) * ('kind -> string) * ('mtype -> string) -> ('sort, 'kind, 'mtype) uvar_mt -> string
end

functor ToStringFn (structure Expr : IDX_TYPE_EXPR where type Idx.base_sort = BaseSorts.base_sort
                                               and type Type.base_type = BaseTypes.base_type
                                               and type Idx.region = Region.region
                                               and type Idx.name = string * Region.region
                                               and type Type.name = string * Region.region
                                               and type Type.region = Region.region
                                               and type mod_id = string * Region.region
                    structure CanToString : CAN_TO_STRING
                    sharing type Expr.Type.bsort = Expr.Idx.bsort
                    sharing type CanToString.var = Expr.var
                    sharing type CanToString.idx = Expr.Idx.idx
                    sharing type CanToString.uvar_bs = Expr.Idx.uvar_bs
                    sharing type CanToString.uvar_i = Expr.Idx.uvar_i
                    sharing type CanToString.uvar_s = Expr.Idx.uvar_s
                    sharing type CanToString.uvar_mt = Expr.Type.uvar_mt
                   ) = struct

open CanToString
open Expr
open Idx
open Type
open Gctx
open List
open Util
open BaseSorts
open BaseTypes
open Operators
open Pattern
open Region
structure IdxUtil = IdxUtilFn (structure Idx = Idx
                               val dummy = dummy
                              )
open IdxUtil
structure TypeUtil = TypeUtilFn (structure Type = Type
                               (* val dummy = Region.dummy *)
                              )
open TypeUtil
structure ExprUtil = ExprUtilFn (Expr)
open ExprUtil
open Bind

infixr 0 $

structure StringUVar = struct
type 'a uvar_bs = string
type ('a, 'b) uvar_i = string
type ('a, 'b) uvar_s = string
type ('a, 'b, 'c) uvar_mt = string
end
                         
structure NamefulIdx = IdxFn (structure UVarI = StringUVar
                             type base_sort = base_sort
                             type var = string
                             type name = name
                             type region = region
                             type 'idx exists_anno = unit
                            )
(* open NamefulIdx *)
(* structure T = NamefulIdx *)

structure NamefulIdxUtil = IdxUtilFn (structure Idx = NamefulIdx
                                      val dummy = dummy
                              )
                             
structure IdxVisitor = IdxVisitorFn (structure S = Idx
                                     structure T = NamefulIdx)
(* open IdxVisitor *)
structure IV = IdxVisitor
                           
(******** the "export" visitor: convertnig de Bruijn indices to nameful terms **************)
    
fun export_idx_visitor_vtable cast gctx (* : ((* 'this *)string list IV.idx_visitor, ToStringUtil.scontext) IV.idx_visitor_vtable *) =
  let
    fun extend this env name = fst name :: env
    fun visit_var this ctx x =
      str_var #1 gctx ctx x
    val str_i = str_i gctx
    val str_s = str_s gctx
    fun visit_uvar_bs this ctx u =
      str_uvar_bs str_bs u
    fun visit_uvar_i this ctx u =
      str_uvar_i (str_bs, str_i []) u
    fun visit_uvar_s this ctx u =
      str_uvar_s (str_s []) u
  in
    IV.default_idx_visitor_vtable
      cast
      extend
      visit_var
      visit_uvar_bs
      visit_uvar_i
      visit_uvar_s
      (ignore_this_env strip_quan)
  end

and new_export_idx_visitor a = IV.new_idx_visitor export_idx_visitor_vtable a
    
and export_bs b =
  let
    val visitor as (IV.IdxVisitor vtable) = new_export_idx_visitor empty
  in
    #visit_bsort vtable visitor [] b
  end

and export_i gctx ctx b =
  let
    val visitor as (IV.IdxVisitor vtable) = new_export_idx_visitor gctx
  in
    #visit_idx vtable visitor ctx b
  end

and export_p gctx ctx b =
  let
    val visitor as (IV.IdxVisitor vtable) = new_export_idx_visitor gctx
  in
    #visit_prop vtable visitor ctx b
  end

and export_s gctx ctx b =
  let
    val visitor as (IV.IdxVisitor vtable) = new_export_idx_visitor gctx
  in
    #visit_sort vtable visitor ctx b
  end

and strn_bs s =
  let
    open NamefulIdx
    open NamefulIdxUtil
  in
    case s of
        Base s => str_b s
      | BSArrow (s1, s2) =>
        let
          fun default () = sprintf "($ => $)" [strn_bs s1, strn_bs s2]
        in
          case is_time_fun s of
              SOME n => if n = 0 then "Time" else sprintf "(Fun $)" [str_int n]
            | NONE => default ()
        end
      | UVarBS u => u
  end

and strn_i i =
    let
      open NamefulIdx
      open NamefulIdxUtil
    in
    (* case is_IApp_UVarI i of *)
    (*     SOME ((x, _), args) => sprintf "($ ...)" [str_uvar_i (str_bs, str_i []) x] *)
    (*   | NONE => *)
      case i of
          VarI x => x
        | IConst (c, _) => str_idx_const c
        | UnOpI (opr, i, _) =>
          (case opr of
               IUDiv n => sprintf "($ / $)" [strn_i i, str_int n]
             | IUExp s => sprintf "($ ^ $)" [strn_i i, s]
             | _ => sprintf "($ $)" [str_idx_un_op opr, strn_i i]
          )
        | BinOpI (opr, i1, i2) =>
          (case opr of
               IApp =>
               let
                 val (f, is) = collect_IApp i
                 val is = f :: is
               in
                 sprintf "($)" [join " " $ map strn_i is]
               end
             | AddI =>
               let
                 val is = collect_AddI_left i
               in
                 sprintf "($)" [join " + " $ map strn_i is]
               end
             | _ => sprintf "($ $ $)" [strn_i i1, str_idx_bin_op opr, strn_i i2]
          )
        | Ite (i1, i2, i3, _) => sprintf "(ite $ $ $)" [strn_i i1, strn_i i2, strn_i i3]
        | IAbs _ =>
          let
            val (bs_names, i) = collect_IAbs i
          in
            sprintf "(fn $ => $)" [join " " $ map (fn (b, name) => sprintf "($ : $)" [name, strn_bs b]) bs_names, strn_i i]
          end
        (* | IAbs ((name, _), i, _) => sprintf "(fn $ => $)" [name, strn_i (name :: ctx) i] *)
        | UVarI (u, _) => u
    end
                                 
and strn_p p =
  let
    open NamefulIdx
  in
    case p of
        PTrueFalse (b, _) => str_bool b
      | Not (p, _) => sprintf "(~ $)" [strn_p p]
      | BinConn (opr, p1, p2) => sprintf "($ $ $)" [strn_p p1, str_bin_conn opr, strn_p p2]
      (* | BinPred (BigO, i1, i2) => sprintf "($ $ $)" [strn_bin_pred BigO, strn_i ctx i1, strn_i ctx i2] *)
      | BinPred (opr, i1, i2) => sprintf "($ $ $)" [strn_i i1, str_bin_pred opr, strn_i i2]
      | Quan (q, bs, Bind ((name, _), p), _) => sprintf "($ ($ : $) $)" [str_quan q, name, strn_bs bs, strn_p p]
  end

and strn_s s =
  let
    open NamefulIdx
    open NamefulIdxUtil
  in
    (* case is_SApp_UVarS s of *)
    (*     SOME ((x, _), args) => sprintf "($ ...)" [str_uvar_s (strn_s []) x] *)
    (*   | NONE => *)
    case s of
        Basic (bs, _) => strn_bs bs
      | Subset ((bs, _), Bind ((name, _), p), _) =>
        let
          fun default () = sprintf "{ $ : $ | $ }" [name, strn_bs bs, strn_p p]
        in
          case (is_time_fun bs, p) of
              (SOME arity, BinPred (BigO, VarI x, i2)) =>
              if x = name then
                sprintf "BigO $ $" [str_int arity, strn_i i2]
              else
                default ()
            | _ => default ()
        end
      | UVarS (u, _) => u
      | SAbs (s1, Bind ((name, _), s), _) =>
        sprintf "(fn $ : $ => $)" [name, strn_bs s1, strn_s s]
      | SApp (s, i) => sprintf "($ $)" [strn_s s, strn_i i]
  end

and str_bs b =
  let
    val b = export_bs b
  in
    strn_bs b
  end
    
and str_i gctx ctx b =
  let
    val b = export_i gctx ctx b
  in
    strn_i b
  end
    
and str_s gctx ctx b =
  let
    val b = export_s gctx ctx b
  in
    strn_s b
  end
    
fun str_p gctx ctx b =
  let
    val b = export_p gctx ctx b
  in
    strn_p b
  end
    
(* (*********** the "export" visitor: convertnig de Bruijn indices to nameful terms *****) *)

(* type naming_ctx = iname list * tname list * ename list *)
(* fun export_expr_visitor_vtable cast (visit_var, visit_idx, visit_sort, visit_ty) : ('this, naming_ctx, 'var, 'idx, 'sort, 'kind, 'ty, 'var2, 'idx2, 'sort2, 'kind, 'ty2) expr_visitor_vtable = *)
(*   let *)
(*     fun extend_i this (sctx, kctx, tctx) name = (name :: sctx, kctx, tctx) *)
(*     fun extend_t this (sctx, kctx, tctx) name = (sctx, name :: kctx, tctx) *)
(*     fun extend_e this (sctx, kctx, tctx) name = (sctx, kctx, name :: tctx) *)
(*     fun only_s f this (sctx, kctx, tctx) name = f sctx name *)
(*     fun only_sk f this (sctx, kctx, tctx) name = f (sctx, kctx) name *)
(*   in *)
(*     default_expr_visitor_vtable *)
(*       cast *)
(*       extend_i *)
(*       extend_t *)
(*       extend_e *)
(*       (ignore_this visit_var) *)
(*       (only_s visit_idx) *)
(*       (only_s visit_sort) *)
(*       (only_sk visit_ty) *)
(*   end *)

(* fun new_export_expr_visitor params = new_expr_visitor export_expr_visitor_vtable params *)
    
(* fun export_fn params ctx e = *)
(*   let *)
(*     val visitor as (ExprVisitor vtable) = new_export_expr_visitor params *)
(*   in *)
(*     #visit_expr vtable visitor ctx e *)
(*   end *)
    
(* (***************** the "import" (or name-resolving) visitor: converting nameful terms to de Bruijn indices **********************)     *)
    
(* fun import_idx_visitor_vtable cast gctx : ('this, scontext) idx_visitor_vtable = *)
(*   let *)
(*     fun extend this env x = fst x :: env *)
(*     fun visit_var this env x = *)
(*       on_long_id gctx #1 env x *)
(*     fun visit_quan _ _ q = on_quan q *)
(*   in *)
(*     default_idx_visitor_vtable *)
(*       cast *)
(*       extend *)
(*       visit_var *)
(*       visit_noop *)
(*       visit_noop *)
(*       visit_noop *)
(*       visit_quan *)
(*   end *)

(* fun new_import_idx_visitor a = new_idx_visitor import_idx_visitor_vtable a *)
    
(* fun on_bsort b = *)
(*   let *)
(*     val visitor as (IdxVisitor vtable) = new_import_idx_visitor empty *)
(*   in *)
(*     #visit_bsort vtable visitor [] b *)
(*   end *)
    
(* fun on_idx gctx ctx b = *)
(*   let *)
(*     val visitor as (IdxVisitor vtable) = new_import_idx_visitor gctx *)
(*   in *)
(*     #visit_idx vtable visitor ctx b *)
(*   end *)
    
(* fun str_bs (s : bsort) = *)
(*   case s of *)
(*       Base s => str_b s *)
(*     | BSArrow (s1, s2) => *)
(*       let *)
(*         fun default () = sprintf "($ => $)" [str_bs s1, str_bs s2] *)
(*       in *)
(*         case is_time_fun s of *)
(*             SOME n => if n = 0 then "Time" else sprintf "(Fun $)" [str_int n] *)
(*           | NONE => default () *)
(*       end *)
(*     | UVarBS u => str_uvar_bs str_bs u *)

fun str_raw_option f a = case a of SOME a => sprintf "SOME ($)" [f a] | NONE => "NONE"

fun str_raw_name (s, _) = s

fun str_raw_bind f (Bind (_, a)) = sprintf "Bind ($)" [f a]

fun str_raw_bs b =
  case b of
      Base s => sprintf "Base ($)" [str_b s]
    | BSArrow (s1, s2) => sprintf "BSArrow ($, $)" [str_raw_bs s1, str_raw_bs s2]
    | UVarBS u => "UVarBS"

fun str_raw_i i =
  case i of
      VarI x => sprintf "VarI ($)" [str_raw_var x]
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
    | MtVar x => sprintf "MtVar ($)" [str_raw_var x]
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

(* fun str_i gctx ctx (i : idx) : string = *)
(*   let *)
(*     val str_i = str_i gctx *)
(*   in *)
(*     (* case is_IApp_UVarI i of *) *)
(*     (*     SOME ((x, _), args) => sprintf "($ ...)" [str_uvar_i (str_bs, str_i []) x] *) *)
(*     (*   | NONE => *) *)
(*     case i of *)
(*         VarI x => str_var #1 gctx ctx x *)
(*       | IConst (c, _) => str_idx_const c *)
(*       | UnOpI (opr, i, _) => *)
(*         (case opr of *)
(*              IUDiv n => sprintf "($ / $)" [str_i ctx i, str_int n] *)
(*            | IUExp s => sprintf "($ ^ $)" [str_i ctx i, s] *)
(*            | _ => sprintf "($ $)" [str_idx_un_op opr, str_i ctx i] *)
(*         ) *)
(*       | BinOpI (opr, i1, i2) => *)
(*         (case opr of *)
(*              IApp => *)
(*              let *)
(*                val (f, is) = collect_IApp i *)
(*                val is = f :: is *)
(*              in *)
(*                sprintf "($)" [join " " $ map (str_i ctx) $ is] *)
(*              end *)
(*            | AddI => *)
(*              let *)
(*                val is = collect_AddI_left i *)
(*              in *)
(*                sprintf "($)" [join " + " $ map (str_i ctx) is] *)
(*              end *)
(*            | _ => sprintf "($ $ $)" [str_i ctx i1, str_idx_bin_op opr, str_i ctx i2] *)
(*         ) *)
(*       | Ite (i1, i2, i3, _) => sprintf "(ite $ $ $)" [str_i ctx i1, str_i ctx i2, str_i ctx i3] *)
(*       | IAbs _ => *)
(*         let *)
(*           val (bs_names, i) = collect_IAbs i *)
(*           val names = map snd bs_names *)
(*         in *)
(*           sprintf "(fn $ => $)" [join " " $ map (fn (b, name) => sprintf "($ : $)" [name, str_bs b]) bs_names, str_i (rev names @ ctx) i] *)
(*         end *)
(*       (* | IAbs ((name, _), i, _) => sprintf "(fn $ => $)" [name, str_i (name :: ctx) i] *) *)
(*       | UVarI (u, _) => str_uvar_i (str_bs, str_i []) u *)
(*   end *)

(* fun str_p gctx ctx p = *)
(*   let *)
(*     val str_p = str_p gctx *)
(*   in *)
(*     case p of *)
(*         PTrueFalse (b, _) => str_bool b *)
(*       | Not (p, _) => sprintf "(~ $)" [str_p ctx p] *)
(*       | BinConn (opr, p1, p2) => sprintf "($ $ $)" [str_p ctx p1, str_bin_conn opr, str_p ctx p2] *)
(*       (* | BinPred (BigO, i1, i2) => sprintf "($ $ $)" [str_bin_pred BigO, str_i ctx i1, str_i ctx i2] *) *)
(*       | BinPred (opr, i1, i2) => sprintf "($ $ $)" [str_i gctx ctx i1, str_bin_pred opr, str_i gctx ctx i2] *)
(*       | Quan (q, bs, Bind ((name, _), p), _) => sprintf "($ ($ : $) $)" [str_quan q, name, str_bs bs, str_p (name :: ctx) p] *)
(*   end *)

(* fun str_s gctx ctx (s : sort) : string = *)
(*   let *)
(*     val str_s = str_s gctx *)
(*   in *)
(*     (* case is_SApp_UVarS s of *) *)
(*     (*     SOME ((x, _), args) => sprintf "($ ...)" [str_uvar_s (str_s []) x] *) *)
(*     (*   | NONE => *) *)
(*     case s of *)
(*         Basic (bs, _) => str_bs bs *)
(*       | Subset ((bs, _), Bind ((name, _), p), _) => *)
(*         let *)
(*           fun default () = sprintf "{ $ : $ | $ }" [name, str_bs bs, str_p gctx (name :: ctx) p] *)
(*         in *)
(*           case (is_time_fun bs, p) of *)
(*               (SOME arity, BinPred (BigO, VarI x, i2)) => *)
(*               if str_var #1 gctx (name :: ctx) x = name then *)
(*                 sprintf "BigO $ $" [str_int arity, str_i gctx (name :: ctx) i2] *)
(*               else *)
(*                 default () *)
(*             | _ => default () *)
(*         end *)
(*       | UVarS (u, _) => str_uvar_s (str_s []) u *)
(*       | SAbs (s1, Bind ((name, _), s), _) => *)
(*         sprintf "(fn $ : $ => $)" [name, str_bs s1, str_s (name :: ctx) s] *)
(*       | SApp (s, i) => sprintf "($ $)" [str_s ctx s, str_i gctx ctx i] *)
(*   end *)

fun export_k (n, sorts) = (n, map export_bs sorts)
  
(* val str_Type = "*" *)
val str_Type = "Type"
                 
fun strn_k (n, sorts) : string =
  if n = 0 andalso null sorts then str_Type
  else
    sprintf "($$$)" [if n = 0 then "" else join " => " (repeat n str_Type) ^ " => ", if null sorts then "" else join " => " (map strn_bs sorts) ^ " => ", str_Type]

fun str_k a = (strn_k o export_k) a
    
datatype 'a bind = 
         KindingT of string
         | SortingT of string * 'a

fun strn_tbinds binds =
  let
    fun f bind =
      case bind of
          KindingT name => KindingT name
        | SortingT (name, s) => SortingT (name, strn_s s)
    val binds = map f binds
  in
    binds
  end
    
structure NamefulType = TypeFn (structure Idx = NamefulIdx
                                structure UVarT = StringUVar
                                type base_type = base_type
                            )

structure NamefulTypeUtil = TypeUtilFn (structure Type = NamefulType
                                      val dummy = dummy
                              )
                             
fun collect_Uni_UniI t =
  let
    open NamefulTypeUtil
    val (tnames, t) = collect_Uni t
    val tnames = map fst tnames
    val (binds, t) = collect_UniI t
    val binds = map (mapFst fst) binds
  in
    (map KindingT tnames @ map SortingT binds, t)
  end

structure TypeVisitor = TypeVisitorFn (structure S = Type
                                     structure T = NamefulType)
structure TV = TypeVisitor
                           
fun export_type_visitor_vtable cast gctx (* : ((string list * string list) TV.type_visitor, string list * string list) TV.type_visitor_vtable *) =
  let
    fun extend_i this (sctx, kctx) name = (fst name :: sctx, kctx)
    fun extend_t this (sctx, kctx) name = (sctx, fst name :: kctx)
    fun visit_var this (sctx, kctx) x =
      str_var #2 gctx kctx x
    fun for_idx f this (sctx, kctx) data = f gctx sctx data
    val str_mt = str_mt gctx
    fun visit_uvar_mt this ctx u =
      let
        (* fun str_region ((left, right) : region) = sprintf "($,$)-($,$)" [str_int (#line left), str_int (#col left), str_int (#line right), str_int (max (#col right) 0)] *)
      in
        (* (surround "[" "] " $ str_region r) ^ *) str_uvar_mt (str_raw_bs, str_raw_k, str_mt ([], [])) u
      end
  in
    TV.default_type_visitor_vtable
      cast
      extend_i
      extend_t
      visit_var
      (ignore_this_env export_bs)
      (for_idx export_i)
      (for_idx export_s)
      (ignore_this_env export_k)
      visit_uvar_mt
  end

and new_export_type_visitor a = TV.new_type_visitor export_type_visitor_vtable a
    
and export_mt gctx ctx b =
  let
    val visitor as (TV.TypeVisitor vtable) = new_export_type_visitor gctx
  in
    #visit_mtype vtable visitor ctx b
  end

and strn_mt t =
  let
    open NamefulIdxUtil
    open NamefulType
    open NamefulTypeUtil
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
    fun strn_apps t = 
      let
        val (f, args) = collect_MtAppI_or_MtApp t
      in
        sprintf "($$)" [strn_mt f, join_prefix " " $ map (map_sum (strn_i, strn_mt)) $ args]
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
    fun strn_abs t =
      let
        val (binds, t) = collect_MtAbsI_or_MtAbs t
        (* val () = println $ strn_int (length binds) *)
        fun strn_bind (c, name) =
          case c of
              inl s => sprintf "{$ : $}" [name, strn_bs s(* "..." *)]
            | inr k => sprintf "[$ : $]" [name, strn_k k]
        val binds = map strn_bind binds
        (* val () = println $ strn_int (length binds) *)
        val t = strn_mt t
      in
        sprintf "(fn$ => $)" [join_prefix " " binds, t]
      end
  in
    (* case is_MtApp_UVar t of *)
    (*     SOME ((x, _), i_args, t_args) => sprintf "($ ...)" [strn_uvar_mt (strn_raw_bs, strn_raw_k, strn_mt ([], [])) x] *)
    (*   | NONE => *)
    case t of
        Arrow (t1, d, t2) =>
        if is_T0 d then
          sprintf "($ -> $)" [strn_mt t1, strn_mt t2]
        else
          sprintf "($ -- $ --> $)" [strn_mt t1, strn_i d, strn_mt t2]
      | TyNat (i, _) => sprintf "(nat $)" [strn_i i]
      | TyArray (t, i) => sprintf "(arr $ $)" [strn_mt t, strn_i i]
      | Unit _ => "unit"
      | Prod (t1, t2) => sprintf "($ * $)" [strn_mt t1, strn_mt t2]
      | UniI _ =>
        let
          val (binds, t) = collect_UniI t
          val binds = map (mapFst fst) binds
        in
          strn_uni (map SortingT binds, t)
        end
      | MtVar x => x
      | MtApp (t1, t2) =>
        (* sprintf "($ $)" [strn_mt ctx t1, strn_mt ctx t2] *)
        strn_apps t
      | MtAbs _ =>
        (* sprintf "(fn [$ : $] => $)" [name, strn_k gctx sctx k, strn_mt (sctx, name :: kctx) t] *)
        strn_abs t
      | MtAppI _ =>
        (* sprintf "($ {$})" [strn_mt ctx t, strn_i gctx sctx i] *)
        strn_apps t
      | MtAbsI _ =>
        (* sprintf "(fn {$ : $} => $)" [name, strn_s gctx sctx s, strn_mt (name :: sctx, kctx) t] *)
        strn_abs t
      | BaseType (bt, _) => str_bt bt
      | UVar (u, r) => u
      | TDatatype (dt, _) => "(datatype ...)"
  end

and strn_uni (binds, t) =
    let 
      val binds = strn_tbinds binds
      fun f bind =
        case bind of
            KindingT name => name
          | SortingT (name, s) => sprintf "{$ : $}" [name, s]
      val binds = map f binds
    in
      sprintf "(forall$, $)" [join_prefix " " binds, strn_mt t]
    end
      
and str_mt gctx ctx b =
  let
    val b = export_mt gctx ctx b
  in
    strn_mt b
  end
    
fun export_t gctx ctx b =
  let
    val visitor as (TV.TypeVisitor vtable) = new_export_type_visitor gctx
  in
    #visit_ty vtable visitor ctx b
  end

fun strn_t t =
  let
    open NamefulType
  in
    case t of
        Mono t => strn_mt t
      | Uni _ => strn_uni (collect_Uni_UniI t)
  end

and str_t gctx ctx b =
  let
    val b = export_t gctx ctx b
  in
    strn_t b
  end
    
(* fun str_k ((n, sorts) : kind) : string = *)
(*   if n = 0 andalso null sorts then str_Type *)
(*   else *)
(*     sprintf "($$$)" [if n = 0 then "" else join " => " (repeat n str_Type) ^ " => ", if null sorts then "" else join " => " (map str_bs sorts) ^ " => ", str_Type] *)

(* fun str_mt gctx (ctx as (sctx, kctx)) (t : mtype) : string = *)
(*   let *)
(*     val str_mt = str_mt gctx *)
(*     fun collect_MtAppI_or_MtApp t = *)
(*       case t of *)
(*           MtAppI (t, i) => *)
(*           let  *)
(*             val (f, args) = collect_MtAppI_or_MtApp t *)
(*           in *)
(*             (f, args @ [inl i]) *)
(*           end *)
(*         | MtApp (t, arg) => *)
(*           let  *)
(*             val (f, args) = collect_MtAppI_or_MtApp t *)
(*           in *)
(*             (f, args @ [inr arg]) *)
(*           end *)
(*         | _ => (t, []) *)
(*     fun map_sum (f_l, f_r) a = *)
(*       case a of *)
(*           inl v => f_l v *)
(*         | inr v => f_r v *)
(*     fun str_apps t =  *)
(*       let *)
(*         val (f, args) = collect_MtAppI_or_MtApp t *)
(*       in *)
(*         sprintf "($$)" [str_mt ctx f, join_prefix " " $ map (map_sum (str_i gctx sctx, str_mt ctx)) $ args] *)
(*       end *)
(*     fun collect_MtAbsI_or_MtAbs t = *)
(*       case t of *)
(*           MtAbsI (s, Bind ((name, _), t), _) => *)
(*           let *)
(*             val (binds, t) = collect_MtAbsI_or_MtAbs t *)
(*           in *)
(*             ((inl s, name) :: binds, t) *)
(*           end *)
(*         | MtAbs (k, Bind ((name, _), t), _) => *)
(*           let *)
(*             val (binds, t) = collect_MtAbsI_or_MtAbs t *)
(*           in *)
(*             ((inr k, name) :: binds, t) *)
(*           end *)
(*         | _ => ([], t) *)
(*     fun str_abs t = *)
(*       let *)
(*         val (binds, t) = collect_MtAbsI_or_MtAbs t *)
(*         (* val () = println $ str_int (length binds) *) *)
(*         fun iter ((c, name), (acc, (sctx, kctx))) = *)
(*           case c of *)
(*               inl s => (sprintf "{$ : $}" [name, str_bs s(* "..." *)] :: acc, (name :: sctx, kctx)) *)
(*             | inr k => (sprintf "[$ : $]" [name, str_k k] :: acc, (sctx, name :: kctx)) *)
(*         val (binds, (sctx, kctx)) = foldl iter ([], (sctx, kctx)) binds *)
(*         val binds = rev binds *)
(*         (* val () = println $ str_int (length binds) *) *)
(*         val t = str_mt (sctx, kctx) t *)
(*       in *)
(*         sprintf "(fn$ => $)" [join_prefix " " binds, t] *)
(*       end *)
(*   in *)
(*     (* case is_MtApp_UVar t of *) *)
(*     (*     SOME ((x, _), i_args, t_args) => sprintf "($ ...)" [str_uvar_mt (str_raw_bs, str_raw_k, str_mt ([], [])) x] *) *)
(*     (*   | NONE => *) *)
(*     case t of *)
(*         Arrow (t1, d, t2) => *)
(*         if eq_i d (T0 dummy) then *)
(*           sprintf "($ -> $)" [str_mt ctx t1, str_mt ctx t2] *)
(*         else *)
(*           sprintf "($ -- $ --> $)" [str_mt ctx t1, str_i gctx sctx d, str_mt ctx t2] *)
(*       | TyNat (i, _) => sprintf "(nat $)" [str_i gctx sctx i] *)
(*       | TyArray (t, i) => sprintf "(arr $ $)" [str_mt ctx t, str_i gctx sctx i] *)
(*       | Unit _ => "unit" *)
(*       | Prod (t1, t2) => sprintf "($ * $)" [str_mt ctx t1, str_mt ctx t2] *)
(*       | UniI _ => *)
(*         let *)
(*           val (binds, t) = collect_UniI t *)
(*           val binds = map (mapFst fst) binds *)
(*         in *)
(*           str_uni gctx ctx (map SortingT binds, t) *)
(*         end *)
(*       | MtVar x => str_var #2 gctx kctx x *)
(*       | MtApp (t1, t2) => *)
(*       (* sprintf "($ $)" [str_mt ctx t1, str_mt ctx t2] *) *)
(*         str_apps t *)
(*       | MtAbs _ => *)
(*       (* sprintf "(fn [$ : $] => $)" [name, str_k gctx sctx k, str_mt (sctx, name :: kctx) t] *) *)
(*         str_abs t *)
(*       | MtAppI _ => *)
(*       (* sprintf "($ {$})" [str_mt ctx t, str_i gctx sctx i] *) *)
(*         str_apps t *)
(*       | MtAbsI _ => *)
(*         (* sprintf "(fn {$ : $} => $)" [name, str_s gctx sctx s, str_mt (name :: sctx, kctx) t] *) *)
(*         str_abs t *)
(*       | BaseType (bt, _) => str_bt bt *)
(*       | UVar (u, r) => *)
(*         let *)
(*           fun str_region ((left, right) : region) = sprintf "($,$)-($,$)" [str_int (#line left), str_int (#col left), str_int (#line right), str_int (max (#col right) 0)] *)
(*         in *)
(*           (* (surround "[" "] " $ str_region r) ^ *) str_uvar_mt (str_raw_bs, str_raw_k, str_mt ([], [])) u *)
(*         end *)
(*       | TDatatype (dt, _) => "(datatype ...)" *)
(*   end *)

(* and str_uni gctx ctx (binds, t) = *)
(*     let  *)
(*       val (binds, ctx) = str_tbinds gctx ctx binds *)
(*       fun f bind = *)
(*         case bind of *)
(*             KindingT name => name *)
(*           | SortingT (name, s) => sprintf "{$ : $}" [name, s] *)
(*       val binds = map f binds *)
(*     in *)
(*       sprintf "(forall$, $)" [join_prefix " " binds, str_mt gctx ctx t] *)
(*     end *)
      
(* fun str_t gctx (ctx as (sctx, kctx)) (t : ty) : string = *)
(*   case t of *)
(*       Mono t => str_mt gctx ctx t *)
(*     | Uni _ => str_uni gctx ctx (collect_Uni_UniI t) *)

fun decorate_var eia s = (if eia then "@" else "") ^ s
    
structure NamefulExpr = ExprFn (
  type var = string
  type cvar = string
  type mod_id = string
  type idx = NamefulIdx.idx
  type sort = NamefulIdx.sort
  type mtype = NamefulType.mtype
  type ptrn_constr_tag = ptrn_constr_tag
  type ty = NamefulType.ty
  type kind = NamefulType.kind
)

structure NamefulExprUtil = ExprUtilFn (NamefulExpr)
                             
structure ToStringExprVisitor = ExprVisitorFn (structure S = Expr
                                       structure T = NamefulExpr)
structure EV = ToStringExprVisitor

open LongId
       
fun export_expr_visitor_vtable cast gctx =
  let
    fun extend_i this (sctx, kctx, cctx, tctx) name = (Name2str name :: sctx, kctx, cctx, tctx)
    fun extend_t this (sctx, kctx, cctx, tctx) name = (sctx, Name2str name :: kctx, cctx, tctx)
    fun extend_c this (sctx, kctx, cctx, tctx) name = (sctx, kctx, Name2str name :: cctx, tctx)
    fun extend_e this (sctx, kctx, cctx, tctx) name = (sctx, kctx, cctx, Name2str name :: tctx)
    fun visit_cvar this (sctx, kctx, cctx, tctx) x =
      str_var #3 gctx cctx x
    fun visit_var this (sctx, kctx, cctx, tctx) x =
      str_var #4 gctx tctx x
    fun visit_mod_id this (sctx, kctx, cctx, tctx) (m, r) =
      fst $ lookup_module gctx m
    fun for_idx f this (sctx, kctx, cctx, tctx) data = f gctx sctx data
    fun for_type f this (sctx, kctx, cctx, tctx) data = f gctx (sctx, kctx) data
  in
    EV.default_expr_visitor_vtable
      cast
      extend_i
      extend_t
      extend_c
      extend_e
      visit_var
      visit_cvar
      visit_mod_id
      (for_idx export_i)
      (for_idx export_s)
      (for_type export_mt)
      visit_noop
  end

fun new_export_expr_visitor a = EV.new_expr_visitor export_expr_visitor_vtable a
    
fun export_e gctx ctx b =
  let
    val visitor as (EV.ExprVisitor vtable) = new_export_expr_visitor gctx
  in
    #visit_expr vtable visitor ctx b
  end

fun export_decl gctx env b =
  let
    val visitor as (EV.ExprVisitor vtable) = new_export_expr_visitor gctx
    val ctx = env2ctx env
    val b = #visit_decl vtable visitor ctx b
    val env = !(#current ctx)
  in
    (b, env)
  end

fun export_decls gctx env b =
  let
    val visitor = new_export_expr_visitor gctx
    val ctx = env2ctx env
    val b = EV.visit_decls visitor ctx b
    val env = !(#current ctx)
  in
    (b, env)
  end

fun strn_pn pn =
  let
  in
    case pn of
        ConstrP (Outer ((x, _), eia), inames, pn, _) => sprintf "$$$" [decorate_var eia x, join_prefix " " $ map (surround "{" "}" o binder2str) inames, " " ^ strn_pn pn]
      | VarP name => binder2str name
      | PairP (pn1, pn2) => sprintf "($, $)" [strn_pn pn1, strn_pn pn2]
      | TTP _ => "()"
      | AliasP (name, pn, _) => sprintf "$ as $" [binder2str name, strn_pn pn]
      | AnnoP (pn, Outer t) => sprintf "($ : $)" [strn_pn pn, strn_mt t]
  end

fun strn_return return =
  case return of
      (NONE, NONE) => ""
    | (SOME t, NONE) => sprintf "return $ " [strn_mt t]
    | (NONE, SOME d) => sprintf "return using $ " [strn_i d]
    | (SOME t, SOME d) => sprintf "return $ using $ " [strn_mt t, strn_i d]

fun strn_sortings binds =
  let
    val binds = strn_tbinds (map SortingT binds)
    fun f bind = case bind of SortingT p => p | _ => raise Impossible "strn_tbinds shouldn't return Kinding"
    val binds = map f binds
  in
    binds
  end

fun strn_e e =
  let
    open NamefulExpr
    open NamefulExprUtil
  in
    case e of
	EVar (x, b) => decorate_var b x
      | EConst (c, _) => str_expr_const c
      | EUnOp (opr, e, _) => sprintf "($ $)" [str_expr_un_op opr, strn_e e]
      | EBinOp (opr, e1, e2) =>
        (case opr of
             EBApp => sprintf "($ $)" [strn_e e1, strn_e e2]
           | EBPair =>
             let
               val es = collect_Pair e
             in
               sprintf "($)" [join ", " $ map strn_e es]
             end
           | EBNew => sprintf "(new $ $)" [strn_e e1, strn_e e2]
           | EBRead => sprintf "(read $ $)" [strn_e e1, strn_e e2]
           | EBAdd => sprintf "($ $ $)" [strn_e e1, str_bin_op opr, strn_e e2]
        )
      | ETriOp (Write, e1, e2, e3) => sprintf "(write $ $ $)" [strn_e e1, strn_e e2, strn_e e3]
      | EEI (opr, e, i) =>
        (case opr of
             EEIAppI => sprintf "($ {$})" [strn_e e, strn_i i]
           | EEIAscTime => sprintf "($ |> $)" [strn_e e, strn_i i]
        )
      | EET (opr, e, t) =>
        (case opr of
             EETAppT => sprintf "($ {$})" [strn_e e, strn_mt t]
           | EETAsc => sprintf "($ : $)" [strn_e e, strn_mt t]
        )
      | ET (opr, t, _) =>
        (case opr of
             ETNever => sprintf "(never [$])" [strn_mt t]
           | ETBuiltin => sprintf "(builtin [$])" [strn_mt t]
        )
      | EAbs bind => 
        let
          val (pn, e) = Unbound.unBind bind
          val pn = strn_pn pn
	  val e = strn_e e
        in
          sprintf "(fn $ => $)" [pn, e]
        end
      | EAbsI (bind, _) =>
        let
          val ((name, s), e) = unBindAnno bind
          val name = Name2str name
        in
          sprintf "(fn {$ : $} => $)" [name, strn_s s, strn_e e]
        end
      | ELet (return, bind, _) => 
        let
          val (decls, e) = Unbound.unBind bind
          val decls = unTeles decls
          val return = strn_return return
          val decls = map strn_decl decls
        in
          sprintf "let $$ in $ end" [return, join_prefix " " decls, strn_e e]
        end
      | EAppConstr ((x, b), ts, is, e, _) =>
        sprintf "([$]$$ $)" [
          decorate_var b x,
          (join "" o map (prefix " ") o map (fn t => sprintf "{$}" [strn_mt t])) ts,
          (join "" o map (prefix " ") o map (fn i => sprintf "{$}" [strn_i i])) is,
          strn_e e]
      | ECase (e, return, rules, _) => sprintf "(case $ $of $)" [strn_e e, strn_return return, join " | " (map strn_rule rules)]
  end

and strn_decl decl =
    let
      open NamefulType
      open NamefulExpr
    in
      case decl of
          DVal (name, Outer bind, _) =>
          let
            val pn = VarP name
            val (tnames, e) = Unbound.unBind bind
            val tnames = map binder2str tnames
            val tnames = (join "" o map (fn nm => sprintf " [$]" [nm])) tnames
            val pn = strn_pn pn
            val e = strn_e e
          in
            sprintf "val$ $ = $" [tnames, pn, e]
          end
        | DValPtrn (pn, Outer e, _) =>
          let
            val e = strn_e e
            val pn = strn_pn pn
          in
            sprintf "val $ = $" [pn, e]
          end
        | DRec (name, bind, _) =>
          let
            val name = binder2str name
            val ((tnames, Rebind binds), ((t, d), e)) = Unbound.unBind $ unInner bind
            val binds = unTeles binds
            val tnames = map binder2str tnames
            val tnames = (join "" o map (fn nm => sprintf " [$]" [nm])) tnames
            fun f bind =
              case bind of
                  SortingST (name, Outer s) =>
                  let
                    val name = binder2str name
                  in
                    sprintf "{$ : $}" [name, strn_s s]
                  end
                | TypingST pn =>
                  strn_pn pn
            val binds = map f binds
            val binds = (join "" o map (prefix " ")) binds
            val t = strn_mt t
            val d = strn_i d
            val e = strn_e e
          in
            sprintf "rec$ $$ : $ |> $ = $" [tnames, name, binds, t, d, e]
          end
        | DIdxDef (name, Outer s, Outer i) =>
          let
            val name = binder2str name
          in
            sprintf "idx $ : $ = $" [name, strn_s s, strn_i i]
          end
        | DAbsIdx2 (name, Outer s, Outer i) =>
          let
            val name = binder2str name
          in
            sprintf "absidx $ : $ = $" [name, strn_s s, strn_i i]
          end
        | DAbsIdx ((name, Outer s, Outer i), Rebind decls, _) =>
          let
            val name = binder2str name
            val decls = unTeles decls
            val decls = map strn_decl decls
          in
            sprintf "absidx $ : $ = $ with$ end" [name, strn_s s, strn_i i, join_prefix " " decls]
          end
        | DTypeDef (name, Outer t) =>
          (case t of
               TDatatype (Bind (name, tbinds), _) =>
               let
                 val name = fst name
                 val (tname_kinds, (sorts, constrs)) = unfold_binds tbinds
                 val tnames = map fst $ map fst tname_kinds
                 val strn_tnames = (join_prefix " " o rev) tnames
                 fun strn_constr_decl ((cname, _), ibinds, _) =
                   let 
                     val (name_sorts, (t, idxs)) = unfold_binds ibinds
                     val name_sorts = map (mapFst fst) name_sorts
                     val name_sorts = strn_sortings name_sorts
                     val name_sorts = map (fn (nm, s) => sprintf "$ : $" [nm, s]) name_sorts
                   in
                     sprintf "$ of$ $ ->$$ $" [cname, (join_prefix " " o map (surround "{" "}")) name_sorts, strn_mt t, (join_prefix " " o map (surround "{" "}" o strn_i) o rev) idxs, strn_tnames, name]
                   end
                 val s = sprintf "datatype$$ $ = $" [(join_prefix " " o map (surround "{" "}" o strn_bs) o rev) sorts, strn_tnames, name, join " | " (map strn_constr_decl constrs)]
               in
                 s
               end
             | _ =>
               let
                 val name = binder2str name
               in
                 sprintf "type $ = $" [name, strn_mt t]
               end
          )
        | DOpen (Outer m, _) =>
          sprintf "open $" [m]
    end
      
and strn_rule bind =
    let
      val (pn, e) = Unbound.unBind bind
    in
      sprintf "$ => $" [strn_pn pn, strn_e e]
    end

fun str_e gctx ctx b =
  let
    val b = export_e gctx ctx b
  in
    strn_e b
  end

fun str_decl gctx ctx b =
  let
    val (b, ctx) = export_decl gctx ctx b
  in
    (strn_decl b, ctx)
  end

fun str_decls gctx ctx b =
  let
    val (b, ctx) = export_decls gctx ctx b
  in
    (map strn_decl b, ctx)
  end

(* fun str_tbinds gctx ctx binds = *)
(*   let *)
(*     fun f (bind, (acc, (sctx, kctx))) = *)
(*       case bind of *)
(*           KindingT name => (KindingT name :: acc, (sctx, name :: kctx)) *)
(*         | SortingT (name, s) => (SortingT (name, str_s gctx sctx s) :: acc, (name :: sctx, kctx)) *)
(*     val (binds, ctx) = foldl f ([], ctx) binds *)
(*     val binds = rev binds *)
(*   in *)
(*     (binds, ctx) *)
(*   end *)
    
(* fun str_sortings gctx ctx binds = *)
(*   let val (binds, ctx) = str_tbinds gctx (ctx, []) (map SortingT binds) *)
(*       fun f bind = case bind of SortingT p => p | _ => raise Impossible "str_tbinds shouldn't return Kinding" *)
(*       val binds = map f binds *)
(*   in *)
(*     (binds, fst ctx) *)
(*   end *)

(* fun str_pn gctx (ctx as (sctx, kctx, cctx)) pn = *)
(*   let *)
(*     val str_pn = str_pn gctx *)
(*   in *)
(*     case pn of *)
(*         ConstrP (Outer ((x, _), eia), inames, pn, _) => sprintf "$$$" [decorate_var eia $ str_var #3 gctx cctx x, join_prefix " " $ map (surround "{" "}" o binder2str) inames, " " ^ str_pn ctx pn] *)
(*       | VarP name => binder2str name *)
(*       | PairP (pn1, pn2) => sprintf "($, $)" [str_pn ctx pn1, str_pn ctx pn2] *)
(*       | TTP _ => "()" *)
(*       | AliasP (name, pn, _) => sprintf "$ as $" [binder2str name, str_pn ctx pn] *)
(*       | AnnoP (pn, Outer t) => sprintf "($ : $)" [str_pn ctx pn, str_mt gctx (sctx, kctx) t] *)
(*   end *)

(* fun str_return gctx (skctx as (sctx, _)) return = *)
(*   case return of *)
(*       (NONE, NONE) => "" *)
(*     | (SOME t, NONE) => sprintf "return $ " [str_mt gctx skctx t] *)
(*     | (NONE, SOME d) => sprintf "return using $ " [str_i gctx sctx d] *)
(*     | (SOME t, SOME d) => sprintf "return $ using $ " [str_mt gctx skctx t, str_i gctx sctx d] *)

(* fun add_sorting name (sctx, kctx, cctx, tctx) = (name :: sctx, kctx, cctx, tctx) *)
(* fun add_kinding name (sctx, kctx, cctx, tctx) = (sctx, name :: kctx, cctx, tctx) *)
(* fun add_typing name (sctx, kctx, cctx, tctx) = (sctx, kctx, cctx, name :: tctx) *)
(* fun add_ctx (sctxd, kctxd, cctxd, tctxd) (sctx, kctx, cctx, tctx) = *)
(*   (sctxd @ sctx, kctxd @ kctx, cctxd @ cctx, tctxd @ tctx) *)

(* fun str_e gctx (ctx as (sctx, kctx, cctx, tctx)) (e : expr) : string = *)
(*   let *)
(*     val str_e = str_e gctx *)
(*     fun add_t name (sctx, kctx, cctx, tctx) = (sctx, kctx, cctx, name :: tctx)  *)
(*     val skctx = (sctx, kctx)  *)
(*   in *)
(*     case e of *)
(* 	EVar (x, b) => decorate_var b $ str_var #4 gctx tctx x *)
(*       | EConst (c, _) => str_expr_const c *)
(*       | EUnOp (opr, e, _) => sprintf "($ $)" [str_expr_un_op opr, str_e ctx e] *)
(*       | EBinOp (opr, e1, e2) => *)
(*         (case opr of *)
(*              EBApp => sprintf "($ $)" [str_e ctx e1, str_e ctx e2] *)
(*            | EBPair => *)
(*              let *)
(*                val es = collect_Pair e *)
(*              in *)
(*                sprintf "($)" [join ", " $ map (str_e ctx) es] *)
(*              end *)
(*            | EBNew => sprintf "(new $ $)" [str_e ctx e1, str_e ctx e2] *)
(*            | EBRead => sprintf "(read $ $)" [str_e ctx e1, str_e ctx e2] *)
(*            | EBAdd => sprintf "($ $ $)" [str_e ctx e1, str_bin_op opr, str_e ctx e2] *)
(*         ) *)
(*       | ETriOp (Write, e1, e2, e3) => sprintf "(write $ $ $)" [str_e ctx e1, str_e ctx e2, str_e ctx e3] *)
(*       | EEI (opr, e, i) => *)
(*         (case opr of *)
(*            EEIAppI => sprintf "($ {$})" [str_e ctx e, str_i gctx sctx i] *)
(*           | EEIAscTime => sprintf "($ |> $)" [str_e ctx e, str_i gctx sctx i] *)
(*         ) *)
(*       | EET (opr, e, t) => *)
(*         (case opr of *)
(*              EETAppT => sprintf "($ {$})" [str_e ctx e, str_mt gctx skctx t] *)
(*            | EETAsc => sprintf "($ : $)" [str_e ctx e, str_mt gctx skctx t] *)
(*         ) *)
(*       | ET (opr, t, _) => *)
(*         (case opr of *)
(*              ETNever => sprintf "(never [$])" [str_mt gctx skctx t] *)
(*            | ETBuiltin => sprintf "(builtin [$])" [str_mt gctx skctx t] *)
(*         ) *)
(*       | EAbs bind =>  *)
(*         let *)
(*           val (pn, e) = Unbound.unBind bind *)
(*           val (inames, enames) = ptrn_names pn *)
(*           val pn = str_pn gctx (sctx, kctx, cctx) pn *)
(*           val ctx = (inames @ sctx, kctx, cctx, enames @ tctx) *)
(* 	  val e = str_e ctx e *)
(*         in *)
(*           sprintf "(fn $ => $)" [pn, e] *)
(*         end *)
(*       | EAbsI (bind, _) => *)
(*         let *)
(*           val ((name, s), e) = unBindAnno bind *)
(*           val name = Name2str name *)
(*         in *)
(*           sprintf "(fn {$ : $} => $)" [name, str_s gctx sctx s, str_e (name :: sctx, kctx, cctx, tctx) e] *)
(*         end *)
(*       | ELet (return, bind, _) =>  *)
(*         let *)
(*           val (decls, e) = Unbound.unBind bind *)
(*           val decls = unTeles decls *)
(*           val return = str_return gctx (sctx, kctx) return *)
(*           val (decls, ctx) = str_decls gctx ctx decls *)
(*         in *)
(*           sprintf "let $$ in $ end" [return, join_prefix " " decls, str_e ctx e] *)
(*         end *)
(*       | EAppConstr ((x, b), ts, is, e, _) => *)
(*         sprintf "([$]$$ $)" [ *)
(*           decorate_var b $ str_var #3 gctx cctx x, *)
(*           (join "" o map (prefix " ") o map (fn t => sprintf "{$}" [str_mt gctx skctx t])) ts, *)
(*           (join "" o map (prefix " ") o map (fn i => sprintf "{$}" [str_i gctx sctx i])) is, *)
(*           str_e ctx e] *)
(*       | ECase (e, return, rules, _) => sprintf "(case $ $of $)" [str_e ctx e, str_return gctx skctx return, join " | " (map (str_rule gctx ctx) rules)] *)
(*   end *)

(* and str_decls gctx (ctx as (sctx, kctx, cctx, tctx)) decls = *)
(*     let *)
(*       fun f (decl, (acc, ctx)) = *)
(*         let val (s, ctx) = str_decl gctx ctx decl *)
(*         in *)
(*           (s :: acc, ctx) *)
(*         end *)
(*       val (decls, ctx) = foldl f ([], ctx) decls *)
(*       val decls = rev decls *)
(*     in *)
(*       (decls, ctx) *)
(*     end *)
      
(* and str_decl gctx (ctx as (sctx, kctx, cctx, tctx)) decl = *)
(*     let *)
(*       val str_decl = str_decl gctx *)
(*     in *)
(*       case decl of *)
(*           DVal (name, Outer bind, _) => *)
(*           let *)
(*             val pn = VarP name *)
(*             val (tnames, e) = Unbound.unBind bind *)
(*             val tnames = map binder2str tnames *)
(*             val ctx' as (sctx', kctx', cctx', _) = (sctx, rev tnames @ kctx, cctx, tctx) *)
(*             val tnames = (join "" o map (fn nm => sprintf " [$]" [nm])) tnames *)
(*             val (inames, enames) = ptrn_names pn *)
(*             val pn = str_pn gctx (sctx', kctx', cctx') pn *)
(*             val e = str_e gctx ctx' e *)
(* 	    val ctx = (inames @ sctx, kctx, cctx, enames @ tctx) *)
(*           in *)
(*             (sprintf "val$ $ = $" [tnames, pn, e], ctx) *)
(*           end *)
(*         | DValPtrn (pn, Outer e, _) => *)
(*           let *)
(*             val (inames, enames) = ptrn_names pn *)
(*             val e = str_e gctx ctx e *)
(*             val pn = str_pn gctx (sctx, kctx, cctx) pn *)
(* 	    val ctx = (inames @ sctx, kctx, cctx, enames @ tctx) *)
(*           in *)
(*             (sprintf "val $ = $" [pn, e], ctx) *)
(*           end *)
(*         | DRec (name, bind, _) => *)
(*           let *)
(*             val name = binder2str name *)
(*             val ((tnames, Rebind binds), ((t, d), e)) = Unbound.unBind $ unInner bind *)
(*             val binds = unTeles binds *)
(*             val tnames = map binder2str tnames *)
(* 	    val ctx as (sctx, kctx, cctx, tctx) = (sctx, kctx, cctx, name :: tctx) *)
(*             val ctx_ret = ctx *)
(*             val ctx as (sctx, kctx, cctx, tctx) = (sctx, rev tnames @ kctx, cctx, tctx) *)
(*             val tnames = (join "" o map (fn nm => sprintf " [$]" [nm])) tnames *)
(*             fun f (bind, (binds, ctx as (sctx, kctx, cctx, tctx))) = *)
(*               case bind of *)
(*                   SortingST (name, Outer s) => *)
(*                   let *)
(*                     val name = binder2str name *)
(*                   in *)
(*                     (sprintf "{$ : $}" [name, str_s gctx sctx s] :: binds, (name :: sctx, kctx, cctx, tctx)) *)
(*                   end *)
(*                 | TypingST pn => *)
(*                   let *)
(*                     val (inames, enames) = ptrn_names pn *)
(*                   in *)
(*                     (str_pn gctx (sctx, kctx, cctx) pn :: binds, (inames @ sctx, kctx, cctx, enames @ tctx)) *)
(*                   end *)
(*             val (binds, ctx as (sctx, kctx, cctx, tctx)) = foldl f ([], ctx) binds *)
(*             val binds = rev binds *)
(*             val binds = (join "" o map (prefix " ")) binds *)
(*             val t = str_mt gctx (sctx, kctx) t *)
(*             val d = str_i gctx sctx d *)
(*             val e = str_e gctx ctx e *)
(*           in *)
(*             (sprintf "rec$ $$ : $ |> $ = $" [tnames, name, binds, t, d, e], ctx_ret) *)
(*           end *)
(*         | DIdxDef (name, Outer s, Outer i) => *)
(*           let *)
(*             val name = binder2str name *)
(*           in *)
(*             (sprintf "idx $ : $ = $" [name, str_s gctx sctx s, str_i gctx sctx i], (name :: sctx, kctx, cctx, tctx)) *)
(*           end *)
(*         | DAbsIdx2 (name, Outer s, Outer i) => *)
(*           let *)
(*             val name = binder2str name *)
(*           in *)
(*             (sprintf "absidx $ : $ = $" [name, str_s gctx sctx s, str_i gctx sctx i], (name :: sctx, kctx, cctx, tctx)) *)
(*           end *)
(*         | DAbsIdx ((name, Outer s, Outer i), Rebind decls, _) => *)
(*           let *)
(*             val name = binder2str name *)
(*             val decls = unTeles decls *)
(*             val ctx' = (name :: sctx, kctx, cctx, tctx) *)
(*             val (decls, ctx') = str_decls gctx ctx' decls *)
(*           in *)
(*             (sprintf "absidx $ : $ = $ with$ end" [name, str_s gctx sctx s, str_i gctx sctx i, join_prefix " " decls], ctx') *)
(*           end *)
(*         | DTypeDef (name, Outer t) => *)
(*           (case t of *)
(*                TDatatype (Bind (name, tbinds), _) => *)
(*                let *)
(*                  val name = fst name *)
(*                  val (tname_kinds, (sorts, constrs)) = unfold_binds tbinds *)
(*                  val tnames = map fst $ map fst tname_kinds *)
(*                  val str_tnames = (join_prefix " " o rev) tnames *)
(*                  fun str_constr_decl ((cname, _), ibinds, _) = *)
(*                    let  *)
(*                      val (name_sorts, (t, idxs)) = unfold_binds ibinds *)
(*                      val name_sorts = map (mapFst fst) name_sorts *)
(*                      val (name_sorts, sctx') = str_sortings gctx sctx name_sorts *)
(*                      val name_sorts = map (fn (nm, s) => sprintf "$ : $" [nm, s]) name_sorts *)
(*                    in *)
(*                      sprintf "$ of$ $ ->$$ $" [cname, (join_prefix " " o map (surround "{" "}")) name_sorts, str_mt gctx (sctx', rev tnames @ name :: kctx) t, (join_prefix " " o map (surround "{" "}" o str_i gctx sctx') o rev) idxs, str_tnames, name] *)
(*                    end *)
(*                  val s = sprintf "datatype$$ $ = $" [(join_prefix " " o map (surround "{" "}" o str_bs) o rev) sorts, str_tnames, name, join " | " (map str_constr_decl constrs)] *)
(*                  val cnames = map fst $ map #1 constrs *)
(*                  val ctx = (sctx, name :: kctx, rev cnames @ cctx, tctx) *)
(*                in *)
(*                  (s, ctx) *)
(*                end *)
(*              | _ => *)
(*                let *)
(*                  val name = binder2str name *)
(*                in *)
(*                  (sprintf "type $ = $" [name, str_mt gctx (sctx, kctx) t], add_kinding name ctx) *)
(*                end *)
(*           ) *)
(*         | DOpen (Outer (m, r), _) => *)
(*           let *)
(*             val (m, ctxd) = lookup_module gctx m *)
(*             val ctx = add_ctx ctxd ctx *)
(*           in *)
(*             (sprintf "open $" [m], ctx) *)
(*           end *)
(*     end *)
      
(* and str_rule gctx (ctx as (sctx, kctx, cctx, tctx)) bind = *)
(*     let *)
(*       val (pn, e) = Unbound.unBind bind *)
(*       val (inames, enames) = ptrn_names pn *)
(*       val ctx' = (inames @ sctx, kctx, cctx, enames @ tctx) *)
(*     in *)
(*       sprintf "$ => $" [str_pn gctx (sctx, kctx, cctx) pn, str_e gctx ctx' e] *)
(*     end *)

end
