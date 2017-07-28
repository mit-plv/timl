signature CAN_TO_STRING = sig
  type var
  type idx
  include UVAR_I
  include UVAR_T
  val str_var : (ToStringUtil.context -> string list) -> ToStringUtil.global_context -> string list -> var -> string
  val lookup_module : ToStringUtil.global_context -> string -> string * ToStringUtil.context
  val map_uvar_bs : ('bsort -> 'bsort2) -> 'bsort uvar_bs -> 'bsort2 uvar_bs
  val map_uvar_i : ('bsort -> 'bsort2) * ('idx -> 'idx2) -> ('bsort, 'idx) uvar_i -> ('bsort2, 'idx2) uvar_i
  val map_uvar_s : ('bsort -> 'bsort2) * ('sort -> 'sort2) -> ('bsort, 'sort) uvar_s -> ('bsort2, 'sort2) uvar_s
  val map_uvar_mt : ('bsort -> 'bsort2) * ('kind -> 'kind2) * ('mtype -> 'mtype2) -> ('bsort, 'kind, 'mtype) uvar_mt -> ('bsort2, 'kind2, 'mtype2) uvar_mt
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
structure IdxUtil = IdxUtilFn (Idx)
open IdxUtil
structure TypeUtil = TypeUtilFn (Type)
open TypeUtil
structure ExprUtil = ExprUtilFn (Expr)
open ExprUtil
open Bind

infixr 0 $

(* structure StringUVar = struct *)
(* type 'a uvar_bs = string *)
(* type ('a, 'b) uvar_i = string *)
(* type ('a, 'b) uvar_s = string *)
(* type ('a, 'b, 'c) uvar_mt = string *)
(* end *)
                         
structure StringUVar = struct
type 'a uvar_bs = 'a uvar_bs
type ('a, 'b) uvar_i = ('a, 'b) uvar_i
type ('a, 'b) uvar_s = ('a, 'b) uvar_s
type ('a, 'b, 'c) uvar_mt = ('a, 'b, 'c) uvar_mt
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

structure NamefulType = TypeFn (structure Idx = NamefulIdx
                                structure UVarT = StringUVar
                                type base_type = base_type
                            )

structure NamefulTypeUtil = TypeUtilFn (NamefulType)
       
structure NamefulExpr = ExprFn (
  type var = string
  type cvar = string
  type mod_id = string
  type idx = NamefulIdx.idx
  type sort = NamefulIdx.sort
  type mtype = NamefulType.mtype
  val get_constr_names = NamefulTypeUtil.get_constr_names
  type ptrn_constr_tag = ptrn_constr_tag
  type ty = NamefulType.ty
  type kind = NamefulType.kind
)

structure ToStringNameful = ToStringNamefulFn (structure Expr = struct
                                               structure Idx = NamefulIdx
                                               structure Type = NamefulType
                                               open NamefulExpr
                                               end
                                               open CanToString
                                              )
structure SN = ToStringNameful
                                              
structure ExportIdx = ExportIdxFn (structure Params = struct
                                   structure S = Idx
                                   structure T = NamefulIdx
                                   end
                                   open CanToString
                                  )
open ExportIdx

fun str_bs b =
  let
    val b = export_bs b
  in
    SN.strn_bs b
  end
    
fun str_i gctx ctx b =
  let
    val b = export_i gctx ctx b
  in
    SN.strn_i b
  end
    
fun str_s gctx ctx b =
  let
    val b = export_s gctx ctx b
  in
    SN.strn_s b
  end
    
fun str_p gctx ctx b =
  let
    val b = export_p gctx ctx b
  in
    SN.strn_p b
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

structure ExportType = ExportTypeFn (structure Params = struct
                                     structure S = Type
                                     structure T = NamefulType
                                     end
                                     open CanToString
                                     open ExportIdx
                                  )
open ExportType

fun str_k a = (SN.strn_k o export_k) a
    
fun str_mt gctx ctx b =
  let
    val b = export_mt gctx ctx b
  in
    SN.strn_mt b
  end
    
and str_t gctx ctx b =
  let
    val b = export_t gctx ctx b
  in
    SN.strn_t b
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

(* open LongId *)
       
structure ExportExpr = ExportExprFn (structure Params = struct
                                     structure S = Expr
                                     structure T = NamefulExpr
                                     end
                                     open CanToString
                                     open ExportIdx
                                     open ExportType
                                  )
open ExportExpr

fun str_e gctx ctx b =
  let
    val b = export_e gctx ctx b
  in
    SN.strn_e b
  end

fun str_decl gctx ctx b =
  let
    val (b, ctx) = export_decl gctx ctx b
  in
    (SN.strn_decl b, ctx)
  end

fun str_decls gctx ctx b =
  let
    val (b, ctx) = export_decls gctx ctx b
  in
    (map SN.strn_decl b, ctx)
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
