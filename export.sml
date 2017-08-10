functor ExportIdxFn (
  structure Params : IDX_VISITOR_PARAMS where type S.name = string * Region.region
                                          and type T.var = string
                                          and type 'a T.exists_anno = unit
  val str_var : (ToStringUtil.context -> string list) -> ToStringUtil.global_context -> string list -> Params.S.var -> string
  val map_uvar_bs : ('bsort -> 'bsort2) -> 'bsort Params.S.uvar_bs -> 'bsort2 Params.T.uvar_bs
  val map_uvar_i : ('bsort -> 'bsort2) * ('idx -> 'idx2) -> ('bsort, 'idx) Params.S.uvar_i -> ('bsort2, 'idx2) Params.T.uvar_i
  val map_uvar_s : ('bsort -> 'bsort2) * ('sort -> 'sort2) -> ('bsort, 'sort) Params.S.uvar_s -> ('bsort2, 'sort2) Params.T.uvar_s
) = struct

open Params
open Gctx
open List
open Util
open VisitorUtil
open Operators
       
structure IdxVisitor = IdxVisitorFn (Params)
(* open IdxVisitor *)
structure IV = IdxVisitor
                           
(******** the "export" visitor: convertnig de Bruijn indices to nameful terms **************)
    
fun export_idx_visitor_vtable cast gctx (* : ((* 'this *)string list IV.idx_visitor, ToStringUtil.scontext) IV.idx_visitor_vtable *) =
  let
    fun extend this env name = fst name :: env
    fun visit_var this ctx x =
      str_var #1 gctx ctx x
    fun visit_uvar_bs this ctx u =
      let
        val vtable = cast this
      in
        map_uvar_bs (#visit_bsort vtable this []) u
      end
    fun visit_uvar_i this ctx (u, r) =
      let
        val vtable = cast this
        val u = map_uvar_i (#visit_bsort vtable this [], #visit_idx vtable this []) u
      in
        (u, r)
      end
    fun visit_uvar_s this ctx (u, r) =
      let
        val vtable = cast this
        val u = map_uvar_s (#visit_bsort vtable this [], #visit_sort vtable this []) u
      in
        (u, r)       
      end
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

fun new_export_idx_visitor a = IV.new_idx_visitor export_idx_visitor_vtable a
    
fun export_bs b =
  let
    val visitor as (IV.IdxVisitor vtable) = new_export_idx_visitor empty
  in
    #visit_bsort vtable visitor [] b
  end

fun export_i gctx ctx b =
  let
    val visitor as (IV.IdxVisitor vtable) = new_export_idx_visitor gctx
  in
    #visit_idx vtable visitor ctx b
  end

fun export_p gctx ctx b =
  let
    val visitor as (IV.IdxVisitor vtable) = new_export_idx_visitor gctx
  in
    #visit_prop vtable visitor ctx b
  end

fun export_s gctx ctx b =
  let
    val visitor as (IV.IdxVisitor vtable) = new_export_idx_visitor gctx
  in
    #visit_sort vtable visitor ctx b
  end

end

functor ExportTypeFn (
  structure Params : TYPE_VISITOR_PARAMS where type S.name = string * Region.region
                                           and type T.var = string
  val str_var : (ToStringUtil.context -> string list) -> ToStringUtil.global_context -> string list -> Params.S.var -> string
  val export_bs : Params.S.bsort -> Params.T.bsort
  val export_i : ToStringUtil.global_context -> string list -> Params.S.idx -> Params.T.idx
  val export_s : ToStringUtil.global_context -> string list -> Params.S.sort -> Params.T.sort
  val map_uvar_mt : ('bsort -> 'bsort2) * ('kind -> 'kind2) * ('mtype -> 'mtype2) -> ('bsort, 'kind, 'mtype) Params.S.uvar_mt -> ('bsort2, 'kind2, 'mtype2) Params.T.uvar_mt
) = struct

open Params
open Util
open VisitorUtil
       
structure TypeVisitor = TypeVisitorFn (Params)
structure TV = TypeVisitor
                           
fun export_k (n, sorts) = (n, map export_bs sorts)
  
fun export_type_visitor_vtable cast gctx (* : ((string list * string list) TV.type_visitor, string list * string list) TV.type_visitor_vtable *) =
  let
    fun extend_i this (sctx, kctx) name = (fst name :: sctx, kctx)
    fun extend_t this (sctx, kctx) name = (sctx, fst name :: kctx)
    fun visit_var this (sctx, kctx) x =
      str_var #2 gctx kctx x
    fun for_idx f this (sctx, kctx) data = f gctx sctx data
    fun visit_uvar_mt this ctx (u, r) =
      let
        val vtable = cast this
        val empty_ctx = ([], [])
        val u = 
            map_uvar_mt (#visit_bsort vtable this empty_ctx, #visit_kind vtable this empty_ctx, #visit_mtype vtable this empty_ctx) u
      in
        (u, r)
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

fun new_export_type_visitor a = TV.new_type_visitor export_type_visitor_vtable a
    
fun export_mt gctx ctx b =
  let
    val visitor as (TV.TypeVisitor vtable) = new_export_type_visitor gctx
  in
    #visit_mtype vtable visitor ctx b
  end

fun export_t gctx ctx b =
  let
    val visitor as (TV.TypeVisitor vtable) = new_export_type_visitor gctx
  in
    #visit_ty vtable visitor ctx b
  end

end                           

functor ExportExprFn (
  structure Params : EXPR_VISITOR_PARAMS where type T.var = string
                                           and type T.cvar = string
                                           and type S.mod_id = string * Region.region
                                           and type T.mod_id = string
  sharing type Params.S.cvar = Params.S.var
  sharing type Params.T.ptrn_constr_tag = Params.S.ptrn_constr_tag
  val str_var : (ToStringUtil.context -> string list) -> ToStringUtil.global_context -> string list -> Params.S.var -> string
  val lookup_module : ToStringUtil.global_context -> string -> string * ToStringUtil.context
  val export_i : ToStringUtil.global_context -> string list -> Params.S.idx -> Params.T.idx
  val export_s : ToStringUtil.global_context -> string list -> Params.S.sort -> Params.T.sort
  val export_mt : ToStringUtil.global_context -> string list * string list -> Params.S.mtype -> Params.T.mtype
) = struct

open Binders
open Util
       
infixr 0 $
         
structure ToStringExprVisitor = ExprVisitorFn (Params)
structure EV = ToStringExprVisitor

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
    val visitor = new_export_expr_visitor gctx
  in
    EV.visit_decl_acc visitor (b, env)
  end

fun export_decls gctx env b =
  let
    val visitor = new_export_expr_visitor gctx
  in
    EV.visit_decls_acc visitor (b, env)
  end

end

                            
