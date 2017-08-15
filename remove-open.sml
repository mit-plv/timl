structure RemoveOpen = struct

open Expr
open ExprVisitor
open Util

infixr 0 $
infixr 0 !!
         
fun remove_DOpen_expr_visitor_vtable cast () : ('this, unit) expr_visitor_vtable =
  let
    val vtable = 
        default_expr_visitor_vtable
          cast
          extend_noop
          extend_noop
          extend_noop
          extend_noop
          visit_noop
          visit_noop
          (visit_imposs "remove_DOpen/visit_mod_id")
          visit_noop
          visit_noop
          visit_noop
          visit_noop
          visit_noop
          visit_noop
    fun visit_DOpen this env (Outer m, octx) =
      let
        val (sctx, kctx, cctx, tctx) = octx !! (fn () => raise Impossible "remove_DOpen: octx must be SOME")
        val decls = []
        fun V i = QID (m, (i, dummy))
        val decls = mapi (fn (i, name) => DIdxDef (name, Outer NONE, Outer $ VarI $ V i)) sctx @ decls
        val decls = mapi (fn (i, name) => DTypeDef (name, Outer $ MtVar $ V i)) kctx @ decls
        val decls = mapi (fn (i, name) => DConstrDef (name, Outer $ V i)) cctx @ decls
        val decls = mapi (fn (i, name) => MakeDVal (unBinderName name, [], EVar (V i, true), dummy)) tctx @ decls
        val decls = rev decls
      in
        decls
      end
    val vtable = override_visit_DOpen vtable visit_DOpen
  in
    vtable
  end

fun new_remove_DOpen_expr_visitor params = new_expr_visitor remove_DOpen_expr_visitor_vtable params
    
fun remove_DOpen_e e =
  let
    val visitor as (ExprVisitor vtable) = new_remove_DOpen_expr_visitor ()
  in
    #visit_expr vtable visitor () e
  end

fun remove_DOpen_decls a = DerivedTrans.for_decls remove_DOpen_e a

fun remove_DOpen_m m =
  let
    val visitor = new_remove_DOpen_expr_visitor ()
  in
    fst $ visit_mod_acc visitor (m, ())
  end

fun remove_DOpen_top_bind b =
  case b of
      TopModBind m => TopModBind $ remove_DOpen_m m
    | _ => raise Unimpl "remove_DOpen_top_bind"
                 
fun remove_DOpen_prog p = map (mapSnd remove_DOpen_top_bind) p
  
end
