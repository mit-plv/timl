structure RemoveOpen = struct

open ExprVisitor

infixr 0 $
         
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
    fun visit_DOpen this env (m, octx) =
      let
        val (sctx, kctx, cctx, tctx) = octx !! (fn () => raise Impossible "remove_DOpen: octx must be SOME")
        val decls = []
        val decls = mapi (fn (i, name) => MakeDIdxDef (name, NONE, VarI $ QID (m, i))) sctx @ decls
        val decls = mapi (fn (i, name) => MakeDTypeDef (name, MtVar $ QID (m, i))) kctx @ decls
        val decls = mapi (fn (i, name) => MakeDConstrDef (name, QID (m, i))) cctx @ decls
        val decls = mapi (fn (i, name) => MakeDVal (name, [], EVar $ QID (m, i))) tctx @ decls
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

end
