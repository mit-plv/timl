structure MicroTiMLExPostProcess = struct

open MicroTiMLEx

fun post_process_expr_visitor_vtable cast () : ('this, unit, 'var, 'idx, 'sort, 'kind, 'ty, 'var, 'idx, 'sort, 'kind, 'ty) expr_visitor_vtable =
  let
    val vtable = 
        default_expr_visitor_vtable
          cast
          extend_noop
          extend_noop
          extend_noop
          visit_noop
          visit_noop
          visit_noop
          visit_noop
    fun visit_EMatchUnfold this env (e, bind) =
      ELet (EUnfold e, bind)
    val vtable = override_visit_EMatchUnfold vtable visit_EMatchUnfold
  in
    vtable
  end

fun new_post_process_expr_visitor params = new_expr_visitor post_process_expr_visitor_vtable params
    
fun post_process_e b =
  let
    val visitor as (ExprVisitor vtable) = new_post_process_expr_visitor ()
  in
    #visit_expr vtable visitor () b
  end
    
fun post_process_e b =
  let
    val visitor as (ExprVisitor vtable) = new_post_process_expr_visitor ()
  in
    #visit_expr vtable visitor () b
  end
    
end
