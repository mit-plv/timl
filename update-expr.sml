structure UpdateExpr = struct

open Normalize
open ExprVisitor

fun update_expr_visitor_vtable cast (visit_idx, visit_sort, visit_mtype, visit_ty, visit_kind) : ('this, unit) expr_visitor_vtable =
  default_expr_visitor_vtable
    cast
    extend_noop
    extend_noop
    extend_noop
    extend_noop
    visit_noop
    visit_noop
    visit_noop
    (ignore_this_env visit_idx)
    (ignore_this_env visit_sort)
    (ignore_this_env visit_mtype)
    (ignore_this_env visit_ty)
    (ignore_this_env visit_kind)
    visit_noop

fun new_update_expr_visitor params = new_expr_visitor update_expr_visitor_vtable params
    
fun update_e_fn params e =
  let
    val visitor as (ExprVisitor vtable) = new_update_expr_visitor params
  in
    #visit_expr vtable visitor () e
  end

fun update_e a = update_e_fn (update_i, update_s, update_mt, update_t, update_k) a
                         
end
                       
