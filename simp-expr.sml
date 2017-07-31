structure SimpExpr = struct

open Simp
open Normalize
open PatternVisitor
open ExprVisitor

(***************** the "simp" visitor  **********************)

fun simp_expr_visitor_vtable cast (visit_idx, visit_sort, visit_mtype) : ('this, kcontext) expr_visitor_vtable =
  let
    fun extend_t this env name = (Name2str name, KeKind Type) :: env
  in
    default_expr_visitor_vtable
      cast
      extend_noop
      extend_t
      extend_noop
      extend_noop
      visit_noop
      visit_noop
      visit_noop
      (ignore_this_env visit_idx)
      (ignore_this_env visit_sort)
      (ignore_this visit_mtype)
      visit_noop
  end

fun new_simp_expr_visitor params = new_expr_visitor simp_expr_visitor_vtable params
    
fun simp_e_fn params kctx e =
  let
    val visitor as (ExprVisitor vtable) = new_simp_expr_visitor params
  in
    #visit_expr vtable visitor kctx e
  end

fun simp_e a = simp_e_fn (simp_i o normalize_i, normalize_s, normalize_mt empty) a
                         
end
                       
