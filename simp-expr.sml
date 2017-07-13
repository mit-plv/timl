structure SimpExpr = struct

open Normalize
open PatternVisitor
open ExprVisitor

(***************** the "simp" visitor  **********************)

fun visit_mtype x = ignore_this (normalize_mt empty) x
                                
fun simp_expr_visitor_vtable cast () : ('this, kcontext) expr_visitor_vtable =
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
      (ignore_this_env (simp_i o normalize_i))
      (ignore_this_env normalize_s)
      visit_mtype
      visit_noop
  end

fun new_simp_expr_visitor params = new_expr_visitor simp_expr_visitor_vtable params
    
fun simp_e kctx e =
  let
    val visitor as (ExprVisitor vtable) = new_simp_expr_visitor ()
  in
    #visit_expr vtable visitor kctx e
  end

end
                       
