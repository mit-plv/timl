structure ExprTrans = struct

open Normalize
open PatternVisitor
open ExprVisitor

infixr 0 $
         
(***************** the "simp" visitor  **********************)

fun visit_mtype x = ignore_this (normalize_mt empty) x
                                
fun simp_ptrn_visitor_vtable cast () : ('this, kcontext, 'var, mtype, 'var, mtype) ptrn_visitor_vtable =
  let
    fun extend_t this env name = (Name2str name, KeKind Type) :: env
  in
    default_ptrn_visitor_vtable
      cast
      extend_noop
      extend_noop
      visit_noop
      visit_mtype
  end

fun new_simp_ptrn_visitor params = new_ptrn_visitor simp_ptrn_visitor_vtable params
    
fun simp_pn kctx pn =
  let
    val visitor as (PtrnVisitor vtable) = new_simp_ptrn_visitor ()
  in
    #visit_ptrn vtable visitor kctx pn
  end
                      
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
      (ignore_this_env (simp_i o normalize_i))
      (ignore_this_env normalize_s)
      visit_mtype
      (visit_imposs "visit_datatype")
      (ignore_this simp_pn)
  end

fun new_simp_expr_visitor params = new_expr_visitor simp_expr_visitor_vtable params
    
fun simp_e kctx e =
  let
    val visitor as (ExprVisitor vtable) = new_simp_expr_visitor ()
  in
    #visit_expr vtable visitor kctx e
  end
                      
(***************** the "subst_t_e" visitor  **********************)    

(* fun visit_datatype this env data = *)
(*   let *)
(*     val vtable =  *)
(*     val (name, _) = data *)
(*     val name = visit_tbinder this env name *)
(*     val t = visit_outer (#visit_mod_projectible vtable this) env $ TDatatype (Abs data, dummy) *)
(*     val data = case t of *)
(*                    TDatatype (Abs dt, _) => dt *)
(*                  | _ => raise Impossible "default_expr_visitor/visit_datatype" *)
(*   in *)
(*     data *)
(*   end *)
    
fun subst_t_expr_visitor_vtable cast ((subst_t_t, subst_t_pn), d, x, v) : ('this, idepth * tdepth) expr_visitor_vtable =
  let
    fun extend_i this env _ = mapFst idepth_inc env
    fun extend_t this env _ = mapSnd tdepth_inc env
    fun add_depth (di, dt) (di', dt') = (idepth_add (di, di'), tdepth_add (dt, dt'))
    fun visit_mtype this env b = subst_t_t (add_depth d env) (x + unTDepth (snd env)) v b
    fun visit_ptrn this env b = subst_t_pn env d x v b
  in
    default_expr_visitor_vtable
      cast
      extend_i
      extend_t
      extend_noop
      extend_noop
      visit_noop
      visit_noop
      visit_noop
      visit_noop
      visit_mtype
      (visit_imposs "visit_datatype")
      visit_ptrn
  end

fun new_subst_t_expr_visitor params = new_expr_visitor subst_t_expr_visitor_vtable params
    
fun subst_t_e_fn substs d x v b =
  let
    val visitor as (ExprVisitor vtable) = new_subst_t_expr_visitor (substs, d, x, v)
  in
    #visit_expr vtable visitor (IDepth 0, TDepth 0) b
  end

end
