functor ExprShiftVisitorFn (Expr : EXPR) = struct

structure ExprVisitor = ExprVisitorFn (structure S = Expr
                                       structure T = Expr
                                      )
open ExprVisitor

fun on_i_expr_visitor_vtable cast (visit_idx, visit_sort, visit_mtype) : ('this, int) expr_visitor_vtable =
  let
    fun extend_one this env _ = env + 1
  in
    default_expr_visitor_vtable
      cast
      extend_one
      extend_noop
      extend_noop
      extend_noop
      visit_noop
      visit_noop
      visit_noop
      (ignore_this visit_idx)
      (ignore_this visit_sort)
      (ignore_this visit_mtype)
      visit_noop
  end

fun new_on_i_expr_visitor params = new_expr_visitor on_i_expr_visitor_vtable params
    
fun on_i_e params b =
  let
    val visitor as (ExprVisitor vtable) = new_on_i_expr_visitor params
  in
    #visit_expr vtable visitor 0 b
  end
    
fun on_t_expr_visitor_vtable cast visit_mtype : ('this, int) expr_visitor_vtable =
  let
    fun extend_one this env _ = env + 1
  in
    default_expr_visitor_vtable
      cast
      extend_noop
      extend_one
      extend_noop
      extend_noop
      visit_noop
      visit_noop
      visit_noop
      visit_noop
      visit_noop
      (ignore_this visit_mtype)
      visit_noop
  end

fun new_on_t_expr_visitor params = new_expr_visitor on_t_expr_visitor_vtable params
    
fun on_t_e params b =
  let
    val visitor as (ExprVisitor vtable) = new_on_t_expr_visitor params
  in
    #visit_expr vtable visitor 0 b
  end
    
fun on_c_expr_visitor_vtable cast visit_cvar : ('this, int) expr_visitor_vtable =
  let
    fun extend_one this env _ = env + 1
  in
    default_expr_visitor_vtable
      cast
      extend_noop
      extend_noop
      extend_one
      extend_noop
      visit_noop
      (ignore_this visit_cvar)
      visit_noop
      visit_noop
      visit_noop
      visit_noop
      visit_noop
  end

fun new_on_c_expr_visitor params = new_expr_visitor on_c_expr_visitor_vtable params
    
fun on_c_e params b =
  let
    val visitor as (ExprVisitor vtable) = new_on_c_expr_visitor params
  in
    #visit_expr vtable visitor 0 b
  end
    
fun on_e_expr_visitor_vtable cast visit_var : ('this, int) expr_visitor_vtable =
  let
    fun extend_one this env _ = env + 1
  in
    default_expr_visitor_vtable
      cast
      extend_noop
      extend_noop
      extend_noop
      extend_one
      (ignore_this visit_var)
      visit_noop
      visit_noop
      visit_noop
      visit_noop
      visit_noop
      visit_noop
  end

fun new_on_e_expr_visitor params = new_expr_visitor on_e_expr_visitor_vtable params
    
fun on_e_e params b =
  let
    val visitor as (ExprVisitor vtable) = new_on_e_expr_visitor params
  in
    #visit_expr vtable visitor 0 b
  end
    
end

functor ExprShiftFn (structure Expr : EXPR
                     structure ShiftableVar : SHIFTABLE_VAR
                     sharing type ShiftableVar.var = Expr.var
                    ) = struct

open ShiftableVar
open Util
       
infixr 0 $
         
structure ExprShiftVisitor = ExprShiftVisitorFn (Expr)
open ExprShiftVisitor
                                         
fun adapt f x n env = f (x + env) n

fun shift_e_params a = adapt shiftx_var a
  
fun shiftx_e_e x n = on_e_e $ shift_e_params x n
                            
fun shift_e_e a = shiftx_e_e 0 1 a
                              
fun forget_e_params a = adapt forget_var a
  
fun forget_e_e x n = on_e_e $ forget_e_params x n

open Bind
       
end

functor ExprSubstFn (structure S : EXPR
                   structure T : EXPR
                   sharing type S.var = T.var
                   sharing type S.cvar = T.cvar
                   sharing type S.mod_id = T.mod_id
                   sharing type S.idx = T.idx
                   sharing type S.sort = T.sort
                   sharing type S.ptrn_constr_tag = T.ptrn_constr_tag
                  ) = struct

structure ExprVisitor = ExprVisitorFn (structure S = S
                                       structure T = T)
open ExprVisitor
       
open Util
       
infixr 0 $
         
(***************** the "subst_t_e" visitor  **********************)    

(* fun visit_datatype this env data = *)
(*   let *)
(*     val vtable =  *)
(*     val (name, _) = data *)
(*     val name = visit_tbinder this env name *)
(*     val t = visit_outer (#visit_mod_id vtable this) env $ TDatatype (Abs data, dummy) *)
(*     val data = case t of *)
(*                    TDatatype (Abs dt, _) => dt *)
(*                  | _ => raise Impossible "default_expr_visitor/visit_datatype" *)
(*   in *)
(*     data *)
(*   end *)
    
fun subst_t_expr_visitor_vtable cast (subst_t_t, d, x, v) : ('this, idepth * tdepth) expr_visitor_vtable =
  let
    fun extend_i this env _ = mapFst idepth_inc env
    fun extend_t this env _ = mapSnd tdepth_inc env
    fun add_depth (di, dt) (di', dt') = (idepth_add (di, di'), tdepth_add (dt, dt'))
    fun visit_mtype this env b = subst_t_t (add_depth d env) (x + unTDepth (snd env)) v b
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
      visit_noop
      visit_mtype
      visit_noop
  end

fun new_subst_t_expr_visitor params = new_expr_visitor subst_t_expr_visitor_vtable params
    
fun subst_t_e_fn substs d x v b =
  let
    val visitor as (ExprVisitor vtable) = new_subst_t_expr_visitor (substs, d, x, v)
  in
    #visit_expr vtable visitor (IDepth 0, TDepth 0) b
  end

end

                        
