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

(* open Bind *)
       
end

functor ExprSubstVisitorFn (Expr : EXPR) = struct

structure ExprVisitor = ExprVisitorFn (structure S = Expr
                                       structure T = Expr)
open ExprVisitor
       
fun subst_i_expr_visitor_vtable cast (visit_idx, visit_sort, visit_mtype) : ('this, int) expr_visitor_vtable =
  let
    fun extend_i this env _ = env + 1
  in
    default_expr_visitor_vtable
      cast
      extend_i
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

fun new_subst_i_expr_visitor params = new_expr_visitor subst_i_expr_visitor_vtable params
    
fun subst_i_e_fn params b =
  let
    val visitor as (ExprVisitor vtable) = new_subst_i_expr_visitor params
  in
    #visit_expr vtable visitor 0 b
  end

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
    
fun subst_t_expr_visitor_vtable cast visit_mtype : ('this, idepth * tdepth) expr_visitor_vtable =
  let
    fun extend_i this env _ = mapFst idepth_inc env
    fun extend_t this env _ = mapSnd tdepth_inc env
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
      (ignore_this visit_mtype)
      visit_noop
  end

fun new_subst_t_expr_visitor params = new_expr_visitor subst_t_expr_visitor_vtable params
    
fun subst_t_e_fn params b =
  let
    val visitor as (ExprVisitor vtable) = new_subst_t_expr_visitor params
  in
    #visit_expr vtable visitor (IDepth 0, TDepth 0) b
  end

end
                                  
functor ExprSubstFn (structure Expr : EXPR
                     val substx_i_i : int -> int -> Expr.idx -> Expr.idx -> Expr.idx
                     val substx_i_s : int -> int -> Expr.idx -> Expr.sort -> Expr.sort
                     val substx_i_mt : int -> int -> Expr.idx -> Expr.mtype -> Expr.mtype
                     val substx_t_mt : int * int -> int -> Expr.mtype -> Expr.mtype -> Expr.mtype
                  ) = struct

open Util
open Namespaces
       
infixr 0 $
         
structure ExprSubstVisitor = ExprSubstVisitorFn (Expr)
open ExprSubstVisitor

fun adapt f d x v env = f (d + env) (x + env) v

fun substx_i_e d x v = subst_i_e_fn (adapt substx_i_i d x v, adapt substx_i_s d x v, adapt substx_i_mt d x v)
                                              
fun subst_i_e a = substx_i_e 0 0 a
                             
fun visit_mtype_t_e (d, x, v) env b =
  let
    fun add_depth (di, dt) (di', dt') = (idepth_add (di, di'), tdepth_add (dt, dt'))
  in
    use_idepth_tdepth substx_t_mt (add_depth d env) (x + unTDepth (snd env)) v b
  end
    
fun substx_t_e d x v = subst_t_e_fn $ visit_mtype_t_e (IDepth_TDepth d, x, v)

fun subst_t_e a = substx_t_e (0, 0) 0 a
                                       
end

                        
