functor TypeShiftVisitorFn (Type : TYPE) = struct

structure TypeVisitor = TypeVisitorFn (structure S = Type
                                       structure T = Type)
open TypeVisitor
                                         
fun on_i_type_visitor_vtable cast (visit_idx, visit_sort) : ('this, int) type_visitor_vtable =
  let
    fun extend_i this env _ = env + 1
  in
    default_type_visitor_vtable
      cast
      extend_i
      extend_noop
      visit_noop
      visit_noop
      (ignore_this visit_idx)
      (ignore_this visit_sort)
      visit_noop
      visit_noop
  end

fun new_on_i_type_visitor a = new_type_visitor on_i_type_visitor_vtable a
    
fun on_i_mt params b =
  let
    val visitor as (TypeVisitor vtable) = new_on_i_type_visitor params
  in
    #visit_mtype vtable visitor 0 b
  end
    
fun on_i_t params b =
  let
    val visitor as (TypeVisitor vtable) = new_on_i_type_visitor params
  in
    #visit_ty vtable visitor 0 b
  end
    
fun on_i_constr_core params b =
  let
    val visitor as (TypeVisitor vtable) = new_on_i_type_visitor params
  in
    #visit_constr_core vtable visitor 0 b
  end
    
fun on_i_c params b =
  let
    val visitor as (TypeVisitor vtable) = new_on_i_type_visitor params
  in
    #visit_constr_info vtable visitor 0 b
  end
    
fun on_t_type_visitor_vtable cast visit_var : ('this, int) type_visitor_vtable =
  let
    fun extend_t this env _ = env + 1
  in
    default_type_visitor_vtable
      cast
      extend_noop
      extend_t
      (ignore_this visit_var)
      visit_noop
      visit_noop
      visit_noop
      visit_noop
      visit_noop
  end

fun new_on_t_type_visitor a = new_type_visitor on_t_type_visitor_vtable a
    
fun on_t_mt params b =
  let
    val visitor as (TypeVisitor vtable) = new_on_t_type_visitor params
  in
    #visit_mtype vtable visitor 0 b
  end
    
fun on_t_t params b =
  let
    val visitor as (TypeVisitor vtable) = new_on_t_type_visitor params
  in
    #visit_ty vtable visitor 0 b
  end
    
fun on_t_constr_core params b =
  let
    val visitor as (TypeVisitor vtable) = new_on_t_type_visitor params
  in
    #visit_constr_core vtable visitor 0 b
  end
    
fun on_t_c params b =
  let
    val visitor as (TypeVisitor vtable) = new_on_t_type_visitor params
  in
    #visit_constr_info vtable visitor 0 b
  end
    
end

signature SHIFTABLE_IDX = sig

  type idx
  type sort
  val shiftx_i_i : int -> int -> idx -> idx
  val shiftx_i_s : int -> int -> sort -> sort
  val forget_i_i : int -> int -> idx -> idx
  val forget_i_s : int -> int -> sort -> sort

end
                            
functor TypeShiftFn (structure Type : TYPE
                     structure ShiftableVar : SHIFTABLE_VAR
                     sharing type Type.var = ShiftableVar.var
                     structure ShiftableIdx : SHIFTABLE_IDX
                     sharing type Type.idx = ShiftableIdx.idx 
                     sharing type Type.sort = ShiftableIdx.sort
                    ) = struct

open Type
open ShiftableVar
open ShiftableIdx
open ShiftUtil
       
infixr 0 $
         
structure TypeShiftVisitor = TypeShiftVisitorFn (Type)
open TypeShiftVisitor
                                         
fun adapt f x n env = f (x + env) n
                        
fun shift_i_params x n = (adapt shiftx_i_i x n, adapt shiftx_i_s x n)
                     
fun shiftx_i_mt x n = on_i_mt (shift_i_params x n)
fun shiftx_i_t x n = on_i_t (shift_i_params x n)
fun shiftx_i_c x n = on_i_c (shift_i_params x n)

fun shift_t_params x n env = shiftx_var (x + env) n
  
and shiftx_t_mt x n = on_t_mt (shift_t_params x n)
fun shiftx_t_t x n = on_t_t (shift_t_params x n)
fun shiftx_t_c x n = on_t_c (shift_t_params x n)
                              
fun shift_i_mt b = shiftx_i_mt 0 1 b
fun shift_i_t b = shiftx_i_t 0 1 b
fun shift_t_mt b = shiftx_t_mt 0 1 b
fun shift_t_t b = shiftx_t_t 0 1 b

fun shift_i_c b = shiftx_i_c 0 1 b
fun shift_t_c b = shiftx_t_c 0 1 b

fun forget_i_params x n = (fn env => forget_i_i (x + env) n, fn env => forget_i_s (x + env) n)
                             
fun forget_i_mt x n = on_i_mt (forget_i_params x n)
fun forget_i_t x n = on_i_t (forget_i_params x n)
                              
fun forget_t_params x n env = forget_var (x + env) n
  
fun forget_t_mt x n = on_t_mt (forget_t_params x n)
fun forget_t_t x n = on_t_t (forget_t_params x n)

end

functor TypeSubstVisitorFn (Type : TYPE) = struct

structure TypeVisitor = TypeVisitorFn (structure S = Type
                                       structure T = Type)
open TypeVisitor
                                         
fun subst_i_type_visitor_vtable cast (visit_idx, visit_sort) : ('this, int) type_visitor_vtable =
  let
    fun extend_i this env _ = env + 1
  in
    default_type_visitor_vtable
      cast
      extend_i
      extend_noop
      visit_noop
      visit_noop
      (ignore_this visit_idx)
      (ignore_this visit_sort)
      visit_noop
      visit_noop
  end

fun new_subst_i_type_visitor params = new_type_visitor subst_i_type_visitor_vtable params
    
fun subst_i_mt_fn params b =
  let
    val visitor as (TypeVisitor vtable) = new_subst_i_type_visitor params
  in
    #visit_mtype vtable visitor 0 b
  end

fun subst_i_t_fn params b =
  let
    val visitor as (TypeVisitor vtable) = new_subst_i_type_visitor params
  in
    #visit_ty vtable visitor 0 b
  end

fun subst_t_type_visitor_vtable cast visit_MtVar : ('this, idepth * tdepth) type_visitor_vtable =
  let
    fun extend_i this (di, dt) _ = (idepth_inc di, dt)
    fun extend_t this (di, dt) _ = (di, tdepth_inc dt)
    val vtable = 
        default_type_visitor_vtable
          cast
          extend_i
          extend_t
          (visit_imposs "subst_t_mt/visit_var")
          visit_noop
          visit_noop
          visit_noop
          visit_noop
          visit_noop
    val vtable = override_visit_MtVar vtable (ignore_this visit_MtVar)
  in
    vtable
  end

fun new_subst_t_type_visitor params = new_type_visitor subst_t_type_visitor_vtable params

fun subst_t_mt_fn params b =
  let
    val visitor as (TypeVisitor vtable) = new_subst_t_type_visitor params
  in
    #visit_mtype vtable visitor (IDepth 0, TDepth 0) b
  end
                               
fun subst_t_t_fn params b =
  let
    val visitor as (TypeVisitor vtable) = new_subst_t_type_visitor params
  in
    #visit_ty vtable visitor (IDepth 0, TDepth 0) b
  end

end
                                  
functor TypeSubstFn (structure Type : TYPE
                     val visit_MtVar : (Namespaces.idepth * Namespaces.tdepth) * int * Type.mtype -> Namespaces.idepth * Namespaces.tdepth -> Type.var -> Type.mtype
                     val substx_i_i : int -> int -> Type.idx -> Type.idx -> Type.idx
                     val substx_i_s : int -> int -> Type.idx -> Type.sort -> Type.sort
                    ) = struct

open Type
open Util
       
infixr 0 $
         
structure TypeSubstVisitor = TypeSubstVisitorFn (Type)
open TypeSubstVisitor
                                         
fun visit_idx (d, x, v) env b = substx_i_i (d + env) (x + env) v b
fun visit_sort (d, x, v) env b = substx_i_s (d + env) (x + env) v b
                                      
fun subst_i_params params = (visit_idx params, visit_sort params)
                       
fun substx_i_mt d x v = subst_i_mt_fn $ subst_i_params (d, x, v)
fun substx_i_t d x v = subst_i_t_fn $ subst_i_params (d, x, v)
                                    
fun subst_i_mt (v : idx) (b : mtype) : mtype = substx_i_mt 0 0 v b
fun subst_i_t (v : idx) (b : ty) : ty = substx_i_t 0 0 v b

val subst_t_params = visit_MtVar

fun substx_t_mt d x v = subst_t_mt_fn $ subst_t_params (IDepth_TDepth d, x, v)
fun substx_t_t d x v = subst_t_t_fn $ subst_t_params (IDepth_TDepth d, x, v)
fun subst_t_mt (v : mtype) (b : mtype) : mtype = substx_t_mt (0, 0) 0 v b
fun subst_t_t v b = substx_t_t (0, 0) 0 v b

fun subst_is_mt is t =
  fst (foldl (fn (i, (t, x)) => (substx_i_mt x x i t, x - 1)) (t, length is - 1) is)
fun subst_ts_mt vs b =
  fst (foldl (fn (v, (b, x)) => (substx_t_mt (0, x) x v b, x - 1)) (b, length vs - 1) vs)
      
end
