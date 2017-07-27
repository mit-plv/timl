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
         
(* fun on_i_mt on_i on_s x n b = *)
(*   let *)
(*     fun f x n b = *)
(*       case b of *)
(* 	  Arrow (t1, d, t2) => Arrow (f x n t1, on_i x n d, f x n t2) *)
(*         | TyNat (i, r) => TyNat (on_i x n i, r) *)
(*         | TyArray (t, i) => TyArray (f x n t, on_i x n i) *)
(*         | Unit r => Unit r *)
(* 	| Prod (t1, t2) => Prod (f x n t1, f x n t2) *)
(* 	| UniI (s, bind, r) => UniI (on_s x n s, on_i_ibind f x n bind, r) *)
(*         | MtVar y => MtVar y *)
(*         | MtApp (t1, t2) => MtApp (f x n t1, f x n t2) *)
(*         | MtAbs (k, bind, r) => MtAbs (k, on_i_tbind f x n bind, r) *)
(*         | MtAppI (t, i) => MtAppI (f x n t, on_i x n i) *)
(*         | MtAbsI (b, bind, r) => MtAbsI (b, on_i_ibind f x n bind, r) *)
(* 	| BaseType a => BaseType a *)
(*         | UVar a => b *)
(*         | TDatatype (Unbound.Abs dt, r) => *)
(*           let *)
(*             fun on_constr_decl x n (name, c, r) = (name, on_i_constr_core on_i on_s f x n c, r) *)
(*             val dt = Bind $ from_Unbound dt *)
(*             val Bind dt = on_i_tbind (on_i_tbinds return3 (on_pair (return3, on_list on_constr_decl))) x n dt *)
(*             val dt = to_Unbound dt *)
(*           in *)
(*             TDatatype (Unbound.Abs dt, r) *)
(*           end *)
(*   in *)
(*     f x n b *)
(*   end *)

(* and on_i_constr_core on_i on_s on_i_mt x n b = on_i_ibinds on_s (on_pair (on_i_mt, on_list on_i)) x n b *)
                                    
structure TypeVisitor = TypeVisitorFn (structure S = Type
                                       structure T = Type)
open TypeVisitor
                                         
fun on_i_type_visitor_vtable cast ((on_i, on_s), n) : ('this, int) type_visitor_vtable =
  let
    fun extend_i this env _ = env + 1
    fun use f this env b = f env n b
  in
    default_type_visitor_vtable
      cast
      extend_i
      extend_noop
      visit_noop
      visit_noop
      (use on_i)
      (use on_s)
      visit_noop
      visit_noop
  end

fun new_on_i_type_visitor a = new_type_visitor on_i_type_visitor_vtable a
    
fun on_i_mt params x n b =
  let
    val visitor as (TypeVisitor vtable) = new_on_i_type_visitor (params, n)
  in
    #visit_mtype vtable visitor x b
  end
    
fun on_i_t params x n b =
  let
    val visitor as (TypeVisitor vtable) = new_on_i_type_visitor (params, n)
  in
    #visit_ty vtable visitor x b
  end
    
fun on_i_constr_core params x n b =
  let
    val visitor as (TypeVisitor vtable) = new_on_i_type_visitor (params, n)
  in
    #visit_constr_core vtable visitor x b
  end
    
fun on_i_c params x n b =
  let
    val visitor as (TypeVisitor vtable) = new_on_i_type_visitor (params, n)
  in
    #visit_constr_info vtable visitor x b
  end
    
(* fun on_i_t on_i_mt x n b = *)
(*   let *)
(*     fun f x n b = *)
(*       case b of *)
(* 	  Mono t => Mono (on_i_mt x n t) *)
(* 	| Uni (bind, r) => Uni (on_i_tbind f x n bind, r) *)
(*   in *)
(*     f x n b *)
(*   end *)

(* fun on_t_mt on_v x n b = *)
(*   let *)
(*     fun f x n b = *)
(*       case b of *)
(* 	  Arrow (t1, d, t2) => Arrow (f x n t1, d, f x n t2) *)
(*         | TyNat (i, r) => TyNat (i, r) *)
(*         | TyArray (t, i) => TyArray (f x n t, i) *)
(*         | Unit r => Unit r *)
(* 	| Prod (t1, t2) => Prod (f x n t1, f x n t2) *)
(* 	| UniI (s, bind, r) => UniI (s, on_t_ibind f x n bind, r) *)
(*         | MtVar y => MtVar $ on_v x n y *)
(*         | MtApp (t1, t2) => MtApp (f x n t1, f x n t2) *)
(*         | MtAbs (k, bind, r) => MtAbs (k, on_t_tbind f x n bind, r) *)
(*         | MtAppI (t, i) => MtAppI (f x n t, i) *)
(*         | MtAbsI (s, bind, r) => MtAbsI (s, on_t_ibind f x n bind, r) *)
(* 	| BaseType a => BaseType a *)
(*         | UVar a => b *)
(*         | TDatatype (Unbound.Abs dt, r) => *)
(*           let *)
(*             fun on_constr_decl x n (name, c, r) = (name, on_t_constr_core f x n c, r) *)
(*             val dt = Bind $ from_Unbound dt *)
(*             val Bind dt = on_t_tbind (on_t_tbinds return3 (on_pair (return3, on_list on_constr_decl))) x n dt *)
(*             val dt = to_Unbound dt *)
(*           in *)
(*             TDatatype (Unbound.Abs dt, r) *)
(*           end *)
(*   in *)
(*     f x n b *)
(*   end *)
    
(* and on_t_constr_core on_mt x n b = on_t_ibinds return3 (on_pair (on_mt, return3)) x n b *)

fun on_t_type_visitor_vtable cast (on_var, n) : ('this, int) type_visitor_vtable =
  let
    fun extend_t this env _ = env + 1
    fun visit_var this env data = on_var env n data
  in
    default_type_visitor_vtable
      cast
      extend_noop
      extend_t
      visit_var
      visit_noop
      visit_noop
      visit_noop
      visit_noop
      visit_noop
  end

fun new_on_t_type_visitor a = new_type_visitor on_t_type_visitor_vtable a
    
fun on_t_mt on_var x n b =
  let
    val visitor as (TypeVisitor vtable) = new_on_t_type_visitor (on_var, n)
  in
    #visit_mtype vtable visitor x b
  end
    
fun on_t_t on_var x n b =
  let
    val visitor as (TypeVisitor vtable) = new_on_t_type_visitor (on_var, n)
  in
    #visit_ty vtable visitor x b
  end
    
fun on_t_constr_core on_var x n b =
  let
    val visitor as (TypeVisitor vtable) = new_on_t_type_visitor (on_var, n)
  in
    #visit_constr_core vtable visitor x b
  end
    
fun on_t_c on_var x n b =
  let
    val visitor as (TypeVisitor vtable) = new_on_t_type_visitor (on_var, n)
  in
    #visit_constr_info vtable visitor x b
  end
    
(* fun on_t_t on_t_mt x n b = *)
(*   let *)
(*     fun f x n b = *)
(*       case b of *)
(* 	  Mono t => Mono (on_t_mt x n t) *)
(* 	| Uni (bind, r) => Uni (on_t_tbind f x n bind, r) *)
(*   in *)
(*     f x n b *)
(*   end *)

(* fun shiftx_i_c x n ((family, tbinds) : mtype constr) : mtype constr = *)
(*   (family, *)
(*    on_i_tbinds return3 (on_i_constr_core (shiftx_i_i, shiftx_i_s)) x n tbinds) *)

(* fun shiftx_t_c x n (((m, family), tbinds) : mtype constr) : mtype constr = *)
(*   ((m, shiftx_id x n family), *)
(*    on_t_tbinds return3 (on_t_constr_core shiftx_var) x n tbinds) *)

fun shiftx_i_mt x n b = on_i_mt (shiftx_i_i, shiftx_i_s) x n b
fun shift_i_mt b = shiftx_i_mt 0 1 b
and shiftx_t_mt x n b = on_t_mt shiftx_var x n b
fun shift_t_mt b = shiftx_t_mt 0 1 b

fun shiftx_i_t x n b = on_i_t (shiftx_i_i, shiftx_i_s) x n b
fun shift_i_t b = shiftx_i_t 0 1 b
fun shiftx_t_t x n b = on_t_t shiftx_var x n b
fun shift_t_t b = shiftx_t_t 0 1 b

fun shiftx_i_c x n b = on_i_c (shiftx_i_i, shiftx_i_s) x n b
fun shift_i_c b = shiftx_i_c 0 1 b
fun shiftx_t_c x n b = on_t_c shiftx_var x n b
fun shift_t_c b = shiftx_t_c 0 1 b

fun forget_i_mt x n b = on_i_mt (forget_i_i, forget_i_s) x n b
fun forget_t_mt x n b = on_t_mt forget_var x n b
fun forget_i_t x n b = on_i_t (forget_i_i, forget_i_s) x n b
fun forget_t_t x n b = on_t_t forget_var x n b

end

functor TypeSubstFn (structure Type : TYPE
                     val visit_MtVar : (Namespaces.idepth * Namespaces.tdepth) * int * Type.mtype -> Namespaces.idepth * Namespaces.tdepth -> Type.var -> Type.mtype
                     val substx_i_i : int -> int -> Type.idx -> Type.idx -> Type.idx
                     val substx_i_s : int -> int -> Type.idx -> Type.sort -> Type.sort
                    ) = struct

open Type
open Util
       
infixr 0 $
         
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
