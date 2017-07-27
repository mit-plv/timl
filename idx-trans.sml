signature SHIFTABLE_VAR = sig
  type var
  val shiftx_var : int -> int -> var -> var
  val forget_var : int -> int -> var -> var
end
                                                      
functor IdxShiftFn (structure Idx : IDX
                    structure ShiftableVar : SHIFTABLE_VAR
                    sharing type Idx.var = ShiftableVar.var
                   ) = struct

open Idx
open ShiftableVar
open ShiftUtil
       
infixr 0 $
         
(* generic traversers for both 'shift' and 'forget' *)
         
structure IdxVisitor = IdxVisitorFn (structure S = Idx
                                     structure T = Idx)
open IdxVisitor
                                         
fun on_i_idx_visitor_vtable cast (on_var, n) : ('this, int) idx_visitor_vtable =
  let
    fun extend_i this env _ = env + 1
    fun visit_var this env data = on_var env n data
  in
    default_idx_visitor_vtable
      cast
      extend_i
      visit_var
      visit_noop
      visit_noop
      visit_noop
      visit_noop
  end

fun new_on_i_idx_visitor a = new_idx_visitor on_i_idx_visitor_vtable a
    
fun on_i_i on_var x n b =
  let
    val visitor as (IdxVisitor vtable) = new_on_i_idx_visitor (on_var, n)
  in
    #visit_idx vtable visitor x b
  end
    
fun on_i_p on_var x n b =
  let
    val visitor as (IdxVisitor vtable) = new_on_i_idx_visitor (on_var, n)
  in
    #visit_prop vtable visitor x b
  end
    
fun on_i_s on_var x n b =
  let
    val visitor as (IdxVisitor vtable) = new_on_i_idx_visitor (on_var, n)
  in
    #visit_sort vtable visitor x b
  end
    
(* fun on_i_i on_v x n b = *)
(*   let *)
(*     fun f x n b = *)
(*       case b of *)
(* 	  VarI y => VarI $ on_v x n y *)
(*         | IConst c => IConst c *)
(*         | UnOpI (opr, i, r) => UnOpI (opr, f x n i, r) *)
(* 	| BinOpI (opr, i1, i2) => BinOpI (opr, f x n i1, f x n i2) *)
(*         | Ite (i1, i2, i3, r) => Ite (f x n i1, f x n i2, f x n i3, r) *)
(*         | IAbs (b, bind, r) => IAbs (b, on_i_ibind f x n bind, r) *)
(*         | UVarI a => b (* uvars are closed, so no need to deal with *) *)
(*   in *)
(*     f x n b *)
(*   end *)

(* fun on_i_p on_i_i x n b = *)
(*   let *)
(*     fun f x n b = *)
(*       case b of *)
(* 	  PTrueFalse b => PTrueFalse b *)
(*         | Not (p, r) => Not (f x n p, r) *)
(* 	| BinConn (opr, p1, p2) => BinConn (opr, f x n p1, f x n p2) *)
(* 	| BinPred (opr, d1, d2) => BinPred (opr, on_i_i x n d1, on_i_i x n d2) *)
(*         | Quan (q, bs, bind, r) => Quan (q, bs, on_i_ibind f x n bind, r) *)
(*   in *)
(*     f x n b *)
(*   end *)

(* fun on_i_s on_i_i on_i_p x n b = *)
(*   let *)
(*     fun f x n b = *)
(*       case b of *)
(* 	  Basic s => Basic s *)
(* 	| Subset (s, bind, r) => Subset (s, on_i_ibind on_i_p x n bind, r) *)
(*         | UVarS a => b *)
(*         | SAbs (b, bind, r) => SAbs (b, on_i_ibind f x n bind, r) *)
(*         | SApp (s, i) => SApp (f x n s, on_i_i x n i) *)
(*   in *)
(*     f x n b *)
(*   end *)

(* shift *)
    
fun shiftx_i_i x n b = on_i_i shiftx_var x n b
fun shift_i_i b = shiftx_i_i 0 1 b

fun shiftx_i_p x n b = on_i_p shiftx_var x n b
fun shift_i_p b = shiftx_i_p 0 1 b

fun shiftx_i_s x n b = on_i_s shiftx_var x n b
fun shift_i_s b = shiftx_i_s 0 1 b

(* forget *)

fun forget_i_i x n b = on_i_i forget_var x n b
fun forget_i_p x n b = on_i_p forget_var x n b
fun forget_i_s x n b = on_i_s forget_var x n b
                              
end

functor IdxSubstFn (structure Idx : IDX
                    val visit_VarI : int * int * Idx.idx -> int -> Idx.var -> Idx.idx
                   ) = struct

open Idx
open Util
       
infixr 0 $

structure IdxVisitor = IdxVisitorFn (structure S = Idx
                                     structure T = Idx)
open IdxVisitor
                                         
(* fun substx_pair (f1, f2) d x v (b1, b2) = (f1 d x v b1, f2 d x v b2) *)
(* fun substx_list f d x v b = map (f d x v) b *)

(* depth [d] is used for shifting value [v] *)
fun subst_i_idx_visitor_vtable cast visit_VarI : ('this, int) idx_visitor_vtable =
  let
    fun extend_i this d _ = d + 1
    val vtable = 
        default_idx_visitor_vtable
          cast
          extend_i
          (visit_imposs "subst_i_i/visit_var")
          visit_noop
          visit_noop
          visit_noop
          visit_noop
    val vtable = override_visit_VarI vtable (ignore_this visit_VarI)
  in
    vtable
  end

fun new_subst_i_idx_visitor params = new_idx_visitor subst_i_idx_visitor_vtable params

fun subst_i_i_fn params b =
  let
    val visitor as (IdxVisitor vtable) = new_subst_i_idx_visitor params
  in
    #visit_idx vtable visitor 0 b
  end
                               
fun subst_i_p_fn params b =
  let
    val visitor as (IdxVisitor vtable) = new_subst_i_idx_visitor params
  in
    #visit_prop vtable visitor 0 b
  end
                               
fun subst_i_s_fn params b =
  let
    val visitor as (IdxVisitor vtable) = new_subst_i_idx_visitor params
  in
    #visit_sort vtable visitor 0 b
  end
                               
val subst_i_params = visit_VarI
                     
fun substx_i_i d x v = subst_i_i_fn $ subst_i_params (d, x, v)
fun substx_i_p d x v = subst_i_p_fn $ subst_i_params (d, x, v)
fun substx_i_s d x v = subst_i_s_fn $ subst_i_params (d, x, v)
      
fun subst_i_i v b = substx_i_i 0 0 v b
fun subst_i_p (v : idx) (b : prop) : prop = substx_i_p 0 0 v b
fun subst_i_s (v : idx) (b : sort) : sort = substx_i_s 0 0 v b

end
