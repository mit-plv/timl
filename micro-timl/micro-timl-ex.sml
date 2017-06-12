(* micro-timl extended *)

structure MicroTiMLEx = struct

open MicroTiML

infixr 0 $
         
datatype ('var, 'bsort, 'idx, 'sort) expr =
         EVar of 'var
         | EAppI of ('var, 'bsort, 'idx, 'sort) expr * 'idx
         | EMatchSum of ('var, 'bsort, 'idx, 'sort) expr * ('var, 'bsort, 'idx, 'sort) expr ebind list
         | EMatchPair of ('var, 'bsort, 'idx, 'sort) expr * ('var, 'bsort, 'idx, 'sort) expr ebind ebind
         | EMatchUnfold of ('var, 'bsort, 'idx, 'sort) expr * ('var, 'bsort, 'idx, 'sort) expr ebind
         | EMatchUnpackI of ('var, 'bsort, 'idx, 'sort) expr * ('var, 'bsort, 'idx, 'sort) expr ebind ibind

type ('this, 'env, 'var, 'bsort, 'idx, 'sort, 'var2, 'bsort2, 'idx2, 'sort2) expr_visitor_vtable =
     {
       visit_expr : 'this -> 'env -> ('var, 'bsort, 'idx, 'sort) expr -> ('var2, 'bsort2, 'idx2, 'sort2) expr,
       visit_EVar : 'this -> 'env -> 'var -> ('var2, 'bsort2, 'idx2, 'sort2) expr,
       visit_EAppI : 'this -> 'env -> ('var, 'bsort, 'idx, 'sort) expr * 'idx -> ('var2, 'bsort2, 'idx2, 'sort2) expr,
       visit_EMatchSum : 'this -> 'env -> ('var, 'bsort, 'idx, 'sort) expr * ('var, 'bsort, 'idx, 'sort) expr ebind list -> ('var2, 'bsort2, 'idx2, 'sort2) expr,
       visit_EMatchPair : 'this -> 'env -> ('var, 'bsort, 'idx, 'sort) expr * ('var, 'bsort, 'idx, 'sort) expr ebind ebind -> ('var2, 'bsort2, 'idx2, 'sort2) expr,
       visit_EMatchUnfold : 'this -> 'env -> ('var, 'bsort, 'idx, 'sort) expr * ('var, 'bsort, 'idx, 'sort) expr ebind -> ('var2, 'bsort2, 'idx2, 'sort2) expr,
       visit_EMatchUnpackI : 'this -> 'env -> ('var, 'bsort, 'idx, 'sort) expr * ('var, 'bsort, 'idx, 'sort) expr ebind ibind -> ('var2, 'bsort2, 'idx2, 'sort2) expr,
       visit_var : 'this -> 'env -> 'var -> 'var2,
       (* visit_bsort : 'this -> 'env -> 'bsort -> 'bsort2, *)
       visit_idx : 'this -> 'env -> 'idx -> 'idx2,
       (* visit_sort : 'this -> 'env -> 'sort -> 'sort2, *)
       (* visit_region : 'this -> 'env -> region -> region, *)
       extend_i : 'this -> 'env -> iname -> 'env,
       extend_e : 'this -> 'env -> ename -> 'env
     }
       
type ('this, 'env, 'var, 'bsort, 'idx, 'sort, 'var2, 'bsort2, 'idx2, 'sort2) expr_visitor_interface =
     ('this, 'env, 'var, 'bsort, 'idx, 'sort, 'var2, 'bsort2, 'idx2, 'sort2) expr_visitor_vtable
                                       
fun override_visit_EVar (record : ('this, 'env, 'var, 'bsort, 'idx, 'sort, 'var2, 'bsort2, 'idx2, 'sort2) expr_visitor_vtable) new : ('this, 'env, 'var, 'bsort, 'idx, 'sort, 'var2, 'bsort2, 'idx2, 'sort2) expr_visitor_vtable =
  {
    visit_expr = #visit_expr record,
    visit_EVar = new,
    visit_EAppI = #visit_EAppI record,
    visit_EMatchSum = #visit_EMatchSum record,
    visit_EMatchPair = #visit_EMatchPair record,
    visit_EMatchUnfold = #visit_EMatchUnfold record,
    visit_EMatchUnpackI = #visit_EMatchUnpackI record,
    visit_var = #visit_var record,
    visit_idx = #visit_idx record,
    extend_i = #extend_i record,
    extend_e = #extend_e record
  }

(***************** the default visitor  **********************)    

open VisitorUtil
       
val visit_ibind = Unbound.visit_bind_simp
val visit_tbind = Unbound.visit_bind_simp
val visit_ebind = Unbound.visit_bind_simp
                    
fun default_expr_visitor_vtable
      (cast : 'this -> ('this, 'env, 'var, 'bsort, 'idx, 'sort, 'var2, 'bsort2, 'idx2, 'sort2) expr_visitor_interface)
      extend_i
      extend_e
      visit_var
      visit_idx
    : ('this, 'env, 'var, 'bsort, 'idx, 'sort, 'var2, 'bsort2, 'idx2, 'sort2) expr_visitor_vtable =
  let
    fun visit_expr this env data =
      let
        val vtable = cast this
      in
        case data of
            EVar data => #visit_EVar vtable this env data
          | EAppI data => #visit_EAppI vtable this env data
          | EMatchSum data => #visit_EMatchSum vtable this env data
          | EMatchPair data => #visit_EMatchPair vtable this env data
          | EMatchUnfold data => #visit_EMatchUnfold vtable this env data
          | EMatchUnpackI data => #visit_EMatchUnpackI vtable this env data
      end
    fun visit_EVar this env data =
      let
        val vtable = cast this
      in
        EVar $ #visit_var vtable this env data
      end
    fun visit_EAppI this env data = 
      let
        val vtable = cast this
        val (e, i) = data
        val e = #visit_expr vtable this env e
        val i = #visit_idx vtable this env i
      in
        EAppI (e, i)
      end
    (* fun default_visit_binder extend this = visit_binder (extend this) *)
    val visit_ebind = fn this => visit_ebind (#extend_e (cast this) this)
    val visit_ibind = fn this => visit_ibind (#extend_i (cast this) this)
    fun visit_EMatchSum this env data =
      let
        val vtable = cast this
        val (e, branches) = data
        val e = #visit_expr vtable this env e
        val branches = (visit_list o visit_ebind this) (#visit_expr vtable this) env branches
      in
        EMatchSum (e, branches)
      end
    fun visit_EMatchPair this env data =
      let
        val vtable = cast this
        val (e, branch) = data
        val e = #visit_expr vtable this env e
        val branch = (visit_ebind this o visit_ebind this) (#visit_expr vtable this) env branch
      in
        EMatchPair (e, branch)
      end
    fun visit_EMatchUnfold this env data =
      let
        val vtable = cast this
        val (e, branch) = data
        val e = #visit_expr vtable this env e
        val branch = visit_ebind this (#visit_expr vtable this) env branch
      in
        EMatchUnfold (e, branch)
      end
    fun visit_EMatchUnpackI this env data =
      let
        val vtable = cast this
        val (e, branch) = data
        val e = #visit_expr vtable this env e
        val branch = (visit_ibind this o visit_ebind this) (#visit_expr vtable this) env branch
      in
        EMatchUnpackI (e, branch)
      end
  in
    {
      visit_expr = visit_expr,
      visit_EVar = visit_EVar,
      visit_EAppI = visit_EAppI,
      visit_EMatchSum = visit_EMatchSum,
      visit_EMatchPair = visit_EMatchPair,
      visit_EMatchUnfold = visit_EMatchUnfold,
      visit_EMatchUnpackI = visit_EMatchUnpackI,
      visit_var = visit_var,
      visit_idx = visit_idx,
      extend_i = extend_i,
      extend_e = extend_e
    }
  end

datatype ('env, 'var, 'bsort, 'idx, 'sort, 'var2, 'bsort2, 'idx2, 'sort2) expr_visitor =
         ExprVisitor of (('env, 'var, 'bsort, 'idx, 'sort, 'var2, 'bsort2, 'idx2, 'sort2) expr_visitor, 'env, 'var, 'bsort, 'idx, 'sort, 'var2, 'bsort2, 'idx2, 'sort2) expr_visitor_interface

fun expr_visitor_impls_interface (this : ('env, 'var, 'bsort, 'idx, 'sort, 'var2, 'bsort2, 'idx2, 'sort2) expr_visitor) :
    (('env, 'var, 'bsort, 'idx, 'sort, 'var2, 'bsort2, 'idx2, 'sort2) expr_visitor, 'env, 'var, 'bsort, 'idx, 'sort, 'var2, 'bsort2, 'idx2, 'sort2) expr_visitor_interface =
  let
    val ExprVisitor vtable = this
  in
    vtable
  end

fun new_expr_visitor vtable params =
  let
    val vtable = vtable expr_visitor_impls_interface params
  in
    ExprVisitor vtable
  end
    
(***************** the "shift_i_e" visitor  **********************)    
    
fun shift_i_expr_visitor_vtable cast (shift_i, n) : ('this, int, 'var, 'bsort2, 'idx, 'sort2, 'var, 'bsort, 'idx2, 'sort) expr_visitor_vtable =
  let
    fun extend_i this env _ = env + 1
    val extend_e = extend_noop
    fun do_shift shift this env b = shift env n b
  in
    default_expr_visitor_vtable
      cast
      extend_i
      extend_e
      visit_noop
      (do_shift shift_i)
  end

fun new_shift_i_expr_visitor params = new_expr_visitor shift_i_expr_visitor_vtable params
    
fun shift_i_e shift_i x n b =
  let
    val visitor as (ExprVisitor vtable) = new_shift_i_expr_visitor (shift_i, n)
  in
    #visit_expr vtable visitor x b
  end
    
(***************** the "shift_e_e" visitor  **********************)    
    
fun shift_e_expr_visitor_vtable cast n : ('this, int, int, 'bsort, 'idx, 'sort, int, 'bsort2, 'idx, 'sort2) expr_visitor_vtable =
  let
    val extend_i = extend_noop
    fun extend_e this env _ = env + 1
    fun visit_var this env data = ShiftUtil.shiftx_int env n data
  in
    default_expr_visitor_vtable
      cast
      extend_i
      extend_e
      visit_var
      visit_noop
  end

fun new_shift_e_expr_visitor params = new_expr_visitor shift_e_expr_visitor_vtable params
    
fun shift_e_e x n b =
  let
    val visitor as (ExprVisitor vtable) = new_shift_e_expr_visitor n
  in
    #visit_expr vtable visitor x b
  end
    
(***************** the "subst_e_e" visitor  **********************)    

fun subst_e_expr_visitor_vtable cast (shift_i_i, d, x, v) : ('this, idepth * edepth, int, 'bsort, 'idx, 'sort, int, 'bsort2, 'idx, 'sort2) expr_visitor_vtable =
  let
    fun extend_i this env _ = mapFst idepth_inc env
    fun extend_e this env _ = mapSnd edepth_inc env
    val add_depth = mapPair2 idepth_add edepth_add
    fun visit_EVar this env y =
      let
        val x = x + open_edepth (snd env)
      in
        if y = x then
          let
            val (di, de) = add_depth d env
          in
            shift_i_e shift_i_i 0 (open_idepth di) $ shift_e_e 0 (open_edepth de) v
          end
        else if y > x then
          EVar (y - 1)
        else
          EVar y
      end
    val vtable = 
        default_expr_visitor_vtable
          cast
          extend_i
          extend_e
          (visit_imposs "subst_e_e/visit_var")
          visit_noop
    val vtable = override_visit_EVar vtable visit_EVar
  in
    vtable
  end

fun new_subst_e_expr_visitor params = new_expr_visitor subst_e_expr_visitor_vtable params
    
fun subst_e_e shift_i_i d x v b =
  let
    val visitor as (ExprVisitor vtable) = new_subst_e_expr_visitor (shift_i_i, d, x, v)
  in
    #visit_expr vtable visitor (IDepth 0, EDepth 0) b
  end

end
