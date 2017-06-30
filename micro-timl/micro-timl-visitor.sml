structure MicroTiMLVisitor = struct

open MicroTiML
open Unbound
open Util
open Operators
       
infixr 0 $
infix 0 !!

type ('this, 'env, 'var, 'bsort, 'idx, 'sort, 'var2, 'bsort2, 'idx2, 'sort2) ty_visitor_vtable =
     {
       visit_kind : 'this -> 'env -> 'bsort kind -> 'bsort2 kind,
       visit_KType : 'this -> 'env -> unit -> 'bsort2 kind,
       visit_KArrow : 'this -> 'env -> 'bsort * 'bsort kind -> 'bsort2 kind,
       visit_KArrowT : 'this -> 'env -> 'bsort kind * 'bsort kind -> 'bsort2 kind,
       visit_ty : 'this -> 'env -> ('var, 'bsort, 'idx, 'sort) ty -> ('var2, 'bsort2, 'idx2, 'sort2) ty,
       visit_TVar : 'this -> 'env -> 'var -> ('var2, 'bsort2, 'idx2, 'sort2) ty,
       visit_TConst : 'this -> 'env -> ty_const -> ('var2, 'bsort2, 'idx2, 'sort2) ty,
       visit_TBinOp : 'this -> 'env -> ty_bin_op * ('var, 'bsort, 'idx, 'sort) ty * ('var, 'bsort, 'idx, 'sort) ty -> ('var2, 'bsort2, 'idx2, 'sort2) ty,
       visit_TArrow : 'this -> 'env -> ('var, 'bsort, 'idx, 'sort) ty * 'idx * ('var, 'bsort, 'idx, 'sort) ty -> ('var2, 'bsort2, 'idx2, 'sort2) ty,
       visit_TAbsI : 'this -> 'env -> ('bsort, ('var, 'bsort, 'idx, 'sort) ty) ibind_anno -> ('var2, 'bsort2, 'idx2, 'sort2) ty,
       visit_TAppI : 'this -> 'env -> ('var, 'bsort, 'idx, 'sort) ty * 'idx -> ('var2, 'bsort2, 'idx2, 'sort2) ty,
       visit_TQuan : 'this -> 'env -> unit quan * ('bsort kind, ('var, 'bsort, 'idx, 'sort) ty) tbind_anno -> ('var2, 'bsort2, 'idx2, 'sort2) ty,
       visit_TQuanI : 'this -> 'env -> unit quan * ('sort, ('var, 'bsort, 'idx, 'sort) ty) ibind_anno -> ('var2, 'bsort2, 'idx2, 'sort2) ty,
       visit_TRec : 'this -> 'env -> ('bsort kind, ('var, 'bsort, 'idx, 'sort) ty) tbind_anno -> ('var2, 'bsort2, 'idx2, 'sort2) ty,
       visit_TNat : 'this -> 'env -> 'idx -> ('var2, 'bsort2, 'idx2, 'sort2) ty,
       visit_TArr : 'this -> 'env -> ('var, 'bsort, 'idx, 'sort) ty * 'idx -> ('var2, 'bsort2, 'idx2, 'sort2) ty,
       visit_TAbsT : 'this -> 'env -> ('bsort kind, ('var, 'bsort, 'idx, 'sort) ty) tbind_anno -> ('var2, 'bsort2, 'idx2, 'sort2) ty,
       visit_TAppT : 'this -> 'env -> ('var, 'bsort, 'idx, 'sort) ty * ('var, 'bsort, 'idx, 'sort) ty -> ('var2, 'bsort2, 'idx2, 'sort2) ty,
       visit_var : 'this -> 'env -> 'var -> 'var2,
       visit_bsort : 'this -> 'env -> 'bsort -> 'bsort2,
       visit_idx : 'this -> 'env -> 'idx -> 'idx2,
       visit_sort : 'this -> 'env -> 'sort -> 'sort2,
       visit_ty_const : 'this -> 'env -> ty_const -> ty_const,
       visit_ty_bin_op : 'this -> 'env -> ty_bin_op -> ty_bin_op,
       visit_quan : 'this -> 'env -> unit quan -> unit quan,
       visit_ibind_anno_bsort : 'this -> ('env -> 'bsort -> 'bsort2) -> ('env -> ('var, 'bsort, 'idx, 'sort) ty -> ('var2, 'bsort2, 'idx2, 'sort2) ty) -> 'env -> ('bsort, ('var, 'bsort, 'idx, 'sort) ty) ibind_anno -> ('bsort2, ('var2, 'bsort2, 'idx2, 'sort2) ty) ibind_anno,
       visit_ibind_anno_sort : 'this -> ('env -> 'sort -> 'sort2) -> ('env -> ('var, 'bsort, 'idx, 'sort) ty -> ('var2, 'bsort2, 'idx2, 'sort2) ty) -> 'env -> ('sort, ('var, 'bsort, 'idx, 'sort) ty) ibind_anno -> ('sort2, ('var2, 'bsort2, 'idx2, 'sort2) ty) ibind_anno,
       visit_tbind_anno : 'this -> ('env -> 'bsort kind -> 'bsort2 kind) -> ('env -> ('var, 'bsort, 'idx, 'sort) ty -> ('var2, 'bsort2, 'idx2, 'sort2) ty) -> 'env -> ('bsort kind, ('var, 'bsort, 'idx, 'sort) ty) tbind_anno -> ('bsort2 kind, ('var2, 'bsort2, 'idx2, 'sort2) ty) tbind_anno,
       extend_i : 'this -> 'env -> iname -> 'env,
       extend_t : 'this -> 'env -> tname -> 'env
     }
       
type ('this, 'env, 'var, 'bsort, 'idx, 'sort, 'var2, 'bsort2, 'idx2, 'sort2) ty_visitor_interface =
     ('this, 'env, 'var, 'bsort, 'idx, 'sort, 'var2, 'bsort2, 'idx2, 'sort2) ty_visitor_vtable
                                       
fun override_visit_TVar (record : ('this, 'env, 'var, 'bsort, 'idx, 'sort, 'var2, 'bsort2, 'idx2, 'sort2) ty_visitor_vtable) new : ('this, 'env, 'var, 'bsort, 'idx, 'sort, 'var2, 'bsort2, 'idx2, 'sort2) ty_visitor_vtable =
  {
       visit_kind = #visit_kind record,
       visit_KType = #visit_KType record,
       visit_KArrow = #visit_KArrow record,
       visit_KArrowT = #visit_KArrowT record,
       visit_ty = #visit_ty record,
       visit_TVar = new,
       visit_TConst = #visit_TConst record,
       visit_TBinOp = #visit_TBinOp record,
       visit_TArrow = #visit_TArrow record,
       visit_TAbsI = #visit_TAbsI record,
       visit_TAppI = #visit_TAppI record,
       visit_TQuan = #visit_TQuan record,
       visit_TQuanI = #visit_TQuanI record,
       visit_TRec = #visit_TRec record,
       visit_TNat = #visit_TNat record,
       visit_TArr = #visit_TArr record,
       visit_TAbsT = #visit_TAbsT record,
       visit_TAppT = #visit_TAppT record,
       visit_var = #visit_var record,
       visit_bsort = #visit_bsort record,
       visit_idx = #visit_idx record,
       visit_sort = #visit_sort record,
       visit_ty_const = #visit_ty_const record,
       visit_ty_bin_op = #visit_ty_bin_op record,
       visit_quan = #visit_quan record,
       visit_ibind_anno_bsort = #visit_ibind_anno_bsort record,
       visit_ibind_anno_sort = #visit_ibind_anno_sort record,
       visit_tbind_anno = #visit_tbind_anno record,
       extend_i = #extend_i record,
       extend_t = #extend_t record
  }

(***************** the default visitor  **********************)    

open VisitorUtil
       
fun default_ty_visitor_vtable
      (cast : 'this -> ('this, 'env, 'var, 'bsort, 'idx, 'sort, 'var2, 'bsort2, 'idx2, 'sort2) ty_visitor_interface)
      extend_i
      extend_t
      visit_var
      visit_bsort
      visit_idx
      visit_sort
    : ('this, 'env, 'var, 'bsort, 'idx, 'sort, 'var2, 'bsort2, 'idx2, 'sort2) ty_visitor_vtable =
  let
    fun visit_kind this env data =
      let
        val vtable = cast this
      in
        case data of
            KType => #visit_KType vtable this env ()
          | KArrow data => #visit_KArrow vtable this env data
          | KArrowT data => #visit_KArrowT vtable this env data
      end
    fun visit_KType this env data = KType
    fun visit_KArrow this env data = 
      let
        val vtable = cast this
        val (b, k) = data
        val b = #visit_bsort vtable this env b
        val k = #visit_kind vtable this env k
      in
        KArrow (b, k)
      end
    fun visit_KArrowT this env data = 
      let
        val vtable = cast this
        val (k1, k2) = data
        val k1 = #visit_kind vtable this env k1
        val k2 = #visit_kind vtable this env k2
      in
        KArrowT (k1, k2)
      end
    fun visit_ty this env data =
      let
        val vtable = cast this
      in
        case data of
            TVar data => #visit_TVar vtable this env data
          | TConst data => #visit_TConst vtable this env data
          | TBinOp data => #visit_TBinOp vtable this env data
          | TArrow data => #visit_TArrow vtable this env data
          | TAbsI data => #visit_TAbsI vtable this env data
          | TAppI data => #visit_TAppI vtable this env data
          | TQuan data => #visit_TQuan vtable this env data
          | TQuanI data => #visit_TQuanI vtable this env data
          | TRec data => #visit_TRec vtable this env data
          | TNat data => #visit_TNat vtable this env data
          | TArr data => #visit_TArr vtable this env data
          | TAbsT data => #visit_TAbsT vtable this env data
          | TAppT data => #visit_TAppT vtable this env data
      end
    fun visit_TVar this env data =
      let
        val vtable = cast this
      in
        TVar $ #visit_var vtable this env data
      end
    fun visit_TConst this env data =
      let
        val vtable = cast this
      in
        TConst $ #visit_ty_const vtable this env data
      end
    fun visit_TBinOp this env data = 
      let
        val vtable = cast this
        val (opr, t1, t2) = data
        val opr = #visit_ty_bin_op vtable this env opr
        val t1 = #visit_ty vtable this env t1
        val t2 = #visit_ty vtable this env t2
      in
        TBinOp (opr, t1, t2)
      end
    fun visit_TArrow this env data = 
      let
        val vtable = cast this
        val (t1, i, t2) = data
        val t1 = #visit_ty vtable this env t1
        val i = #visit_idx vtable this env i
        val t2 = #visit_ty vtable this env t2
      in
        TArrow (t1, i, t2)
      end
    fun visit_TAbsI this env data =
      let
        val vtable = cast this
      in
        TAbsI $ #visit_ibind_anno_bsort vtable this (#visit_bsort vtable this) (#visit_ty vtable this) env data
      end
    fun visit_TAppI this env data = 
      let
        val vtable = cast this
        val (t, i) = data
        val t = #visit_ty vtable this env t
        val i = #visit_idx vtable this env i
      in
        TAppI (t, i)
      end
    fun visit_TQuan this env data =
      let
        val (q, bind) = data
        val vtable = cast this
        val q = #visit_quan vtable this env q
        val bind = #visit_tbind_anno vtable this (#visit_kind vtable this) (#visit_ty vtable this) env bind
      in
        TQuan (q, bind)
      end
    fun visit_TQuanI this env data =
      let
        val (q, bind) = data
        val vtable = cast this
        val q = #visit_quan vtable this env q
        val bind = #visit_ibind_anno_sort vtable this (#visit_sort vtable this) (#visit_ty vtable this) env bind
      in
        TQuanI (q, bind)
      end
    fun visit_TRec this env data =
      let
        val vtable = cast this
      in
        TRec $ #visit_tbind_anno vtable this (#visit_kind vtable this) (#visit_ty vtable this) env data
      end
    fun visit_TNat this env data = 
      let
        val vtable = cast this
      in
        TNat $ #visit_idx vtable this env data
      end
    fun visit_TArr this env data = 
      let
        val vtable = cast this
        val (t, i) = data
        val t = #visit_ty vtable this env t
        val i = #visit_idx vtable this env i
      in
        TArr (t, i)
      end
    fun visit_TAbsT this env data =
      let
        val vtable = cast this
      in
        TAbsT $ #visit_tbind_anno vtable this (#visit_kind vtable this) (#visit_ty vtable this) env data
      end
    fun visit_TAppT this env data = 
      let
        val vtable = cast this
        val (t1, t2) = data
        val t1 = #visit_ty vtable this env t1
        val t2 = #visit_ty vtable this env t2
      in
        TAppT (t1, t2)
      end
    fun default_visit_bind_anno extend this = visit_bind_anno (extend this)
  in
    {visit_kind = visit_kind,
     visit_KType = visit_KType,
     visit_KArrow = visit_KArrow,
     visit_KArrowT = visit_KArrowT,
     visit_ty = visit_ty,
     visit_TVar = visit_TVar,
     visit_TConst = visit_TConst,
     visit_TBinOp = visit_TBinOp,
     visit_TArrow = visit_TArrow,
     visit_TAbsI = visit_TAbsI,
     visit_TAppI = visit_TAppI,
     visit_TQuan = visit_TQuan,
     visit_TQuanI = visit_TQuanI,
     visit_TRec = visit_TRec,
     visit_TNat = visit_TNat,
     visit_TArr = visit_TArr,
     visit_TAbsT = visit_TAbsT,
     visit_TAppT = visit_TAppT,
     visit_var = visit_var,
     visit_bsort = visit_bsort,
     visit_idx = visit_idx,
     visit_sort = visit_sort,
     visit_ty_const = visit_noop,
     visit_ty_bin_op = visit_noop,
     visit_quan = visit_noop,
     visit_ibind_anno_bsort = default_visit_bind_anno extend_i,
     visit_ibind_anno_sort = default_visit_bind_anno extend_i,
     visit_tbind_anno = default_visit_bind_anno extend_t,
     extend_i = extend_i,
     extend_t = extend_t
    }
  end

datatype ('env, 'var, 'bsort, 'idx, 'sort, 'var2, 'bsort2, 'idx2, 'sort2) ty_visitor =
         TyVisitor of (('env, 'var, 'bsort, 'idx, 'sort, 'var2, 'bsort2, 'idx2, 'sort2) ty_visitor, 'env, 'var, 'bsort, 'idx, 'sort, 'var2, 'bsort2, 'idx2, 'sort2) ty_visitor_interface

fun ty_visitor_impls_interface (this : ('env, 'var, 'bsort, 'idx, 'sort, 'var2, 'bsort2, 'idx2, 'sort2) ty_visitor) :
    (('env, 'var, 'bsort, 'idx, 'sort, 'var2, 'bsort2, 'idx2, 'sort2) ty_visitor, 'env, 'var, 'bsort, 'idx, 'sort, 'var2, 'bsort2, 'idx2, 'sort2) ty_visitor_interface =
  let
    val TyVisitor vtable = this
  in
    vtable
  end

fun new_ty_visitor vtable params =
  let
    val vtable = vtable ty_visitor_impls_interface params
  in
    TyVisitor vtable
  end
    
(***************** the "shift_i_t" visitor  **********************)    
    
fun shift_i_ty_visitor_vtable cast ((shift_i, shift_s), n) : ('this, int, 'var, 'bsort, 'idx, 'sort, 'var, 'bsort, 'idx2, 'sort2) ty_visitor_vtable =
  let
    fun extend_i this env _ = env + 1
    val extend_t = extend_noop
    val visit_var = visit_noop
    fun do_shift shift this env b = shift env n b
  in
    default_ty_visitor_vtable
      cast
      extend_i
      extend_t
      visit_var
      visit_noop
      (do_shift shift_i)
      (do_shift shift_s)
  end

fun new_shift_i_ty_visitor a = new_ty_visitor shift_i_ty_visitor_vtable a
    
fun shift_i_t_fn shifts x n b =
  let
    val visitor as (TyVisitor vtable) = new_shift_i_ty_visitor (shifts, n)
  in
    #visit_ty vtable visitor x b
  end
    
(***************** the "shift_t_t" visitor  **********************)    
    
fun shift_t_ty_visitor_vtable cast (shift_var, n) : ('this, int, 'var, 'bsort, 'idx, 'sort, 'var2, 'bsort, 'idx, 'sort) ty_visitor_vtable =
  let
    val extend_i = extend_noop
    fun extend_t this env _ = env + 1
    fun visit_var this env data = shift_var env n data
  in
    default_ty_visitor_vtable
      cast
      extend_i
      extend_t
      visit_var
      visit_noop
      visit_noop
      visit_noop
  end

fun new_shift_t_ty_visitor a = new_ty_visitor shift_t_ty_visitor_vtable a
    
fun shift_t_t_fn shift_var x n b =
  let
    val visitor as (TyVisitor vtable) = new_shift_t_ty_visitor (shift_var, n)
  in
    #visit_ty vtable visitor x b
  end
    
(***************** the "subst_t_t" visitor  **********************)    

fun subst_t_ty_visitor_vtable cast (shift_var, compare_var, (shift_i_i, shift_i_s), d, x, v) : ('this, idepth * tdepth, 'var, 'bsort, 'idx, 'sort, 'var, 'bsort, 'idx, 'sort) ty_visitor_vtable =
  let
    fun extend_i this (di, dt) _ = (idepth_inc di, dt)
    fun extend_t this (di, dt) _ = (di, tdepth_inc dt)
    fun add_depth (di, dt) (di', dt') = (idepth_add (di, di'), tdepth_add (dt, dt'))
    fun get_di (di, dt) = di
    fun get_dt (di, dt) = dt
    val shift_i_t = shift_i_t_fn (shift_i_i, shift_i_s)
    val shift_t_t = shift_t_t_fn shift_var
    fun visit_TVar this env y =
      let
        val x = x + unTDepth (get_dt env)
      in
        case compare_var y x of
            CmpEq =>
            let
              val (di, dt) = add_depth d env
            in
              shift_i_t 0 (unIDepth di) $ shift_t_t 0 (unTDepth dt) v
            end
          | CmpGreater y' =>
            TVar y'
          | _ =>
            TVar y
      end
    val vtable = 
        default_ty_visitor_vtable
          cast
          extend_i
          extend_t
          (visit_imposs "subst_t_t/visit_var")
          visit_noop
          visit_noop
          visit_noop
    val vtable = override_visit_TVar vtable visit_TVar
  in
    vtable
  end

fun new_subst_t_ty_visitor params = new_ty_visitor subst_t_ty_visitor_vtable params
    
fun subst_t_t_fn shift_var compare_var shifts d x v b =
  let
    val visitor as (TyVisitor vtable) = new_subst_t_ty_visitor (shift_var, compare_var, shifts, d, x, v)
  in
    #visit_ty vtable visitor (IDepth 0, TDepth 0) b
  end
                               
end
