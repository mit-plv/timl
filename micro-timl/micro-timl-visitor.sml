structure MicroTiMLVisitor = struct

open Operators
open MicroTiML
open Unbound
open Util
       
infixr 0 $
infix 0 !!

(***************** type visitor  **********************)    

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

fun override_visit_TAppT (record : ('this, 'env, 'var, 'bsort, 'idx, 'sort, 'var2, 'bsort2, 'idx2, 'sort2) ty_visitor_vtable) new : ('this, 'env, 'var, 'bsort, 'idx, 'sort, 'var2, 'bsort2, 'idx2, 'sort2) ty_visitor_vtable =
  {
       visit_kind = #visit_kind record,
       visit_KType = #visit_KType record,
       visit_KArrow = #visit_KArrow record,
       visit_KArrowT = #visit_KArrowT record,
       visit_ty = #visit_ty record,
       visit_TVar = #visit_TVar record,
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
       visit_TAppT = new,
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

fun override_visit_TAppI (record : ('this, 'env, 'var, 'bsort, 'idx, 'sort, 'var2, 'bsort2, 'idx2, 'sort2) ty_visitor_vtable) new : ('this, 'env, 'var, 'bsort, 'idx, 'sort, 'var2, 'bsort2, 'idx2, 'sort2) ty_visitor_vtable =
  {
       visit_kind = #visit_kind record,
       visit_KType = #visit_KType record,
       visit_KArrow = #visit_KArrow record,
       visit_KArrowT = #visit_KArrowT record,
       visit_ty = #visit_ty record,
       visit_TVar = #visit_TVar record,
       visit_TConst = #visit_TConst record,
       visit_TBinOp = #visit_TBinOp record,
       visit_TArrow = #visit_TArrow record,
       visit_TAbsI = #visit_TAbsI record,
       visit_TAppI = new,
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
    
(***************** expr visitor  **********************)    

type ('this, 'env, 'var, 'idx, 'sort, 'kind, 'ty, 'var2, 'idx2, 'sort2, 'kind2, 'ty2) expr_visitor_vtable =
     {
       visit_expr : 'this -> 'env -> ('var, 'idx, 'sort, 'kind, 'ty) expr -> ('var2, 'idx2, 'sort2, 'kind2, 'ty2) expr,
       visit_EVar : 'this -> 'env -> 'var -> ('var2, 'idx2, 'sort2, 'kind2, 'ty2) expr,
       visit_EConst : 'this -> 'env -> Operators.expr_const -> ('var2, 'idx2, 'sort2, 'kind2, 'ty2) expr,
       visit_ELoc : 'this -> 'env -> loc -> ('var2, 'idx2, 'sort2, 'kind2, 'ty2) expr,
       visit_EUnOp : 'this -> 'env -> 'ty expr_un_op * ('var, 'idx, 'sort, 'kind, 'ty) expr -> ('var2, 'idx2, 'sort2, 'kind2, 'ty2) expr,
       visit_EBinOp : 'this -> 'env -> expr_bin_op * ('var, 'idx, 'sort, 'kind, 'ty) expr * ('var, 'idx, 'sort, 'kind, 'ty) expr -> ('var2, 'idx2, 'sort2, 'kind2, 'ty2) expr,
       visit_EWrite : 'this -> 'env -> ('var, 'idx, 'sort, 'kind, 'ty) expr * ('var, 'idx, 'sort, 'kind, 'ty) expr * ('var, 'idx, 'sort, 'kind, 'ty) expr -> ('var2, 'idx2, 'sort2, 'kind2, 'ty2) expr,
       visit_ECase : 'this -> 'env -> ('var, 'idx, 'sort, 'kind, 'ty) expr * ('var, 'idx, 'sort, 'kind, 'ty) expr ebind * ('var, 'idx, 'sort, 'kind, 'ty) expr ebind -> ('var2, 'idx2, 'sort2, 'kind2, 'ty2) expr,
       visit_EAbs : 'this -> 'env -> ('ty, ('var, 'idx, 'sort, 'kind, 'ty) expr) ebind_anno -> ('var2, 'idx2, 'sort2, 'kind2, 'ty2) expr,
       visit_ERec : 'this -> 'env -> ('ty, ('var, 'idx, 'sort, 'kind, 'ty) expr) ebind_anno -> ('var2, 'idx2, 'sort2, 'kind2, 'ty2) expr,
       visit_EAbsT : 'this -> 'env -> ('kind, ('var, 'idx, 'sort, 'kind, 'ty) expr) tbind_anno -> ('var2, 'idx2, 'sort2, 'kind2, 'ty2) expr,
       visit_EAppT : 'this -> 'env -> ('var, 'idx, 'sort, 'kind, 'ty) expr * 'ty -> ('var2, 'idx2, 'sort2, 'kind2, 'ty2) expr,
       visit_EAbsI : 'this -> 'env -> ('sort, ('var, 'idx, 'sort, 'kind, 'ty) expr) ibind_anno -> ('var2, 'idx2, 'sort2, 'kind2, 'ty2) expr,
       visit_EAppI : 'this -> 'env -> ('var, 'idx, 'sort, 'kind, 'ty) expr * 'idx -> ('var2, 'idx2, 'sort2, 'kind2, 'ty2) expr,
       visit_EPack : 'this -> 'env -> 'ty * 'ty * ('var, 'idx, 'sort, 'kind, 'ty) expr -> ('var2, 'idx2, 'sort2, 'kind2, 'ty2) expr,
       visit_EUnpack : 'this -> 'env -> ('var, 'idx, 'sort, 'kind, 'ty) expr * ('var, 'idx, 'sort, 'kind, 'ty) expr ebind tbind -> ('var2, 'idx2, 'sort2, 'kind2, 'ty2) expr,
       visit_EPackI : 'this -> 'env -> 'ty * 'idx * ('var, 'idx, 'sort, 'kind, 'ty) expr -> ('var2, 'idx2, 'sort2, 'kind2, 'ty2) expr,
       visit_EUnpackI : 'this -> 'env -> ('var, 'idx, 'sort, 'kind, 'ty) expr * ('var, 'idx, 'sort, 'kind, 'ty) expr ebind ibind -> ('var2, 'idx2, 'sort2, 'kind2, 'ty2) expr,
       visit_EAscTime : 'this -> 'env -> ('var, 'idx, 'sort, 'kind, 'ty) expr * 'idx (* time ascription *) -> ('var2, 'idx2, 'sort2, 'kind2, 'ty2) expr,
       visit_EAscType : 'this -> 'env -> ('var, 'idx, 'sort, 'kind, 'ty) expr * 'ty (* type ascription *) -> ('var2, 'idx2, 'sort2, 'kind2, 'ty2) expr,
       visit_ENever : 'this -> 'env -> 'ty -> ('var2, 'idx2, 'sort2, 'kind2, 'ty2) expr,
       visit_ELet : 'this -> 'env -> ('var, 'idx, 'sort, 'kind, 'ty) expr * ('var, 'idx, 'sort, 'kind, 'ty) expr ebind -> ('var2, 'idx2, 'sort2, 'kind2, 'ty2) expr,
       visit_var : 'this -> 'env -> 'var -> 'var2,
       visit_idx : 'this -> 'env -> 'idx -> 'idx2,
       visit_sort : 'this -> 'env -> 'sort -> 'sort2,
       visit_kind : 'this -> 'env -> 'kind -> 'kind2,
       visit_ty : 'this -> 'env -> 'ty -> 'ty2,
       extend_i : 'this -> 'env -> iname -> 'env,
       extend_t : 'this -> 'env -> tname -> 'env,
       extend_e : 'this -> 'env -> ename -> 'env
     }
       
type ('this, 'env, 'var, 'idx, 'sort, 'kind, 'ty, 'var2, 'idx2, 'sort2, 'kind2, 'ty2) expr_visitor_interface =
     ('this, 'env, 'var, 'idx, 'sort, 'kind, 'ty, 'var2, 'idx2, 'sort2, 'kind2, 'ty2) expr_visitor_vtable
                                       
fun override_visit_EVar (record : ('this, 'env, 'var, 'idx, 'sort, 'kind, 'ty, 'var2, 'idx2, 'sort2, 'kind2, 'ty2) expr_visitor_vtable) new : ('this, 'env, 'var, 'idx, 'sort, 'kind, 'ty, 'var2, 'idx2, 'sort2, 'kind2, 'ty2) expr_visitor_vtable =
  {
    visit_expr = #visit_expr record,
    visit_EVar = new,
    visit_EConst = #visit_EConst record,
    visit_ELoc = #visit_ELoc record,
    visit_EUnOp = #visit_EUnOp record,
    visit_EBinOp = #visit_EBinOp record,
    visit_EWrite = #visit_EWrite record,
    visit_ECase = #visit_ECase record,
    visit_EAbs = #visit_EAbs record,
    visit_ERec = #visit_ERec record,
    visit_EAbsT = #visit_EAbsT record,
    visit_EAppT = #visit_EAppT record,
    visit_EAbsI = #visit_EAbsI record,
    visit_EAppI = #visit_EAppI record,
    visit_EPack = #visit_EPack record,
    visit_EUnpack = #visit_EUnpack record,
    visit_EPackI = #visit_EPackI record,
    visit_EUnpackI = #visit_EUnpackI record,
    visit_EAscTime = #visit_EAscTime record,
    visit_EAscType = #visit_EAscType record,
    visit_ENever = #visit_ENever record,
    visit_ELet = #visit_ELet record,
    visit_var = #visit_var record,
    visit_idx = #visit_idx record,
    visit_sort = #visit_sort record,
    visit_kind = #visit_kind record,
    visit_ty = #visit_ty record,
    extend_i = #extend_i record,
    extend_t = #extend_t record,
    extend_e = #extend_e record
  }

(***************** the default visitor  **********************)    

open VisitorUtil
       
fun default_expr_visitor_vtable
      (cast : 'this -> ('this, 'env, 'var, 'idx, 'sort, 'kind, 'ty, 'var2, 'idx2, 'sort2, 'kind, 'ty2) expr_visitor_interface)
      extend_i
      extend_t
      extend_e
      visit_var
      visit_idx
      visit_sort
      visit_ty
    : ('this, 'env, 'var, 'idx, 'sort, 'kind, 'ty, 'var2, 'idx2, 'sort2, 'kind, 'ty2) expr_visitor_vtable =
  let
    fun visit_expr this env data =
      let
        val vtable = cast this
      in
        case data of
            EVar data => #visit_EVar vtable this env data
          | EConst data => #visit_EConst vtable this env data
          | ELoc data => #visit_ELoc vtable this env data
          | EUnOp data => #visit_EUnOp vtable this env data
          | EBinOp data => #visit_EBinOp vtable this env data
          | EWrite data => #visit_EWrite vtable this env data
          | ECase data => #visit_ECase vtable this env data
          | EAbs data => #visit_EAbs vtable this env data
          | ERec data => #visit_ERec vtable this env data
          | EAbsT data => #visit_EAbsT vtable this env data
          | EAppT data => #visit_EAppT vtable this env data
          | EAbsI data => #visit_EAbsI vtable this env data
          | EAppI data => #visit_EAppI vtable this env data
          | EPack data => #visit_EPack vtable this env data
          | EUnpack data => #visit_EUnpack vtable this env data
          | EPackI data => #visit_EPackI vtable this env data
          | EUnpackI data => #visit_EUnpackI vtable this env data
          | EAscTime data => #visit_EAscTime vtable this env data
          | EAscType data => #visit_EAscType vtable this env data
          | ENever data => #visit_ENever vtable this env data
          | ELet data => #visit_ELet vtable this env data
      end
    fun visit_EVar this env data =
      let
        val vtable = cast this
      in
        EVar $ #visit_var vtable this env data
      end
    fun visit_EConst this env data = EConst data
    fun visit_ELoc this env data = ELoc data
    fun visit_un_op this env opr = 
      let
        val vtable = cast this
        fun on_t x = #visit_ty vtable this env x
      in
        case opr of
            EUProj opr => EUProj opr
          | EUInj (opr, t) => EUInj (opr, on_t t)
          | EUFold t => EUFold $ on_t t
          | EUUnfold => EUUnfold
      end
    fun visit_EUnOp this env data = 
      let
        val vtable = cast this
        val (opr, e) = data
        val opr = visit_un_op this env opr
        val e = #visit_expr vtable this env e
      in
        EUnOp (opr, e)
      end
    fun visit_EBinOp this env data = 
      let
        val vtable = cast this
        val (opr, e1, e2) = data
        val e1 = #visit_expr vtable this env e1
        val e2 = #visit_expr vtable this env e2
      in
        EBinOp (opr, e1, e2)
      end
    fun visit_EWrite this env data = 
      let
        val vtable = cast this
        val (e1, e2, e3) = data
        val e1 = #visit_expr vtable this env e1
        val e2 = #visit_expr vtable this env e2
        val e3 = #visit_expr vtable this env e3
      in
        EWrite (e1, e2, e3)
      end
    fun visit_ibind this = visit_bind_simp (#extend_i (cast this) this)
    fun visit_tbind this = visit_bind_simp (#extend_t (cast this) this)
    fun visit_ebind this = visit_bind_simp (#extend_e (cast this) this)
    fun visit_ibind_anno this = visit_bind_anno (#extend_i (cast this) this)
    fun visit_tbind_anno this = visit_bind_anno (#extend_t (cast this) this)
    fun visit_ebind_anno this = visit_bind_anno (#extend_e (cast this) this)
    fun visit_ECase this env data =
      let
        val vtable = cast this
        val (e, e1, e2) = data
        val e = #visit_expr vtable this env e
        val e1 = visit_ebind this (#visit_expr vtable this) env e1
        val e2 = visit_ebind this (#visit_expr vtable this) env e2
      in
        ECase (e, e1, e2)
      end
    fun visit_EAbs this env data =
      let
        val vtable = cast this
        val data = visit_ebind_anno this (#visit_ty vtable this) (#visit_expr vtable this) env data
      in
        EAbs data
      end
    fun visit_ERec this env data =
      let
        val vtable = cast this
        val data = visit_ebind_anno this (#visit_ty vtable this) (#visit_expr vtable this) env data
      in
        ERec data
      end
    fun visit_EAbsT this env data =
      let
        val vtable = cast this
        val data = visit_tbind_anno this (#visit_kind vtable this) (#visit_expr vtable this) env data
      in
        EAbsT data
      end
    fun visit_EAppT this env data = 
      let
        val vtable = cast this
        val (e, t) = data
        val e = #visit_expr vtable this env e
        val t = #visit_ty vtable this env t
      in
        EAppT (e, t)
      end
    fun visit_EAbsI this env data =
      let
        val vtable = cast this
        val data = visit_ibind_anno this (#visit_sort vtable this) (#visit_expr vtable this) env data
      in
        EAbsI data
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
    fun visit_EPack this env data = 
      let
        val vtable = cast this
        val (t_all, t, e) = data
        val t_all = #visit_ty vtable this env t_all
        val t = #visit_ty vtable this env t
        val e = #visit_expr vtable this env e
      in
        EPack (t_all, t, e)
      end
    fun visit_EUnpack this env data =
      let
        val vtable = cast this
        val (e, bind) = data
        val e = #visit_expr vtable this env e
        val bind = (visit_tbind this o visit_ebind this) (#visit_expr vtable this) env bind
      in
        EUnpack (e, bind)
      end
    fun visit_EPackI this env data = 
      let
        val vtable = cast this
        val (t, i, e) = data
        val t = #visit_ty vtable this env t
        val i = #visit_idx vtable this env i
        val e = #visit_expr vtable this env e
      in
        EPackI (t, i, e)
      end
    fun visit_EUnpackI this env data =
      let
        val vtable = cast this
        val (e, bind) = data
        val e = #visit_expr vtable this env e
        val bind = (visit_ibind this o visit_ebind this) (#visit_expr vtable this) env bind
      in
        EUnpackI (e, bind)
      end
    fun visit_EAscTime this env data = 
      let
        val vtable = cast this
        val (e, i) = data
        val e = #visit_expr vtable this env e
        val i = #visit_idx vtable this env i
      in
        EAscTime (e, i)
      end
    fun visit_EAscType this env data = 
      let
        val vtable = cast this
        val (e, t) = data
        val e = #visit_expr vtable this env e
        val t = #visit_ty vtable this env t
      in
        EAscType (e, t)
      end
    fun visit_ENever this env data = 
      let
        val vtable = cast this
        val data = #visit_ty vtable this env data
      in
        ENever data
      end
    fun visit_ELet this env data =
      let
        val vtable = cast this
        val (e, bind) = data
        val e = #visit_expr vtable this env e
        val bind = visit_ebind this (#visit_expr vtable this) env bind
      in
        ELet (e, bind)
      end
  in
    {
      visit_expr = visit_expr,
      visit_EVar = visit_EVar,
      visit_EConst = visit_EConst,
      visit_ELoc = visit_ELoc,
      visit_EUnOp = visit_EUnOp,
      visit_EBinOp = visit_EBinOp,
      visit_EWrite = visit_EWrite,
      visit_ECase = visit_ECase,
      visit_EAbs = visit_EAbs,
      visit_ERec = visit_ERec,
      visit_EAbsT = visit_EAbsT,
      visit_EAppT = visit_EAppT,
      visit_EAbsI = visit_EAbsI,
      visit_EAppI = visit_EAppI,
      visit_EPack = visit_EPack,
      visit_EUnpack = visit_EUnpack,
      visit_EPackI = visit_EPackI,
      visit_EUnpackI = visit_EUnpackI,
      visit_EAscTime = visit_EAscTime,
      visit_EAscType = visit_EAscType,
      visit_ENever = visit_ENever,
      visit_ELet = visit_ELet,
      visit_var = visit_var,
      visit_idx = visit_idx,
      visit_sort = visit_sort,
      visit_kind = visit_noop,
      visit_ty = visit_ty,
      extend_i = extend_i,
      extend_t = extend_t,
      extend_e = extend_e
    }
  end

datatype ('env, 'var, 'idx, 'sort, 'kind, 'ty, 'var2, 'idx2, 'sort2, 'kind2, 'ty2) expr_visitor =
         ExprVisitor of (('env, 'var, 'idx, 'sort, 'kind, 'ty, 'var2, 'idx2, 'sort2, 'kind2, 'ty2) expr_visitor, 'env, 'var, 'idx, 'sort, 'kind, 'ty, 'var2, 'idx2, 'sort2, 'kind2, 'ty2) expr_visitor_interface

fun expr_visitor_impls_interface (this : ('env, 'var, 'idx, 'sort, 'kind, 'ty, 'var2, 'idx2, 'sort2, 'kind2, 'ty2) expr_visitor) :
    (('env, 'var, 'idx, 'sort, 'kind, 'ty, 'var2, 'idx2, 'sort2, 'kind2, 'ty2) expr_visitor, 'env, 'var, 'idx, 'sort, 'kind, 'ty, 'var2, 'idx2, 'sort2, 'kind2, 'ty2) expr_visitor_interface =
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
    
(***************** the "subst_i_t" visitor  **********************)    

fun subst_i_ty_visitor_vtable cast ((subst_i_i, subst_i_s), d, x, v) : ('this, int, 'var, 'bsort, 'idx, 'sort, 'var, 'bsort, 'idx2, 'sort2) ty_visitor_vtable =
  let
    fun extend_i this env _ = env + 1
    fun visit_idx this env b = subst_i_i (d + env) (x + env) v b
    fun visit_sort this env b = subst_i_s (d + env) (x + env) v b
  in
    default_ty_visitor_vtable
      cast
      extend_i
      extend_noop
      visit_noop
      visit_noop
      visit_idx
      visit_sort
  end

fun new_subst_i_ty_visitor params = new_ty_visitor subst_i_ty_visitor_vtable params
    
fun subst_i_t_fn substs d x v b =
  let
    val visitor as (TyVisitor vtable) = new_subst_i_ty_visitor (substs, d, x, v)
  in
    #visit_ty vtable visitor 0 b
  end

(***************** the "subst_t_t" visitor  **********************)    

fun subst_t_ty_visitor_vtable cast ((compare_var, shift_var, shift_i_i, shift_i_s), d, x, v) : ('this, idepth * tdepth, 'var, 'bsort, 'idx, 'sort, 'var, 'bsort, 'idx, 'sort) ty_visitor_vtable =
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
    
fun subst_t_t_fn params d x v b =
  let
    val visitor as (TyVisitor vtable) = new_subst_t_ty_visitor (params, d, x, v)
  in
    #visit_ty vtable visitor (IDepth 0, TDepth 0) b
  end
                               
(***************** the "normalize_t" visitor  **********************)    
    
fun normalize_ty_visitor_vtable cast (subst0_i_t, subst0_t_t) : ('this, unit, 'var, 'bsort, 'idx, 'sort, 'var, 'bsort, 'idx, 'sort) ty_visitor_vtable =
  let
    fun visit_TAppT this env data = 
      let
        val vtable = cast this
        val (t1, t2) = data
        val t1 = #visit_ty vtable this env t1
        val t2 = #visit_ty vtable this env t2
      in
        case t1 of
            TAbsT bind =>
            let
              val (_, t1) = unBindAnno bind
            in
              #visit_ty vtable this env $ subst0_t_t t2 t1
            end
          | _ => TAppT (t1, t2)
      end
    fun visit_TAppI this env data = 
      let
        val vtable = cast this
        val (t, i) = data
        val t = #visit_ty vtable this env t
      in
        case t of
            TAbsI bind =>
            let
              val (_, t) = unBindAnno bind
            in
              #visit_ty vtable this env $ subst0_i_t i t
            end
          | _ => TAppI (t, i)
      end
    val vtable =
        default_ty_visitor_vtable
          cast
          extend_noop
          extend_noop
          visit_noop
          visit_noop
          visit_noop
          visit_noop
    val vtable = override_visit_TAppT vtable visit_TAppT
    val vtable = override_visit_TAppI vtable visit_TAppI
  in
    vtable
  end

fun new_normalize_ty_visitor a = new_ty_visitor normalize_ty_visitor_vtable a
    
fun normalize_t_fn params t =
  let
    val visitor as (TyVisitor vtable) = new_normalize_ty_visitor params
  in
    #visit_ty vtable visitor () t
  end
    
(***************** the "export" visitor: convertnig de Bruijn indices to nameful terms **********************)    

fun export_ty_visitor_vtable cast (visit_var, visit_idx, visit_sort) =
  let
    fun extend_i this (sctx, kctx) name = (Name2str name :: sctx, kctx)
    fun extend_t this (sctx, kctx) name = (sctx, Name2str name :: kctx)
    fun only_s f this (sctx, kctx) name = f sctx name
  in
    default_ty_visitor_vtable
      cast
      extend_i
      extend_t
      (ignore_this visit_var)
      visit_noop
      (only_s visit_idx)
      (only_s visit_sort)
  end

fun new_export_ty_visitor params = new_ty_visitor export_ty_visitor_vtable params
    
fun export_t_fn params ctx b =
  let
    val visitor as (TyVisitor vtable) = new_export_ty_visitor params
  in
    #visit_ty vtable visitor ctx b
  end

end
