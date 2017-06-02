(* an implementation of Stephanie Weirich's "Unbound" DSL *)
structure Unbound = struct

type 'p abs = 'p
type 'bn binder = 'bn
type 't outer = 't
type 'p rebind = 'p
           
type 't inner = ('t outer) rebind
type ('p, 't) bind = ('p * 't inner) abs
type ('bn, 'anno, 't) anno_bind = ('bn binder * 'anno outer, 't) bind

type 'env context = {outer : 'env, current : 'env ref}

fun visit_pair visit_fst visit_snd extend env (a, b) =
  (visit_fst extend env a, visit_snd extend env b)

fun visit_abs visit_'p extend env p1 =
  visit_'p extend {outer = env, current = ref env} p1
fun visit_binder _ extend (ctx : 'env context) x1 =
  let
    val env = !(#current ctx)
    val (env, x2) = extend env x1
    val () = #current ctx := env
  in
    x2
  end
fun visit_outer visit_'t extend (ctx : 'env context) t1 = visit_'t (#outer ctx) t1
fun visit_rebind visit_'p extend (ctx : 'env context) p1 = visit_'p extend {outer = !(#current ctx), current = #current ctx} p1
    
fun visit_inner visit_'t = visit_rebind (visit_outer visit_'t)
fun visit_bind visit_'p visit_'t = visit_abs (visit_pair visit_'p (visit_inner visit_'t))
fun visit_anno_bind visit_'bn visit_'anno visit_'t = visit_bind (visit_pair (visit_binder visit_'bn) (visit_outer visit_'anno)) visit_'t

end

signature BINDER_VISITOR = sig
  structure Binders : BINDERS
  type ibn
  type tbn
  val visit_ibind_anno : ('env -> 'anno -> 'anno2) -> ('env -> 't -> 't2) -> ('env -> ibn -> 'env) -> 'env -> ('anno, 't) Binders.ibind_anno -> ('anno2, 't2) Binders.ibind_anno        
  val visit_tbind_anno : ('env -> 'anno -> 'anno2) -> ('env -> 't -> 't2) -> ('env -> tbn -> 'env) -> 'env -> ('anno, 't) Binders.tbind_anno -> ('anno2, 't2) Binders.tbind_anno        
end
                             
functor VisitorFn (structure M : MICRO_TIML
                   structure BinderVisitor : BINDER_VISITOR
                   sharing M.Binders = BinderVisitor.Binders
                  ) = struct

open M
open BinderVisitor
open Binders
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
       visit_ibind_anno_bsort : 'this -> ('env -> 'bsort -> 'bsort2) -> ('env -> ('var, 'bsort, 'idx, 'sort) ty -> ('var2, 'bsort2, 'idx2, 'sort2) ty) -> ('env -> ibn -> 'env) -> 'env -> ('bsort, ('var, 'bsort, 'idx, 'sort) ty) ibind_anno -> ('bsort2, ('var2, 'bsort2, 'idx2, 'sort2) ty) ibind_anno,
       visit_ibind_anno_sort : 'this -> ('env -> 'sort -> 'sort2) -> ('env -> ('var, 'bsort, 'idx, 'sort) ty -> ('var2, 'bsort2, 'idx2, 'sort2) ty) -> ('env -> ibn -> 'env) -> 'env -> ('sort, ('var, 'bsort, 'idx, 'sort) ty) ibind_anno -> ('sort2, ('var2, 'bsort2, 'idx2, 'sort2) ty) ibind_anno,
       visit_tbind_anno : 'this -> ('env -> 'bsort kind -> 'bsort2 kind) -> ('env -> ('var, 'bsort, 'idx, 'sort) ty -> ('var2, 'bsort2, 'idx2, 'sort2) ty) -> ('env -> tbn -> 'env) -> 'env -> ('bsort kind, ('var, 'bsort, 'idx, 'sort) ty) tbind_anno -> ('bsort2 kind, ('var2, 'bsort2, 'idx2, 'sort2) ty) tbind_anno,
       extend_idx : 'this -> 'env -> ibn -> 'env,
       extend_ty : 'this -> 'env -> tbn -> 'env
     }
       
type ('this, 'env, 'var, 'bsort, 'idx, 'sort, 'var2, 'bsort2, 'idx2, 'sort2) ty_visitor_interface =
     ('this, 'env, 'var, 'bsort, 'idx, 'sort, 'var2, 'bsort2, 'idx2, 'sort2) ty_visitor_vtable
                                       
fun extend_noop this env x1 = env
val visit_noop = return3
fun visit_imposs msg _ _ _ = raise Impossible ""
                           
(***************** the default visitor  **********************)    
    
fun default_ty_visitor_vtable
      (cast : 'this -> ('this, 'env, 'var, 'bsort, 'idx, 'sort, 'var2, 'bsort2, 'idx2, 'sort2) ty_visitor_interface)
      extend_idx
      extend_ty
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
        val (opr, e1, e2) = data
        val opr = #visit_ty_bin_op vtable this env opr
        val e1 = #visit_ty vtable this env e1
        val e2 = #visit_ty vtable this env e2
      in
        TBinOp (opr, e1, e2)
      end
    fun visit_TArrow this env data = 
      let
        val vtable = cast this
        val (e1, i, e2) = data
        val e1 = #visit_ty vtable this env e1
        val i = #visit_idx vtable this env i
        val e2 = #visit_ty vtable this env e2
      in
        TArrow (e1, i, e2)
      end
    fun visit_TAbsI this env data =
      let
        val vtable = cast this
      in
        TAbsI $ #visit_ibind_anno_bsort vtable this (#visit_bsort vtable this) (#visit_ty vtable this) (#extend_idx vtable this) env data
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
        val bind = #visit_tbind_anno vtable this (#visit_kind vtable this) (#visit_ty vtable this) (#extend_ty vtable this) env bind
      in
        TQuan (q, bind)
      end
    fun visit_TQuanI this env data =
      let
        val (q, bind) = data
        val vtable = cast this
        val q = #visit_quan vtable this env q
        val bind = #visit_ibind_anno_sort vtable this (#visit_sort vtable this) (#visit_ty vtable this) (#extend_idx vtable this) env bind
      in
        TQuanI (q, bind)
      end
    fun visit_TRec this env data =
      let
        val vtable = cast this
      in
        TRec $ #visit_tbind_anno vtable this (#visit_kind vtable this) (#visit_ty vtable this) (#extend_ty vtable this) env data
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
        TAbsT $ #visit_tbind_anno vtable this (#visit_kind vtable this) (#visit_ty vtable this) (#extend_ty vtable this) env data
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
    fun default_visit_ibind_anno this = visit_ibind_anno
    fun default_visit_tbind_anno this = visit_tbind_anno
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
     visit_ibind_anno_bsort = default_visit_ibind_anno,
     visit_ibind_anno_sort = default_visit_ibind_anno,
     visit_tbind_anno = default_visit_tbind_anno,
     extend_idx = extend_idx,
     extend_ty = extend_ty
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
    
(***************** the "shift_i" visitor  **********************)    
    
fun shift_i_ty_visitor_vtable cast (shift_i, shift_s, n) : ('this, int, int, 'bsort, 'idx, 'sort, int, 'bsort, 'idx2, 'sort2) ty_visitor_vtable =
  let
    fun extend_idx this env _ = env + 1
    val extend_ty = extend_noop
    val visit_var = visit_noop
    fun do_shift shift this env b = shift env n b
  in
    default_ty_visitor_vtable
      cast
      extend_idx
      extend_ty
      visit_var
      visit_noop
      (do_shift shift_i)
      (do_shift shift_s)
  end

val new_shift_i_ty_visitor = new_ty_visitor shift_i_ty_visitor_vtable
    
fun shift_i_t shift_i shift_s x n e =
  let
    val visitor as (TyVisitor vtable) = new_shift_i_ty_visitor (shift_i, shift_s, n)
  in
    #visit_ty vtable visitor x e
  end
    
(***************** the "shift_t" visitor  **********************)    
    
fun shift_t_ty_visitor_vtable cast n : ('this, int, int, 'bsort, 'idx, 'sort, int, 'bsort, 'idx, 'sort) ty_visitor_vtable =
  let
    val extend_idx = extend_noop
    fun extend_ty this env _ = env + 1
    fun visit_var this env data = ShiftUtil.shiftx_int env n data
  in
    default_ty_visitor_vtable
      cast
      extend_idx
      extend_ty
      visit_var
      visit_noop
      visit_noop
      visit_noop
  end

val new_shift_t_ty_visitor = new_ty_visitor shift_t_ty_visitor_vtable
    
fun shift_t_t x n e =
  let
    val visitor as (TyVisitor vtable) = new_shift_t_ty_visitor n
  in
    #visit_ty vtable visitor x e
  end
    
end
