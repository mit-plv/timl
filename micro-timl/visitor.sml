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
  type bn
  val visit_ibind_anno : ('env -> 'anno -> 'anno2) -> ('env -> 't -> 't2) -> ('env -> bn -> 'env * bn) -> 'env -> ('anno, 't) Binders.ibind_anno -> ('anno2, 't2) Binders.ibind_anno        
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
       visit_kind : 'this -> 'env -> 'bsort kind -> 'bsort2 kind,
       visit_ty_const : 'this -> 'env -> ty_const -> ty_const,
       visit_ty_bin_op : 'this -> 'env -> ty_bin_op -> ty_bin_op,
       visit_quan : 'this -> 'env -> unit quan -> unit quan,
       visit_ibind_anno_bsort : 'this -> ('env -> 'bsort -> 'bsort2) -> ('env -> ('var, 'bsort, 'idx, 'sort) ty -> ('var2, 'bsort2, 'idx2, 'sort2) ty) -> ('env -> bn -> 'env * bn) -> 'env -> ('bsort, ('var, 'bsort, 'idx, 'sort) ty) ibind_anno -> ('bsort2, ('var2, 'bsort2, 'idx2, 'sort2) ty) ibind_anno,
       visit_ibind_anno_sort : 'this -> ('env -> 'sort -> 'sort2) -> ('env -> ('var, 'bsort, 'idx, 'sort) ty -> ('var2, 'bsort2, 'idx2, 'sort2) ty) -> ('env -> bn -> 'env * bn) -> 'env -> ('sort, ('var, 'bsort, 'idx, 'sort) ty) ibind_anno -> ('sort2, ('var2, 'bsort2, 'idx2, 'sort2) ty) ibind_anno,
       visit_tbind_anno : 'this -> ('env -> 'bsort kind -> 'bsort2 kind) -> ('env -> ('var, 'bsort, 'idx, 'sort) ty -> ('var2, 'bsort2, 'idx2, 'sort2) ty) -> ('env -> bn -> 'env * bn) -> 'env -> ('bsort kind, ('var, 'bsort, 'idx, 'sort) ty) tbind_anno -> ('bsort2 kind, ('var2, 'bsort2, 'idx2, 'sort2) ty) tbind_anno,
       (* visit_bn : 'this -> 'env -> bn -> bn, *)
       extend : 'this -> 'env -> bn -> 'env * bn
     }
       
type ('this, 'env, 'var, 'bsort, 'idx, 'sort, 'var2, 'bsort2, 'idx2, 'sort2) ty_visitor_interface =
     ('this, 'env, 'var, 'bsort, 'idx, 'sort, 'var2, 'bsort2, 'idx2, 'sort2) ty_visitor_vtable
                                       
fun extend_noop this env x1 = (env, x1)
val visit_noop = return3
fun visit_imposs msg _ _ _ = raise Impossible ""
                           
fun default_ty_visitor_vtable
      (cast : 'this -> ('this, 'env, 'var, 'bsort, 'idx, 'sort, 'var2, 'bsort2, 'idx2, 'sort2) ty_visitor_interface)
      extend
      visit_var
      visit_bsort
      visit_idx
      visit_sort
    : ('this, 'env, 'var, 'bsort, 'idx, 'sort, 'var2, 'bsort2, 'idx2, 'sort2) ty_visitor_vtable =
  let
    fun visit_ty this env (t : ('var, 'bsort, 'idx, 'sort) ty) =
      let
        val vtable = cast this
      in
        case t of
            TVar data => #visit_TVar vtable this env data
          | TConst data => #visit_TConst vtable this env data
          | TBinOp data => #visit_TBinOp vtable this env data
          | TAbsI data => #visit_TAbsI vtable this env (data : ('bsort, ('var, 'bsort, 'idx, 'sort) ty) ibind_anno)
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
    fun visit_TVar this env data =
      let
        val vtable = cast this
      in
        TVar $ #visit_var vtable this env data
      end
    fun visit_TAbsI this env data =
      let
        val vtable = cast this
      in
        TAbsI $ #visit_ibind_anno_bsort vtable this (#visit_bsort vtable this) (#visit_ty vtable this) (#extend vtable this) env data
      end
    fun default_visit_ibind_anno this = visit_ibind_anno
  in
    {visit_ty = visit_ty,
     visit_TConst = visit_TConst,
     visit_TBinOp = visit_TBinOp,
     visit_TVar = visit_TVar,
     visit_TAbsI = visit_TAbsI,
     visit_ty_const = visit_noop,
     visit_var = visit_var,
     visit_bsort = visit_bsort,
     visit_idx = visit_idx,
     visit_sort = visit_sort,
     visit_ibind_anno_bsort = default_visit_ibind_anno,
     visit_ibind_anno_sort = default_visit_ibind_anno,
     extend = extend
    }
  end

end
