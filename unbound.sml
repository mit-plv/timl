(* an implementation of Stephanie Weirich's "Unbound" DSL *)

structure Unbound = struct

open Util
open VisitorUtil
       
infixr 0 $
         
datatype 'p abs = Abs of 'p
datatype 'name binder = Binder of 'name
datatype 't outer = Outer of 't
datatype 'p rebind = Rebind of 'p
           
type 't inner = ('t outer) rebind
fun Inner t = Rebind (Outer t)
type ('p, 't) bind = ('p * 't inner) abs
fun Bind (p, t) = Abs (p, Inner t)

type ('name, 't) bind_simp = ('name binder, 't) bind
fun BindSimp (name, t) = Bind (Binder name, t)
type ('name, 'anno, 't) bind_anno = ('name binder * 'anno outer, 't) bind
fun BindAnno ((name, anno), t) = Bind ((Binder name, Outer anno), t)

type 'env ctx = {outer : 'env, current : 'env ref}

fun env2ctx env = {outer = env, current = ref env}

fun visit_abs visit_'p env (Abs p1) =
  Abs $ visit_'p (env2ctx env) p1

fun visit_binder extend (ctx : 'env ctx) (Binder x1) =
  let
    val env = !(#current ctx)
    val env = extend env x1
    val () = #current ctx := env
  in
    Binder x1
  end
fun visit_outer visit_'t (ctx : 'env ctx) (Outer t1) = Outer $ visit_'t (#outer ctx) t1
fun visit_rebind visit_'p (ctx : 'env ctx) (Rebind p1) = Rebind $ visit_'p {outer = !(#current ctx), current = #current ctx} p1
    
fun visit_inner x = (visit_rebind o visit_outer) x
fun visit_bind visit_'p = visit_abs o visit_pair visit_'p o visit_inner
                                             
fun visit_bind_simp extend = visit_bind (visit_binder extend)
fun visit_bind_anno extend visit_'anno = visit_bind (visit_pair (visit_binder extend) (visit_outer visit_'anno))

end

signature BINDERS = sig
  type ('name, 't) bind_simp
  type ('name, 'anno, 't) bind_anno
end

functor BinderUtilFn (structure Binders : BINDERS
                      type iname
                      type tname
                      type ename
                     ) = struct
type iname = iname
type tname = tname
type ename = ename
type 't ibind = (iname, 't) Binders.bind_simp
type 't tbind = (tname, 't) Binders.bind_simp
type 't ebind = (ename, 't) Binders.bind_simp
type ('anno, 't) ibind_anno = (iname, 'anno, 't) Binders.bind_anno
type ('anno, 't) tbind_anno = (tname, 'anno, 't) Binders.bind_anno
type ('anno, 't) ebind_anno = (ename, 'anno, 't) Binders.bind_anno
end

functor NamespacesFn (type name) = struct
datatype idx_namespace = IdxNS
datatype type_namespace = TypeNS
datatype expr_namespace = ExprNS
type iname = idx_namespace * name
type tname = type_namespace * name
type ename = expr_namespace * name
fun IName name = (IdxNS, name)
fun TName name = (TypeNS, name)
fun EName name = (ExprNS, name)
                   
type idepth = idx_namespace * int
type edepth = expr_namespace * int
fun IDepth n = (IdxNS, n)
fun EDepth n = (ExprNS, n)
fun idepth_inc (IdxNS, n) = (IdxNS, n + 1)
fun edepth_inc (ExprNS, n) = (ExprNS, n + 1)
fun idepth_add ((IdxNS, a), (IdxNS, b)) = (IdxNS, a + b)
fun edepth_add ((ExprNS, a), (ExprNS, b)) = (ExprNS, a + b)
fun open_idepth (IdxNS, n) = n
fun open_edepth (ExprNS, n) = n
                              
end

structure Namespaces = NamespacesFn (type name = string * Region.region)
                                    
structure Binders = BinderUtilFn (structure Binders = Unbound
                                  type iname = Namespaces.iname
                                  type tname = Namespaces.tname
                                  type ename = Namespaces.ename
                                 )
                                     
