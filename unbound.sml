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
type ('p, 't) bind = ('p * 't inner) abs

datatype 'p tele =
         TeleNil
         | TeleCons of 'p * 'p tele rebind

type ('name, 't) bind_simp = ('name binder, 't) bind
type ('name, 'anno, 't) bind_anno = ('name binder * 'anno outer, 't) bind

fun Inner t = Rebind (Outer t)
fun Bind (p, t) = Abs (p, Inner t)
fun Teles ps = foldr (TeleCons o mapSnd Rebind) TeleNil ps
fun BindSimp (name, t) = Bind (Binder name, t)
fun BindAnno ((name, anno), t) = Bind ((Binder name, Outer anno), t)

fun unfold_Binder (Binder n) = n
fun unfold_Bind (Abs (p, Rebind (Outer t))) = (p, t)
fun unfold_Inner (Rebind (Outer t)) = t
fun unfold_Teles t =
  case t of
      TeleNil => []
    | TeleCons (p, Rebind t) => p :: unfold_Teles t
fun unfold_BindAnno t =
  let
    val ((Binder name, Outer anno), t) = unfold_Bind t
  in
    ((name, anno), t)
  end
                                      
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
                      structure Names : sig
                                  type iname
                                  type tname
                                  type cname
                                  type ename
                                end
                     ) = struct
open Names
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
datatype constr_namespace = ConstrNS
datatype expr_namespace = ExprNS
type iname = idx_namespace * name
type tname = type_namespace * name
type cname = constr_namespace * name
type ename = expr_namespace * name
fun IName name = (IdxNS, name)
fun TName name = (TypeNS, name)
fun CName name = (ConstrNS, name)
fun EName name = (ExprNS, name)
val unfold_Name = Util.snd
                   
type idepth = idx_namespace * int
type edepth = expr_namespace * int
fun IDepth n = (IdxNS, n)
fun EDepth n = (ExprNS, n)
fun idepth_inc (IdxNS, n) = (IdxNS, n + 1)
fun edepth_inc (ExprNS, n) = (ExprNS, n + 1)
fun idepth_add ((IdxNS, a), (IdxNS, b)) = (IdxNS, a + b)
fun edepth_add ((ExprNS, a), (ExprNS, b)) = (ExprNS, a + b)
fun unfold_idepth (IdxNS, n) = n
fun unfold_edepth (ExprNS, n) = n
                              
end

structure Namespaces = NamespacesFn (type name = string * Region.region)
                                    
structure Binders = BinderUtilFn (structure Binders = Unbound
                                  structure Names = Namespaces
                                 )
                                     
