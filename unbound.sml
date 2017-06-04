(* an implementation of Stephanie Weirich's "Unbound" DSL *)

structure Unbound = struct

type 'p abs = 'p
type 'name binder = 'name
type 't outer = 't
type 'p rebind = 'p
           
type 't inner = ('t outer) rebind
type ('p, 't) bind = ('p * 't inner) abs

type ('name, 't) bind_simp = ('name binder, 't) bind
type ('name, 'anno, 't) bind_anno = ('name binder * 'anno outer, 't) bind

type 'env ctx = {outer : 'env, current : 'env ref}

fun visit_pair visit_fst visit_snd env (a, b) =
  (visit_fst env a, visit_snd env b)
    
fun env2ctx env = {outer = env, current = ref env}

fun visit_abs visit_'p env p1 =
  visit_'p (env2ctx env) p1
fun visit_binder extend (ctx : 'env ctx) x1 =
  let
    val env = !(#current ctx)
    val env = extend env x1
    val () = #current ctx := env
  in
    x1
  end
fun visit_outer visit_'t (ctx : 'env ctx) t1 = visit_'t (#outer ctx) t1
fun visit_rebind visit_'p (ctx : 'env ctx) p1 = visit_'p {outer = !(#current ctx), current = #current ctx} p1
    
fun visit_inner visit_'t = visit_rebind (visit_outer visit_'t)
fun visit_bind visit_'p visit_'t = visit_abs (visit_pair visit_'p (visit_inner visit_'t))
                                             
fun visit_bind_simp extend visit_'t = visit_bind (visit_binder extend) visit_'t
fun visit_bind_anno extend visit_'anno visit_'t = visit_bind (visit_pair (visit_binder extend) (visit_outer visit_'anno)) visit_'t

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
