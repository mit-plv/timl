(* signature BINDER_VISITOR = sig *)
(*   structure Binders : BINDERS *)
(*   val visit_bind_anno : ('env -> 'anno -> 'anno2) -> ('env -> 't -> 't2) -> ('env -> 'name -> 'env) -> 'env -> ('name, 'anno, 't) Binders.bind_anno -> ('name, 'anno2, 't2) Binders.bind_anno         *)
(* end *)
                             
functor PatternVisitorFn (type iname
                          type ename
                          val IName : string -> iname
                         ) = struct

open Util
open Operators
open Region
open Unbound
       
type tname = unit
structure Binders = BinderUtilFn (structure Binders = Unbound
                                  type iname = iname
                                  type tname = tname
                                  type ename = ename
                                 )
open Binders
       
infixr 0 $
infix 0 !!

type inj = int * int
             
(* datatype ptrn_un_op = *)
(*          PnUOInj of inj *)
(*          | PnUOUnfold *)
             
datatype ('expr, 'mtype) ptrn =
         PnVar of ename binder
         | PnTT of region outer
         | PnPair of ('expr, 'mtype) ptrn * ('expr, 'mtype) ptrn
         | PnAlias of ename binder * ('expr, 'mtype) ptrn * region outer
	 | PnConstr of inj outer * iname binder list * ('expr, 'mtype) ptrn * region outer
         | PnAnno of ('expr, 'mtype) ptrn * 'mtype outer
         (* | PnUnOp of ptrn_un_op outer * ('expr, 'mtype) ptrn *)
         | PnInj of inj outer * ('expr, 'mtype) ptrn
         | PnUnfold of ('expr, 'mtype) ptrn
         | PnUnpackI of iname binder * ('expr, 'mtype) ptrn
         | PnExpr of 'expr inner
         | PnWildcard

(* fun PnInj (inj, p) = PnUnOp (PnUOInj inj, p) *)
(* fun PnInl p = PnInj (true, p) *)
(* fun PnInr p = PnInj (false, p) *)
(* fun PnUnfold p = PnUnOp (PnUOUnfold, p) *)

type ('this, 'env, 'expr, 'mtype, 'expr2, 'mtype2) ptrn_visitor_vtable =
     {
       visit_ptrn : 'this -> 'env ctx -> ('expr, 'mtype) ptrn -> ('expr2, 'mtype2) ptrn,
       visit_PnVar : 'this -> 'env ctx -> ename binder -> ('expr2, 'mtype2) ptrn,
       visit_PnTT : 'this -> 'env ctx -> region outer -> ('expr2, 'mtype2) ptrn,
       visit_PnPair : 'this -> 'env ctx -> ('expr, 'mtype) ptrn * ('expr, 'mtype) ptrn -> ('expr2, 'mtype2) ptrn,
       visit_PnAlias : 'this -> 'env ctx -> ename binder * ('expr, 'mtype) ptrn * region outer -> ('expr2, 'mtype2) ptrn,
       visit_PnConstr : 'this -> 'env ctx -> inj outer * iname binder list * ('expr, 'mtype) ptrn * region outer -> ('expr2, 'mtype2) ptrn,
       visit_PnAnno : 'this -> 'env ctx -> ('expr, 'mtype) ptrn * 'mtype outer -> ('expr2, 'mtype2) ptrn,
       (* visit_PnUnOp : 'this -> 'env ctx -> ptrn_un_op outer * ('expr, 'mtype) ptrn -> ('expr2, 'mtype2) ptrn, *)
       visit_PnUnpackI : 'this -> 'env ctx -> iname binder * ('expr, 'mtype) ptrn -> ('expr2, 'mtype2) ptrn,
       visit_PnInj : 'this -> 'env ctx -> inj outer * ('expr, 'mtype) ptrn -> ('expr2, 'mtype2) ptrn,
       visit_PnExpr : 'this -> 'env ctx -> 'expr inner -> ('expr2, 'mtype2) ptrn,
       visit_PnUnfold : 'this -> 'env ctx -> ('expr, 'mtype) ptrn -> ('expr2, 'mtype2) ptrn,
       visit_expr : 'this -> 'env -> 'expr -> 'expr2,
       visit_mtype : 'this -> 'env -> 'mtype -> 'mtype2,
       visit_region : 'this -> 'env -> region -> region,
       visit_inj : 'this -> 'env -> inj -> inj,
       visit_ibinder : 'this -> 'env ctx -> iname binder -> iname binder,
       visit_ebinder : 'this -> 'env ctx -> ename binder -> ename binder,
       extend_i : 'this -> 'env -> iname -> 'env,
       extend_e : 'this -> 'env -> ename -> 'env
     }
       
type ('this, 'env, 'expr, 'mtype, 'expr2, 'mtype2) ptrn_visitor_interface =
     ('this, 'env, 'expr, 'mtype, 'expr2, 'mtype2) ptrn_visitor_vtable
                                       
fun override_visit_PnVar (record : ('this, 'env, 'expr, 'mtype, 'expr2, 'mtype2) ptrn_visitor_vtable) new : ('this, 'env, 'expr, 'mtype, 'expr2, 'mtype2) ptrn_visitor_vtable =
  {
    visit_ptrn = #visit_ptrn record,
    visit_PnPair = #visit_PnPair record,
    visit_PnTT = #visit_PnTT record,
    visit_PnAnno = #visit_PnAnno record,
    visit_PnAlias = #visit_PnAlias record,
    visit_PnVar = new,
    visit_PnConstr = #visit_PnConstr record,
    visit_PnInj = #visit_PnInj record,
    visit_PnUnfold = #visit_PnUnfold record,
    visit_PnUnpackI = #visit_PnUnpackI record,
    visit_PnExpr = #visit_PnExpr record,
    visit_expr = #visit_expr record,
    visit_mtype = #visit_mtype record,
    visit_region = #visit_region record,
    visit_inj = #visit_inj record,
    visit_ibinder = #visit_ibinder record,
    visit_ebinder = #visit_ebinder record,
    extend_i = #extend_i record,
    extend_e = #extend_e record
  }

fun override_visit_PnPair (record : ('this, 'env, 'expr, 'mtype, 'expr2, 'mtype2) ptrn_visitor_vtable) new : ('this, 'env, 'expr, 'mtype, 'expr2, 'mtype2) ptrn_visitor_vtable =
  {
    visit_ptrn = #visit_ptrn record,
    visit_PnVar = #visit_PnVar record,
    visit_PnTT = #visit_PnTT record,
    visit_PnAnno = #visit_PnAnno record,
    visit_PnAlias = #visit_PnAlias record,
    visit_PnPair = new,
    visit_PnConstr = #visit_PnConstr record,
    visit_PnInj = #visit_PnInj record,
    visit_PnUnfold = #visit_PnUnfold record,
    visit_PnUnpackI = #visit_PnUnpackI record,
    visit_PnExpr = #visit_PnExpr record,
    visit_expr = #visit_expr record,
    visit_mtype = #visit_mtype record,
    visit_region = #visit_region record,
    visit_inj = #visit_inj record,
    visit_ibinder = #visit_ibinder record,
    visit_ebinder = #visit_ebinder record,
    extend_i = #extend_i record,
    extend_e = #extend_e record
  }

fun override_visit_PnAnno (record : ('this, 'env, 'expr, 'mtype, 'expr2, 'mtype2) ptrn_visitor_vtable) new : ('this, 'env, 'expr, 'mtype, 'expr2, 'mtype2) ptrn_visitor_vtable =
  {
    visit_ptrn = #visit_ptrn record,
    visit_PnVar = #visit_PnVar record,
    visit_PnTT = #visit_PnTT record,
    visit_PnPair = #visit_PnPair record,
    visit_PnAlias = #visit_PnAlias record,
    visit_PnAnno = new,
    visit_PnConstr = #visit_PnConstr record,
    visit_PnInj = #visit_PnInj record,
    visit_PnUnfold = #visit_PnUnfold record,
    visit_PnUnpackI = #visit_PnUnpackI record,
    visit_PnExpr = #visit_PnExpr record,
    visit_expr = #visit_expr record,
    visit_mtype = #visit_mtype record,
    visit_region = #visit_region record,
    visit_inj = #visit_inj record,
    visit_ibinder = #visit_ibinder record,
    visit_ebinder = #visit_ebinder record,
    extend_i = #extend_i record,
    extend_e = #extend_e record
  }

fun override_visit_PnConstr (record : ('this, 'env, 'expr, 'mtype, 'expr2, 'mtype2) ptrn_visitor_vtable) new : ('this, 'env, 'expr, 'mtype, 'expr2, 'mtype2) ptrn_visitor_vtable =
  {
    visit_ptrn = #visit_ptrn record,
    visit_PnVar = #visit_PnVar record,
    visit_PnTT = #visit_PnTT record,
    visit_PnPair = #visit_PnPair record,
    visit_PnAlias = #visit_PnAlias record,
    visit_PnConstr = new,
    visit_PnAnno = #visit_PnAnno record,
    visit_PnInj = #visit_PnInj record,
    visit_PnUnfold = #visit_PnUnfold record,
    visit_PnUnpackI = #visit_PnUnpackI record,
    visit_PnExpr = #visit_PnExpr record,
    visit_expr = #visit_expr record,
    visit_mtype = #visit_mtype record,
    visit_region = #visit_region record,
    visit_inj = #visit_inj record,
    visit_ibinder = #visit_ibinder record,
    visit_ebinder = #visit_ebinder record,
    extend_i = #extend_i record,
    extend_e = #extend_e record
  }

(***************** the default visitor  **********************)    

open VisitorUtil
       
fun default_ptrn_visitor_vtable
      (cast : 'this -> ('this, 'env, 'expr, 'mtype, 'expr2, 'mtype2) ptrn_visitor_interface)
      extend_i
      extend_e
      visit_expr
      visit_mtype
    : ('this, 'env, 'expr, 'mtype, 'expr2, 'mtype2) ptrn_visitor_vtable =
  let
    fun visit_ptrn this env data =
      let
        val vtable = cast this
      in
        case data of
            PnVar data => #visit_PnVar vtable this env data
          | PnTT data => #visit_PnTT vtable this env data
          | PnPair data => #visit_PnPair vtable this env data
          | PnAlias data => #visit_PnAlias vtable this env data
          | PnConstr data => #visit_PnConstr vtable this env data
          | PnAnno data => #visit_PnAnno vtable this env data
          (* | PnUnOp data => #visit_PnUnOp vtable this env data *)
          | PnUnpackI data => #visit_PnUnpackI vtable this env data
          | PnInj data => #visit_PnInj vtable this env data
          | PnUnfold data => #visit_PnUnfold vtable this env data
          | PnExpr data => #visit_PnExpr vtable this env data
          | PnWildcard => PnWildcard
      end
    fun visit_PnVar this env data =
      let
        val vtable = cast this
      in
        PnVar $ #visit_ebinder vtable this env data
      end
    fun visit_PnTT this env data =
      let
        val vtable = cast this
      in
        PnTT $ visit_outer (#visit_region vtable this) env data
      end
    fun visit_PnPair this env data = 
      let
        val vtable = cast this
        val (p1, p2) = data
        val p1 = #visit_ptrn vtable this env p1
        val p2 = #visit_ptrn vtable this env p2
      in
        PnPair (p1, p2)
      end
    fun visit_PnAlias this env data =
      let
        val vtable = cast this
        val (name, p, r) = data
        val name = #visit_ebinder vtable this env name
        val p = #visit_ptrn vtable this env p
        val r = visit_outer (#visit_region vtable this) env r
      in
        PnAlias (name, p, r)
      end
    fun visit_PnAnno this env data = 
      let
        val vtable = cast this
        val (p, t) = data
        val p = #visit_ptrn vtable this env p
        val t = visit_outer (#visit_mtype vtable this) env t
      in
        PnAnno (p, t)
      end
    fun visit_PnConstr this env data =
      let
        val vtable = cast this
        val (x, inames, p, r) = data
        val x = visit_outer (#visit_inj vtable this) env x
        val inames = map (#visit_ibinder vtable this env) inames
        val p = #visit_ptrn vtable this env p
        val r = visit_outer (#visit_region vtable this) env r
      in
        PnConstr (x, inames, p, r)
      end
    (* fun visit_PnUnOp this env data =  *)
    (*   let *)
    (*     val vtable = cast this *)
    (*     val (opr, p) = data *)
    (*   in *)
    (*     case opr of *)
    (*         PnUOInj data => #visit_PnInj vtable this env (data, p) *)
    (*       | PnUOUnfold data => #visit_PnUnfold vtable this env p *)
    (*   end *)
    fun visit_PnUnpackI this env data =
      let
        val vtable = cast this
        val (name, p) = data
        val name = #visit_ibinder vtable this env name
        val p = #visit_ptrn vtable this env p
      in
        PnUnpackI (name, p)
      end
    fun visit_PnInj this env data =
      let
        val vtable = cast this
        val (inj, p) = data
        val inj = visit_outer (#visit_inj vtable this) env inj
        val p = #visit_ptrn vtable this env p
      in
        PnInj (inj, p)
      end
    fun visit_PnUnfold this env data =
      let
        val vtable = cast this
        val data = #visit_ptrn vtable this env data
      in
        PnUnfold data
      end
    fun visit_PnExpr this env data =
      let
        val vtable = cast this
        val data = visit_inner (#visit_expr vtable this) env data
      in
        PnExpr data
      end
    fun default_visit_binder extend this = visit_binder (extend this)
  in
    {
      visit_ptrn = visit_ptrn,
      visit_PnVar = visit_PnVar,
      visit_PnTT = visit_PnTT,
      visit_PnPair = visit_PnPair,
      visit_PnAlias = visit_PnAlias,
      visit_PnAnno = visit_PnAnno,
      visit_PnConstr = visit_PnConstr,
      visit_PnInj = visit_PnInj,
      visit_PnUnfold = visit_PnUnfold,
      visit_PnUnpackI = visit_PnUnpackI,
      visit_PnExpr = visit_PnExpr,
      visit_expr = visit_expr,
      visit_mtype = visit_mtype,
      visit_region = visit_noop,
      visit_inj = visit_noop,
      visit_ibinder = default_visit_binder extend_i,
      visit_ebinder = default_visit_binder extend_e,
      extend_i = extend_i,
      extend_e = extend_e
    }
  end

datatype ('env, 'expr, 'mtype, 'expr2, 'mtype2) ptrn_visitor =
         PtrnVisitor of (('env, 'expr, 'mtype, 'expr2, 'mtype2) ptrn_visitor, 'env, 'expr, 'mtype, 'expr2, 'mtype2) ptrn_visitor_interface

fun ptrn_visitor_impls_interface (this : ('env, 'expr, 'mtype, 'expr2, 'mtype2) ptrn_visitor) :
    (('env, 'expr, 'mtype, 'expr2, 'mtype2) ptrn_visitor, 'env, 'expr, 'mtype, 'expr2, 'mtype2) ptrn_visitor_interface =
  let
    val PtrnVisitor vtable = this
  in
    vtable
  end

fun new_ptrn_visitor vtable params =
  let
    val vtable = vtable ptrn_visitor_impls_interface params
  in
    PtrnVisitor vtable
  end
    
(***************** the "shift_i_pn" visitor  **********************)    
    
fun shift_i_ptrn_visitor_vtable cast (shift_e, shift_mt, n) : ('this, int, 'expr, 'mtype, 'expr2, 'mtype2) ptrn_visitor_vtable =
  let
    fun extend_i this env _ = env + 1
    val extend_e = extend_noop
    fun do_shift shift this env b = shift env n b
  in
    default_ptrn_visitor_vtable
      cast
      extend_i
      extend_e
      (do_shift shift_e)
      (do_shift shift_mt)
  end

fun new_shift_i_ptrn_visitor params = new_ptrn_visitor shift_i_ptrn_visitor_vtable params
    
fun shift_i_pn shift_e shift_mt x n b =
  let
    val visitor as (PtrnVisitor vtable) = new_shift_i_ptrn_visitor (shift_e, shift_mt, n)
  in
    visit_abs (#visit_ptrn vtable visitor) x b
  end
    
(***************** the "shift_e_pn" visitor  **********************)    
    
fun shift_e_ptrn_visitor_vtable cast (shift_e, n) : ('this, int, 'expr, 'mtype, 'expr2, 'mtype) ptrn_visitor_vtable =
  let
    val extend_i = extend_noop
    fun extend_e this env _ = env + 1
    fun do_shift shift this env b = shift env n b
  in
    default_ptrn_visitor_vtable
      cast
      extend_i
      extend_e
      (do_shift shift_e)
      return3
  end

fun new_shift_e_ptrn_visitor params = new_ptrn_visitor shift_e_ptrn_visitor_vtable params
    
fun shift_e_pn shift_e x n b =
  let
    val visitor as (PtrnVisitor vtable) = new_shift_e_ptrn_visitor (shift_e, n)
  in
    visit_abs (#visit_ptrn vtable visitor) x b
  end
    
(***************** the "subst_e_pn" visitor  **********************)    

fun mapPair2 f1 f2 (a1, a2) (b1, b2) = (f1 (a1, b1), f2 (a2, b2))
fun add_pair a b = mapPair2 op+ op+ a b
                            
fun subst_e_ptrn_visitor_vtable cast (subst_e, d, x, v) : ('this, int * int, 'expr, 'mtype, 'expr2, 'mtype) ptrn_visitor_vtable =
  let
    fun extend_i this (di, de) _ = (di + 1, de)
    fun extend_e this (di, de) _ = (di, de + 1)
    fun visit_expr this env b = subst_e (add_pair d env) (x + snd env) v b
  in
    default_ptrn_visitor_vtable
      cast
      extend_i
      extend_e
      visit_expr
      return3
  end

fun new_subst_e_ptrn_visitor params = new_ptrn_visitor subst_e_ptrn_visitor_vtable params
    
fun subst_e_pn subst_e d x v b =
  let
    val visitor as (PtrnVisitor vtable) = new_subst_e_ptrn_visitor (subst_e, d, x, v)
  in
    visit_abs (#visit_ptrn vtable visitor) (0, 0) b
  end

fun subst0_e_pn subst_e v b = subst_e_pn subst_e (0, 0) 0 v b

(***************** the "remove_anno" visitor  **********************)    
    
fun remove_anno_ptrn_visitor_vtable cast ()
    : ('this, 'env, 'expr, 'mtype, 'expr, 'mtype2) ptrn_visitor_vtable =
  let
    fun visit_PnAnno this env data = 
      let
        val vtable = cast this
        val (p, t) = data
        val p = #visit_ptrn vtable this env p
      in
        p
      end
    val vtable =
        default_ptrn_visitor_vtable
          cast
          extend_noop
          extend_noop
          visit_noop
          (visit_imposs "remove_anno_ptrn_visitor_vtable/visit_mtype()")
    val vtable = override_visit_PnAnno vtable visit_PnAnno
  in
    vtable
  end

fun new_remove_anno_ptrn_visitor params = new_ptrn_visitor remove_anno_ptrn_visitor_vtable params
    
fun remove_anno p =
  let
    val visitor as (PtrnVisitor vtable) = new_remove_anno_ptrn_visitor ()
  in
    visit_abs (#visit_ptrn vtable visitor) () p
  end
    
(***************** the "remove_var" visitor  **********************)    
    
fun remove_var_ptrn_visitor_vtable cast ()
    : ('this, 'env, 'expr, 'mtype, 'expr, 'mtype) ptrn_visitor_vtable =
  let
    fun visit_PnVar this env data =
      PnAlias (data, PnWildcard, dummy)
    val vtable =
        default_ptrn_visitor_vtable
          cast
          extend_noop
          extend_noop
          visit_noop
          visit_noop
    val vtable = override_visit_PnVar vtable visit_PnVar
  in
    vtable
  end

fun new_remove_var_ptrn_visitor params = new_ptrn_visitor remove_var_ptrn_visitor_vtable params
    
fun remove_var p =
  let
    val visitor as (PtrnVisitor vtable) = new_remove_var_ptrn_visitor ()
  in
    visit_abs (#visit_ptrn vtable visitor) () p
  end
    
(***************** the "remove_constr" visitor  **********************)    

fun unop_ref f r = r := f (!r)
                             
fun shift_imposs msg _ _ _ = raise Impossible msg

fun PnUnpackIMany (names, p) = foldr PnUnpackI p names
                                    
fun remove_constr_ptrn_visitor_vtable cast shift_i_e
    : ('this, ('expr, 'mtype) ptrn ref, 'expr, 'mtype, 'expr, 'mtype2) ptrn_visitor_vtable =
  let
    fun shift_i p = shift_i_pn shift_i_e (shift_imposs "remove_constr/shift_i_mt()") 0 1 p
    fun visit_PnConstr this env data =
      let
        val vtable = cast this
        val (x, inames, p, r) = data
        val p = shift_i p
        val () = unop_ref shift_i $ #outer env
        val p = #visit_ptrn vtable this env p
        val p = PnUnpackI (IName "__datatype_constraint", p)
        val p = PnUnpackIMany (inames, p)
        val p = PnUnfold p
        val p = PnInj (x, p)
      in
        p
      end
    fun visit_PnPair this env data = 
      let
        val vtable = cast this
        val (p1, p2) = data
        val pk = !(#outer env)
        val () = #outer env := PnPair (p2, pk)
        val p1 = #visit_ptrn vtable this env p1
        val (p2, pk) = case !(#outer env) of
                           PnPair a => a
                         | _ => raise Impossible "remove_constr/visit_PnPair()"
        val () = #outer env := pk
        val p2 = #visit_ptrn vtable this env p2
      in
        PnPair (p1, p2)
      end
    val vtable =
        default_ptrn_visitor_vtable
          cast
          extend_noop
          extend_noop
          visit_noop
          (visit_imposs "remove_constr_ptrn_visitor_vtable/visit_mtype()")
    val vtable = override_visit_PnConstr vtable visit_PnConstr
    val vtable = override_visit_PnPair vtable visit_PnPair
  in
    vtable
  end

fun new_remove_constr_ptrn_visitor params = new_ptrn_visitor remove_constr_ptrn_visitor_vtable params

(* with the 'continuation pattern' *)                                                             
fun remove_constr_k shift_i_e (p, pk) =
  let
    val visitor as (PtrnVisitor vtable) = new_remove_constr_ptrn_visitor shift_i_e
    val env = ref pk
    val p = visit_abs (#visit_ptrn vtable visitor) env p
    val pk = !env
  in
    (p, pk)
  end

fun remove_constr shift_i_e p = fst $ remove_constr_k shift_i_e (p, PnTT dummy) 
    
(***************** the "remove_deep" visitor  **********************)    

(* open Expr *)
(* open Subst *)

(* datatype expr = *)
(*          EVar of int *)
(*          | EAppI of expr * idx *)
(*          | EMatchSum of expr * list *)

(* fun shift_i_e x n b = *)
(*   case b of *)
(*       EVar _ => b *)
(*     | EAppI (e, i) => EAppI (shift_i_e x n e, shiftx_i_i x n i) *)

datatype ('var, 'bsort, 'idx, 'sort) expr =
         EVar of 'var
         | EAppI of ('var, 'bsort, 'idx, 'sort) expr * 'idx
         | EMatchSum of ('var, 'bsort, 'idx, 'sort) expr * ('var, 'bsort, 'idx, 'sort) expr ebind list
         | EMatchPair of ('var, 'bsort, 'idx, 'sort) expr * ('var, 'bsort, 'idx, 'sort) expr ebind ebind
         | EMatchUnfold of ('var, 'bsort, 'idx, 'sort) expr * ('var, 'bsort, 'idx, 'sort) expr ebind
         | EMatchUnpackI of ('var, 'bsort, 'idx, 'sort) expr * ('var, 'bsort, 'idx, 'sort) expr ebind ibind

fun shift_e_e x n b = b
fun shift_i_e x n b = b
fun subst_e_e d x v b = b

val shift_e_pn = fn a => shift_e_pn shift_e_e a
val subst0_e_pn = fn a => subst0_e_pn subst_e_e a

val Cons = op::

fun update i f ls = mapi (fn (i', a) => if i' = i then f a else a) ls
             
fun remove_deep fresh_name matchees pks =
  let
    val remove_deep = remove_deep fresh_name
    fun remove_top_aliases e p =
      case p of
          PnPair (p, pk) =>
          (case p of
               PnAlias (_, p, _) => remove_top_aliases e $ subst0_e_pn e (PnPair (p, pk))
             | _ => p
          )
        | _ => p
    local
      fun get_pn_alias p =
        case p of
            PnAlias (name, _, _) => SOME name
          | _ => NONE
    in
    fun get_top_alias p =
      case p of
          PnPair (p, _) => get_pn_alias p
        | _ => NONE
    end
    val get_alias = firstSuccess get_top_alias
    datatype shape =
             ShTT
             | ShPair
             | ShUnfold
             | ShInj of int
             | ShUnpackI of iname
    fun get_shape p =
      case p of
          PnWildcard => NONE
        | PnTT _ => SOME ShTT
        | PnPair _ => SOME ShPair
        | PnInj ((n, _), _) => SOME $ ShInj n
        | PnUnfold _ => SOME ShUnfold
        | PnUnpackI (iname, _) => SOME $ ShUnpackI iname
        | _ => raise Impossible "get_shape()"
    val is_all_Wildcard = firstSuccess get_shape
    fun is_all_TT ps = app (fn p => case p of PnTT _ => () | PnWildcard => () | _ => raise Impossible "is_all_TT()") ps
    fun is_all_Pair ps = unzip $ map (fn p => case p of PnPair p => p | PnWildcard => (PnWildcard, PnWildcard) | _ => raise Impossible "is_all_Pair()") ps
    fun is_all_Unfold ps = map (fn p => case p of PnUnfold p => p | PnWildcard => PnWildcard | _ => raise Impossible "is_all_Unfold()") ps
    fun is_all_UnpackI ps = map (fn p => case p of PnUnpackI (_, p) => p | PnWildcard => PnWildcard | _ => raise Impossible "is_all_UnpackI()") ps
    fun group_inj n ps =
      let
        fun do_group (p, acc) =
          let
            val (p, pk) =
                case p of
                    PnPair data => data
                  | _ => raise Impossible "do_group()/PnPair"
            fun add_to i a ls =
              let
                val () = assert (fn () => i < length ls) ("i < length ls")
              in
                update i (curry Cons a) ls
              end
          in
            case p of
                PnInj ((n', i), p) =>
                let
                  val () = assert (fn () => n' = n) "n' = n"
                  val () = assert (fn () => i < n) "i < n"
                in
                  add_to i (PnPair (p, pk)) acc
                end
              | PnWildcard => map (curry Cons $ PnPair (PnWildcard, pk)) acc
              | _ => raise Impossible "do_group()"
          end
        val groups = map rev $ foldl do_group (repeat n []) ps
      in
        groups
      end
    fun split_first_column ps = unzip $ map (fn p => case p of PnPair p => p | _ => raise Impossible "split_first_column()") ps
    fun add_column ps pks = map PnPair $ zip (ps, pks)
  in
    case matchees of
        [] =>
        (case pks of
             [PnExpr e] => e
           | _ => raise Impossible "remove_deep()"
        )
      | matchee :: matchees =>
        let
          val pks = map (remove_top_aliases matchee) pks
          val () = assert (fn () => isNone $ get_alias pks) "get_alias pks = NONE"
          val (pns, pks') = split_first_column pks
        in
          case is_all_Wildcard pns of
              NONE => remove_deep matchees pks'
            | SOME shape =>
              case shape of
                  ShTT =>
                  let
                    val () = is_all_TT pns
                  in
                    remove_deep matchees pks'
                  end
                | ShPair =>
                  let
                    val matchees = map (shift_e_e 0 2) matchees
                    val pks = map (shift_e_pn 0 2) pks
                    val (pns, pks) = split_first_column pks
                    val (pns1, pns2) = is_all_Pair pns
                    val ename1 = lazy_default fresh_name $ get_alias pns1
                    val ename2 = lazy_default fresh_name $ get_alias pns2
                  in
                    EMatchPair (matchee, (ename1, (ename2, remove_deep (EVar 1 :: EVar 0 :: matchees) (add_column pns1 $ add_column pns2 pks))))
                  end
                | ShInj n =>
                  let
                    val matchees = map (shift_e_e 0 1) matchees
                    val pks = map (shift_e_pn 0 1) pks
                    val pn_groups = group_inj n pks
                    val cases = map (remove_deep (EVar 0 :: matchees)) $ pn_groups
                    val enames = map (lazy_default fresh_name o get_alias) pn_groups
                  in
                    EMatchSum (matchee, zip (enames, cases))
                  end
                | ShUnfold =>
                  let
                    val matchees = map (shift_e_e 0 1) matchees
                    val pks = map (shift_e_pn 0 1) pks
                    val (pns, pks) = split_first_column pks
                    val pns = is_all_Unfold pns
                    val ename = lazy_default fresh_name $ get_alias pns
                  in
                    EMatchUnfold (matchee, (ename, remove_deep (EVar 0 :: matchees) (add_column pns pks)))
                  end
                | ShUnpackI iname =>
                  let
                    val matchees = map (shift_e_e 0 1) matchees
                    val matchees = map (shift_i_e 0 1) matchees
                    val pks = map (shift_e_pn 0 1) pks
                    val (pns, pks) = split_first_column pks
                    val pns = is_all_UnpackI pns
                    val ename = lazy_default fresh_name $ get_alias pns
                  in
                    EMatchUnpackI (matchee, (iname, (ename, remove_deep (EVar 0 :: matchees) (add_column pns pks))))
                  end
        end
  end
        
end

structure PatternVisitorFnUnitTest = struct
open Util
(* open MicroTiML *)
(* val IName = fn s => IName (s, dummy) *)
type iname = string
type ename = string
val IName = id
                          
structure Visitor = PatternVisitorFn (type iname = iname
                                      type ename = ename
                                      val IName = IName
                                     )
open Visitor

open Expr
              
(* fun EVar n = Var ((NONE, (n, dummy)), false) *)
fun IVar n = VarI (NONE, (n, dummy))
                  
fun test () =
  let
    val p = PnAnno (PnPair (PnAnno (PnTT dummy, ()), PnAnno (PnTT dummy, ())), ())
    val p1 = remove_anno p
    val p2 = PnConstr ((5,1), [IName "a", IName "b"], PnPair (PnTT dummy, PnExpr (EAppI (EVar 0, IVar 2))), dummy)
    val p3 = remove_constr shift_i_e p2
    val p4 = PnPair (PnConstr ((5,1), [IName "a", IName "b"], PnTT dummy, dummy), PnExpr (EAppI (EVar 0, IVar 2)))
    val p5 = remove_constr shift_i_e p4
  in
    (p, p1, p3, p5)
  end
    
end
