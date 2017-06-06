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
         TyVisitor of (('env, 'expr, 'mtype, 'expr2, 'mtype2) ptrn_visitor, 'env, 'expr, 'mtype, 'expr2, 'mtype2) ptrn_visitor_interface

fun ptrn_visitor_impls_interface (this : ('env, 'expr, 'mtype, 'expr2, 'mtype2) ptrn_visitor) :
    (('env, 'expr, 'mtype, 'expr2, 'mtype2) ptrn_visitor, 'env, 'expr, 'mtype, 'expr2, 'mtype2) ptrn_visitor_interface =
  let
    val TyVisitor vtable = this
  in
    vtable
  end

fun new_ptrn_visitor vtable params =
  let
    val vtable = vtable ptrn_visitor_impls_interface params
  in
    TyVisitor vtable
  end
    
(***************** the "shift_i_t" visitor  **********************)    
    
fun shift_i_ptrn_visitor_vtable cast (shift_e, shift_mt, n) : ('this, int, 'expr, 'mtype, 'expr, 'mtype2) ptrn_visitor_vtable =
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
    val visitor as (TyVisitor vtable) = new_shift_i_ptrn_visitor (shift_e, shift_mt, n)
  in
    #visit_ptrn vtable visitor (env2ctx x) b
  end
    
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
    val visitor as (TyVisitor vtable) = new_remove_anno_ptrn_visitor ()
  in
    #visit_ptrn vtable visitor (env2ctx ()) p
  end
    
(***************** the "remove_constr" visitor  **********************)    

fun shift_imposs msg _ _ _ = raise Impossible msg

fun PnUnpackIMany (names, p) = foldr PnUnpackI p names
                                    
fun remove_constr_ptrn_visitor_vtable cast shift_i_e
    : ('this, 'env, 'expr, 'mtype, 'expr, 'mtype2) ptrn_visitor_vtable =
  let
    fun visit_PnConstr this env data =
      let
        val vtable = cast this
        val (x, inames, p, r) = data
        val p = shift_i_pn shift_i_e (shift_imposs "remove_constr/shift_i_mt()") 0 1 p
        val p = #visit_ptrn vtable this env p
        val p = PnUnpackI (IName "__datatype_constraint", p)
        val p = PnUnpackIMany (inames, p)
        val p = PnUnfold p
        val p = PnInj (x, p)
      in
        p
      end
    val vtable =
        default_ptrn_visitor_vtable
          cast
          extend_noop
          extend_noop
          visit_noop
          (visit_imposs "remove_constr_ptrn_visitor_vtable/visit_mtype()")
    val vtable = override_visit_PnConstr vtable visit_PnConstr
  in
    vtable
  end

fun new_remove_constr_ptrn_visitor params = new_ptrn_visitor remove_constr_ptrn_visitor_vtable params
    
fun remove_constr shift_i_e p =
  let
    val visitor as (TyVisitor vtable) = new_remove_constr_ptrn_visitor shift_i_e
  in
    #visit_ptrn vtable visitor (env2ctx ()) p
  end

(***************** the "remove_deep" visitor  **********************)    
    
(* fun remove_deep matchees patterns_and_expr_list = *)
(*   case matchees of *)
(*       [] => *)
(*       (case patterns_and_expr_list of *)
(*            [([], e)] => e *)
(*          | _ => raise Impossible "" *)
(*       ) *)
(*     | matchee :: matchees => *)
(*       let *)
(*         val patterns_and_expr_list = remove_alias matchee patterns_and_expr_list *)
(*         val (pns, patterns_and_expr_list) = get_first_column patterns_and_expr_list *)
(*       in *)
(*         case all_wildcard pns of *)
(*             NONE => remove_deep matchees patterns_and_expr_list *)
(*           | SOME shape => *)
(*             (case shape of *)
(*               ShPair => *)
(*               let *)
(*                 val (pns1, pns2) = split_pair pns *)
(*                 val _ = do_some_shifts *)
(*               in *)
(*                 EMatchPair (matchee, remove_deep (Var 1 :: Var 0 :: matchees) (pns1 :: pns2 :: patterns_and_expr_list)) *)
(*               end *)
(*             | ShInj n =>  *)
(*               let *)
(*                 val pn_groups = group_inj n $ zip (pns, patterns_and_expr_list) *)
(*                 val _ = do_some_shifts *)
(*                 val cases = map (fn pael => remove_deep (Var 0 :: matchees) pael) $ pn_groups *)
(*               in *)
(*                 EMatchSum (matchee, cases) *)
(*               end *)
(*       end *)
        
end

structure PatternVisitorFnUnitTest = struct
open Util
open MicroTiML
open Expr
open Subst
(* type iname = string *)
(* type ename = string *)
val IName = fn s => IName (s, dummy)
                          
structure Visitor = PatternVisitorFn (type iname = iname
                                      type ename = ename
                                      val IName = IName
                                     )
open Visitor

fun test () =
  let
    val p = PnAnno (PnPair (PnAnno (PnTT dummy, ()), PnAnno (PnTT dummy, ())), ())
    val p1 = remove_anno p
    fun EVar n = Var ((NONE, (n, dummy)), false)
    fun IVar n = VarI (NONE, (n, dummy))
    val p2 = PnConstr ((5,1), [IName "a", IName "b"], PnPair (PnTT dummy, (* PnExpr (AppI (EVar 0, IVar 2)) *)PnTT dummy), dummy)
    val p3 = remove_constr (* shiftx_i_e *)return3 p2
  in
    (p, p1, p3)
  end
    
end
