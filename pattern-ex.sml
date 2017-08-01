(* signature BINDER_VISITOR = sig *)
(*   structure Binders : BINDERS *)
(*   val visit_bind_anno : ('env -> 'anno -> 'anno2) -> ('env -> 't -> 't2) -> ('env -> 'name -> 'env) -> 'env -> ('name, 'anno, 't) Binders.bind_anno -> ('name, 'anno2, 't2) Binders.bind_anno         *)
(* end *)
                             
structure PatternEx = struct

open Operators
open Util
       
open Region
type name = string * region
open Namespaces
open Binders
open Unbound

val IName = fn s => IName (s, dummy)
       
infixr 0 $
infix 0 !!

type inj = int * int
             
(* datatype ptrn_un_op = *)
(*          PnUOInj of inj *)
(*          | PnUOUnfold *)
             
datatype ('mtype, 'expr) ptrn =
         PnVar of ename binder
         | PnTT of region outer
         | PnPair of ('mtype, 'expr) ptrn * ('mtype, 'expr) ptrn
         | PnAlias of ename binder * ('mtype, 'expr) ptrn * region outer
	 | PnConstr of inj outer * iname binder list * ('mtype, 'expr) ptrn * region outer
         | PnAnno of ('mtype, 'expr) ptrn * 'mtype outer
         (* | PnUnOp of ptrn_un_op outer * ('mtype, 'expr) ptrn *)
         | PnInj of inj outer * ('mtype, 'expr) ptrn
         | PnUnfold of ('mtype, 'expr) ptrn
         | PnUnpackI of iname binder * ('mtype, 'expr) ptrn
         | PnExpr of 'expr inner
         | PnWildcard

fun from_TiML_ptrn p =
  let
    open Pattern
    val f = from_TiML_ptrn
  in
    case p of
        VarP name => PnVar name
      | TTP r => PnTT r
      | PairP (p1, p2) => PnPair (f p1, f p2)
      | AnnoP (p, t) => PnAnno (f p, t)
      | AliasP (name, p, r) => PnAlias (name, f p, r)
      | ConstrP (Outer ((_, inj), _), inames, p, r) => PnConstr (Outer inj, inames, f p, r)
  end

local
  fun get_name (Binder (_, (name, _))) = name
in
fun str_pn p =
  case p of
      PnVar name => sprintf "PnVar $" [get_name name]
    | PnTT _ => "PnTT"
    | PnPair (p1, p2) => sprintf "PnPair ($, $)" [str_pn p1, str_pn p2]
    | PnAlias (name, p, _) => sprintf "PnAlias ($, $)" [get_name name, str_pn p]
    | PnConstr (Outer inj, names, p, _) => sprintf "PnConstr ($, $, $)" [str_pair (str_int, str_int) inj, str_ls get_name names, str_pn p]
    | PnAnno (p, _) => sprintf "PnAnno ($, <mtype>)" [str_pn p]
    | PnInj (Outer inj, p) => sprintf "PnInj ($, $)" [str_pair (str_int, str_int) inj, str_pn p]
    | PnUnfold p => sprintf "PnUnfold ($)" [str_pn p]
    | PnUnpackI (name, p) => sprintf "PnUnpackI ($, $)" [get_name name, str_pn p]
    | PnExpr _ => "PnExpr <expr>"
    | PnWildcard => "PnWildcard"
end

(* fun PnInj (inj, p) = PnUnOp (PnUOInj inj, p) *)
(* fun PnInl p = PnInj (true, p) *)
(* fun PnInr p = PnInj (false, p) *)
(* fun PnUnfold p = PnUnOp (PnUOUnfold, p) *)

type ('this, 'env, 'mtype, 'expr, 'mtype2, 'expr2) ptrn_visitor_vtable =
     {
       visit_ptrn : 'this -> 'env ctx -> ('mtype, 'expr) ptrn -> ('mtype2, 'expr2) ptrn,
       visit_PnVar : 'this -> 'env ctx -> ename binder -> ('mtype2, 'expr2) ptrn,
       visit_PnTT : 'this -> 'env ctx -> region outer -> ('mtype2, 'expr2) ptrn,
       visit_PnPair : 'this -> 'env ctx -> ('mtype, 'expr) ptrn * ('mtype, 'expr) ptrn -> ('mtype2, 'expr2) ptrn,
       visit_PnAlias : 'this -> 'env ctx -> ename binder * ('mtype, 'expr) ptrn * region outer -> ('mtype2, 'expr2) ptrn,
       visit_PnConstr : 'this -> 'env ctx -> inj outer * iname binder list * ('mtype, 'expr) ptrn * region outer -> ('mtype2, 'expr2) ptrn,
       visit_PnAnno : 'this -> 'env ctx -> ('mtype, 'expr) ptrn * 'mtype outer -> ('mtype2, 'expr2) ptrn,
       (* visit_PnUnOp : 'this -> 'env ctx -> ptrn_un_op outer * ('mtype, 'expr) ptrn -> ('mtype2, 'expr2) ptrn, *)
       visit_PnUnpackI : 'this -> 'env ctx -> iname binder * ('mtype, 'expr) ptrn -> ('mtype2, 'expr2) ptrn,
       visit_PnInj : 'this -> 'env ctx -> inj outer * ('mtype, 'expr) ptrn -> ('mtype2, 'expr2) ptrn,
       visit_PnExpr : 'this -> 'env ctx -> 'expr inner -> ('mtype2, 'expr2) ptrn,
       visit_PnUnfold : 'this -> 'env ctx -> ('mtype, 'expr) ptrn -> ('mtype2, 'expr2) ptrn,
       visit_expr : 'this -> 'env -> 'expr -> 'expr2,
       visit_mtype : 'this -> 'env -> 'mtype -> 'mtype2,
       visit_region : 'this -> 'env -> region -> region,
       visit_inj : 'this -> 'env -> inj -> inj,
       visit_ibinder : 'this -> 'env ctx -> iname binder -> iname binder,
       visit_ebinder : 'this -> 'env ctx -> ename binder -> ename binder,
       extend_i : 'this -> 'env -> iname -> 'env,
       extend_e : 'this -> 'env -> ename -> 'env
     }
       
type ('this, 'env, 'mtype, 'expr, 'mtype2, 'expr2) ptrn_visitor_interface =
     ('this, 'env, 'mtype, 'expr, 'mtype2, 'expr2) ptrn_visitor_vtable
                                       
fun override_visit_PnVar (record : ('this, 'env, 'mtype, 'expr, 'mtype2, 'expr2) ptrn_visitor_vtable) new : ('this, 'env, 'mtype, 'expr, 'mtype2, 'expr2) ptrn_visitor_vtable =
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

fun override_visit_PnPair (record : ('this, 'env, 'mtype, 'expr, 'mtype2, 'expr2) ptrn_visitor_vtable) new : ('this, 'env, 'mtype, 'expr, 'mtype2, 'expr2) ptrn_visitor_vtable =
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

fun override_visit_PnAnno (record : ('this, 'env, 'mtype, 'expr, 'mtype2, 'expr2) ptrn_visitor_vtable) new : ('this, 'env, 'mtype, 'expr, 'mtype2, 'expr2) ptrn_visitor_vtable =
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

fun override_visit_PnConstr (record : ('this, 'env, 'mtype, 'expr, 'mtype2, 'expr2) ptrn_visitor_vtable) new : ('this, 'env, 'mtype, 'expr, 'mtype2, 'expr2) ptrn_visitor_vtable =
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
      (cast : 'this -> ('this, 'env, 'mtype, 'expr, 'mtype2, 'expr2) ptrn_visitor_interface)
      extend_i
      extend_e
      visit_expr
      visit_mtype
    : ('this, 'env, 'mtype, 'expr, 'mtype2, 'expr2) ptrn_visitor_vtable =
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
    
fun shift_i_pn_fn shift_e shift_mt x n b =
  let
    val visitor as (PtrnVisitor vtable) = new_shift_i_ptrn_visitor (shift_e, shift_mt, n)
  in
    #visit_ptrn vtable visitor (env2ctx x) b
  end
    
(***************** the "shift_e_pn" visitor  **********************)    
    
fun shift_e_ptrn_visitor_vtable cast (shift_e, n) : ('this, int, 'mtype, 'expr, 'mtype, 'expr2) ptrn_visitor_vtable =
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
      visit_noop
  end

fun new_shift_e_ptrn_visitor params = new_ptrn_visitor shift_e_ptrn_visitor_vtable params
    
fun shift_e_pn_fn shift_e x n b =
  let
    val visitor as (PtrnVisitor vtable) = new_shift_e_ptrn_visitor (shift_e, n)
  in
    #visit_ptrn vtable visitor (env2ctx x) b
  end
    
(***************** the "subst_e_pn" visitor  **********************)    

fun subst_e_ptrn_visitor_vtable cast (subst_e, d, x, v) : ('this, idepth * tdepth * edepth, 'mtype, 'expr, 'mtype, 'expr2) ptrn_visitor_vtable =
  let
    fun extend_i this (di, dt, de) _ = (idepth_inc di, dt, de)
    fun extend_e this (di, dt, de) _ = (di, dt, edepth_inc de)
    fun add_depth (di, dt, de) (di', dt', de') = (idepth_add (di, di'), tdepth_add (dt, dt'), edepth_add (de, de'))
    fun get_di (di, dt, de) = di
    fun get_dt (di, dt, de) = dt
    fun get_de (di, dt, de) = de
    fun visit_expr this env b = subst_e (add_depth d env) (x + unEDepth (get_de env)) v b
  in
    default_ptrn_visitor_vtable
      cast
      extend_i
      extend_e
      visit_expr
      visit_noop
  end

fun new_subst_e_ptrn_visitor params = new_ptrn_visitor subst_e_ptrn_visitor_vtable params
    
fun visit_subst_e_pn_fn subst_e env d x v b =
  let
    val visitor as (PtrnVisitor vtable) = new_subst_e_ptrn_visitor (subst_e, d, x, v)
  in
    #visit_ptrn vtable visitor env b
  end

fun subst_e_pn_fn subst_e = visit_subst_e_pn_fn subst_e (env2ctx (IDepth 0, TDepth 0, EDepth 0))
fun substx_e_pn_fn subst_e = subst_e_pn_fn subst_e (IDepth 0, TDepth 0, EDepth 0) 
fun subst0_e_pn_fn subst_e = substx_e_pn_fn subst_e 0

(***************** the "remove_anno" visitor  **********************)    
    
fun remove_anno_ptrn_visitor_vtable cast ()
    : ('this, 'env, 'mtype, 'expr, 'mtype2, 'expr) ptrn_visitor_vtable =
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
    #visit_ptrn vtable visitor (env2ctx ()) p
  end
    
(***************** the "remove_var" visitor  **********************)    
    
fun remove_var_ptrn_visitor_vtable cast ()
    : ('this, 'env, 'expr, 'mtype, 'expr, 'mtype) ptrn_visitor_vtable =
  let
    fun visit_PnVar this env data =
      PnAlias (data, PnWildcard, Outer dummy)
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
    #visit_ptrn vtable visitor (env2ctx ()) p
  end
    
(***************** the "remove_constr" visitor  **********************)    

fun unop_ref f r = r := f (!r)
                             
fun shift_imposs msg _ _ _ = raise Impossible msg

fun PnUnpackIMany (names, p) = foldr PnUnpackI p names
                                    
fun remove_constr_ptrn_visitor_vtable (cast : 'this -> ('this, ('mtype, 'expr) ptrn ref, 'mtype, 'expr, 'mtype2, 'expr) ptrn_visitor_interface) shift_i_e
    : ('this, ('mtype, 'expr) ptrn ref, 'mtype, 'expr, 'mtype2, 'expr) ptrn_visitor_vtable =
  let
    fun shift_i p = shift_i_pn_fn shift_i_e (shift_imposs "remove_constr/shift_i_mt()") 0 1 p
    fun visit_PnConstr this (env : ('mtype, 'expr) ptrn ref ctx) data =
      let
        val vtable = cast this
        val (Outer x, inames, p, r) = data
        val p = shift_i p
        val () = unop_ref shift_i $ #outer env
        val p = #visit_ptrn vtable this env p
        val extra_name = "__VC"
        val p = PnUnpackI (Binder $ IName extra_name, p)
        val p = PnUnpackIMany (inames, p)
        fun PnInl p = PnInj (Outer (2, 0), p)
        fun PnInr p = PnInj (Outer (2, 1), p)
        fun BinPnInj (Outer (n, x), p) = self_compose x PnInr $ (if x = n - 1 then p else PnInl p)
        val p = BinPnInj (Outer x, p)
        val p = PnUnfold p
      in
        p
      end
    fun visit_PnPair this (env : ('mtype, 'expr) ptrn ref ctx) data = 
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
    val p = #visit_ptrn vtable visitor (env2ctx env) p
    val pk = !env
  in
    (p, pk)
  end

fun remove_constr shift_i_e p = fst $ remove_constr_k shift_i_e (p, PnTT $ Outer dummy) 
    
(***************** the "remove_deep" visitor  **********************)    

fun get_pn_alias p =
  case p of
      PnAlias (Binder name, _, _) => SOME name
    | PnVar (Binder name) => SOME name
    | PnAnno (p, _) => get_pn_alias p
    | _ => NONE
             
open MicroTiMLEx
       
fun remove_deep_many fresh_name (params as (shift_i_e, shift_e_e, subst_e_e, EV)) matchees pks =
  let
    fun shift_e_pn a = shift_e_pn_fn shift_e_e a
    fun subst0_e_pn a = subst0_e_pn_fn subst_e_e a
    val remove_deep_many = remove_deep_many fresh_name params
    fun remove_top_aliases e p =
      case p of
          PnPair (p1, pk) =>
          (case p1 of
               PnAlias (_, p1, _) => remove_top_aliases e $ subst0_e_pn e (PnPair (p1, pk))
             | _ => p
          )
        | _ => p
    (* fun get_top_alias p = *)
    (*   case p of *)
    (*       PnPair (p, _) => get_pn_alias p *)
    (*     | _ => NONE *)
    val get_alias = firstSuccess get_pn_alias
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
        | PnInj (Outer (n, _), _) => SOME $ ShInj n
        | PnUnfold _ => SOME ShUnfold
        | PnUnpackI (Binder iname, _) => SOME $ ShUnpackI iname
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
                PnInj (Outer (n', i), p) =>
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
    (* val () = println $ "before " ^ str_int (length matchees) *)
    val result =
        case matchees of
            [] =>
            (case pks of
                 [PnExpr (Rebind (Outer e))] => e
               | _ => raise Impossible "remove_deep_many()"
            )
          | matchee :: matchees =>
            let
              (* val () = app (fn p => println $ str_pn p) pks *)
              val pks = map (remove_top_aliases matchee) pks
              (* val () = app (fn p => println $ str_pn p) pks *)
              val () = assert (fn () => isNone $ get_alias pks) "get_alias pks = NONE"
              (* val () = println "before" *)
              val (pns, pks') = split_first_column pks
              (* val () = println "after" *)
            in
              case is_all_Wildcard pns of
                  NONE => remove_deep_many matchees pks'
                | SOME shape =>
                  case shape of
                      ShTT =>
                      let
                        val () = is_all_TT pns
                      in
                        remove_deep_many matchees pks'
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
                        EMatchPair (matchee, BindSimp (ename1, BindSimp (ename2, remove_deep_many (EV 1 :: EV 0 :: matchees) (add_column pns1 $ add_column pns2 pks))))
                      end
                    | ShInj n =>
                      let
                        val matchees = map (shift_e_e 0 1) matchees
                        val pks = map (shift_e_pn 0 1) pks
                        val pn_groups = group_inj n pks
                        val cases = map (remove_deep_many (EV 0 :: matchees)) $ pn_groups
                        val enames = map (lazy_default fresh_name o get_alias) pn_groups
                      in
                        EMatchSum (matchee, map BindSimp $ zip (enames, cases))
                      end
                    | ShUnfold =>
                      let
                        val matchees = map (shift_e_e 0 1) matchees
                        val pks = map (shift_e_pn 0 1) pks
                        val (pns, pks) = split_first_column pks
                        val pns = is_all_Unfold pns
                        val ename = lazy_default fresh_name $ get_alias pns
                      in
                        EMatchUnfold (matchee, BindSimp (ename, remove_deep_many (EV 0 :: matchees) (add_column pns pks)))
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
                        EUnpackI (matchee, BindSimp (iname, BindSimp (ename, remove_deep_many (EV 0 :: matchees) (add_column pns pks))))
                      end
            end
    (* val () = println $ "after " ^ str_int (length matchees) *)
  in
    result
  end

fun get_and_inc r =
  let
    val v = !r
    val () = r := v + 1
  in
    v
  end
    
fun PnBind (p, e) = PnPair (p, PnExpr $ Inner e)
                           
fun remove_deep params matchee =
  let
    val counter = ref 0
    val EName = fn s => EName (s, dummy)
    fun fresh_name () = EName $ prefix "__x" $ str_int $ get_and_inc counter
  in
    remove_deep_many fresh_name params [matchee]
  end
  
fun to_expr (shift_i_e, shift_e_e, subst_e_e, EV) matchee branches : ('var, 'idx, 'sort, 'kind, 'ty) expr =
  let
    val branches = map remove_anno branches
    val branches = map (remove_constr shift_i_e) branches
    val branches = map remove_var branches
    val e = remove_deep (shift_i_e, shift_e_e, subst_e_e, EV) matchee branches
  in
    e
  end

end

structure PatternExUnitTest = struct
open Util
open PatternEx

infixr 0 $
         
val shift_var = ShiftUtil.shiftx_int  
fun compare_var y x =
  let
    open MicroTiMLEx
  in
    if y = x then CmpEq
    else if y > x then
      CmpGreater (y - 1)
    else CmpOther
  end
    
fun test () =
  let
    open Expr
    open MicroTiMLEx
    open Subst
           
    fun shift_i_e a = shift_i_e_fn (shiftx_i_i, shiftx_i_s, shiftx_i_mt) a
                                      
    val IName = fn s => IName (s, dummy)
                              
    fun IVar n = VarI (ID (n, dummy))
    val dummy = Outer dummy
                      
    val p = PnAnno (PnPair (PnAnno (PnTT dummy, Outer ()), PnAnno (PnTT dummy, Outer ())), Outer ())
    val p1 = remove_anno p
    val p2 = PnConstr (Outer (5,1), [Binder $ IName "a", Binder $ IName "b"], PnPair (PnTT dummy, PnExpr $ Inner (EAppI (EVar 0, IVar 2))), dummy)
    val p3 = remove_constr shift_i_e p2
    val p4 = PnPair (PnConstr (Outer (5,1), [Binder $ IName "a", Binder $ IName "b"], PnTT dummy, dummy), PnExpr $ Inner (EAppI (EVar 0, IVar 2)))
    val p5 = remove_constr shift_i_e p4
  in
    (p, p1, p3, p5)
  end
    
fun test2 () =
  let
    open Expr
    open Subst
    fun IVar n = VarI (ID (n, dummy))
                      
    open MicroTiMLEx
    open MicroTiMLExPP
           
    val IName = fn s => IName (s, dummy)
    val EName = fn s => EName (s, dummy)
    fun EV n = EVar n
    val dummy = Outer dummy

    fun shift_i_e a = shift_i_e_fn (shiftx_i_i, shiftx_i_s, shiftx_i_mt) a
    fun shift_e_e a = shift_e_e_fn shift_var a
    fun subst_e_e a = subst_e_e_fn (compare_var, shift_var, shiftx_i_i, shiftx_i_s, shiftx_i_mt, shiftx_t_mt) a
                                      
    val branches =
        [
          (PnConstr (Outer (2, 0), [], PnTT dummy, dummy), EAppI (EV 0, IVar 0)),
          (PnConstr (Outer (2, 1), [Binder $ IName "n"], PnPair (PnVar $ Binder $ EName "x", PnVar $ Binder $ EName "xs"), dummy), EAppI (EV 2, IVar 0))
        ]
    val branches = map PnBind branches
    val e = to_expr (shift_i_e, shift_e_e, subst_e_e, EV) (EV 0) branches
    open ToStringRaw
    open ToString
    val pp_e = pp_e_fn (str_int, str_raw_i, str_raw_s, str_raw_k, str_raw_mt)
    val () = pp_e e
                  
    (* val branches = map remove_anno branches *)
    (* val branches = map (remove_constr shift_i_e) branches *)
    (* (* val () = app (fn p => println $ PatternEx.str_pn p) branches *) *)
    (* val branches = map remove_var branches *)
    (* val e = remove_deep (shift_var, compare_var) (EV 0) branches *)
    (* (* val () = println $ str_e str_int str_raw_i e *) *)
    (* val () = pp_e str_int str_raw_i e *)
  in
    ()
  end
  (* handle Util.Impossible msg => (Util.println ("Impossible: " ^ msg); raise Impossible "") *)
                                  
end
