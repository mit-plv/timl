functor IdxVisitorFn (structure S : IDX
                      structure T : IDX
                      sharing type S.base_sort = T.base_sort
                      sharing type S.name = T.name
                      sharing type S.region = T.region
                     ) = struct

open Unbound
open Namespaces
open Binders
open Operators
open Region
open S

infixr 0 $
       
type ('this, 'env) idx_visitor_vtable =
     {
       visit_bsort : 'this -> 'env -> bsort -> T.bsort,
       visit_Base : 'this -> 'env -> base_sort  -> T.bsort,
       visit_BSArrow : 'this -> 'env -> bsort * bsort -> T.bsort,
       visit_UVarBS : 'this -> 'env -> bsort uvar_bs -> T.bsort,
       visit_idx : 'this -> 'env -> idx -> T.idx,
       visit_VarI : 'this -> 'env -> var -> T.idx,
       visit_IConst : 'this -> 'env -> Operators.idx_const * region -> T.idx,
       visit_UnOpI : 'this -> 'env -> Operators.idx_un_op * idx * region -> T.idx,
       visit_BinOpI : 'this -> 'env -> Operators.idx_bin_op * idx * idx -> T.idx,
       visit_Ite : 'this -> 'env -> idx * idx * idx * region -> T.idx,
       visit_IAbs : 'this -> 'env -> bsort * (name * idx) Bind.ibind * region -> T.idx,
       visit_UVarI : 'this -> 'env -> (bsort, idx) uvar_i * region -> T.idx,
       visit_prop : 'this -> 'env -> prop -> T.prop,
       visit_PTrueFalse : 'this -> 'env -> bool * region -> T.prop,
       visit_BinConn : 'this -> 'env -> Operators.bin_conn * prop * prop -> T.prop,
       visit_Not : 'this -> 'env -> prop * region -> T.prop,
       visit_BinPred : 'this -> 'env -> Operators.bin_pred * idx * idx -> T.prop,
       visit_Quan : 'this -> 'env -> idx exists_anno (*for linking idx inferer with types*) Operators.quan * bsort * (name * prop) Bind.ibind * region -> T.prop,
       visit_sort : 'this -> 'env -> sort -> T.sort,
       visit_Basic : 'this -> 'env -> bsort * region -> T.sort,
       visit_Subset : 'this -> 'env -> (bsort * region) * (name * prop) Bind.ibind * region -> T.sort,
       visit_UVarS : 'this -> 'env -> (bsort, sort) uvar_s * region -> T.sort,
       visit_SAbs : 'this -> 'env -> bsort * (name * sort) Bind.ibind * region -> T.sort,
       visit_SApp : 'this -> 'env -> sort * idx -> T.sort,
       visit_var : 'this -> 'env -> var -> T.var,
       visit_uvar_bs : 'this -> 'env -> bsort uvar_bs -> T.bsort T.uvar_bs,
       visit_uvar_i : 'this -> 'env -> (bsort, idx) uvar_i -> (T.bsort, T.idx) T.uvar_i,
       visit_uvar_s : 'this -> 'env -> (bsort, sort) uvar_s -> (T.bsort, T.sort) T.uvar_s,
       visit_quan : 'this -> 'env -> idx exists_anno quan -> T.idx T.exists_anno quan,
       extend : 'this -> 'env -> name -> 'env
     }
       
fun override_visit_idx (record : ('this, 'env) idx_visitor_vtable) new =
  {
    visit_bsort = #visit_bsort record,
    visit_Base = #visit_Base record,
    visit_BSArrow = #visit_BSArrow record,
    visit_UVarBS = #visit_UVarBS record,
    visit_idx = new,
    visit_VarI = #visit_VarI record,
    visit_IConst = #visit_IConst record,
    visit_UnOpI = #visit_UnOpI record,
    visit_BinOpI = #visit_BinOpI record,
    visit_Ite = #visit_Ite record,
    visit_IAbs = #visit_IAbs record,
    visit_UVarI = #visit_UVarI record,
    visit_prop = #visit_prop record,
    visit_PTrueFalse = #visit_PTrueFalse record,
    visit_BinConn = #visit_BinConn record,
    visit_Not = #visit_Not record,
    visit_BinPred = #visit_BinPred record,
    visit_Quan = #visit_Quan record,
    visit_sort = #visit_sort record,
    visit_Basic = #visit_Basic record,
    visit_Subset = #visit_Subset record,
    visit_UVarS = #visit_UVarS record,
    visit_SAbs = #visit_SAbs record,
    visit_SApp = #visit_SApp record,
    visit_var = #visit_var record,
    visit_uvar_bs = #visit_uvar_bs record,
    visit_uvar_i = #visit_uvar_i record,
    visit_uvar_s = #visit_uvar_s record,
    visit_quan = #visit_quan record,
    extend = #extend record
  }

fun override_visit_UVarBS (record : ('this, 'env) idx_visitor_vtable) new =
  {
    visit_bsort = #visit_bsort record,
    visit_Base = #visit_Base record,
    visit_BSArrow = #visit_BSArrow record,
    visit_UVarBS = new,
    visit_idx = #visit_idx record,
    visit_VarI = #visit_VarI record,
    visit_IConst = #visit_IConst record,
    visit_UnOpI = #visit_UnOpI record,
    visit_BinOpI = #visit_BinOpI record,
    visit_Ite = #visit_Ite record,
    visit_IAbs = #visit_IAbs record,
    visit_UVarI = #visit_UVarI record,
    visit_prop = #visit_prop record,
    visit_PTrueFalse = #visit_PTrueFalse record,
    visit_BinConn = #visit_BinConn record,
    visit_Not = #visit_Not record,
    visit_BinPred = #visit_BinPred record,
    visit_Quan = #visit_Quan record,
    visit_sort = #visit_sort record,
    visit_Basic = #visit_Basic record,
    visit_Subset = #visit_Subset record,
    visit_UVarS = #visit_UVarS record,
    visit_SAbs = #visit_SAbs record,
    visit_SApp = #visit_SApp record,
    visit_var = #visit_var record,
    visit_uvar_bs = #visit_uvar_bs record,
    visit_uvar_i = #visit_uvar_i record,
    visit_uvar_s = #visit_uvar_s record,
    visit_quan = #visit_quan record,
    extend = #extend record
  }

fun override_visit_VarI (record : ('this, 'env) idx_visitor_vtable) new =
  {
    visit_bsort = #visit_bsort record,
    visit_Base = #visit_Base record,
    visit_BSArrow = #visit_BSArrow record,
    visit_UVarBS = #visit_UVarBS record,
    visit_idx = #visit_idx record,
    visit_VarI = new,
    visit_IConst = #visit_IConst record,
    visit_UnOpI = #visit_UnOpI record,
    visit_BinOpI = #visit_BinOpI record,
    visit_Ite = #visit_Ite record,
    visit_IAbs = #visit_IAbs record,
    visit_UVarI = #visit_UVarI record,
    visit_prop = #visit_prop record,
    visit_PTrueFalse = #visit_PTrueFalse record,
    visit_BinConn = #visit_BinConn record,
    visit_Not = #visit_Not record,
    visit_BinPred = #visit_BinPred record,
    visit_Quan = #visit_Quan record,
    visit_sort = #visit_sort record,
    visit_Basic = #visit_Basic record,
    visit_Subset = #visit_Subset record,
    visit_UVarS = #visit_UVarS record,
    visit_SAbs = #visit_SAbs record,
    visit_SApp = #visit_SApp record,
    visit_var = #visit_var record,
    visit_uvar_bs = #visit_uvar_bs record,
    visit_uvar_i = #visit_uvar_i record,
    visit_uvar_s = #visit_uvar_s record,
    visit_quan = #visit_quan record,
    extend = #extend record
  }

fun override_visit_BinOpI (record : ('this, 'env) idx_visitor_vtable) new =
  {
    visit_bsort = #visit_bsort record,
    visit_Base = #visit_Base record,
    visit_BSArrow = #visit_BSArrow record,
    visit_UVarBS = #visit_UVarBS record,
    visit_idx = #visit_idx record,
    visit_VarI = #visit_VarI record,
    visit_IConst = #visit_IConst record,
    visit_UnOpI = #visit_UnOpI record,
    visit_BinOpI = new,
    visit_Ite = #visit_Ite record,
    visit_IAbs = #visit_IAbs record,
    visit_UVarI = #visit_UVarI record,
    visit_prop = #visit_prop record,
    visit_PTrueFalse = #visit_PTrueFalse record,
    visit_BinConn = #visit_BinConn record,
    visit_Not = #visit_Not record,
    visit_BinPred = #visit_BinPred record,
    visit_Quan = #visit_Quan record,
    visit_sort = #visit_sort record,
    visit_Basic = #visit_Basic record,
    visit_Subset = #visit_Subset record,
    visit_UVarS = #visit_UVarS record,
    visit_SAbs = #visit_SAbs record,
    visit_SApp = #visit_SApp record,
    visit_var = #visit_var record,
    visit_uvar_bs = #visit_uvar_bs record,
    visit_uvar_i = #visit_uvar_i record,
    visit_uvar_s = #visit_uvar_s record,
    visit_quan = #visit_quan record,
    extend = #extend record
  }

fun override_visit_Ite (record : ('this, 'env) idx_visitor_vtable) new =
  {
    visit_bsort = #visit_bsort record,
    visit_Base = #visit_Base record,
    visit_BSArrow = #visit_BSArrow record,
    visit_UVarBS = #visit_UVarBS record,
    visit_idx = #visit_idx record,
    visit_VarI = #visit_VarI record,
    visit_IConst = #visit_IConst record,
    visit_UnOpI = #visit_UnOpI record,
    visit_BinOpI = #visit_BinOpI record,
    visit_Ite = new,
    visit_IAbs = #visit_IAbs record,
    visit_UVarI = #visit_UVarI record,
    visit_prop = #visit_prop record,
    visit_PTrueFalse = #visit_PTrueFalse record,
    visit_BinConn = #visit_BinConn record,
    visit_Not = #visit_Not record,
    visit_BinPred = #visit_BinPred record,
    visit_Quan = #visit_Quan record,
    visit_sort = #visit_sort record,
    visit_Basic = #visit_Basic record,
    visit_Subset = #visit_Subset record,
    visit_UVarS = #visit_UVarS record,
    visit_SAbs = #visit_SAbs record,
    visit_SApp = #visit_SApp record,
    visit_var = #visit_var record,
    visit_uvar_bs = #visit_uvar_bs record,
    visit_uvar_i = #visit_uvar_i record,
    visit_uvar_s = #visit_uvar_s record,
    visit_quan = #visit_quan record,
    extend = #extend record
  }

fun override_visit_UVarI (record : ('this, 'env) idx_visitor_vtable) new =
  {
    visit_bsort = #visit_bsort record,
    visit_Base = #visit_Base record,
    visit_BSArrow = #visit_BSArrow record,
    visit_UVarBS = #visit_UVarBS record,
    visit_idx = #visit_idx record,
    visit_VarI = #visit_VarI record,
    visit_IConst = #visit_IConst record,
    visit_UnOpI = #visit_UnOpI record,
    visit_BinOpI = #visit_BinOpI record,
    visit_Ite = #visit_Ite record,
    visit_IAbs = #visit_IAbs record,
    visit_UVarI = new,
    visit_prop = #visit_prop record,
    visit_PTrueFalse = #visit_PTrueFalse record,
    visit_BinConn = #visit_BinConn record,
    visit_Not = #visit_Not record,
    visit_BinPred = #visit_BinPred record,
    visit_Quan = #visit_Quan record,
    visit_sort = #visit_sort record,
    visit_Basic = #visit_Basic record,
    visit_Subset = #visit_Subset record,
    visit_UVarS = #visit_UVarS record,
    visit_SAbs = #visit_SAbs record,
    visit_SApp = #visit_SApp record,
    visit_var = #visit_var record,
    visit_uvar_bs = #visit_uvar_bs record,
    visit_uvar_i = #visit_uvar_i record,
    visit_uvar_s = #visit_uvar_s record,
    visit_quan = #visit_quan record,
    extend = #extend record
  }

fun override_visit_SApp (record : ('this, 'env) idx_visitor_vtable) new =
  {
    visit_bsort = #visit_bsort record,
    visit_Base = #visit_Base record,
    visit_BSArrow = #visit_BSArrow record,
    visit_UVarBS = #visit_UVarBS record,
    visit_idx = #visit_idx record,
    visit_VarI = #visit_VarI record,
    visit_IConst = #visit_IConst record,
    visit_UnOpI = #visit_UnOpI record,
    visit_BinOpI = #visit_BinOpI record,
    visit_Ite = #visit_Ite record,
    visit_IAbs = #visit_IAbs record,
    visit_UVarI = #visit_UVarI record,
    visit_prop = #visit_prop record,
    visit_PTrueFalse = #visit_PTrueFalse record,
    visit_BinConn = #visit_BinConn record,
    visit_Not = #visit_Not record,
    visit_BinPred = #visit_BinPred record,
    visit_Quan = #visit_Quan record,
    visit_sort = #visit_sort record,
    visit_Basic = #visit_Basic record,
    visit_Subset = #visit_Subset record,
    visit_UVarS = #visit_UVarS record,
    visit_SAbs = #visit_SAbs record,
    visit_SApp = new,
    visit_var = #visit_var record,
    visit_uvar_bs = #visit_uvar_bs record,
    visit_uvar_i = #visit_uvar_i record,
    visit_uvar_s = #visit_uvar_s record,
    visit_quan = #visit_quan record,
    extend = #extend record
  }

fun override_visit_UVarS (record : ('this, 'env) idx_visitor_vtable) new =
  {
    visit_bsort = #visit_bsort record,
    visit_Base = #visit_Base record,
    visit_BSArrow = #visit_BSArrow record,
    visit_UVarBS = #visit_UVarBS record,
    visit_idx = #visit_idx record,
    visit_VarI = #visit_VarI record,
    visit_IConst = #visit_IConst record,
    visit_UnOpI = #visit_UnOpI record,
    visit_BinOpI = #visit_BinOpI record,
    visit_Ite = #visit_Ite record,
    visit_IAbs = #visit_IAbs record,
    visit_UVarI = #visit_UVarI record,
    visit_prop = #visit_prop record,
    visit_PTrueFalse = #visit_PTrueFalse record,
    visit_BinConn = #visit_BinConn record,
    visit_Not = #visit_Not record,
    visit_BinPred = #visit_BinPred record,
    visit_Quan = #visit_Quan record,
    visit_sort = #visit_sort record,
    visit_Basic = #visit_Basic record,
    visit_Subset = #visit_Subset record,
    visit_UVarS = new,
    visit_SAbs = #visit_SAbs record,
    visit_SApp = #visit_SApp record,
    visit_var = #visit_var record,
    visit_uvar_bs = #visit_uvar_bs record,
    visit_uvar_i = #visit_uvar_i record,
    visit_uvar_s = #visit_uvar_s record,
    visit_quan = #visit_quan record,
    extend = #extend record
  }

type ('this, 'env) idx_visitor_interface =
     ('this, 'env) idx_visitor_vtable
                                       
datatype 'env idx_visitor =
         IdxVisitor of ('env idx_visitor, 'env) idx_visitor_interface

fun idx_visitor_impls_interface (this : 'env idx_visitor) :
    ('env idx_visitor, 'env) idx_visitor_interface =
  let
    val IdxVisitor vtable = this
  in
    vtable
  end

fun new_idx_visitor vtable params =
  let
    val vtable = vtable idx_visitor_impls_interface params
  in
    IdxVisitor vtable
  end
    
(***************** the default visitor  **********************)    

open VisitorUtil
       
fun default_idx_visitor_vtable
      (cast : 'this -> ('this, 'env) idx_visitor_interface)
      extend
      visit_var
      visit_uvar_bs
      visit_uvar_i
      visit_uvar_s
      visit_quan
    : ('this, 'env) idx_visitor_vtable =
  let
    fun visit_bsort this env data =
      let
        val vtable = cast this
      in
        case data of
            Base data => #visit_Base vtable this env data
          | BSArrow data => #visit_BSArrow vtable this env data
          | UVarBS data => #visit_UVarBS vtable this env data
      end
    fun visit_Base this env data =
      T.Base data
    fun visit_BSArrow this env data =
      let
        val vtable = cast this
        val (b1, b2) = data
        val b1 = #visit_bsort vtable this env b1
        val b2 = #visit_bsort vtable this env b2
      in
        T.BSArrow (b1, b2)
      end
    fun visit_UVarBS this env data =
      let
        val vtable = cast this
        val data = #visit_uvar_bs vtable this env data
      in
        T.UVarBS data
      end
    fun visit_idx this env data =
      let
        val vtable = cast this
      in
        case data of
	    VarI data => #visit_VarI vtable this env data
          | IConst data => #visit_IConst vtable this env data
          | UnOpI data => #visit_UnOpI vtable this env data
          | BinOpI data => #visit_BinOpI vtable this env data
          | Ite data => #visit_Ite vtable this env data
          | IAbs data => #visit_IAbs vtable this env data
          | UVarI data => #visit_UVarI vtable this env data
      end
    fun visit_VarI this env data =
      let
        val vtable = cast this
        val data = #visit_var vtable this env data
      in
        T.VarI data
      end
    fun visit_IConst this env data =
      T.IConst data
    fun visit_UnOpI this env data =
      let
        val vtable = cast this
        val (opr, i, r) = data
        val i = #visit_idx vtable this env i
      in
        T.UnOpI (opr, i, r)
      end
    fun visit_BinOpI this env data =
      let
        val vtable = cast this
        val (opr, i1, i2) = data
        val i1 = #visit_idx vtable this env i1
        val i2 = #visit_idx vtable this env i2
      in
        T.BinOpI (opr, i1, i2)
      end
    fun visit_Ite this env data =
      let
        val vtable = cast this
        val (i1, i2, i3, r) = data
        val i1 = #visit_idx vtable this env i1
        val i2 = #visit_idx vtable this env i2
        val i3 = #visit_idx vtable this env i3
      in
        T.Ite (i1, i2, i3, r)
      end
    fun visit_ibind this =
      let
        val vtable = cast this
      in
        Bind.visit_bind (#extend vtable this)
      end
    fun visit_IAbs this env data =
      let
        val vtable = cast this
        val (b, bind, r) = data
        val b = #visit_bsort vtable this env b
        val bind = visit_ibind this (#visit_idx vtable this) env bind
      in
        T.IAbs (b, bind, r)
      end
    fun visit_UVarI this env data =
      let
        val vtable = cast this
        val (u, r) = data
        val u = #visit_uvar_i vtable this env u
      in
        T.UVarI (u, r)
      end
    fun visit_prop this env data =
      let
        val vtable = cast this
      in
        case data of
	    PTrueFalse data => #visit_PTrueFalse vtable this env data
          | BinConn data => #visit_BinConn vtable this env data
          | Not data => #visit_Not vtable this env data
	  | BinPred data => #visit_BinPred vtable this env data
          | Quan data => #visit_Quan vtable this env data
      end
    fun visit_PTrueFalse this env data =
      T.PTrueFalse data
    fun visit_BinConn this env data =
      let
        val vtable = cast this
        val (opr, p1, p2) = data
        val p1 = #visit_prop vtable this env p1
        val p2 = #visit_prop vtable this env p2
      in
        T.BinConn (opr, p1, p2)
      end
    fun visit_Not this env data =
      let
        val vtable = cast this
        val (p, r) = data
        val p = #visit_prop vtable this env p
      in
        T.Not (p, r)
      end
    fun visit_BinPred this env data =
      let
        val vtable = cast this
        val (opr, i1, i2) = data
        val i1 = #visit_idx vtable this env i1
        val i2 = #visit_idx vtable this env i2
      in
        T.BinPred (opr, i1, i2)
      end
    fun visit_Quan this env data =
      let
        val vtable = cast this
        val (q, b, bind, r) = data
        val q = #visit_quan vtable this env q
        val b = #visit_bsort vtable this env b
        val bind = visit_ibind this (#visit_prop vtable this) env bind
      in
        T.Quan (q, b, bind, r)
      end
    fun visit_sort this env data =
      let
        val vtable = cast this
      in
        case data of
	    Basic data => #visit_Basic vtable this env data
	  | Subset data => #visit_Subset vtable this env data
          | UVarS data => #visit_UVarS vtable this env data
          | SAbs data => #visit_SAbs vtable this env data
          | SApp data => #visit_SApp vtable this env data
      end
    fun visit_Basic this env data =
      let
        val vtable = cast this
        val (b, r) = data
        val b = #visit_bsort vtable this env b
      in
        T.Basic (b, r)
      end
    fun visit_Subset this env data =
      let
        val vtable = cast this
        val ((b, r), bind, r2) = data
        val b = #visit_bsort vtable this env b
        val bind = visit_ibind this (#visit_prop vtable this) env bind
      in
        T.Subset ((b, r), bind, r2)
      end
    fun visit_UVarS this env data =
      let
        val vtable = cast this
        val (u, r) = data
        val u = #visit_uvar_s vtable this env u
      in
        T.UVarS (u, r)
      end
    fun visit_SAbs this env data =
      let
        val vtable = cast this
        val (b, bind, r) = data
        val b = #visit_bsort vtable this env b
        val bind = visit_ibind this (#visit_sort vtable this) env bind
      in
        T.SAbs (b, bind, r)
      end
    fun visit_SApp this env data =
      let
        val vtable = cast this
        val (s, i) = data
        val s = #visit_sort vtable this env s
        val i = #visit_idx vtable this env i
      in
        T.SApp (s, i)
      end
  in
    {
      visit_bsort = visit_bsort,
      visit_Base = visit_Base,
      visit_BSArrow = visit_BSArrow,
      visit_UVarBS = visit_UVarBS,
      visit_idx = visit_idx,
      visit_VarI = visit_VarI,
      visit_IConst = visit_IConst,
      visit_UnOpI = visit_UnOpI,
      visit_BinOpI = visit_BinOpI,
      visit_Ite = visit_Ite,
      visit_IAbs = visit_IAbs,
      visit_UVarI = visit_UVarI,
      visit_prop = visit_prop,
      visit_PTrueFalse = visit_PTrueFalse,
      visit_BinConn = visit_BinConn,
      visit_Not = visit_Not,
      visit_BinPred = visit_BinPred,
      visit_Quan = visit_Quan,
      visit_sort = visit_sort,
      visit_Basic = visit_Basic,
      visit_Subset = visit_Subset,
      visit_UVarS = visit_UVarS,
      visit_SAbs = visit_SAbs,
      visit_SApp = visit_SApp,
      visit_var = visit_var,
      visit_uvar_bs = visit_uvar_bs,
      visit_uvar_i = visit_uvar_i,
      visit_uvar_s = visit_uvar_s,
      visit_quan = visit_quan,
      extend = extend
    }
  end

end
