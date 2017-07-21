functor TypeVisitorFn (structure S : TYPE
                        structure T : TYPE
                        sharing type S.base_type = T.base_type
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
       
type ('this, 'env) type_visitor_vtable =
     {
       visit_mtype : 'this -> 'env -> mtype -> T.mtype,
       visit_Arrow : 'this -> 'env -> mtype * Idx.idx * mtype -> T.mtype,
       visit_TyNat : 'this -> 'env -> Idx.idx * region -> T.mtype,
       visit_TyArray : 'this -> 'env -> mtype * Idx.idx -> T.mtype,
       visit_BaseType : 'this -> 'env -> base_type * region -> T.mtype,
       visit_Unit : 'this -> 'env -> region -> T.mtype,
       visit_Prod : 'this -> 'env -> mtype * mtype -> T.mtype,
       visit_UniI : 'this -> 'env -> Idx.sort * (name * mtype) Bind.ibind * region -> T.mtype,
       visit_MtVar : 'this -> 'env -> var -> T.mtype,
       visit_MtAbs : 'this -> 'env -> kind * (name * mtype) Bind.tbind * region -> T.mtype,
       visit_MtApp : 'this -> 'env -> mtype * mtype -> T.mtype,
       visit_MtAbsI : 'this -> 'env -> Idx.bsort * (name * mtype) Bind.ibind  * region -> T.mtype,
       visit_MtAppI : 'this -> 'env -> mtype * Idx.idx -> T.mtype,
       visit_UVar : 'this -> 'env -> (Idx.bsort, kind, mtype) UVarT.uvar_mt * region -> T.mtype,
       visit_TDatatype : 'this -> 'env -> mtype datatype_def * region -> T.mtype,
       visit_ty : 'this -> 'env -> ty -> T.ty,
       visit_Mono : 'this -> 'env -> mtype -> T.ty,
       visit_Uni : 'this -> 'env -> (name * ty) Bind.tbind * region -> T.ty,
       visit_datatype : 'this -> 'env -> mtype datatype_def -> T.mtype T.datatype_def,
       visit_constr_core : 'this -> 'env -> mtype constr_core -> T.mtype T.constr_core,
       visit_constr : 'this -> 'env -> mtype constr -> T.mtype T.constr,
       visit_var : 'this -> 'env -> var -> T.var,
       visit_bsort : 'this -> 'env -> Idx.bsort -> T.Idx.bsort,
       visit_idx : 'this -> 'env -> Idx.idx -> T.Idx.idx,
       visit_sort : 'this -> 'env -> Idx.sort -> T.Idx.sort,
       visit_kind : 'this -> 'env -> kind -> T.kind,
       visit_uvar : 'this -> 'env -> (Idx.bsort, kind, mtype) UVarT.uvar_mt -> (T.Idx.bsort, T.kind, T.mtype) T.UVarT.uvar_mt,
       extend_i : 'this -> 'env -> name -> 'env,
       extend_t_anno : 'this -> 'env -> name * T.kind -> 'env,
       extend_t : 'this -> 'env -> name -> 'env
     }
       
fun override_visit_mtype (record : ('this, 'env) type_visitor_vtable) new =
  {
    visit_mtype = new,
    visit_Arrow = #visit_Arrow record,
    visit_TyNat = #visit_TyNat record,
    visit_TyArray = #visit_TyArray record,
    visit_BaseType = #visit_BaseType record,
    visit_Unit = #visit_Unit record,
    visit_Prod = #visit_Prod record,
    visit_UniI = #visit_UniI record,
    visit_MtVar = #visit_MtVar record,
    visit_MtAbs = #visit_MtAbs record,
    visit_MtApp = #visit_MtApp record,
    visit_MtAbsI = #visit_MtAbsI record,
    visit_MtAppI = #visit_MtAppI record,
    visit_UVar = #visit_UVar record,
    visit_TDatatype = #visit_TDatatype record,
    visit_ty = #visit_ty record,
    visit_Mono = #visit_Mono record,
    visit_Uni = #visit_Uni record,
    visit_datatype = #visit_datatype record,
    visit_constr_core = #visit_constr_core record,
    visit_constr = #visit_constr record,
    visit_var = #visit_var record,
    visit_bsort = #visit_bsort record,
    visit_idx = #visit_idx record,
    visit_sort = #visit_sort record,
    visit_kind = #visit_kind record,
    visit_uvar = #visit_uvar record,
    extend_i = #extend_i record,
    extend_t_anno = #extend_t_anno record,
    extend_t = #extend_t record
  }

fun override_visit_MtVar (record : ('this, 'env) type_visitor_vtable) new =
  {
    visit_mtype = #visit_mtype record,
    visit_Arrow = #visit_Arrow record,
    visit_TyNat = #visit_TyNat record,
    visit_TyArray = #visit_TyArray record,
    visit_BaseType = #visit_BaseType record,
    visit_Unit = #visit_Unit record,
    visit_Prod = #visit_Prod record,
    visit_UniI = #visit_UniI record,
    visit_MtVar = new,
    visit_MtAbs = #visit_MtAbs record,
    visit_MtApp = #visit_MtApp record,
    visit_MtAbsI = #visit_MtAbsI record,
    visit_MtAppI = #visit_MtAppI record,
    visit_UVar = #visit_UVar record,
    visit_TDatatype = #visit_TDatatype record,
    visit_ty = #visit_ty record,
    visit_Mono = #visit_Mono record,
    visit_Uni = #visit_Uni record,
    visit_datatype = #visit_datatype record,
    visit_constr_core = #visit_constr_core record,
    visit_constr = #visit_constr record,
    visit_var = #visit_var record,
    visit_bsort = #visit_bsort record,
    visit_idx = #visit_idx record,
    visit_sort = #visit_sort record,
    visit_kind = #visit_kind record,
    visit_uvar = #visit_uvar record,
    extend_i = #extend_i record,
    extend_t_anno = #extend_t_anno record,
    extend_t = #extend_t record
  }

fun override_visit_MtAppI (record : ('this, 'env) type_visitor_vtable) new =
  {
    visit_mtype = #visit_mtype record,
    visit_Arrow = #visit_Arrow record,
    visit_TyNat = #visit_TyNat record,
    visit_TyArray = #visit_TyArray record,
    visit_BaseType = #visit_BaseType record,
    visit_Unit = #visit_Unit record,
    visit_Prod = #visit_Prod record,
    visit_UniI = #visit_UniI record,
    visit_MtVar = #visit_MtVar record,
    visit_MtAbs = #visit_MtAbs record,
    visit_MtApp = #visit_MtApp record,
    visit_MtAbsI = #visit_MtAbsI record,
    visit_MtAppI = new,
    visit_UVar = #visit_UVar record,
    visit_TDatatype = #visit_TDatatype record,
    visit_ty = #visit_ty record,
    visit_Mono = #visit_Mono record,
    visit_Uni = #visit_Uni record,
    visit_datatype = #visit_datatype record,
    visit_constr_core = #visit_constr_core record,
    visit_constr = #visit_constr record,
    visit_var = #visit_var record,
    visit_bsort = #visit_bsort record,
    visit_idx = #visit_idx record,
    visit_sort = #visit_sort record,
    visit_kind = #visit_kind record,
    visit_uvar = #visit_uvar record,
    extend_i = #extend_i record,
    extend_t_anno = #extend_t_anno record,
    extend_t = #extend_t record
  }

fun override_visit_MtApp (record : ('this, 'env) type_visitor_vtable) new =
  {
    visit_mtype = #visit_mtype record,
    visit_Arrow = #visit_Arrow record,
    visit_TyNat = #visit_TyNat record,
    visit_TyArray = #visit_TyArray record,
    visit_BaseType = #visit_BaseType record,
    visit_Unit = #visit_Unit record,
    visit_Prod = #visit_Prod record,
    visit_UniI = #visit_UniI record,
    visit_MtVar = #visit_MtVar record,
    visit_MtAbs = #visit_MtAbs record,
    visit_MtApp = new,
    visit_MtAbsI = #visit_MtAbsI record,
    visit_MtAppI = #visit_MtAppI record,
    visit_UVar = #visit_UVar record,
    visit_TDatatype = #visit_TDatatype record,
    visit_ty = #visit_ty record,
    visit_Mono = #visit_Mono record,
    visit_Uni = #visit_Uni record,
    visit_datatype = #visit_datatype record,
    visit_constr_core = #visit_constr_core record,
    visit_constr = #visit_constr record,
    visit_var = #visit_var record,
    visit_bsort = #visit_bsort record,
    visit_idx = #visit_idx record,
    visit_sort = #visit_sort record,
    visit_kind = #visit_kind record,
    visit_uvar = #visit_uvar record,
    extend_i = #extend_i record,
    extend_t_anno = #extend_t_anno record,
    extend_t = #extend_t record
  }

fun override_visit_UVar (record : ('this, 'env) type_visitor_vtable) new =
  {
    visit_mtype = #visit_mtype record,
    visit_Arrow = #visit_Arrow record,
    visit_TyNat = #visit_TyNat record,
    visit_TyArray = #visit_TyArray record,
    visit_BaseType = #visit_BaseType record,
    visit_Unit = #visit_Unit record,
    visit_Prod = #visit_Prod record,
    visit_UniI = #visit_UniI record,
    visit_MtVar = #visit_MtVar record,
    visit_MtAbs = #visit_MtAbs record,
    visit_MtApp = #visit_MtApp record,
    visit_MtAbsI = #visit_MtAbsI record,
    visit_MtAppI = #visit_MtAppI record,
    visit_UVar = new,
    visit_TDatatype = #visit_TDatatype record,
    visit_ty = #visit_ty record,
    visit_Mono = #visit_Mono record,
    visit_Uni = #visit_Uni record,
    visit_datatype = #visit_datatype record,
    visit_constr_core = #visit_constr_core record,
    visit_constr = #visit_constr record,
    visit_var = #visit_var record,
    visit_bsort = #visit_bsort record,
    visit_idx = #visit_idx record,
    visit_sort = #visit_sort record,
    visit_kind = #visit_kind record,
    visit_uvar = #visit_uvar record,
    extend_i = #extend_i record,
    extend_t_anno = #extend_t_anno record,
    extend_t = #extend_t record
  }

fun override_extend_t_anno (record : ('this, 'env) type_visitor_vtable) new =
  {
    visit_mtype = #visit_mtype record,
    visit_Arrow = #visit_Arrow record,
    visit_TyNat = #visit_TyNat record,
    visit_TyArray = #visit_TyArray record,
    visit_BaseType = #visit_BaseType record,
    visit_Unit = #visit_Unit record,
    visit_Prod = #visit_Prod record,
    visit_UniI = #visit_UniI record,
    visit_MtVar = #visit_MtVar record,
    visit_MtAbs = #visit_MtAbs record,
    visit_MtApp = #visit_MtApp record,
    visit_MtAbsI = #visit_MtAbsI record,
    visit_MtAppI = #visit_MtAppI record,
    visit_UVar = #visit_UVar record,
    visit_TDatatype = #visit_TDatatype record,
    visit_ty = #visit_ty record,
    visit_Mono = #visit_Mono record,
    visit_Uni = #visit_Uni record,
    visit_datatype = #visit_datatype record,
    visit_constr_core = #visit_constr_core record,
    visit_constr = #visit_constr record,
    visit_var = #visit_var record,
    visit_bsort = #visit_bsort record,
    visit_idx = #visit_idx record,
    visit_sort = #visit_sort record,
    visit_kind = #visit_kind record,
    visit_uvar = #visit_uvar record,
    extend_i = #extend_i record,
    extend_t_anno = new,
    extend_t = #extend_t record
  }

type ('this, 'env) type_visitor_interface =
     ('this, 'env) type_visitor_vtable
                                       
datatype 'env type_visitor =
         TypeVisitor of ('env type_visitor, 'env) type_visitor_interface

fun type_visitor_impls_interface (this : 'env type_visitor) :
    ('env type_visitor, 'env) type_visitor_interface =
  let
    val TypeVisitor vtable = this
  in
    vtable
  end

fun new_type_visitor vtable params =
  let
    val vtable = vtable type_visitor_impls_interface params
  in
    TypeVisitor vtable
  end
    
(***************** the default visitor  **********************)    

open VisitorUtil
       
fun default_type_visitor_vtable
      (cast : 'this -> ('this, 'env) type_visitor_interface)
      extend_i
      extend_t
      visit_var
      visit_bsort
      visit_idx
      visit_sort
      visit_kind
      visit_uvar
    : ('this, 'env) type_visitor_vtable =
  let
    fun visit_mtype this env data =
      let
        val vtable = cast this
      in
        case data of
	    Arrow data => #visit_Arrow vtable this env data
          | TyNat data => #visit_TyNat vtable this env data
          | TyArray data => #visit_TyArray vtable this env data
	  | BaseType data => #visit_BaseType vtable this env data
          | Unit data => #visit_Unit vtable this env data
	  | Prod data => #visit_Prod vtable this env data
	  | UniI data => #visit_UniI vtable this env data
          | MtVar data => #visit_MtVar vtable this env data
          | MtAbs data => #visit_MtAbs vtable this env data
          | MtApp data => #visit_MtApp vtable this env data
          | MtAbsI data => #visit_MtAbsI vtable this env data
          | MtAppI data => #visit_MtAppI vtable this env data
          | UVar data => #visit_UVar vtable this env data
          | TDatatype data => #visit_TDatatype vtable this env data
      end
    fun visit_Arrow this env data =
      let
        val vtable = cast this
        val (t1, i, t2) = data
        val t1 = #visit_mtype vtable this env t1
        val i = #visit_idx vtable this env i
        val t2 = #visit_mtype vtable this env t2
      in
        T.Arrow (t1, i, t2)
      end
    fun visit_TyNat this env data =
      let
        val vtable = cast this
        val (i, r) = data
        val i = #visit_idx vtable this env i
      in
        T.TyNat (i, r)
      end
    fun visit_TyArray this env data =
      let
        val vtable = cast this
        val (t, i) = data
        val t = #visit_mtype vtable this env t
        val i = #visit_idx vtable this env i
      in
        T.TyArray (t, i)
      end
    fun visit_BaseType this env data =
      T.BaseType data
    fun visit_Unit this env data =
      T.Unit data
    fun visit_Prod this env data =
      let
        val vtable = cast this
        val (t1, t2) = data
        val t1 = #visit_mtype vtable this env t1
        val t2 = #visit_mtype vtable this env t2
      in
        T.Prod (t1, t2)
      end
    fun visit_ibind this =
      let
        val vtable = cast this
      in
        Bind.visit_bind (#extend_i vtable this)
      end
    fun visit_tbind this =
      let
        val vtable = cast this
      in
        Bind.visit_bind (#extend_t vtable this)
      end
    fun visit_binds visit_bind this f_anno f_term env (binds : ('namespace, 'classifier, 'name, 'inner) Bind.binds) : ('namespace, 'classifier2, 'name, 'inner2) Bind.binds=
      let
        val visit_ibinds = visit_binds visit_bind this f_anno f_term
        val vtable = cast this
      in
        case binds of
            Bind.BindNil t => Bind.BindNil $ f_term env t
          | Bind.BindCons (anno, bind) => Bind.BindCons (f_anno env anno, visit_bind this visit_ibinds env bind)
      end
    fun visit_ibinds a = visit_binds visit_ibind a
    fun visit_tbinds a = visit_binds visit_tbind a
    fun visit_UniI this env data =
      let
        val vtable = cast this
        val (s, bind, r) = data
        val s = #visit_sort vtable this env s
        val bind = visit_ibind this (#visit_mtype vtable this) env bind
      in
        T.UniI (s, bind, r)
      end
    fun visit_MtVar this env data =
      let
        val vtable = cast this
        val data = #visit_var vtable this env data
      in
        T.MtVar data
      end
    fun extend_t_anno this env (name, _) = 
      let
        val vtable = cast this
      in
        #extend_t vtable this env name
      end
    fun visit_tbind_anno this f env (anno, bind) = 
      let
        val vtable = cast this
        val Bind.Bind (name, t) = bind
        val t = f (#extend_t_anno vtable this env (name, anno)) t
        val bind = Bind.Bind (name, t)
      in
        (anno, bind)
      end
    fun visit_MtAbs this env data =
      let
        val vtable = cast this
        val (k, bind, r) = data
        val k = #visit_kind vtable this env k
        val (k, bind) = visit_tbind_anno this (#visit_mtype vtable this) env (k, bind)
      in
        T.MtAbs (k, bind, r)
      end
    fun visit_MtApp this env data =
      let
        val vtable = cast this
        val (t1, t2) = data
        val t1 = #visit_mtype vtable this env t1
        val t2 = #visit_mtype vtable this env t2
      in
        T.MtApp (t1, t2)
      end
    fun visit_MtAbsI this env data =
      let
        val vtable = cast this
        val (b, bind, r) = data
        val b = #visit_bsort vtable this env b
        val bind = visit_ibind this (#visit_mtype vtable this) env bind
      in
        T.MtAbsI (b, bind, r)
      end
    fun visit_MtAppI this env data =
      let
        val vtable = cast this
        val (t, i) = data
        val t = #visit_mtype vtable this env t
        val i = #visit_idx vtable this env i
      in
        T.MtAppI (t, i)
      end
    fun visit_UVar this env data =
      let
        val vtable = cast this
        val (x, r) = data
        val x = #visit_uvar vtable this env x
      in
        T.UVar (x, r)
      end
    fun visit_ty this env data =
      let
        val vtable = cast this
      in
        case data of
	    Mono data => #visit_Mono vtable this env data
	  | Uni data => #visit_Uni vtable this env data
      end
    fun visit_Mono this env data =
      let
        val vtable = cast this
        val data = #visit_mtype vtable this env data
      in
        T.Mono data
      end
    fun visit_Uni this env data =
      let
        val vtable = cast this
        val (bind, r) = data
        val bind = visit_tbind this (#visit_ty vtable this) env bind
      in
        T.Uni (bind, r)
      end
    fun visit_constr_core this env (data : mtype constr_core) : T.mtype T.constr_core =
      let
        val vtable = cast this
      in
        visit_ibinds this
                     (#visit_sort vtable this)
                     (visit_pair (#visit_mtype vtable this)
                                 (visit_list (#visit_idx vtable this))) env data
      end
    fun visit_constr this env (data : mtype constr) : T.mtype T.constr =
      let
        val vtable = cast this
      in
        visit_pair (#visit_var vtable this)
                   (visit_tbinds this
                                 return2
                                 (#visit_constr_core vtable this)) env data
      end
    fun visit_datatype this env data =
      let
        val vtable = cast this
        fun visit_constr_decl env (name, c, r) = (name, #visit_constr_core vtable this env c, r)
      in
        visit_tbind this
                    (visit_tbinds this
                                  return2
                                  (visit_pair (visit_list (#visit_bsort vtable this))
                                              (visit_list visit_constr_decl))) env data
      end
    fun visit_TDatatype this env data =
      let
        val vtable = cast this
        val (dt, r) = data
        fun visit_constr_decl env (name, c, r) = (name, visit_constr_core this env c, r)
        val dt = #visit_datatype vtable this env dt
      in
        T.TDatatype (dt, r)
      end
  in
    {
      visit_mtype = visit_mtype,
      visit_Arrow = visit_Arrow,
      visit_TyNat = visit_TyNat,
      visit_TyArray = visit_TyArray,
      visit_BaseType = visit_BaseType,
      visit_Unit = visit_Unit,
      visit_Prod = visit_Prod,
      visit_UniI = visit_UniI,
      visit_MtVar = visit_MtVar,
      visit_MtAbs = visit_MtAbs,
      visit_MtApp = visit_MtApp,
      visit_MtAbsI = visit_MtAbsI,
      visit_MtAppI = visit_MtAppI,
      visit_UVar = visit_UVar,
      visit_TDatatype = visit_TDatatype,
      visit_ty = visit_ty,
      visit_Mono = visit_Mono,
      visit_Uni = visit_Uni,
      visit_datatype = visit_datatype,
      visit_constr_core = visit_constr_core,
      visit_constr = visit_constr,
      visit_var = visit_var,
      visit_bsort = visit_bsort,
      visit_idx = visit_idx,
      visit_sort = visit_sort,
      visit_kind = visit_kind,
      visit_uvar = visit_uvar,
      extend_i = extend_i,
      extend_t_anno = extend_t_anno,
      extend_t = extend_t
    }
  end

end

