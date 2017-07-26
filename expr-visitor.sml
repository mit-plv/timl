signature EXPR_VISITOR_PARAMS = sig
structure S : EXPR
structure T : EXPR
end

functor ExprVisitorFn (Params : EXPR_VISITOR_PARAMS) = struct

open Params
open Unbound
open Namespaces
open Binders
open Operators
open Region
open Pattern
open S

infixr 0 $
       
type ('this, 'env) expr_visitor_vtable =
     {
       visit_expr : 'this -> 'env -> expr -> T.expr,
       visit_EVar : 'this -> 'env -> var * bool -> T.expr,
       visit_EConst : 'this -> 'env -> expr_const * region -> T.expr,
       visit_EUnOp : 'this -> 'env -> expr_un_op * expr * region -> T.expr,
       visit_EBinOp : 'this -> 'env -> bin_op * expr * expr -> T.expr,
       visit_ETriOp : 'this -> 'env -> tri_op * expr * expr * expr -> T.expr,
       visit_EEI : 'this -> 'env -> expr_EI * expr * idx -> T.expr,
       visit_EET : 'this -> 'env -> expr_ET * expr * mtype -> T.expr,
       visit_ET : 'this -> 'env -> expr_T * mtype * region -> T.expr,
       visit_EAbs : 'this -> 'env -> (ptrn, expr) bind -> T.expr,
       visit_EAbsI : 'this -> 'env -> (sort, expr) ibind_anno * region -> T.expr,
       visit_EAppConstr : 'this -> 'env -> (cvar * bool) * mtype list * idx list * expr * (int * mtype) option -> T.expr,
       visit_ECase : 'this -> 'env -> expr * return * (ptrn, expr) bind list * region -> T.expr,
       visit_ELet : 'this -> 'env -> return * (decl tele, expr) bind * region -> T.expr,
       visit_decl : 'this -> 'env ctx -> decl -> T.decl,
       visit_DVal : 'this -> 'env ctx -> ename binder * (tname binder list, expr) bind outer * region outer -> T.decl,
       visit_DValPtrn : 'this -> 'env ctx -> ptrn * expr outer * region outer -> T.decl,
       visit_DRec : 'this -> 'env ctx -> ename binder * (tname binder list * stbind tele rebind, (mtype * idx) * expr) bind inner * region outer -> T.decl,
       visit_DIdxDef : 'this -> 'env ctx -> iname binder * sort outer * idx outer -> T.decl,
       visit_DAbsIdx2 : 'this -> 'env ctx -> iname binder * sort outer * idx outer -> T.decl,
       visit_DAbsIdx : 'this -> 'env ctx -> (iname binder * sort outer * idx outer) * decl tele rebind * region outer -> T.decl,
       visit_DTypeDef : 'this -> 'env ctx -> tname binder * mtype outer -> T.decl,
       visit_DOpen : 'this -> 'env ctx -> mod_id outer * scoping_ctx option -> T.decl,
       visit_ptrn : 'this -> 'env ctx -> ptrn -> T.ptrn,
       visit_VarP : 'this -> 'env ctx -> ename binder -> T.ptrn,
       visit_TTP : 'this -> 'env ctx -> region outer -> T.ptrn,
       visit_PairP : 'this -> 'env ctx -> ptrn * ptrn -> T.ptrn,
       visit_AliasP : 'this -> 'env ctx -> ename binder * ptrn * region outer -> T.ptrn,
       visit_ConstrP : 'this -> 'env ctx -> ((cvar * ptrn_constr_tag) * bool) outer * iname binder list * ptrn * region outer -> T.ptrn,
       visit_AnnoP : 'this -> 'env ctx -> ptrn * mtype outer -> T.ptrn,
       visit_EApp : 'this -> 'env -> expr * expr -> T.expr,
       visit_EPair : 'this -> 'env -> expr * expr -> T.expr,
       visit_EAdd : 'this -> 'env -> expr * expr -> T.expr,
       visit_ENew : 'this -> 'env -> expr * expr -> T.expr,
       visit_ERead : 'this -> 'env -> expr * expr -> T.expr,
       visit_EAppI : 'this -> 'env -> expr * idx -> T.expr,
       visit_EAscTime : 'this -> 'env -> expr * idx -> T.expr,
       visit_EAppT : 'this -> 'env -> expr * mtype -> T.expr,
       visit_EAsc : 'this -> 'env -> expr * mtype -> T.expr,
       visit_var : 'this -> 'env -> var -> T.var,
       visit_cvar : 'this -> 'env -> cvar -> T.cvar,
       visit_mod_id : 'this -> 'env -> mod_id -> T.mod_id,
       visit_idx : 'this -> 'env -> idx -> T.idx,
       visit_sort : 'this -> 'env -> sort -> T.sort,
       visit_mtype : 'this -> 'env -> mtype -> T.mtype,
       visit_ptrn_constr_tag : 'this -> 'env -> ptrn_constr_tag -> T.ptrn_constr_tag,
       extend_i : 'this -> 'env -> iname -> 'env,
       extend_t : 'this -> 'env -> tname -> 'env,
       extend_c : 'this -> 'env -> cname -> 'env,
       extend_e : 'this -> 'env -> ename -> 'env
     }
       
fun override_visit_ConstrP (record : ('this, 'env) expr_visitor_vtable) new : ('this, 'env) expr_visitor_vtable =
  {
    visit_expr = #visit_expr record,
    visit_EVar = #visit_EVar record,
    visit_EConst = #visit_EConst record,
    visit_EUnOp = #visit_EUnOp record,
    visit_EBinOp = #visit_EBinOp record,
    visit_ETriOp = #visit_ETriOp record,
    visit_EEI = #visit_EEI record,
    visit_EET = #visit_EET record,
    visit_ET = #visit_ET record,
    visit_EAbs = #visit_EAbs record,
    visit_EAbsI = #visit_EAbsI record,
    visit_EAppConstr = #visit_EAppConstr record,
    visit_ECase = #visit_ECase record,
    visit_ELet = #visit_ELet record,
    visit_EAppT = #visit_EAppT record,
    visit_EAsc = #visit_EAsc record,
    visit_decl = #visit_decl record,
    visit_DVal = #visit_DVal record,
    visit_DValPtrn = #visit_DValPtrn record,
    visit_DRec = #visit_DRec record,
    visit_DIdxDef = #visit_DIdxDef record,
    visit_DAbsIdx2 = #visit_DAbsIdx2 record,
    visit_DAbsIdx = #visit_DAbsIdx record,
    visit_DTypeDef = #visit_DTypeDef record,
    visit_DOpen = #visit_DOpen record,
    visit_ptrn = #visit_ptrn record,
    visit_VarP = #visit_VarP record,
    visit_TTP = #visit_TTP record,
    visit_PairP = #visit_PairP record,
    visit_AliasP = #visit_AliasP record,
    visit_ConstrP = new,
    visit_AnnoP = #visit_AnnoP record,
    visit_EApp = #visit_EApp record,
    visit_EPair = #visit_EPair record,
    visit_EAdd = #visit_EAdd record,
    visit_ENew = #visit_ENew record,
    visit_ERead = #visit_ERead record,
    visit_EAppI = #visit_EAppI record,
    visit_EAscTime = #visit_EAscTime record,
    visit_var = #visit_var record,
    visit_cvar = #visit_cvar record,
    visit_mod_id = #visit_mod_id record,
    visit_idx = #visit_idx record,
    visit_sort = #visit_sort record,
    visit_mtype = #visit_mtype record,
    visit_ptrn_constr_tag = #visit_ptrn_constr_tag record,
    extend_i = #extend_i record,
    extend_t = #extend_t record,
    extend_c = #extend_c record,
    extend_e = #extend_e record
  }
    
fun override_visit_VarP (record : ('this, 'env) expr_visitor_vtable) new : ('this, 'env) expr_visitor_vtable =
  {
    visit_expr = #visit_expr record,
    visit_EVar = #visit_EVar record,
    visit_EConst = #visit_EConst record,
    visit_EUnOp = #visit_EUnOp record,
    visit_EBinOp = #visit_EBinOp record,
    visit_ETriOp = #visit_ETriOp record,
    visit_EEI = #visit_EEI record,
    visit_EET = #visit_EET record,
    visit_ET = #visit_ET record,
    visit_EAbs = #visit_EAbs record,
    visit_EAbsI = #visit_EAbsI record,
    visit_EAppConstr = #visit_EAppConstr record,
    visit_ECase = #visit_ECase record,
    visit_ELet = #visit_ELet record,
    visit_EAppT = #visit_EAppT record,
    visit_EAsc = #visit_EAsc record,
    visit_decl = #visit_decl record,
    visit_DVal = #visit_DVal record,
    visit_DValPtrn = #visit_DValPtrn record,
    visit_DRec = #visit_DRec record,
    visit_DIdxDef = #visit_DIdxDef record,
    visit_DAbsIdx2 = #visit_DAbsIdx2 record,
    visit_DAbsIdx = #visit_DAbsIdx record,
    visit_DTypeDef = #visit_DTypeDef record,
    visit_DOpen = #visit_DOpen record,
    visit_ptrn = #visit_ptrn record,
    visit_VarP = new,
    visit_TTP = #visit_TTP record,
    visit_PairP = #visit_PairP record,
    visit_AliasP = #visit_AliasP record,
    visit_ConstrP = #visit_ConstrP record,
    visit_AnnoP = #visit_AnnoP record,
    visit_EApp = #visit_EApp record,
    visit_EPair = #visit_EPair record,
    visit_EAdd = #visit_EAdd record,
    visit_ENew = #visit_ENew record,
    visit_ERead = #visit_ERead record,
    visit_EAppI = #visit_EAppI record,
    visit_EAscTime = #visit_EAscTime record,
    visit_var = #visit_var record,
    visit_cvar = #visit_cvar record,
    visit_mod_id = #visit_mod_id record,
    visit_idx = #visit_idx record,
    visit_sort = #visit_sort record,
    visit_mtype = #visit_mtype record,
    visit_ptrn_constr_tag = #visit_ptrn_constr_tag record,
    extend_i = #extend_i record,
    extend_t = #extend_t record,
    extend_c = #extend_c record,
    extend_e = #extend_e record
  }

fun override_visit_EVar (record : ('this, 'env) expr_visitor_vtable) new : ('this, 'env) expr_visitor_vtable =
  {
    visit_expr = #visit_expr record,
    visit_EVar = new,
    visit_EConst = #visit_EConst record,
    visit_EUnOp = #visit_EUnOp record,
    visit_EBinOp = #visit_EBinOp record,
    visit_ETriOp = #visit_ETriOp record,
    visit_EEI = #visit_EEI record,
    visit_EET = #visit_EET record,
    visit_ET = #visit_ET record,
    visit_EAbs = #visit_EAbs record,
    visit_EAbsI = #visit_EAbsI record,
    visit_EAppConstr = #visit_EAppConstr record,
    visit_ECase = #visit_ECase record,
    visit_ELet = #visit_ELet record,
    visit_EAppT = #visit_EAppT record,
    visit_EAsc = #visit_EAsc record,
    visit_decl = #visit_decl record,
    visit_DVal = #visit_DVal record,
    visit_DValPtrn = #visit_DValPtrn record,
    visit_DRec = #visit_DRec record,
    visit_DIdxDef = #visit_DIdxDef record,
    visit_DAbsIdx2 = #visit_DAbsIdx2 record,
    visit_DAbsIdx = #visit_DAbsIdx record,
    visit_DTypeDef = #visit_DTypeDef record,
    visit_DOpen = #visit_DOpen record,
    visit_ptrn = #visit_ptrn record,
    visit_VarP = #visit_VarP record,
    visit_TTP = #visit_TTP record,
    visit_PairP = #visit_PairP record,
    visit_AliasP = #visit_AliasP record,
    visit_ConstrP = #visit_ConstrP record,
    visit_AnnoP = #visit_AnnoP record,
    visit_EApp = #visit_EApp record,
    visit_EPair = #visit_EPair record,
    visit_EAdd = #visit_EAdd record,
    visit_ENew = #visit_ENew record,
    visit_ERead = #visit_ERead record,
    visit_EAppI = #visit_EAppI record,
    visit_EAscTime = #visit_EAscTime record,
    visit_var = #visit_var record,
    visit_cvar = #visit_cvar record,
    visit_mod_id = #visit_mod_id record,
    visit_idx = #visit_idx record,
    visit_sort = #visit_sort record,
    visit_mtype = #visit_mtype record,
    visit_ptrn_constr_tag = #visit_ptrn_constr_tag record,
    extend_i = #extend_i record,
    extend_t = #extend_t record,
    extend_c = #extend_c record,
    extend_e = #extend_e record
  }

fun override_visit_EBinOp (record : ('this, 'env) expr_visitor_vtable) new : ('this, 'env) expr_visitor_vtable =
  {
    visit_expr = #visit_expr record,
    visit_EVar = #visit_EVar record,
    visit_EConst = #visit_EConst record,
    visit_EUnOp = #visit_EUnOp record,
    visit_EBinOp = new,
    visit_ETriOp = #visit_ETriOp record,
    visit_EEI = #visit_EEI record,
    visit_EET = #visit_EET record,
    visit_ET = #visit_ET record,
    visit_EAbs = #visit_EAbs record,
    visit_EAbsI = #visit_EAbsI record,
    visit_EAppConstr = #visit_EAppConstr record,
    visit_ECase = #visit_ECase record,
    visit_ELet = #visit_ELet record,
    visit_EAppT = #visit_EAppT record,
    visit_EAsc = #visit_EAsc record,
    visit_decl = #visit_decl record,
    visit_DVal = #visit_DVal record,
    visit_DValPtrn = #visit_DValPtrn record,
    visit_DRec = #visit_DRec record,
    visit_DIdxDef = #visit_DIdxDef record,
    visit_DAbsIdx2 = #visit_DAbsIdx2 record,
    visit_DAbsIdx = #visit_DAbsIdx record,
    visit_DTypeDef = #visit_DTypeDef record,
    visit_DOpen = #visit_DOpen record,
    visit_ptrn = #visit_ptrn record,
    visit_VarP = #visit_VarP record,
    visit_TTP = #visit_TTP record,
    visit_PairP = #visit_PairP record,
    visit_AliasP = #visit_AliasP record,
    visit_ConstrP = #visit_ConstrP record,
    visit_AnnoP = #visit_AnnoP record,
    visit_EApp = #visit_EApp record,
    visit_EPair = #visit_EPair record,
    visit_EAdd = #visit_EAdd record,
    visit_ENew = #visit_ENew record,
    visit_ERead = #visit_ERead record,
    visit_EAppI = #visit_EAppI record,
    visit_EAscTime = #visit_EAscTime record,
    visit_var = #visit_var record,
    visit_cvar = #visit_cvar record,
    visit_mod_id = #visit_mod_id record,
    visit_idx = #visit_idx record,
    visit_sort = #visit_sort record,
    visit_mtype = #visit_mtype record,
    visit_ptrn_constr_tag = #visit_ptrn_constr_tag record,
    extend_i = #extend_i record,
    extend_t = #extend_t record,
    extend_c = #extend_c record,
    extend_e = #extend_e record
  }

fun override_visit_EApp (record : ('this, 'env) expr_visitor_vtable) new : ('this, 'env) expr_visitor_vtable =
  {
    visit_expr = #visit_expr record,
    visit_EVar = #visit_EVar record,
    visit_EConst = #visit_EConst record,
    visit_EUnOp = #visit_EUnOp record,
    visit_EBinOp = #visit_EBinOp record,
    visit_ETriOp = #visit_ETriOp record,
    visit_EEI = #visit_EEI record,
    visit_EET = #visit_EET record,
    visit_ET = #visit_ET record,
    visit_EAbs = #visit_EAbs record,
    visit_EAbsI = #visit_EAbsI record,
    visit_EAppConstr = #visit_EAppConstr record,
    visit_ECase = #visit_ECase record,
    visit_ELet = #visit_ELet record,
    visit_EAppT = #visit_EAppT record,
    visit_EAsc = #visit_EAsc record,
    visit_decl = #visit_decl record,
    visit_DVal = #visit_DVal record,
    visit_DValPtrn = #visit_DValPtrn record,
    visit_DRec = #visit_DRec record,
    visit_DIdxDef = #visit_DIdxDef record,
    visit_DAbsIdx2 = #visit_DAbsIdx2 record,
    visit_DAbsIdx = #visit_DAbsIdx record,
    visit_DTypeDef = #visit_DTypeDef record,
    visit_DOpen = #visit_DOpen record,
    visit_ptrn = #visit_ptrn record,
    visit_VarP = #visit_VarP record,
    visit_TTP = #visit_TTP record,
    visit_PairP = #visit_PairP record,
    visit_AliasP = #visit_AliasP record,
    visit_ConstrP = #visit_ConstrP record,
    visit_AnnoP = #visit_AnnoP record,
    visit_EApp = new,
    visit_EPair = #visit_EPair record,
    visit_EAdd = #visit_EAdd record,
    visit_ENew = #visit_ENew record,
    visit_ERead = #visit_ERead record,
    visit_EAppI = #visit_EAppI record,
    visit_EAscTime = #visit_EAscTime record,
    visit_var = #visit_var record,
    visit_cvar = #visit_cvar record,
    visit_mod_id = #visit_mod_id record,
    visit_idx = #visit_idx record,
    visit_sort = #visit_sort record,
    visit_mtype = #visit_mtype record,
    visit_ptrn_constr_tag = #visit_ptrn_constr_tag record,
    extend_i = #extend_i record,
    extend_t = #extend_t record,
    extend_c = #extend_c record,
    extend_e = #extend_e record
  }

fun override_visit_EEI (record : ('this, 'env) expr_visitor_vtable) new : ('this, 'env) expr_visitor_vtable =
  {
    visit_expr = #visit_expr record,
    visit_EVar = #visit_EVar record,
    visit_EConst = #visit_EConst record,
    visit_EUnOp = #visit_EUnOp record,
    visit_EBinOp = #visit_EBinOp record,
    visit_ETriOp = #visit_ETriOp record,
    visit_EEI = new,
    visit_EET = #visit_EET record,
    visit_ET = #visit_ET record,
    visit_EAbs = #visit_EAbs record,
    visit_EAbsI = #visit_EAbsI record,
    visit_EAppConstr = #visit_EAppConstr record,
    visit_ECase = #visit_ECase record,
    visit_ELet = #visit_ELet record,
    visit_EAppT = #visit_EAppT record,
    visit_EAsc = #visit_EAsc record,
    visit_decl = #visit_decl record,
    visit_DVal = #visit_DVal record,
    visit_DValPtrn = #visit_DValPtrn record,
    visit_DRec = #visit_DRec record,
    visit_DIdxDef = #visit_DIdxDef record,
    visit_DAbsIdx2 = #visit_DAbsIdx2 record,
    visit_DAbsIdx = #visit_DAbsIdx record,
    visit_DTypeDef = #visit_DTypeDef record,
    visit_DOpen = #visit_DOpen record,
    visit_ptrn = #visit_ptrn record,
    visit_VarP = #visit_VarP record,
    visit_TTP = #visit_TTP record,
    visit_PairP = #visit_PairP record,
    visit_AliasP = #visit_AliasP record,
    visit_ConstrP = #visit_ConstrP record,
    visit_AnnoP = #visit_AnnoP record,
    visit_EApp = #visit_EApp record,
    visit_EPair = #visit_EPair record,
    visit_EAdd = #visit_EAdd record,
    visit_ENew = #visit_ENew record,
    visit_ERead = #visit_ERead record,
    visit_EAppI = #visit_EAppI record,
    visit_EAscTime = #visit_EAscTime record,
    visit_var = #visit_var record,
    visit_cvar = #visit_cvar record,
    visit_mod_id = #visit_mod_id record,
    visit_idx = #visit_idx record,
    visit_sort = #visit_sort record,
    visit_mtype = #visit_mtype record,
    visit_ptrn_constr_tag = #visit_ptrn_constr_tag record,
    extend_i = #extend_i record,
    extend_t = #extend_t record,
    extend_c = #extend_c record,
    extend_e = #extend_e record
  }

fun override_visit_EAppI (record : ('this, 'env) expr_visitor_vtable) new : ('this, 'env) expr_visitor_vtable =
  {
    visit_expr = #visit_expr record,
    visit_EVar = #visit_EVar record,
    visit_EConst = #visit_EConst record,
    visit_EUnOp = #visit_EUnOp record,
    visit_EBinOp = #visit_EBinOp record,
    visit_ETriOp = #visit_ETriOp record,
    visit_EEI = #visit_EEI record,
    visit_EET = #visit_EET record,
    visit_ET = #visit_ET record,
    visit_EAbs = #visit_EAbs record,
    visit_EAbsI = #visit_EAbsI record,
    visit_EAppConstr = #visit_EAppConstr record,
    visit_ECase = #visit_ECase record,
    visit_ELet = #visit_ELet record,
    visit_EAppT = #visit_EAppT record,
    visit_EAsc = #visit_EAsc record,
    visit_decl = #visit_decl record,
    visit_DVal = #visit_DVal record,
    visit_DValPtrn = #visit_DValPtrn record,
    visit_DRec = #visit_DRec record,
    visit_DIdxDef = #visit_DIdxDef record,
    visit_DAbsIdx2 = #visit_DAbsIdx2 record,
    visit_DAbsIdx = #visit_DAbsIdx record,
    visit_DTypeDef = #visit_DTypeDef record,
    visit_DOpen = #visit_DOpen record,
    visit_ptrn = #visit_ptrn record,
    visit_VarP = #visit_VarP record,
    visit_TTP = #visit_TTP record,
    visit_PairP = #visit_PairP record,
    visit_AliasP = #visit_AliasP record,
    visit_ConstrP = #visit_ConstrP record,
    visit_AnnoP = #visit_AnnoP record,
    visit_EApp = #visit_EApp record,
    visit_EPair = #visit_EPair record,
    visit_EAdd = #visit_EAdd record,
    visit_ENew = #visit_ENew record,
    visit_ERead = #visit_ERead record,
    visit_EAppI = new,
    visit_EAscTime = #visit_EAscTime record,
    visit_var = #visit_var record,
    visit_cvar = #visit_cvar record,
    visit_mod_id = #visit_mod_id record,
    visit_idx = #visit_idx record,
    visit_sort = #visit_sort record,
    visit_mtype = #visit_mtype record,
    visit_ptrn_constr_tag = #visit_ptrn_constr_tag record,
    extend_i = #extend_i record,
    extend_t = #extend_t record,
    extend_c = #extend_c record,
    extend_e = #extend_e record
  }

fun override_visit_EAscTime (record : ('this, 'env) expr_visitor_vtable) new : ('this, 'env) expr_visitor_vtable =
  {
    visit_expr = #visit_expr record,
    visit_EVar = #visit_EVar record,
    visit_EConst = #visit_EConst record,
    visit_EUnOp = #visit_EUnOp record,
    visit_EBinOp = #visit_EBinOp record,
    visit_ETriOp = #visit_ETriOp record,
    visit_EEI = #visit_EEI record,
    visit_EET = #visit_EET record,
    visit_ET = #visit_ET record,
    visit_EAbs = #visit_EAbs record,
    visit_EAbsI = #visit_EAbsI record,
    visit_EAppConstr = #visit_EAppConstr record,
    visit_ECase = #visit_ECase record,
    visit_ELet = #visit_ELet record,
    visit_EAppT = #visit_EAppT record,
    visit_EAsc = #visit_EAsc record,
    visit_decl = #visit_decl record,
    visit_DVal = #visit_DVal record,
    visit_DValPtrn = #visit_DValPtrn record,
    visit_DRec = #visit_DRec record,
    visit_DIdxDef = #visit_DIdxDef record,
    visit_DAbsIdx2 = #visit_DAbsIdx2 record,
    visit_DAbsIdx = #visit_DAbsIdx record,
    visit_DTypeDef = #visit_DTypeDef record,
    visit_DOpen = #visit_DOpen record,
    visit_ptrn = #visit_ptrn record,
    visit_VarP = #visit_VarP record,
    visit_TTP = #visit_TTP record,
    visit_PairP = #visit_PairP record,
    visit_AliasP = #visit_AliasP record,
    visit_ConstrP = #visit_ConstrP record,
    visit_AnnoP = #visit_AnnoP record,
    visit_EApp = #visit_EApp record,
    visit_EPair = #visit_EPair record,
    visit_EAdd = #visit_EAdd record,
    visit_ENew = #visit_ENew record,
    visit_ERead = #visit_ERead record,
    visit_EAppI = #visit_EAppI record,
    visit_EAscTime = new,
    visit_var = #visit_var record,
    visit_cvar = #visit_cvar record,
    visit_mod_id = #visit_mod_id record,
    visit_idx = #visit_idx record,
    visit_sort = #visit_sort record,
    visit_mtype = #visit_mtype record,
    visit_ptrn_constr_tag = #visit_ptrn_constr_tag record,
    extend_i = #extend_i record,
    extend_t = #extend_t record,
    extend_c = #extend_c record,
    extend_e = #extend_e record
  }

fun override_visit_EAsc (record : ('this, 'env) expr_visitor_vtable) new : ('this, 'env) expr_visitor_vtable =
  {
    visit_expr = #visit_expr record,
    visit_EVar = #visit_EVar record,
    visit_EConst = #visit_EConst record,
    visit_EUnOp = #visit_EUnOp record,
    visit_EBinOp = #visit_EBinOp record,
    visit_ETriOp = #visit_ETriOp record,
    visit_EEI = #visit_EEI record,
    visit_EET = #visit_EET record,
    visit_ET = #visit_ET record,
    visit_EAbs = #visit_EAbs record,
    visit_EAbsI = #visit_EAbsI record,
    visit_EAppConstr = #visit_EAppConstr record,
    visit_ECase = #visit_ECase record,
    visit_ELet = #visit_ELet record,
    visit_EAppT = #visit_EAppT record,
    visit_EAsc = new,
    visit_decl = #visit_decl record,
    visit_DVal = #visit_DVal record,
    visit_DValPtrn = #visit_DValPtrn record,
    visit_DRec = #visit_DRec record,
    visit_DIdxDef = #visit_DIdxDef record,
    visit_DAbsIdx2 = #visit_DAbsIdx2 record,
    visit_DAbsIdx = #visit_DAbsIdx record,
    visit_DTypeDef = #visit_DTypeDef record,
    visit_DOpen = #visit_DOpen record,
    visit_ptrn = #visit_ptrn record,
    visit_VarP = #visit_VarP record,
    visit_TTP = #visit_TTP record,
    visit_PairP = #visit_PairP record,
    visit_AliasP = #visit_AliasP record,
    visit_ConstrP = #visit_ConstrP record,
    visit_AnnoP = #visit_AnnoP record,
    visit_EApp = #visit_EApp record,
    visit_EPair = #visit_EPair record,
    visit_EAdd = #visit_EAdd record,
    visit_ENew = #visit_ENew record,
    visit_ERead = #visit_ERead record,
    visit_EAppI = #visit_EAppI record,
    visit_EAscTime = #visit_EAscTime record,
    visit_var = #visit_var record,
    visit_cvar = #visit_cvar record,
    visit_mod_id = #visit_mod_id record,
    visit_idx = #visit_idx record,
    visit_sort = #visit_sort record,
    visit_mtype = #visit_mtype record,
    visit_ptrn_constr_tag = #visit_ptrn_constr_tag record,
    extend_i = #extend_i record,
    extend_t = #extend_t record,
    extend_c = #extend_c record,
    extend_e = #extend_e record
  }

fun override_visit_ECase (record : ('this, 'env) expr_visitor_vtable) new : ('this, 'env) expr_visitor_vtable =
  {
    visit_expr = #visit_expr record,
    visit_EVar = #visit_EVar record,
    visit_EConst = #visit_EConst record,
    visit_EUnOp = #visit_EUnOp record,
    visit_EBinOp = #visit_EBinOp record,
    visit_ETriOp = #visit_ETriOp record,
    visit_EEI = #visit_EEI record,
    visit_EET = #visit_EET record,
    visit_ET = #visit_ET record,
    visit_EAbs = #visit_EAbs record,
    visit_EAbsI = #visit_EAbsI record,
    visit_EAppConstr = #visit_EAppConstr record,
    visit_ECase = new,
    visit_ELet = #visit_ELet record,
    visit_EAppT = #visit_EAppT record,
    visit_EAsc = #visit_EAsc record,
    visit_decl = #visit_decl record,
    visit_DVal = #visit_DVal record,
    visit_DValPtrn = #visit_DValPtrn record,
    visit_DRec = #visit_DRec record,
    visit_DIdxDef = #visit_DIdxDef record,
    visit_DAbsIdx2 = #visit_DAbsIdx2 record,
    visit_DAbsIdx = #visit_DAbsIdx record,
    visit_DTypeDef = #visit_DTypeDef record,
    visit_DOpen = #visit_DOpen record,
    visit_ptrn = #visit_ptrn record,
    visit_VarP = #visit_VarP record,
    visit_TTP = #visit_TTP record,
    visit_PairP = #visit_PairP record,
    visit_AliasP = #visit_AliasP record,
    visit_ConstrP = #visit_ConstrP record,
    visit_AnnoP = #visit_AnnoP record,
    visit_EApp = #visit_EApp record,
    visit_EPair = #visit_EPair record,
    visit_EAdd = #visit_EAdd record,
    visit_ENew = #visit_ENew record,
    visit_ERead = #visit_ERead record,
    visit_EAppI = #visit_EAppI record,
    visit_EAscTime = #visit_EAscTime record,
    visit_var = #visit_var record,
    visit_cvar = #visit_cvar record,
    visit_mod_id = #visit_mod_id record,
    visit_idx = #visit_idx record,
    visit_sort = #visit_sort record,
    visit_mtype = #visit_mtype record,
    visit_ptrn_constr_tag = #visit_ptrn_constr_tag record,
    extend_i = #extend_i record,
    extend_t = #extend_t record,
    extend_c = #extend_c record,
    extend_e = #extend_e record
  }

fun override_visit_DRec (record : ('this, 'env) expr_visitor_vtable) new : ('this, 'env) expr_visitor_vtable =
  {
    visit_expr = #visit_expr record,
    visit_EVar = #visit_EVar record,
    visit_EConst = #visit_EConst record,
    visit_EUnOp = #visit_EUnOp record,
    visit_EBinOp = #visit_EBinOp record,
    visit_ETriOp = #visit_ETriOp record,
    visit_EEI = #visit_EEI record,
    visit_EET = #visit_EET record,
    visit_ET = #visit_ET record,
    visit_EAbs = #visit_EAbs record,
    visit_EAbsI = #visit_EAbsI record,
    visit_EAppConstr = #visit_EAppConstr record,
    visit_ECase = #visit_ECase record,
    visit_ELet = #visit_ELet record,
    visit_EAppT = #visit_EAppT record,
    visit_EAsc = #visit_EAsc record,
    visit_decl = #visit_decl record,
    visit_DVal = #visit_DVal record,
    visit_DValPtrn = #visit_DValPtrn record,
    visit_DRec = new,
    visit_DIdxDef = #visit_DIdxDef record,
    visit_DAbsIdx2 = #visit_DAbsIdx2 record,
    visit_DAbsIdx = #visit_DAbsIdx record,
    visit_DTypeDef = #visit_DTypeDef record,
    visit_DOpen = #visit_DOpen record,
    visit_ptrn = #visit_ptrn record,
    visit_VarP = #visit_VarP record,
    visit_TTP = #visit_TTP record,
    visit_PairP = #visit_PairP record,
    visit_AliasP = #visit_AliasP record,
    visit_ConstrP = #visit_ConstrP record,
    visit_AnnoP = #visit_AnnoP record,
    visit_EApp = #visit_EApp record,
    visit_EPair = #visit_EPair record,
    visit_EAdd = #visit_EAdd record,
    visit_ENew = #visit_ENew record,
    visit_ERead = #visit_ERead record,
    visit_EAppI = #visit_EAppI record,
    visit_EAscTime = #visit_EAscTime record,
    visit_var = #visit_var record,
    visit_cvar = #visit_cvar record,
    visit_mod_id = #visit_mod_id record,
    visit_idx = #visit_idx record,
    visit_sort = #visit_sort record,
    visit_mtype = #visit_mtype record,
    visit_ptrn_constr_tag = #visit_ptrn_constr_tag record,
    extend_i = #extend_i record,
    extend_t = #extend_t record,
    extend_c = #extend_c record,
    extend_e = #extend_e record
  }

fun override_visit_DTypeDef (record : ('this, 'env) expr_visitor_vtable) new : ('this, 'env) expr_visitor_vtable =
  {
    visit_expr = #visit_expr record,
    visit_EVar = #visit_EVar record,
    visit_EConst = #visit_EConst record,
    visit_EUnOp = #visit_EUnOp record,
    visit_EBinOp = #visit_EBinOp record,
    visit_ETriOp = #visit_ETriOp record,
    visit_EEI = #visit_EEI record,
    visit_EET = #visit_EET record,
    visit_ET = #visit_ET record,
    visit_EAbs = #visit_EAbs record,
    visit_EAbsI = #visit_EAbsI record,
    visit_EAppConstr = #visit_EAppConstr record,
    visit_ECase = #visit_ECase record,
    visit_ELet = #visit_ELet record,
    visit_EAppT = #visit_EAppT record,
    visit_EAsc = #visit_EAsc record,
    visit_decl = #visit_decl record,
    visit_DVal = #visit_DVal record,
    visit_DValPtrn = #visit_DValPtrn record,
    visit_DRec = #visit_DRec record,
    visit_DIdxDef = #visit_DIdxDef record,
    visit_DAbsIdx2 = #visit_DAbsIdx2 record,
    visit_DAbsIdx = #visit_DAbsIdx record,
    visit_DTypeDef = new,
    visit_DOpen = #visit_DOpen record,
    visit_ptrn = #visit_ptrn record,
    visit_VarP = #visit_VarP record,
    visit_TTP = #visit_TTP record,
    visit_PairP = #visit_PairP record,
    visit_AliasP = #visit_AliasP record,
    visit_ConstrP = #visit_ConstrP record,
    visit_AnnoP = #visit_AnnoP record,
    visit_EApp = #visit_EApp record,
    visit_EPair = #visit_EPair record,
    visit_EAdd = #visit_EAdd record,
    visit_ENew = #visit_ENew record,
    visit_ERead = #visit_ERead record,
    visit_EAppI = #visit_EAppI record,
    visit_EAscTime = #visit_EAscTime record,
    visit_var = #visit_var record,
    visit_cvar = #visit_cvar record,
    visit_mod_id = #visit_mod_id record,
    visit_idx = #visit_idx record,
    visit_sort = #visit_sort record,
    visit_mtype = #visit_mtype record,
    visit_ptrn_constr_tag = #visit_ptrn_constr_tag record,
    extend_i = #extend_i record,
    extend_t = #extend_t record,
    extend_c = #extend_c record,
    extend_e = #extend_e record
  }

fun override_visit_DOpen (record : ('this, 'env) expr_visitor_vtable) new : ('this, 'env) expr_visitor_vtable =
  {
    visit_expr = #visit_expr record,
    visit_EVar = #visit_EVar record,
    visit_EConst = #visit_EConst record,
    visit_EUnOp = #visit_EUnOp record,
    visit_EBinOp = #visit_EBinOp record,
    visit_ETriOp = #visit_ETriOp record,
    visit_EEI = #visit_EEI record,
    visit_EET = #visit_EET record,
    visit_ET = #visit_ET record,
    visit_EAbs = #visit_EAbs record,
    visit_EAbsI = #visit_EAbsI record,
    visit_EAppConstr = #visit_EAppConstr record,
    visit_ECase = #visit_ECase record,
    visit_ELet = #visit_ELet record,
    visit_EAppT = #visit_EAppT record,
    visit_EAsc = #visit_EAsc record,
    visit_decl = #visit_decl record,
    visit_DVal = #visit_DVal record,
    visit_DValPtrn = #visit_DValPtrn record,
    visit_DRec = #visit_DRec record,
    visit_DIdxDef = #visit_DIdxDef record,
    visit_DAbsIdx2 = #visit_DAbsIdx2 record,
    visit_DAbsIdx = #visit_DAbsIdx record,
    visit_DTypeDef = #visit_DTypeDef record,
    visit_DOpen = new,
    visit_ptrn = #visit_ptrn record,
    visit_VarP = #visit_VarP record,
    visit_TTP = #visit_TTP record,
    visit_PairP = #visit_PairP record,
    visit_AliasP = #visit_AliasP record,
    visit_ConstrP = #visit_ConstrP record,
    visit_AnnoP = #visit_AnnoP record,
    visit_EApp = #visit_EApp record,
    visit_EPair = #visit_EPair record,
    visit_EAdd = #visit_EAdd record,
    visit_ENew = #visit_ENew record,
    visit_ERead = #visit_ERead record,
    visit_EAppI = #visit_EAppI record,
    visit_EAscTime = #visit_EAscTime record,
    visit_var = #visit_var record,
    visit_cvar = #visit_cvar record,
    visit_mod_id = #visit_mod_id record,
    visit_idx = #visit_idx record,
    visit_sort = #visit_sort record,
    visit_mtype = #visit_mtype record,
    visit_ptrn_constr_tag = #visit_ptrn_constr_tag record,
    extend_i = #extend_i record,
    extend_t = #extend_t record,
    extend_c = #extend_c record,
    extend_e = #extend_e record
  }

type ('this, 'env) expr_visitor_interface =
     ('this, 'env) expr_visitor_vtable
                                       
(***************** the default visitor  **********************)    

open VisitorUtil
       
(* val visit_ibind = Unbound.visit_bind_simp *)
(* val visit_tbind = Unbound.visit_bind_simp *)
(* val visit_ebind = Unbound.visit_bind_simp *)

structure PV = PatternVisitor
       
fun default_expr_visitor_vtable
      (cast : 'this -> ('this, 'env) expr_visitor_interface)
      extend_i
      extend_t
      extend_c
      extend_e
      visit_var
      visit_cvar
      visit_mod_id
      visit_idx
      visit_sort
      visit_mtype
      visit_ptrn_constr_tag
    : ('this, 'env) expr_visitor_vtable =
  let
    fun visit_expr this env data =
      let
        val vtable = cast this
      in
        case data of
	    EVar data => #visit_EVar vtable this env data
          | EConst data => #visit_EConst vtable this env data
          | EUnOp data => #visit_EUnOp vtable this env data
          | EBinOp data => #visit_EBinOp vtable this env data
	  | ETriOp data => #visit_ETriOp vtable this env data
          | EEI data => #visit_EEI vtable this env data
          | EET data => #visit_EET vtable this env data
          | ET data => #visit_ET vtable this env data
	  | EAbs data => #visit_EAbs vtable this env data
	  | EAbsI data => #visit_EAbsI vtable this env data
	  | EAppConstr data => #visit_EAppConstr vtable this env data
	  | ECase data => #visit_ECase vtable this env data
	  | ELet data => #visit_ELet vtable this env data
      end
    fun visit_EVar this env data =
      let
        val vtable = cast this
        val (var, eia) = data
        val var = #visit_var vtable this env var
      in
        T.EVar (var, eia)
      end
    fun visit_EConst this env data =
      let
        val vtable = cast this
      in
        T.EConst data
      end
    fun visit_EUnOp this env data =
      let
        val vtable = cast this
        val (opr, e, r) = data
        val e = #visit_expr vtable this env e
      in
        T.EUnOp (opr, e, r)
      end
    fun visit_EBinOp this env data =
      let
        val vtable = cast this
        val (opr, e1, e2) = data
        val data = (e1, e2)
      in
        case opr of
            EBApp => #visit_EApp vtable this env data
          | EBPair => #visit_EPair vtable this env data
          | EBAdd => #visit_EAdd vtable this env data
          | EBNew => #visit_ENew vtable this env data
          | EBRead => #visit_ERead vtable this env data
      end
    fun visit_EApp this env data =
      let
        val vtable = cast this
        val (e1, e2) = data
        val e1 = #visit_expr vtable this env e1
        val e2 = #visit_expr vtable this env e2
      in
        T.EBinOp (EBApp, e1, e2)
      end
    fun visit_EPair this env data =
      let
        val vtable = cast this
        val (e1, e2) = data
        val e1 = #visit_expr vtable this env e1
        val e2 = #visit_expr vtable this env e2
      in
        T.EBinOp (EBPair, e1, e2)
      end
    fun visit_EAdd this env data =
      let
        val vtable = cast this
        val (e1, e2) = data
        val e1 = #visit_expr vtable this env e1
        val e2 = #visit_expr vtable this env e2
      in
        T.EBinOp (EBAdd, e1, e2)
      end
    fun visit_ENew this env data =
      let
        val vtable = cast this
        val (e1, e2) = data
        val e1 = #visit_expr vtable this env e1
        val e2 = #visit_expr vtable this env e2
      in
        T.EBinOp (EBNew, e1, e2)
      end
    fun visit_ERead this env data =
      let
        val vtable = cast this
        val (e1, e2) = data
        val e1 = #visit_expr vtable this env e1
        val e2 = #visit_expr vtable this env e2
      in
        T.EBinOp (EBRead, e1, e2)
      end
    fun visit_ETriOp this env data =
      let
        val vtable = cast this
        val (opr, e1, e2, e3) = data
        val e1 = #visit_expr vtable this env e1
        val e2 = #visit_expr vtable this env e2
        val e3 = #visit_expr vtable this env e3
      in
        T.ETriOp (opr, e1, e2, e3)
      end
    fun visit_EEI this env data = 
      let
        val vtable = cast this
        val (opr, e, i) = data
        val data = (e, i)
      in
        case opr of
	    EEIAppI => #visit_EAppI vtable this env data
	  | EEIAscTime => #visit_EAscTime vtable this env data
      end
    fun visit_EAppI this env data = 
      let
        val vtable = cast this
        val (e, i) = data
        val e = #visit_expr vtable this env e
        val i = #visit_idx vtable this env i
      in
        T.EEI (EEIAppI, e, i)
      end
    fun visit_EAscTime this env data = 
      let
        val vtable = cast this
        val (e, i) = data
        val e = #visit_expr vtable this env e
        val i = #visit_idx vtable this env i
      in
        T.EEI (EEIAscTime, e, i)
      end
    fun visit_EET this env data = 
      let
        val vtable = cast this
        val (opr, e, t) = data
        val data = (e, t)
      in
        case opr of
	    EETAppT => #visit_EAppT vtable this env data
	  | EETAsc => #visit_EAsc vtable this env data
      end
    fun visit_EAppT this env data = 
      let
        val vtable = cast this
        val (e, t) = data
        val e = #visit_expr vtable this env e
        val t = #visit_mtype vtable this env t
      in
        T.EET (EETAppT, e, t)
      end
    fun visit_EAsc this env data = 
      let
        val vtable = cast this
        val (e, t) = data
        val e = #visit_expr vtable this env e
        val t = #visit_mtype vtable this env t
      in
        T.EET (EETAsc, e, t)
      end
    fun visit_ET this env data = 
      let
        val vtable = cast this
        val (opr, t, r) = data
        val t = #visit_mtype vtable this env t
      in
        T.ET (opr, t, r)
      end
    fun visit_EAbs this env data =
      let
        val vtable = cast this
        val data = visit_bind (#visit_ptrn vtable this) (#visit_expr vtable this) env data
      in
        T.EAbs data
      end
    fun visit_ibind_anno this = visit_bind_anno (#extend_i (cast this) this)
    fun visit_EAbsI this env data =
      let
        val vtable = cast this
        val (bind, r) = data
        val bind = visit_ibind_anno this (#visit_sort vtable this) (#visit_expr vtable this) env bind
      in
        T.EAbsI (bind, r)
      end
    fun visit_EAppConstr this env data = 
      let
        val vtable = cast this
        val ((var, eia), ts, is, e, ot) = data
        val var = #visit_cvar vtable this env var
        val ts = map (#visit_mtype vtable this env) ts
        val is = map (#visit_idx vtable this env) is
        val e = #visit_expr vtable this env e
        val ot = Option.map (mapSnd (#visit_mtype vtable this env)) ot
      in
        T.EAppConstr ((var, eia), ts, is, e, ot)
      end
    fun visit_return this env (t, i) =
      let
        val vtable = cast this
        val t = Option.map (#visit_mtype vtable this env) t                                      
        val i = Option.map (#visit_idx vtable this env) i                                     
      in
        (t, i)
      end
    fun visit_ECase this env data =
      let
        val vtable = cast this
        val (e, return, binds, r) = data
        val e = #visit_expr vtable this env e
        val return = visit_return this env return
        val binds = map (visit_bind (#visit_ptrn vtable this) (#visit_expr vtable this) env) binds
      in
        T.ECase (e, return, binds, r)
      end
    fun visit_ELet this env data =
      let
        val vtable = cast this
        val (return, bind, r) = data
        val return = visit_return this env return
        val bind = visit_bind (visit_tele (#visit_decl vtable this)) (#visit_expr vtable this) env bind
      in
        T.ELet (return, bind, r)
      end
    fun visit_decl this env data =
      let
        val vtable = cast this
      in
        case data of
            DVal data => #visit_DVal vtable this env data
          | DValPtrn data => #visit_DValPtrn vtable this env data
          | DRec data => #visit_DRec vtable this env data
          | DIdxDef data => #visit_DIdxDef vtable this env data
          | DAbsIdx2 data => #visit_DAbsIdx2 vtable this env data
          | DAbsIdx data => #visit_DAbsIdx vtable this env data
          | DTypeDef data => #visit_DTypeDef vtable this env data
          | DOpen data => #visit_DOpen vtable this env data
      end
    fun visit_ibinder this env name =
      let
        val vtable = cast this
        val name = visit_binder (#extend_i vtable this) env name
      in
        name
      end
    fun visit_tbinder this env name =
      let
        val vtable = cast this
        val name = visit_binder (#extend_t vtable this) env name
      in
        name
      end
    fun visit_cbinder this env name =
      let
        val vtable = cast this
        val name = visit_binder (#extend_c vtable this) env name
      in
        name
      end
    fun visit_ebinder this env name =
      let
        val vtable = cast this
        val name = visit_binder (#extend_e vtable this) env name
      in
        name
      end
    fun visit_DVal this env data =
      let
        val vtable = cast this
        val (name, bind, r) = data
        val name = visit_ebinder this env name
        val bind = visit_outer (visit_bind (visit_list (visit_tbinder this)) (#visit_expr vtable this)) env bind
      in
        T.DVal (name, bind, r)
      end
    fun visit_DValPtrn this env data =
      let
        val vtable = cast this
        val (pn, e, r) = data
        val pn = #visit_ptrn vtable this env pn
        val e = visit_outer (#visit_expr vtable this) env e
      in
        T.DValPtrn (pn, e, r)
      end
    fun visit_stbind this env data =
      let
        val vtable = cast this
      in
        case data of
            SortingST data => T.SortingST $ visit_pair (visit_ibinder this) (visit_outer (#visit_sort vtable this)) env data
          | TypingST pn => T.TypingST $ #visit_ptrn vtable this env pn
      end
    fun visit_DRec this env data =
      let
        val vtable = cast this
        val (name, bind, r) = data
        val name = visit_ebinder this env name
        val bind =
            visit_inner (
              visit_bind (visit_pair (visit_list (visit_tbinder this))
                                     (visit_rebind (visit_tele (visit_stbind this))))
                         (visit_pair (visit_pair (#visit_mtype vtable this)
                                                 (#visit_idx vtable this))
                                     (#visit_expr vtable this))) env bind
      in
        T.DRec (name, bind, r)
      end
    fun visit_DIdxDef this env data =
      let
        val vtable = cast this
        val (name, s, i) = data
        val name = visit_ibinder this env name
        val s = visit_outer (#visit_sort vtable this) env s
        val i = visit_outer (#visit_idx vtable this) env i
      in
        T.DIdxDef (name, s, i)
      end
    fun visit_DAbsIdx2 this env data =
      let
        val vtable = cast this
        val (name, s, i) = data
        val name = visit_ibinder this env name
        val s = visit_outer (#visit_sort vtable this) env s
        val i = visit_outer (#visit_idx vtable this) env i
      in
        T.DAbsIdx2 (name, s, i)
      end
    fun visit_DAbsIdx this env data =
      let
        val vtable = cast this
        val ((name, s, i), decls, r) = data
        val name = visit_ibinder this env name
        val s = visit_outer (#visit_sort vtable this) env s
        val i = visit_outer (#visit_idx vtable this) env i
        val decls = visit_rebind (visit_tele (#visit_decl vtable this)) env decls
      in
        T.DAbsIdx ((name, s, i), decls, r)
      end
    fun visit_DTypeDef this env data =
      let
        val vtable = cast this
        val (name, t) = data
        val name = visit_tbinder this env name
        val t = visit_outer (#visit_mtype vtable this) env t
      in
        T.DTypeDef (name, t)
      end
    fun visit_scoping_ctx this env (sctx, kctx, cctx, tctx) =
      let
        val _ = visit_list (visit_ibinder this) env $ rev sctx
        val _ = visit_list (visit_tbinder this) env $ rev kctx
        val _ = visit_list (visit_cbinder this) env $ rev cctx
        val _ = visit_list (visit_ebinder this) env $ rev tctx
      in
        (sctx, kctx, cctx, tctx)
      end
    fun visit_DOpen this env data =
      let
        val vtable = cast this
        val (m, scp) = data
        val m = visit_outer (#visit_mod_id vtable this) env m
        val scp = Option.map (visit_scoping_ctx this env) scp
      in
        T.DOpen (m, scp)
      end
    fun visit_cvar_tag this env data =
      let
        val vtable = cast this
      in
        visit_pair (#visit_cvar vtable this) (#visit_ptrn_constr_tag vtable this) env data
      end
    fun this_impls_ptrn_visitor_interface this :
        ('this, 'env, cvar * ptrn_constr_tag, mtype, T.cvar * T.ptrn_constr_tag, T.mtype) PV.ptrn_visitor_interface =
      let
        val vtable = cast this
      in
        {
          visit_ptrn = #visit_ptrn vtable,
          visit_VarP = #visit_VarP vtable,
          visit_TTP = #visit_TTP vtable,
          visit_PairP = #visit_PairP vtable,
          visit_AliasP = #visit_AliasP vtable,
          visit_AnnoP = #visit_AnnoP vtable,
          visit_ConstrP = #visit_ConstrP vtable,
          visit_cvar = visit_cvar_tag,
          visit_mtype = #visit_mtype vtable,
          extend_i = #extend_i vtable,
          extend_e = #extend_e vtable
        }
      end
    val pv_vtable =
        PV.default_ptrn_visitor_vtable
          this_impls_ptrn_visitor_interface
          extend_i
          extend_e
          visit_cvar_tag
          visit_mtype
    (* fun visit_ptrn this env data = *)
    (*   let *)
    (*     val vtable = cast this *)
    (*   in *)
    (*     case data of *)
    (*         VarP data => #visit_VarP vtable this env data *)
    (*       | TTP data => #visit_TTP vtable this env data *)
    (*       | PairP data => #visit_PairP vtable this env data *)
    (*       | AliasP data => #visit_AliasP vtable this env data *)
    (*       | ConstrP data => #visit_ConstrP vtable this env data *)
    (*       | AnnoP data => #visit_AnnoP vtable this env data *)
    (*   end *)
    (* fun visit_VarP this env data = *)
    (*   let *)
    (*     val vtable = cast this *)
    (*   in *)
    (*     VarP $ visit_ebinder this env data *)
    (*   end *)
    (* fun visit_TTP this env data = *)
    (*   TTP data *)
    (* fun visit_PairP this env data =  *)
    (*   let *)
    (*     val vtable = cast this *)
    (*     val (p1, p2) = data *)
    (*     val p1 = #visit_ptrn vtable this env p1 *)
    (*     val p2 = #visit_ptrn vtable this env p2 *)
    (*   in *)
    (*     PairP (p1, p2) *)
    (*   end *)
    (* fun visit_AliasP this env data = *)
    (*   let *)
    (*     val vtable = cast this *)
    (*     val (name, p, r) = data *)
    (*     val name = visit_ebinder this env name *)
    (*     val p = #visit_ptrn vtable this env p *)
    (*   in *)
    (*     AliasP (name, p, r) *)
    (*   end *)
    (* fun visit_AnnoP this env data =  *)
    (*   let *)
    (*     val vtable = cast this *)
    (*     val (p, t) = data *)
    (*     val p = #visit_ptrn vtable this env p *)
    (*     val t = visit_outer (#visit_mtype vtable this) env t *)
    (*   in *)
    (*     AnnoP (p, t) *)
    (*   end *)
    (* fun visit_ConstrP this env data = *)
    (*   let *)
    (*     val vtable = cast this *)
    (*     val (x, inames, p, r) = data *)
    (*     val x = visit_outer (visit_pair (visit_pair (#visit_cvar vtable this) (#visit_ptrn_constr_tag vtable this)) return2) env x *)
    (*     val inames = map (visit_ibinder this env) inames *)
    (*     val p = #visit_ptrn vtable this env p *)
    (*   in *)
    (*     ConstrP (x, inames, p, r) *)
    (*   end *)
  in
    {
      visit_expr = visit_expr,
      visit_EVar = visit_EVar,
      visit_EConst = visit_EConst,
      visit_EUnOp = visit_EUnOp,
      visit_EBinOp = visit_EBinOp,
      visit_ETriOp = visit_ETriOp,
      visit_EEI = visit_EEI,
      visit_EET = visit_EET,
      visit_ET = visit_ET,
      visit_EAbs = visit_EAbs,
      visit_EAbsI = visit_EAbsI,
      visit_EAppConstr = visit_EAppConstr,
      visit_ECase = visit_ECase,
      visit_ELet = visit_ELet,
      visit_decl = visit_decl,
      visit_DVal = visit_DVal,
      visit_DValPtrn = visit_DValPtrn,
      visit_DRec = visit_DRec,
      visit_DIdxDef = visit_DIdxDef,
      visit_DAbsIdx2 = visit_DAbsIdx2,
      visit_DAbsIdx = visit_DAbsIdx,
      visit_DTypeDef = visit_DTypeDef,
      visit_DOpen = visit_DOpen,
      
      (* visit_ptrn = visit_ptrn, *)
      (* visit_VarP = visit_VarP, *)
      (* visit_TTP = visit_TTP, *)
      (* visit_PairP = visit_PairP, *)
      (* visit_AliasP = visit_AliasP, *)
      (* visit_AnnoP = visit_AnnoP, *)
      (* visit_ConstrP = visit_ConstrP, *)
      visit_ptrn = #visit_ptrn pv_vtable,
      visit_VarP = #visit_VarP pv_vtable,
      visit_TTP = #visit_TTP pv_vtable,
      visit_PairP = #visit_PairP pv_vtable,
      visit_AliasP = #visit_AliasP pv_vtable,
      visit_AnnoP = #visit_AnnoP pv_vtable,
      visit_ConstrP = #visit_ConstrP pv_vtable,
      
      visit_EApp = visit_EApp,
      visit_EPair = visit_EPair,
      visit_EAdd = visit_EAdd,
      visit_ENew = visit_ENew,
      visit_ERead = visit_ERead,
      visit_EAppT = visit_EAppT,
      visit_EAsc = visit_EAsc,
      visit_EAppI = visit_EAppI,
      visit_EAscTime = visit_EAscTime,
      visit_var = visit_var,
      visit_cvar = visit_cvar,
      visit_mod_id = visit_mod_id,
      visit_idx = visit_idx,
      visit_sort = visit_sort,
      visit_mtype = visit_mtype,
      visit_ptrn_constr_tag = visit_ptrn_constr_tag,
      extend_i = extend_i,
      extend_t = extend_t,
      extend_c = extend_c,
      extend_e = extend_e
    }
  end

datatype 'env expr_visitor =
         ExprVisitor of ('env expr_visitor, 'env) expr_visitor_interface

fun expr_visitor_impls_interface (this : 'env expr_visitor) :
    ('env expr_visitor, 'env) expr_visitor_interface =
  let
    val ExprVisitor vtable = this
  in
    vtable
  end

fun new_expr_visitor vtable params =
  let
    val vtable = vtable expr_visitor_impls_interface params
  in
    ExprVisitor vtable
  end
    
fun visit_decls visitor ctx decls =
  let
    val ExprVisitor vtable = visitor
    val decls = unTeles $ visit_tele (#visit_decl vtable visitor) ctx $ Teles decls
  in
    decls
  end
    
end
