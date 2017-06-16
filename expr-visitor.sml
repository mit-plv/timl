structure ExprVisitor = struct

open Expr
       
type ('this, 'env) expr_visitor_vtable =
     {
       visit_expr : 'this -> 'env -> expr -> expr,
       visit_Var : 'this -> 'env -> 'var -> expr,
       visit_EAppI : 'this -> 'env -> expr * 'idx -> expr,
       visit_EMatchSum : 'this -> 'env -> expr * expr ebind list -> expr,
       visit_EMatchPair : 'this -> 'env -> expr * expr ebind ebind -> expr,
       visit_EMatchUnfold : 'this -> 'env -> expr * expr ebind -> expr,
       visit_EMatchUnpackI : 'this -> 'env -> expr * expr ebind ibind -> expr,
       visit_var : 'this -> 'env -> 'var -> 'var2,
       (* visit_bsort : 'this -> 'env -> 'bsort -> 'bsort2, *)
       visit_idx : 'this -> 'env -> 'idx -> 'idx2,
       (* visit_sort : 'this -> 'env -> 'sort -> 'sort2, *)
       (* visit_region : 'this -> 'env -> region -> region, *)
       extend_i : 'this -> 'env -> iname -> 'env,
       extend_e : 'this -> 'env -> ename -> 'env
     }
       
type ('this, 'env) expr_visitor_interface =
     ('this, 'env) expr_visitor_vtable
                                       
fun override_visit_EVar (record : ('this, 'env) expr_visitor_vtable) new : ('this, 'env) expr_visitor_vtable =
  {
    visit_expr = #visit_expr record,
    visit_EVar = new,
    visit_EAppI = #visit_EAppI record,
    visit_EMatchSum = #visit_EMatchSum record,
    visit_EMatchPair = #visit_EMatchPair record,
    visit_EMatchUnfold = #visit_EMatchUnfold record,
    visit_EMatchUnpackI = #visit_EMatchUnpackI record,
    visit_var = #visit_var record,
    visit_idx = #visit_idx record,
    extend_i = #extend_i record,
    extend_e = #extend_e record
  }

(***************** the default visitor  **********************)    

open VisitorUtil
       
val visit_ibind = Unbound.visit_bind_simp
val visit_tbind = Unbound.visit_bind_simp
val visit_ebind = Unbound.visit_bind_simp
                    
fun default_expr_visitor_vtable
      (cast : 'this -> ('this, 'env) expr_visitor_interface)
      extend_i
      extend_e
      visit_var
      visit_idx
    : ('this, 'env) expr_visitor_vtable =
  let
    fun visit_expr this env data =
      let
        val vtable = cast this
      in
        case data of
            EVar data => #visit_EVar vtable this env data
          | EAppI data => #visit_EAppI vtable this env data
          | _ => raise Unimpl ""
      end
    fun visit_EVar this env data =
      let
        val vtable = cast this
        val (var, eia) = data
        val var = #visit_var vtable this var
      in
        EVar (var, eia)
      end
    fun visit_EConst this env data =
      let
        val vtable = cast this
      in
        EConst data
      end
    fun visit_EUnOp this env data =
      let
        val vtable = cast this
        val (opr, e, r) = data
        val e = #visit_expr vtable this env e
      in
        EUnOp (opr, e, r)
      end
    fun visit_EBinOp this env data =
      let
        val vtable = cast this
        val (opr, e1, e2) = data
        val e1 = #visit_expr vtable this env e1
        val e2 = #visit_expr vtable this env e2
      in
        EBinOp (opr, e1, e2)
      end
    fun visit_ETriOp this env data =
      let
        val vtable = cast this
        val (opr, e1, e2, e3) = data
        val e1 = #visit_expr vtable this env e1
        val e2 = #visit_expr vtable this env e2
        val e3 = #visit_expr vtable this env e3
      in
        ETriOp (opr, e1, e2, e3)
      end
    fun visit_EEI this env data = 
      let
        val vtable = cast this
        val (opr, e, i) = data
        val e = #visit_expr vtable this env e
        val i = #visit_idx vtable this env i
      in
        EEI (opr, e, i)
      end
    fun visit_EAbsI this env data =
      let
        val vtable = cast this
        val (bind, r) = data
        val bind = visit_bind_anno (#extend_i vtable this) (#visit_sort vtable this env) (#visit_expr vtable this) env bind
      in
        EAbsI (bind, r)
      end
datatype expr =
	 EVar of long_id * bool(*explicit index arguments (EIA)*)
         | EConst of expr_const * region
         | EUnOp of expr_un_op * expr * region
         | EBinOp of bin_op * expr * expr
	 | ETriOp of tri_op * expr * expr * expr
         | EEI of expr_EI * expr * idx
         | ET of expr_T * mtype * region
	 | EAbs of (ptrn, expr) bind
	 | EAbsI of (sort, expr) ibind_anno * region
	 | EAppConstr of (long_id * bool) * idx list * expr
	 | ECase of expr * return * (ptrn, expr) bind list * region
	 | ELet of return * (decl tele, expr) bind * region
	 | EAscription of expr * mtype


     and decl =
         DVal of ename binder * (tname binder list, expr) bind outer * region outer
         | DValPtrn of ptrn * expr outer * region outer
         | DRec of ename binder * (tname binder list * stbind tele rebind, (mtype * idx) * expr) bind inner * region outer
	 | DDatatype of mtype datatype_def * region outer
         | DIdxDef of iname binder * sort outer * idx outer
         | DAbsIdx2 of iname binder * sort outer * idx outer
         | DAbsIdx of (iname binder * sort outer * idx outer) * decl tele rebind * region outer
         | DTypeDef of tname binder * mtype outer
         | DOpen of mod_projectible outer * scoping_ctx option

    fun visit_EAbs this env data =
      let
        val vtable = cast this
        val (bind, r) = data
        val bind = visit_bind_anno (#extend_i vtable this) (#visit_sort vtable this env) (#visit_expr vtable this) env bind
      in
        EAbs (bind, r)
      end
    (* fun default_visit_binder extend this = visit_binder (extend this) *)
    val visit_ebind = fn this => visit_ebind (#extend_e (cast this) this)
    val visit_ibind = fn this => visit_ibind (#extend_i (cast this) this)
    fun visit_EMatchSum this env data =
      let
        val vtable = cast this
        val (e, branches) = data
        val e = #visit_expr vtable this env e
        val branches = (visit_list o visit_ebind this) (#visit_expr vtable this) env branches
      in
        EMatchSum (e, branches)
      end
    fun visit_EMatchPair this env data =
      let
        val vtable = cast this
        val (e, branch) = data
        val e = #visit_expr vtable this env e
        val branch = (visit_ebind this o visit_ebind this) (#visit_expr vtable this) env branch
      in
        EMatchPair (e, branch)
      end
    fun visit_EMatchUnfold this env data =
      let
        val vtable = cast this
        val (e, branch) = data
        val e = #visit_expr vtable this env e
        val branch = visit_ebind this (#visit_expr vtable this) env branch
      in
        EMatchUnfold (e, branch)
      end
    fun visit_EMatchUnpackI this env data =
      let
        val vtable = cast this
        val (e, branch) = data
        val e = #visit_expr vtable this env e
        val branch = (visit_ibind this o visit_ebind this) (#visit_expr vtable this) env branch
      in
        EMatchUnpackI (e, branch)
      end
  in
    {
      visit_expr = visit_expr,
      visit_EVar = visit_EVar,
      visit_EAppI = visit_EAppI,
      visit_EMatchSum = visit_EMatchSum,
      visit_EMatchPair = visit_EMatchPair,
      visit_EMatchUnfold = visit_EMatchUnfold,
      visit_EMatchUnpackI = visit_EMatchUnpackI,
      visit_var = visit_var,
      visit_idx = visit_idx,
      extend_i = extend_i,
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
    
end
