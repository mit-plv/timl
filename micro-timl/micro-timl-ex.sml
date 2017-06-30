(* micro-timl extended *)

structure MicroTiMLEx = struct

open MicroTiML
open Unbound
       
infixr 0 $
         
datatype ('var, 'idx, 'sort, 'kind, 'ty) expr =
         EVar of 'var
         | EConst of Operators.expr_const
         | ELoc of loc
         | EUnOp of 'ty expr_un_op * ('var, 'idx, 'sort, 'kind, 'ty) expr
         | EBinOp of expr_bin_op * ('var, 'idx, 'sort, 'kind, 'ty) expr * ('var, 'idx, 'sort, 'kind, 'ty) expr
         | EWrite of ('var, 'idx, 'sort, 'kind, 'ty) expr * ('var, 'idx, 'sort, 'kind, 'ty) expr * ('var, 'idx, 'sort, 'kind, 'ty) expr
         | ECase of ('var, 'idx, 'sort, 'kind, 'ty) expr * ('var, 'idx, 'sort, 'kind, 'ty) expr ebind * ('var, 'idx, 'sort, 'kind, 'ty) expr ebind
         | EAbs of ('ty, ('var, 'idx, 'sort, 'kind, 'ty) expr) ebind_anno
         | ERec of ('ty, ('var, 'idx, 'sort, 'kind, 'ty) expr) ebind_anno
         | EAbsT of ('kind, ('var, 'idx, 'sort, 'kind, 'ty) expr) tbind_anno
         | EAppT of ('var, 'idx, 'sort, 'kind, 'ty) expr * 'ty
         | EAbsI of ('sort, ('var, 'idx, 'sort, 'kind, 'ty) expr) ibind_anno
         | EAppI of ('var, 'idx, 'sort, 'kind, 'ty) expr * 'idx
         | EPack of 'ty * 'ty * ('var, 'idx, 'sort, 'kind, 'ty) expr
         | EUnpack of ('var, 'idx, 'sort, 'kind, 'ty) expr * ('var, 'idx, 'sort, 'kind, 'ty) expr ebind tbind
         | EPackI of 'ty * 'idx * ('var, 'idx, 'sort, 'kind, 'ty) expr
         | EPackIs of 'ty * 'idx list * ('var, 'idx, 'sort, 'kind, 'ty) expr
         | EUnpackI of ('var, 'idx, 'sort, 'kind, 'ty) expr * ('var, 'idx, 'sort, 'kind, 'ty) expr ebind ibind
         | EAscTime of ('var, 'idx, 'sort, 'kind, 'ty) expr * 'idx (* time ascription *)
         | EAscType of ('var, 'idx, 'sort, 'kind, 'ty) expr * 'ty (* type ascription *)
         | ENever of 'ty
         | ELet of ('var, 'idx, 'sort, 'kind, 'ty) expr * ('var, 'idx, 'sort, 'kind, 'ty) expr ebind
         | EMatchSum of ('var, 'idx, 'sort, 'kind, 'ty) expr * ('var, 'idx, 'sort, 'kind, 'ty) expr ebind list
         | EMatchPair of ('var, 'idx, 'sort, 'kind, 'ty) expr * ('var, 'idx, 'sort, 'kind, 'ty) expr ebind ebind
         | EMatchUnfold of ('var, 'idx, 'sort, 'kind, 'ty) expr * ('var, 'idx, 'sort, 'kind, 'ty) expr ebind
         | EMatchUnpackI of ('var, 'idx, 'sort, 'kind, 'ty) expr * ('var, 'idx, 'sort, 'kind, 'ty) expr ebind ibind

type ('this, 'env, 'var, 'idx, 'sort, 'kind, 'ty, 'var2, 'idx2, 'sort2, 'kind2, 'ty2) expr_visitor_vtable =
     {
       visit_expr : 'this -> 'env -> ('var, 'idx, 'sort, 'kind, 'ty) expr -> ('var2, 'idx2, 'sort2, 'kind2, 'ty2) expr,
       visit_EVar : 'this -> 'env -> 'var -> ('var2, 'idx2, 'sort2, 'kind2, 'ty2) expr,
       visit_EConst : 'this -> 'env -> Operators.expr_const -> ('var2, 'idx2, 'sort2, 'kind2, 'ty2) expr,
       visit_ELoc : 'this -> 'env -> loc -> ('var2, 'idx2, 'sort2, 'kind2, 'ty2) expr,
       visit_EUnOp : 'this -> 'env -> 'ty expr_un_op * ('var, 'idx, 'sort, 'kind, 'ty) expr -> ('var2, 'idx2, 'sort2, 'kind2, 'ty2) expr,
       visit_EBinOp : 'this -> 'env -> expr_bin_op * ('var, 'idx, 'sort, 'kind, 'ty) expr * ('var, 'idx, 'sort, 'kind, 'ty) expr -> ('var2, 'idx2, 'sort2, 'kind2, 'ty2) expr,
       visit_EWrite : 'this -> 'env -> ('var, 'idx, 'sort, 'kind, 'ty) expr * ('var, 'idx, 'sort, 'kind, 'ty) expr * ('var, 'idx, 'sort, 'kind, 'ty) expr -> ('var2, 'idx2, 'sort2, 'kind2, 'ty2) expr,
       visit_ECase : 'this -> 'env -> ('var, 'idx, 'sort, 'kind, 'ty) expr * ('var, 'idx, 'sort, 'kind, 'ty) expr ebind * ('var, 'idx, 'sort, 'kind, 'ty) expr ebind -> ('var2, 'idx2, 'sort2, 'kind2, 'ty2) expr,
       visit_EAbs : 'this -> 'env -> ('ty, ('var, 'idx, 'sort, 'kind, 'ty) expr) ebind_anno -> ('var2, 'idx2, 'sort2, 'kind2, 'ty2) expr,
       visit_ERec : 'this -> 'env -> ('ty, ('var, 'idx, 'sort, 'kind, 'ty) expr) ebind_anno -> ('var2, 'idx2, 'sort2, 'kind2, 'ty2) expr,
       visit_EAbsT : 'this -> 'env -> ('kind, ('var, 'idx, 'sort, 'kind, 'ty) expr) tbind_anno -> ('var2, 'idx2, 'sort2, 'kind2, 'ty2) expr,
       visit_EAppT : 'this -> 'env -> ('var, 'idx, 'sort, 'kind, 'ty) expr * 'ty -> ('var2, 'idx2, 'sort2, 'kind2, 'ty2) expr,
       visit_EAbsI : 'this -> 'env -> ('sort, ('var, 'idx, 'sort, 'kind, 'ty) expr) ibind_anno -> ('var2, 'idx2, 'sort2, 'kind2, 'ty2) expr,
       visit_EAppI : 'this -> 'env -> ('var, 'idx, 'sort, 'kind, 'ty) expr * 'idx -> ('var2, 'idx2, 'sort2, 'kind2, 'ty2) expr,
       visit_EPack : 'this -> 'env -> 'ty * 'ty * ('var, 'idx, 'sort, 'kind, 'ty) expr -> ('var2, 'idx2, 'sort2, 'kind2, 'ty2) expr,
       visit_EUnpack : 'this -> 'env -> ('var, 'idx, 'sort, 'kind, 'ty) expr * ('var, 'idx, 'sort, 'kind, 'ty) expr ebind tbind -> ('var2, 'idx2, 'sort2, 'kind2, 'ty2) expr,
       visit_EPackI : 'this -> 'env -> 'ty * 'idx * ('var, 'idx, 'sort, 'kind, 'ty) expr -> ('var2, 'idx2, 'sort2, 'kind2, 'ty2) expr,
       visit_EPackIs : 'this -> 'env -> 'ty * 'idx list * ('var, 'idx, 'sort, 'kind, 'ty) expr -> ('var2, 'idx2, 'sort2, 'kind2, 'ty2) expr,
       visit_EUnpackI : 'this -> 'env -> ('var, 'idx, 'sort, 'kind, 'ty) expr * ('var, 'idx, 'sort, 'kind, 'ty) expr ebind ibind -> ('var2, 'idx2, 'sort2, 'kind2, 'ty2) expr,
       visit_EAscTime : 'this -> 'env -> ('var, 'idx, 'sort, 'kind, 'ty) expr * 'idx (* time ascription *) -> ('var2, 'idx2, 'sort2, 'kind2, 'ty2) expr,
       visit_EAscType : 'this -> 'env -> ('var, 'idx, 'sort, 'kind, 'ty) expr * 'ty (* type ascription *) -> ('var2, 'idx2, 'sort2, 'kind2, 'ty2) expr,
       visit_ENever : 'this -> 'env -> 'ty -> ('var2, 'idx2, 'sort2, 'kind2, 'ty2) expr,
       visit_ELet : 'this -> 'env -> ('var, 'idx, 'sort, 'kind, 'ty) expr * ('var, 'idx, 'sort, 'kind, 'ty) expr ebind -> ('var2, 'idx2, 'sort2, 'kind2, 'ty2) expr,
       visit_EMatchSum : 'this -> 'env -> ('var, 'idx, 'sort, 'kind, 'ty) expr * ('var, 'idx, 'sort, 'kind, 'ty) expr ebind list -> ('var2, 'idx2, 'sort2, 'kind2, 'ty2) expr,
       visit_EMatchPair : 'this -> 'env -> ('var, 'idx, 'sort, 'kind, 'ty) expr * ('var, 'idx, 'sort, 'kind, 'ty) expr ebind ebind -> ('var2, 'idx2, 'sort2, 'kind2, 'ty2) expr,
       visit_EMatchUnfold : 'this -> 'env -> ('var, 'idx, 'sort, 'kind, 'ty) expr * ('var, 'idx, 'sort, 'kind, 'ty) expr ebind -> ('var2, 'idx2, 'sort2, 'kind2, 'ty2) expr,
       visit_EMatchUnpackI : 'this -> 'env -> ('var, 'idx, 'sort, 'kind, 'ty) expr * ('var, 'idx, 'sort, 'kind, 'ty) expr ebind ibind -> ('var2, 'idx2, 'sort2, 'kind2, 'ty2) expr,
       visit_var : 'this -> 'env -> 'var -> 'var2,
       visit_idx : 'this -> 'env -> 'idx -> 'idx2,
       visit_sort : 'this -> 'env -> 'sort -> 'sort2,
       visit_kind : 'this -> 'env -> 'kind -> 'kind2,
       visit_ty : 'this -> 'env -> 'ty -> 'ty2,
       extend_i : 'this -> 'env -> iname -> 'env,
       extend_t : 'this -> 'env -> tname -> 'env,
       extend_e : 'this -> 'env -> ename -> 'env
     }
       
type ('this, 'env, 'var, 'idx, 'sort, 'kind, 'ty, 'var2, 'idx2, 'sort2, 'kind2, 'ty2) expr_visitor_interface =
     ('this, 'env, 'var, 'idx, 'sort, 'kind, 'ty, 'var2, 'idx2, 'sort2, 'kind2, 'ty2) expr_visitor_vtable
                                       
fun override_visit_EVar (record : ('this, 'env, 'var, 'idx, 'sort, 'kind, 'ty, 'var2, 'idx2, 'sort2, 'kind2, 'ty2) expr_visitor_vtable) new : ('this, 'env, 'var, 'idx, 'sort, 'kind, 'ty, 'var2, 'idx2, 'sort2, 'kind2, 'ty2) expr_visitor_vtable =
  {
    visit_expr = #visit_expr record,
    visit_EVar = new,
    visit_EConst = #visit_EConst record,
    visit_ELoc = #visit_ELoc record,
    visit_EUnOp = #visit_EUnOp record,
    visit_EBinOp = #visit_EBinOp record,
    visit_EWrite = #visit_EWrite record,
    visit_ECase = #visit_ECase record,
    visit_EAbs = #visit_EAbs record,
    visit_ERec = #visit_ERec record,
    visit_EAbsT = #visit_EAbsT record,
    visit_EAppT = #visit_EAppT record,
    visit_EAbsI = #visit_EAbsI record,
    visit_EAppI = #visit_EAppI record,
    visit_EPack = #visit_EPack record,
    visit_EUnpack = #visit_EUnpack record,
    visit_EPackI = #visit_EPackI record,
    visit_EPackIs = #visit_EPackIs record,
    visit_EUnpackI = #visit_EUnpackI record,
    visit_EAscTime = #visit_EAscTime record,
    visit_EAscType = #visit_EAscType record,
    visit_ENever = #visit_ENever record,
    visit_ELet = #visit_ELet record,
    visit_EMatchSum = #visit_EMatchSum record,
    visit_EMatchPair = #visit_EMatchPair record,
    visit_EMatchUnfold = #visit_EMatchUnfold record,
    visit_EMatchUnpackI = #visit_EMatchUnpackI record,
    visit_var = #visit_var record,
    visit_idx = #visit_idx record,
    visit_sort = #visit_sort record,
    visit_kind = #visit_kind record,
    visit_ty = #visit_ty record,
    extend_i = #extend_i record,
    extend_t = #extend_t record,
    extend_e = #extend_e record
  }

(***************** the default visitor  **********************)    

open VisitorUtil
       
fun default_expr_visitor_vtable
      (cast : 'this -> ('this, 'env, 'var, 'idx, 'sort, 'kind, 'ty, 'var2, 'idx2, 'sort2, 'kind, 'ty2) expr_visitor_interface)
      extend_i
      extend_t
      extend_e
      visit_var
      visit_idx
      visit_sort
      visit_ty
    : ('this, 'env, 'var, 'idx, 'sort, 'kind, 'ty, 'var2, 'idx2, 'sort2, 'kind, 'ty2) expr_visitor_vtable =
  let
    fun visit_expr this env data =
      let
        val vtable = cast this
      in
        case data of
            EVar data => #visit_EVar vtable this env data
          | EConst data => #visit_EConst vtable this env data
          | ELoc data => #visit_ELoc vtable this env data
          | EUnOp data => #visit_EUnOp vtable this env data
          | EBinOp data => #visit_EBinOp vtable this env data
          | EWrite data => #visit_EWrite vtable this env data
          | ECase data => #visit_ECase vtable this env data
          | EAbs data => #visit_EAbs vtable this env data
          | ERec data => #visit_ERec vtable this env data
          | EAbsT data => #visit_EAbsT vtable this env data
          | EAppT data => #visit_EAppT vtable this env data
          | EAbsI data => #visit_EAbsI vtable this env data
          | EAppI data => #visit_EAppI vtable this env data
          | EPack data => #visit_EPack vtable this env data
          | EUnpack data => #visit_EUnpack vtable this env data
          | EPackI data => #visit_EPackI vtable this env data
          | EPackIs data => #visit_EPackIs vtable this env data
          | EUnpackI data => #visit_EUnpackI vtable this env data
          | EAscTime data => #visit_EAscTime vtable this env data
          | EAscType data => #visit_EAscType vtable this env data
          | ENever data => #visit_ENever vtable this env data
          | ELet data => #visit_ELet vtable this env data
          | EMatchSum data => #visit_EMatchSum vtable this env data
          | EMatchPair data => #visit_EMatchPair vtable this env data
          | EMatchUnfold data => #visit_EMatchUnfold vtable this env data
          | EMatchUnpackI data => #visit_EMatchUnpackI vtable this env data
      end
    fun visit_EVar this env data =
      let
        val vtable = cast this
      in
        EVar $ #visit_var vtable this env data
      end
    fun visit_EConst this env data = EConst data
    fun visit_ELoc this env data = ELoc data
    fun visit_un_op this env opr = 
      let
        val vtable = cast this
        fun on_t x = #visit_ty vtable this env x
      in
        case opr of
            EUProj opr => EUProj opr
          | EUInj (opr, t) => EUInj (opr, on_t t)
          | EUFold t => EUFold $ on_t t
          | EUUnfold => EUUnfold
      end
    fun visit_EUnOp this env data = 
      let
        val vtable = cast this
        val (opr, e) = data
        val opr = visit_un_op this env opr
        val e = #visit_expr vtable this env e
      in
        EUnOp (opr, e)
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
    fun visit_EWrite this env data = 
      let
        val vtable = cast this
        val (e1, e2, e3) = data
        val e1 = #visit_expr vtable this env e1
        val e2 = #visit_expr vtable this env e2
        val e3 = #visit_expr vtable this env e3
      in
        EWrite (e1, e2, e3)
      end
    fun visit_ibind this = visit_bind_simp (#extend_i (cast this) this)
    fun visit_tbind this = visit_bind_simp (#extend_t (cast this) this)
    fun visit_ebind this = visit_bind_simp (#extend_e (cast this) this)
    fun visit_ibind_anno this = visit_bind_anno (#extend_i (cast this) this)
    fun visit_tbind_anno this = visit_bind_anno (#extend_t (cast this) this)
    fun visit_ebind_anno this = visit_bind_anno (#extend_e (cast this) this)
    fun visit_ECase this env data =
      let
        val vtable = cast this
        val (e, e1, e2) = data
        val e = #visit_expr vtable this env e
        val e1 = visit_ebind this (#visit_expr vtable this) env e1
        val e2 = visit_ebind this (#visit_expr vtable this) env e2
      in
        ECase (e, e1, e2)
      end
    fun visit_EAbs this env data =
      let
        val vtable = cast this
        val data = visit_ebind_anno this (#visit_ty vtable this) (#visit_expr vtable this) env data
      in
        EAbs data
      end
    fun visit_ERec this env data =
      let
        val vtable = cast this
        val data = visit_ebind_anno this (#visit_ty vtable this) (#visit_expr vtable this) env data
      in
        ERec data
      end
    fun visit_EAbsT this env data =
      let
        val vtable = cast this
        val data = visit_tbind_anno this (#visit_kind vtable this) (#visit_expr vtable this) env data
      in
        EAbsT data
      end
    fun visit_EAppT this env data = 
      let
        val vtable = cast this
        val (e, t) = data
        val e = #visit_expr vtable this env e
        val t = #visit_ty vtable this env t
      in
        EAppT (e, t)
      end
    fun visit_EAbsI this env data =
      let
        val vtable = cast this
        val data = visit_ibind_anno this (#visit_sort vtable this) (#visit_expr vtable this) env data
      in
        EAbsI data
      end
    fun visit_EAppI this env data = 
      let
        val vtable = cast this
        val (e, i) = data
        val e = #visit_expr vtable this env e
        val i = #visit_idx vtable this env i
      in
        EAppI (e, i)
      end
    fun visit_EPack this env data = 
      let
        val vtable = cast this
        val (t_all, t, e) = data
        val t_all = #visit_ty vtable this env t_all
        val t = #visit_ty vtable this env t
        val e = #visit_expr vtable this env e
      in
        EPack (t_all, t, e)
      end
    fun visit_EUnpack this env data =
      let
        val vtable = cast this
        val (e, bind) = data
        val e = #visit_expr vtable this env e
        val bind = (visit_tbind this o visit_ebind this) (#visit_expr vtable this) env bind
      in
        EUnpack (e, bind)
      end
    fun visit_EPackI this env data = 
      let
        val vtable = cast this
        val (t, i, e) = data
        val t = #visit_ty vtable this env t
        val i = #visit_idx vtable this env i
        val e = #visit_expr vtable this env e
      in
        EPackI (t, i, e)
      end
    fun visit_EPackIs this env data = 
      let
        val vtable = cast this
        val (t, is, e) = data
        val t = #visit_ty vtable this env t
        val is = map (#visit_idx vtable this env) is
        val e = #visit_expr vtable this env e
      in
        EPackIs (t, is, e)
      end
    fun visit_EUnpackI this env data =
      let
        val vtable = cast this
        val (e, bind) = data
        val e = #visit_expr vtable this env e
        val bind = (visit_ibind this o visit_ebind this) (#visit_expr vtable this) env bind
      in
        EUnpackI (e, bind)
      end
    fun visit_EAscTime this env data = 
      let
        val vtable = cast this
        val (e, i) = data
        val e = #visit_expr vtable this env e
        val i = #visit_idx vtable this env i
      in
        EAscTime (e, i)
      end
    fun visit_EAscType this env data = 
      let
        val vtable = cast this
        val (e, t) = data
        val e = #visit_expr vtable this env e
        val t = #visit_ty vtable this env t
      in
        EAscType (e, t)
      end
    fun visit_ENever this env data = 
      let
        val vtable = cast this
        val data = #visit_ty vtable this env data
      in
        ENever data
      end
    fun visit_ELet this env data =
      let
        val vtable = cast this
        val (e, bind) = data
        val e = #visit_expr vtable this env e
        val bind = visit_ebind this (#visit_expr vtable this) env bind
      in
        ELet (e, bind)
      end
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
      visit_EConst = visit_EConst,
      visit_ELoc = visit_ELoc,
      visit_EUnOp = visit_EUnOp,
      visit_EBinOp = visit_EBinOp,
      visit_EWrite = visit_EWrite,
      visit_ECase = visit_ECase,
      visit_EAbs = visit_EAbs,
      visit_ERec = visit_ERec,
      visit_EAbsT = visit_EAbsT,
      visit_EAppT = visit_EAppT,
      visit_EAbsI = visit_EAbsI,
      visit_EAppI = visit_EAppI,
      visit_EPack = visit_EPack,
      visit_EUnpack = visit_EUnpack,
      visit_EPackI = visit_EPackI,
      visit_EPackIs = visit_EPackIs,
      visit_EUnpackI = visit_EUnpackI,
      visit_EAscTime = visit_EAscTime,
      visit_EAscType = visit_EAscType,
      visit_ENever = visit_ENever,
      visit_ELet = visit_ELet,
      visit_EMatchSum = visit_EMatchSum,
      visit_EMatchPair = visit_EMatchPair,
      visit_EMatchUnfold = visit_EMatchUnfold,
      visit_EMatchUnpackI = visit_EMatchUnpackI,
      visit_var = visit_var,
      visit_idx = visit_idx,
      visit_sort = visit_sort,
      visit_kind = visit_noop,
      visit_ty = visit_ty,
      extend_i = extend_i,
      extend_t = extend_t,
      extend_e = extend_e
    }
  end

datatype ('env, 'var, 'idx, 'sort, 'kind, 'ty, 'var2, 'idx2, 'sort2, 'kind2, 'ty2) expr_visitor =
         ExprVisitor of (('env, 'var, 'idx, 'sort, 'kind, 'ty, 'var2, 'idx2, 'sort2, 'kind2, 'ty2) expr_visitor, 'env, 'var, 'idx, 'sort, 'kind, 'ty, 'var2, 'idx2, 'sort2, 'kind2, 'ty2) expr_visitor_interface

fun expr_visitor_impls_interface (this : ('env, 'var, 'idx, 'sort, 'kind, 'ty, 'var2, 'idx2, 'sort2, 'kind2, 'ty2) expr_visitor) :
    (('env, 'var, 'idx, 'sort, 'kind, 'ty, 'var2, 'idx2, 'sort2, 'kind2, 'ty2) expr_visitor, 'env, 'var, 'idx, 'sort, 'kind, 'ty, 'var2, 'idx2, 'sort2, 'kind2, 'ty2) expr_visitor_interface =
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
    
(***************** the "shift_i_e" visitor  **********************)    
    
fun shift_i_expr_visitor_vtable cast ((shift_i, shift_s, shift_t), n) : ('this, int, 'var, 'idx, 'sort2, 'kind, 'ty, 'var, 'idx2, 'sort, 'kind, 'ty2) expr_visitor_vtable =
  let
    fun extend_i this env _ = env + 1
    fun do_shift shift this env b = shift env n b
  in
    default_expr_visitor_vtable
      cast
      extend_i
      extend_noop
      extend_noop
      visit_noop
      (do_shift shift_i)
      (do_shift shift_s)
      (do_shift shift_t)
  end

fun new_shift_i_expr_visitor params = new_expr_visitor shift_i_expr_visitor_vtable params
    
fun shift_i_e_fn shifts x n b =
  let
    val visitor as (ExprVisitor vtable) = new_shift_i_expr_visitor (shifts, n)
  in
    #visit_expr vtable visitor x b
  end
    
(***************** the "shift_t_e" visitor  **********************)    
    
fun shift_t_expr_visitor_vtable cast (shift_t, n) : ('this, int, 'var, 'idx, 'sort, 'kind, 'ty, 'var, 'idx, 'sort, 'kind, 'ty2) expr_visitor_vtable =
  let
    fun extend_t this env _ = env + 1
    fun do_shift shift this env b = shift env n b
  in
    default_expr_visitor_vtable
      cast
      extend_noop
      extend_t
      extend_noop
      visit_noop
      visit_noop
      visit_noop
      (do_shift shift_t)
  end

fun new_shift_t_expr_visitor params = new_expr_visitor shift_t_expr_visitor_vtable params
    
fun shift_t_e_fn shift_t x n b =
  let
    val visitor as (ExprVisitor vtable) = new_shift_t_expr_visitor (shift_t, n)
  in
    #visit_expr vtable visitor x b
  end
    
(***************** the "shift_e_e" visitor  **********************)    
    
fun shift_e_expr_visitor_vtable cast (shift_var, n) : ('this, int, 'var, 'idx, 'sort, 'kind, 'ty, 'var2, 'idx, 'sort, 'kind, 'ty) expr_visitor_vtable =
  let
    fun extend_e this env _ = env + 1
    fun visit_var this env data = shift_var env n data
  in
    default_expr_visitor_vtable
      cast
      extend_noop
      extend_noop
      extend_e
      visit_var
      visit_noop
      visit_noop
      visit_noop
  end

fun new_shift_e_expr_visitor params = new_expr_visitor shift_e_expr_visitor_vtable params
    
fun shift_e_e_fn shift_var x n b =
  let
    val visitor as (ExprVisitor vtable) = new_shift_e_expr_visitor (shift_var, n)
  in
    #visit_expr vtable visitor x b
  end
    
(***************** the "subst_e_e" visitor  **********************)    

datatype 'a cmp_var =
         CmpEq
         | CmpGreater of 'a
         | CmpOther

fun subst_e_expr_visitor_vtable cast (shift_var, compare_var, (shift_i_i, shift_i_s, shift_i_t, shift_t_t), d, x, v) : ('this, idepth * tdepth * edepth, 'var, 'idx, 'sort, 'kind, 'ty, 'var, 'idx, 'sort, 'kind, 'ty) expr_visitor_vtable =
  let
    fun extend_i this (di, dt, de) _ = (idepth_inc di, dt, de)
    fun extend_t this (di, dt, de) _ = (di, tdepth_inc dt, de)
    fun extend_e this (di, dt, de) _ = (di, dt, edepth_inc de)
    fun add_depth (di, dt, de) (di', dt', de') = (idepth_add (di, di'), tdepth_add (dt, dt'), edepth_add (de, de'))
    fun get_di (di, dt, de) = di
    fun get_dt (di, dt, de) = dt
    fun get_de (di, dt, de) = de
    val shift_i_e = shift_i_e_fn (shift_i_i, shift_i_s, shift_i_t)
    val shift_t_e = shift_t_e_fn shift_t_t
    val shift_e_e = shift_e_e_fn shift_var
    fun visit_EVar this env y =
      let
        val x = x + unEDepth (get_de env)
      in
        case compare_var y x of
            CmpEq =>
            let
              val (di, dt, de) = add_depth d env
            in
              shift_i_e 0 (unIDepth di) $ shift_t_e 0 (unTDepth dt) $ shift_e_e 0 (unEDepth de) v
            end
          | CmpGreater y' =>
            EVar y'
          | _ =>
            EVar y
      end
    val vtable = 
        default_expr_visitor_vtable
          cast
          extend_i
          extend_t
          extend_e
          (visit_imposs "subst_e_e/visit_var")
          visit_noop
          visit_noop
          visit_noop
    val vtable = override_visit_EVar vtable visit_EVar
  in
    vtable
  end

fun new_subst_e_expr_visitor params = new_expr_visitor subst_e_expr_visitor_vtable params
    
fun subst_e_e_fn shift_var compare_var shifts d x v b =
  let
    val visitor as (ExprVisitor vtable) = new_subst_e_expr_visitor (shift_var, compare_var, shifts, d, x, v)
  in
    #visit_expr vtable visitor (IDepth 0, TDepth 0, EDepth 0) b
  end

(***************** the "export" visitor: convertnig de Bruijn indices to nameful terms **********************)    

type naming_ctx = iname list * tname list * ename list
fun export_expr_visitor_vtable cast (visit_var, visit_idx, visit_sort, visit_ty) : ('this, naming_ctx, 'var, 'idx, 'sort, 'kind, 'ty, 'var2, 'idx2, 'sort2, 'kind, 'ty2) expr_visitor_vtable =
  let
    fun extend_i this (sctx, kctx, tctx) name = (name :: sctx, kctx, tctx)
    fun extend_t this (sctx, kctx, tctx) name = (sctx, name :: kctx, tctx)
    fun extend_e this (sctx, kctx, tctx) name = (sctx, kctx, name :: tctx)
    fun only_s f this (sctx, kctx, tctx) name = f sctx name
    fun only_sk f this (sctx, kctx, tctx) name = f (sctx, kctx) name
  in
    default_expr_visitor_vtable
      cast
      extend_i
      extend_t
      extend_e
      (ignore_this visit_var)
      (only_s visit_idx)
      (only_s visit_sort)
      (only_sk visit_ty)
  end

fun new_export_expr_visitor params = new_expr_visitor export_expr_visitor_vtable params
    
fun export_fn params ctx e =
  let
    val visitor as (ExprVisitor vtable) = new_export_expr_visitor params
  in
    #visit_expr vtable visitor ctx e
  end
    
end
