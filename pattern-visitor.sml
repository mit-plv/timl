structure PatternVisitor = struct

open Pattern
       
infixr 0 $
       
type ('this, 'env, 'var, 'mtype, 'var2, 'mtype2) ptrn_visitor_vtable =
     {
       visit_ptrn : 'this -> 'env ctx -> ('var, 'mtype) ptrn -> ('var2, 'mtype2) ptrn,
       visit_VarP : 'this -> 'env ctx -> ename binder -> ('var2, 'mtype2) ptrn,
       visit_TTP : 'this -> 'env ctx -> region outer -> ('var2, 'mtype2) ptrn,
       visit_PairP : 'this -> 'env ctx -> ('var, 'mtype) ptrn * ('var, 'mtype) ptrn -> ('var2, 'mtype2) ptrn,
       visit_AliasP : 'this -> 'env ctx -> ename binder * ('var, 'mtype) ptrn * region outer -> ('var2, 'mtype2) ptrn,
       visit_ConstrP : 'this -> 'env ctx -> ('var * bool) outer * iname binder list * ('var, 'mtype) ptrn * region outer -> ('var2, 'mtype2) ptrn,
       visit_AnnoP : 'this -> 'env ctx -> ('var, 'mtype) ptrn * 'mtype outer -> ('var2, 'mtype2) ptrn,
       visit_var : 'this -> 'env -> 'var -> 'var2,
       visit_mtype : 'this -> 'env -> 'mtype -> 'mtype2,
       extend_i : 'this -> 'env -> iname -> 'env,
       extend_e : 'this -> 'env -> ename -> 'env
     }
       
type ('this, 'env, 'var, 'mtype, 'var2, 'mtype2) ptrn_visitor_interface =
     ('this, 'env, 'var, 'mtype, 'var2, 'mtype2) ptrn_visitor_vtable
                                       
(***************** the default visitor  **********************)    

open VisitorUtil
       
fun default_ptrn_visitor_vtable
      (cast : 'this -> ('this, 'env, 'var, 'mtype, 'var2, 'mtype2) ptrn_visitor_interface)
      extend_i
      extend_e
      visit_var
      visit_mtype
    : ('this, 'env, 'var, 'mtype, 'var2, 'mtype2) ptrn_visitor_vtable =
  let
    fun visit_ibinder this env name =
      let
        val vtable = cast this
        val name = visit_binder (#extend_i vtable this) env name
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
    fun visit_ptrn this env data =
      let
        val vtable = cast this
      in
        case data of
            VarP data => #visit_VarP vtable this env data
          | TTP data => #visit_TTP vtable this env data
          | PairP data => #visit_PairP vtable this env data
          | AliasP data => #visit_AliasP vtable this env data
          | ConstrP data => #visit_ConstrP vtable this env data
          | AnnoP data => #visit_AnnoP vtable this env data
      end
    fun visit_VarP this env data =
      let
        val vtable = cast this
      in
        VarP $ visit_ebinder this env data
      end
    fun visit_TTP this env data =
      TTP data
    fun visit_PairP this env data = 
      let
        val vtable = cast this
        val (p1, p2) = data
        val p1 = #visit_ptrn vtable this env p1
        val p2 = #visit_ptrn vtable this env p2
      in
        PairP (p1, p2)
      end
    fun visit_AliasP this env data =
      let
        val vtable = cast this
        val (name, p, r) = data
        val name = visit_ebinder this env name
        val p = #visit_ptrn vtable this env p
      in
        AliasP (name, p, r)
      end
    fun visit_AnnoP this env data = 
      let
        val vtable = cast this
        val (p, t) = data
        val p = #visit_ptrn vtable this env p
        val t = visit_outer (#visit_mtype vtable this) env t
      in
        AnnoP (p, t)
      end
    fun visit_ConstrP this env data =
      let
        val vtable = cast this
        val (x, inames, p, r) = data
        val x = visit_outer (visit_pair (#visit_var vtable this) return2) env x
        val inames = map (visit_ibinder this env) inames
        val p = #visit_ptrn vtable this env p
      in
        ConstrP (x, inames, p, r)
      end
  in
    {
      visit_ptrn = visit_ptrn,
      visit_VarP = visit_VarP,
      visit_TTP = visit_TTP,
      visit_PairP = visit_PairP,
      visit_AliasP = visit_AliasP,
      visit_AnnoP = visit_AnnoP,
      visit_ConstrP = visit_ConstrP,
      visit_var = visit_var,
      visit_mtype = visit_mtype,
      extend_i = extend_i,
      extend_e = extend_e
    }
  end

datatype ('env, 'var, 'mtype, 'var2, 'mtype2) ptrn_visitor =
         PtrnVisitor of (('env, 'var, 'mtype, 'var2, 'mtype2) ptrn_visitor, 'env, 'var, 'mtype, 'var2, 'mtype2) ptrn_visitor_interface

fun ptrn_visitor_impls_interface (this : ('env, 'var, 'mtype, 'var2, 'mtype2) ptrn_visitor) :
    (('env, 'var, 'mtype, 'var2, 'mtype2) ptrn_visitor, 'env, 'var, 'mtype, 'var2, 'mtype2) ptrn_visitor_interface =
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
    
end
