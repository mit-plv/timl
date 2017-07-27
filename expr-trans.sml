functor ExprShiftVisitorFn (Expr : EXPR) = struct

structure ExprVisitor = ExprVisitorFn (structure S = Expr
                                       structure T = Expr
                                      )
open ExprVisitor

fun on_e_expr_visitor_vtable cast visit_var : ('this, int) expr_visitor_vtable =
  let
    fun extend_e this env _ = env + 1
  in
    default_expr_visitor_vtable
      cast
      extend_noop
      extend_noop
      extend_noop
      extend_e
      (ignore_this visit_var)
      visit_noop
      visit_noop
      visit_noop
      visit_noop
      visit_noop
      visit_noop
  end

fun new_on_e_expr_visitor params = new_expr_visitor on_e_expr_visitor_vtable params
    
fun on_e_e params b =
  let
    val visitor as (ExprVisitor vtable) = new_on_e_expr_visitor params
  in
    #visit_expr vtable visitor 0 b
  end
    
end

functor ExprShiftFn (structure Expr : EXPR
                     structure ShiftableVar : SHIFTABLE_VAR
                     sharing type ShiftableVar.var = Expr.var
                    ) = struct

open ShiftableVar
open Util
       
infixr 0 $
         
structure ExprShiftVisitor = ExprShiftVisitorFn (Expr)
open ExprShiftVisitor
                                         
fun adapt f x n env = f (x + env) n

fun shift_e_params a = adapt shiftx_var a
  
fun shiftx_e_e x n = on_e_e $ shift_e_params x n
                            
fun shift_e_e a = shiftx_e_e 0 1 a
                              
fun forget_e_params a = adapt forget_var a
  
fun forget_e_e x n = on_e_e $ forget_e_params x n

open Bind
       
(* fun on_e_ibind f x n (Bind (name, b) : ('a * 'b) ibind) = Bind (name, f x n b) *)
                                                               
(* fun on_e_e on_v = *)
(*   let *)
(*     fun f x n b = *)
(*       case b of *)
(* 	  EVar (y, b) => EVar (on_v x n y, b) *)
(*         | EConst _ => b *)
(* 	| EUnOp (opr, e, r) => EUnOp (opr, f x n e, r) *)
(* 	| EBinOp (opr, e1, e2) => EBinOp (opr, f x n e1, f x n e2) *)
(* 	| ETriOp (opr, e1, e2, e3) => ETriOp (opr, f x n e1, f x n e2, f x n e3) *)
(* 	| EEI (opr, e, i) => EEI (opr, f x n e, i) *)
(* 	| EET (opr, e, t) => EET (opr, f x n e, t) *)
(* 	| ET (opr, t, r) => ET (opr, t, r) *)
(* 	| EAbs bind => *)
(*           let *)
(*             val (pn, e) = unBind bind *)
(*           in *)
(*             EAbs $ Unbound.Bind (pn, f (x + (length $ snd $ ptrn_names pn)) n e) *)
(*           end *)
(* 	| EAbsI (bind, r) => *)
(*           let *)
(*             val ((name, s), e) = unBindAnno bind *)
(*             val bind = Bind (name, e) *)
(*             val Bind (name, e) = on_e_ibind f x n bind *)
(*             val bind = BindAnno ((name, s), e) *)
(*           in *)
(*             EAbsI (bind, r) *)
(*           end *)
(* 	| ELet (return, bind, r) => *)
(* 	  let *)
(*             val (decls, e) = unBind bind *)
(*             val decls = unTeles decls *)
(* 	    val (decls, m) = f_decls x n decls *)
(*             val decls = Teles decls *)
(* 	  in *)
(* 	    ELet (return, Unbound.Bind (decls, f (x + m) n e), r) *)
(* 	  end *)
(* 	| EAsc (e, t) => EAsc (f x n e, t) *)
(* 	| EAppConstr (cx, ts, is, e, ot) => EAppConstr (cx, ts, is, f x n e, ot) *)
(* 	| ECase (e, return, rules, r) => ECase (f x n e, return, map (f_rule x n) rules, r) *)

(*     and f_decls x n decls = *)
(* 	let  *)
(*           fun g (dec, (acc, m)) = *)
(* 	    let *)
(* 	      val (dec, m') = f_dec (x + m) n dec *)
(* 	    in *)
(* 	      (dec :: acc, m' + m) *)
(* 	    end *)
(* 	  val (decls, m) = foldl g ([], 0) decls *)
(* 	  val decls = rev decls *)
(* 	in *)
(*           (decls, m) *)
(*         end *)

(*     and f_dec x n dec = *)
(* 	case dec of *)
(* 	    DVal (name, Outer bind, r) =>  *)
(* 	    let *)
(*               val (tnames, e) = unBind bind *)
(* 	    in *)
(*               (DVal (name, Outer $ Unbound.Bind (tnames, f x n e), r), 1) *)
(*             end *)
(* 	  | DValPtrn (pn, Outer e, r) =>  *)
(* 	    let  *)
(*               val (_, enames) = ptrn_names pn  *)
(* 	    in *)
(*               (DValPtrn (pn, Outer $ f x n e, r), length enames) *)
(*             end *)
(*           | DRec (name, bind, r) =>  *)
(*             let *)
(*               val ((tnames, Rebind binds), ((t, d), e)) = unBind $ unInner bind *)
(*               val binds = unTeles binds *)
(*               fun g (bind, m) = *)
(*                 case bind of *)
(*                     SortingST _ => m *)
(*                   | TypingST pn => *)
(* 	            let  *)
(*                       val (_, enames) = ptrn_names pn  *)
(* 	            in *)
(*                       m + length enames *)
(*                     end *)
(*               val m = foldl g 0 binds *)
(*               val e = f (x + 1 + m) n e *)
(*             in *)
(*               (DRec (name, Inner $ Unbound.Bind ((tnames, Rebind $ Teles binds), ((t, d), e)), r), 1) *)
(*             end *)
(*           | DDatatype a => (DDatatype a, 0) *)
(*           | DIdxDef a => (DIdxDef a, 0) *)
(*           | DAbsIdx2 a => (DAbsIdx2 a, 0) *)
(*           | DAbsIdx (a, Rebind decls, r) =>  *)
(*             let *)
(*               val decls = unTeles decls *)
(*               val (decls, m) = f_decls x n decls *)
(*             in *)
(*               (DAbsIdx (a, Rebind $ Teles decls, r), m) *)
(*             end *)
(*           | DTypeDef (name, t) => (DTypeDef (name, t), 0) *)
(*           | DOpen (m, octx) => *)
(*             case octx of *)
(*                 NONE => raise Impossible "ctx can't be NONE" *)
(*               | SOME ctx => (DOpen (m, octx), length $ #4 ctx) *)

(*     and f_rule x n bind = *)
(* 	let *)
(*           val (pn, e) = unBind bind *)
(*           val (_, enames) = ptrn_names pn  *)
(* 	in *)
(* 	  Unbound.Bind (pn, f (x + length enames) n e) *)
(* 	end *)
(*   in *)
(*     f *)
(*   end *)

(* fun shiftx_e_e x n b = on_e_e shiftx_v x n b *)
(* fun shift_e_e b = shiftx_e_e 0 1 b *)
(* fun forget_e_e x n b = on_e_e forget_v x n b *)
                              
end

functor ExprSubstFn (structure S : EXPR
                   structure T : EXPR
                   sharing type S.var = T.var
                   sharing type S.cvar = T.cvar
                   sharing type S.mod_id = T.mod_id
                   sharing type S.idx = T.idx
                   sharing type S.sort = T.sort
                   sharing type S.ptrn_constr_tag = T.ptrn_constr_tag
                  ) = struct

structure ExprVisitor = ExprVisitorFn (structure S = S
                                       structure T = T)
open ExprVisitor
       
open Util
       
infixr 0 $
         
(***************** the "subst_t_e" visitor  **********************)    

(* fun visit_datatype this env data = *)
(*   let *)
(*     val vtable =  *)
(*     val (name, _) = data *)
(*     val name = visit_tbinder this env name *)
(*     val t = visit_outer (#visit_mod_id vtable this) env $ TDatatype (Abs data, dummy) *)
(*     val data = case t of *)
(*                    TDatatype (Abs dt, _) => dt *)
(*                  | _ => raise Impossible "default_expr_visitor/visit_datatype" *)
(*   in *)
(*     data *)
(*   end *)
    
fun subst_t_expr_visitor_vtable cast (subst_t_t, d, x, v) : ('this, idepth * tdepth) expr_visitor_vtable =
  let
    fun extend_i this env _ = mapFst idepth_inc env
    fun extend_t this env _ = mapSnd tdepth_inc env
    fun add_depth (di, dt) (di', dt') = (idepth_add (di, di'), tdepth_add (dt, dt'))
    fun visit_mtype this env b = subst_t_t (add_depth d env) (x + unTDepth (snd env)) v b
  in
    default_expr_visitor_vtable
      cast
      extend_i
      extend_t
      extend_noop
      extend_noop
      visit_noop
      visit_noop
      visit_noop
      visit_noop
      visit_noop
      visit_mtype
      visit_noop
  end

fun new_subst_t_expr_visitor params = new_expr_visitor subst_t_expr_visitor_vtable params
    
fun subst_t_e_fn substs d x v b =
  let
    val visitor as (ExprVisitor vtable) = new_subst_t_expr_visitor (substs, d, x, v)
  in
    #visit_expr vtable visitor (IDepth 0, TDepth 0) b
  end

end

                        
