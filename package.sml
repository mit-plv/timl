(* a special kind of substitution, where a variable y such that y >= x will be replaced with m.(y-x) *)
(* This is used for packagin things in the top-level context into a module *)

structure Package = struct
open Expr
open Util
open Subst
open Bind

infixr 0 $

fun package_long_id x m (id : long_id) =
  case id of
      ID (y, r) =>
      if y >= x then
        QID (m, (y - x, r))
      else
        id
    | QID _ => id (* if it has module reference, don't substitute *)
        
(* fun package_i_ibind f x v (Bind (name, inner) : ('a * 'b) ibind) = *)
(*   Bind (name, f (x + 1) v inner) *)

(* fun package_i_tbind f x v (Bind (name, inner)) = *)
(*   Bind (name, f x v inner) *)

(* fun package_i_idx_visitor_vtable cast (on_var, n) : ('this, int) idx_visitor_vtable = *)
(*   let *)
(*     fun extend_i this env _ = env + 1 *)
(*     fun visit_var this env data = on_var env n data *)
(*   in *)
(*     default_idx_visitor_vtable *)
(*       cast *)
(*       extend_i *)
(*       visit_var *)
(*       visit_noop *)
(*       visit_noop *)
(*       visit_noop *)
(*       visit_noop *)
(*   end *)

(* fun new_package_i_idx_visitor a = new_idx_visitor package_i_idx_visitor_vtable a *)
    
(* fun package_i_i on_var x n b = *)
(*   let *)
(*     val visitor as (IdxVisitor vtable) = new_package_i_idx_visitor (on_var, n) *)
(*   in *)
(*     #visit_idx vtable visitor x b *)
(*   end *)
    
(* local *)
(*   fun f x v b = *)
(*     case b of *)
(* 	VarI y => VarI $ package_long_id x v y *)
(*       | IConst _ => b *)
(*       | UnOpI (opr, i, r) => UnOpI (opr, f x v i, r) *)
(*       | BinOpI (opr, d1, d2) => BinOpI (opr, f x v d1, f x v d2) *)
(*       | Ite (i1, i2, i3, r) => Ite (f x v i1, f x v i2, f x v i3, r) *)
(*       | IAbs (b, bind, r) => IAbs (b, package_i_ibind f x v bind, r) *)
(*       | UVarI a => b *)
(* in *)
(* fun package_i_i x v (b : idx) : idx = f x v b *)
(* end *)

(* local *)
(*   fun f x v b = *)
(*     case b of *)
(* 	PTrueFalse _ => b *)
(*       | Not (p, r) => Not (f x v p, r) *)
(*       | BinConn (opr,p1, p2) => BinConn (opr, f x v p1, f x v p2) *)
(*       | BinPred (opr, d1, d2) => BinPred (opr, package_i_i x v d1, package_i_i x v d2) *)
(*       | Quan (q, bs, bind, r) => Quan (q, bs, package_i_ibind f x v bind, r) *)
(* in *)
(* fun package_i_p x v b = f x v b *)
(* end *)

(* local *)
(*   fun f x v b = *)
(*     case b of *)
(* 	Basic s => Basic s *)
(*       | Subset (s, bind, r) => Subset (s, package_i_ibind package_i_p x v bind, r) *)
(*       | UVarS a => b *)
(*       | SAbs (b, bind, r) => SAbs (b, package_i_ibind f x v bind, r) *)
(*       | SApp (s, i) => SApp (f x v s, package_i_i x v i) *)
(* in *)
(* fun package_i_s x v (b : sort) : sort = f x v b *)
(* end *)

fun params_i (x, n) env = package_long_id (x + env) n
                            
fun package_i_i x n = IdxShiftVisitor.on_i_i $ params_i (x, n)
fun package_i_s x n  = IdxShiftVisitor.on_i_s $ params_i (x, n)

fun package0_i_i a = package_i_i 0 a
fun package0_i_s a = package_i_s 0 a
                               
val package0_i = package0_i_i
val package0_s = package0_i_s
                               
(* fun package_t_ibind f x v (Bind (name, inner) : ('a * 'b) ibind) = *)
(*   Bind (name, f x v inner) *)

(* fun package_t_tbind f x v (Bind (name, inner) : ('a * 'b) tbind) = *)
(*   Bind (name, f (x + 1) v inner) *)

(* fun package_binds on_bind f_cls f_inner x v ibinds = *)
(*   let *)
(*     val package_binds = package_binds on_bind f_cls f_inner *)
(*   in *)
(*     case ibinds of *)
(*         BindNil inner => BindNil $ f_inner x v inner *)
(*       | BindCons (cls, bind) => BindCons (f_cls x v cls, on_bind package_binds x v bind) *)
(*   end *)
    
(* fun package_i_ibinds f_cls f_inner x v ibinds = package_binds package_i_ibind f_cls f_inner x v ibinds *)
(* fun package_i_ibinds f_cls f_inner x v ibinds = *)
(*   let *)
(*     val package_i_ibinds = package_i_ibinds f_cls f_inner *)
(*   in *)
(*     case ibinds of *)
(*         BindNil inner => BindNil $ f_inner x v inner *)
(*       | BindCons (cls, bind) => BindCons (f_cls x v cls, package_i_ibind package_i_ibinds x v bind) *)
(*   end *)
    
(* fun package_t_ibinds f_cls f_inner x v ibinds = package_binds package_t_ibind f_cls f_inner x v ibinds *)
(* fun package_t_ibinds f_cls f_inner x v ibinds = *)
(*   let *)
(*     val package_t_ibinds = package_t_ibinds f_cls f_inner *)
(*   in *)
(*     case ibinds of *)
(*         BindNil inner => BindNil $ f_inner x v inner *)
(*       | BindCons (cls, bind) => BindCons (f_cls x v cls, package_t_ibind package_t_ibinds x v bind) *)
(*   end *)
    
(* fun package_i_tbinds f_cls f_inner x v ibinds = package_binds package_i_tbind f_cls f_inner x v ibinds *)
(* fun package_t_tbinds f_cls f_inner x v ibinds = package_binds package_t_tbind f_cls f_inner x v ibinds *)

(* fun package_i_mt x v (b : mtype) : mtype = *)
(*   let *)
(*     val f = package_i_mt *)
(*   in *)
(*     case b of *)
(* 	Arrow (t1, d, t2) => Arrow (f x v t1, package_i_i x v d, f x v t2) *)
(*       | TyArray (t, i) => TyArray (f x v t, package_i_i x v i) *)
(*       | TyNat (i, r) => TyNat (package_i_i x v i, r) *)
(*       | Unit r => Unit r *)
(*       | Prod (t1, t2) => Prod (f x v t1, f x v t2) *)
(*       | UniI (s, bind, r) => UniI (package_i_s x v s, package_i_ibind f x v bind, r) *)
(*       | MtVar y => MtVar y *)
(*       | MtAbs (k, bind, r) => MtAbs (k, package_i_tbind f x v bind, r) *)
(*       | MtApp (t1, t2) => MtApp (f x v t1, f x v t2) *)
(*       | MtAbsI (b, bind, r) => MtAbsI (b, package_i_ibind f x v bind, r) *)
(*       | MtAppI (t, i) => MtAppI (f x v t, package_i_i x v i) *)
(*       | BaseType a => BaseType a *)
(*       | UVar a => b *)
(*       | TDatatype (Bind (name, tbinds), r) => *)
(*         let *)
(*           fun on_body x v (bsorts, decls) = *)
(*             (bsorts, map (map2_3 (package_i_constr_core x v)) decls) *)
(*           val tbinds = package_i_tbinds return3 on_body x v tbinds *)
(*         in *)
(*           TDatatype (Bind (name, tbinds), r) *)
(*         end *)
(*   end *)

(* and package_i_constr_core x m b = *)
(*   let *)
(*     fun on_body x m (t, is) = (package_i_mt x m t, map (package_i_i x m) is) *)
(*   in *)
(*     package_i_ibinds package_i_s on_body x m b *)
(*   end *)
    
(* local *)
(*   fun f x v b = *)
(*     case b of *)
(* 	Mono t => Mono (package_i_mt x v t) *)
(*       | Uni (bind, r) => Uni (package_i_tbind f x v bind, r) *)
(* in *)
(* fun package_i_t x v (b : ty) : ty = f x v b *)
(* end *)

(* fun package_i_c x m ((family, core) : mtype constr) = *)
(*   let *)
(*     val core = package_i_tbinds return3 package_i_constr_core x m core *)
(*   in *)
(*     (family, core) *)
(*   end *)

fun adapt f x n env = f (x + env) n
fun params_i_t x m = (adapt package_i_i x m, adapt package_i_s x m)
      
fun package_i_mt x m = TypeShiftVisitor.on_i_mt (params_i_t x m)
fun package_i_t x m = TypeShiftVisitor.on_i_t (params_i_t x m)
fun package_i_constr_core x m = TypeShiftVisitor.on_i_constr_core (params_i_t x m)
fun package_i_c x m = TypeShiftVisitor.on_i_c (params_i_t x m)

fun package0_i_mt a = package_i_mt 0 a
fun package0_i_t a = package_i_t 0 a
fun package0_i_constr_core a = package_i_constr_core 0 a
fun package0_i_c a = package_i_c 0 a

(* fun package_t_mt x v (b : mtype) : mtype = *)
(*   let *)
(*     val f = package_t_mt *)
(*   in *)
(*     case b of *)
(* 	Arrow (t1, d, t2) => Arrow (f x v t1, d, f x v t2) *)
(*       | TyArray (t, i) => TyArray (f x v t, i) *)
(*       | TyNat (i, r) => TyNat (i, r) *)
(*       | Unit r => Unit r *)
(*       | Prod (t1, t2) => Prod (f x v t1, f x v t2) *)
(*       | UniI (s, bind, r) => UniI (s, package_t_ibind f x v bind, r) *)
(*       | MtVar y => MtVar $ package_long_id x v y *)
(*       | MtAbs (k, bind, r) => MtAbs (k, package_t_tbind f x v bind, r) *)
(*       | MtApp (t1, t2) => MtApp (f x v t1, f x v t2) *)
(*       | MtAbsI (s, bind, r) => MtAbsI (s, package_t_ibind f x v bind, r) *)
(*       | MtAppI (t, i) => MtAppI (f x v t, i) *)
(*       | BaseType a => BaseType a *)
(*       | UVar a => b *)
(*       | TDatatype (Bind (name, tbinds), r) => *)
(*         let *)
(*           fun on_body x v (bsorts, decls) = *)
(*             (bsorts, map (map2_3 (package_t_constr_core x v)) decls) *)
(*           val tbinds = package_t_tbinds return3 on_body x v tbinds *)
(*         in *)
(*           TDatatype (Bind (name, tbinds), r) *)
(*         end *)
(*   end *)
    
(* and package_t_constr_core x m b = *)
(*   let *)
(*     fun on_body x v (t, is) = (package_t_mt x v t, is) *)
(*   in *)
(*     package_t_ibinds return3 on_body x m b *)
(*   end *)
    
(* fun package_t_t x v (b : ty) : ty = *)
(*   case b of *)
(*       Mono t => Mono (package_t_mt x v t) *)
(*     | Uni (bind, r) => Uni (package_t_tbind package_t_t x v bind, r) *)

(* fun package_t_c x m ((family, core) : mtype constr) = *)
(*   let *)
(*     val core = package_t_tbinds return3 package_t_constr_core x m core *)
(*     val family = package_long_id x m family *)
(*   in *)
(*     (family, core) *)
(*   end *)

fun params_t x m env = package_long_id (x + env) m
                                     
fun package_t_mt x m = TypeShiftVisitor.on_t_mt $ params_t x m
fun package_t_t x m = TypeShiftVisitor.on_t_t $ params_t x m
fun package_t_constr_core x m = TypeShiftVisitor.on_t_constr_core $ params_t x m
fun package_t_c x m = TypeShiftVisitor.on_t_c $ params_t x m

fun package0_t_mt a = package_t_mt 0 a
fun package0_t_t a = package_t_t 0 a
fun package0_t_constr_core a = package_t_constr_core 0 a
fun package0_t_c a = package_t_c 0 a

fun package0_mt m = package0_t_mt m o package0_i_mt m
fun package0_t m = package0_t_t m o package0_i_t m
fun package0_c m = package0_t_c m o package0_i_c m
              
(*                               
fun package_long_id m (m', x) =
    (SOME $ default m m', x)
      
fun package_i m b =
    let
      fun f b =
	  case b of
	      VarI x => VarI $ package_long_id m x
	    | ConstIN n => ConstIN n
	    | ConstIT x => ConstIT x
            | UnOpI (opr, i, r) => UnOpI (opr, f i, r)
            | DivI (i1, n2) => DivI (f i1, n2)
            | ExpI (i1, n2) => ExpI (f i1, n2)
	    | BinOpI (opr, i1, i2) => BinOpI (opr, f i1, f i2)
            | Ite (i1, i2, i3, r) => Ite (f i1, f i2, f i3, r)
	    | TTI r => TTI r
	    | TrueI r => TrueI r
	    | FalseI r => FalseI r
            | IAbs (name, i, r) => IAbs (name, f i, r)
            | AdmitI r => AdmitI r
            | UVarI a => raise ModuleUVar "package_i ()"
    in
      f b
    end

fun package_ibind f m bind =
    case bind of
        Bind (name, inner) => Bind (name, f m inner)

fun package_tbind f m bind =
    case bind of
        Bind (name, inner) => Bind (name, f m inner)

fun package_p m b =
    let
      fun f m b =
          case b of
	      True r => True r
	    | False r => False r
            | Not (p, r) => Not (f m p, r)
	    | BinConn (opr, p1, p2) => BinConn (opr, f m p1, f m p2)
	    | BinPred (opr, d1, d2) => BinPred (opr, package_i m d1, package_i m d2)
            | Quan (q, bs, bind, r) => Quan (q, bs, package_ibind f m bind, r)
    in
      f m b
    end

fun package_s m b =
    let
      fun f m b =
	  case b of
	      Basic s => Basic s
	    | Subset (s, bind, r) => Subset (s, package_ibind package_p m bind, r)
            | UVarS a => raise ModuleUVar "package_s ()"
    in
      f m b
    end

fun package_mt m b =
    let
      fun f m b =
	  case b of
	      Arrow (t1, d, t2) => Arrow (f m t1, package_i m d, f m t2)
            | Unit r => Unit r
	    | Prod (t1, t2) => Prod (f m t1, f m t2)
	    | UniI (s, bind, r) => UniI (package_s m s, package_ibind f m bind, r)
            | MtVar x => MtVar $ package_long_id m x
            (* | MtApp (t1, t2) => MtApp (f m t1, f m t2) *)
            (* | MtAbs (bind, r) => MtAbs (package_tbind f m bind, r) *)
            (* | MtAppI (t, i) => MtAppI (f m t, package_i m i) *)
            (* | MtAbsI (s, bind, r) => MtAbsI (package_s m s, package_ibind f m bind, r) *)
	    | AppV (x, ts, is, r) => AppV (package_long_id m x, map (f m) ts, map (package_i m) is, r)
	    | BaseType a => BaseType a
            | UVar a => raise ModuleUVar "package_mt ()"
    in
      f m b
    end

fun package_t m b =
    let
      fun f m b =
	  case b of
	      Mono t => Mono (package_mt m t)
	    | Uni (bind, r) => Uni (package_tbind f m bind, r)
    in
      f m b
    end

fun package_kind m b =
    case b of
	ArrowK (is_datatype, n, sorts) => ArrowK (is_datatype, n, map (package_s m) sorts)

fun package_c m (family, tnames, core) =
    let
      val family = package_long_id m family
      val (name_sorts, (t, is)) = unfold_binds core
      val t = package_mt m t
      val is = map (package_i m) is
      val name_sorts = map (mapSnd $ package_s m) name_sorts
      val core = fold_binds (name_sorts, (t, is))
    in
      (family, tnames, core)
    end
*)
              
end
