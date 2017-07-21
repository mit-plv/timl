(* normalization *)

structure Normalize = struct
open Util
open UVar
open Expr
open Subst
open TypecheckUtil
       
infixr 0 $

(* update all [Refined] uvars *)         
         
fun load_uvar on_refined on_fresh (a as (x, r)) =
  case !x of
      Refined b => on_refined b
    | Fresh _ => on_fresh x

fun load_uvar' on_refined origin x = load_uvar on_refined (const_fun origin) (x, dummy)

fun update_idx_visitor_vtable cast () : ('this, unit) idx_visitor_vtable =
  let
    val vtable =
        default_idx_visitor_vtable
          cast
          extend_noop
          visit_noop
          (visit_imposs "update/visit_UVarBS")
          (visit_imposs "update/visit_UVarI")
          (visit_imposs "update/visit_UVarS")
          visit_noop
    fun visit_UVarBS this env x =
      let
        val vtable = cast this
      in
        load_uvar' (#visit_bsort vtable this env) (UVarBS x) x
      end
    val vtable = override_visit_UVarBS vtable visit_UVarBS
    fun visit_UVarI this env (data as (x, r)) =
      let
        val vtable = cast this
      in
        load_uvar' (#visit_idx vtable this env) (UVarI data) x
      end
    val vtable = override_visit_UVarI vtable visit_UVarI
    fun visit_UVarS this env (data as (x, r)) =
      let
        val vtable = cast this
      in
        load_uvar' (#visit_sort vtable this env) (UVarS data) x
      end
    val vtable = override_visit_UVarS vtable visit_UVarS
  in
    vtable
  end

fun new_update_idx_visitor a = new_idx_visitor update_idx_visitor_vtable a
    
fun update_bs b =
  let
    val visitor as (IdxVisitor vtable) = new_update_idx_visitor ()
  in
    #visit_bsort vtable visitor () b
  end
    
fun update_i b =
  let
    val visitor as (IdxVisitor vtable) = new_update_idx_visitor ()
  in
    #visit_idx vtable visitor () b
  end
    
fun update_p b =
  let
    val visitor as (IdxVisitor vtable) = new_update_idx_visitor ()
  in
    #visit_prop vtable visitor () b
  end
    
fun update_s b =
  let
    val visitor as (IdxVisitor vtable) = new_update_idx_visitor ()
  in
    #visit_sort vtable visitor () b
  end
                   
(* fun update_bs bs = *)
(*   case bs of *)
(*       UVarBS x => *)
(*       (case !x of *)
(*            Refined bs =>  *)
(*            let  *)
(*              val bs = update_bs bs *)
(*              val () = x := Refined bs *)
(*            in *)
(*              bs *)
(*            end *)
(*          | Fresh _ => bs *)
(*       ) *)
(*     | BSArrow (a, b) => BSArrow (update_bs a, update_bs b) *)
(*     | Base _ => bs *)

(* fun update_i i = *)
(*   case i of *)
(*       UVarI (x, r) => load_uvar' update_i i x *)
(*     | IConst _ => i *)
(*     | UnOpI (opr, i, r) => UnOpI (opr, update_i i, r) *)
(*     | BinOpI (opr, i1, i2) => BinOpI (opr, update_i i1, update_i i2) *)
(*     | Ite (i1, i2, i3, r) => Ite (update_i i1, update_i i2, update_i i3, r) *)
(*     | VarI _ => i *)
(*     | IAbs (b, Bind (name, i), r) => IAbs (update_bs b, Bind (name, update_i i), r) *)

(* fun update_p p = *)
(*   case p of *)
(*       Quan (q, bs, Bind (name, p), r) => Quan (q, update_bs bs, Bind (name, update_p p), r) *)
(*     | BinConn (opr, p1, p2) => BinConn (opr, update_p p1, update_p p2) *)
(*     | BinPred (opr, i1, i2) => BinPred (opr, update_i i1, update_i i2) *)
(*     | Not (p, r) => Not (update_p p, r) *)
(*     | PTrueFalse _ => p *)

(* fun update_s s = *)
(*   case s of *)
(*       UVarS (x, r) => load_uvar' update_s s x *)
(*     | Basic _ => s *)
(*     | Subset ((b, r1), Bind (name, p), r) => Subset ((update_bs b, r1), Bind (name, update_p p), r) *)
(*     | SAbs (s1, Bind (name, s), r) => SAbs (update_bs s1, Bind (name, update_s s), r) *)
(*     | SApp (s, i) => SApp (update_s s, update_i i) *)

fun update_k k = mapSnd (map update_bs) k
                      
fun update_type_visitor_vtable cast (on_bs, on_i, on_s, on_k) : ('this, unit) type_visitor_vtable =
  let
    fun adapt f this env b = f b
    val vtable =
        default_type_visitor_vtable
          cast
          extend_noop
          extend_noop
          visit_noop
          (adapt on_bs)
          (adapt on_i)
          (adapt on_s)
          (adapt on_k)
          (visit_imposs "update/visit_UVar")
    fun visit_UVar this env (data as (x, r)) =
      let
        val vtable = cast this
      in
        load_uvar' (#visit_mtype vtable this env) (UVar data) x
      end
    val vtable = override_visit_UVar vtable visit_UVar
  in
    vtable
  end

fun new_update_type_visitor a = new_type_visitor update_type_visitor_vtable a
    
fun update_mt b =
  let
    val visitor as (TypeVisitor vtable) = new_update_type_visitor (update_bs, update_i, update_s, update_k)
  in
    #visit_mtype vtable visitor () b
  end
    
fun update_t b =
  let
    val visitor as (TypeVisitor vtable) = new_update_type_visitor (update_bs, update_i, update_s, update_k)
  in
    #visit_ty vtable visitor () b
  end
    
(* fun update_mt t = *)
(*   case t of *)
(*       UVar (x, r) => load_uvar' update_mt t x *)
(*     | Unit r => Unit r *)
(*     | Arrow (t1, d, t2) => Arrow (update_mt t1, update_i d, update_mt t2) *)
(*     | TyArray (t, i) => TyArray (update_mt t, update_i i) *)
(*     | TyNat (i, r) => TyNat (update_i i, r) *)
(*     | Prod (t1, t2) => Prod (update_mt t1, update_mt t2) *)
(*     | UniI (s, Bind (name, t1), r) => UniI (update_s s, Bind (name, update_mt t1), r) *)
(*     | MtVar x => MtVar x *)
(*     | MtAbs (k, Bind (name, t), r) => MtAbs (update_k k, Bind (name, update_mt t), r) *)
(*     | MtApp (t1, t2) => MtApp (update_mt t1, update_mt t2) *)
(*     | MtAbsI (s, Bind (name, t), r) => MtAbsI (update_bs s, Bind (name, update_mt t), r) *)
(*     | MtAppI (t, i) => MtAppI (update_mt t, update_i i) *)
(*     | BaseType a => BaseType a *)
(*     | TDatatype (Bind (name, tbinds), r) => *)
(*       let *)
(*         val (tname_kinds, (bsorts, decls)) = unfold_binds tbinds *)
(*         val bsorts = map update_bs bsorts *)
(*         fun update_constr_core ibinds = *)
(*           let *)
(*             val (name_sorts, (t, is)) = unfold_binds ibinds *)
(*             val name_sorts = map (mapSnd update_s) name_sorts *)
(*             val t = update_mt t *)
(*             val is = map update_i is *)
(*           in *)
(*             fold_binds (name_sorts, (t, is)) *)
(*           end *)
(*         val decls = map (map2_3 update_constr_core) decls *)
(*         val tbinds = fold_binds (tname_kinds, (bsorts, decls)) *)
(*       in *)
(*         TDatatype (Bind (name, tbinds), r) *)
(*       end *)

(* fun update_t t = *)
(*   case t of *)
(*       Mono t => Mono (update_mt t) *)
(*     | Uni (Bind (name, t), r) => Uni (Bind (name, update_t t), r) *)

fun update_ke (k, t) = (update_k k, Option.map update_mt t)

fun update_c ((x, tbinds) : mtype constr) =
  let
    val (tname_kinds, ibinds) = unfold_binds tbinds
    val (ns, (t, is)) = unfold_binds ibinds
    val ns = map (mapSnd update_s) ns
    val t = update_mt t
    val is = map update_i is
    val ibinds = fold_binds (ns, (t, is))
    val tbinds = fold_binds (tname_kinds, ibinds)
  in
    (x, tbinds)
  end

fun update_ctx (sctx, kctx, cctx, tctx) =
  let
    val sctx = map (mapSnd update_s) sctx
    val kctx = map (mapSnd update_ke) kctx
    val cctx = map (mapSnd update_c) cctx
    val tctx = map (mapSnd update_t) tctx
  in
    (sctx, kctx, cctx, tctx)
  end

fun update_sgntr sg =
  case sg of
      Sig ctx => Sig $ update_ctx ctx
    | FunctorBind ((arg_name, arg), body) =>
      FunctorBind ((arg_name, update_ctx arg), update_ctx body)

fun update_gctx gctx =
  map (mapSnd update_sgntr) gctx

(* Normalize to weak head normal form (WHNF) (i.e. only reveal head structure). Efficient for equivalence test. *)      
fun whnf_i i =
  case i of
      UVarI (x, r) => load_uvar' whnf_i i x
    | BinOpI (opr, i1, i2) =>
      let
        val i1 = whnf_i i1
        val i2 = whnf_i i2
      in
        case (opr, i1) of
            (IApp, IAbs (_, Bind (_, i1), _)) => whnf_i (subst_i_i i2 i1)
          | _ => BinOpI (opr, i1, i2)
      end
    | Ite (i1, i2, i3, r) =>
      let
        val i1 = whnf_i i1
        val i2 = whnf_i i2
        val i3 = whnf_i i3
      in
        case i1 of
            IConst (ICBool b, _) => if b then i2 else i3
          | _ => Ite (i1, i2, i3, r)
      end
    | _ => i

fun whnf_s s =
  case s of
      UVarS (x, r) => load_uvar' whnf_s s x
    | SApp (s, i) =>
      let
        val s = whnf_s s
        val i = whnf_i i
      in
        case s of
            SAbs (_, Bind (_, s), _) => whnf_s (subst_i_s i s)
          | _ => SApp (s, i)
      end
    | _ => s
             
fun whnf_mt gctx kctx (t : mtype) : mtype =
  let
    val whnf_mt = whnf_mt gctx
  in
    case t of
        UVar (x, r) => load_uvar' (whnf_mt kctx) t x
      | MtVar x => try_retrieve_MtVar (whnf_mt kctx) gctx kctx x
      | MtAppI (t, i) =>
        let
          val t = whnf_mt kctx t
          val i = whnf_i i
        in
          case t of
              MtAbsI (_, Bind (_, t), _) => whnf_mt kctx (subst_i_mt i t)
            | _ => MtAppI (t, i)
        end
      | MtApp (t1, t2) =>
        let
          val t1 = whnf_mt kctx t1
          val t2 = whnf_mt kctx t2
        in
          case t1 of
              MtAbs (_, Bind (_, t1), _) => whnf_mt kctx (subst_t_mt t2 t1)
            | _ => MtApp (t1, t2)
        end
      | _ => t
  end

(* Normalize to full normal form (i.e reduce under binders) *)

fun normalize_idx_visitor_vtable cast () : ('this, unit) idx_visitor_vtable =
  let
    val vtable =
        update_idx_visitor_vtable
          cast
          ()
    fun visit_BinOpI this env (data as (opr, i1, i2)) =
      let
        val vtable = cast this
        fun normalize_i a = #visit_idx vtable this env a
        val i1 = normalize_i i1
        val i2 = normalize_i i2
      in
        case (opr, i1) of
            (IApp, IAbs (_, Bind (_, i1), _)) => normalize_i (subst_i_i i2 i1)
          | _ => BinOpI (opr, i1, i2)
      end
    val vtable = override_visit_BinOpI vtable visit_BinOpI
    fun visit_Ite this env (data as (i1, i2, i3, r)) =
      let
        val vtable = cast this
        fun normalize_i a = #visit_idx vtable this env a
        val i1 = normalize_i i1
        val i2 = normalize_i i2
        val i3 = normalize_i i3
      in
        case i1 of
            IConst (ICBool b, _) => if b then i2 else i3
          | _ => Ite (i1, i2, i3, r)
      end
    val vtable = override_visit_Ite vtable visit_Ite
    fun visit_SApp this env (data as (s, i)) =
      let
        val vtable = cast this
        fun normalize_i a = #visit_idx vtable this env a
        fun normalize_s a = #visit_sort vtable this env a
        val s = normalize_s s
        val i = normalize_i i
      in
        case s of
            SAbs (_, Bind (_, s), _) => normalize_s (subst_i_s i s)
          | _ => SApp (s, i)
      end
    val vtable = override_visit_SApp vtable visit_SApp
  in
    vtable
  end

fun new_normalize_idx_visitor a = new_idx_visitor normalize_idx_visitor_vtable a
    
fun normalize_bs b =
  let
    val visitor as (IdxVisitor vtable) = new_normalize_idx_visitor ()
  in
    #visit_bsort vtable visitor () b
  end
    
fun normalize_i b =
  let
    val visitor as (IdxVisitor vtable) = new_normalize_idx_visitor ()
  in
    #visit_idx vtable visitor () b
  end
    
fun normalize_p b =
  let
    val visitor as (IdxVisitor vtable) = new_normalize_idx_visitor ()
  in
    #visit_prop vtable visitor () b
  end
    
fun normalize_s b =
  let
    val visitor as (IdxVisitor vtable) = new_normalize_idx_visitor ()
  in
    #visit_sort vtable visitor () b
  end
                   
(* val normalize_bs = update_bs *)

(* fun normalize_i i = *)
(*   case i of *)
(*       UVarI (x, r) => load_uvar' normalize_i i x *)
(*     | IConst _ => i *)
(*     | UnOpI (opr, i, r) => UnOpI (opr, normalize_i i, r) *)
(*     | BinOpI (opr, i1, i2) => *)
(*       let *)
(*         val i1 = normalize_i i1 *)
(*         val i2 = normalize_i i2 *)
(*       in *)
(*         case (opr, i1) of *)
(*             (IApp, IAbs (_, Bind (_, i1), _)) => normalize_i (subst_i_i i2 i1) *)
(*           | _ => BinOpI (opr, i1, i2) *)
(*       end *)
(*     | Ite (i1, i2, i3, r) => *)
(*       let *)
(*         val i1 = normalize_i i1 *)
(*         val i2 = normalize_i i2 *)
(*         val i3 = normalize_i i3 *)
(*       in *)
(*         case i1 of *)
(*             IConst (ICBool b, _) => if b then i2 else i3 *)
(*           | _ => Ite (i1, i2, i3, r) *)
(*       end *)
(*     | VarI _ => i *)
(*     | IAbs (b, Bind (name, i), r) => IAbs (normalize_bs b, Bind (name, normalize_i i), r) *)

(* fun normalize_p p = *)
(*   case p of *)
(*       Quan (q, bs, Bind (name, p), r) => Quan (q, normalize_bs bs, Bind (name, normalize_p p), r) *)
(*     | BinConn (opr, p1, p2) => BinConn (opr, normalize_p p1, normalize_p p2) *)
(*     | BinPred (opr, i1, i2) => BinPred (opr, normalize_i i1, normalize_i i2) *)
(*     | Not (p, r) => Not (normalize_p p, r) *)
(*     | PTrueFalse _ => p *)
                   
(* fun normalize_s s = *)
(*   case s of *)
(*       UVarS (x, r) => load_uvar' normalize_s s x *)
(*     | Basic _ => s *)
(*     | Subset ((b, r1), Bind (name, p), r) => Subset ((normalize_bs b, r1), Bind (name, normalize_p p), r) *)
(*     | SAbs (s_arg, Bind (name, s), r) => SAbs (normalize_bs s_arg, Bind (name, normalize_s s), r) *)
(*     | SApp (s, i) => *)
(*       let *)
(*         val s = normalize_s s *)
(*         val i = normalize_i i *)
(*       in *)
(*         case s of *)
(*             SAbs (_, Bind (_, s), _) => normalize_s (subst_i_s i s) *)
(*           | _ => SApp (s, i) *)
(*       end *)
        
fun normalize_k k = mapSnd (map normalize_bs) k
                                      
fun normalize_ibind f kctx (Bind (name, t) : ('a * 'b) ibind) =
  Bind (name, f (shiftx_i_kctx 1 kctx) t)
       
fun normalize_tbind f kctx k (Bind (name, t) : ((string * 'a) * 'b) tbind) =
  Bind (name, f (add_kinding (fst name, k) kctx) t)

fun normalize_binds get_cls on_bind f_cls f ctx binds =
  let
    val normalize_binds = normalize_binds get_cls on_bind f_cls f
  in
    case binds of
        BindNil a => BindNil (f ctx a)
      | BindCons (cls, bind) =>
        let
          val cls = f_cls cls
        in
          BindCons (cls, on_bind normalize_binds ctx (get_cls cls) bind)
        end
  end

fun normalize_ibind' f kctx _ bind = normalize_ibind f kctx bind
fun normalize_ibinds f_cls f ctx (b : ('classifier, 'name, 'inner) ibinds) = normalize_binds id normalize_ibind' f_cls f ctx b
fun normalize_tbinds get_cls f_cls f ctx (b : ('classifier, string * 'a, 'inner) tbinds) = normalize_binds get_cls normalize_tbind f_cls f ctx b
       
fun normalize_type_visitor_vtable cast gctx : ('this, kcontext) type_visitor_vtable =
  let
    fun adapt f this env b = f b
    fun extend_i this kctx name = shiftx_i_kctx 1 kctx (*an optimization opportunity here by lazy shifting*)
    fun extend_t this kctx name = add_kinding (fst name, Type) kctx
    fun extend_t_anno this kctx (name, k) = add_kinding (fst name, k) kctx
    val vtable =
        default_type_visitor_vtable
          cast
          extend_i
          extend_t
          (visit_imposs "normalize_mt/visit_var")
          (adapt normalize_bs)
          (adapt normalize_i)
          (adapt normalize_s)
          (adapt normalize_k)
          (visit_imposs "update/visit_UVar")
    val vtable = override_extend_t_anno vtable extend_t_anno
    fun visit_MtVar this kctx x =
      let
        val vtable = cast this
        fun normalize_mt a = #visit_mtype vtable this kctx a
      in
        try_retrieve_MtVar normalize_mt gctx kctx x
      end
    val vtable = override_visit_MtVar vtable visit_MtVar
    fun visit_UVar this env (data as (x, r)) =
      let
        val vtable = cast this
      in
        load_uvar' (#visit_mtype vtable this env) (UVar data) x
      end
    val vtable = override_visit_UVar vtable visit_UVar
    fun visit_MtAppI this kctx (data as (t, i)) =
      let
        val vtable = cast this
        fun normalize_mt a = #visit_mtype vtable this kctx a
        fun normalize_i a = #visit_idx vtable this kctx a
        val t = normalize_mt t
        val i = normalize_i i
      in
        case t of
            MtAbsI (_, Bind (_, t), _) => normalize_mt (subst_i_mt i t)
          | _ => MtAppI (t, i)
      end
    val vtable = override_visit_MtAppI vtable visit_MtAppI
    fun visit_MtApp this kctx (data as (t1, t2)) =
      let
        val vtable = cast this
        fun normalize_mt a = #visit_mtype vtable this kctx a
        val t1 = normalize_mt t1
        val t2 = normalize_mt t2
      in
        case t1 of
            MtAbs (_, Bind (_, t1), _) => normalize_mt (subst_t_mt t2 t1)
          | _ => MtApp (t1, t2)
      end
    val vtable = override_visit_MtApp vtable visit_MtApp
  in
    vtable
  end

fun new_normalize_type_visitor a = new_type_visitor normalize_type_visitor_vtable a
    
fun normalize_mt gctx kctx b =
  let
    val visitor as (TypeVisitor vtable) = new_normalize_type_visitor gctx
  in
    #visit_mtype vtable visitor kctx b
  end
    
fun normalize_constr_core gctx kctx b =
  let
    val visitor as (TypeVisitor vtable) = new_normalize_type_visitor gctx
  in
    #visit_constr_core vtable visitor kctx b
  end
    
fun normalize_t gctx kctx b =
  let
    val visitor as (TypeVisitor vtable) = new_normalize_type_visitor gctx
  in
    #visit_ty vtable visitor kctx b
  end
    
(* fun normalize_mt gctx kctx t = *)
(*   let *)
(*     val normalize_mt = normalize_mt gctx *)
(*     (* val () = println $ "begin normalize_mt()" *) *)
(*     val ret = *)
(*         case t of *)
(*             UVar (x, r) => load_uvar' (normalize_mt kctx) t x *)
(*           | Unit r => Unit r *)
(*           | Arrow (t1, d, t2) => Arrow (normalize_mt kctx t1, normalize_i d, normalize_mt kctx t2) *)
(*           | TyArray (t, i) => TyArray (normalize_mt kctx t, normalize_i i) *)
(*           | TyNat (i, r) => TyNat (normalize_i i, r) *)
(*           | Prod (t1, t2) => Prod (normalize_mt kctx t1, normalize_mt kctx t2) *)
(*           | UniI (s, bind, r) => UniI (normalize_s s, normalize_ibind normalize_mt kctx bind, r) *)
(*           | MtVar x => try_retrieve_MtVar (normalize_mt kctx) gctx kctx x *)
(*           | MtAbsI (s, bind, r) => MtAbsI (normalize_bs s, normalize_ibind normalize_mt kctx bind, r) *)
(*           | MtAppI (t, i) => *)
(*             let *)
(*               val t = normalize_mt kctx t *)
(*               val i = normalize_i i *)
(*             in *)
(*               case t of *)
(*                   MtAbsI (_, Bind (_, t), _) => normalize_mt kctx (subst_i_mt i t) *)
(*                 | _ => MtAppI (t, i) *)
(*             end *)
(*           | MtAbs (k, bind, r) => *)
(*             let *)
(*               val k = normalize_k k *)
(*               val t = MtAbs (k, normalize_tbind normalize_mt kctx k bind, r) *)
(*             in *)
(*               t *)
(*             end *)
(*           | MtApp (t1, t2) => *)
(*             let *)
(*               val t1 = normalize_mt kctx t1 *)
(*               val t2 = normalize_mt kctx t2 *)
(*             in *)
(*               case t1 of *)
(*                   MtAbs (_, Bind (_, t1), _) => normalize_mt kctx (subst_t_mt t2 t1) *)
(*                 | _ => MtApp (t1, t2) *)
(*             end *)
(*           | BaseType a => BaseType a *)
(*           | TDatatype (dt, r) => *)
(*             let *)
(*               fun get_kind (Bind dt) = *)
(*                 let *)
(*                   val (tname_kinds, (bsorts, _)) = unfold_binds $ snd dt *)
(*                 in *)
(*                   (length tname_kinds, bsorts) *)
(*                 end *)
(*               fun on_body kctx (bsorts, constr_decls) = *)
(*                 (bsorts, (map o map2_3) (normalize_constr_core gctx kctx) constr_decls) *)
(*               val dt = normalize_tbind (normalize_tbinds (const_fun Type) id on_body) kctx (get_kind dt) $ dt *)
(*             in *)
(*               TDatatype (dt, r) *)
(*             end *)
(*     (* val () = println $ "end normalize_mt()" *) *)
(*   in *)
(*     ret *)
(*   end *)

(* and normalize_constr_core gctx kctx c = *)
(*   let *)
(*     fun on_body kctx (t, is) = *)
(*       let *)
(*         val t = normalize_mt gctx kctx t *)
(*         val is = map normalize_i is *)
(*       in *)
(*         (t, is) *)
(*       end *)
(*   in *)
(*     normalize_ibinds normalize_s on_body kctx c *)
(*   end *)
    
(* fun normalize_t gctx kctx t = *)
(*   case t of *)
(*       Mono t => Mono (normalize_mt gctx kctx t) *)
(*     | Uni (Bind (name, t), r) => Uni (Bind (name, normalize_t gctx (add_kinding (fst name, Type) kctx) t), r) *)

fun normalize_k k = mapSnd (map normalize_bs) k

fun normalize_ke gctx kctx ((k, t) : kind_ext) = (normalize_k k, Option.map (normalize_mt gctx kctx) t)

fun normalize_c gctx kctx ((x, core) : mtype constr) : mtype constr =
  let
    val core = normalize_tbinds (const_fun Type) id (normalize_constr_core gctx) kctx core
  in
    (x, core)
  end

fun normalize_ctx gctx ((sctx, kctx, cctx, tctx) : context) =
  let
    val sctx = map (mapSnd normalize_s) sctx
    val kctx = foldr (fn ((name, ke), kctx) => (name, normalize_ke gctx kctx ke) :: kctx) [] kctx
    val cctx = map (mapSnd (normalize_c gctx kctx)) cctx
    val tctx = map (mapSnd (normalize_t gctx kctx)) tctx
  in
    (sctx, kctx, cctx, tctx)
  end

fun normalize_sgntr gctx sg =
  case sg of
      Sig ctx => Sig $ normalize_ctx gctx ctx
    | FunctorBind ((arg_name, arg), body) =>
      let
        val arg = normalize_ctx gctx arg
      in
        FunctorBind ((arg_name, arg), normalize_ctx (add_sigging (arg_name, arg) gctx) body)
      end

fun normalize_sgntr_list gctx0 gctx =
  fst $ foldr (fn ((name, sg), (acc, gctx)) => let val p = (name, normalize_sgntr gctx sg) in (p :: acc, add p gctx) end) ([], gctx0) gctx

fun normalize_gctx gctx0 gctx =
  let
    val gctx0 = Gctx.union (gctx0, gctx)
  in
    Gctx.map (normalize_sgntr gctx0) gctx
  end

open VC
       
fun normalize_hyp h =
    case h of
        VarH (name, b) => VarH (name, normalize_bs b)
      | PropH p => PropH (normalize_p p)

fun normalize_vc ((hyps, p) : vc) : vc =
    let
      val hyps = map normalize_hyp hyps
      val p = normalize_p p
    in
      (hyps, p)
    end

end
