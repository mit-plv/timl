structure NameResolve = struct
structure S = NamefulExpr
structure T = UnderscoredExpr
open T
open Region
open Gctx
open List
       
exception Error of region * string

infixr 0 $

(* sorting context *)
type scontext = string list
(* kinding context *)
(* type kinding = kind *)
type kcontext = string list 
(* constructor context *)
type ccontext = (string * string list) list
(* typing context *)
type tcontext = string list
type context = scontext * kcontext * ccontext * tcontext
datatype sgntr =
         Sig of (* ns_sigcontext *  *)context
         | FunctorBind of (string * context) (* list *) * context
                                                            
fun is_FunctorBind s =
  case s of
      FunctorBind a => SOME a
    | _ => NONE

type ns_sigcontext = sgntr Gctx.map
                                   
fun runError m _ =
    OK (m ())
    handle
    Error e => Failed e

fun on_id ctx (x, r) =
    case find_idx x ctx of
	SOME i => (i, r)
      | NONE => raise Error (r, sprintf "Unbound variable $ in context: $" [x, str_ls id ctx])

fun filter_module gctx =
    Gctx.mapPartial (fn sg => case sg of Sig sg => SOME sg | _ => NONE) gctx

fun ns_lookup_module gctx m =
    nth_error2 (filter_module gctx) m

fun names ctx = map fst ctx

fun ctx_names ((sctx, kctx, cctx, tctx) : context) =
    (sctx, kctx, names cctx, tctx) 

fun gctx_names (gctx : ns_sigcontext) =
    let
      val gctx = filter_module gctx
      val gctx = Gctx.map ctx_names gctx
    in
      gctx
    end
      
fun find_long_id gctx sel eq ctx (m, (x, xr)) =
    case m of
        NONE =>
        opt_bind (findOptionWithIdx (eq x) ctx)
                 (fn x => opt_return (NONE, (x, xr)))
      | SOME (m, mr) =>
        opt_bind (ns_lookup_module gctx m)
                 (fn (m, sg) =>
                     opt_bind (findOptionWithIdx (eq x) $ sel sg)
                              (fn x => opt_return (SOME (m, mr), (x, xr))))
                 
fun on_long_id gctx sel ctx x =
    case find_long_id gctx sel is_eq_snd ctx x of
        SOME x => x
      | NONE => raise Error (S.get_region_long_id x, sprintf "Unbound (long) variable '$' in context: $ $" [S.str_long_id #1 empty [] x, str_ls id ctx, str_ls id $ domain gctx])
                      
fun find_constr (gctx : ns_sigcontext) ctx x =
    flip Option.map (find_long_id gctx #3 is_eq_fst_snd ctx x)
         (fn (m, ((i, inames), xr)) => ((m, (i, xr)), inames))
         
fun on_ibind f ctx (Bind (name, inner) : ((string * 'a) * 'b) ibind) = Bind (name, f (fst name :: ctx) inner)

fun on_quan q =
    case q of
        Forall => Forall
      | Exists _ => Exists NONE

structure IdxVisitor = IdxVisitorFn (structure S = S.Idx
                                     structure T = T.Idx)
open IdxVisitor
                           
(***************** the "import" (or name-resolving) visitor: converting nameful terms to de Bruijn indices **********************)    
    
fun import_idx_visitor_vtable cast gctx : ('this, scontext) idx_visitor_vtable =
  let
    fun extend this env x1 = fst x1 :: env
    fun visit_var this env x =
      on_long_id gctx #1 env x
    fun visit_quan _ _ q = on_quan q
  in
    default_idx_visitor_vtable
      cast
      extend
      visit_var
      visit_noop
      visit_noop
      visit_noop
      visit_quan
  end

fun new_import_idx_visitor a = new_idx_visitor import_idx_visitor_vtable a
    
fun on_bsort b =
  let
    val visitor as (IdxVisitor vtable) = new_import_idx_visitor empty
  in
    #visit_bsort vtable visitor [] b
  end
    
fun on_idx gctx ctx b =
  let
    val visitor as (IdxVisitor vtable) = new_import_idx_visitor gctx
  in
    #visit_idx vtable visitor ctx b
  end
    
fun on_prop gctx ctx b =
  let
    val visitor as (IdxVisitor vtable) = new_import_idx_visitor gctx
  in
    #visit_prop vtable visitor ctx b
  end
    
fun on_sort gctx ctx b =
  let
    val visitor as (IdxVisitor vtable) = new_import_idx_visitor gctx
  in
    #visit_sort vtable visitor ctx b
  end
    
(* fun on_bsort bs = *)
(*     case bs of *)
(*         S.Base b => Base b *)
(*       | S.BSArrow (a, b) => BSArrow (on_bsort a, on_bsort b) *)
(*       | S.UVarBS u => UVarBS u *)

(* fun on_idx (gctx : ns_sigcontext) ctx i = *)
(*     let *)
(*       val on_idx = on_idx gctx *)
(*     in *)
(*       case i of *)
(* 	  S.VarI x => VarI (on_long_id gctx #1 ctx x) *)
(*         | S.IConst c => IConst c *)
(*         | S.UnOpI (opr, i, r) => UnOpI (opr, on_idx ctx i, r) *)
(* 	| S.BinOpI (opr, i1, i2) => BinOpI (opr, on_idx ctx i1, on_idx ctx i2) *)
(*         | S.Ite (i1, i2, i3, r) => Ite (on_idx ctx i1, on_idx ctx i2, on_idx ctx i3, r) *)
(*         | S.IAbs (bs, bind, r) => IAbs (on_bsort bs, on_ibind on_idx ctx bind, r) *)
(*         | S.UVarI u => UVarI u *)
(*     end *)
      
(* fun on_prop gctx ctx p = *)
(*     let *)
(*       val on_prop = on_prop gctx *)
(*     in *)
(*       case p of *)
(* 	  S.PTrueFalse b => PTrueFalse b *)
(*         | S.Not (p, r) => Not (on_prop ctx p, r) *)
(* 	| S.BinConn (opr, p1, p2) => BinConn (opr, on_prop ctx p1, on_prop ctx p2) *)
(* 	| S.BinPred (opr, i1, i2) => BinPred (opr, on_idx gctx ctx i1, on_idx gctx ctx i2) *)
(*         | S.Quan (q, bs, bind, r_all) => Quan (on_quan q, on_bsort bs, on_ibind on_prop ctx bind, r_all) *)
(*     end *)

(* fun on_sort gctx ctx s = *)
(*     case s of *)
(* 	S.Basic (b, r) => Basic (on_bsort b, r) *)
(*       | S.Subset ((s, r1), bind, r_all) => Subset ((on_bsort s, r1), on_ibind (on_prop gctx) ctx bind, r_all) *)
(*       | S.UVarS u => UVarS u *)
(*       | S.SAbs (b, bind, r) => SAbs (on_bsort b, on_ibind (on_sort gctx) ctx bind, r) *)
(*       | S.SApp (s, i) => SApp (on_sort gctx ctx s, on_idx gctx ctx i) *)

fun on_kind k = mapSnd (map on_bsort) k

open Bind
       
fun on_tbind f kctx (Bind (name, b) : ((string * 'a) * 'b) tbind) = 
  Bind (name, f (fst name :: kctx) b)

fun on_binds on_bind on_anno on_inner ctx ibinds =
  let
    val on_binds = on_binds on_bind on_anno on_inner
  in
    case ibinds of
        BindNil inner => BindNil (on_inner ctx inner)
      | BindCons (anno, bind) =>
        BindCons (on_anno ctx anno, on_bind on_binds ctx bind)
  end

fun on_ibinds on_anno on_inner ctx (ibinds : ('a, string * 'b, 'c) ibinds) = on_binds on_ibind on_anno on_inner ctx ibinds
(* fun on_ibinds on_anno on_inner ctx ibinds = *)
(*   let *)
(*     val on_ibinds = on_ibinds on_anno on_inner *)
(*   in *)
(*     case ibinds of *)
(*         BindNil inner => BindNil (on_inner ctx inner) *)
(*       | BindCons (anno, bind) => *)
(*         BindCons (on_anno ctx anno, on_ibind_generic on_ibinds ctx bind) *)
(*   end *)

fun on_tbinds on_anno on_inner ctx (tbinds : ('a, string * 'b, 'c) tbinds) = on_binds on_tbind on_anno on_inner ctx tbinds
                                                                                         
fun get_datatype_names (Bind (name, tbinds)) =
    let
      val (_, (_, constr_decls)) = unfold_binds tbinds
      val cnames = map (fn (name, core, _) => (fst name, get_constr_inames core)) constr_decls
    in
      (fst name, cnames)
    end
      
structure TV = TypeVisitorFn (structure S = S.Type
                                       structure T = T.Type)
                                         
fun on_i_type_visitor_vtable (cast : 'this -> ('this, scontext * kcontext) TV.type_visitor_vtable) gctx : ('this, scontext * kcontext) TV.type_visitor_vtable =
  let
    fun extend_i this (sctx, kctx) name = (fst name :: sctx, kctx)
    fun extend_t this (sctx, kctx) name = (sctx, fst name :: kctx)
    fun visit_var this (sctx, kctx) x =
      on_long_id gctx #2 kctx x
    fun for_idx f this (sctx, kctx) b = f gctx sctx b
    fun for_bsort f _ _ b = f b
    val vtable = 
        TV.default_type_visitor_vtable
          cast
          extend_i
          extend_t
          visit_var
          (for_bsort on_bsort)
          (for_idx on_idx)
          (for_idx on_sort)
          (for_bsort on_kind)
          visit_noop
    fun visit_MtAppI this ctx (data as (t1, i)) =
      let
        val vtable = cast this
        fun default () = MtAppI (#visit_mtype vtable this ctx t1, #visit_idx vtable this ctx i)
        val t = S.MtAppI data
      in
        case S.is_AppV t of
            SOME (x, ts, is) =>
            let
              val ts = map (#visit_mtype vtable this ctx) ts
              val is = map (#visit_idx vtable this ctx) (is : S.idx list)
            in
              if S.eq_long_id (x, (NONE, ("nat", dummy))) andalso length ts = 0 andalso length is = 1 then
                TyNat (hd is, S.get_region_mt t)
              else if S.eq_long_id (x, (NONE, ("array", dummy))) andalso length ts = 1 andalso length is = 1 then
                TyArray (hd ts, hd is)
              else
                default ()
            end
          | NONE => default ()         
      end
    val vtable = TV.override_visit_MtAppI vtable visit_MtAppI
  in
    vtable
  end

fun new_on_i_type_visitor a = TV.new_type_visitor on_i_type_visitor_vtable a
    
fun on_mtype gctx ctx b =
  let
    val visitor as (TV.TypeVisitor vtable) = new_on_i_type_visitor gctx
  in
    #visit_mtype vtable visitor ctx b
  end
    
fun on_datatype gctx ctx b =
  let
    val visitor as (TV.TypeVisitor vtable) = new_on_i_type_visitor gctx
  in
    #visit_datatype vtable visitor ctx b
  end
    
fun on_constr_core gctx ctx b =
  let
    val visitor as (TV.TypeVisitor vtable) = new_on_i_type_visitor gctx
  in
    #visit_constr_core vtable visitor ctx b
  end
    
fun on_type gctx ctx b =
  let
    val visitor as (TV.TypeVisitor vtable) = new_on_i_type_visitor gctx
  in
    #visit_ty vtable visitor ctx b
  end
    
(* fun on_mtype gctx (ctx as (sctx, kctx)) t = *)
(*     let *)
(*       val on_mtype = on_mtype gctx *)
(*     in *)
(*       case t of *)
(* 	  S.Arrow (t1, d, t2) => Arrow (on_mtype ctx t1, on_idx gctx sctx d, on_mtype ctx t2) *)
(*         | S.TyArray (t, i) => TyArray (on_mtype ctx t, on_idx gctx sctx i) *)
(*         | S.TyNat (i, r) => TyNat (on_idx gctx sctx i, r) *)
(*         | S.Unit r => Unit r *)
(* 	| S.Prod (t1, t2) => Prod (on_mtype ctx t1, on_mtype ctx t2) *)
(* 	| S.UniI (s, bind, r_all) => UniI (on_sort gctx sctx s, on_ibind (fn sctx => on_mtype (sctx, kctx)) sctx bind, r_all) *)
(*         | S.MtVar x => MtVar $ on_long_id gctx #2 kctx x *)
(*         | S.MtApp (t1, t2) => MtApp (on_mtype ctx t1, on_mtype ctx t2) *)
(*         | S.MtAbs (k, bind, r_all) => MtAbs (on_kind k, on_tbind (fn kctx => (on_mtype (sctx, kctx))) kctx bind, r_all) *)
(*         | S.MtAppI (t1, i) => *)
(*           let *)
(*             fun default () = MtAppI (on_mtype ctx t1, on_idx gctx sctx i) *)
(*           in *)
(*             case S.is_AppV t of *)
(*                 SOME (x, ts, is) => *)
(*                 let *)
(*                   val ts = map (on_mtype ctx) ts *)
(*                   val is = map (on_idx gctx sctx) is *)
(*                 in *)
(*                   if S.eq_long_id (x, (NONE, ("nat", dummy))) andalso length ts = 0 andalso length is = 1 then *)
(*                     TyNat (hd is, S.get_region_mt t) *)
(*                   else if S.eq_long_id (x, (NONE, ("array", dummy))) andalso length ts = 1 andalso length is = 1 then *)
(*                     TyArray (hd ts, hd is) *)
(*                   else *)
(*                     default () *)
(*                 end *)
(*               | NONE => default ()          *)
(*           end *)
(*         | S.MtAbsI (b, bind, r_all) => MtAbsI (on_bsort b, on_ibind (fn sctx => on_mtype (sctx, kctx)) sctx bind, r_all) *)
(* 	| S.BaseType (bt, r) => BaseType (bt, r) *)
(*         | S.UVar u => UVar u *)
(*         | S.TDatatype (dt, r) => *)
(*           let *)
(*             val dt = on_datatype gctx ctx dt *)
(*           in *)
(*             TDatatype (dt, r) *)
(*           end *)
(*     end *)

(* and on_datatype gctx (sctx, kctx) dt = *)
(*     let *)
(*       fun on_constr_decl kctx (cname, core, r) = *)
(*         (cname, on_constr_core gctx (sctx, kctx) core, r) *)
(*       fun on_constrs kctx (sorts, constr_decls) = *)
(*         (map on_bsort sorts, map (on_constr_decl kctx) constr_decls) *)
(*       val dt = on_tbind (on_tbinds return2 on_constrs) kctx dt *)
(*     in *)
(*       dt *)
(*     end *)

(* and on_constr_core gctx (ctx as (sctx, kctx)) (ibinds : S.mtype S.constr_core) : mtype constr_core = *)
(*     on_ibinds (on_sort gctx) (fn sctx => fn (t, is) => (on_mtype gctx (sctx, kctx) t, map (on_idx gctx sctx) is)) sctx ibinds *)
      
(* fun on_type gctx (ctx as (sctx, kctx)) t = *)
(*     let *)
(*       val on_type = on_type gctx *)
(*     in *)
(*       case t of *)
(* 	  S.Mono t => Mono (on_mtype gctx ctx t) *)
(* 	| S.Uni (Bind ((name, r), t), r_all) => Uni (Bind ((name, r), on_type (sctx, name :: kctx) t), r_all) *)
(*     end *)
      
fun on_ptrn gctx (ctx as (sctx, kctx, cctx)) pn =
    let
      val on_ptrn = on_ptrn gctx
    in
      case pn of
	  S.ConstrP (Outer ((x, ()), eia), inames, pn, Outer r) =>
          (case find_constr gctx cctx x of
	       SOME (x, c_inames) =>
               let
                 val inames =
                     if eia then
                       inames
                     else
                       if length inames = 0 then map (str2ibinder o prefix "__") c_inames
                       else raise Error (r, "Constructor pattern can't have explicit index pattern arguments. Use [@constructor_name] if you want to write explict index pattern arguments.")
               in
                 ConstrP (Outer ((x, ()), true), inames, on_ptrn ctx pn, Outer r)
               end
	     | NONE =>
               raise Error (S.get_region_long_id x, "Unknown constructor " ^ S.str_long_id #1 empty [] x)
          )
        | S.VarP ename =>
          let
            val name = unBinderName ename
          in
            case find_constr gctx cctx (NONE, name) of
	        SOME (x, c_inames) =>
                let
                  val r = snd name
                  val inames = map (str2ibinder o prefix "__") c_inames
                in
                  ConstrP (Outer ((x, ()), true), inames, TTP $ Outer r, Outer r)
                end
	      | NONE =>
                VarP ename
          end
        | S.PairP (pn1, pn2) =>
          PairP (on_ptrn ctx pn1, on_ptrn ctx pn2)
        | S.TTP r =>
          TTP r
        | S.AliasP (name, pn, r) =>
          AliasP (name, on_ptrn ctx pn, r)
        | S.AnnoP (pn, Outer t) =>
          AnnoP (on_ptrn ctx pn, Outer $ on_mtype gctx (sctx, kctx) t)
    end

fun on_constr gctx (ctx as (sctx, kctx)) ((family, tbinds) : S.mtype S.constr) : mtype constr =
    (on_long_id gctx #2 kctx family,
     on_tbinds return2 (fn kctx => on_constr_core gctx (sctx, kctx)) kctx tbinds)

fun on_return gctx (ctx as (sctx, _)) return = mapPair (Option.map (on_mtype gctx ctx), Option.map (on_idx gctx sctx)) return

fun shift_return (sctxn, kctxn) (t, d) =
    let
      open Subst
    in
      (Option.map (fn t => shiftx_t_mt 0 kctxn $ shiftx_i_mt 0 sctxn t) t,
       Option.map (fn d => shiftx_i_i 0 sctxn d) d)
    end
      
fun copy_anno gctx (anno as (t, d)) e =
    let
      val copy_anno = copy_anno gctx
      val copy_anno_rule = copy_anno_rule gctx
      fun copy a b = case a of
                         NONE => b
                       | SOME _ => a
    in
      case e of
          ECase (e, (t', d'), es, r) =>
          let
            fun is_tuple_value e =
                case e of
                    EVar _ => true
                  | EBinOp (EBPair, e1, e2) => is_tuple_value e1 andalso is_tuple_value e2
                  | _ => false
            (* if e is tuple value, we are sure it doesn't cost time, so we can copy time annotation *)
            val d = if is_tuple_value e then d else NONE
            val (t, d) = (copy t' t, copy d' d)
            val es = map (copy_anno_rule (t, d)) es
          in
            ECase (e, (t, d), es, r)
          end
        | ELet ((t', d'), bind, r) =>
          let
            val (decls, e) = Unbound.unBind bind
            val decls = unTeles decls
            val (t, d) = (copy t' t, copy d' d)
            val (_, (sctx, kctx, _, _)) = str_decls gctx ([], [], [], []) decls
            val (sctxn, kctxn) = (length sctx, length kctx)
            fun is_match_var decl =
                case decl of
                    DValPtrn (_, Outer (EVar _), _) => true
                  | DVal (_, Outer bind, _) =>
                    let
                      val (_, e) = Unbound.unBind bind
                    in
                      case e of
                          EVar _ => true
                        | _ => false
                    end
                  | _ => false
            val d' = if List.all is_match_var decls then d else NONE
          in
            ELet ((t, d), Unbound.Bind (Teles decls, copy_anno (shift_return (sctxn, kctxn) (t, d')) e), r)
          end
        | EAsc (e, t') =>
          let
            val t = SOME t'
            val e = copy_anno (t, d) e
          in
            EAsc (e, t')
          end
        | EEI (EEIAscTime, e, d') =>
          let
            val d = SOME d'
            val e = copy_anno (t, d) e
          in
            EAscTime (e, d')
          end
        | ET (ETNever, _, _) => e
        | _ =>
          case t of
              SOME t => EAsc (e, t)
            | NONE => e
    end
      
and copy_anno_rule gctx return bind =
    let
      val (pn, e) = Unbound.unBind bind
      val (sctx, _) = ptrn_names pn
      val offset = (length sctx, 0)
    in
      Unbound.Bind (pn, copy_anno gctx (shift_return offset return) e)
    end
      
val empty_ctx = ([], [], [], [])
fun add_sorting_skct name (sctx, kctx, cctx, tctx) = (name :: sctx, kctx, cctx, tctx)
fun add_kinding_skct name (sctx, kctx, cctx, tctx) = (sctx, name :: kctx, cctx, tctx)
fun add_typing_skct name (sctx, kctx, cctx, tctx) = (sctx, kctx, cctx, name :: tctx)
fun add_ctx (sctxd, kctxd, cctxd, tctxd) (sctx, kctx, cctx, tctx) =
    (sctxd @ sctx, kctxd @ kctx, cctxd @ cctx, tctxd @ tctx)
      
fun on_expr gctx (ctx as (sctx, kctx, cctx, tctx)) e =
    let
      val on_expr = on_expr gctx
      (* val () = println $ sprintf "on_expr $ in context $" [S.str_e ctx e, join " " tctx] *)
      val skctx = (sctx, kctx)
    in
      case e of
	  S.EVar (x, b) => 
	  (case find_constr gctx cctx x of
	       SOME (x, _) => EAppConstr ((x, b), [], [], ETT $ get_region_long_id x, NONE)
	     | NONE => EVar ((on_long_id gctx #4 tctx x), b)
          )
        | S.EConst c => EConst c
	| S.EUnOp (opr, e, r) => EUnOp (opr, on_expr ctx e, r)
	| S.EBinOp (opr, e1, e2) =>
          (case opr of
	       EBApp => 
	       let
                 val e2 = on_expr ctx e2
	         fun default () = 
                   EApp (on_expr ctx e1, e2)
	         val (e1, is) = S.collect_EAppI e1 
	       in
	         case e1 of
		     S.EVar (x, b) =>
		     (case find_constr gctx cctx x of
		          SOME (x, _) => EAppConstr ((x, b), [], map (on_idx gctx sctx) is, e2, NONE)
		        | NONE => default ())
	           | _ => default ()
	       end
	     | _ => EBinOp (opr, on_expr ctx e1, on_expr ctx e2)
          )
	| S.ETriOp (opr, e1, e2, e3) => ETriOp (opr, on_expr ctx e1, on_expr ctx e2, on_expr ctx e3)
	| S.EEI (opr, e, i) =>
          (case opr of
	       EEIAppI => 
	       let
                 fun default () = 
                   EAppI (on_expr ctx e, on_idx gctx sctx i)
	         val (e, is) = S.collect_EAppI e
                 val is = is @ [i]
	       in
	         case e of
		     S.EVar (x, b) =>
		     (case find_constr gctx cctx x of
		          SOME (x, _) => EAppConstr ((x, b), [], map (on_idx gctx sctx) is, ETT (S.get_region_i i), NONE)
		        | NONE => default ())
	           | _ => default ()
	       end
	     | EEIAscTime =>
               let
                 val i = on_idx gctx sctx i
                 val e = on_expr ctx e
                 val e = copy_anno (gctx_names gctx) (NONE, SOME i) e
               in
                 EAscTime (e, i)
               end
          )
	| S.EET (opr, e, t) =>
          (case opr of
	       EETAppT => raise Impossible "name-resolve/EAppT"
          )
	| S.ET (opr, t, r) => ET (opr, on_mtype gctx skctx t, r)
	| S.EAbs bind => 
          let
            val (pn, e) = Unbound.unBind bind
            val pn = on_ptrn gctx (sctx, kctx, cctx) pn
            val (inames, enames) = ptrn_names pn
            val ctx = (inames @ sctx, kctx, cctx, enames @ tctx)
            val e = on_expr ctx e
          in
            EAbs $ Unbound.Bind (pn, e)
          end
	| S.EAbsI (bind, r_all) =>
          let
            val ((name, s), e) = unBindAnno bind
            val (name, r) = unName name
          in
            EAbsI (BindAnno ((IName (name, r), on_sort gctx sctx s), on_expr (add_sorting_skct name ctx) e), r_all)
          end
	| S.ELet (return, bind, r) =>
          let
            val (decls, e) = Unbound.unBind bind
            val decls = unTeles decls
            val return = on_return gctx skctx return
            val (decls, ctx) = on_decls gctx ctx decls
          in
            ELet (return, Unbound.Bind (Teles decls, on_expr ctx e), r)
          end
	| S.EAsc (e, t) =>
          let
            val t = on_mtype gctx skctx t
            val e = on_expr ctx e
            val e = copy_anno (gctx_names gctx) (SOME t, NONE) e
          in
            EAsc (e, t)
          end
	| S.EAppConstr ((x, b), ts, is, e, ot) => EAppConstr ((on_long_id gctx (map fst o #3) (map fst cctx) x, b), map (on_mtype gctx skctx) ts, map (on_idx gctx sctx) is, on_expr ctx e, Option.map (mapSnd (on_mtype gctx skctx)) ot)
	| S.ECase (e, return, rules, r) =>
          let
            val return = on_return gctx skctx return
            val rules = map (on_rule gctx ctx) rules
            val rules = map (copy_anno_rule (gctx_names gctx) return) rules
          in
            ECase (on_expr ctx e, return, rules, r)
          end
    end

and on_decls gctx (ctx as (sctx, kctx, cctx, tctx)) decls =
    let
      fun f (decl, (acc, ctx)) =
          let val (decl, ctx) = on_decl gctx ctx decl
          in
            (decl :: acc, ctx)
          end
      val (decls, ctx) = foldl f ([], ctx) decls
      val decls = rev decls
    in
      (decls, ctx)
    end

and on_decl gctx (ctx as (sctx, kctx, cctx, tctx)) decl =
    let
      val on_decl = on_decl gctx
    in
      case decl of
          S.DVal (name, Outer bind, Outer r) =>
          let
            val (tnames, e) = Unbound.unBind bind
            val tnames = map unBinderName tnames
            val pn = VarP name
            val ctx' as (sctx', kctx', cctx', _) = (sctx, (rev o map fst) tnames @ kctx, cctx, tctx)
            val pn = on_ptrn gctx (sctx', kctx', cctx') pn
            val e = on_expr gctx ctx' e
            val (inames, enames) = ptrn_names pn
            val ctx = (inames @ sctx, kctx, cctx, enames @ tctx)
          in
            (DVal (name, Outer $ Unbound.Bind (map (Binder o TName) tnames, e), Outer r), ctx)
          end
        | S.DValPtrn (pn, Outer e, Outer r) =>
          let 
            val pn = on_ptrn gctx (sctx, kctx, cctx) pn
            val e = on_expr gctx ctx e
            val (inames, enames) = ptrn_names pn
            val ctx = (inames @ sctx, kctx, cctx, enames @ tctx)
          in
            (DValPtrn (pn, Outer e, Outer r), ctx)
          end
	| S.DRec (name, bind, Outer r) => 
	  let
            val (name, r1) = unBinderName name
            val ((tnames, Rebind binds), ((t, d), e)) = Unbound.unBind $ unInner bind
            val tnames = map unBinderName tnames
            val binds = unTeles binds
	    val ctx as (sctx, kctx, cctx, tctx) = (sctx, kctx, cctx, name :: tctx)
            val ctx_ret = ctx
            val ctx as (sctx, kctx, cctx, tctx) = (sctx, (rev o map fst) tnames @ kctx, cctx, tctx)
            fun f (bind, (binds, ctx as (sctx, kctx, cctx, tctx))) =
                case bind of
                    S.SortingST (name, Outer s) => 
                    (SortingST (name, Outer $ on_sort gctx sctx s) :: binds, add_sorting_skct (binder2str name) ctx)
                  | S.TypingST pn =>
                    let
                      val pn = on_ptrn gctx (sctx, kctx, cctx) pn
                      val (inames, enames) = ptrn_names pn
                    in
                      (TypingST pn :: binds, (inames @ sctx, kctx, cctx, enames @ tctx))
                    end
            val (binds, ctx as (sctx, kctx, cctx, tctx)) = foldl f ([], ctx) binds
            val binds = rev binds
            val t = on_mtype gctx (sctx, kctx) t
            val d = on_idx gctx sctx d
            val e = on_expr gctx ctx e
            val e = copy_anno (gctx_names gctx) (SOME t, SOME d) e
            val decl = DRec (Binder $ EName (name, r1), Inner $ Unbound.Bind ((map (Binder o TName) tnames, Rebind $ Teles binds), ((t, d), e)), Outer r)
          in
            (decl, ctx_ret)
          end
        | S.DIdxDef (name, Outer s, Outer i) =>
          (DIdxDef (name, Outer $ on_sort gctx sctx s, Outer $ on_idx gctx sctx i), add_sorting_skct (binder2str name) ctx)
        | S.DAbsIdx2 (name, Outer s, Outer i) =>
          (DAbsIdx2 (name, Outer $ on_sort gctx sctx s, Outer $ on_idx gctx sctx i), add_sorting_skct (binder2str name) ctx)
        | S.DAbsIdx ((name, Outer s, Outer i), Rebind decls, Outer r) =>
          let
            val (name, r1) = unBinderName name
            val decls = unTeles decls
            val s = on_sort gctx sctx s
            val i = on_idx gctx sctx i
            val ctx = add_sorting_skct name ctx
            val (decls, ctx) = on_decls gctx ctx decls
            val decl = DAbsIdx ((Binder $ IName (name, r1), Outer s, Outer i), Rebind $ Teles decls, Outer r)
          in
            (decl, ctx)
          end
        | S.DTypeDef (name, Outer t) =>
          (case t of
               S.TDatatype (dt, r) =>
               let
                 val dt = on_datatype gctx (sctx, kctx) dt
                 val (tname, cnames) = get_datatype_names dt
                 val ctx = (sctx, tname :: kctx, rev cnames @ cctx, tctx)
               in
                 (DTypeDef (name, Outer $ TDatatype (dt, r)), ctx)
               end
             | _ =>
               let
                 val t = on_mtype gctx (sctx, kctx) t
               in
                 (DTypeDef (name, Outer t), add_kinding_skct (binder2str name) ctx)
               end
          )
        | S.DOpen (Outer (m, r), _) =>
          let
            val (m, ctxd) =
                case ns_lookup_module gctx m of
                    SOME a => a
                  | NONE => raise Error (r, "Unbound module " ^ m)
            val ctx = add_ctx ctxd ctx
            val ctxd = case ctxd of (sctx, kctx, cctx, tctx) =>
                                    (map (Binder o IName o attach_snd r) sctx,
                                     map (Binder o TName o attach_snd r) kctx,
                                     map (Binder o CName o attach_snd r o fst) cctx,
                                     map (Binder o EName o attach_snd r) tctx
                                    )
          in
            (DOpen (Outer (m, r), SOME ctxd), ctx)
          end
    end

and on_rule gctx (ctx as (sctx, kctx, cctx, tctx)) bind =
    let
      val (pn, e) = Unbound.unBind bind
      (* val () = println $ sprintf "on_rule $ in context $" [S.str_rule ctx (pn, e), join " " tctx] *)
      val pn = on_ptrn gctx (sctx, kctx, cctx) pn
      val (inames, enames) = ptrn_names pn
      (* val () = println $ sprintf "enames of $: $" [S.str_pn (sctx, kctx, cctx) pn, join " " enames] *)
      val ctx' = (inames @ sctx, kctx, cctx, enames @ tctx)
    in
      Unbound.Bind (pn, on_expr gctx ctx' e)
    end

fun on_sig gctx (comps, r) =
  let
    fun on_spec (ctx as (sctx, kctx, cctx, tctx)) spec =
      case spec of
          S.SpecVal ((name, r), t) =>
          let
            val t = on_type gctx (sctx, kctx) t
          in
            (SpecVal ((name, r), t), add_typing_skct name ctx)
          end
        | S.SpecIdx ((name, r), s) =>
          let
            val s = on_sort gctx sctx s
          in
            (SpecIdx ((name, r), s), add_sorting_skct name ctx)
          end
        | S.SpecType ((name, r), k) =>
          let
            val k = on_kind k
          in
            (SpecType ((name, r), k), add_kinding_skct name ctx)
          end
        | S.SpecTypeDef ((name, r), t) =>
          (case t of
               S.TDatatype (dt, r) =>
               let
                 val dt = on_datatype gctx (sctx, kctx) dt
                 val (tname, cnames) = get_datatype_names dt
                 val ctx = (sctx, tname :: kctx, rev cnames @ cctx, tctx)
               in
                 (SpecTypeDef ((name, r), TDatatype (dt, r)), ctx)
               end
             | _ =>
               let
                 val t = on_mtype gctx (sctx, kctx) t
               in
                 (SpecTypeDef ((name, r), t), add_kinding_skct name ctx)
               end
          )
    fun iter (spec, (specs, ctx)) =
      let
        val (spec, ctx) = on_spec ctx spec
      in
        (spec :: specs, ctx)
      end
    val (comps, ctx) = foldl iter ([], empty_ctx) comps
    val comps = rev comps
  in
    ((comps, r), ctx)
  end
    
fun on_module gctx m =
    case m of
        S.ModComponents (comps, r) =>
        let
          val (comps, ctx) = on_decls gctx empty_ctx comps
        in
          (ModComponents (comps, r), ctx)
        end
      | S.ModSeal (m, sg) =>
        let
          val (sg, ctx) = on_sig gctx sg
          val (m, _) = on_module gctx m
        in
          (ModSeal (m, sg), ctx)
        end
      | S.ModTransparentAsc (m, sg) =>
        let
          val (sg, _) = on_sig gctx sg
          val (m, ctx) = on_module gctx m
        in
          (ModTransparentAsc (m, sg), ctx)
        end

fun on_top_bind gctx (name, bind) = 
    case bind of
        S.TopModBind m =>
        let
          val (m, ctx) = on_module gctx m
        in
          (TopModBind m, [(name, Sig ctx)])
        end
      (* | S.TopModSpec ((name, r), sg) => *)
      (*   let *)
      (*     val (sg = on_sig gctx sg *)
      (*     val () = open_module (name, sg) *)
      (*   in *)
      (*     [(name, Sig sg)] *)
      (*   end *)
      | S.TopFunctorBind (((arg_name, r2), arg), m) =>
        let
          val (arg, arg_ctx) = on_sig gctx arg
          val gctx = add (arg_name, Sig arg_ctx) gctx
          val (m, body_ctx) = on_module gctx m
        in
          (TopFunctorBind (((arg_name, r2), arg), m), [(name, FunctorBind ((arg_name, arg_ctx), body_ctx))])
        end
      | S.TopFunctorApp ((f, f_r), m) =>
        let
          fun lookup_functor (gctx : ns_sigcontext) m =
            opt_bind (Gctx.find (gctx, m)) is_FunctorBind
          fun fetch_functor gctx (m, r) =
              case lookup_functor gctx m of
                  SOME a => a
                | NONE => raise Error (r, "Unbound functor " ^ m)
          val ((formal_arg_name, formal_arg), body) = fetch_functor gctx (f, f_r)
        in
          (TopFunctorApp ((f, f_r), m), [(name, Sig body), (formal_arg_name, Sig formal_arg)])
        end
          
and on_prog gctx binds =
    let
      fun iter (((name, r), bind), (binds, acc, gctx)) =
          let
            val (bind, gctxd) = on_top_bind gctx (name, bind)
          in
            (((name, r), bind) :: binds, gctxd @ acc, addList (gctx, gctxd))
          end
      val (binds, gctxd, gctx) = foldl iter ([], [], gctx) binds
      val binds = rev binds
    in
      (binds, gctxd, gctx)
    end

val resolve_type = on_type
val resolve_expr = on_expr
fun resolve_decls gctx ctx decls = fst (on_decls gctx ctx decls)
val resolve_prog = on_prog

val resolve_constr = on_constr
val resolve_kind = on_kind

fun resolve_type_opt ctx e = runError (fn () => on_type ctx e) ()
fun resolve_expr_opt ctx e = runError (fn () => on_expr ctx e) ()

fun resolve_constr_opt ctx e = runError (fn () => on_constr ctx e) ()
fun resolve_kind_opt e = runError (fn () => on_kind e) ()

end
