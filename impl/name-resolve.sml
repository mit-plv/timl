structure NameResolve = struct
structure E = NamefulExpr
open UnderscoredExpr

open Region
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
         Sig of (* sigcontext *  *)context
         | FunctorBind of (string * context) (* list *) * context
type sigcontext = (string * sgntr) list
                                   
fun runError m _ =
    OK (m ())
    handle
    Error e => Failed e

fun on_id ctx (x, r) =
    case find_idx x ctx of
	SOME i => (i, r)
      | NONE => raise Error (r, "Unbound variable " ^ x ^ sprintf " in context: $" [join " " $ rev ctx])

fun lookup_module gctx m =
    find_idx_value m (List.mapPartial (fn (name, sg) => case sg of Sig sg => SOME (name, sg) | _ => NONE) gctx)
                   
fun find_long_id gctx sel eq ctx (m, (x, xr)) =
    case m of
        NONE =>
        opt_bind (findOptionWithIdx (eq x) ctx)
                 (fn x => opt_return (NONE, (x, xr)))
      | SOME (m, mr) =>
        opt_bind (lookup_module gctx m)
                 (fn (m, sg) =>
                     opt_bind (findOptionWithIdx (eq x) $ sel sg)
                              (fn x => opt_return (SOME (m, mr), (x, xr))))
                 
fun on_long_id gctx sel ctx x =
    case find_long_id gctx sel is_eq_snd ctx x of
        SOME x => x
      | NONE => raise Error (E.get_region_long_id x, sprintf "Unbound variable $ in context: $" [E.str_long_id [] [] x, join " " $ rev $ ctx @ map fst gctx])
                      
fun find_constr (gctx : sigcontext) ctx x =
    flip Option.map (find_long_id gctx #3 is_eq_fst_snd ctx x)
         (fn (m, ((i, inames), xr)) => ((m, (i, xr)), inames))
         
fun on_idx (gctx : sigcontext) ctx i =
    let
      val on_idx = on_idx gctx
    in
      case i of
	  E.VarI x => VarI (on_long_id gctx #1 ctx x)
	| E.ConstIN n => ConstIN n
	| E.ConstIT c => ConstIT c
        | E.UnOpI (opr, i, r) => UnOpI (opr, on_idx ctx i, r)
        | E.DivI (i1, n2) => DivI (on_idx ctx i1, n2)
        | E.ExpI (i1, n2) => ExpI (on_idx ctx i1, n2)
	| E.BinOpI (opr, i1, i2) => BinOpI (opr, on_idx ctx i1, on_idx ctx i2)
        | E.Ite (i1, i2, i3, r) => Ite (on_idx ctx i1, on_idx ctx i2, on_idx ctx i3, r)
	| E.TrueI r => TrueI r
	| E.FalseI r => FalseI r
	| E.TTI r => TTI r
        | E.TimeAbs ((name, r1), i, r) => TimeAbs ((name, r1), on_idx (name :: ctx) i, r)
        | E.AdmitI r => AdmitI r
        | E.UVarI u => UVarI u
    end
      
fun on_bsort bs =
    case bs of
        E.Base b => Base b
      | E.UVarBS u => UVarBS u

fun on_quan q =
    case q of
        Forall => Forall
      | Exists _ => Exists NONE
                           
fun on_ibind f ctx (E.Bind ((name, r), inner)) = Bind ((name, r), f (name :: ctx) inner)

fun on_prop gctx ctx p =
    let
      val on_prop = on_prop gctx
    in
      case p of
	  E.True r => True r
	| E.False r => False r
        | E.Not (p, r) => Not (on_prop ctx p, r)
	| E.BinConn (opr, p1, p2) => BinConn (opr, on_prop ctx p1, on_prop ctx p2)
	| E.BinPred (opr, i1, i2) => BinPred (opr, on_idx gctx ctx i1, on_idx gctx ctx i2)
        | E.Quan (q, bs, bind, r_all) => Quan (on_quan q, on_bsort bs, on_ibind on_prop ctx bind, r_all)
    end

fun on_sort gctx ctx s =
    case s of
	E.Basic (s, r) => Basic (on_bsort s, r)
      | E.Subset ((s, r1), bind, r_all) => Subset ((on_bsort s, r1), on_ibind (on_prop gctx) ctx bind, r_all)
      | E.UVarS u => UVarS u

fun on_mtype gctx (ctx as (sctx, kctx)) t =
    let
      val on_mtype = on_mtype gctx
    in
      case t of
	  E.Arrow (t1, d, t2) => Arrow (on_mtype ctx t1, on_idx gctx sctx d, on_mtype ctx t2)
        | E.Unit r => Unit r
	| E.Prod (t1, t2) => Prod (on_mtype ctx t1, on_mtype ctx t2)
	| E.UniI (s, E.Bind ((name, r), t), r_all) => UniI (on_sort gctx sctx s, Bind ((name, r), on_mtype (name :: sctx, kctx) t), r_all)
        | E.MtVar x => MtVar $ on_long_id gctx #2 kctx x
        (* | E.MtApp (t1, t2) => MtApp (on_mtype ctx t1, on_mtype ctx t2) *)
        (* | E.MtAbs (Bind ((name, r), t), r_all) => MtAbs (Bind ((name, r), on_mtype (sctx, name :: kctx) t), r_all) *)
        (* | E.MtAppI (t, i) => MtAppI (on_mtype ctx t, on_idx gctx sctx i) *)
        (* | E.MtAbsI (s, Bind ((name, r), t), r_all) => MtAbsI (on_sort gctx sctx s, Bind ((name, r), on_mtype (name :: sctx, kctx) t), r_all) *)
        | E.AppV (x, ts, is, r) => AppV (on_long_id gctx #2 kctx x, map (on_mtype ctx) ts, map (on_idx gctx sctx) is, r)
	| E.BaseType (bt, r) => BaseType (bt, r)
        | E.UVar u => UVar u
    end

fun on_type gctx (ctx as (sctx, kctx)) t =
    let
      val on_type = on_type gctx
    in
      case t of
	  E.Mono t => Mono (on_mtype gctx ctx t)
	| E.Uni (Bind ((name, r), t), r_all) => Uni (Bind ((name, r), on_type (sctx, name :: kctx) t), r_all)
    end
      
fun on_ptrn gctx (ctx as (sctx, kctx, cctx)) pn =
    let
      val on_ptrn = on_ptrn gctx
    in
      case pn of
	  E.ConstrP ((x, eia), inames, pn, r) =>
          (case find_constr gctx cctx x of
	       SOME (x, c_inames) =>
               let
                 val inames =
                     if eia then
                       inames
                     else
                       if length inames = 0 then map (prefix "__") c_inames
                       else raise Error (r, "Constructor pattern can't have explicit index pattern arguments. Use [@constructor_name] if you want to write explict index pattern arguments.")
               in
                 ConstrP ((x, true), inames, Option.map (on_ptrn ctx) pn, r)
               end
	     | NONE =>
               (case (fst x, eia, inames, pn) of
                    (NONE, false, [], NONE) => VarP $ snd x
                  | _ =>
                    raise Error (E.get_region_long_id x, "Unknown constructor " ^ E.str_long_id [] [] x)
               )
          )
        | E.VarP name =>
          VarP name
        | E.PairP (pn1, pn2) =>
          PairP (on_ptrn ctx pn1, on_ptrn ctx pn2)
        | E.TTP r =>
          TTP r
        | E.AliasP (name, pn, r) =>
          AliasP (name, on_ptrn ctx pn, r)
        | E.AnnoP (pn, t) =>
          AnnoP (on_ptrn ctx pn, on_mtype gctx (sctx, kctx) t)
    end

fun on_ibinds on_anno on_inner ctx ibinds =
    case ibinds of
        BindNil inner => BindNil (on_inner ctx inner)
      | BindCons (anno, E.Bind (name, ibinds)) =>
        BindCons (on_anno ctx anno, Bind (name, on_ibinds on_anno on_inner (name :: ctx) ibinds))

fun on_constr_core gctx (ctx as (sctx, kctx)) tnames (ibinds : E.constr_core) : constr_core =
    on_ibinds (on_sort gctx) (fn sctx => fn (t, is) => (on_mtype gctx (sctx, rev tnames @ kctx) t, map (on_idx gctx sctx) is)) sctx ibinds

fun on_constr gctx (ctx as (sctx, kctx)) ((family, tnames, core) : E.constr) : constr =
    (on_long_id gctx #2 kctx family,
     tnames, 
     on_constr_core gctx ctx tnames core)

fun on_return gctx (ctx as (sctx, _)) return = mapPair (Option.map (on_mtype gctx ctx), Option.map (on_idx gctx sctx)) return

fun shift_return (sctxn, kctxn) (t, d) =
    let
      open Subst
    in
      (Option.map (fn t => shiftx_t_mt 0 kctxn $ shiftx_i_mt 0 sctxn t) t,
       Option.map (fn d => shiftx_i_i 0 sctxn d) d)
    end
      
fun copy_anno (anno as (t, d)) e =
    let
      fun copy a b = case a of
                         NONE => b
                       | SOME _ => a
    in
      case e of
          Case (e, (t', d'), es, r) =>
          let
            fun is_tuple_value e =
                case e of
                    Var _ => true
                  | Pair (e1, e2) => is_tuple_value e1 andalso is_tuple_value e2
                  | _ => false
            (* if e is tuple value, we are sure it doesn't cost time, so we can copy time annotation *)
            val d = if is_tuple_value e then d else NONE
            val (t, d) = (copy t' t, copy d' d)
            val es = map (copy_anno_rule (t, d)) es
          in
            Case (e, (t, d), es, r)
          end
        | Let ((t', d'), decls, e, r) =>
          let
            val (t, d) = (copy t' t, copy d' d)
            val (_, (sctx, kctx, _, _)) = str_decls [] ([], [], [], []) decls
            val (sctxn, kctxn) = (length sctx, length kctx)
            fun is_match_var decl =
                case decl of
                    Val (_, _, Var _, _) => true
                  | _ => false
            val d' = if List.all is_match_var decls then d else NONE
          in
            Let ((t, d), decls, copy_anno (shift_return (sctxn, kctxn) (t, d')) e, r)
          end
        | Ascription (e, t') =>
          let
            val t = SOME t'
            val e = copy_anno (t, d) e
          in
            Ascription (e, t')
          end
        | AscriptionTime (e, d') =>
          let
            val d = SOME d'
            val e = copy_anno (t, d) e
          in
            AscriptionTime (e, d')
          end
        | Never _ => e
        | _ =>
          case t of
              SOME t => Ascription (e, t)
            | NONE => e
    end
      
and copy_anno_rule return (pn, e) =
    let
      val (sctx, _) = ptrn_names pn
      val offset = (length sctx, 0)
    in
      (pn, copy_anno (shift_return offset return) e)
    end
      
fun get_constr_inames core = map fst $ fst $ unfold_ibinds core
                                 
val empty_ctx = ([], [], [], [])
fun add_sorting_skct name (sctx, kctx, cctx, tctx) = (name :: sctx, kctx, cctx, tctx)
fun add_kinding_skct name (sctx, kctx, cctx, tctx) = (sctx, name :: kctx, cctx, tctx)
fun add_typing_skct name (sctx, kctx, cctx, tctx) = (sctx, kctx, cctx, name :: tctx)
fun add_ctx (sctxd, kctxd, cctxd, tctxd) (sctx, kctx, cctx, tctx) =
    (sctxd @ sctx, kctxd @ kctx, cctxd @ cctx, tctxd @ tctx)
      
fun on_expr gctx (ctx as (sctx, kctx, cctx, tctx)) e =
    let
      val on_expr = on_expr gctx
      (* val () = println $ sprintf "on_expr $ in context $" [E.str_e ctx e, join " " tctx] *)
      val skctx = (sctx, kctx)
    in
      case e of
	  E.Var (x, b) => 
	  (case find_constr gctx cctx x of
	       SOME (x, _) => AppConstr ((x, b), [], TT $ get_region_long_id x)
	     | NONE => Var ((on_long_id gctx #4 tctx x), b)
          )
	| E.Abs (pn, e) => 
          let 
            val pn = on_ptrn gctx (sctx, kctx, cctx) pn
            val (inames, enames) = ptrn_names pn
            val ctx = (inames @ sctx, kctx, cctx, enames @ tctx)
            val e = on_expr ctx e
          in
            Abs (pn, e)
          end
	| E.App (e1, e2) => 
	  let
            val e2 = on_expr ctx e2
	    fun default () = 
                App (on_expr ctx e1, e2)
	    val (e1, is) = E.collect_AppI e1 
	  in
	    case e1 of
		E.Var (x, b) =>
		(case find_constr gctx cctx x of
		     SOME (x, _) => AppConstr ((x, b), map (on_idx gctx sctx) is, e2)
		   | NONE => default ())
	      | _ => default ()
	  end
	| E.TT r => TT r
	| E.Pair (e1, e2) => Pair (on_expr ctx e1, on_expr ctx e2)
	| E.Fst e => Fst (on_expr ctx e)
	| E.Snd e => Snd (on_expr ctx e)
	| E.AbsI (s, (name, r), e, r_all) => AbsI (on_sort gctx sctx s, (name, r), on_expr (add_sorting_skct name ctx) e, r_all)
	| E.AppI (e, i) => 
	  let
            fun default () = 
                AppI (on_expr ctx e, on_idx gctx sctx i)
	    val (e, is) = E.collect_AppI e
            val is = is @ [i]
	  in
	    case e of
		E.Var (x, b) =>
		(case find_constr gctx cctx x of
		     SOME (x, _) => AppConstr ((x, b), map (on_idx gctx sctx) is, TT (E.get_region_i i))
		   | NONE => default ())
	      | _ => default ()
	  end
	| E.Let (return, decls, e, r) =>
          let 
            val return = on_return gctx skctx return
            val (decls, ctx) = on_decls gctx ctx decls
          in
            Let (return, decls, on_expr ctx e, r)
          end
	| E.Ascription (e, t) =>
          let
            val t = on_mtype gctx skctx t
            val e = on_expr ctx e
            val e = copy_anno (SOME t, NONE) e
          in
            Ascription (e, t)
          end
	| E.AscriptionTime (e, d) =>
          let
            val d = on_idx gctx sctx d
            val e = on_expr ctx e
            val e = copy_anno (NONE, SOME d) e
          in
            AscriptionTime (e, d)
          end
	| E.ConstInt n => ConstInt n
	| E.BinOp (opr, e1, e2) => BinOp (opr, on_expr ctx e1, on_expr ctx e2)
	| E.AppConstr ((x, b), is, e) => AppConstr ((on_long_id gctx (map fst o #3) (map fst cctx) x, b), map (on_idx gctx sctx) is, on_expr ctx e)
	| E.Case (e, return, rules, r) =>
          let
            val return = on_return gctx skctx return
            val rules = map (on_rule gctx ctx) rules
            val rules = map (copy_anno_rule return) rules
          in
            Case (on_expr ctx e, return, rules, r)
          end
	| E.Never (t, r) => Never (on_mtype gctx skctx t, r)
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
          E.Val (tnames, pn, e, r) =>
          let 
            val ctx' as (sctx', kctx', cctx', _) = (sctx, (rev o map fst) tnames @ kctx, cctx, tctx)
            val pn = on_ptrn gctx (sctx', kctx', cctx') pn
            val e = on_expr gctx ctx' e
            val (inames, enames) = ptrn_names pn
            val ctx = (inames @ sctx, kctx, cctx, enames @ tctx)
          in
            (Val (tnames, pn, e, r), ctx)
          end
        | E.Rec (tnames, (name, r1), (binds, ((t, d), e)), r) =>
          let 
	    val ctx as (sctx, kctx, cctx, tctx) = (sctx, kctx, cctx, name :: tctx)
            val ctx_ret = ctx
            val ctx as (sctx, kctx, cctx, tctx) = (sctx, (rev o map fst) tnames @ kctx, cctx, tctx)
            fun f (bind, (binds, ctx as (sctx, kctx, cctx, tctx))) =
                case bind of
                    E.SortingST ((name, r), s) => 
                    (SortingST ((name, r), on_sort gctx sctx s) :: binds, add_sorting_skct name ctx)
                  | E.TypingST pn =>
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
            val e = copy_anno (SOME t, SOME d) e
          in
            (Rec (tnames, (name, r1), (binds, ((t, d), e)), r), ctx_ret)
          end
        | E.Datatype a =>
          mapFst Datatype $ on_datatype gctx ctx a
        | E.IdxDef ((name, r), s, i) =>
          (IdxDef ((name, r), on_sort gctx sctx s, on_idx gctx sctx i), add_sorting_skct name ctx)
        | E.AbsIdx (((name, r1), s, i), decls, r) =>
          let
            val s = on_sort gctx sctx s
            val i = on_idx gctx sctx i
            val ctx = add_sorting_skct name ctx
            val (decls, ctx) = on_decls gctx ctx decls
          in
            (AbsIdx (((name, r1), s, i), decls, r), ctx)
          end
        | E.TypeDef ((name, r), t) =>
          let
            val t = on_mtype gctx (sctx, kctx) t
          in
            (TypeDef ((name, r), t), add_kinding_skct name ctx)
          end
        | E.Open (m, r) =>
          let
            val (m, ctxd) =
                case lookup_module gctx m of
                    SOME a => a
                  | NONE => raise Error (r, "Unbound module " ^ m)
          in
            (Open (m, r), add_ctx ctxd ctx)
          end
    end

and on_datatype gctx (ctx as (sctx, kctx, cctx, tctx)) (name, tnames, sorts, constr_decls, r) =
    let
      fun on_constr_decl (cname, core, r) =
          (cname, on_constr_core gctx (sctx, name :: kctx) tnames core, r)
      val decl = (name, tnames, map (on_sort gctx sctx) sorts, map on_constr_decl constr_decls, r)
      val cnames = map (fn (name, core, _) => (name, get_constr_inames core)) constr_decls
      val ctx = (sctx, name :: kctx, rev cnames @ cctx, tctx)
    in
      (decl, ctx)
    end
      
and on_rule gctx (ctx as (sctx, kctx, cctx, tctx)) (pn, e) =
    let 
      (* val () = println $ sprintf "on_rule $ in context $" [E.str_rule ctx (pn, e), join " " tctx] *)
      val pn = on_ptrn gctx (sctx, kctx, cctx) pn
      val (inames, enames) = ptrn_names pn
      (* val () = println $ sprintf "enames of $: $" [E.str_pn (sctx, kctx, cctx) pn, join " " enames] *)
      val ctx' = (inames @ sctx, kctx, cctx, enames @ tctx)
    in
      (pn, on_expr gctx ctx' e)
    end

fun on_kind gctx ctx k =
    case k of
	E.ArrowK (is_datatype, n, sorts) => ArrowK (is_datatype, n, map (on_sort gctx ctx) sorts)

fun on_sig gctx sg =
    case sg of
        E.SigComponents (comps, r) =>
        let
          fun on_spec (ctx as (sctx, kctx, _, _)) spec =
              case spec of
                  E.SpecVal ((name, r), t) =>
                  let
                    val t = on_type gctx (sctx, kctx) t
                  in
                    (SpecVal ((name, r), t), add_typing_skct name ctx)
                  end
                | E.SpecIdx ((name, r), s) =>
                  let
                    val s = on_sort gctx sctx s
                  in
                    (SpecIdx ((name, r), s), add_sorting_skct name ctx)
                  end
                | E.SpecType ((name, r), k) =>
                  let
                    val k = on_kind gctx sctx k
                  in
                    (SpecType ((name, r), k), add_kinding_skct name ctx)
                  end
                | E.SpecTypeDef ((name, r), t) =>
                  let
                    val t = on_mtype gctx (sctx, kctx) t
                  in
                    (SpecTypeDef ((name, r), t), add_kinding_skct name ctx)
                  end
                | E.SpecDatatype a =>
                  mapFst SpecDatatype $ on_datatype gctx ctx a
          fun iter (spec, (specs, ctx)) =
              let
                val (spec, ctx) = on_spec ctx spec
              in
                (spec :: specs, ctx)
              end
          val (comps, ctx) = foldl iter ([], empty_ctx) comps
          val comps = rev comps
        in
          (SigComponents (comps, r), ctx)
        end
          
fun on_module gctx m =
    case m of
        E.ModComponents (comps, r) =>
        let
          val (comps, ctx) = on_decls gctx empty_ctx comps
        in
          (ModComponents (comps, r), ctx)
        end
      | E.ModSeal (m, sg) =>
        let
          val (sg, ctx) = on_sig gctx sg
          val (m, _) = on_module gctx m
        in
          (ModSeal (m, sg), ctx)
        end
      | E.ModTransparentAscription (m, sg) =>
        let
          val (sg, _) = on_sig gctx sg
          val (m, ctx) = on_module gctx m
        in
          (ModTransparentAscription (m, sg), ctx)
        end

fun on_top_bind gctx bind = 
    case bind of
        E.TopModBind ((name, r), m) =>
        let
          val (m, ctx) = on_module gctx m
        in
          (TopModBind ((name, r), m), [(name, Sig ctx)])
        end
      (* | E.TopModSpec ((name, r), sg) => *)
      (*   let *)
      (*     val (sg = on_sig gctx sg *)
      (*     val () = open_module (name, sg) *)
      (*   in *)
      (*     [(name, Sig sg)] *)
      (*   end *)
      | E.TopFunctorBind ((name, r1), ((arg_name, r2), arg), m) =>
        let
          val (arg, arg_ctx) = on_sig gctx arg
          val gctx = (arg_name, Sig arg_ctx) :: gctx
          val (m, body_ctx) = on_module gctx m
        in
          (TopFunctorBind ((name, r1), ((arg_name, r2), arg), m), [(name, FunctorBind ((arg_name, arg_ctx), body_ctx))])
        end
      | E.TopFunctorApp ((name, r), (f, f_r), m) =>
        let
          fun lookup_functor (gctx : sigcontext) name =
              let
                fun iter ((name', sg), (nsig, nfunc)) =
                    case sg of
                        Sig _ => Continue (nsig + 1, nfunc)
                      | FunctorBind a =>
                        if name' = name then
                          ShortCircuit (nsig, nfunc, a)
                        else
                          Continue (nsig, nfunc + 1)
              in
                case is_ShortCircuit $ foldlM_Error iter (0, 0) gctx of
                    SOME (nsig, nfunc, (arg, body : context)) => SOME (nfunc, (arg, body))
                  | NONE => NONE
              end
          fun fetch_functor gctx (m, r) =
              case lookup_functor gctx m of
                  SOME a => a
                | NONE => raise Error (r, "Unbound functor " ^ m)
          val (f, ((_, formal_arg), body)) = fetch_functor gctx (f, f_r)
          val m = on_id (map fst gctx) m
          val formal_arg_name = "__formal_mod_arg"
          val gctxd = [(formal_arg_name, Sig formal_arg)]
        in
          (TopFunctorApp ((name, r), (f, f_r), m), (name, Sig body) :: gctxd)
        end
          
and on_top_binds gctx binds =
    let
      fun iter (bind, (binds, acc, gctx)) =
          let
            val (bind, gctxd) = on_top_bind gctx bind
          in
            (bind :: binds, gctxd @ acc, gctxd @ gctx)
          end
      val (binds, gctxd, gctx) = foldl iter ([], [], gctx) binds
      val binds = rev binds
    in
      (binds, gctxd, gctx)
    end

val resolve_type = on_type
val resolve_expr = on_expr
fun resolve_decls gctx ctx decls = fst (on_decls gctx ctx decls)

val resolve_constr = on_constr
val resolve_kind = on_kind

fun resolve_type_opt ctx e = runError (fn () => on_type ctx e) ()
fun resolve_expr_opt ctx e = runError (fn () => on_expr ctx e) ()

fun resolve_constr_opt ctx e = runError (fn () => on_constr ctx e) ()
fun resolve_kind_opt ctx e = runError (fn () => on_kind ctx e) ()

val get_constr_inames = get_constr_inames

end
