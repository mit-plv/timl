structure NameResolve = struct
structure E = NamefulExpr
open UnderscoredExpr

open Region
exception Error of region * string

infixr 0 $

local

  fun runError m _ =
      OK (m ())
      handle
      Error e => Failed e

  (* fun find_idx (x : string) ctx = find_by_snd_eq op= x (add_idx ctx) *)
  fun find_idx (x : string) ctx = Option.map fst $ findWithIdx (fn (_, y) => y = x) ctx
  fun find_idx_value (x : string) ctx = Option.map (fn (i, (_, v)) => (i, v)) $ findWithIdx (fn (_, (y, _)) => y = x) ctx

  fun on_var ctx (x, r) =
      case find_idx x ctx of
	  SOME i => (i, r)
	| NONE => raise Error (r, "Unbound variable " ^ x ^ sprintf " in context: $" [join " " $ rev ctx])

  fun on_idx ctx i =
      case i of
	  E.VarI x => VarI (on_var ctx x)
	| E.ConstIN n => ConstIN n
	| E.ConstIT x => ConstIT x
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

  fun on_bsort bs =
      case bs of
          E.Base b => Base b
        | E.UVarBS u => UVarBS u

  fun on_quan q =
      case q of
          Forall => Forall
        | Exists _ => Exists NONE
                             
  fun on_prop ctx p =
      case p of
	  E.True r => True r
	| E.False r => False r
        | E.Not (p, r) => Not (on_prop ctx p, r)
	| E.BinConn (opr, p1, p2) => BinConn (opr, on_prop ctx p1, on_prop ctx p2)
	| E.BinPred (opr, i1, i2) => BinPred (opr, on_idx ctx i1, on_idx ctx i2)
        | E.Quan (q, bs, (name, r), p, r_all) => Quan (on_quan q, on_bsort bs, (name, r), on_prop (name :: ctx) p, r_all)

  fun on_ibind f ctx (E.BindI ((name, r), inner)) = BindI ((name, r), f (name :: ctx) inner)

  fun on_sort ctx s =
      case s of
	  E.Basic (s, r) => Basic (on_bsort s, r)
	| E.Subset ((s, r1), E.BindI ((name, r), p), r_all) => Subset ((on_bsort s, r1), BindI ((name, r), on_prop (name :: ctx) p), r_all)
        | E.UVarS u => UVarS u

  fun on_mtype (ctx as (sctx, kctx)) t =
      case t of
	  E.Arrow (t1, d, t2) => Arrow (on_mtype ctx t1, on_idx sctx d, on_mtype ctx t2)
        | E.Unit r => Unit r
	| E.Prod (t1, t2) => Prod (on_mtype ctx t1, on_mtype ctx t2)
	| E.UniI (s, E.BindI ((name, r), t), r_all) => UniI (on_sort sctx s, BindI ((name, r), on_mtype (name :: sctx, kctx) t), r_all)
	| E.AppV (x, ts, is, r) => AppV (on_var kctx x, map (on_mtype ctx) ts, map (on_idx sctx) is, r)
	| E.BaseType (bt, r) => BaseType (bt, r)
        | E.UVar u => UVar u

  fun on_type (ctx as (sctx, kctx)) t =
      case t of
	  E.Mono t => Mono (on_mtype ctx t)
	| E.Uni ((name, r), t, r_all) => Uni ((name, r), on_type (sctx, name :: kctx) t, r_all)

  fun on_ptrn (ctx as (sctx, kctx, cctx)) pn =
      case pn of
	  E.ConstrP (((x, xr), eia), inames, pn, r) =>
          (case find_idx_value x cctx of
	       SOME (i, c_inames) =>
               let
                 val inames =
                     if eia then
                       inames
                     else
                       if length inames = 0 then map (prefix "__") c_inames
                       else raise Error (r, "Constructor pattern can't have explicit index pattern arguments. Use [@constructor_name] if you want to write explict index pattern arguments.")
               in
                 ConstrP (((i, xr), true), inames, Option.map (on_ptrn ctx) pn, r)
               end
	     | NONE =>
               (case (eia, inames, pn) of
                    (false, [], NONE) => VarP (x, r)
                  | _ =>
                    raise Error (r, "Unknown constructor " ^ x)))
        | E.VarP name =>
          VarP name
        | E.PairP (pn1, pn2) =>
          PairP (on_ptrn ctx pn1, on_ptrn ctx pn2)
        | E.TTP r =>
          TTP r
        | E.AliasP (name, pn, r) =>
          AliasP (name, on_ptrn ctx pn, r)
        | E.AnnoP (pn, t) =>
          AnnoP (on_ptrn ctx pn, on_mtype (sctx, kctx) t)

  fun on_ibinds on_anno on_inner ctx ibinds =
      case ibinds of
          E.NilIB inner => NilIB (on_inner ctx inner)
        | E.ConsIB (anno, E.BindI (name, ibinds)) =>
          ConsIB (on_anno ctx anno, BindI (name, on_ibinds on_anno on_inner (name :: ctx) ibinds))

  fun on_constr_core (ctx as (sctx, kctx)) tnames (ibinds : E.constr_core) : constr_core =
      on_ibinds on_sort (fn sctx => fn (t, is) => (on_mtype (sctx, rev tnames @ kctx) t, map (on_idx sctx) is)) sctx ibinds

  fun on_constr (ctx as (sctx, kctx)) ((family, tnames, core) : E.constr) : constr =
      (#1 (on_var kctx (family, dummy_region)),
       tnames, 
       on_constr_core ctx tnames core)

  fun on_return (ctx as (sctx, _)) return = mapPair (Option.map (on_mtype ctx), Option.map (on_idx sctx)) return

  fun shift_return (sctxn, kctxn) (t, d) =
      let
        open UnderscoredSubst
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
              val (_, (sctx, kctx, _, _)) = str_decls ([], [], [], []) decls
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
                                   
  fun add_sorting name (sctx, kctx, cctx, tctx) = (name :: sctx, kctx, cctx, tctx)
                                                    
  fun on_expr (ctx as (sctx, kctx, cctx, tctx)) e =
      let 
        (* val () = println $ sprintf "on_expr $ in context $" [E.str_e ctx e, join " " tctx] *)
        fun add_t name (sctx, kctx, cctx, tctx) = (sctx, kctx, cctx, name :: tctx)
	val skctx = (sctx, kctx)
      in
	case e of
	    E.Var ((x, r), b) => 
	    (case find_idx_value x cctx of
		 SOME (i, _) => AppConstr (((i, r), b), [], TT r)
	       | NONE => Var ((on_var tctx (x, r)), b)
            )
	  | E.Abs (pn, e) => 
            let 
              val pn = on_ptrn (sctx, kctx, cctx) pn
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
		  E.Var ((x, r), b) =>
		  (case find_idx_value x cctx of
		       SOME (i, _) => AppConstr (((i, r), b), map (on_idx sctx) is, e2)
		     | NONE => default ())
		| _ => default ()
	    end
	  | E.TT r => TT r
	  | E.Pair (e1, e2) => Pair (on_expr ctx e1, on_expr ctx e2)
	  | E.Fst e => Fst (on_expr ctx e)
	  | E.Snd e => Snd (on_expr ctx e)
	  | E.AbsI (s, (name, r), e, r_all) => AbsI (on_sort sctx s, (name, r), on_expr (add_sorting name ctx) e, r_all)
	  | E.AppI (e, i) => 
	    let
              fun default () = 
                  AppI (on_expr ctx e, on_idx sctx i)
	      val (e, is) = E.collect_AppI e
              val is = is @ [i]
	    in
	      case e of
		  E.Var ((x, r), b) =>
		  (case find_idx_value x cctx of
		       SOME (n, _) => AppConstr (((n, r), b), map (on_idx sctx) is, TT (E.get_region_i i))
		     | NONE => default ())
		| _ => default ()
	    end
	  | E.Let (return, decls, e, r) =>
            let 
              val return = on_return skctx return
              val (decls, ctx) = on_decls ctx decls
            in
              Let (return, decls, on_expr ctx e, r)
            end
	  | E.Ascription (e, t) =>
            let
              val t = on_mtype skctx t
              val e = on_expr ctx e
              val e = copy_anno (SOME t, NONE) e
            in
              Ascription (e, t)
            end
	  | E.AscriptionTime (e, d) =>
            let
              val d = on_idx sctx d
              val e = on_expr ctx e
              val e = copy_anno (NONE, SOME d) e
            in
              AscriptionTime (e, d)
            end
	  | E.ConstInt n => ConstInt n
	  | E.BinOp (opr, e1, e2) => BinOp (opr, on_expr ctx e1, on_expr ctx e2)
	  | E.AppConstr ((x, b), is, e) => AppConstr ((on_var (map fst cctx) x, b), map (on_idx sctx) is, on_expr ctx e)
	  | E.Case (e, return, rules, r) =>
            let
              val return = on_return skctx return
              val rules = map (on_rule ctx) rules
              val rules = map (copy_anno_rule return) rules
            in
              Case (on_expr ctx e, return, rules, r)
            end
	  | E.Never (t, r) => Never (on_mtype skctx t, r)
      end

  and on_decls (ctx as (sctx, kctx, cctx, tctx)) decls =
      let fun f (decl, (acc, ctx)) =
              let val (decl, ctx) = on_decl ctx decl
              in
                (decl :: acc, ctx)
              end
          val (decls, ctx) = foldl f ([], ctx) decls
          val decls = rev decls
      in
        (decls, ctx)
      end

  and on_decl (ctx as (sctx, kctx, cctx, tctx)) decl =
      case decl of
          E.Val (tnames, pn, e, r) =>
          let 
            val ctx' as (sctx', kctx', cctx', _) = (sctx, (rev o map fst) tnames @ kctx, cctx, tctx)
            val pn = on_ptrn (sctx', kctx', cctx') pn
            val e = on_expr ctx' e
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
                    (SortingST ((name, r), on_sort sctx s) :: binds, add_sorting name ctx)
                  | E.TypingST pn =>
                    let
                      val pn = on_ptrn (sctx, kctx, cctx) pn
                      val (inames, enames) = ptrn_names pn
                    in
                      (TypingST pn :: binds, (inames @ sctx, kctx, cctx, enames @ tctx))
                    end
            val (binds, ctx as (sctx, kctx, cctx, tctx)) = foldl f ([], ctx) binds
            val binds = rev binds
            val t = on_mtype (sctx, kctx) t
            val d = on_idx sctx d
            val e = on_expr ctx e
            val e = copy_anno (SOME t, SOME d) e
          in
            (Rec (tnames, (name, r1), (binds, ((t, d), e)), r), ctx_ret)
          end
        | E.Datatype (name, tnames, sorts, constr_decls, r) =>
          let
            fun on_constr_decl (cname, core, r) =
                (cname, on_constr_core (sctx, name :: kctx) tnames core, r)
            val decl = Datatype (name, tnames, map (on_sort sctx) sorts, map on_constr_decl constr_decls, r)
            val cnames = map (fn (name, core, _) => (name, get_constr_inames core)) constr_decls
            val ctx = (sctx, name :: kctx, rev cnames @ cctx, tctx)
          in
            (decl, ctx)
          end
        | E.IdxDef ((name, r), s, i) =>
          (IdxDef ((name, r), on_sort sctx s, on_idx sctx i), add_sorting name ctx)
        | E.AbsIdx (((name, r1), s, i), decls, r) =>
          let
            val s = on_sort sctx s
            val i = on_idx sctx i
            val ctx = add_sorting name ctx
            val (decls, ctx) = on_decls ctx decls
          in
            (AbsIdx (((name, r1), s, i), decls, r), ctx)
          end

  and on_rule (ctx as (sctx, kctx, cctx, tctx)) (pn, e) =
      let 
        (* val () = println $ sprintf "on_rule $ in context $" [E.str_rule ctx (pn, e), join " " tctx] *)
        val pn = on_ptrn (sctx, kctx, cctx) pn
        val (inames, enames) = ptrn_names pn
        (* val () = println $ sprintf "enames of $: $" [E.str_pn (sctx, kctx, cctx) pn, join " " enames] *)
        val ctx' = (inames @ sctx, kctx, cctx, enames @ tctx)
      in
        (pn, on_expr ctx' e)
      end

  fun on_kind ctx k =
      case k of
	  E.ArrowK (is_datatype, n, sorts) => ArrowK (is_datatype, n, map (on_sort ctx) sorts)

in
val resolve_type = on_type
val resolve_expr = on_expr
fun resolve_decls ctx decls = fst (on_decls ctx decls)

val resolve_constr = on_constr
val resolve_kind = on_kind

fun resolve_type_opt ctx e = runError (fn () => on_type ctx e) ()
fun resolve_expr_opt ctx e = runError (fn () => on_expr ctx e) ()

fun resolve_constr_opt ctx e = runError (fn () => on_constr ctx e) ()
fun resolve_kind_opt ctx e = runError (fn () => on_kind ctx e) ()

val get_constr_inames = get_constr_inames
end

end
