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

    fun find_idx (x : string) ctx =
      Option.map #1 (List.find (fn (_, y) => y = x) (add_idx ctx))

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
	| E.BinOpI (opr, i1, i2) => BinOpI (opr, on_idx ctx i1, on_idx ctx i2)
	| E.TrueI r => TrueI r
	| E.FalseI r => FalseI r
	| E.TTI r => TTI r
        | E.UVarI u => UVarI u

    fun on_bsort bs =
      case bs of
          E.Base b => Base b
        | E.UVarBS u => UVarBS u
                                                            
    fun on_prop ctx p =
      case p of
	  E.True r => True r
	| E.False r => False r
        | E.Not (p, r) => Not (on_prop ctx p, r)
	| E.BinConn (opr, p1, p2) => BinConn (opr, on_prop ctx p1, on_prop ctx p2)
	| E.BinPred (opr, i1, i2) => BinPred (opr, on_idx ctx i1, on_idx ctx i2)
        | E.Quan (q, bs, (name, r), p) => Quan (q, on_bsort bs, (name, r), on_prop (name :: ctx) p)

    fun on_ibind f ctx (E.BindI ((name, r), inner)) = BindI ((name, r), f (name :: ctx) inner)

    fun on_sort ctx s =
      case s of
	  E.Basic (s, r) => Basic (on_bsort s, r)
	| E.Subset ((s, r1), E.BindI ((name, r), p)) => Subset ((on_bsort s, r1), BindI ((name, r), on_prop (name :: ctx) p))
        | E.UVarS u => UVarS u

    fun on_mtype (ctx as (sctx, kctx)) t =
      case t of
	  E.Arrow (t1, d, t2) => Arrow (on_mtype ctx t1, on_idx sctx d, on_mtype ctx t2)
	| E.Prod (t1, t2) => Prod (on_mtype ctx t1, on_mtype ctx t2)
	| E.Unit r => Unit r
	| E.UniI (s, E.BindI ((name, r), t)) => UniI (on_sort sctx s, BindI ((name, r), on_mtype (name :: sctx, kctx) t))
	| E.AppV (x, ts, is, r) => AppV (on_var kctx x, map (on_mtype ctx) ts, map (on_idx sctx) is, r)
	| E.Int r => Int r
        | E.UVar u => UVar u

    fun on_type (ctx as (sctx, kctx)) t =
      case t of
	  E.Mono t => Mono (on_mtype ctx t)
	| E.Uni ((name, r), t) => Uni ((name, r), on_type (sctx, name :: kctx) t)

    fun on_ptrn (ctx as (sctx, kctx, cctx)) pn =
      case pn of
	  E.ConstrP ((x, xr), inames, pn, r) =>
          (case find_idx x cctx of
	       SOME i => 
               ConstrP ((i, xr), inames, Option.map (on_ptrn ctx) pn, r)
	     | NONE =>
               (case (inames, pn) of
                    ([], NONE) => VarP (x, r)
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

    fun on_expr (ctx as (sctx, kctx, cctx, tctx)) e =
      let 
          (* val () = println $ sprintf "on_expr $ in context $" [E.str_e ctx e, join " " tctx] *)
          fun add_t name (sctx, kctx, cctx, tctx) = (sctx, kctx, cctx, name :: tctx)
	  val skctx = (sctx, kctx)
      in
	  case e of
	      E.Var (x, r) => 
	      (case find_idx x cctx of
		   SOME i => AppConstr ((i, r), [], TT r)
		 | NONE => Var (on_var tctx (x, r))
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
		  val (e1, is) = E.peel_AppI e1 
	      in
		  case e1 of
		      E.Var (x, r) =>
		      (case find_idx x cctx of
			   SOME i => AppConstr ((i, r), map (on_idx sctx) is, e2)
			 | NONE => default ())
		    | _ => default ()
	      end
	    | E.TT r => TT r
	    | E.Pair (e1, e2) => Pair (on_expr ctx e1, on_expr ctx e2)
	    | E.Fst e => Fst (on_expr ctx e)
	    | E.Snd e => Snd (on_expr ctx e)
	    | E.AbsI (s, (name, r), e) => AbsI (on_sort sctx s, (name, r), on_expr (name :: sctx, kctx, cctx, tctx) e)
	    | E.AppI (e, i) => 
	      let
                  fun default () = 
                      AppI (on_expr ctx e, on_idx sctx i)
		  val (e, is) = E.peel_AppI e
                  val is = is @ [i]
	      in
		  case e of
		      E.Var (x, r) =>
		      (case find_idx x cctx of
			   SOME n => AppConstr ((n, r), map (on_idx sctx) is, TT (E.get_region_i i))
			 | NONE => default ())
		    | _ => default ()
	      end
	    | E.Let (decls, e, r) =>
              let 
                  val (decls, ctx) = on_decls ctx decls
              in
                  Let (decls, on_expr ctx e, r)
              end
	    | E.Ascription (e, t) => Ascription (on_expr ctx e, on_mtype skctx t)
	    | E.AscriptionTime (e, d) => AscriptionTime (on_expr ctx e, on_idx sctx d)
	    | E.Const n => Const n
	    | E.BinOp (opr, e1, e2) => BinOp (opr, on_expr ctx e1, on_expr ctx e2)
	    | E.AppConstr (x, is, e) => AppConstr (on_var cctx x, map (on_idx sctx) is, on_expr ctx e)
	    | E.Case (e, return, rules, r) =>
              Case (on_expr ctx e, on_return skctx return, map (on_rule ctx) rules, r)
	    | E.Never t => Never (on_mtype skctx t)
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
                        (SortingST ((name, r), on_sort sctx s) :: binds, (name :: sctx, kctx, cctx, tctx))
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
            in
                (Rec (tnames, (name, r1), (binds, ((t, d), e)), r), ctx_ret)
            end
          | E.Datatype (name, tnames, sorts, constr_decls, r) =>
            let fun on_constr_decl (cname, core, r) =
                  (cname, on_constr_core (sctx, name :: kctx) tnames core, r)
                val decl = Datatype (name, tnames, map (on_sort sctx) sorts, map on_constr_decl constr_decls, r)
                val cnames = map #1 constr_decls
                val ctx = (sctx, name :: kctx, rev cnames @ cctx, tctx)
            in
                (decl, ctx)
            end
          | E.IdxDef ((name, r), s, i) =>
            (IdxDef ((name, r), on_sort sctx s, on_idx sctx i), (name :: sctx, kctx, cctx, tctx))
          | E.AbsIdx (((name, r1), s, i), decls, r) =>
            let
                val ctx' = (name :: sctx, kctx, cctx, tctx)
                val (decls, ctx') = on_decls ctx' decls
            in
                (AbsIdx (((name, r1), on_sort sctx s, on_idx sctx i), decls, r), ctx')
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
end

end
