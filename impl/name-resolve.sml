structure NameResolve = struct
structure E = NamefulExpr
open Expr

open Region
exception Error of region * string

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
	| NONE => raise Error (r, "Unbound variable " ^ x)

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

    fun on_prop ctx p =
      case p of
	  E.True r => True r
	| E.False r => False r
        | E.Not (p, r) => Not (on_prop ctx p, r)
	| E.BinConn (opr, p1, p2) => BinConn (opr, on_prop ctx p1, on_prop ctx p2)
	| E.BinPred (opr, i1, i2) => BinPred (opr, on_idx ctx i1, on_idx ctx i2)

    fun on_ibind f ctx (E.BindI ((name, r), inner)) = BindI ((name, r), f (name :: ctx) inner)

    fun on_sort ctx s =
      case s of
	  E.Basic s => Basic s
	| E.Subset (s, E.BindI ((name, r), p)) => Subset (s, BindI ((name, r), on_prop (name :: ctx) p))

    fun on_type (ctx as (sctx, kctx)) t =
      case t of
	  E.Arrow (t1, d, t2) => Arrow (on_type ctx t1, on_idx sctx d, on_type ctx t2)
	| E.Prod (t1, t2) => Prod (on_type ctx t1, on_type ctx t2)
	| E.Sum (t1, t2) => Sum (on_type ctx t1, on_type ctx t2)
	| E.Unit r => Unit r
	| E.Uni ((name, r), t) => Uni ((name, r), on_type (sctx, name :: kctx) t)
	| E.UniI (s, E.BindI ((name, r), t)) => UniI (on_sort sctx s, BindI ((name, r), on_type (name :: sctx, kctx) t))
	| E.ExI (s, E.BindI ((name, r), t)) => ExI (on_sort sctx s, BindI ((name, r), on_type (name :: sctx, kctx) t))
	| E.AppRecur (name, name_sorts, t, is, r) => AppRecur (name, map (mapSnd (on_sort sctx)) name_sorts, on_type (rev (map #1 name_sorts) @ sctx, name :: kctx) t, map (on_idx sctx) is, r)
	| E.AppV (x, ts, is, r) => AppV (on_var kctx x, map (on_type ctx) ts, map (on_idx sctx) is, r)
	| E.Int r => Int r

    fun on_ptrn cctx pn =
      case pn of
	  E.ConstrP ((x, xr), inames, pn, r) =>
          (case find_idx x cctx of
	       SOME i => 
               ConstrP ((i, xr), inames, Option.map (on_ptrn cctx) pn, r)
	     | NONE =>
               (case (inames, pn) of
                    ([], NONE) => VarP (x, r)
                  | _ =>
                    raise Error (r, "Unknown constructor " ^ x)))
        | E.VarP name =>
          VarP name
        | E.PairP (pn1, pn2) =>
          PairP (on_ptrn cctx pn1, on_ptrn cctx pn2)
        | E.TTP r =>
          TTP r
        | E.AliasP (name, pn, r) =>
          AliasP (name, on_ptrn cctx pn, r)

    fun get_is e =
      case e of 
	  E.AppI (e, i) =>
	  let val (e, is) = get_is e in
	      (e, is @ [i])
	  end
	| _ => (e, [])

    fun get_ts e =
      case e of 
	  E.AppT (e, t) =>
	  let val (e, ts) = get_ts e in
	      (e, ts @ [t])
	  end
	| _ => (e, [])

    fun on_ibinds on_anno on_inner ctx ibinds =
        case ibinds of
            E.NilIB inner => NilIB (on_inner ctx inner)
          | E.ConsIB (anno, E.BindI (name, ibinds)) =>
            ConsIB (on_anno ctx anno, BindI (name, on_ibinds on_anno on_inner (name :: ctx) ibinds))

    fun on_constr_core (ctx as (sctx, kctx)) tnames (ibinds : E.constr_core) : constr_core =
        on_ibinds on_sort (fn sctx => fn (t, is) => (on_type (sctx, rev tnames @ kctx) t, map (on_idx sctx) is)) sctx ibinds

    fun on_constr (ctx as (sctx, kctx)) ((family, tnames, core) : E.constr) : constr =
      (#1 (on_var kctx (family, dummy_region)),
       tnames, 
       on_constr_core ctx tnames core)

    fun on_return (ctx as (sctx, _)) return = mapPair (Option.map (on_type ctx), Option.map (on_idx sctx)) return

    fun on_expr (ctx as (sctx, kctx, cctx, tctx)) e =
      let fun add_t name (sctx, kctx, cctx, tctx) = (sctx, kctx, cctx, name :: tctx)
	  val skctx = (sctx, kctx)
      in
	  case e of
	      E.Var x => Var (on_var tctx x)
	    | E.Abs (t, pn, e) => 
              let val t = on_type skctx t
                  val pn = on_ptrn cctx pn
                  val (inames, enames) = ptrn_names pn
                  val ctx = (inames @ sctx, kctx, cctx, enames @ tctx)
                  val e = on_expr ctx e
              in
                  Abs (t, pn, e)
              end
	    | E.App (e1, e2) => 
	      let val e2 = on_expr ctx e2
		  fun default () = 
                      App (on_expr ctx e1, e2)
		  val (e1, is) = get_is e1 
		  val (e1, ts) = get_ts e1
	      in
		  case e1 of
		      E.Var (x, r) =>
		      (case find_idx x cctx of
			   SOME i => AppConstr ((i, r), map (on_type skctx) ts, map (on_idx sctx) is, e2)
			 | NONE => default ())
		    | _ => default ()
	      end
	    | E.TT r => TT r
	    | E.Pair (e1, e2) => Pair (on_expr ctx e1, on_expr ctx e2)
	    | E.Fst e => Fst (on_expr ctx e)
	    | E.Snd e => Snd (on_expr ctx e)
	    | E.Inr (t, e) => Inr (on_type skctx t, on_expr ctx e)
	    | E.Inl (t, e) => Inl (on_type skctx t, on_expr ctx e)
	    | E.SumCase (e, name1, e1, name2, e2) => SumCase (on_expr ctx e, name1, on_expr (add_t name1 ctx) e1, name2, on_expr (add_t name2 ctx) e2)
	    | E.Fold (t, e) => Fold (on_type skctx t, on_expr ctx e)
	    | E.Unfold e => Unfold (on_expr ctx e)
	    | E.AbsT ((name, r), e) => AbsT ((name, r), on_expr (sctx, name :: kctx, cctx, tctx) e)
	    | E.AppT (e, t) => 
	      let fun default () = 
                      AppT (on_expr ctx e, on_type skctx t)
		  val (e, ts) = get_ts e
                  val ts = ts @ [t]
	      in
		  case e of
		      E.Var (x, r) =>
		      (case find_idx x cctx of
			   SOME n => AppConstr ((n, r), map (on_type skctx) ts, [], TT (ExprRegion.get_region_t (on_type skctx t)))
			 | NONE => default ())
		    | _ => default ()
	      end
	    | E.AbsI (s, (name, r), e) => AbsI (on_sort sctx s, (name, r), on_expr (name :: sctx, kctx, cctx, tctx) e)
	    | E.AppI (e, i) => 
	      let fun default () = 
                      AppI (on_expr ctx e, on_idx sctx i)
		  val (e, is) = get_is e
                  val is = is @ [i]
		  val (e, ts) = get_ts e
	      in
		  case e of
		      E.Var (x, r) =>
		      (case find_idx x cctx of
			   SOME n => AppConstr ((n, r), map (on_type skctx) ts, map (on_idx sctx) is, TT (ExprRegion.get_region_i (on_idx sctx i)))
			 | NONE => default ())
		    | _ => default ()
	      end
	    | E.Pack (t, i, e) => Pack (on_type skctx t, on_idx sctx i, on_expr ctx e)
	    | E.Unpack (e1, return, iname, ename, e2) => Unpack (on_expr ctx e1, on_return skctx return, iname, ename, on_expr (iname :: sctx, kctx, cctx, ename :: tctx) e2)
	    | E.Fix (t, (name, r), e) => Fix (on_type skctx t, (name, r), on_expr (add_t name ctx) e)
	    | E.Let (decls, e, r) =>
              let val (decls, ctx) = on_decls ctx decls
              in
                  Let (decls, on_expr ctx e, r)
              end
	    | E.Ascription (e, t) => Ascription (on_expr ctx e, on_type skctx t)
	    | E.AscriptionTime (e, d) => AscriptionTime (on_expr ctx e, on_idx sctx d)
	    | E.Const n => Const n
	    | E.BinOp (opr, e1, e2) => BinOp (opr, on_expr ctx e1, on_expr ctx e2)
	    | E.AppConstr (x, ts, is, e) => AppConstr (on_var cctx x, map (on_type skctx) ts, map (on_idx sctx) is, on_expr ctx e)
	    | E.Case (e, return, rules, r) =>
              Case (on_expr ctx e, on_return skctx return, map (on_rule ctx) rules, r)
	    | E.Never t => Never (on_type skctx t)
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
            E.Val (pn, e) =>
            let val e = on_expr ctx e
                val pn = on_ptrn cctx pn
                val (inames, enames) = ptrn_names pn
                val ctx = (inames @ sctx, kctx, cctx, enames @ tctx)
            in
                (Val (pn, e), ctx)
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

    and on_rule (ctx as (sctx, kctx, cctx, tctx)) (pn, e) =
        let val pn = on_ptrn cctx pn
            val (inames, enames) = ptrn_names pn
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
