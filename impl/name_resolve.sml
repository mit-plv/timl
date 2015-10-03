structure NameResolve = struct
structure T = NamefulType
structure E = NamefulExpr
open Type
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
	    T.VarI x => VarI (on_var ctx x)
	  | T.T0 r => T0 r
	  | T.T1 r => T1 r
	  | T.Tadd (i1, i2) => Tadd (on_idx ctx i1, on_idx ctx i2)
	  | T.Tmult (i1, i2) => Tmult (on_idx ctx i1, on_idx ctx i2)
	  | T.Tmax (i1, i2) => Tmax (on_idx ctx i1, on_idx ctx i2)
	  | T.Tmin (i1, i2) => Tmin (on_idx ctx i1, on_idx ctx i2)
	  | T.TrueI r => TrueI r
	  | T.FalseI r => FalseI r
	  | T.TTI r => TTI r
	  | T.Tconst n => Tconst n

    fun on_prop ctx p =
	case p of
	    T.True r => True r
	  | T.False r => False r
	  | T.And (p1, p2) => And (on_prop ctx p1, on_prop ctx p2)
	  | T.Or (p1, p2) => Or (on_prop ctx p1, on_prop ctx p2)
	  | T.Imply (p1, p2) => Imply (on_prop ctx p1, on_prop ctx p2)
	  | T.Iff (p1, p2) => Iff (on_prop ctx p1, on_prop ctx p2)
	  | T.TimeLe (i1, i2) => TimeLe (on_idx ctx i1, on_idx ctx i2)
	  | T.Eq (i1, i2) => Eq (on_idx ctx i1, on_idx ctx i2)

    fun on_sort ctx s =
	case s of
	    T.Basic s => Basic s
	  | T.Subset (s, (name, r), p) => Subset (s, (name, r), on_prop (name :: ctx) p)

    fun on_type (ctx as (sctx, kctx)) t =
	case t of
	    T.Arrow (t1, d, t2) => Arrow (on_type ctx t1, on_idx sctx d, on_type ctx t2)
	  | T.Prod (t1, t2) => Prod (on_type ctx t1, on_type ctx t2)
	  | T.Sum (t1, t2) => Sum (on_type ctx t1, on_type ctx t2)
	  | T.Unit r => Unit r
	  | T.Uni ((name, r), t) => Uni ((name, r), on_type (sctx, name :: kctx) t)
	  | T.UniI (s, (name, r), t) => UniI (on_sort sctx s, (name, r), on_type (name :: sctx, kctx) t)
	  | T.ExI (s, (name, r), t) => ExI (on_sort sctx s, (name, r), on_type (name :: sctx, kctx) t)
	  | T.AppRecur (name, name_sorts, t, is, r) => AppRecur (name, map (mapSnd (on_sort sctx)) name_sorts, on_type (rev (map #1 name_sorts) @ sctx, name :: kctx) t, map (on_idx sctx) is, r)
	  | T.AppV (x, ts, is, r) => AppV (on_var kctx x, map (on_type ctx) ts, map (on_idx sctx) is, r)
	  | T.Int r => Int r

    fun on_ptrn cctx pn =
	case pn of
	    E.Constr (x, inames, ename) => Constr (on_var cctx x, inames, ename)

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

    fun on_expr (ctx as (sctx, kctx, cctx, tctx)) e =
	let fun add_t name (sctx, kctx, cctx, tctx) = (sctx, kctx, cctx, name :: tctx)
	    val skctx = (sctx, kctx)
	in
	    case e of
		E.Var x => Var (on_var tctx x)
	      | E.Abs (t, (name, r), e) => Abs (on_type skctx t, (name, r), on_expr (add_t name ctx) e)
	      | E.App (e1, e2) => 
		let val e2 = on_expr ctx e2
		    fun default () = App (on_expr ctx e1, e2)
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
	      | E.AppT (e, t) => AppT (on_expr ctx e, on_type skctx t)
	      | E.AbsI (s, (name, r), e) => AbsI (on_sort sctx s, (name, r), on_expr (name :: sctx, kctx, cctx, tctx) e)
	      | E.AppI (e, i) => AppI (on_expr ctx e, on_idx sctx i)
	      | E.Pack (t, i, e) => Pack (on_type skctx t, on_idx sctx i, on_expr ctx e)
	      | E.Unpack (e1, t, d, iname, ename, e2) => Unpack (on_expr ctx e1, on_type skctx t, on_idx sctx d, iname, ename, on_expr (iname :: sctx, kctx, cctx, ename :: tctx) e2)
	      | E.Fix (t, (name, r), e) => Fix (on_type skctx t, (name, r), on_expr (add_t name ctx) e)
	      | E.Let (decls, e, r) =>
                let val (decls, ctx) = on_decls ctx decls
                in
                    Let (decls, on_expr ctx e, r)
                end
	      | E.Ascription (e, t) => Ascription (on_expr ctx e, on_type skctx t)
	      | E.AscriptionTime (e, d) => AscriptionTime (on_expr ctx e, on_idx sctx d)
	      | E.Const n => Const n
	      | E.Plus (e1, e2) => Plus (on_expr ctx e1, on_expr ctx e2)
	      | E.AppConstr (x, ts, is, e) => AppConstr (on_var cctx x, map (on_type skctx) ts, map (on_idx sctx) is, on_expr ctx e)
	      | E.Case (e, t, d, rules, r) => Case (on_expr ctx e, on_type skctx t, on_idx sctx d, map (fn (pn, e) => (on_ptrn cctx pn, let val (inames, enames) = E.ptrn_names pn in on_expr (inames @ sctx, kctx, cctx, enames @ tctx ) e end)) rules, r)
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
            E.Val ((name, r), e) =>
            (Val ((name, r), on_expr ctx e), (sctx, kctx, cctx, name :: tctx))


    fun on_constr (ctx as (sctx, kctx)) ((family, tnames, name_sorts, t, is) : T.constr) : constr =
	let val sctx' = rev (map #1 name_sorts) @ sctx
	in
	    (#1 (on_var kctx (family, dummy_region)), tnames, 
	     (rev o #1) (foldl (fn ((name, s), (acc, names)) => ((name, on_sort (names @ sctx) s) :: acc, name :: names)) ([], []) name_sorts),
	     on_type (sctx', rev tnames @ kctx) t,
	     map (on_idx sctx') is
	    )
	end

    fun on_kind ctx k =
	case k of
	    T.ArrowK (n, sorts) => ArrowK (n, map (on_sort ctx) sorts)

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
