(* collect module references *)

structure CollectMod = struct
open Util
open Expr

infixr 0 $

fun on_ibind f acc (Bind (_, b) : ('a * 'b) ibind) = f acc b

fun on_long_id acc (m, _) = (option2list $ Option.map fst m) @ acc
fun collect_mod_long_id b = on_long_id [] b
  
local
  fun f acc b =
    case b of
	VarI x => on_long_id acc x
      | IConst _ => acc
      | UnOpI (opr, i, r) => f acc i
      | BinOpI (opr, i1, i2) => 
        let
          val acc = f acc i1
          val acc = f acc i2
        in
          acc
        end
      | Ite (i1, i2, i3, r) =>
        let
          val acc = f acc i1
          val acc = f acc i2
          val acc = f acc i3
        in
          acc
        end
      | IAbs (b, bind, r) =>
        on_ibind f acc bind
      | UVarI a => acc
in
val on_i = f
fun collect_mod_i b = f [] b
end

local
  fun f acc b =
    case b of
	PTrueFalse _ => acc
      | Not (p, r) => f acc p
      | BinConn (opr,p1, p2) =>
        let
          val acc = f acc p1
          val acc = f acc p2
        in
          acc
        end
      | BinPred (opr, i1, i2) => 
        let
          val acc = on_i acc i1
          val acc = on_i acc i2
        in
          acc
        end
      | Quan (q, bs, bind, r) => on_ibind f acc bind
in
val on_p = f
fun collect_mod_p b = f [] b
end

local
  fun f acc b =
    case b of
	Basic s => acc
      | Subset (b, bind, r) => on_ibind on_p acc bind
      | UVarS a => acc
      | SortBigO (b, i, r) => on_i acc i
      | SAbs (s, bind, r) => on_ibind f acc bind
      | SApp (s, i) =>
        let
          val acc = f acc s
          val acc = on_i acc i
        in
          acc
        end
in
val on_s = f
fun collect_mod_s b = f [] b
end

fun on_tbind f acc (Bind (_, b) : ('a * 'b) tbind) = f acc b

fun on_k acc (_, sorts) =
  foldl (fn (s, acc) => on_s acc s) acc sorts
                                                                        
local
  fun f acc b =
    case b of
	Arrow (t1, i, t2) =>
        let
          val acc = f acc t1
          val acc = on_i acc i
          val acc = f acc t2
        in
          acc
        end
      | TyNat (i, _) => on_i acc i
      | TyArray (t, i) =>
        let
          val acc = f acc t
          val acc = on_i acc i
        in
          acc
        end
      | Unit _ => acc
      | Prod (t1, t2) =>
        let
          val acc = f acc t1
          val acc = f acc t2
        in
          acc
        end
      | UniI (s, bind, _) =>
        let
          val acc = on_s acc s
          val acc = on_ibind f acc bind
        in
          acc
        end
      | MtVar x => on_long_id acc x
      | MtApp (t1, t2) =>
        let
          val acc = f acc t1
          val acc = f acc t2
        in
          acc
        end
      | MtAbs (k, bind, _) =>
        let
          val acc = on_k acc k
          val acc = on_tbind f acc bind
        in
          acc
        end
      | MtAppI (t, i) =>
        let
          val acc = f acc t
          val acc = on_i acc i
        in
          acc
        end
      | MtAbsI (s, bind, r) =>
        let
          val acc = on_s acc s
          val acc = on_ibind f acc bind
        in
          acc
        end
      | BaseType _ => acc
      | UVar _ => acc
in
val on_mt = f
fun collect_mod_mt b = f [] b
end

local
  fun f acc b =
    case b of
	Mono t => on_mt acc t
      | Uni (bind, r) => on_tbind f acc bind
in
val on_t = f
fun collect_mod_t b = f [] b
end

fun on_option f acc a =
  case a of
      SOME a => f acc a
    | NONE => acc
                
local
  fun f acc b =
    case b of
	ConstrP ((x, eia), inames, pn, r) =>
        let
          val acc = on_long_id acc x
          val acc = on_option f acc pn
        in
          acc
        end
      | VarP name => acc
      | PairP (pn1, pn2) =>
        let
          val acc = f acc pn1
          val acc = f acc pn2
        in
          acc
        end
      | TTP r => acc
      | AliasP (name, pn, r) => f acc pn
      | AnnoP (pn, t) =>
        let
          val acc = f acc pn
          val acc = on_mt acc t
        in
          acc
        end
in
val on_ptrn = f
fun collect_mod_ptrn b = f [] b
end

fun on_list f acc b = foldl (fn (b, acc) => f acc b) acc b
fun on_pair (f, g) acc (a, b) =
  let
    val acc = f acc a
    val acc = g acc b
  in
    acc
  end
  
val on_return = on_pair (on_option on_mt, on_option on_i)
                      
local
  fun f acc b =
      case b of
	  Var (x, _) => collect_mod_long_id x @ acc
	| EConst c => acc
	| EUnOp (opr, e, r) => Fst (f x n e)
	| BinOp (opr, e1, e2) =>
          let
            val acc = f acc e1
            val acc = f acc e2
          in
            acc
          end
	| TriOp (opr, e1, e2, e3) => TriOp (opr, f x n e1, f x n e2, f x n e3)
	| EEI (opr, e, i) =>
          let
            val acc = f acc e
            val acc = on_i acc i
          in
            acc
          end
	| ET (opr, t, r) => on_mt acc t
	| Abs (pn, e) =>
          let
            val acc = on_ptrn acc pn
            val acc = f acc e
          in
            acc
          end
	| AbsI (s, Bind (name, e), r) =>
          let
            val acc = on_s acc s
            val acc = f acc e
          in
            acc
          end
	| Ascription (e, t) =>
          let
            val acc = f acc e
            val acc = on_mt acc t
          in
            acc
          end
	| AppConstr ((x, ie), is, e) =>
          let
            val acc = on_long_id acc x
            val acc = on_list on_i acc x
            val acc = f acc e
          in
            acc
          end
	| Case (e, return, rules, r) =>
          let
            val acc = f acc e
            val acc = on_return acc return
            val on_rule = on_pair (on_ptrn, f)
            val acc = on_list on_rule acc rules
          in
            acc
          end
	| Let (return, decls, e, r) =>
          let
            val acc = on_return acc return
            val acc = on_list on_decl acc decls
            val acc = f acc e
          in
            acc
          end

  and on_decl acc b =
      case b of
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
            val e = copy_anno (gctx_names gctx) (SOME t, SOME d) e
          in
            (Rec (tnames, (name, r1), (binds, ((t, d), e)), r), ctx_ret)
          end
        | E.Datatype a =>
          mapFst Datatype $ on_datatype gctx ctx a
        | E.IdxDef ((name, r), s, i) =>
          (IdxDef ((name, r), on_sort gctx sctx s, on_idx gctx sctx i), add_sorting_skct name ctx)
        | E.AbsIdx2 ((name, r), s, i) =>
          (AbsIdx2 ((name, r), on_sort gctx sctx s, on_idx gctx sctx i), add_sorting_skct name ctx)
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
            val ctx = add_ctx ctxd ctx
          in
            (Open (m, r), ctx)
          end

in
val on_e = f
fun collect_mod_e b = f [] b
end

end
