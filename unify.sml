(* unification *)

structure Unify = struct
open ParaSubst
open Expr
open Util
open UVar
open Subst
open Normalize
open TypecheckUtil
open CollectVar
       
infixr 0 $
infix 0 !!

infix 9 %@
infix 8 %^
infix 7 %*
infix 6 %+ 
infix 4 %<=
infix 4 %>=
infix 4 %=
infixr 3 /\
infixr 2 \/
infixr 1 -->
infix 1 <->
        
fun unify_error cls r (s, s') =             
  Error (r, [sprintf "Can't unify $ " [cls]] @ indent [s] @ ["and"] @ indent [s'])

(* assumes arguments are already checked for well-formedness *)
fun unify_bs r (bs, bs') =
  case (update_bs bs, update_bs bs') of
      (UVarBS x, _) =>
      refine x bs'
    | (_, UVarBS _) =>
      unify_bs r (bs', bs)
    | (BSArrow (a, b), BSArrow (a', b')) => (unify_bs r (a, a'); unify_bs r (b, b'))
    | (Base b, Base b') =>
      if b = b' then
	()
      else
	raise Error (r, [sprintf "Base sort mismatch: $ and $" [str_b b, str_b b']])
    | _ => raise unify_error "base sort" r (str_bs bs, str_bs bs')
	         
fun V r n = VarI (NONE, (n, r))
fun TV r n = MtVar (NONE, (n, r))
               
fun find_injection (eq : 'a -> 'a -> bool) (xs : 'a list) (ys : 'a list) : int list option =
  let
    exception Error
    fun f x =
      case findi (fn y => eq x y) ys of
          SOME (n, _) => n
        | NONE => raise Error
  in
    SOME (map f xs)
    handle Error => NONE
  end

exception UnifyAppUVarFailed of string
(* Try to see whether [i']'s variables are covered by the arguments applied to [x]. If so, then refine [x] with [i'], with the latter's variables replaced by the former's arguments. This may not be the most general instantiation, because [i']'s constants will be fixed for [x], although those constants may be arguments in a more instantiation. For example, unifying [x y 5] with [y+5] will refine [x] to be [fun y z => y+5], but a more general instantiation is [fun y z => y+z]. This less-general instantiation may cause later unifications to fail. *)
fun unify_IApp r i i' =
  let
    val i = normalize_i i
    val ((x, _), args) = is_IApp_UVarI i !! (fn () => raise UnifyAppUVarFailed "")
    val i' = normalize_i i'
    open CollectUVar
    val () = if mem op= x (map #1 $ collect_uvar_i_i i') then raise UnifyAppUVarFailed "" else ()
    val vars' = dedup eq_long_id $ collect_var_i_i i'

                      
    (* open CollectVar *)
    (* val uncovered = List.filter (fn var => not (List.exists (fn arg => eq_i (VarI var) arg) args)) vars' *)
    (* fun forget_nonconsuming (var as (m, (x, _))) b = *)
    (*   let *)
    (*     val () = if isNone m then () else raise UnifyAppUVarFailed *)
    (*     open UVarForget *)
    (*     val b = forget_i_i x 1 b *)
    (*     val b = shiftx_i_i x 1 b *)
    (*   in *)
    (*     b *)
    (*   end *)
    (* val i' = foldl (fn (x, acc) => forget_nonconsuming x acc) i' uncovered *)
    (*           handle ForgetError _ => raise UnifyAppUVarFailed *)
    (* val i' = normalize_i i' *)

                         
    val inj = find_injection eq_i (map VarI vars') (rev args) !! (fn () => raise UnifyAppUVarFailed "")
    val i' = psubst_is_i vars' (map (V r) inj) i'
    val (name, ctx, b) = get_uvar_info x !! (fn () => raise Impossible "unify_IApp(): shouldn't be [Refined]")
    val b = update_bs b
    (* val () = println $ str_bs b *)
    (* val () = println $ sprintf "unifying ?$" [str_int name] *)
    fun var_name n = "__x" ^ str_int n
    val (bsorts, _) = collect_BSArrow b
    val bsorts = rev bsorts
    (* val () = println $ str_ls str_bs bsorts *)
    val ext_ctx = mapi (mapFst var_name) bsorts
    val ctx = ext_ctx @ ctx
    val () = if length args <= length ctx then () else raise Impossible "unify_IApp(): #args shouldn't be larger than #ctx"
    (* #args could be < #ctx because of partial application *)
    val ctx = lastn (length args) ctx
    fun IAbsMany (ctx, i, r) = foldl (fn ((name, b), i) => IAbs (b, Bind ((name, r), i), r)) i ctx
    val i' = IAbsMany (ctx, i', r)
    val () = refine x i'
  in
    ()
  end
    
fun unify_i r gctxn ctxn (i, i') =
  let
    val unify_i = unify_i r gctxn
    fun structural_compare (i, i') =
      let
        fun default () = 
          if eq_i i i' then ()
          else write_prop (BinPred (EqP, i, i'), r)
      in
        (* if one-side is not in a normal form because of uvar, we can't do structural comparison *)
        if isSome (is_IApp_UVarI i) orelse isSome (is_IApp_UVarI i') then
          default ()
        else
        case (i, i') of
            (* ToReal is injective *)
            (UnOpI (ToReal, i, _), UnOpI (ToReal, i', _)) =>
            unify_i ctxn (i', i)
          | _ => default ()
      end
    val i = whnf_i i (* todo: whnf_i is enough *)
    val i' = whnf_i i'
    (* val () = println $ sprintf "Unifying indices $ and $" [str_i gctxn ctxn i, str_i gctxn ctxn i'] *)
    val () =
        if eq_i i i' then ()
        else
          (* first try unifying applications of uvars with the other index; if unsuccessful in both directions, then try ordinary structural unification *)
          unify_IApp r i i'
          handle
          UnifyAppUVarFailed _ =>
          (unify_IApp r i' i
           handle
           UnifyAppUVarFailed _ =>
           structural_compare (i, i'))
    (* val () = println "unify_i () ended" *)
  in
    ()
  end

fun is_sub_sort r gctxn ctxn (s, s') =
  let
    val is_sub_sort = is_sub_sort r gctxn
    val is_eqv_sort = is_eqv_sort r gctxn
    fun unify_SApp s s' =
      let
        val ((x, _), args) = is_SApp_UVarS s !! (fn () => raise UnifyAppUVarFailed "")
        val args = map normalize_i args
        val s' = normalize_s s'
        open CollectUVar
        val () = if mem op= x (map #1 $ collect_uvar_s_s s') then raise UnifyAppUVarFailed "" else ()
        val vars' = dedup eq_long_id $ collect_var_i_s s'
        val inj = find_injection eq_i (map VarI vars') (rev args) !! (fn () => raise UnifyAppUVarFailed "")
        val s' = psubst_is_s vars' (map (V r) inj) s'
        val (_, ctx) = get_uvar_info x !! (fn () => raise Impossible "unify_s()/SApp: shouldn't be [Refined]")
        val () = if length args <= length ctx then () else raise Impossible "unify_SApp(): #args shouldn't be larger than #ctx"
        (* #args could be < #ctx because of partial application *)
        val ctx = lastn (length args) ctx
        val s' = SAbsMany (ctx, s', r)
        val () = refine x s'
      in
        ()
      end
    fun structural_compare (s, s') =
      let
        fun default () = raise Error (r, ["Sort"] @ indent [str_s gctxn ctxn s] @ ["is not a subsort of"] @ indent [str_s gctxn ctxn s'])
      in
        (* if one-side is not in a normal form because of uvar, we can't do structural comparison *)
        if isSome (is_SApp_UVarS s) orelse isSome (is_SApp_UVarS s') then
          default ()
        else
        case (s, s') of
            (Basic (bs, _), Basic (bs', _)) =>
            unify_bs r (bs, bs')
          | (Subset ((bs, r1), Bind ((name, _), p), _), Subset ((bs', _), Bind (_, p'), _)) =>
            let
	      val () = unify_bs r (bs, bs')
              val ctxd = ctx_from_sorting (name, Basic (bs, r1))
              val () = open_ctx ctxd
	      (* val () = write_prop (p <-> p', r) *)
	      val () = write_prop (p --> p', r)
	      (* val () = write_prop (p' --> p, r) *)
              val () = close_ctx ctxd
            in
              ()
            end
          | (Subset ((bs, r1), Bind ((name, _), p), _), Basic (bs', _)) =>
            let
	      val () = unify_bs r (bs, bs')
              val ctxd = ctx_from_sorting (name, Basic (bs, r1))
              val () = open_ctx ctxd
	      (* val () = write_prop (p, r) *)
              val () = close_ctx ctxd
            in
              ()
            end
          | (Basic (bs, r1), Subset ((bs', _), Bind ((name, _), p), _)) =>
            let
	      val () = unify_bs r (bs, bs')
              val ctxd = ctx_from_sorting (name, Basic (bs, r1))
              val () = open_ctx ctxd
	      val () = write_prop (p, r)
              val () = close_ctx ctxd
            in
              ()
            end
          | (SortBigO s, s') => is_sub_sort ctxn (SortBigO_to_Subset s, s')
          | (s, SortBigO s') => is_sub_sort ctxn (s, SortBigO_to_Subset s')
          | (SAbs (s1, Bind ((name, _), s), _), SAbs (s1', Bind (_, s'), _)) =>
            let
              val () = is_eqv_sort ctxn (s1, s1')
              val () = is_sub_sort (name :: ctxn) (s, s')
            in
              ()
            end
          | (SApp (s, i), SApp (s', i')) =>
            let
              val () = is_sub_sort ctxn (s, s')
              val () = unify_i r gctxn ctxn (i, i')
            in
              ()
            end
          | _ => default ()
      end
    val s = whnf_s s
    val s' = whnf_s s'
  in
    if eq_s s s' then ()
    else
      unify_SApp s s'
      handle
      UnifyAppUVarFailed _ =>
      (unify_SApp s' s
       handle
       UnifyAppUVarFailed _ =>
       structural_compare (s, s'))
  end

and is_eqv_sort r gctxn ctxn (s, s') =
  let
    val () = is_sub_sort r gctxn ctxn (s, s')
    val () = is_sub_sort r gctxn ctxn (s', s)
  in
    ()
  end
    
fun is_sub_sorts r gctx ctx (sorts, sorts') =
  (check_length r (sorts, sorts');
   ListPair.app (is_sub_sort r gctx ctx) (sorts, sorts'))

fun is_eqv_sorts r gctx ctx (sorts, sorts') =
  let
    val () = is_sub_sorts r gctx ctx (sorts, sorts')
    val () = is_sub_sorts r gctx ctx (sorts', sorts)
  in
    ()
  end

fun kind_mismatch expect str_got got = sprintf "Kind mismatch: expect $ got $" [expect, str_got got]
fun kind_mismatch_in_type expected str_got got thing =
  [sprintf "Kind mismatch:" [thing]] @ indent [sprintf "expected:\t $" [expected], sprintf "got:\t $" [str_got got], sprintf "in type:\t $" [thing]]

fun is_sub_kind r gctxn sctxn (k as (ntargs, sorts), k' as (ntargs', sorts')) =
  let
    val () = check_eq r op= (ntargs, ntargs')
    (* contravariant *)
    val () = is_sub_sorts r gctxn sctxn (sorts', sorts)
  in
    ()
  end
  handle Error _ => raise Error (r, [kind_mismatch (str_k gctxn sctxn k') (str_k gctxn sctxn) k])
                              
fun is_eqv_kind r gctxn sctxn (k, k') =
  let
    val () = is_sub_kind r gctxn sctxn (k, k')
    val () = is_sub_kind r gctxn sctxn (k', k)
  in
    ()
  end

(*      
fun unify_kind r gctxn sctxn (k, k') =
    case (k, k') of
        (ArrowK (is_dt, ntargs, sorts), ArrowK (is_dt', ntargs', sorts')) =>
        let
          val () = check_eq r op= (is_dt, is_dt')
          val () = check_eq r op= (ntargs, ntargs')
          val () = unify_sorts r gctxn sctxn (sorts, sorts')
        in
          ()
        end
        handle Error _ => raise Error (r, [kind_mismatch gctxn sctxn (str_k gctxn sctxn k) k'])
*)
    
fun unify_mt r gctx ctx (t, t') =
  let
    val unify_mt = unify_mt r gctx
    val sctx = #1 ctx
    val kctx = #2 ctx
    val gctxn = gctx_names gctx
    val ctxn as (sctxn, kctxn) = (sctx_names sctx, names kctx)
    fun error ctxn (t, t') = unify_error "type" r (str_mt gctxn ctxn t, str_mt gctxn ctxn t')
    (* fun error ctxn (t, t') = unify_error "type" r (str_raw_mt t, str_raw_mt t') *)
    fun unify_MtApp t t' =
      let
        val ((x, _), i_args, t_args) = is_MtApp_UVar t !! (fn () => raise UnifyAppUVarFailed "is_MtApp_UVar() fails")
        (* val () = println $ "#i_args=" ^ str_int (length i_args) *)
        val i_args = map normalize_i i_args
        val t_args = map (normalize_mt gctx kctx) t_args
        val t' = normalize_mt gctx kctx t'
        val i_vars' = dedup eq_long_id $ collect_var_i_mt t'
        (* val () = println $ "t'=" ^ (str_mt gctxn ctxn t') *)
                                       
                                       
        open CollectVar
        val uncovered = List.filter (fn var => not (List.exists (fn arg => eq_i (VarI var) arg) i_args)) i_vars'
        fun forget_nonconsuming (var as (m, (x, _))) b =
          let
            val () = if isNone m then () else raise UnifyAppUVarFailed "can't forget moduled variable"
            open UVarForget
            val b = normalize_mt gctx kctx b
            val b = forget_i_mt x 1 b
            val b = shiftx_i_mt x 1 b
          in
            b
          end
        val t' = foldl (fn (x, acc) => forget_nonconsuming x acc) t' uncovered
                 handle ForgetError _ => raise UnifyAppUVarFailed "ForgetError"
        val t' = normalize_mt gctx kctx t'

        (* val () = println $ "t'=" ^ (str_mt gctxn ctxn t') *)
        val t = normalize_mt gctx kctx t
        val ((x, _), i_args, t_args) = is_MtApp_UVar t !! (fn () => raise UnifyAppUVarFailed "is_MtApp_UVar() fails")
        val () = if mem op= x (map #1 $ CollectUVar.collect_uvar_t_mt t') then raise UnifyAppUVarFailed "[x] is in [t']" else ()
        val i_vars' = dedup eq_long_id $ collect_var_i_mt t'
        val t_vars' = dedup eq_long_id $ collect_var_t_mt t'
        val i_inj = find_injection eq_i (map VarI i_vars') (rev i_args) !! (fn () => raise UnifyAppUVarFailed "find_inject(i_args) failed")
        val t_inj = find_injection eq_mt (map MtVar t_vars') (rev t_args) !! (fn () => raise UnifyAppUVarFailed "find_inject(t_args) failed")
        val () = assert (fn () => length t_vars' = length t_inj) "length t_vars' = length t_inj"
        val t' = psubst_ts_mt t_vars' (map (TV r) t_inj) t'
        val t' = psubst_is_mt i_vars' (map (V r) i_inj) t'
        val (uvar_name, (sctx, kctx)) = get_uvar_info x !! (fn () => raise Impossible "unify_MtApp()/MtApp: shouldn't be [Refined]")
        (* val () = println $ "sctx=" ^ str_ls fst sctx *)
        val () = if length i_args <= length sctx then () else raise Impossible "unify_MtApp(): #i_args <> #sctx"
        (* #i_args could be < #sctx because of partial application *)
        val () = if length t_args <= length kctx then () else raise Impossible "unify_MtApp(): #t_args shouldn't be larger than #kctx"
        (* #t_args could be < #kctx because of partial application *)
        (* val () = println $ "#i_args=" ^ str_int (length i_args) *)
        val sctx = lastn (length i_args) sctx
        val kctx = lastn (length t_args) kctx
        val t' = MtAbsMany (kctx, t', r)
        (* val () = println $ "sctx=" ^ str_ls fst sctx *)
        val t' = MtAbsIMany (sctx, t', r)
        (* val () = println $ str_mt empty ([], []) t' *)
        (* val () = println $ str_raw_mt t' *)
        (* val () = println $ sprintf "unify_MtApp(): refine ?$ to be $" [str_int uvar_name, str_mt gctxn ctxn t'] *)
        val () = refine x t'
        (* val () = println "unify_MtApp() succeeded" *)
      in
        ()
      end
    fun structural_compare (t, t') =
      if eq_mt t t' then ()
      (* if one-side is not in a normal form because of uvar, we can't do structural comparison *)
      else if isSome (is_MtApp_UVar t) orelse isSome (is_MtApp_UVar t') then
        raise error ctxn (t, t')
      else
      case (t, t') of
          (Arrow (t1, d, t2), Arrow (t1', d', t2')) =>
          (unify_mt ctx (t1, t1');
           unify_i r gctxn sctxn (d, d');
           unify_mt ctx (t2, t2'))
        | (TyArray (t, i), TyArray (t', i')) =>
          (unify_mt ctx (t, t');
           unify_i r gctxn sctxn (i, i')
          )
        | (TyNat (i, _), TyNat (i', _)) =>
          unify_i r gctxn sctxn (i, i')
        | (Prod (t1, t2), Prod (t1', t2')) =>
          (unify_mt ctx (t1, t1');
           unify_mt ctx (t2, t2'))
        | (UniI (s, Bind ((name, _), t1), _), UniI (s', Bind (_, t1'), _)) =>
          let
            val () = is_eqv_sort r gctxn sctxn (s, s')
            val () = open_close add_sorting_sk (name, s) ctx (fn ctx => unify_mt ctx (t1, t1'))
          in
            ()
          end
        | (Unit _, Unit _) => ()
	| (BaseType (Int, _), BaseType (Int, _)) => ()
        | (MtAbs (k, Bind ((name, _), t), _), MtAbs (k', Bind (_, t'), _)) =>
          let
            val () = is_eqv_kind r gctxn sctxn (k, k')
            val () = unify_mt (add_kinding_sk (name, k) ctx) (t, t')
          in
            ()
          end
        | (MtApp (t1, t2), MtApp (t1', t2')) => 
          let
            val () = unify_mt ctx (t1, t1')
            val () = unify_mt ctx (t2, t2')
          in
            ()
          end
        | (MtAbsI (s, Bind ((name, _), t), _), MtAbsI (s', Bind (_, t'), _)) =>
          let
            val () = is_eqv_sort r gctxn sctxn (s, s')
            val () = open_close add_sorting_sk (name, s) ctx (fn ctx => unify_mt ctx (t, t'))
          in
            ()
          end
        | (MtAppI (t, i), MtAppI (t', i')) => 
          let
            val () = unify_mt ctx (t, t')
            val () = unify_i r gctxn sctxn (i, i')
          in
            ()
          end
	| _ => raise error ctxn (t, t')
    val t = whnf_mt gctx kctx t
    val t' = whnf_mt gctx kctx t'
    (* val () = println $ sprintf "Unifying types\n\t$\n  and\n\t$" [str_mt gctxn ctxn t, str_mt gctxn ctxn t'] *)
    (* Apply [unify_MtApp] in which order? Here is a heuristic: *)
    fun more_uvar_args (a, b) =
      case (is_MtApp_UVar a, is_MtApp_UVar b) of
          (SOME (_, i_args, t_args), SOME (_, i_args', t_args')) =>
          length i_args > length i_args' andalso length t_args > length t_args'
        | _ => false
    val (t_more, t_less) = if more_uvar_args (t', t) then
               (t', t)
             else
               (t, t')
    val () = 
        if eq_mt t t' then ()
        else
          unify_MtApp t_more t_less
          handle
          UnifyAppUVarFailed msg =>
          let
            (* val () = println ("(unify_MtApp t t') failed because " ^ msg) *)
            val t_less = whnf_mt gctx kctx t_less
          in
            unify_MtApp t_less t_more
            handle
            UnifyAppUVarFailed msg =>
            let
              (* val () = println ("(unify_MtApp t' t) failed because " ^ msg) *)
              val t = whnf_mt gctx kctx t
              val t' = whnf_mt gctx kctx t'
            in
              structural_compare (t, t')
            end
          end
    (* val () = println "unify_mt () ended" *)
  in
    ()
  end

fun unify_t r gctx ctx (t, t') =
  case (t, t') of
      (Mono t, Mono t') => unify_mt r gctx ctx (t, t')
    | (Uni (Bind ((name, _), t), _), Uni (Bind (_, t'), _)) => unify_t r gctx (add_kinding_sk (name, Type) ctx) (t, t')
    | _ =>
      let
        val gctxn = gctx_names gctx
        val ctxn = (sctx_names $ #1 ctx, names $ #2 ctx)
      in
        raise unify_error "poly-type" r (str_t gctxn ctxn t, str_t gctxn ctxn t')
      end
        
fun is_sub_kindext r gctx ctx (ke as (dt, k, t), ke' as (dt', k', t')) =
  let
    val gctxn = gctx_names gctx
    val sctxn = sctx_names $ #1 ctx
    val kctxn = names $ #2 ctx
    val () = check_eq r op= (dt, dt')
    val () = is_sub_kind r gctxn sctxn (k, k')
  in
    case (t, t') of
        (NONE, NONE) => ()
      | (SOME t, SOME t') => unify_mt r gctx ctx (t, t')
      | (SOME _, NONE) => ()
      | (_, _) => raise Error (r, [sprintf "Kind $ is not a sub kind of $" [str_ke gctxn (sctxn, kctxn) ke, str_ke gctxn (sctxn, kctxn) ke']])
  end

end
