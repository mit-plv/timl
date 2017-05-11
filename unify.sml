(* unification *)

structure Unify = struct
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
	         
(* parallel substitution *)
    
fun psubst_aux_is_ibind f d x v (Bind (name, b) : ('a * 'b) ibind) =
  Bind (name, f (d + 1) x v b)
       
fun apply_depth d (m, (x, r)) =
  case m of
      SOME _ => (m, (x, r))
    | NONE => (NONE, (x + d, r))

fun psubst_long_id d x get_v default y =
  case findi (curry eq_long_id y) (map (apply_depth d) x) of
      SOME (n, _) => get_v n
    | NONE => default
          
local
  fun f d x v b =
    case b of
	VarI y => psubst_long_id d x (fn n => shiftx_i_i 0 d (List.nth (v, n))) b y
      | IConst _ => b
      | UnOpI (opr, i, r) => UnOpI (opr, f d x v i, r)
      | BinOpI (opr, d1, d2) => BinOpI (opr, f d x v d1, f d x v d2)
      | Ite (i1, i2, i3, r) => Ite (f d x v i1, f d x v i2, f d x v i3, r)
      | IAbs (b, bind, r) => IAbs (b, psubst_aux_is_ibind f d x v bind, r)
      | UVarI a => b
in
val psubst_aux_is_i = f 
fun psubst_is_i x v b = f 0 x v b
end
        
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

exception UnifyIAppFailed
(* Try to see whether [i']'s variables are covered by the arguments applied to [x]. If so, then refine [x] with [i'], with the latter's variables replaced by the former's arguments. This may not be the most general instantiation, because [i']'s constants will be fixed for [x], although those constants may be arguments in a more instantiation. For example, unifying [x y 5] with [y+5] will refine [x] to be [fun y z => y+5], but a more general instantiation is [fun y z => y+z]. This less-general instantiation may cause later unifications to fail. *)
fun unify_IApp r i i' =
  let
    val i = normalize_i i
    val ((x, _), args) = is_IApp_UVarI i !! (fn () => raise UnifyIAppFailed)
    val i' = normalize_i i'
    open CollectUVar
    val () = if mem op= x (map #1 $ collect_uvar_i_i i') then raise UnifyIAppFailed else ()
    val vars' = dedup eq_long_id $ collect_var_i_i i'

                      
    (* open CollectVar *)
    (* val uncovered = List.filter (fn var => not (List.exists (fn arg => eq_i (VarI var) arg) args)) vars' *)
    (* fun forget_nonconsuming (var as (m, (x, _))) b = *)
    (*   let *)
    (*     val () = if isNone m then () else raise UnifyIAppFailed *)
    (*     open UVarForget *)
    (*     val b = forget_i_i x 1 b *)
    (*     val b = shiftx_i_i x 1 b *)
    (*   in *)
    (*     b *)
    (*   end *)
    (* val i' = foldl (fn (x, acc) => forget_nonconsuming x acc) i' uncovered *)
    (*           handle ForgetError _ => raise UnifyIAppFailed *)
    (* val i' = normalize_i i' *)

                         
    val inj = find_injection eq_i (map VarI vars') (rev args) !! (fn () => raise UnifyIAppFailed)
    val i' = psubst_is_i vars' (map (V r) inj) i'
    val (name, ctx, b) = get_uvar_info x !! (fn () => raise Impossible "unify_IApp(): shouldn't be [Refined]")
    val b = update_bs b
    (* val () = println $ str_bs b *)
    val () = println $ sprintf "unifying ?$" [str_int name]
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
          UnifyIAppFailed =>
          (unify_IApp r i' i
           handle
           UnifyIAppFailed =>
           structural_compare (i, i'))
    (* val () = println "unify_i () ended" *)
  in
    ()
  end

local
  fun f d x v b =
    case b of
	PTrueFalse _ => b
      | Not (p, r) => Not (f d x v p, r)
      | BinConn (opr,p1, p2) => BinConn (opr, f d x v p1, f d x v p2)
      | BinPred (opr, i1, i2) => BinPred (opr, psubst_aux_is_i d x v i1, psubst_aux_is_i d x v i2)
      | Quan (q, bs, bind, r) => Quan (q, bs, psubst_aux_is_ibind f d x v bind, r)
in
val psubst_aux_is_p = f
fun psubst_is_p x v b = f 0 x v b
end

local
  fun f d x v b =
    case b of
	Basic s => Basic s
      | Subset (b, bind, r) => Subset (b, psubst_aux_is_ibind psubst_aux_is_p d x v bind, r)
      | UVarS a => b
      | SortBigO (b, i, r) => SortBigO (b, psubst_aux_is_i d x v i, r)
      | SAbs (s, bind, r) => SAbs (f d x v s, psubst_aux_is_ibind f d x v bind, r)
      | SApp (s, i) => SApp (f d x v s, psubst_aux_is_i d x v i)
in
val psubst_aux_is_s = f
fun psubst_is_s x v b = f 0 x v b
end

fun eq_s s s' =
  case s of
      Basic (b, _) =>
      (case s' of
           Basic (b', _) => eq_bs b b'
         | _ => false
      )
    | Subset ((b, _), Bind (_, p), _) =>
      (case s' of
           Subset ((b', _), Bind (_, p'), _) => eq_bs b b' andalso eq_p p p'
         | _ => false
      )
    | UVarS (x, _) =>
      (case s' of
           UVarS (x', _) => x = x'
         | _ => false
      )
    | SortBigO ((b, _), i, _) =>
      (case s' of
           SortBigO ((b', _), i', _) => eq_bs b b' andalso eq_i i i'
         | _ => false
      )
    | SAbs (s1, Bind (_, s), _) =>
      (case s' of
           SAbs (s1', Bind (_, s'), _) => eq_s s1 s1' andalso eq_s s s'
         | _ => false
      )
    | SApp (s, i) =>
      (case s' of
           SApp (s', i') => eq_s s s' andalso eq_i i i'
         | _ => false
      )
                                                             
fun is_sub_sort r gctxn ctxn (s, s') =
  let
    val is_sub_sort = is_sub_sort r gctxn
    val is_eqv_sort = is_eqv_sort r gctxn
    exception UnifySAppFailed
    fun unify_SApp s s' =
      let
        val (x, args) = is_SApp_UVarS s !! (fn () => raise UnifySAppFailed)
        val args = map normalize_i args
        val s' = normalize_s s'
        val vars' = collect_var_i_s s'
        val inj = find_injection eq_i (map VarI vars') (rev args) !! (fn () => raise UnifySAppFailed)
        val s' = psubst_is_s vars' (map (V r) inj) s'
        val (_, ctx) = get_uvar_info x !! (fn () => raise Impossible "unify_s()/SApp: shouldn't be [Refined]")
        val s' = SAbsMany (ctx, s', r)
        val () = refine x s'
      in
        ()
      end
    fun structural_compare (s, s') =
      let
        fun default () = raise Error (r, ["Sort"] @ indent [str_s gctxn ctxn s] @ ["is not a subsort of"] @ indent [str_s gctxn ctxn s'])
      in
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
      UnifySAppFailed =>
      (unify_SApp s' s
       handle
       UnifySAppFailed =>
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
    
fun psubst_aux_is_k d x v b = mapSnd (map (psubst_aux_is_s d x v)) b
        
fun psubst_aux_is_tbind f d x v (Bind (name, b) : ('a * 'b) tbind) =
  Bind (name, f d x v b)
local
  fun f d x v b =
    case b of
	Arrow (t1, i, t2) => Arrow (f d x v t1, psubst_aux_is_i d x v i, f d x v t2)
      | TyNat (i, r) => TyNat (psubst_aux_is_i d x v i, r)
      | TyArray (t, i) => TyArray (f d x v t, psubst_aux_is_i d x v i)
      | Unit r => Unit r
      | Prod (t1, t2) => Prod (f d x v t1, f d x v t2)
      | UniI (s, bind, r) => UniI (psubst_aux_is_s d x v s, psubst_aux_is_ibind f d x v bind, r)
      | MtVar y => MtVar y
      | MtApp (t1, t2) => MtApp (f d x v t1, f d x v t2)
      | MtAbs (k, bind, r) => MtAbs (psubst_aux_is_k d x v k, psubst_aux_is_tbind f d x v bind, r)
      | MtAppI (t, i) => MtAppI (f d x v t, psubst_aux_is_i d x v i)
      | MtAbsI (s, bind, r) => MtAbsI (psubst_aux_is_s d x v s, psubst_aux_is_ibind f d x v bind, r)
      | BaseType a => BaseType a
      | UVar a => b
in
val psubst_aux_is_mt = f
fun psubst_is_mt x v b = f 0 x v b
end

fun psubst_aux_ts_ibind f (di, dt) x v (Bind (name, b) : ('a * 'b) ibind) =
  Bind (name, f (di + 1, dt) x v b)
fun psubst_aux_ts_tbind f (di, dt) x v (Bind (name, b) : ('a * 'b) tbind) =
  Bind (name, f (di, dt + 1) x v b)
local
  fun f d x v b =
    case b of
	Arrow (t1, i, t2) => Arrow (f d x v t1, i, f d x v t2)
      | TyNat (i, r) => TyNat (i, r)
      | TyArray (t, i) => TyArray (f d x v t, i)
      | Unit r => Unit r
      | Prod (t1, t2) => Prod (f d x v t1, f d x v t2)
      | UniI (s, bind, r) => UniI (s, psubst_aux_ts_ibind f d x v bind, r)
      | MtVar y => psubst_long_id (snd d) x (fn n => shiftx_i_mt 0 (fst d) (shiftx_t_mt 0 (snd d) (List.nth (v, n)))) b y
      | MtAbs (k, bind, r) => MtAbs (k, psubst_aux_ts_tbind f d x v bind, r)
      | MtApp (t1, t2) => MtApp (f d x v t1, f d x v t2)
      | MtAbsI (s, bind, r) => MtAbsI (s, psubst_aux_ts_ibind f d x v bind, r)
      | MtAppI (t, i) => MtAppI (f d x v t, i)
      | BaseType a => BaseType a
      | UVar a => b
in
val psubst_aux_ts_mt = f
fun psubst_ts_mt x v b = f (0, 0) x v b
end

fun eq_ls eq (ls1, ls2) = length ls1 = length ls2 andalso List.all eq $ zip (ls1, ls2)
                                                              
fun eq_k ((n, sorts) : kind) (n', sorts') =
  n = n' andalso eq_ls (uncurry eq_s) (sorts, sorts')
  
fun eq_mt t t' = 
    case t of
	Arrow (t1, i, t2) =>
        (case t' of
	     Arrow (t1', i', t2') => eq_mt t1 t1' andalso eq_i i i' andalso eq_mt t2 t2'
           | _ => false
        )
      | TyNat (i, r) =>
        (case t' of
             TyNat (i', _) => eq_i i i'
           | _ => false
        )
      | TyArray (t, i) =>
        (case t' of
             TyArray (t', i') => eq_mt t t' andalso eq_i i i'
           | _ => false
        )
      | Unit r =>
        (case t' of
             Unit _ => true
           | _ => false
        )
      | Prod (t1, t2) =>
        (case t' of
             Prod (t1', t2') => eq_mt t1 t1' andalso eq_mt t2 t2'
           | _ => false
        )
      | UniI (s, Bind (_, t), r) =>
        (case t' of
             UniI (s', Bind (_, t'), _) => eq_s s s' andalso eq_mt t t'
           | _ => false
        )
      | MtVar x =>
        (case t' of
             MtVar x' => eq_long_id (x, x')
           | _ => false
        )
      | MtAbs (k, Bind (_, t), r) =>
        (case t' of
             MtAbs (k', Bind (_, t'), _) => eq_k k k' andalso eq_mt t t'
           | _ => false
        )
      | MtApp (t1, t2) =>
        (case t' of
             MtApp (t1', t2') => eq_mt t1 t1' andalso eq_mt t2 t2'
           | _ => false
        )
      | MtAbsI (s, Bind (_, t), r) =>
        (case t' of
             MtAbsI (s', Bind (_, t'), _) => eq_s s s' andalso eq_mt t t'
           | _ => false
        )
      | MtAppI (t, i) =>
        (case t' of
             MtAppI (t', i') => eq_mt t t' andalso eq_i i i'
           | _ => false
        )
      | BaseType (a : base_type, r) =>
        (case t' of
             BaseType (a' : base_type, _)  => eq_base_type (a, a')
           | _ => false
        )
      | UVar (x, _) =>
        (case t' of
             UVar (x', _) => x = x'
           | _ => false
        )

fun MtAbsMany (ctx, t, r) = foldl (fn ((name, k), t) => MtAbs (k, Bind ((name, r), t), r)) t ctx
fun MtAbsIMany (ctx, t, r) = foldl (fn ((name, s), t) => MtAbsI (s, Bind ((name, r), t), r)) t ctx

fun unify_mt r gctx ctx (t, t') =
  let
    val unify_mt = unify_mt r gctx
    val sctx = #1 ctx
    val kctx = #2 ctx
    val gctxn = gctx_names gctx
    val ctxn as (sctxn, kctxn) = (sctx_names sctx, names kctx)
    fun error ctxn (t, t') = unify_error "type" r (str_mt gctxn ctxn t, str_mt gctxn ctxn t')
    (* fun error ctxn (t, t') = unify_error "type" r (str_raw_mt t, str_raw_mt t') *)
    exception UnifyMtAppFailed
    fun unify_MtApp t t' =
      let
        val (x, i_args, t_args) = is_MtApp_UVar t !! (fn () => raise UnifyMtAppFailed)
        val i_args = map normalize_i i_args
        val t_args = map (normalize_mt gctx kctx) t_args
        val t' = normalize_mt gctx kctx t'
        val i_vars' = collect_var_i_mt t'
        val i_inj = find_injection eq_i (map VarI i_vars') (rev i_args) !! (fn () => raise UnifyMtAppFailed)
        val t_vars' = collect_var_t_mt t'
        val t_inj = find_injection eq_mt (map MtVar t_vars') (rev t_args) !! (fn () => raise UnifyMtAppFailed)
        val () = assert (fn () => length t_vars' = length t_inj) "length t_vars' = length t_inj"
        val t' = psubst_ts_mt t_vars' (map (TV r) t_inj) t'
        val t' = psubst_is_mt i_vars' (map (V r) i_inj) t'
        val (_, (sctx, kctx)) = get_uvar_info x !! (fn () => raise Impossible "unify_t()/MtApp: shouldn't be [Refined]")
        val () = if length i_args <= length sctx then () else raise Impossible "unify_MtApp(): #i_args <> #sctx"
        val () = if length t_args <= length kctx then () else raise Impossible "unify_MtApp(): #t_args shouldn't be larger than #kctx"
        (* #t_args could be < #kctx because of partial application *)
        val kctx = lastn (length t_args) kctx
        val t' = MtAbsMany (kctx, t', r)
        val t' = MtAbsIMany (sctx, t', r)
        val () = refine x t'
        (* val () = println "unify_MtApp() succeeded" *)
      in
        ()
      end
    fun structural_compare (t, t') =
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
    val () = 
        if eq_mt t t' then ()
        else
          unify_MtApp t t'
          handle
          UnifyMtAppFailed =>
          ((* println "(unify_MtApp t t') failed";  *)unify_MtApp t' t
           handle
           UnifyMtAppFailed =>
           structural_compare (t, t'))
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
