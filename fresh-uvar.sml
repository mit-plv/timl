(* generate fresh uvar *)

structure FreshUVar = struct
open Util
open Expr
open Normalize
open TypecheckUtil

infixr 0 $
infix 0 !!
        
val counter = ref 0

fun inc () = 
  let 
    val n = !counter
    val () = counter := n + 1
  in
    n
  end

fun get_base (* r gctx ctx *) on_UVarS s =
  let
    val r = get_region_s s
    val s = normalize_s s
    exception OnSAppFailed
    fun on_SApp_UVarS s =
      let
        val (x, args) = is_SApp_UVarS s !! (fn () => raise OnSAppFailed)
        val info = get_uvar_info x !! (fn () => raise Impossible "check_sort()/unify_SApp_UVar(): x should be Fresh")
      in
        on_UVarS (x, r, info, args)
      end
    fun main s =
      case s of
          Basic (s, _) => s
        | Subset ((s, _), _, _) => s
        | SortBigO ((s, _), _, _) => s
        | UVarS _ => raise Impossible "get_base()/main(): shouldn't be UVarS"
        | SAbs _ => raise Impossible "get_base()/main(): shouldn't be SAbs"
        | SApp _ => raise Impossible "get_base()/main(): shouldn't be SApp"
  in
    on_SApp_UVarS s
    handle
    OnSAppFailed =>
    main s
  end

fun fresh_bsort () = UVarBS (ref (Fresh (inc ())))

fun refine_UVarS_to_Basic (x, r, info, args) =
  let
    val b = fresh_bsort ()
    val s = Basic (b, r)
    val (_, ctx) = info
    val s = SAbsMany (ctx, s, r)
    val () = refine x s
  in
    b
  end

fun V r n = VarI (NONE, (n, r))
fun TV r n = MtVar (NONE, (n, r))

fun fresh_uvar_i ctx bsort = ref (Fresh (inc (), ctx, bsort))

fun get_ctx_and_args sel make_arg on_snd gctx ctx_local r =
  let
    val gctx = filter_module gctx
    fun on_sgn (mod_name, ctx : context) =
      let
        val sctx = sel ctx
        val sctx = map (mapFst $ prefix $ mod_name ^ "_") sctx
        val sctx = map (mapSnd on_snd) sctx
        val sctx = mapi (mapFst (fn x => make_arg (SOME (mod_name, r), (x, r)))) sctx
      in
        sctx
      end
    val (args_global, ctx_global) = unzip $ List.concat $ map on_sgn $ gctx
    val args_global = rev args_global
    val ctx_local = map (mapSnd on_snd) ctx_local
    val ctx_total = ctx_local @ ctx_global
    val args_local = rev $ map (fn x => make_arg (NONE, (x, r))) $ range $ length ctx_local
    val args_total = args_global @ args_local
    val () = assert (fn () => length ctx_total = length args_total) "length ctx_total = length args_total"
  in
    (ctx_total, args_total)
  end

fun get_sctx_and_args x = get_ctx_and_args #1 VarI x
fun get_kctx_and_args x = get_ctx_and_args #2 MtVar x
    
fun fresh_i gctx ctx bsort r = 
  let
    val get_base = get_base refine_UVarS_to_Basic
    val (ctx, args) = get_sctx_and_args get_base gctx ctx r
    val x = fresh_uvar_i ctx bsort
    val i = UVarI (x, r)
    val i = IApps i args
  in
    i
  end

fun fresh_sort gctx ctx r =
  let
    val (ctx, args) = get_sctx_and_args id gctx ctx r
    val x = ref (Fresh (inc (), ctx))
    val s = UVarS (x, r)
    val s = SApps s args
  in
    s
  end
                                             
fun uvar_s_ignore_args (x, info, r) =
  let
    val (_, ctx) = info
    val s = fresh_sort [] [] r
    val s = SAbsMany (ctx, s, r)
    val () = refine x s
  in
    ()
  end

fun uvar_i_ignore_args (x, info, r) =
  let
    val (_, ctx, b) = info
    val s = fresh_i [] [] b r
    val s = IAbsMany (ctx, s, r)
    val () = assert (fn () => is_fresh x) "uvar_i_ignore_args(): fresh"
    val () = refine x s
  in
    ()
  end

fun fresh_mt gctx (sctx, kctx) r : mtype =
  let
    val (sctx, i_args) = get_sctx_and_args id gctx sctx r
    val (kctx, t_args) = get_kctx_and_args get_ke_kind gctx kctx r
    val x = ref (Fresh (inc (), (sctx, kctx)))
    val t = UVar (x, r)
    val t = MtAppIs t i_args
    val t = MtApps t t_args
  in
    t
  end

end
