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
        val ((x, _), args) = is_SApp_UVarS s !! (fn () => raise OnSAppFailed)
        val info = get_uvar_info x !! (fn () => raise Impossible "check_sort()/unify_SApp_UVar(): x should be Fresh")
      in
        on_UVarS (x, r, info, args)
      end
    fun main s =
      case s of
          Basic (s, _) => s
        | Subset ((s, _), _, _) => s
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
    val (uvar_name, ctx) = info
    val s = SAbs_Many (rev ctx, s, r)
    val () = println $ sprintf "Warning: refining ?$ to $ (where $ is a base-sort) in order to get its base sort" [str_int uvar_name, str_s empty [] s, str_bs b]
    val () = refine x s
  in
    b
  end

fun V r n = VarI (ID (n, r))
fun TV r n = MtVar (ID (n, r))

fun fresh_uvar_i ctx bsort = ref (Fresh (inc (), ctx, bsort))
fun fresh_uvar_mt ctx = ref (Fresh (inc (), ctx))

fun get_ctx_and_args sel make_arg on_snd package gctx ctx_local r =
  let
    val gctx = filter_module gctx
    fun on_sgn (mod_name : string, ctx : context) =
      let
        val ctx = sel ctx
        val ctx = map (mapFst $ prefix $ mod_name ^ "_") ctx
        val ctx = map (mapSnd (package (mod_name, r) o on_snd)) ctx
        val args_ctx = mapi (mapFst (fn x => make_arg $ QID ((mod_name, r), (x, r)))) ctx
      in
        args_ctx
      end
    val (args_global, ctx_global) = unzip $ concatMap on_sgn $ listItemsi gctx
    val args_global = rev args_global
    val ctx_local = map (mapSnd on_snd) ctx_local
    val ctx_total = ctx_local @ ctx_global
    val args_local = rev $ map (fn x => make_arg (ID (x, r))) $ range $ length ctx_local
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
    val (ctx, args) = get_sctx_and_args get_base return2 gctx ctx r
    val x = fresh_uvar_i ctx bsort
    val i = UVarI (x, r)
    val i = IApps i args
  in
    i
  end

fun fresh_sort gctx ctx r =
  let
    val get_base = get_base refine_UVarS_to_Basic
    val (ctx, args) = get_sctx_and_args get_base return2 gctx ctx r
    val x = ref (Fresh (inc (), ctx))
    val s = UVarS (x, r)
    val s = SApps s args
  in
    s
  end
                                             
fun uvar_s_ignore_args (x, info, r) =
  let
    val (_, ctx) = info
    val s = fresh_sort empty [] r
    val s = SAbs_Many (rev ctx, s, r)
    val () = refine x s
  in
    ()
  end

fun uvar_i_ignore_args (x, info, r) =
  let
    val (_, ctx, b) = info
    val s = fresh_i empty [] b r
    val s = IAbs_Many (rev ctx, s, r)
    val () = assert (fn () => is_fresh x) "uvar_i_ignore_args(): fresh"
    val () = refine x s
  in
    ()
  end

fun fresh_mt gctx (sctx, kctx) r : mtype =
  let
    val get_base = get_base refine_UVarS_to_Basic
    val (sctx, i_args) = get_sctx_and_args get_base return2 gctx sctx r
    val (kctx, t_args) = get_kctx_and_args get_ke_kind return2 gctx kctx r
    val x = fresh_uvar_mt (sctx, kctx)
    val t = UVar (x, r)
    val t = MtAppIs t i_args
    val t = MtApps t t_args
  in
    t
  end

end
