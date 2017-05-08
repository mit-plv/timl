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
               
fun fresh_i_with_bsorts ctx bsort r = 
  let
    val x = fresh_uvar_i ctx bsort
    val i = UVarI (x, r)
    val i = IApps i (map (V r) $ rev $ range (length ctx))
  in
    i
  end

fun fresh_i ctx bsort r = 
  let
    val ctx = map (mapSnd (get_base refine_UVarS_to_Basic)) ctx
    val i = fresh_i_with_bsorts ctx bsort r
  in
    i
  end

fun fresh_sort ctx r : sort =
  let
    val x = ref (Fresh (inc (), ctx))
    val s = UVarS (x, r)
    val s = SApps s (map (V r) $ rev $ range (length ctx))
  in
    s
  end
                                             
fun uvar_s_ignore_args (x, info, r) =
  let
    val (_, ctx) = info
    val s = fresh_sort [] r
    val s = SAbsMany (ctx, s, r)
    val () = refine x s
  in
    ()
  end

fun uvar_i_ignore_args (x, info, r) =
  let
    val (_, ctx, b) = info
    val s = fresh_i [] b r
    val s = IAbsMany (ctx, s, r)
    val () = assert (fn () => is_fresh x) "uvar_i_ignore_args(): fresh"
    val () = refine x s
  in
    ()
  end

fun fresh_mt (ctx as (sctx, kctx)) r : mtype =
  let
    val x = ref (Fresh (inc (), mapSnd (map (mapSnd get_ke_kind)) ctx))
    val t = UVar (x, r)
    val t = MtAppIs t (map (V r) $ rev $ range (length sctx))
    val t = MtApps t (map (TV r) $ rev $ range (length kctx))
  in
    t
  end

end
