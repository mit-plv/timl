structure SimpCtx = struct

open Simp
open SimpType
open TypecheckUtil
open Util
       
infixr 0 $
       
val simp_bs = id
val simp_c = id
                
fun simp_k k = mapSnd (map simp_bs) k
                      
fun simp_ke (k, t) = (simp_k k, Option.map simp_mt t)

fun simp_ctx (sctx, kctx, cctx, tctx) =
  let
    val sctx = map (mapSnd simp_s) sctx
    val kctx = map (mapSnd simp_ke) kctx
    val cctx = map (mapSnd simp_c) cctx
    val tctx = map (mapSnd simp_t) tctx
  in
    (sctx, kctx, cctx, tctx)
  end

fun simp_sgntr sg =
  case sg of
      Sig ctx => Sig $ simp_ctx ctx
    | FunctorBind ((arg_name, arg), body) =>
      FunctorBind ((arg_name, simp_ctx arg), simp_ctx body)

fun simp_sgntr_list gctx =
  List.map (mapSnd simp_sgntr) gctx

end
