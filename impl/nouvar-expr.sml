structure NoUVar = struct
open Util
       
type 'bsort uvar_bs = empty
type ('bsort, 'idx) uvar_i = empty
type 'sort uvar_s = empty
type 'mtype uvar_mt = empty
fun str_uvar_bs (_ : 'a -> string) (u : 'a uvar_bs) = exfalso u
fun str_uvar_mt (_ : string list * string list -> 'mtype -> string) (_ : string list * string list) (u : 'mtype uvar_mt) = exfalso u
fun str_uvar_i (_ : string list -> 'idx -> string) (_ : string list) (u : ('bsort, 'idx) uvar_i) = exfalso u
fun eq_uvar_i (u : ('bsort, 'idx) uvar_i, u' : ('bsort, 'idx) uvar_i) = exfalso u

fun shiftx_i_UVarI UVarI _ _ _ (u, _) = exfalso u
fun shiftx_i_UVarS UVarS _ _ _ (u, _) = exfalso u
fun shiftx_i_UVar _ UVar _ _ _ (u, _) = exfalso u
fun shiftx_t_UVar _ UVar _ _ _ (u, _) = exfalso u
                         
fun forget_i_UVarI _ _ UVarI _ _ _ (u, _) = exfalso u
fun forget_i_UVarS _ _ UVarS _ _ _ (u, _) = exfalso u
fun forget_i_UVar _ _ _ UVar _ _ _ (u, _) = exfalso u
fun forget_t_UVar _ _ _ UVar _ _ _ (u, _) = exfalso u
                         
fun substx_i_UVarI _ UVarI _ _ _ (u, _) = exfalso u
fun substx_i_UVarS _ UVarS _ _ _ (u, _) = exfalso u
fun substx_i_UVar _ _ UVar _ _ _ (u, _) = exfalso u
fun substx_t_UVar _ _ UVar _ _ _ (u, _) = exfalso u
                         
end

structure NoUVarExpr = ExprFun (structure Var = IntVar structure UVar = NoUVar)
