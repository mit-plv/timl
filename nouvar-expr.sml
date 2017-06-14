structure NoUVar = struct
open Util
       
type 'bsort uvar_bs = empty
type ('bsort, 'idx) uvar_i = empty
type ('bsort, 'sort) uvar_s = empty
type ('sort, 'kind, 'mtype) uvar_mt = empty
fun str_uvar_bs _ (u : 'a uvar_bs) = exfalso u
fun str_uvar_i _ (u : ('bsort, 'idx) uvar_i) = exfalso u
fun str_uvar_s _ (u : ('bsort, 'sort) uvar_s) = exfalso u
fun str_uvar_mt _ (u : ('sort, 'kind, 'mtype) uvar_mt) = exfalso u
fun eq_uvar_bs (u : 'bsort uvar_bs, _) = exfalso u
fun eq_uvar_i (u : ('bsort, 'idx) uvar_i, _) = exfalso u
fun eq_uvar_s (u : ('bsort, 'sort) uvar_s, _) = exfalso u
fun eq_uvar_mt (u : ('sort, 'kind, 'mtype) uvar_mt, _) = exfalso u

end

structure NoUVarExpr = ExprFn (structure Var = IntVar
                               structure UVarI = NoUVar
                               structure UVarT = NoUVar
                               type ptrn_constr_tag = int * int
                              )
