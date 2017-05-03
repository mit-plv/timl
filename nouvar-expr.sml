structure NoUVar = struct
open Util
       
type 'bsort uvar_bs = empty
type ('bsort, 'idx) uvar_i = empty
type 'sort uvar_s = empty
type ('sort, 'kind, 'mtype) uvar_mt = empty
fun str_uvar_bs (_ : 'a -> string) (u : 'a uvar_bs) = exfalso u
fun str_uvar_i (_ : 'bsort -> string) (_ : 'idx -> string) (u : ('bsort, 'idx) uvar_i) = exfalso u
fun str_uvar_s (_ : 'sort -> string) (u : 'sort uvar_s) = exfalso u
fun str_uvar_mt (_ : 'mtype -> string) (u : ('sort, 'kind, 'mtype) uvar_mt) = exfalso u
fun eq_uvar_bs (u : 'bsort uvar_bs, u' : 'bsort uvar_bs) = exfalso u
fun eq_uvar_i (u : ('bsort, 'idx) uvar_i, u' : ('bsort, 'idx) uvar_i) = exfalso u

end

structure NoUVarExpr = ExprFun (structure Var = IntVar structure UVar = NoUVar)
