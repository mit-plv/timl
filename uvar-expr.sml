structure UVar = struct
open Util
       
datatype ('a, 'b) uvar = 
         Fresh of 'a
         | Refined of 'b

type uvar_name = int

type ('a, 'b) uvar_ref = (('a, 'b) uvar) ref
                             
(* uvar for bsort *)                  
type 'bsort uvar_bs = (uvar_name, 'bsort) uvar_ref

(* uvar for index *)                  
type ('bsort, 'idx) uvar_i = (uvar_name * (string * 'bsort) list(*context*) * 'bsort(*result*), 'idx) uvar_ref

(* uvar for sort *)                  
type 'sort uvar_s = (uvar_name * (string * 'sort) list(*context*), 'sort) uvar_ref

(* uvar for (mono-)type *)                  
type ('sort, 'mtype) uvar_mt = (uvar_name * (string * 'sort) list(*index context*) * string list(*type context*), 'mtype) uvar_ref

fun refine (x : ('a, 'b) uvar_ref) (v : 'b) = 
  case !x of
      Refined _ => raise Impossible "refine(): should only refine Fresh uvar"
    | Fresh _ =>
      x := Refined v

fun str_uvar n = "?" ^ str_int n

fun str_uinfo_bs n = str_uvar n
fun str_uinfo_i (n, ctx, _) = str_uvar n
fun str_uinfo_s (n, ctx) = str_uvar n
fun str_uinfo_mt (n, sctx, kctx) = str_uvar n
                                         
(* fun str_uinfo_i (n, ctx, _) = sprintf "($ $)" [str_uvar n, str_ls id (rev ctx)] *)
                                         
fun str_uvar_bs str_bs (u : 'bsort uvar_bs) =
  case !u of
      Refined bs => str_bs bs
    | Fresh info => str_uinfo_bs info
                                 
fun str_uvar_i str_i (u : ('bsort, 'idx) uvar_i) =
  case !u of
      Refined i => str_i i
    | Fresh info => str_uinfo_i info

fun str_uvar_s str_s (u : 'sort uvar_s) =
  case !u of
      Refined s => str_s s
    | Fresh info => str_uinfo_s info

fun str_uvar_mt str_mt (u : ('sort, 'mtype) uvar_mt) =
  case !u of
      Refined t => str_mt t
    | Fresh info => str_uinfo_mt info
                            
fun eq_uvar_bs (u : 'bsort uvar_bs, u' : 'bsort uvar_bs) = u = u'
fun eq_uvar_i (u : ('bsort, 'idx) uvar_i, u' : ('bsort, 'idx) uvar_i) = u = u'
                                                                                        
end
                       
structure Expr = ExprFun (structure Var = IntVar structure UVar = UVar)
