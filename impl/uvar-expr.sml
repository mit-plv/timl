structure UVarUtil = struct
open Util
         
datatype ('a, 'b) uvar = 
         Fresh of 'a
         | Refined of 'b

datatype 'bsort uvar_name =
         NonIdx of int * ((('bsort uvar_name) ref) list) ref * int (* order *)
         | Idx of int * ((('bsort uvar_name) ref) list) ref * int (* order *) * 'bsort
         | BSort of int
         | Gone

type 'bsort anchor = (('bsort uvar_name) ref) list

(* invisible segments *)
type invisibles = (int * int) list
                              
type ('bsort, 't) uvar_ref = ((('bsort uvar_name) ref, 't) uvar) ref

fun refine (x : ('bsort, 't) uvar_ref) (v : 't) = 
    case !x of
        Refined _ => raise Impossible "refine(): should only refine Fresh uvar"
      | Fresh name =>
        (name := Gone;
         x := Refined v)

end
        
structure UVar = struct
open UVarUtil
type 'bsort uvar_bs = ('bsort, 'bsort) uvar_ref
type ('bsort, 'idx) uvar_i = invisibles * ('bsort, 'idx) uvar_ref
type ('bsort, 'sort) uvar_s = invisibles * ('bsort, 'sort) uvar_ref
type ('bsort, 'mtype) uvar_mt = (invisibles (* sortings *) * invisibles (* kindings *)) * ('bsort, 'mtype) uvar_ref
end

structure OnlyIdxUVar = struct
open UVarUtil
type ('bsort, 'idx) uvar_i = invisibles * ('bsort, 'idx) uvar_ref
type 't uvar_bs = empty
type 't uvar_s = empty
type 't uvar_mt = empty
end

structure Expr = ExprFun (structure Var = IntVar structure UVar = UVar)

