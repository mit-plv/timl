structure UVarUtil = struct

datatype ('a, 'b) uvar = 
         Fresh of 'a
         | Refined of 'b

datatype uvar_name =
         NonIdx of uvar_name_core
         | Idx of uvar_name_core * bsort
         | BSort of int
         | Gone

     and uvar_name_core = int * anchor ref * int (* order *)
                                                         
     and anchor = (uvar_name ref) list

(* invisible segments *)
type invisibles = (int * int) list
                              
type 't uvar_ref = ((uvar_name ref, 't) uvar) ref

fun refine (x : 't uvar_ref) (v : 't) = 
    case !x of
        Refined _ => raise Impossible "refine(): should only refine Fresh uvar"
      | Fresh name =>
        (name := Gone;
         x := Refined v)

end
        
structure UVar = struct
open UVarUtil
type 'idx uvar_i = invisibles * 'idx uvar_ref
type 'bsort uvar_bs = 'bsort uvar_ref
type 'sort uvar_s = 'sort uvar_ref
type 'mtype uvar_mt = (invisibles (* sortings *) * invisibles (* kindings *)) * 'mtype uvar_ref
end

structure OnlyIdxUVar = struct
open UVarUtil
type 't uvar_i = invisibles * 'idx uvar_ref
type 't uvar_bs = empty
type 't uvar_s = empty
type 't uvar_mt = empty
end

structure Expr = ExprFun (structure Var = IntVar structure UVar = UVar)

