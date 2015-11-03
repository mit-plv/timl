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
                              
fun expand shift invis b = 
    (fst o foldl (fn ((off, len), (b, base)) => (shift (base + off) len b, base + off + len)) (b, 0)) invis
fun shrink forget invis b = 
    (fst o foldl (fn ((off, len), (b, base)) => (forget (base + off) len b, base + off)) (b, 0)) invis
fun shrink_ctx invis ctx = shrink skip invis ctx

type ('bsort, 't) uvar_ref = ((('bsort uvar_name) ref, 't) uvar) ref

fun refine (x : ('bsort, 't) uvar_ref) (v : 't) = 
    case !x of
        Refined _ => raise Impossible "refine(): should only refine Fresh uvar"
      | Fresh name =>
        (name := Gone;
         x := Refined v)

type ('bsort, 'idx) uvar_i = invisibles * ('bsort, 'idx) uvar_ref
fun str_uvar_i str_i ctx ((invis, u) : ('bsort, 'idx) uvar_i) =
    case !u of
        Refined i => str_i (shrink_ctx invis ctx) i
      | Fresh name_ref => 
        case !name_ref of
            Idx (n, _, _, _) => "?" ^ str_int n
          | _ => raise Impossible "str_uvar_i (): name should be Idx"

end
        
structure UVar = struct
open UVarUtil
type 'bsort uvar_bs = ('bsort, 'bsort) uvar_ref
type ('bsort, 'sort) uvar_s = invisibles * ('bsort, 'sort) uvar_ref
type ('bsort, 'mtype) uvar_mt = (invisibles (* sortings *) * invisibles (* kindings *)) * ('bsort, 'mtype) uvar_ref
fun str_uvar_bs str_bs (u : 'bsort uvar_bs) =
    case !u of
        Refined bs => str_bs bs
      | Fresh name_ref => 
        case !name_ref of
            BSort n => "?" ^ str_int n
          | _ => raise Impossible "str_uvar_bs (): name should be BSort"
end

structure OnlyIdxUVar = struct
open UVarUtil
type 'a uvar_bs = empty
type ('a, 'b) uvar_s = empty
type ('a, 'b) uvar_mt = empty
fun str_uvar_bs (_ : 'a -> string) (u : 'a uvar_bs) = exfalso u
end

structure Expr = ExprFun (structure Var = IntVar structure UVar = UVar)
structure OnlyIdxUVarExpr = ExprFun (structure Var = IntVar structure UVar = OnlyIdxUVar)

