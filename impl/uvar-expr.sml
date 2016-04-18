structure UVarUtil = struct
open Util
       
datatype ('a, 'b) uvar = 
         Fresh of 'a
         | Refined of 'b

(* invisible segments *)
type invisibles = (int * int) list

type 'bsort uname_i = int * string list (*ctx*) * 'bsort
type ('bsort, 'idx) uvar_ref_i = (('bsort uname_i, 'idx) uvar) ref
type ('bsort, 'idx) uvar_i = invisibles * ('bsort, 'idx) uvar_ref_i

type uname_bs = int
type 'bsort uvar_bs = ((uname_bs, 'bsort) uvar) ref
                                       
type uname_nonidx = int * string list (*ctx*)
type 't uvar_ref_nonidx = ((uname_nonidx, 't) uvar) ref
                                       
type 'sort uvar_s = invisibles * 'sort uvar_ref_nonidx

type 'mtype uvar_mt = (invisibles (* sortings *) * invisibles (* kindings *)) * 'mtype uvar_ref_nonidx

fun expand shift invis b = 
    (fst o foldl (fn ((off, len), (b, base)) => (shift (base + off) len b, base + off + len)) (b, 0)) invis
fun shrink forget invis b = 
    (fst o foldl (fn ((off, len), (b, base)) => (forget (base + off) len b, base + off)) (b, 0)) invis
fun shrink_ctx invis ctx = shrink skip invis ctx

fun refine (x : (('a, 'b) uvar) ref) (v : 'b) = 
    case !x of
        Refined _ => raise Impossible "refine(): should only refine Fresh uvar"
      | Fresh _ =>
        x := Refined v

fun str_uvar n = "?" ^ str_int n

fun str_uname_i (n, ctx, _) = str_uvar n
fun str_uname_bs n = str_uvar n
fun str_uname_nonidx (n, ctx) = str_uvar n
                                   
fun str_uname_i (n, ctx, _) = sprintf "($ $)" [str_uvar n, str_ls id (rev ctx)]
fun str_uname_bs n = str_uvar n
fun str_uname_nonidx (n, ctx) = sprintf "($ $)" [str_uvar n, str_ls id (rev ctx)]
                                   
fun str_uvar_i str_i ctx ((invis, u) : ('bsort, 'idx) uvar_i) =
    case !u of
        Refined i => str_i (shrink_ctx invis ctx) i
      | Fresh name => str_uname_i name
(* | Fresh name_ref => sprintf "($ $)" [str_uname (!name_ref), str_ls (str_pair (str_int, str_int)) invis] *)

fun str_uvar_bs str_bs (u : 'bsort uvar_bs) =
    case !u of
        Refined bs => str_bs bs
      | Fresh name => str_uname_bs name
                                   
fun str_uvar_mt str_mt (ctx as (sctx, kctx)) ((invis as (invisi, invist), u) : 'mtype uvar_mt) =
    case !u of
        Refined t => str_mt (shrink_ctx invisi sctx, shrink_ctx invist kctx) t
      | Fresh name => str_uname_nonidx name
(* | Fresh name_ref => sprintf "($ $ $)" [str_uname (!name_ref), str_ls (str_pair (str_int, str_int)) invisi, str_ls (str_pair (str_int, str_int)) invist] *)
                                  
fun eq_uvar_i ((_, u) : ('bsort, 'idx) uvar_i, (_, u') : ('bsort, 'idx) uvar_i) = u = u'
                                                                                        
end
                       
structure UVar = struct
open UVarUtil
end

structure Expr = ExprFun (structure Var = IntVar structure UVar = UVar)
