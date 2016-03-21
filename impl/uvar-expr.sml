structure UVarUtil = struct
open Util
         
datatype ('a, 'b) uvar = 
         Fresh of 'a
         | Refined of 'b

datatype 'bsort uvar_name =
         NonIdx of 'bsort uvar_name_core
         | Idx of 'bsort uvar_name_core * 'bsort
         | BSort of int

(* order: when we convert leftover fresh idx variables to existentially quantified variables, because the quantification point is the variable's [anchor], which is not necessarily the point where the fresh variable was first introduced, there could be an implicit Skolemization involved. [order] indicates the degree of Skolemization. For example, if [order = 1], this fresh idx variable should (in principle) be converted into an existentially quantified variable of type [idx -> idx], not just [idx]. Considering the capability of the solver used to find this existential variable, we might choose to let its type be just [idx], which corresponds to giving up the flexibility of changing the existential variable's value according to some variables introduced after it. 
An invariant: length ctx = order
 *)

(*                        
(* only works with SML/NJ *)                        
withtype 'bsort anchor = ((('bsort uvar_name) option) ref) list
and 'bsort uvar_name_core = int * ('bsort anchor) ref * int (*order*) * string list (*ctx*)
*)

(* works with both SML/NJ and MLton *)                        
withtype 'bsort uvar_name_core = int * (((('bsort uvar_name) option) ref) list) ref * int (*order*) * string list (*ctx*)
type 'bsort anchor = ((('bsort uvar_name) option) ref) list

(* invisible segments *)
type invisibles = (int * int) list
                              
fun expand shift invis b = 
    (fst o foldl (fn ((off, len), (b, base)) => (shift (base + off) len b, base + off + len)) (b, 0)) invis
fun shrink forget invis b = 
    (fst o foldl (fn ((off, len), (b, base)) => (forget (base + off) len b, base + off)) (b, 0)) invis
fun shrink_ctx invis ctx = shrink skip invis ctx

type ('bsort, 't) uvar_ref = (((('bsort uvar_name) option) ref, 't) uvar) ref

fun refine (x : ('bsort, 't) uvar_ref) (v : 't) = 
    case !x of
        Refined _ => raise Impossible "refine(): should only refine Fresh uvar"
      | Fresh name =>
        (name := NONE;
         x := Refined v)

fun str_uvar n = "?" ^ str_int n
fun str_uname uname =
  case uname of
      NONE => "NONE_uname"
    | SOME uname =>
      (* case uname of *)
      (*     Idx ((n, _, _, _), _) => str_uvar n *)
      (*   | NonIdx (n, _, _, _) => str_uvar n *)
      (*   | BSort n => str_uvar n *)
      case uname of
          Idx ((n, _, order, ctx), _) => sprintf "($ $ $)" [str_uvar n, str_ls id (rev ctx), str_int order]
        | NonIdx (n, _, order, ctx) =>
          if n < 0 then
            hd ctx
          else
            sprintf "($ $ $)" [str_uvar n, str_ls id (rev ctx), str_int order]
        | BSort n => str_uvar n

type ('bsort, 'idx) uvar_i = invisibles * ('bsort, 'idx) uvar_ref
fun str_uvar_i str_i ctx ((invis, u) : ('bsort, 'idx) uvar_i) =
    case !u of
        Refined i => str_i (shrink_ctx invis ctx) i
      | Fresh name_ref => sprintf "$" [str_uname (!name_ref)]
      (* | Fresh name_ref => sprintf "($ $)" [str_uname (!name_ref), str_ls (str_pair (str_int, str_int)) invis] *)

end
        
structure UVar = struct
open UVarUtil
type 'bsort uvar_bs = ('bsort, 'bsort) uvar_ref
type ('bsort, 'sort) uvar_s = invisibles * ('bsort, 'sort) uvar_ref
type ('bsort, 'mtype) uvar_mt = (invisibles (* sortings *) * invisibles (* kindings *)) * ('bsort, 'mtype) uvar_ref
fun str_uvar_bs str_bs (u : 'bsort uvar_bs) =
    case !u of
        Refined bs => str_bs bs
      | Fresh name_ref => str_uname (!name_ref)
fun str_uvar_mt str_mt (ctx as (sctx, kctx)) ((invis as (invisi, invist), u) : ('bsort, 'mtype) uvar_mt) =
    case !u of
        Refined t => str_mt (shrink_ctx invisi sctx, shrink_ctx invist kctx) t
      | Fresh name_ref => sprintf "$" [str_uname (!name_ref)]
      (* | Fresh name_ref => sprintf "($ $ $)" [str_uname (!name_ref), str_ls (str_pair (str_int, str_int)) invisi, str_ls (str_pair (str_int, str_int)) invist] *)
fun eq_uvar_i ((_, u) : ('bsort, 'idx) uvar_i, (_, u') : ('bsort, 'idx) uvar_i) = u = u'
end

structure Expr = ExprFun (structure Var = IntVar structure UVar = UVar)
