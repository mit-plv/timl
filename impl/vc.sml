structure NoUVar = struct
type 'a uvar_bs = empty
type ('a, 'b) uvar_s = empty
type ('a, 'b) uvar_mt = empty
type ('a, 'b) uvar_i = int
fun str_uvar_bs (_ : 'a -> string) (u : 'a uvar_bs) = exfalso u
fun str_uvar_mt (_ : string list * string list -> 'mtype -> string) (_ : string list * string list) (u : ('bsort, 'mtype) uvar_mt) = exfalso u
fun evar_name n = "?" ^ str_int n
fun str_uvar_i (_ : string list -> 'idx -> string) (_ : string list) n = evar_name n
end

structure NoUVarExpr = ExprFun (structure Var = IntVar structure UVar = NoUVar)

structure VC = struct
open Util
open Region
open NoUVarExpr

datatype formula =
         ForallF of string * base_sort * formula list
         | ImplyF of prop * formula list
         | PropF of prop * region
         | ExistsF of int * base_sort * formula list

fun str_f ctx f =
    case f of
        ForallF (name, bsort, fs) =>
        sprintf "(forall ($ : $) ($))" [name, str_b bsort, str_fs (name :: ctx) fs]
      | ImplyF (p, fs) =>
        sprintf "($ => ($))" [str_p ctx p, str_fs ctx fs]
      | AnchorF anchor => sprintf "(anchor ($))" [join " " $ map (fn x => str_uname (!x)) (!anchor)]
      | PropF (p, _) => str_p ctx p
      | ExistsF (name, bsort, fs) =>
        sprintf "(exists ($ : $) ($))" [name, str_b bsort, str_fs ctx fs]

and str_fs ctx fs = join " " $ map (str_f ctx) fs

fun collect (pairs, ps) : bscontext * prop list = 
    let fun get_p s n ps =
	    case s of
	        Basic _ => ps
	      | Subset (_, _, p) => shiftx_i_p 0 n p :: ps
        val bctx = map (mapSnd get_base) pairs
        val (ps', _) = foldl (fn ((name, s), (ps, n)) => (get_p s n ps, n + 1)) ([], 0) pairs
    in
        (bctx, ps @ ps')
    end

type bscontext = (string * bsort) list

type vc = bscontext * prop list * prop * region

local
    fun find_unique name ls =
        if not (mem op= name ls) then
	    name
        else
	    let fun loop n =
		    let val name' = name ^ str_int n in
		        if not (mem op= name' ls) then name' else loop (n + 1)
		    end in
	        loop 0
	    end
in
fun unique names = foldr (fn (name, acc) => find_unique name acc :: acc) [] names
fun uniquefy ctx = ListPair.zip (mapFst unique (ListPair.unzip ctx))
fun uniquefy_names ((ctx, ps, p, r) : vc) = (uniquefy ctx, ps, p, r)
end

fun str_vc show_region filename (ctx : bscontext, ps, p, r : region) =
    let 
        val ctxn = map #1 ctx
    in
        (if show_region then [str_region "" filename r] else []) @
        map (fn (name, s) => sprintf "$ : $" [name, str_bs s]) (rev ctx) @
        map (str_p ctxn) ps @
        ["==============="] @
        [str_p ctxn p]
    end 

end
