structure NoUVar = struct
open Util
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
open NoUVar
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
      | PropF (p, _) => str_p ctx p
      | ExistsF (name, bsort, fs) =>
        sprintf "(exists ($ : $) ($))" [evar_name name, str_b bsort, str_fs ctx fs]

and str_fs ctx fs = (join " " o map (str_f ctx)) fs

local
    fun find_unique ls name =
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
fun uniquefy_ls names = foldr (fn (name, acc) => find_unique acc name :: acc) [] names
fun uniquefy ctx f =
    case f of
        ForallF (name, bs, fs) =>
        let
            val name = find_unique ctx name
        in
            ForallF (name, bs, map (uniquefy (name :: ctx)) fs)
        end
      | ImplyF (p, fs) => ImplyF (p, map (uniquefy ctx) fs)
      | PropF p => PropF p
      | ExistsF (n, bs, fs) => ExistsF (n, bs, map (uniquefy ctx) fs)
end

(* fun collect (pairs, ps) : bscontext * prop list =  *)
(*     let fun get_p s n ps = *)
(* 	    case s of *)
(* 	        Basic _ => ps *)
(* 	      | Subset (_, _, p) => shiftx_i_p 0 n p :: ps *)
(*         val bctx = map (mapSnd get_base) pairs *)
(*         val (ps', _) = foldl (fn ((name, s), (ps, n)) => (get_p s n ps, n + 1)) ([], 0) pairs *)
(*     in *)
(*         (bctx, ps @ ps') *)
(*     end *)

datatype hyp = 
         VarH of string * base_sort
       | PropH of  prop 

type vc = hyp list * formula

fun split_formula f =
    let
        fun add_hyp h vc = mapFst (fn hyps => h :: hyps) vc
    in
        case f of
            ForallF (name, bs, fs) =>
            let
                val vcs = split_formulas fs
                val vcs = map (add_hyp (VarH (name, bs))) vcs
            in
                vcs
            end
          | ImplyF (p, fs) =>
            let
                val vcs = split_formulas fs
                val vcs = map (add_hyp (PropH p)) vcs
            in
                vcs
            end
          | _ => [([], f)]
    end

and split_formulas fs = concatMap split_formula fs

fun str_vc show_region filename ((hyps, f) : vc) =
    let 
        val region = if show_region then 
                         case f of
                             PropF (_, r) =>
                             [str_region "" filename r] 
                           | _ => []
                     else []
        fun g (h, (hyps, ctx)) =
            case h of
                VarH (name, bs) => (sprintf "$ : $" [name, str_b bs] :: hyps, name :: ctx)
              | PropH p => (str_p ctx p :: hyps, ctx)
        val (hyps, ctx) = foldl g ([], []) hyps
        val hyps = rev hyps
        val f = str_f ctx f
    in
        region @
        hyps @
        ["==============="] @
        [f]
    end 

end
