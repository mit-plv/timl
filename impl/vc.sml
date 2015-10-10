structure VC = struct
open Util
open Region
open Type

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
fun uniquefy_names (ctx, ps, p, r) = (uniquefy ctx, ps, p, r)
end

fun str_vc show_region filename (ctx : bscontext, ps, p, r : region) =
    let 
        val ctxn = map #1 ctx
    in
        (if show_region then [str_region "" filename r] else []) @
        map (fn (name, s) => sprintf "$ : $" [name, str_b s]) (rev ctx) @
        map (str_p ctxn) ps @
        ["==============="] @
        [str_p ctxn p]
    end 

end
