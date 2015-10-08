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
end

fun str_vc filename (ctx : bscontext, ps, p, r : region) =
    let 
        val ctx = uniquefy ctx
        val ctxn = map #1 ctx in
        sprintf "$$$===============\n$\n" 
	        [str_region "" filename r,
                 join "" (map (fn (name, s) => sprintf "$ : $\n" [name, str_b s]) (rev ctx)), 
	         join "" (map (fn p => str_p ctxn p ^ "\n") ps), 
	         str_p ctxn p
                (* , *)
                (*                  sprintf "(from $.$-$.$)" [str_int (#line (fst r)), str_int (#col (fst r)), str_int (#line (snd r)), str_int (#col (snd r))] *)
                ]
    end 

end
