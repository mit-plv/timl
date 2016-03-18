structure Cont = struct

structure M = MLtonCont

fun callcc f = M.callcc f
fun throw k v = M.throw (k, v)
(* val _ = print (callcc (fn k => throw k "hahaha")) *)
              
end
