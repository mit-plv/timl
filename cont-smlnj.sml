structure Cont = struct

structure M = SMLofNJ.Cont

fun callcc f = M.callcc f
fun throw k v = M.throw k v

end
