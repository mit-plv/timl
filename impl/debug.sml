structure Debug = struct

local

    val debug = false
    (* val debug = true *)

in

val print = fn s => if debug then print s else ()

fun println s = if debug then print (s ^ "\n") else ()

end

end
