structure TimeType = struct

(* type time = string *)
(* val zero = "0.0" *)
(* val one = "1.0" *)
       
open Real
       
type time = real
val zero = fromInt 0
val one = fromInt 1

fun str_time x = toString x
                   
val time_eq = op== 

end
