structure LongId = struct

open Region

type mod_id = string * region
                                  
datatype 'var long_id =
         ID of 'var * region
       | QID of mod_id * ('var * region) (* qualified id *)
                         
fun eq_mod_id ((s, _) : mod_id, (s', _)) = s = s'
  
fun eq_long_id eq_id (a : 'var long_id, a') =
  case (a, a') of
      (ID x, ID x') => eq_id (x, x')
    | (QID (m, x), QID (m', x')) => eq_mod_id (m, m') andalso eq_id (x, x')
    | _ => false

fun str_raw_long_id str_raw_v id =
  case id of
      ID (x, _) => str_raw_v x
    | QID ((m, _), (x, _)) => sprintf "QID ($, $)" [m, str_raw_v x]
                       
(* if it has module reference, don't shift/forget *)
fun on_v_long_id on_v x n (id : 'var long_id) : 'var long_id =
  case id of
      ID (y, r) => ID (on_v x n y, r)
    | QID _ => id
    
(* if it has the module name part, don't substitute, because this is not the variable you are targeting *)
fun substx_long_id substx_v (constr : 'var long_id -> 'a) x (get_v : unit -> 'a) (id : 'var long_id) =
  case id of
      ID (y, r) => substx_v (fn x => constr (ID (x, r))) x get_v y
    | QID _ => constr id

end
