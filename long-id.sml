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
                       
end
