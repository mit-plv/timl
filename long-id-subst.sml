structure LongIdSubst = struct

open LongId
open ShiftUtil
       
val shiftx_v = shiftx_int
val forget_v = forget_int
                 
(* if it has module reference, don't shift/forget *)
fun on_v_long_id on_v x n (id : 'var long_id) : 'var long_id =
  case id of
      ID (y, r) => ID (on_v x n y, r)
    | QID _ => id
    
fun shiftx_long_id x n b = on_v_long_id shiftx_v x n b
val forget_v = forget_v ForgetError
fun forget_long_id x n b = on_v_long_id forget_v x n b
                                        
type var = int long_id
val shiftx_var = shiftx_long_id
val forget_var = forget_long_id
                   
fun substx_v Var x v y =
  if y = x then
    v ()
  else if y > x then
    Var (y - 1)
  else
    Var y

(* if it has the module name part, don't substitute, because this is not the variable you are targeting *)
fun substx_long_id substx_v (constr : 'var long_id -> 'a) x (get_v : unit -> 'a) (id : 'var long_id) =
  case id of
      ID (y, r) => substx_v (fn x => constr (ID (x, r))) x get_v y
    | QID _ => constr id

fun substx_var a = substx_long_id substx_v a
                                         
end

