structure LongIdSubst = struct

open ShiftUtil
open LongId
       
val shiftx_v = shiftx_int
val forget_v = forget_int
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

fun substx_var a = LongId.substx_long_id substx_v a
                                         
end

