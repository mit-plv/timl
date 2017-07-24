structure IntVar = struct
open Util
open LongId
open ShiftUtil
open Gctx
type var = int
type name_context = string list * string list * string list * string list
type global_name_context = name_context Gctx.map
                                        
fun str_v ctx x : string =
  (* sprintf "%$" [str_int x] *)
  case nth_error ctx x of
      SOME name => name
    | NONE => "unbound_" ^ str_int x
                                   
fun str_raw_v x = str_int x
                    
fun str_id ctx (x, _) =
  str_v ctx x
        
fun lookup_module gctx m =
  case nth_error2 gctx m of
      SOME (name, ctx) => (name, ctx)
    | NONE => ("unbound_module_" ^ m, ([], [], [], []))
                
fun str_long_id sel gctx ctx id =
  case id of
      QID ((m, _), x) =>
      let
        val (name, ctx) = lookup_module gctx m
        val ctx = sel ctx
      in
        name ^ "." ^ str_id ctx x
      end
    | ID x => str_id ctx x
    
fun eq_v (x : var, y) = x = y

val shiftx_v = shiftx_int
val forget_v = forget_int
                 
fun substx_v Var x v y =
  if y = x then
    v ()
  else if y > x then
    Var (y - 1)
  else
    Var y

end
