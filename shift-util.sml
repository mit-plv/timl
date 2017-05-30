structure ShiftUtil = struct
open Bind

infixr 0 $
         
fun on_snd f x n (a, b) = (a, f x n b)
fun on_pair (f, g) x n (a, b) = (f x n a, g x n b)
fun on_list f x n b = map (f x n) b
fun on_list_snd f = on_list $ on_snd f

fun on_i_ibind f x n (bind : ('a * 'b) ibind) =
  case bind of
      Bind (name, inner) => Bind (name, f (x + 1) n inner)

fun on_i_tbind f x n (bind : ('a * 'b) tbind) =
  case bind of
      Bind (name, inner) => Bind (name, f x n inner)

fun on_t_ibind f x n (bind : ('a * 'b) ibind) =
  case bind of
      Bind (name, inner) => Bind (name, f x n inner)

fun on_t_tbind f x n (bind : ('a * 'b) tbind) =
  case bind of
      Bind (name, inner) => Bind (name, f (x + 1) n inner)

fun on_binds on_bind on_anno on_inner x n b =
  let
    val on_binds = on_binds on_bind on_anno on_inner
  in
    case b of
        BindNil inner => 
        BindNil (on_inner x n inner)
      | BindCons (anno, bind) =>
        BindCons (on_anno x n anno, on_bind on_binds x n bind)
  end

fun on_i_ibinds on_anno on_inner x n (b : ('a, 'b, 'c) ibinds) =
  on_binds on_i_ibind on_anno on_inner x n b
(* fun on_i_ibinds on_anno on_inner x n (ibinds : ('a, 'b, 'c) ibinds) = *)
(*   case ibinds of *)
(*       BindNil inner =>  *)
(*       BindNil (on_inner x n inner) *)
(*     | BindCons (anno, bind) => *)
(*       BindCons (on_anno x n anno, on_i_ibind (on_i_ibinds on_anno on_inner) x n bind) *)

fun on_i_tbinds on_anno on_inner x n (b : ('a, 'b, 'c) tbinds) =
  on_binds on_i_tbind on_anno on_inner x n b
           
fun on_t_ibinds on_anno on_inner x n (b : ('a, 'b, 'c) ibinds) =
  on_binds on_t_ibind on_anno on_inner x n b
(* fun on_t_ibinds on_anno on_inner x n (ibinds : ('a, 'b, 'c) ibinds) = *)
(*   case ibinds of *)
(*       BindNil inner =>  *)
(*       BindNil (on_inner x n inner) *)
(*     | BindCons (anno, bind) => *)
(*       BindCons (on_anno x n anno, on_t_ibind (on_t_ibinds on_anno on_inner) x n bind) *)

fun on_t_tbinds on_anno on_inner x n (b : ('a, 'b, 'c) tbinds) =
  on_binds on_t_tbind on_anno on_inner x n b
  
fun shiftx_int x n y = 
  if y >= x then
    y + n
  else
    y

fun forget_int ForgetError x n y = 
  if y >= x + n then
    y - n
  else if y < x then
    y
  else
    raise ForgetError (y, "")

exception ForgetError of int * string
                                 
end
