structure Region = struct
open Util

infixr 0 $

type pos = {abs : int, line : int, col : int}

type region = pos * pos

val dummy_pos : pos = {abs = 0, line = 0, col = 0}
val dummy_region = (dummy_pos, dummy_pos)
val dummy = dummy_region

(* default style *)
fun str_region header filename ((left, right) : region) = sprintf "$: $ $.$.\n" [header, filename, str_int (#line left), str_int (#col left)]
(* python style *)
fun str_region header filename (r as (left, right) : region) = sprintf "File $, line $-$, characters $-$:" [filename, str_int (#line left), str_int (#line right), str_int (#col left), str_int (max (#col right) 0)]

fun str_error header filename region msg = join_lines $ str_region header filename region :: indent msg

fun combine_region (r1 : region) (r2 : region) : region = (#1 r1, #2 r2)

end

