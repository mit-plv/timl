structure Region = struct
open Util

type pos = {abs : int, line : int, col : int}

type region = pos * pos

val dummy_pos : pos = {abs = 0, line = 0, col = 0}
val dummy_region = (dummy_pos, dummy_pos)

(* fun right_col ((left, right) : region) = #col left + #abs right - #abs left - 1 *)

(* default style *)
fun str_region header filename ((left, right) : region) = sprintf "$: $ $.$.\n" [header, filename, str_int (#line left), str_int (#col left)]
(* python style *)
fun str_region header filename (r as (left, right) : region) = sprintf "File $, line $-$, characters $-$:\n" [filename, str_int (#line left), str_int (#line right), str_int (#col left), str_int (#col right)]

fun str_error header filename region msg = sprintf "$  $\n" [str_region header filename region, msg]

fun combine_region (r1 : region) (r2 : region) : region = (#1 r1, #2 r2)
(* fun combine_regions rs =  *)
(*     case rs of *)
(*         [] => dummy_region *)
(*       | r :: rs => foldl (fn (r2, r1) => combine_region r1 r2) r rs *)

end

