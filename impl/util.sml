structure Util = struct
fun interleave xs ys =
    case xs of
	x :: xs' => x :: interleave ys xs'
      | nil => ys

fun sprintf s ls =
    String.concat (interleave (String.fields (fn c => c = #"$") s) ls)
fun println s = print (s ^ "\n")

val join = String.concatWith
fun prefix fix s = fix ^ s
fun suffix fix s = s ^ fix
fun surround pre post s = pre ^ s ^ post
fun indent msg = map (fn s => "  " ^ s) msg
val str_int = Int.toString
fun join_lines ls = (join "" o map (suffix "\n")) ls

fun id x = x
fun const a _ = a
fun range n = List.tabulate (n, id)
fun repeat n a = List.tabulate (n, const a)
fun add_idx ls = ListPair.zip (range (length ls), ls)

fun nth_error ls n =
    if n < 0 orelse n >= length ls then
	NONE
    else
	SOME (List.nth (ls, n))

fun fst (a, b) = a
fun snd (a, b) = b
fun mapFst f (a, b) = (f a, b)
fun mapSnd f (a, b) = (a, f b)
fun mapPair (fa, fb) (a, b) = (fa a, fb b)
fun curry f a b = f (a, b)
fun uncurry f (a, b) = f a b
fun upd4 f (a, b, c, d) = (a, b, c, f d)

datatype ('a, 'b) result =
	 OK of 'a
	 | Failed of 'b

val zip = ListPair.zip
val unzip = ListPair.unzip

end
