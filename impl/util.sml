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
val str_int = Int.toString

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
fun curry f a b = f (a, b)
fun uncurry f (a, b) = f a b

datatype ('a, 'b) result =
	 OK of 'a
	 | Failed of 'b

end
