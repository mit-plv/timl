structure Util = struct

infixr 0 $
fun f $ x = f x

fun interleave xs ys =
    case xs of
	x :: xs' => x :: interleave ys xs'
      | nil => ys
fun skip start len ls = List.take (ls, start) @ List.drop (ls, start + len)

fun sprintf s ls =
    String.concat (interleave (String.fields (fn c => c = #"$") s) ls)
fun println s = print (s ^ "\n")

fun default v opt = getOpt (opt, v)
fun lazy_default v opt = 
    case opt of
        SOME a => a
      | NONE => v ()
fun isNull opt = not (isSome opt)

val join = String.concatWith
fun prefix fix s = fix ^ s
fun suffix fix s = s ^ fix
fun surround pre post s = pre ^ s ^ post
fun indent msg = map (fn s => "  " ^ s) msg
fun join_lines ls = (join "" o map (suffix "\n")) ls
fun join_prefix pre ls = (join "" o map (prefix pre)) ls
                                                                
fun str_ls f ls = (surround "[" "]" o join ", " o map f) ls
fun str_pair (f, g) (a, b) = sprintf "($, $)" [f a, g b]
fun str_opt f opt = (default "" o Option.map f) opt
val str_int = Int.toString
fun str_bool b = if b then "true" else "false"

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
fun swap f (a, b) = f (b, a)
fun upd4 f (a, b, c, d) = (a, b, c, f d)

datatype ('a, 'b) result =
	 OK of 'a
	 | Failed of 'b

val zip = ListPair.zip
val unzip = ListPair.unzip

fun allSome f xs =
  case xs of
      [] => OK []
    | x :: xs =>
      (case f x of
           SOME x =>
           (case allSome f xs of
                OK xs => OK (x :: xs)
              | Failed i => Failed (i + 1)
           )
         | NONE => Failed 0
      )

fun to_hd i l = List.nth (l, i) :: List.take (l, i) @ List.drop (l, i + 1)

exception Impossible of string
                
fun mem eq x ls = List.exists (fn y => eq (y, x)) ls
fun subset eq a b =
  List.all (fn x => mem eq x b) a
fun diff eq a b = List.filter (fn x => not (mem eq x b)) a
fun dedup eq xs =
    case xs of
        [] => []
      | x :: xs => x :: dedup eq (diff eq xs [x])

fun foldl' f init xs =
    case xs of
        [] => init
      | x :: xs => foldl f x xs

fun max a b = if a < b then b else a

fun write_file (filename, s) =
    let
        val out =  TextIO.openOut filename
        val () = TextIO.output (out, s)
        val () = TextIO.closeOut out
    in
        ()
    end

fun read_file filename =
    let
        val ins = TextIO.openIn filename
        val s = TextIO.input ins
        val _ = TextIO.closeIn ins
    in
        s
    end
                       
fun concatMap f ls = (List.concat o map f) ls

fun inc r = r := !r + 1
fun dec r = r := !r - 1

structure Range = struct

type range = int * int

fun zero_to length = (0, length)

fun foldl f init (start, len) =
    if len <= 0 then
        init
    else
        foldl f (f (start, init)) (start + 1, len - 1)

fun for f init range = foldl f init range

fun app f range = foldl (fn (i, ()) => (f i; ())) () range

end

fun repeat_app f n = Range.app (fn _ => f ()) (Range.zero_to n)

(* uninhabited *)
datatype empty = Empty of empty
fun exfalso (x : empty) = raise Impossible "type empty shouldn't have inhabitant"

fun push xs x = x :: xs
fun binop_ref f r x = r := f (!r) x
fun push_ref r x = binop_ref push r x

datatype ('a, 'b) sum = 
         inl of 'a
         | inr of 'b

end
