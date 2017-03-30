structure Util =
struct
infixr 0 $
fun f $ x = f x

exception Impossible of string

fun max a b = if a < b then b else a

fun inc r = r := !r + 1
fun dec r = r := !r - 1

val str_int = Int.toString

fun fst (a, b) = a
fun snd (a, b) = b

fun interleave xs ys =
  case xs of
      x :: xs' => x :: interleave ys xs'
    | nil => ys

fun println s = print (s ^ "\n")
fun sprintf s ls = String.concat (interleave (String.fields (fn c => c = #"$") s) ls)

val join = String.concatWith
fun prefix fix s = fix ^ s
fun suffix fix s = s ^ fix
fun indent msg = map (fn s => "  " ^ s) msg
fun join_lines ls = (join "" o map (suffix "\n")) ls

fun mapi f ls =
  let
      fun inner i ls =
        case ls of
            [] => []
          | h :: t => f (i, h) :: inner (i + 1) t
  in
      inner 0 ls
  end

fun foldli f x ls =
  let
      fun inner i x ls =
        case ls of
            [] => x
          | h :: t => inner (i + 1) (f (i, h, x)) t
  in
      inner 0 x ls
  end

fun foldri f x ls =
  let
      fun inner i x ls =
        case ls of
            [] => x
          | h :: t => f (i, h, inner (i + 1) x t)
  in
      inner 0 x ls
  end

exception Not_found

fun assoc a l =
  let
      fun inner l =
        case l of
            [] => raise Not_found
          | (k, v) :: l' => if k = a then v else inner l'
  in
      inner l
  end

fun mem_assoc a l =
  let
      fun inner l =
        case l of
            [] => false
          | (k, _) :: l' => k = a orelse inner l'
  in
      inner l
  end

fun add_assoc k v l = (k, v) :: l

fun subseteq_assoc l1 l2 =
  let
      fun inner l1 =
        case l1 of
            [] => true
          | (k, v) :: l1' => mem_assoc k l2 andalso assoc k l2 = v andalso inner l1'
  in
      inner l1
  end

fun eq_assoc l1 l2 = subseteq_assoc l1 l2 andalso subseteq_assoc l2 l1

fun map_assoc f l =
  let
      fun inner l =
        case l of
            [] => []
          | (k, v) :: l' => (k, f v) :: inner l'
  in
      inner l
  end
end
