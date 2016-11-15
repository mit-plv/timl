structure Util =
struct
infixr 0 $
fun f $ x = f x

exception Impossible of string

val str_int = Int.toString

fun fst (a, b) = a
fun snd (a, b) = b

fun println s = print (s ^ "\n")

fun prefix fix s = fix ^ s
fun suffix fix s = s ^ fix

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
end
