functor SetUtilFn (S : ORD_SET) = struct
open Util
structure Set = S

infixr 0 $

fun to_set ls = S.addList (S.empty, ls)
val to_list = S.listItems
fun member x s = S.member (s, x)
fun dedup ls = to_list $ to_set ls
fun pop s =
  case S.find (const true) s of
      SOME e => SOME (e, S.delete (s, e))
    | NONE => NONE
                       
end
