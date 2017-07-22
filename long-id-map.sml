structure LongIdMap = struct
open Util
open Expr
       
fun compare_option cmp (a, a') =
  case a of
      NONE =>
      (case a' of
           NONE => EQUAL
         | SOME _ => LESS
      )
    | SOME a =>
      (case a' of
           NONE => GREATER
         | SOME a' => cmp (a, a')
      )

fun compare_pair (cmp1, cmp2) ((a, b), (a', b')) =
  case cmp1 (a, a') of
      EQUAL => cmp2 (b, b')
    | ret => ret
      

fun compare_int (n, n') =
  if n < n' then LESS
  else if n = n' then EQUAL
  else GREATER
         
fun compare_id (x, x') = compare_int (fst x, fst x')
                                     
fun compare_name (x, x') = String.compare (fst x, fst x')
                                     
structure LongIdOrdKey = struct
type ord_key = long_id
fun compare (a : long_id, a' : long_id) =
  let
    fun to_pair id =
      case id of
          ID x => (NONE, x)
        | QID (m, x) => (SOME m, x)
  in
    compare_pair (compare_option compare_name, compare_id) (to_pair a, to_pair a')
  end
end

structure LongIdBinaryMap = BinaryMapFn (LongIdOrdKey)

end
