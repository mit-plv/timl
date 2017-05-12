(* a map that enforces freshness when adding elements *)

signature UNIQUE_ORD_MAP = sig
  include ORD_MAP
  exception KeyAlreadyExists of Key.ord_key * Key.ord_key list
  val union : 'a map * 'a map -> 'a map
end

functor UniqueMapFn (M : ORD_MAP) : UNIQUE_ORD_MAP = struct
open Util
open M
structure MapUtil = MapUtilFn (M)
                              
infixr 0 $
         
exception KeyAlreadyExists of M.Key.ord_key * M.Key.ord_key list

fun check_fresh (ks, m) =
  List.app (fn k => if isNone $ M.find (m, k) then ()
                    else raise KeyAlreadyExists (k, MapUtil.domain m)
           ) ks
    
fun insert (args as (m, k, v)) =
  let
    val () = check_fresh ([k], m)
  in
    M.insert args
  end
    
fun insert' (args as ((k, v), m)) =
  let
    val () = check_fresh ([k], m)
  in
    M.insert' args
  end

fun unionWith f (m, m') =
  let
    val () = check_fresh (MapUtil.domain m', m)
  in
    M.unionWith f (m, m')
  end
    
fun unionWithi f (m, m') =
  let
    val () = check_fresh (MapUtil.domain m', m)
  in
    M.unionWithi f (m, m')
  end

fun union (m, m') = unionWith (fn _ => raise Impossible "Gctx.union(): shouldn't overlap") (m, m')
                              
end
