functor ListPairMapFn (K : sig eqtype t end) = struct
open Util
infixr 0 $

structure Key = K
                  
type key = K.t
type 'a map = (key * 'a) list
fun find (m : 'a map, k) = Option.map snd $ List.find (fn (k', v) => k' = k) m
fun insert' (kv, m : 'a map) = kv :: m
val listItemsi = id
end
                          
structure StringListPairMap = ListPairMapFn (struct type t = string end)
