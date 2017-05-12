functor MapUtilFn (M : ORD_MAP) = struct

fun restrict ks m = foldl (fn (k, acc) =>
                              case M.find (m, k) of
                                  SOME v => M.insert (acc, k, v)
                                | NONE => acc
                          ) M.empty (Util.dedup (Util.isEqual o M.Key.compare) ks)

fun str_map (fk, fv) = Util.surround "{" "}" o Util.join ", " o List.map (fn (k, v) => Util.sprintf "$ => $" [fk k, fv v]) o M.listItemsi
  
fun domain m = List.map Util.fst (M.listItemsi m)

fun addList (m, kvs) = foldl (fn ((k, v), m) => M.insert (m, k, v)) m kvs

fun to_map kvs = addList (M.empty, kvs)
                        
end
