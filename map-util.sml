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

fun foldli' f = M.foldli (fn (k, v, acc) => f ((k, v), acc))

fun delete (m, k) = Util.fst (M.remove (m, k)) handle NotFound => m
                        
fun enumerate c : ((M.Key.ord_key * 'value), 'result) Enum.enum = fn f => (fn init => foldli' f init c)
                                     
fun remove_many (m : 'a M.map) (ks : (M.Key.ord_key, 'a M.map) Enum.enum) : 'a M.map = ks (fn (k, m) => delete (m, k)) m

fun find_many g ks = List.mapPartial (fn k => Option.map (Util.attach_fst k) (M.find (g, k))) ks
                                         
end
