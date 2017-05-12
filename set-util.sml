structure SetUtil = struct

structure S = IntBinarySet
fun to_set ls = S.addList (S.empty, ls)
fun member x s = S.member (s, x)
        
end
