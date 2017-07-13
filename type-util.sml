structure TypeUtil = struct

local
  open Unbound
  open Namespaces
in
fun from_Unbound (Binder (TypeNS, name), Rebind (Outer t)) = (name, t)
fun to_Unbound (name, t) = (Binder (TypeNS, name), Rebind (Outer t))
end
                                                       
end
                       
