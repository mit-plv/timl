signature PATTERN = sig

datatype ('var, 'mtype) ptrn =
	 ConstrP of ('var * bool(*eia*)) Unbound.outer * Namespaces.iname Unbound.binder list * ('var, 'mtype) ptrn * Region.region Unbound.outer (* eia : is explicit index arguments? *)                                         
         | VarP of Namespaces.ename Unbound.binder
         | PairP of ('var, 'mtype) ptrn * ('var, 'mtype) ptrn
         | TTP of Region.region Unbound.outer
         | AliasP of Namespaces.ename Unbound.binder * ('var, 'mtype) ptrn * Region.region Unbound.outer
         | AnnoP of ('var, 'mtype) ptrn * 'mtype Unbound.outer

end
