structure Pattern = struct

datatype ('var, 'mtype, 'name, 'region) ptrn =
	 ConstrP of ('var * bool(*eia*)) * string list * ('var, 'mtype, 'name, 'region) ptrn * 'region (* eia : is explicit index arguments? *)                                         
         | VarP of 'name
         | PairP of ('var, 'mtype, 'name, 'region) ptrn * ('var, 'mtype, 'name, 'region) ptrn
         | TTP of 'region
         | AliasP of 'name * ('var, 'mtype, 'name, 'region) ptrn * 'region
         | AnnoP of ('var, 'mtype, 'name, 'region) ptrn * 'mtype

end
