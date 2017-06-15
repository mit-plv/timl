structure Pattern = struct

open Namespaces
open Binders
open Unbound
       
datatype ('var, 'mtype, 'region) ptrn =
	 ConstrP of ('var * bool(*eia*)) outer * iname binder list * ('var, 'mtype, 'region) ptrn * 'region outer (* eia : is explicit index arguments? *)                                         
         | VarP of ename binder
         | PairP of ('var, 'mtype, 'region) ptrn * ('var, 'mtype, 'region) ptrn
         | TTP of 'region outer
         | AliasP of ename binder * ('var, 'mtype, 'region) ptrn * 'region outer
         | AnnoP of ('var, 'mtype, 'region) ptrn * 'mtype outer

end
