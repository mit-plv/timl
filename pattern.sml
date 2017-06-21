structure Pattern = struct

open Namespaces
open Binders
open Unbound
open Region
       
datatype ('var, 'mtype) ptrn =
	 ConstrP of ('var * bool(*eia*)) outer * iname binder list * ('var, 'mtype) ptrn * region outer (* eia : is explicit index arguments? *)                                         
         | VarP of ename binder
         | PairP of ('var, 'mtype) ptrn * ('var, 'mtype) ptrn
         | TTP of region outer
         | AliasP of ename binder * ('var, 'mtype) ptrn * region outer
         | AnnoP of ('var, 'mtype) ptrn * 'mtype outer

end
