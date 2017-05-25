functor PatternFn (structure Idx : IDX type var) = struct

open Idx
open Region

datatype 'mtype ptrn =
	 ConstrP of (var * bool(*eia*)) * string list * 'mtype ptrn option * region (* eia : is explicit index arguments? *)                                         
         | VarP of name
         | PairP of 'mtype ptrn * 'mtype ptrn
         | TTP of region
         | AliasP of name * 'mtype ptrn * region
         | AnnoP of 'mtype ptrn * 'mtype

end
