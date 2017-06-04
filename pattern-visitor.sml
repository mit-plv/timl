functor PatternVisitorFn (BinderVisitor : BINDER_VISITOR) = struct

open M
open BinderVisitor
open Binders
open Util
open Operators
open Unbound
       
infixr 0 $
infix 0 !!

datatype ('var, 'mtype) ptrn =
	 ConstrP of ('var * bool(*eia*)) outer * tname binder list * ('var, 'mtype) ptrn option rebind * region outer (* eia : is explicit index arguments? *)
         | VarP of ename binder
         | PairP of ('var, 'mtype) ptrn * ('var, 'mtype) ptrn
         | TTP of region outer
         | AliasP of ename binder * ('var, 'mtype) ptrn rebind * region outer
         | AnnoP of ('var, 'mtype) ptrn * 'mtype outer

end
