functor MicroTiMLVisitor (M : MICRO_TIML) = struct

open Util
       
infixr 0 $
         
type ('this, 'a, 'b, 'a2, 'b2, 'env) expr_visitor_vtable =
     {
       visit_expr : 'this -> 'env -> ('a, 'b) expr -> ('a2, 'b2) expr,
       visit_EConst : 'this -> 'env -> 'a -> ('a2, 'b2) expr,
       visit_EAdd : 'this -> 'env -> 'b * ('a, 'b) expr * ('a, 'b) expr -> ('a2, 'b2) expr,
       visit_'a : 'this -> 'env -> 'a -> 'a2,
       visit_'b : 'this -> 'env -> 'b -> 'b2
     }
       
end
