structure Visitor = struct

open Util
       
infixr 0 $
         
datatype ('a, 'b) expr =
         EConst of 'a
         | EAdd of 'b * ('a, 'b) expr * ('a, 'b) expr

(* using record types and recursive types (datatypes) to mimic object-oriented programming (dynamic dispatching and inheritance) *)

(* This is the expression visitor interface. An interface is a (self-referencing) record where the carrier type ['this] is unknown but we know it has the desired methods. *)
(* Only interfaces can be inherited, overrode and extended. *)
(* [is_sub] is a coercion to mimic subtyping or subclassing *)
datatype ('this, 'a, 'b, 'a2, 'b2, 'env) expr_visitor_interface =
         ExprVisitorInterface of
         {
           is_sub : 'this -> ('this, 'a, 'b, 'a2, 'b2, 'env) expr_visitor_interface,
           visit_expr : 'this -> 'env -> ('a, 'b) expr -> ('a2, 'b2) expr,
           visit_EConst : 'this -> 'env -> 'a -> ('a2, 'b2) expr,
           visit_EAdd : 'this -> 'env -> 'b * ('a, 'b) expr * ('a, 'b) expr -> ('a2, 'b2) expr,
           visit_'a : 'this -> 'env -> 'a -> 'a2,
           visit_'b : 'this -> 'env -> 'b -> 'b2
         }

(* Always implement runtime behaviors in terms of interface, so it can be inherited, overrode and extended. *)
local
fun default_visit_expr is_sub this env data =
  let
    val ExprVisitorInterface record = is_sub this
  in
    case data of
        EConst data => #visit_EConst record this env data
      | EAdd data => #visit_EAdd record this env data
  end
fun default_visit_EConst is_sub this env data =
  let
    val ExprVisitorInterface record = is_sub this
  in
    EConst $ #visit_'a record this env data
  end
fun default_visit_EAdd is_sub this env data = 
  let
    val ExprVisitorInterface record = is_sub this
    val (data, e1, e2) = data
    val data = #visit_'b record this env data
    val e1 = #visit_expr record this env e1
    val e2 = #visit_expr record this env e2
  in
    EAdd (data, e1, e2)
  end
in
fun default_expr_visitor is_sub visit_'a visit_'b =
  ExprVisitorInterface {is_sub = is_sub,
               visit_expr = default_visit_expr is_sub,
               visit_EConst = default_visit_EConst is_sub,
               visit_EAdd = default_visit_EAdd is_sub,
               visit_'a = visit_'a,
               visit_'b = visit_'b}
end

(*
fun override_visit_expr super visit_expr =
  let
    val ExprVisitor record = super
  in
    ExprVisitor {visit_expr = visit_expr, visit_EConst = #visit_EConst record, visit_EAdd = #visit_EAdd record, visit_'a = #visit_'a record, visit_'b = #visit_'b record}
  end
    
fun override_visit_EConst super new =
  let
    val ExprVisitor record = super
  in
    ExprVisitor {visit_expr = #visit_expr record, visit_EConst = new, visit_EAdd = #visit_EAdd record, visit_'a = #visit_'a record, visit_'b = #visit_'b record}
  end
    
fun override_visit_EAdd super new =
  let
    val ExprVisitor record = super
  in
    ExprVisitor {visit_expr = #visit_expr record, visit_EConst = #visit_EConst record, visit_EAdd = new, visit_'a = #visit_'a record, visit_'b = #visit_'b record}
  end

fun override_visit_'a super new =
  let
    val ExprVisitor record = super
  in
    ExprVisitor {visit_expr = #visit_expr record, visit_EConst = #visit_EConst record, visit_EAdd = #visit_EAdd record, visit_'a = new, visit_'b = #visit_'b record}
  end

fun override_visit_'b super new =
  let
    val ExprVisitor record = super
  in
    ExprVisitor {visit_expr = #visit_expr record, visit_EConst = #visit_EConst record, visit_EAdd = #visit_EAdd record, visit_'a = #visit_'a record, visit_'b = new}
  end
*)

(* Always implement runtime behaviors in terms of interface, so it can be inherited, overrode and extended. *)
fun strip_expr_visitor is_sub () =
  let
    fun visit_'a_'b _ _ _ = ()
  in
    default_expr_visitor is_sub visit_'a_'b visit_'a_'b
  end

(* This is the expression visitor class. A class determines the real memory layout. It is not parametrized on a carrier type so it is closed and cannot be inherited, overrode or extended. *)    
datatype ('a, 'b, 'a2, 'b2, 'env) expr_visitor =
         ExprVisitor of
         {
           visit_expr : ('a, 'b, 'a2, 'b2, 'env) expr_visitor -> 'env -> ('a, 'b) expr -> ('a2, 'b2) expr,
           visit_EConst : ('a, 'b, 'a2, 'b2, 'env) expr_visitor -> 'env -> 'a -> ('a2, 'b2) expr,
           visit_EAdd : ('a, 'b, 'a2, 'b2, 'env) expr_visitor -> 'env -> 'b * ('a, 'b) expr * ('a, 'b) expr -> ('a2, 'b2) expr,
           visit_'a : ('a, 'b, 'a2, 'b2, 'env) expr_visitor -> 'env -> 'a -> 'a2,
           visit_'b : ('a, 'b, 'a2, 'b2, 'env) expr_visitor -> 'env -> 'b -> 'b2
         }

fun expr_visitor_impls_interface (this : ('a, 'b, 'a2, 'b2, 'env) expr_visitor) :
    (('a, 'b, 'a2, 'b2, 'env) expr_visitor, 'a, 'b, 'a2, 'b2, 'env) expr_visitor_interface =
  let
    val ExprVisitor record = this
    fun visit_expr this = #visit_expr record this
    fun visit_EConst this = #visit_EConst record this
    fun visit_EAdd this = #visit_EAdd record this
    fun visit_'a this = #visit_'a record this
    fun visit_'b this = #visit_'b record this
  in
    ExprVisitorInterface {is_sub = expr_visitor_impls_interface,
                          visit_expr = visit_expr,
                          visit_EConst = visit_EConst,
                          visit_EAdd = visit_EAdd,
                          visit_'a = visit_'a,
                          visit_'b = visit_'b}
  end

(* create a real visitor in memory *)
fun new_strip_expr_visitor () : ('a, 'b, unit, unit, 'env) expr_visitor =
  let
    val visitor as (ExprVisitorInterface record) = strip_expr_visitor expr_visitor_impls_interface ()
    fun visit_expr this = #visit_expr record this 
    fun visit_EConst this = #visit_EConst record this
    fun visit_EAdd this = #visit_EAdd record this
    fun visit_'a this = #visit_'a record this
    fun visit_'b this = #visit_'b record this
  in
    ExprVisitor {visit_expr = visit_expr,
                 visit_EConst = visit_EConst,
                 visit_EAdd = visit_EAdd,
                 visit_'a = visit_'a,
                 visit_'b = visit_'b}
  end
    
fun strip e : (unit, unit) expr =
  let
    val visitor as (ExprVisitor record) = new_strip_expr_visitor ()
  in
    #visit_expr record visitor () e
  end
    
datatype ('this, 'a, 'b, 'env) number_expr_visitor_interface =
         NumberExprVisitorInterface of
         {
           is_sub : 'this -> ('this, 'a, 'b, 'env) number_expr_visitor_interface,
           visit_expr : 'this -> 'env -> ('a, 'b) expr -> (int, int) expr,
           visit_EConst : 'this -> 'env -> 'a -> (int, int) expr,
           visit_EAdd : 'this -> 'env -> 'b * ('a, 'b) expr * ('a, 'b) expr -> (int, int) expr,
           visit_'a : 'this -> 'env -> 'a -> int,
           visit_'b : 'this -> 'env -> 'b -> int,
           count : int ref
         }

fun number_expr_visitor_refines_expr_visitor (is_sub : 'this -> ('this, 'a, 'b, 'env) number_expr_visitor_interface) (this : 'this) : ('this, 'a, 'b, int, int, 'env) expr_visitor_interface =
  let
    val NumberExprVisitorInterface record = is_sub this
    fun visit_expr this = #visit_expr record this
    fun visit_EConst this = #visit_EConst record this
    fun visit_EAdd this = #visit_EAdd record this
    fun visit_'a this = #visit_'a record this
    fun visit_'b this = #visit_'b record this
  in
    ExprVisitorInterface {is_sub = number_expr_visitor_refines_expr_visitor is_sub,
                          visit_expr = visit_expr,
                          visit_EConst = visit_EConst,
                          visit_EAdd = visit_EAdd,
                          visit_'a = visit_'a,
                          visit_'b = visit_'b}
  end

fun number_expr_visitor (is_sub : 'this -> ('this, 'a, 'b, 'env) number_expr_visitor_interface) () : ('this, 'a, 'b, int, int, 'env) expr_visitor_interface =
  let
    fun visit_'a_'b (this : 'this) _ _ =
      let
        val NumberExprVisitorInterface record = is_sub this
        val count = #count record
        val old = !count
        val () = count := old + 1
      in
        old
      end
  in
    default_expr_visitor (number_expr_visitor_refines_expr_visitor is_sub) visit_'a_'b visit_'a_'b
  end
    
datatype ('a, 'b, 'env) number_expr_visitor =
         NumberExprVisitor of
         {
           visit_expr : ('a, 'b, 'env) number_expr_visitor -> 'env -> ('a, 'b) expr -> (int, int) expr,
           visit_EConst : ('a, 'b, 'env) number_expr_visitor -> 'env -> 'a -> (int, int) expr,
           visit_EAdd : ('a, 'b, 'env) number_expr_visitor -> 'env -> 'b * ('a, 'b) expr * ('a, 'b) expr -> (int, int) expr,
           visit_'a : ('a, 'b, 'env) number_expr_visitor -> 'env -> 'a -> int,
           visit_'b : ('a, 'b, 'env) number_expr_visitor -> 'env -> 'b -> int,
           count : int ref
         }

fun number_expr_visitor_impls_interface (this : ('a, 'b, 'env) number_expr_visitor) :
    (('a, 'b, 'env) number_expr_visitor, 'a, 'b, 'env) number_expr_visitor_interface =
  let
    val NumberExprVisitor record = this
    fun visit_expr this = #visit_expr record this
    fun visit_EConst this = #visit_EConst record this
    fun visit_EAdd this = #visit_EAdd record this
    fun visit_'a this = #visit_'a record this
    fun visit_'b this = #visit_'b record this
    val count = #count record
  in
    NumberExprVisitorInterface {is_sub = number_expr_visitor_impls_interface,
                                visit_expr = visit_expr,
                                visit_EConst = visit_EConst,
                                visit_EAdd = visit_EAdd,
                                visit_'a = visit_'a,
                                visit_'b = visit_'b,
                                count = count
                               }
  end

fun new_number_expr_visitor () : ('a, 'b, 'env) number_expr_visitor =
  let
    val visitor as (ExprVisitorInterface record) = number_expr_visitor number_expr_visitor_impls_interface ()
    fun visit_expr this = #visit_expr record this 
    fun visit_EConst this = #visit_EConst record this
    fun visit_EAdd this = #visit_EAdd record this
    fun visit_'a this = #visit_'a record this
    fun visit_'b this = #visit_'b record this
    val count = ref 0
  in
    NumberExprVisitor {visit_expr = visit_expr,
                       visit_EConst = visit_EConst,
                       visit_EAdd = visit_EAdd,
                       visit_'a = visit_'a,
                       visit_'b = visit_'b,
                       count = count
                      }
  end
                                  
fun number e : (int, int) expr =
  let
    val visitor as (NumberExprVisitor record) = new_number_expr_visitor ()
  in
    #visit_expr record visitor () e
  end

(*    
fun number2 e : (int, int) expr =
  let
    val super = new_number_visitor ()
    val count = snd super
    fun visit_'b _ _ _ = 
      let
        val old = !count
        val () = count := old + 1
      in
        old + 10000
      end
    val visitor as (ExprVisitor visiter_record) = override_visit_'b (number_visitor_is_visitor super) visit_'b
  in
    #visit_expr visiter_record visitor () e
  end
*)
    
val e = EAdd ("a", EAdd ("b", EConst [()], EConst [(), ()]), EConst [])
             
val e1 = strip e
val e2 = number e
(* val e3 = number2 e *)

end
