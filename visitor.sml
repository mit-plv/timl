structure Visitor = struct

open Util
       
infixr 0 $
         
datatype ('a, 'b) expr =
         EConst of 'a
         | EAdd of 'b * ('a, 'b) expr * ('a, 'b) expr

(* using record types and recursive types (datatypes) to mimic object-oriented programming (dynamic dispatching and inheritance) *)

(* This is the expression visitor interface. An interface is a record where the carrier type ['this] is unknown but we know it has the desired methods. *)
(* Only interfaces can be inherited, overrode and extended. *)
type ('this, 'a, 'b, 'a2, 'b2, 'env) expr_visitor_vtable =
     {
       visit_expr : 'this -> 'env -> ('a, 'b) expr -> ('a2, 'b2) expr,
       visit_EConst : 'this -> 'env -> 'a -> ('a2, 'b2) expr,
       visit_EAdd : 'this -> 'env -> 'b * ('a, 'b) expr * ('a, 'b) expr -> ('a2, 'b2) expr,
       visit_'a : 'this -> 'env -> 'a -> 'a2,
       visit_'b : 'this -> 'env -> 'b -> 'b2
     }
type ('this, 'a, 'b, 'a2, 'b2, 'env) expr_visitor_interface =
     ('this, 'a, 'b, 'a2, 'b2, 'env) expr_visitor_vtable

(* Always implement runtime behaviors in terms of interface, so it can be inherited, overrode and extended. *)
(* [is_sub] is a coercion to mimic subtyping or subclassing *)
local
  type ('this, 'a, 'b, 'a2, 'b2, 'env) refinement = 'this -> ('this, 'a, 'b, 'a2, 'b2, 'env) expr_visitor_interface
  fun default_visit_expr (is_sub : ('this, 'a, 'b, 'a2, 'b2, 'env) refinement) this env data =
  let
    val vtable = is_sub this
  in
    case data of
        EConst data => #visit_EConst vtable this env data
      | EAdd data => #visit_EAdd vtable this env data
  end
fun default_visit_EConst (is_sub : ('this, 'a, 'b, 'a2, 'b2, 'env) refinement) this env data =
  let
    val vtable = is_sub this
  in
    EConst $ #visit_'a vtable this env data
  end
fun default_visit_EAdd (is_sub : ('this, 'a, 'b, 'a2, 'b2, 'env) refinement) this env data = 
  let
    val vtable = is_sub this
    val (data, e1, e2) = data
    val data = #visit_'b vtable this env data
    val e1 = #visit_expr vtable this env e1
    val e2 = #visit_expr vtable this env e2
  in
    EAdd (data, e1, e2)
  end
in
fun default_expr_visitor_vtable is_sub visit_'a visit_'b =
  {visit_expr = default_visit_expr is_sub,
   visit_EConst = default_visit_EConst is_sub,
   visit_EAdd = default_visit_EAdd is_sub,
   visit_'a = visit_'a,
   visit_'b = visit_'b}
end

(* fun override_visit_expr super visit_expr = *)
(*   let *)
(*     val ExprVisitor record = super *)
(*   in *)
(*     ExprVisitor {visit_expr = visit_expr, visit_EConst = #visit_EConst record, visit_EAdd = #visit_EAdd record, visit_'a = #visit_'a record, visit_'b = #visit_'b record} *)
(*   end *)
    
(* fun override_visit_EConst super new = *)
(*   let *)
(*     val ExprVisitor record = super *)
(*   in *)
(*     ExprVisitor {visit_expr = #visit_expr record, visit_EConst = new, visit_EAdd = #visit_EAdd record, visit_'a = #visit_'a record, visit_'b = #visit_'b record} *)
(*   end *)
    
(* fun override_visit_EAdd super new = *)
(*   let *)
(*     val ExprVisitor record = super *)
(*   in *)
(*     ExprVisitor {visit_expr = #visit_expr record, visit_EConst = #visit_EConst record, visit_EAdd = new, visit_'a = #visit_'a record, visit_'b = #visit_'b record} *)
(*   end *)

(* fun override_visit_'a super new = *)
(*   let *)
(*     val ExprVisitor record = super *)
(*   in *)
(*     ExprVisitor {visit_expr = #visit_expr record, visit_EConst = #visit_EConst record, visit_EAdd = #visit_EAdd record, visit_'a = new, visit_'b = #visit_'b record} *)
(*   end *)

fun override_visit_'b (record : ('this, 'a, 'b, 'a2, 'b2, 'env) expr_visitor_vtable) new =
    {visit_expr = #visit_expr record, visit_EConst = #visit_EConst record, visit_EAdd = #visit_EAdd record, visit_'a = #visit_'a record, visit_'b = new}

(* Always implement runtime behaviors in terms of interface, so it can be inherited, overrode and extended. *)
fun strip_expr_visitor_vtable is_sub () =
  let
    fun visit_'a_'b _ _ _ = ()
  in
    default_expr_visitor_vtable is_sub visit_'a_'b visit_'a_'b
  end

(* This is the expression visitor class. A class determines the real memory layout. It is not parametrized on a carrier type so it is closed and cannot be inherited, overrode or extended. *)    
datatype ('a, 'b, 'a2, 'b2, 'env) expr_visitor =
         ExprVisitor of (('a, 'b, 'a2, 'b2, 'env) expr_visitor, 'a, 'b, 'a2, 'b2, 'env) expr_visitor_vtable

fun expr_visitor_impls_interface (this : ('a, 'b, 'a2, 'b2, 'env) expr_visitor) :
    (('a, 'b, 'a2, 'b2, 'env) expr_visitor, 'a, 'b, 'a2, 'b2, 'env) expr_visitor_interface =
  let
    val ExprVisitor vtable = this
  in
    vtable
  end

(* create a real visitor in memory *)
fun new_strip_expr_visitor () : ('a, 'b, unit, unit, 'env) expr_visitor =
  let
    val vtable = strip_expr_visitor_vtable expr_visitor_impls_interface ()
  in
    ExprVisitor vtable
  end
    
fun strip e : (unit, unit) expr =
  let
    val visitor as (ExprVisitor vtable) = new_strip_expr_visitor ()
  in
    #visit_expr vtable visitor () e
  end
    
type ('this, 'a, 'b, 'env) number_expr_visitor_interface =
         {
           vtable : ('this, 'a, 'b, int, int, 'env) expr_visitor_vtable,
           count : int ref
         }

fun number_expr_visitor_refines_expr_visitor (is_sub : 'this -> ('this, 'a, 'b, 'env) number_expr_visitor_interface) (this : 'this) : ('this, 'a, 'b, int, int, 'env) expr_visitor_interface =
  let
    val record = is_sub this
    val vtable = #vtable record
  in
    vtable
  end

fun number_expr_visitor_vtable is_sub =
  let
    fun visit_'a_'b this _ _ =
      let
        val record = is_sub this
        val count = #count record
        val old = !count
        val () = count := old + 1
      in
        old
      end
  in
    default_expr_visitor_vtable (number_expr_visitor_refines_expr_visitor is_sub) visit_'a_'b visit_'a_'b
  end

datatype ('a, 'b, 'env) number_expr_visitor =
         NumberExprVisitor of
         {
           vtable : (('a, 'b, 'env) number_expr_visitor, 'a, 'b, int, int, 'env) expr_visitor_vtable,
           count : int ref
         }

fun number_expr_visitor_impls_interface (this : ('a, 'b, 'env) number_expr_visitor) :
    (('a, 'b, 'env) number_expr_visitor, 'a, 'b, 'env) number_expr_visitor_interface =
  let
    val NumberExprVisitor record = this
    val vtable = #vtable record
    val count = #count record
  in
    {vtable = vtable,
     count = count
    }
  end

fun new_number_expr_visitor () : ('a, 'b, 'env) number_expr_visitor =
  let
    val vtable = number_expr_visitor_vtable number_expr_visitor_impls_interface
    val count = ref 0
  in
    NumberExprVisitor {vtable = vtable,
                       count = count
                      }
  end
                                  
fun number e : (int, int) expr =
  let
    val visitor as (NumberExprVisitor record) = new_number_expr_visitor ()
    val vtable = #vtable record
  in
    #visit_expr vtable visitor () e
  end

fun number2_expr_visitor_vtable (is_sub : 'this -> ('this, 'a, 'b, 'env) number_expr_visitor_interface) =
  let
    fun visit_'b this _ _ =
      let
        val record = is_sub this
        val count = #count record
        val old = !count
        val () = count := old + 1
      in
        old + 10000
      end
    val vtable = number_expr_visitor_vtable number_expr_visitor_impls_interface
    val vtable = override_visit_'b vtable visit_'b
  in
    vtable
  end

fun new_number2_expr_visitor () : ('a, 'b, 'env) number_expr_visitor =
  let
    val vtable = number2_expr_visitor_vtable number_expr_visitor_impls_interface
    val count = ref 0
  in
    NumberExprVisitor {vtable = vtable,
                       count = count
                      }
  end
                                  
fun number2 e : (int, int) expr =
  let
    val visitor as (NumberExprVisitor record) = new_number2_expr_visitor ()
    val vtable = #vtable record
  in
    #visit_expr vtable visitor () e
  end

val e = EAdd ("a", EAdd ("b", EConst [()], EConst [(), ()]), EConst [])
             
val e1 = strip e
val e2 = number e
val e3 = number2 e

end
