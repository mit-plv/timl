structure Visitor = struct

open Util
       
infixr 0 $

type bn = string
             
datatype ty =
         TInt

type 'p abs = 'p
type 'bn binder = 'bn
type 't outer = 't
type 'p rebind = 'p
           
type 't inner = ('t outer) rebind
type ('p, 't) bind = ('p * 't inner) abs
     
datatype ('c, 'fn) expr =
         EConst of 'c
         | EApp of ('c, 'fn) expr * ('c, 'fn) expr
         | EVar of 'fn
         | EAbs of (bn binder, ty outer, ('c, 'fn) expr) bind

(* using record types and recursive types (datatypes) to mimic object-oriented programming (dynamic dispatching and inheritance) *)

(* This is the expression visitor interface. An interface is a record where the carrier type ['this] is unknown but we know it has the desired methods. *)
(* Only interfaces can be inherited, overrode and extended. *)
type ('this, 'c, 'fn, 'c2, 'fn2, 'env) expr_visitor_vtable =
     {
       visit_expr : 'this -> 'env -> ('c, 'fn) expr -> ('c2, 'fn2) expr,
       visit_EConst : 'this -> 'env -> 'c -> ('c2, 'fn2) expr,
       visit_EApp : 'this -> 'env -> 'fn * ('c, 'fn) expr * ('c, 'fn) expr -> ('c2, 'fn2) expr,
       visit_'c : 'this -> 'env -> 'c -> 'c2,
       visit_'fn : 'this -> 'env -> 'fn -> 'fn2
     }
type ('this, 'c, 'fn, 'c2, 'fn2, 'env) expr_visitor_interface =
     ('this, 'c, 'fn, 'c2, 'fn2, 'env) expr_visitor_vtable

(* Always implement runtime behaviors in terms of interface, so it can be inherited, overrode and extended. *)
(* [is_sub] is a coercion to mimic subtyping or subclassing *)
local
  type ('this, 'c, 'fn, 'c2, 'fn2, 'env) refinement = 'this -> ('this, 'c, 'fn, 'c2, 'fn2, 'env) expr_visitor_interface
  fun default_visit_expr (is_sub : ('this, 'c, 'fn, 'c2, 'fn2, 'env) refinement) this env data =
  let
    val vtable = is_sub this
  in
    case data of
        EConst data => #visit_EConst vtable this env data
      | EApp data => #visit_EApp vtable this env data
  end
fun default_visit_EConst (is_sub : ('this, 'c, 'fn, 'c2, 'fn2, 'env) refinement) this env data =
  let
    val vtable = is_sub this
  in
    EConst $ #visit_'c vtable this env data
  end
fun default_visit_EApp (is_sub : ('this, 'c, 'fn, 'c2, 'fn2, 'env) refinement) this env data = 
  let
    val vtable = is_sub this
    val (data, e1, e2) = data
    val data = #visit_'fn vtable this env data
    val e1 = #visit_expr vtable this env e1
    val e2 = #visit_expr vtable this env e2
  in
    EApp (data, e1, e2)
  end
in
fun default_expr_visitor_vtable is_sub visit_'c visit_'fn =
  {visit_expr = default_visit_expr is_sub,
   visit_EConst = default_visit_EConst is_sub,
   visit_EApp = default_visit_EApp is_sub,
   visit_'c = visit_'c,
   visit_'fn = visit_'fn}
end

(* fun override_visit_expr super visit_expr = *)
(*   let *)
(*     val ExprVisitor record = super *)
(*   in *)
(*     ExprVisitor {visit_expr = visit_expr, visit_EConst = #visit_EConst record, visit_EApp = #visit_EApp record, visit_'c = #visit_'c record, visit_'fn = #visit_'fn record} *)
(*   end *)
    
(* fun override_visit_EConst super new = *)
(*   let *)
(*     val ExprVisitor record = super *)
(*   in *)
(*     ExprVisitor {visit_expr = #visit_expr record, visit_EConst = new, visit_EApp = #visit_EApp record, visit_'c = #visit_'c record, visit_'fn = #visit_'fn record} *)
(*   end *)
    
(* fun override_visit_EApp super new = *)
(*   let *)
(*     val ExprVisitor record = super *)
(*   in *)
(*     ExprVisitor {visit_expr = #visit_expr record, visit_EConst = #visit_EConst record, visit_EApp = new, visit_'c = #visit_'c record, visit_'fn = #visit_'fn record} *)
(*   end *)

(* fun override_visit_'c super new = *)
(*   let *)
(*     val ExprVisitor record = super *)
(*   in *)
(*     ExprVisitor {visit_expr = #visit_expr record, visit_EConst = #visit_EConst record, visit_EApp = #visit_EApp record, visit_'c = new, visit_'fn = #visit_'fn record} *)
(*   end *)

fun override_visit_'fn (record : ('this, 'c, 'fn, 'c2, 'fn2, 'env) expr_visitor_vtable) new =
    {visit_expr = #visit_expr record, visit_EConst = #visit_EConst record, visit_EApp = #visit_EApp record, visit_'c = #visit_'c record, visit_'fn = new}

(* Always implement runtime behaviors in terms of interface, so it can be inherited, overrode and extended. *)
fun strip_expr_visitor_vtable is_sub () =
  let
    fun visit_'c_'fn _ _ _ = ()
  in
    default_expr_visitor_vtable is_sub visit_'c_'fn visit_'c_'fn
  end

(* This is the expression visitor class. A class determines the real memory layout. It is not parametrized on a carrier type so it is closed and cannot be inherited, overrode or extended. *)    
datatype ('c, 'fn, 'c2, 'fn2, 'env) expr_visitor =
         ExprVisitor of (('c, 'fn, 'c2, 'fn2, 'env) expr_visitor, 'c, 'fn, 'c2, 'fn2, 'env) expr_visitor_vtable

fun expr_visitor_impls_interface (this : ('c, 'fn, 'c2, 'fn2, 'env) expr_visitor) :
    (('c, 'fn, 'c2, 'fn2, 'env) expr_visitor, 'c, 'fn, 'c2, 'fn2, 'env) expr_visitor_interface =
  let
    val ExprVisitor vtable = this
  in
    vtable
  end

(* create a real visitor in memory *)
fun new_strip_expr_visitor () : ('c, 'fn, unit, unit, 'env) expr_visitor =
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
    
type ('this, 'c, 'fn, 'env) number_expr_visitor_interface =
         {
           vtable : ('this, 'c, 'fn, int, int, 'env) expr_visitor_vtable,
           count : int ref
         }

fun number_expr_visitor_refines_expr_visitor (is_sub : 'this -> ('this, 'c, 'fn, 'env) number_expr_visitor_interface) (this : 'this) : ('this, 'c, 'fn, int, int, 'env) expr_visitor_interface =
  let
    val record = is_sub this
    val vtable = #vtable record
  in
    vtable
  end

fun number_expr_visitor_vtable is_sub =
  let
    fun visit_'c_'fn this _ _ =
      let
        val record = is_sub this
        val count = #count record
        val old = !count
        val () = count := old + 1
      in
        old
      end
  in
    default_expr_visitor_vtable (number_expr_visitor_refines_expr_visitor is_sub) visit_'c_'fn visit_'c_'fn
  end

datatype ('c, 'fn, 'env) number_expr_visitor =
         NumberExprVisitor of
         {
           vtable : (('c, 'fn, 'env) number_expr_visitor, 'c, 'fn, int, int, 'env) expr_visitor_vtable,
           count : int ref
         }

fun number_expr_visitor_impls_interface (this : ('c, 'fn, 'env) number_expr_visitor) :
    (('c, 'fn, 'env) number_expr_visitor, 'c, 'fn, 'env) number_expr_visitor_interface =
  let
    val NumberExprVisitor record = this
    val vtable = #vtable record
    val count = #count record
  in
    {vtable = vtable,
     count = count
    }
  end

fun new_number_expr_visitor () : ('c, 'fn, 'env) number_expr_visitor =
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

fun number2_expr_visitor_vtable (is_sub : 'this -> ('this, 'c, 'fn, 'env) number_expr_visitor_interface) =
  let
    val super_vtable = number_expr_visitor_vtable number_expr_visitor_impls_interface
    fun visit_'fn this env data = #visit_'fn super_vtable this env data + 10000
    val vtable = override_visit_'fn super_vtable visit_'fn
  in
    vtable
  end

fun new_number2_expr_visitor () : ('c, 'fn, 'env) number_expr_visitor =
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

val e = EApp ("a", EApp ("b", EConst [()], EConst [(), ()]), EConst [])
             
val e1 = strip e
val e2 = number e
val e3 = number2 e

end
