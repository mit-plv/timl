structure Visitor = struct

open Util
       
infixr 0 $
         
datatype ('a, 'b) expr =
         EConst of 'a
         | EAdd of 'b * ('a, 'b) expr * ('a, 'b) expr

(* using record types and recursive types (datatypes) to mimic object-oriented programming (dynamic dispatching and inheritance) *)
datatype ('a, 'b, 'a2, 'b2, 'env) expr_visitor =
         Visitor_expr of
         {
           visit_expr : ('a, 'b, 'a2, 'b2, 'env) expr_visitor -> 'env -> ('a, 'b) expr -> ('a2, 'b2) expr,
           visit_EConst : ('a, 'b, 'a2, 'b2, 'env) expr_visitor -> 'env -> 'a -> ('a2, 'b2) expr,
           visit_EAdd : ('a, 'b, 'a2, 'b2, 'env) expr_visitor -> 'env -> 'b * ('a, 'b) expr * ('a, 'b) expr -> ('a2, 'b2) expr,
           visit_'a : ('a, 'b, 'a2, 'b2, 'env) expr_visitor -> 'env -> 'a -> 'a2,
           visit_'b : ('a, 'b, 'a2, 'b2, 'env) expr_visitor -> 'env -> 'b -> 'b2
         }

fun default_visit_expr this env data =
  let
    val Visitor_expr record = this
  in
    case data of
        EConst data => #visit_EConst record this env data
      | EAdd data => #visit_EAdd record this env data
  end
    
fun default_visit_EConst this env data =
  let
    val Visitor_expr record = this
  in
    EConst $ #visit_'a record this env data
  end
    
fun default_visit_EAdd this env data = 
  let
    val Visitor_expr record = this
    val (data, e1, e2) = data
    val data = #visit_'b record this env data
    val e1 = #visit_expr record this env e1
    val e2 = #visit_expr record this env e2
  in
    EAdd (data, e1, e2)
  end
    
fun default_expr_visitor visit_'a visit_'b : ('a, 'b, 'a2, 'b2, 'env) expr_visitor =
  Visitor_expr {visit_expr = default_visit_expr, visit_EConst = default_visit_EConst, visit_EAdd = default_visit_EAdd, visit_'a = visit_'a, visit_'b = visit_'b}

fun override_visit_expr super visit_expr =
  let
    val Visitor_expr record = super
  in
    Visitor_expr {visit_expr = visit_expr, visit_EConst = #visit_EConst record, visit_EAdd = #visit_EAdd record, visit_'a = #visit_'a record, visit_'b = #visit_'b record}
  end
    
fun override_visit_EConst super new =
  let
    val Visitor_expr record = super
  in
    Visitor_expr {visit_expr = #visit_expr record, visit_EConst = new, visit_EAdd = #visit_EAdd record, visit_'a = #visit_'a record, visit_'b = #visit_'b record}
  end
    
fun override_visit_EAdd super new =
  let
    val Visitor_expr record = super
  in
    Visitor_expr {visit_expr = #visit_expr record, visit_EConst = #visit_EConst record, visit_EAdd = new, visit_'a = #visit_'a record, visit_'b = #visit_'b record}
  end

fun override_visit_'a super new =
  let
    val Visitor_expr record = super
  in
    Visitor_expr {visit_expr = #visit_expr record, visit_EConst = #visit_EConst record, visit_EAdd = #visit_EAdd record, visit_'a = new, visit_'b = #visit_'b record}
  end

fun override_visit_'b super new =
  let
    val Visitor_expr record = super
  in
    Visitor_expr {visit_expr = #visit_expr record, visit_EConst = #visit_EConst record, visit_EAdd = #visit_EAdd record, visit_'a = #visit_'a record, visit_'b = new}
  end

fun strip e : (unit, unit) expr =
  let
    fun visit_'a_'b _ _ _ = ()
    val visitor as (Visitor_expr visiter_record) = default_expr_visitor visit_'a_'b visit_'a_'b
  in
    #visit_expr visiter_record visitor () e
  end
   
fun new_number_visitor () =
  let
    val count = ref 0
    fun visit_'a_'b _ _ _ =
      let
        val old = !count
        val () = count := old + 1
      in
        old
      end
    val visitor = default_expr_visitor visit_'a_'b visit_'a_'b
  in
    (visitor, count)
  end

val number_visitor_is_visitor = fst
                                  
fun number e : (int, int) expr =
  let
    val visitor as (Visitor_expr visiter_record) = number_visitor_is_visitor $ new_number_visitor ()
  in
    #visit_expr visiter_record visitor () e
  end

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
    val visitor as (Visitor_expr visiter_record) = override_visit_'b (number_visitor_is_visitor super) visit_'b
  in
    #visit_expr visiter_record visitor () e
  end
   
val e = EAdd ("a", EAdd ("b", EConst [()], EConst [(), ()]), EConst [])

val e1 = strip e
val e2 = number e
val e3 = number2 e
   
end
