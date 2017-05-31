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
           visit_EAdd : ('a, 'b, 'a2, 'b2, 'env) expr_visitor -> 'env -> 'b * ('a, 'b) expr * ('a, 'b) expr -> ('a2, 'b2) expr
         }

fun default_expr_visitor (visit_'a : ('a, 'b, 'a2, 'b2, 'env) expr_visitor -> 'env -> 'a -> 'a2)
                         (visit_'b : ('a, 'b, 'a2, 'b2, 'env) expr_visitor -> 'env -> 'b -> 'b2)
    : ('a, 'b, 'a2, 'b2, 'env) expr_visitor =
  let
    fun visit_expr this env data =
      let
        val Visitor_expr record = this
      in
        case data of
            EConst data => #visit_EConst record this env data
          | EAdd data => #visit_EAdd record this env data
      end
    fun visit_EConst this env data =
      EConst $ visit_'a this env data
    fun visit_EAdd this env data = 
      let
        val Visitor_expr record = this
        val (data, e1, e2) = data
        val data = visit_'b this env data
        val e1 = #visit_expr record this env e1
        val e2 = #visit_expr record this env e2
      in
        EAdd (data, e1, e2)
      end
  in
    Visitor_expr {visit_expr = visit_expr, visit_EConst = visit_EConst, visit_EAdd = visit_EAdd}
  end

fun override_visit_expr super visit_expr =
  let
    val Visitor_expr record = super
  in
    Visitor_expr {visit_expr = visit_expr, visit_EConst = #visit_EConst record, visit_EAdd = #visit_EAdd record}
  end
    
fun override_visit_EConst super visit_EConst =
  let
    val Visitor_expr record = super
  in
    Visitor_expr {visit_expr = #visit_expr record, visit_EConst = visit_EConst, visit_EAdd = #visit_EAdd record}
  end
    
fun override_visit_EAdd super visit_EAdd =
  let
    val Visitor_expr record = super
  in
    Visitor_expr {visit_expr = #visit_expr record, visit_EConst = #visit_EConst record, visit_EAdd = visit_EAdd}
  end

fun strip e : (unit, unit) expr =
  let
    fun visit_'a_'b _ _ _ = ()
    val visitor as (Visitor_expr visiter_record) = default_expr_visitor visit_'a_'b visit_'a_'b
  in
    #visit_expr visiter_record visitor () e
  end
   
fun number e : (int, int) expr =
  let
    val count = ref 0
    fun visit_'a_'b _ _ _ =
      let
        val old = !count
        val () = count := old + 1
      in
        old
      end
    val visitor as (Visitor_expr visiter_record) = default_expr_visitor visit_'a_'b visit_'a_'b
  in
    #visit_expr visiter_record visitor () e
  end

val e = EAdd ("a", EAdd ("b", EConst [()], EConst [(), ()]), EConst [])

val e1 = strip e
val e2 = number e
   
end
