structure Visitor = struct

open Util
       
infixr 0 $
         
datatype ('a, 'b) expr =
         EConst of 'a
         | EAdd of 'b * ('a, 'b) expr * ('a, 'b) expr

(* using record types and recursive types (datatypes) to mimic object-oriented programming (dynamic dispatching and inheritance) *)

                                                 
datatype ('this, 'a, 'b, 'a2, 'b2, 'env) expr_visitor =
         ExprVisitor of
         {
           visit_expr : 'this -> ('this -> ('this, 'a, 'b, 'a2, 'b2, 'env) expr_visitor) -> 'env -> ('a, 'b) expr -> ('a2, 'b2) expr,
           visit_EConst : 'this -> ('this -> ('this, 'a, 'b, 'a2, 'b2, 'env) expr_visitor) -> 'env -> 'a -> ('a2, 'b2) expr,
           visit_EAdd : 'this -> ('this -> ('this, 'a, 'b, 'a2, 'b2, 'env) expr_visitor) -> 'env -> 'b * ('a, 'b) expr * ('a, 'b) expr -> ('a2, 'b2) expr,
           visit_'a : 'this -> ('this -> ('this, 'a, 'b, 'a2, 'b2, 'env) expr_visitor) -> 'env -> 'a -> 'a2,
           visit_'b : 'this -> ('this -> ('this, 'a, 'b, 'a2, 'b2, 'env) expr_visitor) -> 'env -> 'b -> 'b2
         }

local
fun default_visit_expr this this_is_visitor env data =
  let
    val ExprVisitor record = this_is_visitor this
  in
    case data of
        EConst data => #visit_EConst record this this_is_visitor env data
      | EAdd data => #visit_EAdd record this this_is_visitor env data
  end
fun default_visit_EConst this this_is_visitor env data =
  let
    val ExprVisitor record = this_is_visitor this
  in
    EConst $ #visit_'a record this this_is_visitor env data
  end
fun default_visit_EAdd this this_is_visitor env data = 
  let
    val ExprVisitor record = this_is_visitor this
    val (data, e1, e2) = data
    val data = #visit_'b record this this_is_visitor env data
    val e1 = #visit_expr record this this_is_visitor env e1
    val e2 = #visit_expr record this this_is_visitor env e2
  in
    EAdd (data, e1, e2)
  end
in
fun default_expr_visitor visit_'a visit_'b (* : ('a, 'b, 'a2, 'b2, 'env) default_expr_visitor *) =
  ExprVisitor {visit_expr = default_visit_expr, visit_EConst = default_visit_EConst, visit_EAdd = default_visit_EAdd, visit_'a = visit_'a, visit_'b = visit_'b}
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

fun strip_expr_visitor () =
  let
    fun visit_'a_'b _ _ _ _ = ()
  in
    default_expr_visitor visit_'a_'b visit_'a_'b
  end

(* the real type in memory *)    
datatype ('a, 'b, 'a2, 'b2, 'env) strip_expr_visitor =
         StripExprVisitor of
         {
           visit_expr : ('a, 'b, 'a2, 'b2, 'env) strip_expr_visitor -> 'env -> ('a, 'b) expr -> ('a2, 'b2) expr,
           visit_EConst : ('a, 'b, 'a2, 'b2, 'env) strip_expr_visitor -> 'env -> 'a -> ('a2, 'b2) expr,
           visit_EAdd : ('a, 'b, 'a2, 'b2, 'env) strip_expr_visitor -> 'env -> 'b * ('a, 'b) expr * ('a, 'b) expr -> ('a2, 'b2) expr,
           visit_'a : ('a, 'b, 'a2, 'b2, 'env) strip_expr_visitor -> 'env -> 'a -> 'a2,
           visit_'b : ('a, 'b, 'a2, 'b2, 'env) strip_expr_visitor -> 'env -> 'b -> 'b2
         }

fun strip_expr_visitor_is_expr_visitor (this : ('a, 'b, 'a2, 'b2, 'env) strip_expr_visitor) :
    (('a, 'b, 'a2, 'b2, 'env) strip_expr_visitor, 'a, 'b, 'a2, 'b2, 'env) expr_visitor =
  let
    val StripExprVisitor record = this
    fun visit_expr this this_is_visitor = #visit_expr record this
    fun visit_EConst this this_is_visitor = #visit_EConst record this
    fun visit_EAdd this this_is_visitor = #visit_EAdd record this
    fun visit_'a this this_is_visitor = #visit_'a record this
    fun visit_'b this this_is_visitor = #visit_'b record this
  in
    ExprVisitor {visit_expr = visit_expr, visit_EConst = visit_EConst, visit_EAdd = visit_EAdd, visit_'a = visit_'a, visit_'b = visit_'b}
  end

fun new_strip_expr_visitor () : ('a, 'b, unit, unit, 'env) strip_expr_visitor =
  let
    val visitor as (ExprVisitor record) = strip_expr_visitor ()
    fun visit_expr this = #visit_expr record this strip_expr_visitor_is_expr_visitor
    fun visit_EConst this = #visit_EConst record this strip_expr_visitor_is_expr_visitor
    fun visit_EAdd this = #visit_EAdd record this strip_expr_visitor_is_expr_visitor
    fun visit_'a this = #visit_'a record this strip_expr_visitor_is_expr_visitor
    fun visit_'b this = #visit_'b record this strip_expr_visitor_is_expr_visitor
  in
    StripExprVisitor {visit_expr = visit_expr, visit_EConst = visit_EConst, visit_EAdd = visit_EAdd, visit_'a = visit_'a, visit_'b = visit_'b}
  end
    
fun strip e : (unit, unit) expr =
  let
    val visitor as (StripExprVisitor record) = new_strip_expr_visitor ()
  in
    #visit_expr record visitor () e
  end
    
(*    
datatype ('a, 'b, 'env) number_expr_visitor =
     {
       visit_expr : 'this -> 'env -> ('a, 'b) expr -> (int, int) expr,
       visit_EConst : 'this -> 'env -> 'a -> (int, int) expr,
       visit_EAdd : 'this -> 'env -> 'b * ('a, 'b) expr * ('a, 'b) expr -> (int, int) expr,
       visit_'a : 'this -> 'env -> 'a -> int,
       visit_'b : 'this -> 'env -> 'b -> int,
       count : int ref
     }

fun number_expr_visitor () =
  let
    val count = ref 0
    fun visit_'a_'b this _ _ =
      let
        val NumberExprVisitor record = this
        val count = #count record
        val old = !count
        val () = count := old + 1
      in
        old
      end
    val visitor as DefaultExprVisitor visitor_record = default_expr_visitor visit_'a_'b visit_'a_'b
  in
    (visitor, count)
  end

val number_visitor_is_visitor = fst
                                  
fun number e : (int, int) expr =
  let
    val visitor as (ExprVisitor visiter_record) = number_visitor_is_visitor $ new_number_visitor ()
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
    val visitor as (ExprVisitor visiter_record) = override_visit_'b (number_visitor_is_visitor super) visit_'b
  in
    #visit_expr visiter_record visitor () e
  end
*)
    
val e = EAdd ("a", EAdd ("b", EConst [()], EConst [(), ()]), EConst [])
             
val e1 = strip e
(* val e2 = number e *)
(* val e3 = number2 e *)

end
