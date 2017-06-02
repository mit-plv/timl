(* inspired by the ICFP 2017 paper "Visitors Unchained" by FRANÇOIS POTTIER *)
structure Visitor = struct

open Util
       
infixr 0 $
infix 0 !!

type bn = string
             
datatype ty =
         TInt

type 'p abs = 'p
type 'bn binder = 'bn
type 't outer = 't
type 'p rebind = 'p
           
type 't inner = ('t outer) rebind
type ('p, 't) bind = ('p * 't inner) abs
type ('bn, 'anno, 't) anno_bind = ('bn binder * 'anno outer, 't) bind

type 'env context = {outer : 'env, current : 'env ref}

fun visit_pair visit_fst visit_snd extend env (a, b) =
  (visit_fst extend env a, visit_snd extend env b)

fun visit_abs visit_'p extend env p1 =
  visit_'p extend {outer = env, current = ref env} p1
fun visit_binder _ extend (ctx : 'env context) x1 =
  let
    val env = !(#current ctx)
    val (env, x2) = extend env x1
    val () = #current ctx := env
  in
    x2
  end
fun visit_outer visit_'t extend (ctx : 'env context) t1 = visit_'t (#outer ctx) t1
fun visit_rebind visit_'p extend (ctx : 'env context) p1 = visit_'p extend {outer = !(#current ctx), current = #current ctx} p1
    
fun visit_inner visit_'t = visit_rebind (visit_outer visit_'t)
fun visit_bind visit_'p visit_'t = visit_abs (visit_pair visit_'p (visit_inner visit_'t))
fun visit_anno_bind visit_'bn visit_'anno visit_'t = visit_bind (visit_pair (visit_binder visit_'bn) (visit_outer visit_'anno)) visit_'t

fun extend_noop this env x1 = (env, x1)
val visit_noop = return3
fun visit_imposs msg _ _ _ = raise Impossible ""
                           
datatype ('c, 'fn) expr =
         EConst of 'c
         | EApp of ('c, 'fn) expr * ('c, 'fn) expr
         | EVar of 'fn
         | EAbs of (bn, ty, ('c, 'fn) expr) anno_bind
                (* ((bn binder * ty outer) * ('c, 'fn) expr outer rebind) abs *)

(* using record types and recursive types (datatypes) to mimic object-oriented programming (dynamic dispatching and inheritance) *)

(* All behaviors are defined by virtual tables (vtables). *)
type ('this, 'c, 'fn, 'c2, 'fn2, 'env) expr_visitor_vtable =
     {
       visit_expr : 'this -> 'env -> ('c, 'fn) expr -> ('c2, 'fn2) expr,
       visit_EConst : 'this -> 'env -> 'c -> ('c2, 'fn2) expr,
       visit_EApp : 'this -> 'env -> ('c, 'fn) expr * ('c, 'fn) expr -> ('c2, 'fn2) expr,
       visit_EVar : 'this -> 'env -> 'fn -> ('c2, 'fn2) expr,
       visit_EAbs : 'this -> 'env -> (bn, ty, ('c, 'fn) expr) anno_bind -> ('c2, 'fn2) expr,
       visit_'c : 'this -> 'env -> 'c -> 'c2,
       visit_'fn : 'this -> 'env -> 'fn -> 'fn2,
       visit_ty : 'this -> 'env -> ty -> ty,
       visit_bn : 'this -> 'env -> string -> string,
       visit_anno_bind : 'this -> ('env -> bn -> bn) -> ('env -> ty -> ty) -> ('env -> ('c, 'fn) expr -> ('c2, 'fn2) expr) -> ('env -> bn -> 'env * bn) -> 'env -> (bn, ty, ('c, 'fn) expr) anno_bind -> (bn, ty, ('c2, 'fn2) expr) anno_bind,
       extend : 'this -> 'env -> bn -> 'env * bn
     }
       
(* This is the expression visitor interface. An interface is a record where the carrier type ['this] is unknown but we know it has the desired methods. *)
(* Only interfaces can be inherited, overrode and extended. *)
type ('this, 'c, 'fn, 'c2, 'fn2, 'env) expr_visitor_interface =
     ('this, 'c, 'fn, 'c2, 'fn2, 'env) expr_visitor_vtable

(* Always implement runtime behaviors as vtables in terms of interface, so it can be inherited, overrode and extended. *)
(* [cast] is a coercion to mimic subtyping or subclassing *)
fun default_expr_visitor_vtable
      (cast : 'this -> ('this, 'c, 'fn, 'c2, 'fn2, 'env) expr_visitor_interface)
      extend
      visit_'c
      visit_'fn
      visit_ty
    : ('this, 'c, 'fn, 'c2, 'fn2, 'env) expr_visitor_vtable =
  let
    fun visit_expr this env data =
      let
        val vtable = cast this
      in
        case data of
            EConst data => #visit_EConst vtable this env data
          | EApp data => #visit_EApp vtable this env data
          | EVar data => #visit_EVar vtable this env data
          | EAbs data => #visit_EAbs vtable this env data
      end
    fun visit_EConst this env data =
      let
        val vtable = cast this
      in
        EConst $ #visit_'c vtable this env data
      end
    fun visit_EApp this env data = 
      let
        val vtable = cast this
        val (e1, e2) = data
        val e1 = #visit_expr vtable this env e1
        val e2 = #visit_expr vtable this env e2
      in
        EApp (e1, e2)
      end
    fun visit_EVar this env data =
      let
        val vtable = cast this
      in
        EVar $ #visit_'fn vtable this env data
      end
    fun visit_EAbs this env data =
      let
        val vtable = cast this
      in
        EAbs $ #visit_anno_bind vtable this (#visit_bn vtable this) (#visit_ty vtable this) (#visit_expr vtable this) (#extend vtable this) env data
      end
    fun default_visit_anno_bind this = visit_anno_bind
    val visit_bn = visit_imposs "visit_bn()"
  in
    {visit_expr = visit_expr,
     visit_EConst = visit_EConst,
     visit_EApp = visit_EApp,
     visit_EVar = visit_EVar,
     visit_EAbs = visit_EAbs,
     visit_'c = visit_'c,
     visit_'fn = visit_'fn,
     visit_ty = visit_ty,
     visit_bn = visit_bn,
     visit_anno_bind = default_visit_anno_bind,
     extend = extend
    }
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

fun override_visit_EVar (record : ('this, 'c, 'fn, 'c2, 'fn2, 'env) expr_visitor_vtable) new : ('this, 'c, 'fn, 'c2, 'fn2, 'env) expr_visitor_vtable =
  {visit_expr = #visit_expr record,
   visit_EConst = #visit_EConst record,
   visit_EApp = #visit_EApp record,
   visit_EVar = new,
   visit_EAbs = #visit_EAbs record,
   visit_'c = #visit_'c record,
   visit_'fn = #visit_'fn record,
   visit_bn = #visit_bn record,
   visit_ty = #visit_ty record,
   visit_anno_bind = #visit_anno_bind record,
   extend = #extend record
  }

fun override_visit_'c (record : ('this, 'c, 'fn, 'c2, 'fn2, 'env) expr_visitor_vtable) new : ('this, 'c, 'fn, 'c2, 'fn2, 'env) expr_visitor_vtable =
  {visit_expr = #visit_expr record,
   visit_EConst = #visit_EConst record,
   visit_EApp = #visit_EApp record,
   visit_EVar = #visit_EVar record,
   visit_EAbs = #visit_EAbs record,
   visit_'c = new,
   visit_'fn = #visit_'fn record,
   visit_bn = #visit_bn record,
   visit_ty = #visit_ty record,
   visit_anno_bind = #visit_anno_bind record,
   extend = #extend record
  }

(***************** the "strip" visitor  **********************)    
    
(* Always implement runtime behaviors in terms of interface, so it can be inherited, overrode and extended. *)
fun strip_expr_visitor_vtable cast : ('this, 'c, 'fn, unit, 'fn, 'env) expr_visitor_vtable =
  let
    fun visit_'c _ _ _ = ()
  in
    default_expr_visitor_vtable cast extend_noop visit_'c visit_noop visit_noop
  end

(* This is the expression visitor class. A class determines the real memory layout. It is not parametrized on a carrier type so it is closed and cannot be inherited, overrode or extended. *)    
datatype ('c, 'fn, 'c2, 'fn2, 'env) expr_visitor =
         ExprVisitor of (('c, 'fn, 'c2, 'fn2, 'env) expr_visitor, 'c, 'fn, 'c2, 'fn2, 'env) expr_visitor_interface

fun expr_visitor_impls_interface (this : ('c, 'fn, 'c2, 'fn2, 'env) expr_visitor) :
    (('c, 'fn, 'c2, 'fn2, 'env) expr_visitor, 'c, 'fn, 'c2, 'fn2, 'env) expr_visitor_interface =
  let
    val ExprVisitor vtable = this
  in
    vtable
  end

(* create a real visitor in memory *)
fun new_strip_expr_visitor () =
  let
    val vtable = strip_expr_visitor_vtable expr_visitor_impls_interface
  in
    ExprVisitor vtable
  end
    
fun strip e =
  let
    val visitor as (ExprVisitor vtable) = new_strip_expr_visitor ()
  in
    #visit_expr vtable visitor () e
  end
    
type ('this, 'c, 'fn, 'env) number_expr_visitor_interface =
         {
           vtable : ('this, 'c, 'fn, int, 'fn, 'env) expr_visitor_vtable,
           count : int ref
         }

(***************** the "number" visitor  **********************)    
    
fun number_expr_visitor_refines_expr_visitor (cast : 'this -> ('this, 'c, 'fn, 'env) number_expr_visitor_interface) (this : 'this) : ('this, 'c, 'fn, int, 'fn, 'env) expr_visitor_interface =
  let
    val record = cast this
    val vtable = #vtable record
  in
    vtable
  end

fun number_expr_visitor_vtable cast : ('this, 'c, 'fn, int, 'fn, 'env) expr_visitor_vtable =
  let
    fun visit_'c this _ _ =
      let
        val record = cast this
        val count = #count record
        val old = !count
        val () = count := old + 1
      in
        old
      end
  in
    default_expr_visitor_vtable (number_expr_visitor_refines_expr_visitor cast) extend_noop visit_'c visit_noop visit_noop
  end

datatype ('c, 'fn, 'env) number_expr_visitor =
         NumberExprVisitor of (('c, 'fn, 'env) number_expr_visitor, 'c, 'fn, 'env) number_expr_visitor_interface

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

fun new_number_expr_visitor () =
  let
    val vtable = number_expr_visitor_vtable number_expr_visitor_impls_interface
    val count = ref 0
  in
    NumberExprVisitor {vtable = vtable,
                       count = count
                      }
  end
                                  
fun number e =
  let
    val visitor as (NumberExprVisitor record) = new_number_expr_visitor ()
    val vtable = #vtable record
  in
    #visit_expr vtable visitor () e
  end

(***************** a variant of the "number" visitor  **********************)    
    
fun number2_expr_visitor_vtable (cast : 'this -> ('this, 'c, 'fn, 'env) number_expr_visitor_interface) : ('this, 'c, 'fn, int, 'fn, 'env) expr_visitor_vtable =
  let
    val vtable = number_expr_visitor_vtable cast
    fun visit_'c this env data = #visit_'c vtable this env data + 10000
    val vtable = override_visit_'c vtable visit_'c
  in
    vtable
  end

fun new_number2_expr_visitor () =
  let
    val vtable = number2_expr_visitor_vtable number_expr_visitor_impls_interface
    val count = ref 0
  in
    NumberExprVisitor {vtable = vtable,
                       count = count
                      }
  end
                                  
fun number2 e =
  let
    val visitor as (NumberExprVisitor record) = new_number2_expr_visitor ()
    val vtable = #vtable record
  in
    #visit_expr vtable visitor () e
  end

(***************** the "import" (or name-resolving) visitor: converting nameful terms to de Bruijn indices **********************)    
    
exception Unbound of string
                       
fun import_expr_visitor_vtable cast : ('this, 'c, string, 'c, int, string list) expr_visitor_vtable =
  let
    fun extend this env x1 = (x1 :: env, x1)
    fun visit_'fn this env x = find_idx x env !! (fn () => raise Unbound x)
  in
    default_expr_visitor_vtable cast extend visit_noop visit_'fn visit_noop
  end

fun new_import_expr_visitor () =
  let
    val vtable = import_expr_visitor_vtable expr_visitor_impls_interface
  in
    ExprVisitor vtable
  end
    
fun import ctx e =
  let
    val visitor as (ExprVisitor vtable) = new_import_expr_visitor ()
  in
    #visit_expr vtable visitor ctx e
  end
    
(***************** the "export" visitor: convertnig de Bruijn indices to nameful terms **********************)    
    
fun export_expr_visitor_vtable cast : ('this, 'c, int, 'c, string, string list) expr_visitor_vtable =
  let
    fun extend this env x1 = (x1 :: env, x1)
    fun visit_'fn this env x = nth_error env x !! (fn () => raise Unbound $ str_int x)
  in
    default_expr_visitor_vtable cast extend visit_noop visit_'fn visit_noop
  end

fun new_export_expr_visitor () =
  let
    val vtable = export_expr_visitor_vtable expr_visitor_impls_interface
  in
    ExprVisitor vtable
  end
    
fun export ctx e =
  let
    val visitor as (ExprVisitor vtable) = new_export_expr_visitor ()
  in
    #visit_expr vtable visitor ctx e
  end
    
(***************** the "shift" visitor  **********************)    
    
fun shift_expr_visitor_vtable cast n : ('this, 'c, int, 'c, int, int) expr_visitor_vtable =
  let
    fun extend this env x1 = (1 + env, x1)
    fun visit_'fn this env data = ShiftUtil.shiftx_int env n data
  in
    default_expr_visitor_vtable cast extend visit_noop visit_'fn visit_noop
  end

fun new_shift_expr_visitor params =
  let
    val vtable = shift_expr_visitor_vtable expr_visitor_impls_interface params
  in
    ExprVisitor vtable
  end
    
fun shift x n e =
  let
    val visitor as (ExprVisitor vtable) = new_shift_expr_visitor n
  in
    #visit_expr vtable visitor x e
  end
    
(***************** the "subst" visitor  **********************)    
    
fun subst_expr_visitor_vtable cast (d, x, v) : ('this, 'c, int, 'c, int, int) expr_visitor_vtable =
  let
    fun extend this env x1 = (1 + env, x1)
    val visit_'fn = visit_imposs "visit_'fn()"
    fun visit_EVar this env y =
      let
        val x = x + env
        val d = d + env
      in
        if y = x then
          shift 0 d v
        else if y > x then
          EVar (y - 1)
        else
          EVar y
      end
    val vtable = default_expr_visitor_vtable cast extend visit_noop visit_'fn visit_noop
    val vtable = override_visit_EVar vtable visit_EVar
  in
    vtable
  end

fun new_subst_expr_visitor params =
  let
    val vtable = subst_expr_visitor_vtable expr_visitor_impls_interface params
  in
    ExprVisitor vtable
  end
    
fun subst d x v e =
  let
    val visitor as (ExprVisitor vtable) = new_subst_expr_visitor (d, x, v)
  in
    #visit_expr vtable visitor 0 e
  end
    
(***************** tests  **********************)    

fun test () =
  let
    val e = EApp (EApp (EConst "A", EConst "B"), EConst "C")
                 
    val e1 = strip e
    val e2 = number e
    val e3 = number2 e

    val e = EAbs (("x", TInt), EAbs (("y", TInt), EApp (EVar "x", EVar "y")))

    val e4 = import [] e
    val e5 = export [] e4
                    
    val e = EAbs (("x", TInt), EAbs (("y", TInt), EApp (EVar "x", EVar "z")))

    val e6 = import ["z", "w"] e
    val e7 = shift 0 1 e6
    val e8 = shift 1 1 e6

    val e9 = subst 0 0 e6 e6
  in
    (e1, e2, e3, e4, e5, e6, e7, e8, e9)
  end
                   
end
