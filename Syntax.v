Require Import Complexity.

Export Complexity.

Inductive tconstr :=
| TCunit
| TCprod
| TCsum
(* | TCint *)
.

Inductive type :=
| Tarrow (t1 : type) (time_cost : cexpr) (result_size : size) (t2 : type)
(* basic types *)
| Tconstr (_ : tconstr)
(* polymorphism *)           
| Tvar (x : var)
| Tuniversal (time_cost : cexpr) (result_size : size) (t : type)
(* higher-order operators *)
| Tabs (t : type)
| Tapp (a b : type)
(* recursive types *)         
| Trecur (t : type)
(* to deal with statistics s2 and s3 *)
| Thide (_ : type)
.

Coercion Tvar : var >-> type.

Inductive constr :=
| Ctt
| Cpair
| Cinl
| Cinr
.

Inductive expr :=
  | Evar (x : var)
  | Econstr (c : constr)
  | Eapp (f : expr) (arg : expr)
  | Eabs (t : type) (body : expr)
  | Elet (t : type) (def : expr) (main : expr)
  (* 'Definition' means the RHS of := in letrec.
     Each definition must be a function, so there is an implicit quantifier on the RHS of :=. The LHS of := are also implicitly quantified. For example:
     letrec x := \a. a * x (a - 1) with
            y := \b. b * y (b - 1) in
            x 10 + y 20
     is written as 
     letrec #0 * #2 (#0 - 1) with   (#2, #1, #0 -> x, y, a)
            #0 * #1 (#0 - 1) in     (#2, #1, #0 -> x, y, b)
            #1 10 + #0 10           (#1, #0 -> x, y)  
     This must-be-function restriction is necessary for the type system to work 
   *)
  | Eletrec (defs : list (type * type * expr)) (main : expr)
  (* The handler can access #1 and #0 representing the components of the pair
   *)              
  | Ematch_pair (target : expr) (handler : expr)
  (* left and right can access #0 representing the corresponding payload *)
  | Ematch_sum (target : expr) (left right : expr)
  (* | Eabs_notype (e : expr) (* a version of Eabs used in match handlers, where type annotation is not needed *) *)
  | Etapp (e : expr) (t : type)
  | Etabs (body : expr)
  | Efold (_ : type) (_ : expr)
  | Eunfold (_ : type) (_ : expr)
  | Ehide (_ : expr)
  | Eunhide (_ : expr)
.

Definition letrec_entry := (type * type * expr)%type.

Coercion Evar : var >-> expr.
Coercion Econstr : constr >-> expr.

