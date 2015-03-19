Require Import Util.
Require Import Complexity.

Export Complexity.

Inductive type :=
| Tarrow (t1 : type) (time_cost : cexpr) (result_size : size) (t2 : type)
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
(* basic types *)
| Tunit
| Tprod (_ _ : type)
| Tsum (_ _ : type)
.

Coercion Tvar : var >-> type.

Inductive expr :=
  | Evar (x : var)
  | Eapp (f : expr) (arg : expr)
  | Eabs (t : type) (body : expr)
  | Elet (def : expr) (main : expr)
  | Etapp (e : expr) (t : type)
  | Etabs (body : expr)
  | Efold (_ : type) (_ : expr)
  | Eunfold (_ : expr)
  | Ehide (_ : expr)
  | Eunhide (_ : expr)
  | Ett
  | Epair (_ _ : expr)
  | Einl (_ : type) (_ : expr)
  | Einr (_ : type) (_ : expr)
  | Ematch_pair (target : expr) (handler : expr)
  (* left and right can access #0 representing the corresponding payload *)
  | Ematch_sum (target : expr) (left right : expr)
  (* | Eabs_notype (e : expr) (* a version of Eabs used in match handlers, where type annotation is not needed *) *)
.

Coercion Evar : var >-> expr.

Instance Apply_type_type_type : Apply type type type :=
  {
    apply := Tapp
  }.

Instance Apply_expr_expr_expr : Apply expr expr expr :=
  {
    apply := Eapp
  }.

Instance Apply_expr_type_expr : Apply expr type expr :=
  {
    apply := Etapp
  }.

