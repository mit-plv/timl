Set Maximal Implicit Insertion.
Set Implicit Arguments.

Require Import List.
Require Import Util.
Require Import Complexity.

Export Complexity.

Inductive type ctx : Type :=
| Tarrow : type ctx -> cexpr (CEexpr :: ctx) -> size (CEexpr :: ctx) ->  type (CEexpr :: ctx) -> type ctx
(* polymorphism *)           
| Tvar : var CEtype ctx -> type ctx
| Tuniversal : cexpr ctx -> size ctx -> type (CEtype :: ctx) -> type ctx
(* higher-order operators *)
| Tabs : type (CEtype :: ctx) -> type ctx
| Tapp : type ctx -> type ctx -> type ctx
(* recursive types *)         
| Trecur : type (CEtype :: ctx) -> type ctx
(* to deal with statistics s2 and s3 *)
| Thide : type ctx -> type ctx
(* basic types *)
| Tunit : type ctx
| Tprod : type ctx -> type ctx -> type ctx
| Tsum : type ctx -> type ctx -> type ctx
.

Coercion Tvar : var >-> type.

Inductive expr ctx : Type :=
| Evar : var CEexpr ctx -> expr ctx
| Eapp : expr ctx -> expr ctx -> expr ctx
| Eabs : type ctx -> expr (CEexpr :: ctx) -> expr ctx
| Elet : expr ctx -> expr (CEexpr :: ctx) -> expr ctx
| Etapp : expr ctx -> type ctx -> expr ctx
| Etabs : expr (CEtype :: ctx) -> expr ctx
| Efold : type ctx -> expr ctx -> expr ctx
| Eunfold : expr ctx -> expr ctx
| Ehide : expr ctx -> expr ctx
| Eunhide : expr ctx -> expr ctx
| Ett : expr ctx
| Epair : expr ctx -> expr ctx -> expr ctx
| Einl : type ctx -> expr ctx -> expr ctx
| Einr : type ctx -> expr ctx -> expr ctx
| Ematch_pair : expr ctx -> expr (CEexpr :: CEexpr :: ctx) -> expr ctx
| Ematch_sum : expr ctx -> expr (CEexpr :: ctx) -> expr (CEexpr :: ctx) -> expr ctx
.

Coercion Evar : var >-> expr.

Global Instance Apply_type_type_type ctx : Apply (type ctx) (type ctx) (type ctx) :=
  {
    apply := Tapp
  }.

Global Instance Apply_expr_expr_expr ctx : Apply (expr ctx) (expr ctx) (expr ctx) :=
  {
    apply := Eapp
  }.

Global Instance Apply_expr_type_expr ctx : Apply (expr ctx) (type ctx) (expr ctx) :=
  {
    apply := Etapp
  }.
