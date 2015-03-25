Require Import List.
Require Import Util.
Require Import Complexity.

Export Complexity.

Inductive type : context -> Type :=
| Tarrow {ctx} : type ctx -> cexpr (CEexpr :: ctx) -> size (CEexpr :: ctx) ->  type (CEexpr :: ctx) -> type ctx
(* polymorphism *)           
| Tvar {ctx} : var ctx CEtype -> type ctx
| Tuniversal {ctx} : cexpr ctx -> size ctx -> type (CEtype :: ctx) -> type ctx
(* higher-order operators *)
| Tabs {ctx} : type (CEtype :: ctx) -> type ctx
| Tapp {ctx} : type ctx -> type ctx -> type ctx
(* recursive types *)         
| Trecur {ctx} : type (CEtype :: ctx) -> type ctx
(* to deal with statistics s2 and s3 *)
| Thide {ctx} : type ctx -> type ctx
(* basic types *)
| Tunit {ctx} : type ctx
| Tprod {ctx} : type ctx -> type ctx -> type ctx
| Tsum {ctx} : type ctx -> type ctx -> type ctx
.

Coercion Tvar : var >-> type.

Inductive expr : context -> Type :=
| Evar {ctx} : var ctx CEexpr -> expr ctx
| Eapp {ctx} : expr ctx -> expr ctx -> expr ctx
| Eabs {ctx} : type ctx -> expr (CEexpr :: ctx) -> expr ctx
| Elet {ctx} : expr ctx -> expr (CEexpr :: ctx) -> expr ctx
| Etapp {ctx} : expr ctx -> type ctx -> expr ctx
| Etabs {ctx} : expr (CEtype :: ctx) -> expr ctx
| Efold {ctx} : type ctx -> expr ctx -> expr ctx
| Eunfold {ctx} : expr ctx -> expr ctx
| Ehide {ctx} : expr ctx -> expr ctx
| Eunhide {ctx} : expr ctx -> expr ctx
| Ett {ctx} : expr ctx
| Epair {ctx} : expr ctx -> expr ctx -> expr ctx
| Einl {ctx} : type ctx -> expr ctx -> expr ctx
| Einr {ctx} : type ctx -> expr ctx -> expr ctx
| Ematch_pair {ctx} : expr ctx -> expr (CEexpr :: CEexpr :: ctx)
| Ematch_sum {ctx} : expr ctx -> expr (CEexpr :: ctx) -> expr (CEexpr :: ctx) -> expr ctx
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
