Set Maximal Implicit Insertion.
Set Implicit Arguments.

Require Import List.
Require Import Util.
Require Import Syntax.
Require Import Subst.

Export Syntax.

Import ListNotations.
Local Open Scope list_scope.
Local Open Scope prog_scope.

Inductive IsValue {ctx} : expr ctx -> Prop :=
| Vvar x : IsValue (Evar x)
| Vabs t e : IsValue (Eabs t e)
| Vtabs e : IsValue (Etabs e)
| Vfold t v : IsValue v -> IsValue (Efold t v)
| Vhide v : IsValue v -> IsValue (Ehide v)
| Vtt : IsValue Ett
| Vpair a b : IsValue a -> IsValue b -> IsValue (Epair a b)
| Vinl t v : IsValue v -> IsValue (Einl t v)
| Vinr t v : IsValue v -> IsValue (Einr t v)
.

(* (n, e) ~> (n', e'), n is the "fuel" *)
Inductive step : nat -> expr [] -> nat -> expr [] -> Prop :=
| STapp n t body arg : IsValue arg -> step (1 + n) (Eapp (Eabs t body) arg) n (subst arg body)
| STfst n v1 v2 :
    IsValue v1 ->
    IsValue v2 ->
    step (1 + n) (Efst (Epair v1 v2)) n v1
| STsnd n v1 v2 :
    IsValue v1 ->
    IsValue v2 ->
    step (1 + n) (Esnd (Epair v1 v2)) n v2
| STmatch_inl n t' v t s k1 k2 : 
    IsValue v ->
    step (1 + n) (Ematch (Einl t' v) t s k1 k2) n (subst v k1)
| STmatch_inr n t' v t s k1 k2 : 
    IsValue v ->
    step (1 + n) (Ematch (Einr t' v) t s k1 k2) n (subst v k2)
| STtapp n body t : step (1 + n) (Etapp (Etabs body) t) n (subst t body)
| STunfold_fold n v t1 : 
    IsValue v ->
    step (1 + n) (Eunfold (Efold t1 v)) n v
| STunhide_hide n v :
    IsValue v ->
    step (1 + n) (Eunhide (Ehide v)) n v
(* contextual cases *)
| STcapp1 n e1 n' e1' e2 :
    step n e1 n' e1' ->
    step n (Eapp e1 e2) n' (Eapp e1' e2)
| STcapp2 v n e n' e':
    IsValue v ->
    step n e n' e' ->
    step n (Eapp v e) n' (Eapp v e')
| STctapp n e n' e' t :
    step n e n' e' ->
    step n (Etapp e t) n' (Etapp e' t)
| STcfold n e n' e' t :
    step n e n' e' ->
    step n (Efold t e) n' (Efold t e')
| STcunfold n e n' e' :
    step n e n' e' ->
    step n (Eunfold e) n' (Eunfold e')
| STchide n e n' e' :
    step n e n' e' ->
    step n (Ehide e) n' (Ehide e')
| STcunhide n e n' e' :
    step n e n' e' ->
    step n (Eunhide e) n' (Eunhide e')
| STcpair1 n e1 n' e1' e2 :
    step n e1 n' e1' ->
    step n (Epair e1 e2) n' (Epair e1' e2)
| STcpair2 v n e n' e' :
    IsValue v ->
    step n e n' e' ->
    step n (Epair v e) n' (Epair v e')
| STcinl n e n' e' t :
    step n e n' e' ->
    step n (Einl t e) n' (Einl t e')
| STcinr n e n' e' t :
    step n e n' e' ->
    step n (Einr t e) n' (Einr t e')
| STcfst n e n' e' :
    step n e n' e' ->
    step n (Efst e) n' (Efst e')
| STcsnd n e n' e' :
    step n e n' e' ->
    step n (Esnd e) n' (Esnd e')
| STcmatch n e n' e' t s e1 e2 :
    step n e n' e' ->
    step n (Ematch e t s e1 e2) n' (Ematch e' t s e1 e2)
.
