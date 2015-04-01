Require Import List.
Require Import Util.
Require Import Syntax.
Require Import Subst.

Export Syntax.

Import ListNotations.
Local Open Scope list_scope.
Local Open Scope prog_scope.

Local Notation open_type := type.
Local Notation open_expr := expr.
Local Notation type := (open_type []).
Local Notation expr := (open_expr []).

Inductive IsValue : expr -> Prop :=
| Vvar x : IsValue (Evar x)
| Vabs t e : IsValue (Eabs t e)
| Vtabs e : IsValue (Etabs e)
| Vfold t v : IsValue v -> IsValue (Efold t v)
| Vtt : IsValue Ett
| Vpair a b : IsValue a -> IsValue b -> IsValue (Epair a b)
| Vinl t v : IsValue v -> IsValue (Einl t v)
| Vinr t v : IsValue v -> IsValue (Einr t v)
.

(* evaluation context *)
Inductive econtext :=
| ECempty
| ECapp1 (f : econtext) (arg : expr)
| ECapp2 (f : expr) (arg : econtext) : IsValue f -> econtext
| EClet (def : econtext) (main : open_expr [CEexpr])
| ECtapp (f : econtext) (t : type)
| ECfold (t : type) (_ : econtext)
| ECunfold (_ : econtext)
| EChide (_ : econtext)
| ECunhide (_ : econtext)
| ECpair1 (a : econtext) (b : expr)
| ECpair2 (a : expr) (b : econtext) : IsValue a -> econtext
| ECinl (_ : type) (_ : econtext)
| ECinr (_ : type) (_ : econtext)
| ECfst (_ : econtext)
| ECsnd (_ : econtext)
| ECmatch (target : econtext) (a b : open_expr [CEexpr])
.

Inductive plug : econtext -> expr -> expr -> Prop :=
| Pempty e : plug ECempty e e
| Papp1 E e f arg : plug E e f -> plug (ECapp1 E arg) e (Eapp f arg)
| Papp2 E e arg f h : plug E e arg -> plug (ECapp2 f E h) e (Eapp f arg)
| Plet E e def main : plug E e def -> plug (EClet E main) e (Elet def main)
| Ptapp E e f t : plug E e f -> plug (ECtapp E t) e (Etapp f t)
| Pfold E e e' t : plug E e e' -> plug (ECfold t E) e (Efold t e')
| Punfold E e e' : plug E e e' -> plug (ECunfold E) e (Eunfold e')
| Phide E e e' : plug E e e' -> plug (EChide E) e (Ehide e')
| Punhide E e e' : plug E e e' -> plug (ECunhide E) e (Eunhide e')
| Ppair1 E e a b : plug E e a -> plug (ECpair1 E b) e (Epair a b)
| Ppair2 E e b a h : plug E e b -> plug (ECpair2 a E h) e (Epair a b)
| Pinl E e e' t : plug E e e' -> plug (ECinl t E) e (Einl t e')
| Pinr E e e' t : plug E e e' -> plug (ECinr t E) e (Einr t e')
| Pfst E e e' : plug E e e' -> plug (ECfst E) e (Efst e')
| Psnd E e e' : plug E e e' -> plug (ECsnd E) e (Esnd e')
| Pmatch E e target k1 k2 : plug E e target -> plug (ECmatch E k1 k2) e (Ematch target k1 k2)
.

Inductive step : expr -> expr -> Prop :=
| STecontext E e1 e2 e1' e2' : 
    step e1 e2 -> 
    plug E e1 e1' -> 
    plug E e2 e2' -> 
    step e1' e2'
| STapp t body arg : IsValue arg -> step (Eapp (Eabs t body) arg) (subst arg body)
| STlet v main : IsValue v -> step (Elet v main) (subst v main)
| STfst v1 v2 :
    IsValue v1 ->
    IsValue v2 ->
    step (Efst (Epair v1 v2)) v1
| STsnd v1 v2 :
    IsValue v1 ->
    IsValue v2 ->
    step (Esnd (Epair v1 v2)) v2
| STmatch_inl t v k1 k2 : 
    IsValue v ->
    step (Ematch (Einl t v) k1 k2) (subst v k1)
| STmatch_inr t v k1 k2 : 
    IsValue v ->
    step (Ematch (Einr t v) k1 k2) (subst v k2)
| STtapp body t : step (Etapp (Etabs body) t) (subst t body)
| STunfold_fold v t1 : 
    IsValue v ->
    step (Eunfold (Efold t1 v)) v
| STunhide_hide v :
    IsValue v ->
    step (Eunhide (Ehide v)) v
.

