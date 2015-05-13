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
| Vtt : IsValue Ett
| Vpair a b : IsValue a -> IsValue b -> IsValue (Epair a b)
| Vinl t v : IsValue v -> IsValue (Einl t v)
| Vinr t v : IsValue v -> IsValue (Einr t v)
.

(* evaluation context *)
Inductive econtext ctx : Type :=
| ECempty : econtext ctx
| ECapp1 (f : econtext ctx) (arg : expr ctx) : econtext ctx
| ECapp2 (f : expr ctx) (arg : econtext ctx) : IsValue f -> econtext ctx
| EClet (def : econtext ctx) (main : expr (CEexpr :: ctx)) : econtext ctx
| ECtapp (f : econtext ctx) (t : type ctx)  : econtext ctx
| ECfold (t : type ctx) (_ : econtext ctx) : econtext ctx
| ECunfold (_ : econtext ctx) : econtext ctx
| EChide (_ : econtext ctx) : econtext ctx
| ECunhide (_ : econtext ctx) : econtext ctx
| ECpair1 (a : econtext ctx) (b : expr ctx) : econtext ctx
| ECpair2 (a : expr ctx) (b : econtext ctx) : IsValue a -> econtext ctx
| ECinl (_ : type ctx) (_ : econtext ctx) : econtext ctx
| ECinr (_ : type ctx) (_ : econtext ctx) : econtext ctx
| ECfst (_ : econtext ctx) : econtext ctx
| ECsnd (_ : econtext ctx) : econtext ctx
| ECmatch (target : econtext ctx) (a b : expr (CEexpr :: ctx)) : econtext ctx
.

Arguments ECempty {ctx} .

Fixpoint plug {ctx} (c : econtext ctx) (e : expr ctx) : expr ctx :=
  match c with
    | ECempty => e
    | ECapp1 f arg => Eapp (plug f e) arg
    | ECapp2 f arg _ => Eapp f (plug arg e)
    | EClet def main => Elet (plug def e) main
    | ECtapp f t => Etapp (plug f e) t
    | ECfold t c => Efold t (plug c e)
    | ECunfold c => Eunfold (plug c e)
    | EChide c => Ehide (plug c e)
    | ECunhide c => Eunhide (plug c e)
    | ECpair1 a b => Epair (plug a e) b
    | ECpair2 a b _ => Epair a (plug b e)
    | ECinl t c => Einl t (plug c e)
    | ECinr t c => Einr t (plug c e)
    | ECfst c => Efst (plug c e)
    | ECsnd c => Esnd (plug c e)
    | ECmatch target a b => Ematch (plug target e) a b
  end.

(*
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
*)

Inductive step : expr [] -> expr [] -> Prop :=
| STecontext E e1 e2 : 
    step e1 e2 -> 
    step (plug E e1) (plug E e2)
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

