Require Import List.
Require Import Util.
Require Import Syntax.
Require Import Subst.

Export Syntax.

Import ListNotations.
Local Open Scope list_scope.
Local Open Scope prog_scope.

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
| EClet (t : type) (def : econtext) (main : expr)
| ECtapp (f : econtext) (t : type)
| ECfold (t : type) (_ : econtext)
| ECunfold (_ : econtext)
| EChide (_ : econtext)
| ECunhide (_ : econtext)
| ECpair1 (a : econtext) (b : expr)
| ECpair2 (a : expr) (b : econtext) : IsValue a -> econtext
| ECinl (_ : type) (_ : econtext)
| ECinr (_ : type) (_ : econtext)
| ECmatch_pair (target : econtext) (_ : expr)
| ECmatch_sum (target : econtext) (a b : expr)
.

Inductive plug : econtext -> expr -> expr -> Prop :=
| Pempty e : plug ECempty e e
| Papp1 E e f arg : plug E e f -> plug (ECapp1 E arg) e (Eapp f arg)
| Papp2 E e arg f h : plug E e arg -> plug (ECapp2 f E h) e (Eapp f arg)
| Plet E e def t main : plug E e def -> plug (EClet t E main) e (Elet t def main)
| Ptapp E e f t : plug E e f -> plug (ECtapp E t) e (Etapp f t)
| Pfold E e e' t : plug E e e' -> plug (ECfold t E) e (Efold t e')
| Punfold E e e' : plug E e e' -> plug (ECunfold E) e (Eunfold e')
| Phide E e e' : plug E e e' -> plug (EChide E) e (Ehide e')
| Punhide E e e' : plug E e e' -> plug (ECunhide E) e (Eunhide e')
| Ppair1 E e a b : plug E e a -> plug (ECpair1 E b) e (Epair a b)
| Ppair2 E e b a h : plug E e b -> plug (ECpair2 a E h) e (Epair a b)
| Pinl E e e' t : plug E e e' -> plug (ECinl t E) e (Einl t e')
| Pinr E e e' t : plug E e e' -> plug (ECinr t E) e (Einr t e')
| Pmatch_pair E e target k : plug E e target -> plug (ECmatch_pair E k) e (Ematch_pair target k)
| Pmatch_sum E e target k1 k2 : plug E e target -> plug (ECmatch_sum E k1 k2) e (Ematch_sum target k1 k2)
.

(*
Fixpoint plug (c : econtext) (e : expr) : expr :=
  match c with
    | ECempty => e
    | ECapp1 f arg => Eapp (plug f e) arg
    | ECapp2 f arg _ => Eapp f (plug arg e)
    | EClet t def main => Elet t (plug def e) main
    | ECtapp f t => Etapp (plug f e) t
    | ECfold t c => Efold t (plug c e)
    | ECunfold c => Eunfold (plug c e)
    | EChide c => Ehide (plug c e)
    | ECunhide c => Eunhide (plug c e)
    | ECpair1 a b => Epair (plug a e) b
    | ECpair2 a b _ => Epair a (plug b e)
    | ECinl t c => Einl t (plug c e)
    | ECinr t c => Einr t (plug c e)
    | ECmatch_pair target k => Ematch_pair (plug target e) k
    | ECmatch_sum target a b => Ematch_sum (plug target e) a b
  end.
*)

Inductive step : expr -> expr -> Prop :=
| STecontext E e1 e2 e1' e2' : 
    step e1 e2 -> 
    plug E e1 e1' -> 
    plug E e2 e2' -> 
    step e1' e2'
| STapp t body arg : IsValue arg -> step (Eapp (Eabs t body) arg) (subst arg body)
| STlet t v main : IsValue v -> step (Elet t v main) (subst v main)
| STmatch_pair t1 t2 v1 v2 k : 
    IsValue v1 ->
    IsValue v2 ->
    step (Ematch_pair (Epair $$ t1 $$ t2 $$ v1 $$ v2) k) (subst_list [v1; v2] k)
| STmatch_inl t1 t2 v k1 k2 : 
    IsValue v ->
    step (Ematch_sum (Einl $$ t1 $$ t2 $$ v) k1 k2) (subst v k1)
| STmatch_inr t1 t2 v k1 k2 : 
    IsValue v ->
    step (Ematch_sum (Einr $$ t1 $$ t2 $$ v) k1 k2) (subst v k2)
| STtapp body t : step (Etapp (Etabs body) t) (subst t body)
| STunfold_fold v t1 : 
    IsValue v ->
    step (Eunfold (Efold t1 v)) v
| STunhide_hide v :
    IsValue v ->
    step (Eunhide (Ehide v)) v
.

