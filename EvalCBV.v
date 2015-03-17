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

Inductive step : expr -> expr -> Prop :=
  | STecontext c e1 e2 : step e1 e2 -> step (plug c e1) (plug c e2)
  | STapp t body arg : IsValue arg -> step (Eapp (Eabs t body) arg) (subst arg body)
  | STlet t v main : IsValue v -> step (Elet t v main) (subst v main)
  | STmatch_pair ta tb a b k : 
      IsValue a ->
      IsValue b ->
      step (Ematch_pair (Epair $$ ta $$ tb $$ a $$ b) k) (subst_list [a; b] k)
  | STmatch_inl ta tb v k1 k2 : 
      IsValue v ->
      step (Ematch_sum (Einl $$ ta $$ tb $$ v) k1 k2) (subst v k1)
  | STmatch_inr ta tb v k1 k2 : 
      IsValue v ->
      step (Ematch_sum (Einr $$ ta $$ tb $$ v) k1 k2) (subst v k2)
  | STtapp body t : step (Etapp (Etabs body) t) (subst t body)
  | STunfold_fold v t1 : 
      IsValue v ->
      step (Eunfold (Efold t1 v)) v
  | STunhide_hide v :
      IsValue v ->
      step (Eunhide (Ehide v)) v
.

