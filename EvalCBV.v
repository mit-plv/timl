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

(* expression context *)
Inductive econtext ctx : Type :=
| ECempty : econtext ctx
| ECapp1 (f : econtext ctx) (arg : expr ctx) : econtext ctx
| ECapp2 (f : expr ctx) (arg : econtext ctx) : econtext ctx
| ECtapp (f : econtext ctx) (t : type ctx)  : econtext ctx
| ECfold (t : type ctx) (_ : econtext ctx) : econtext ctx
| ECunfold (_ : econtext ctx) : econtext ctx
| EChide (_ : econtext ctx) : econtext ctx
| ECunhide (_ : econtext ctx) : econtext ctx
| ECpair1 (a : econtext ctx) (b : expr ctx) : econtext ctx
| ECpair2 (a : expr ctx) (b : econtext ctx) : econtext ctx
| ECinl (_ : type ctx) (_ : econtext ctx) : econtext ctx
| ECinr (_ : type ctx) (_ : econtext ctx) : econtext ctx
| ECfst (_ : econtext ctx) : econtext ctx
| ECsnd (_ : econtext ctx) : econtext ctx
| ECmatch (target : econtext ctx) (t : type ctx) (s : size ctx) (a b : expr (CEexpr :: ctx)) : econtext ctx
.

Arguments ECempty {ctx} .

(* evaluation context *)
Inductive IsEC {ctx} : econtext ctx -> Prop :=
| IECempty : IsEC ECempty
| IECapp1 (f : econtext ctx) (arg : expr ctx) : IsEC f ->IsEC (ECapp1 f arg)
| IECapp2 (f : expr ctx) (arg : econtext ctx) : IsValue f -> IsEC arg -> IsEC (ECapp2 f arg)
| IECtapp (f : econtext ctx) (t : type ctx)  : IsEC f -> IsEC (ECtapp f t)
| IECfold (t : type ctx) (e : econtext ctx) : IsEC e -> IsEC (ECfold t e)
| IECunfold (e : econtext ctx) : IsEC e -> IsEC (ECunfold e)
| IEChide (e : econtext ctx) : IsEC e -> IsEC (EChide e)
| IECunhide (e : econtext ctx) : IsEC e -> IsEC (ECunhide e)
| IECpair1 (a : econtext ctx) (b : expr ctx) : IsEC a -> IsEC (ECpair1 a b)
| IECpair2 (a : expr ctx) (b : econtext ctx) : IsValue a -> IsEC b -> IsEC (ECpair2 a b)
| IECinl (t : type ctx) (e : econtext ctx) : IsEC e -> IsEC (ECinl t e)
| IECinr (t : type ctx) (e : econtext ctx) : IsEC e -> IsEC (ECinr t e)
| IECfst (e : econtext ctx) : IsEC e -> IsEC (ECfst e)
| IECsnd (e : econtext ctx) : IsEC e -> IsEC (ECsnd e)
| IECmatch (target : econtext ctx) (t : type ctx) (s : size ctx) (a b : expr (CEexpr :: ctx)) : IsEC target -> IsEC (ECmatch target t s a b)
.

(* Both Fixpoint and Inductive version of plug are useful *)
Fixpoint plug {ctx} (c : econtext ctx) (e : expr ctx) : expr ctx :=
  match c with
    | ECempty => e
    | ECapp1 f arg => Eapp (plug f e) arg
    | ECapp2 f arg => Eapp f (plug arg e)
    | ECtapp f t => Etapp (plug f e) t
    | ECfold t c => Efold t (plug c e)
    | ECunfold c => Eunfold (plug c e)
    | EChide c => Ehide (plug c e)
    | ECunhide c => Eunhide (plug c e)
    | ECpair1 a b => Epair (plug a e) b
    | ECpair2 a b => Epair a (plug b e)
    | ECinl t c => Einl t (plug c e)
    | ECinr t c => Einr t (plug c e)
    | ECfst c => Efst (plug c e)
    | ECsnd c => Esnd (plug c e)
    | ECmatch target t s a b => Ematch (plug target e) t s a b
  end.

(* (n, e) ~> (n', e'), n is the "fuel" *)
Inductive step : nat -> expr [] -> nat -> expr [] -> Prop :=
| STecontext E n1 e1 n2 e2 : 
    step n1 e1 n2 e2 -> 
    IsEC E ->
    step n1 (plug E e1) n2 (plug E e2)
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
.

