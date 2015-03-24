Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 
Generalizable All Variables.

Require Import List.
Require Import Program.
Require Import Util.
Require Import Syntax.
Require Import Subst.
Require Import Order.

Export Syntax Subst Order.

Import ListNotations.
Local Open Scope list_scope.

Instance Shift_option `{Shift A} : Shift (option A) :=
  {
    shift_from n o := option_map (shift_from n) o
  }.

Instance Shift_pair `{Shift A, Shift B} : Shift (A * B) :=
  {
    shift_from n p := (shift_from n (fst p), shift_from n (snd p))
  }.

(* kinds are restricted to the form (* => * => ... => *). 0 means * *)
Definition kind := nat.

(* Typing context.
   The second field of TEtyping is the optional size constraint
 *)
Inductive tc_entry := 
  | TEtyping (_ : type)
  | TEkinding
.

Definition tcontext := list tc_entry.

Local Open Scope prog_scope.

Definition add_typing t T := TEtyping t :: T.
Definition add_typings ls T := fst $ fold_left (fun (p : tcontext * nat) t => let (T, n) := p in (add_typing (shiftby n t) T, S n)) ls (T, 0%nat).
Definition add_kinding T := TEkinding :: T.

Coercion var_to_size (x : var) : size := Svar (x, []).

Inductive kinding : tcontext -> type -> kind -> Prop :=
| Kvar T x : find x T = Some TEkinding -> kinding T #x 0
| Kapp T t1 t2 k :
    kinding T t1 (S k) ->
    kinding T t2 0 ->
    kinding T (Tapp t1 t2) k
| Kabs T t k :
    kinding (add_kinding T) t k ->
    kinding T (Tabs t) (S k)
| Karrow T t1 c s t2 :
    kinding T t1 0 ->
    kinding (add_typing t1 T) t2 0 ->
    kinding T (Tarrow t1 c s t2) 0
| Kuniversal T c s t :
    kinding (add_kinding T) t 0 ->
    kinding T (Tuniversal c s t) 0
| Krecur T t :
    kinding (add_kinding T) t 0 ->
    kinding T (Trecur t) 0
| Khide T t :
    kinding T t 0 ->
    kinding T (Thide t) 0
| Kunit T :
    kinding T Tunit 0
| Kprod T a b :
    kinding T a 0 ->
    kinding T b 0 ->
    kinding T (Tprod a b) 0
| Ksum T a b :
    kinding T a 0 ->
    kinding T b 0 ->
    kinding T (Tsum a b) 0
.

Inductive teq : type -> type -> Prop :=
| Qrefl t : teq t t
| Qsymm a b : teq a b -> teq b a
| Qtrans a b c : teq a b -> teq b c -> teq a c
| Qabs a b :
    teq a b ->
    teq (Tabs a) (Tabs b)
| Qapp a b a' b' :
    teq a a' ->
    teq b b' ->
    teq (Tapp a b) (Tapp a' b')
| Qbeta t1 t2 :
    teq (Tapp (Tabs t1) t2) (subst t2 t1)
| Qarrow a c s b a' b' : 
    teq a a' ->
    teq b b' ->
    teq (Tarrow a c s b) (Tarrow a' c s b')
| Qrecur a b :
    teq a b ->
    teq (Trecur a) (Trecur b)
| Qprod a b a' b' :
    teq a a' ->
    teq b b' ->
    teq (Tprod a b) (Tprod a' b')
| Qsum a b a' b' :
    teq a a' ->
    teq b b' ->
    teq (Tsum a b) (Tsum a' b')
.

Global Add Relation type teq
    reflexivity proved by Qrefl
    symmetry proved by Qsymm
    transitivity proved by Qtrans
      as teq_rel.

Class Equal t :=
  {
    equal : t -> t -> Prop
  }.

Infix "==" := equal (at level 70) : G.

Instance Equal_type : Equal type :=
  {
    equal := teq
  }.

Definition add_snd {A B} (b : B) (a : A) := (a, b).

Local Open Scope F.
Local Open Scope G.

Local Open Scope prog_scope.

Notation Tuniversal0 := (Tuniversal F0 S0).

Inductive typing : tcontext -> expr -> type -> cexpr -> size -> Prop :=
| TPvar Γ x τ : 
    find x Γ = Some (TEtyping τ) -> 
    typing Γ #x (shiftby (S x) τ) F0 (var_to_size #x)
| TPapp Γ e₀ e₁ τ₁ c s τ₂ c₀ nouse c₁ s₁ : 
    typing Γ e₀ (Tarrow τ₁ c s τ₂) c₀ nouse ->
    typing Γ e₁ τ₁ c₁ s₁ ->
    typing Γ (Eapp e₀ e₁) (subst s₁ τ₂) (c₀ + c₁ + subst s₁ c) (subst s₁ s)
| TPabs T e t1 t2 c s :
    kinding T t1 0 ->
    typing (add_typing t1 T) e t2 c s ->
    typing T (Eabs t1 e) (Tarrow t1 c s t2) F0 S0
| TPtapp T e t2 c s t c' :
    typing T e (Tuniversal (shift c) (shift s) t) c' S0 ->
    typing T (Etapp e t2) (subst t2 t) (c' + c) s
| TPtabs T e c s t :
    typing (add_kinding T) e t c s ->
    typing T (Etabs e) (Tuniversal c s t) F0 S0
| TPlet T t1 e1 e2 t2 c1 c2 s1 s2:
    typing T e1 t1 c1 s1 ->
    typing (add_typing t1 T) e2 t2 c2 s2 ->
    typing T (Elet e1 e2) (subst s1 t2) (c1 + subst s1 c2) (subst s1 s2)
| TPfold T e t c s t1 :
    t == Trecur t1 ->
    typing T e (subst t t1) c s ->
    typing T (Efold t e) t c (Sfold s)
| TPunfold T e t c s s1 t1 :
    typing T e t c s ->
    is_fold s = Some s1 ->
    t == Trecur t1 ->
    typing T (Eunfold e) (subst t t1) (F1 + c) s1
| TPhide T e t c s :
    typing T e t c s ->
    typing T (Ehide e) (Thide t) c (Shide s)
| TPunhide T e t c s s1 :
    typing T e (Thide t) c s ->
    is_hide s = Some s1 ->
    typing T (Eunhide e) t c s1
| TPeq T e t1 t2 c s :
    typing T e t1 c s ->
    t1 == t2 ->
    typing T e t2 c s
| TPsub T e t c c' s s' :
    typing T e t c s ->
    c <<= c' ->
    s <= s' ->
    typing T e t c' s'
(* basic types - intro *)
| TPtt T :
    typing T Ett Tunit F0 S0
| TPpair T e1 t1 c1 s1 e2 t2 c2 s2 : 
    typing T e1 t1 c1 s1 ->
    typing T e2 t2 c2 s2 ->
    typing T (Epair e1 e2) (Tprod t1 t2) (c1 + c2) (Spair s1 s2)
| TPinl T t e te c s:
    typing T e te c s ->
    typing T (Einl t e) (Tsum te t) c (Sinlinr s S0)
| TPinr T t e te c s:
    typing T e te c s ->
    typing T (Einr t e) (Tsum t te) c (Sinlinr S0 s)
(* basic types - elim *)
| TPmatch_pair T e e' t t1 t2 c s c' s' s1 s2 :
    typing T e (Tprod t1 t2) c s ->
    let t12 := [t1; t2] in
    let T' := add_typings t12 T in
    typing T' e' t c' s' ->
    is_pair s = Some (s1, s2) ->
    let s12 := [s1; s2] in
    typing T (Ematch_pair e e') (subst_list s12 t) (c + subst_list s12 c') (subst_list s12 s')
| TPmatch_sum T e e1 e2 t1 t2 c s s1 s2 t c1 c2 s' s1' s2' :
    typing T e (Tsum t1 t2) c s ->
    (* timing constraints are passed forward; size and type constraints are passed backward.
       t' and s' are backward guidance for branches *)
    typing (add_typing t1 T) e1 (shift t) c1 s1' -> 
    typing (add_typing t2 T) e2 (shift t) c2 s2' -> 
    is_inlinr s = Some (s1, s2) ->
    subst s1 s1' <= s' ->
    subst s2 s2' <= s' ->
    typing T (Ematch_sum e e1 e2) t (c + max (subst s1 c1) (subst s2 c2)) s'
.

