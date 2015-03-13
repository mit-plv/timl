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
  | TEtyping (_ : type * option size)
  | TEkinding (_ : kind).

Definition tcontext := list tc_entry.

Local Open Scope prog_scope.

Definition add_typing t T := TEtyping t :: T.
Definition add_typings ls T := fst $ fold_left (fun (p : tcontext * nat) t => let (T, n) := p in (add_typing (shiftby n t) T, S n)) ls (T, 0%nat).
Definition add_kinding k T := TEkinding k :: T.

Coercion var_to_size (x : var) : size := Svar (x, []).

Inductive kinding : tcontext -> type -> kind -> Prop :=
| Kvar T n k : find n T = Some (TEkinding k) -> kinding T #n k
| Kapp T t1 t2 k :
    kinding T t1 (S k) ->
    kinding T t2 0 ->
    kinding T (Tapp t1 t2) k
| Kabs T t k :
    kinding (add_kinding 0 T) t k ->
    kinding T (Tabs t) (S k)
| Karrow T t1 f g t2 :
    kinding T t1 0 ->
    kinding (add_typing (t1, None) T) t2 0 ->
    kinding T (Tarrow t1 f g t2) 0
| Kuniversal T f g t :
    kinding (add_kinding 0 T) t 0 ->
    kinding T (Tuniversal f g t) 0
| Krecur T t :
    kinding (add_kinding 0 T) t 0 ->
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
| Qarrow a f g b a' b' : 
    teq a a' ->
    teq b b' ->
    teq (Tarrow a f g b) (Tarrow a' f g b')
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

Notation Tuniversal0 := (Tuniversal F0 Stt).

Inductive typing : tcontext -> expr -> type -> cexpr -> size -> Prop :=
| TPvar T n t s : 
    find n T = Some (TEtyping (t, s)) -> 
    typing T #n (shiftby (S n) t) F0 (default (var_to_size #n) (shiftby (S n) s))
| TPapp T e1 e2 ta tb n s n1 n2 nouse s2 : 
    typing T e1 (Tarrow ta n s tb) n1 nouse ->
    typing T e2 ta n2 s2 ->
    typing T (Eapp e1 e2) (subst s2 tb) (n1 + n2 + F1 + subst s2 n) (subst s2 s)
| TPabs T e t1 t2 n s :
    kinding T t1 0 ->
    typing (add_typing (t1, None) T) e t2 n s ->
    typing T (Eabs t1 e) (Tarrow t1 n s t2) F0 Stt
| TPtapp T e t2 n s t n' :
    typing T e (Tuniversal (shift n) (shift s) t) n' Stt ->
    typing T (Etapp e t2) (subst t2 t) (n' + F1 + n) s
| TPtabs T e n s t :
    typing (add_kinding 0 T) e t n s ->
    typing T (Etabs e) (Tuniversal n s t) F0 Stt
| TPlet T t1 e1 e2 t2 n1 n2 s1 s2:
    typing T e1 t1 n1 s1 ->
    typing (add_typing (t1, Some s1) T) e2 t2 n2 s2 ->
    typing T (Elet t1 e1 e2) (subst s1 t2) (n1 + subst s1 n2) (subst s1 s2)
| TPfold T e t n s t1 :
    t == Trecur t1 ->
    typing T e (subst t t1) n s ->
    typing T (Efold t e) t n (Sfold s)
| TPunfold T e t n s s1 t1 :
    typing T e t n s ->
    is_fold s = Some s1 ->
    t == Trecur t1 ->
    typing T (Eunfold e) (subst t t1) n s1
| TPhide T e t n s :
    typing T e t n s ->
    typing T (Ehide e) (Thide t) n (Shide s)
| TPunhide T e t n s s1 :
    typing T e (Thide t) n s ->
    is_hide s = Some s1 ->
    typing T (Eunhide e) t n s1
| TPeq T e t1 t2 n s :
    typing T e t1 n s ->
    t1 == t2 ->
    typing T e t2 n s
| TPsub T e t n n' s s' :
    typing T e t n s ->
    n <<= n' ->
    s <= s' ->
    typing T e t n' s'
(* basic types - intro *)
| TPtt T :
    typing T Ett Tunit F0 Stt
| TPpair T e1 t1 c1 s1 e2 t2 c2 s2 : 
    typing T e1 t1 c1 s1 ->
    typing T e2 t2 c2 s2 ->
    typing T (Epair e1 e2) (Tprod t1 t2) (c1 + c2) (Spair s1 s2)
| TPinl T t e te c s:
    typing T e te c s ->
    typing T (Einl t e) (Tsum te t) c (Sinl s)
| TPinr T t e te c s:
    typing T e te c s ->
    typing T (Einr t e) (Tsum t te) c (Sinr s)
(* basic types - elim *)
| TPmatch_pair T e e' t t1 t2 n s n' s' s1 s2 :
    typing T e (Tprod t1 t2) n s ->
    is_pair s = Some (s1, s2) ->
    let t12 := [(t1, Some s1); (t2, Some s2)] in
    let T' := add_typings t12 T in
    typing T' e' t n' s' ->
    let s12 := [s1; s2] in
    typing T (Ematch_pair e e') (subst_list s12 t) (n + F1 + subst_list s12 n') (subst_list s12 s')
| TPmatch_inlinr T e e1 e2 t1 t2 n s s1 s2 t n1 n2 s' :
    typing T e (Tsum t1 t2) n s ->
    is_inlinr s = Some (s1, s2) ->
    (* timing constraints are passed forward; size and type constraints are passed backward.
       t' and s' are backward guidance for branches *)
    typing (add_typing (t1, Some s1) T) e1 (shift t) n1 (shift s') -> 
    typing (add_typing (t2, Some s2) T) e2 (shift t) n2 (shift s') -> 
    typing T (Ematch_sum e e1 e2) t (n + F1 + max (subst s1 n1) (subst s2 n2)) s'
| TPmatch_inl T e e1 e2 t1 t2 n s t' n' s' :
    typing T e (Tsum t1 t2) n (Sinl s) ->
    typing (add_typing (t1, Some s) T) e1 t' n' s' ->
    typing T (Ematch_sum e e1 e2) (subst s t') (n + F1 + subst s n') (subst s s')
| TPmatch_inr T e e1 e2 t1 t2 n s t' n' s' :
    typing T e (Tsum t1 t2) n (Sinr s) ->
    typing (add_typing (t2, Some s) T) e2 t' n' s' ->
    typing T (Ematch_sum e e1 e2) (subst s t') (n + F1 + subst s n') (subst s s')
.

