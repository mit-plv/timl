(* Type soundness *)

Require Import List.
Require Import Typing EvalCBV.

Import ListNotations.
Local Open Scope list_scope.

(* encoding of fix by recursive-type :
     fix f(x).e := \y. (unfold v) v y 
        where v := fold (\z. (\f. \x. e) (\y. (unfold z) z y)) 
                    (for y,z\not\in FV(e))
 *)

Inductive steps : expr -> expr -> Prop :=
| Steps0 e : steps e e
| StepsS e1 e2 e3 : step e1 e2 -> steps e2 e3 -> steps e1 e3
.

Definition typingsim T e t := exists c s, typing T e t c s.

Definition nostuck e := forall e', steps e e' -> IsValue e' \/ exists e'', step e' e''.

Lemma sound_wrt_nostuck :
  forall e t,
    typingsim [] e t ->
    nostuck e.
Proof.
  admit.
Qed.

Definition value_of v t := IsValue v /\ typingsim [] v t.

Inductive nsteps : expr -> nat -> expr -> Prop :=
| Nsteps0 e : nsteps e 0 e
| NstepsS e1 e2 n e3 : step e1 e2 -> nsteps e2 n e3 -> nsteps e1 (S n) e3
.

Local Open Scope G.

(* concrete size *)
Inductive csize :=
| CStt
| CSinl (_ : csize)
| CSinr (_ : csize)
| CSinlinr (a b: csize)
| CSpair (a b: csize)
| CSfold (_ : csize)
| CShide (_ : csize)
.

Definition leCS : csize -> csize -> Prop.
  admit.
Defined.

Instance Le_csize : Le csize :=
  {
    le := leCS
  }.

Definition get_size (e : expr) : csize.
  admit.
Defined.

Definition nat_of_cexpr (c : cexpr) : option nat.
  admit.
Defined.

Definition csize_to_size (s : csize) : size.
  admit.
Defined.

Coercion csize_to_size : csize >-> size.

Instance Subst_csize_cexpr : Subst csize cexpr :=
  {
    substn n v b := substn n (v : size) b
  }.

Instance Subst_csize_size : Subst csize size :=
  {
    substn n v b := substn n (v : size) b
  }.

(*
Definition csize_of_size (s : size) : option csize.
  admit.
Defined.
*)

Definition bounded t1 e c (s : size) :=
  exists (C : nat) (xi0 : csize), 
    forall v1,
      value_of v1 t1 ->
      let xi1 := get_size v1 in
      xi0 <= xi1 ->
      forall v n, 
        IsValue v -> 
        (* n is the actual running time *)
        nsteps (subst v1 e) n v ->
        (* n is bounded *)
        (exists c_xi1, nat_of_cexpr (subst xi1 c) = Some c_xi1 /\ n <= C * c_xi1) 
(*
        /\
        (* xi is the actual result size *)
        let xi := get_size v in
        (* xi is bounded *)
        (exists s_xi1, csize_of_size (subst xi1 s) = Some s_xi1 /\ xi <= s_xi1)
*)
.

Lemma sound_wrt_bounded :
  forall t1 e t c s, 
    typing [TEtyping (t1, None)] e t c s -> 
    bounded t1 e c s.
Proof.
  admit.
Qed.
