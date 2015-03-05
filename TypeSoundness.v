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

Inductive nsteps : expr -> nat -> expr -> Prop :=
| Nsteps0 e : nsteps e 0 e
| NstepsS e1 e2 n e3 : step e1 e2 -> nsteps e2 n e3 -> nsteps e1 (S n) e3
.

Inductive steps : expr -> expr -> Prop :=
| Steps0 e : steps e e
| StepsS e1 e2 e3 : step e1 e2 -> steps e2 e3 -> steps e1 e3
.

Definition get_size (e : expr) : size.
  admit.
Defined.

Definition typingsim T e t := exists c s, typing T e t c s.

Local Open Scope G.

Definition nat_of_cexpr (c : cexpr) : option nat.
  admit.
Defined.

Definition nostuck e := forall e', steps e e' -> IsValue e' \/ exists e'', step e' e''.

Theorem type_soundness : forall t1 c s e t, 
  typing [TEtyping (t1, None)] e t c s -> 
  (forall v1,
     IsValue v1 ->
     typingsim [] v1 t1 ->
     nostuck (subst v1 e)) /\
  exists Ct s0, 
    forall v1,
      IsValue v1 ->
      typingsim [] v1 t1 ->
      let s1 := get_size v1 in
      (s0 <= s1) ->
      forall v n, 
        IsValue v -> 
        nsteps (subst v1 e) n v ->
        (exists c_s1, nat_of_cexpr (subst s1 c) = Some c_s1 /\ n <= Ct * c_s1) /\
        get_size v <= subst s1 s.
Proof.
  admit.
Qed.
