Require Import Util.
Require Import TypingFacts.

Export Typing.

Local Open Scope prog_scope.

Definition Tbool := Tsum Tunit Tunit.
Definition Etrue := Einl $$ Tunit $$ Tunit $$ Ett.
Definition Efalse := Einr $$ Tunit $$ Tunit $$ Ett.
Definition Eif e b_true b_false :=
  Ematch_sum e (shift b_true) (shift b_false).

Lemma Kbool T : kinding T Tbool 0.
Proof.
  eapply Ksum'; eapply Kunit.
Qed.

Definition bool_size := Sinlinr Stt Stt.

Local Open Scope F.

Lemma TPif T e e1 e2 n s' t n1 n2 s s1 s2 :
  typing T e Tbool n s' ->
  is_inlinr s' = Some (s1, s2) ->
  typing T e1 t n1 s ->
  typing T e2 t n2 s ->
  typing T (Eif e e1 e2) t (n + F1 + max n1 n2) s.
Proof.
  intros He Hs H1 H2.
  {
    eapply TPsubn.
    {
      eapply TPmatch_inlinr.
      { eauto. }
      { eauto. }
      { eapply TPinsert0; eauto. }
      { eapply TPinsert0; eauto. }
    }
    {
      simpl.
      repeat rewrite fold_subst_s_f.
      repeat rewrite fold_shift_from_f.
      repeat rewrite subst_shift_s_f.
      reflexivity.
    }
  }
Qed.

