(* nonnegative rationals *)

Definition QN : Type.
  admit.
Defined.

Definition QN0 : QN.
  admit.
Defined.

Definition QN1 : QN.
  admit.
Defined.

Definition QNadd : QN -> QN -> QN.
  admit.
Defined.

Definition QNmul : QN -> QN -> QN.
  admit.
Defined.

Definition QNdiv : QN -> QN -> QN.
  admit.
Defined.

Definition QNeq : QN -> QN -> Prop.
  admit.
Defined.

Definition QNle : QN -> QN -> Prop.
  admit.
Defined.

Delimit Scope QN_scope with QN.
Notation " 0 " := QN0 : QN_scope.
Notation " 1 " := QN1 : QN_scope.
Notation " 2 " := (QNadd 1 1)%QN : QN_scope.
Infix "+" := QNadd : QN_scope.
Infix "*" := QNmul : QN_scope.
Infix "/" := QNdiv : QN_scope.
Infix "==" := QNeq (at level 70) : QN_scope.
Infix "<=" := QNle : QN_scope.
Notation "a != b" := (~ QNeq a b) (at level 70) : QN_scope.

Lemma QNeq_refl q : (q == q)%QN.
  admit.
Qed.

Lemma QNeq_trans a b c : (a == b -> b == c -> a == c)%QN.
  admit.
Qed.

Lemma QNeq_symm a b : (a == b -> b == a)%QN.
  admit.
Qed.

Require Import Setoid.

Global Add Relation QN QNeq
    reflexivity proved by QNeq_refl
    symmetry proved by QNeq_symm
    transitivity proved by QNeq_trans
      as QNeq_rel.

Lemma QNle_refl q : (q <= q)%QN.
  admit.
Qed.

Lemma QNle_trans a b c : (a <= b -> b <= c -> a <= c)%QN.
  admit.
Qed.

Global Add Relation QN QNle
    reflexivity proved by QNle_refl
    transitivity proved by QNle_trans
      as QNle_rel.

Lemma QN_addxx q : (q + q == 2 * q)%QN.
  admit.
Qed.

Lemma QN_2_mul_half : (2 * (1 / 2) == 1)%QN.
  admit.
Qed.

Lemma QN_exists_inverse q : (q != 0 -> exists q', q * q' == 1)%QN.
  admit.
Qed.

Lemma QN_half_not_0 : (1 / 2 != 0)%QN.
  admit.
Qed.

Lemma QN_2_not_0 : (2 != 0)%QN.
  admit.
Qed.

Lemma QN_1_not_0 : (1 != 0)%QN.
  admit.
Qed.

Lemma QN_mulx1 q : (q * 1 == q)%QN.
  admit.
Qed.

