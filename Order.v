Set Maximal Implicit Insertion.
Set Implicit Arguments.

Require Import List.
Require Import GeneralTactics.
Require Import NonnegRational.
Require Import Util.
Require Import Complexity.

Export Complexity.

Class Le a b :=
  {
    le : a -> b -> Prop
  }.

Infix "<=" := le : G.
Local Open Scope G.

Global Instance Le_nat : Le nat nat :=
  {
    le := Peano.le
  }.

Section ctx.

  Variable ctx : context.

  Definition Fdiv a b := (@Fscale ctx (1 / b)%QN a).

  Infix "+" := Fadd : F.
  Infix "*" := Fmul : F.
  Infix "/" := Fdiv : F.
  Local Open Scope F.

  Notation " 0 " := F0 : F01.
  Notation " 1 " := F1 : F01.
  Local Open Scope F01.

  Infix "*:" := Fscale (at level 40).

  Notation log2 := (Flog 2%QN).

  Definition Fconst c := @Fscale ctx c F1.
  Coercion Fconst : QN >-> cexpr.

  Inductive leE : cexpr ctx -> cexpr ctx -> Prop :=
  | leE_refl n : n == n
  | leE_trans a b c : a == b -> b == c -> a == c
  | leE_symm a b : a == b -> b == a
  (* semiring rules *)
  | leE_add0x n : 0 + n == n
  | leE_addA a b c : a + (b + c) == a + b + c
  | leE_addC a b : a + b == b + a
  | leE_mulA a b c : a * (b * c) == a * b * c
  | leE_mulC a b : a * b == b * a
  | leE_mul1x n : 1 * n == n
  | leE_mulDx a b c : (a + b) * c == a * c + b * c
  | leE_mul0x n : 0 * n == 0
  (* module rules *)
  | leE_scaleA a b c : a *: (b *: c) == (a * b)%QN *: c
  | leE_scale1x n : 1%QN *: n == n
  | leE_scalexD a b c : a *: (b + c) == a *: b + a *: c
  | leE_scaleDx a b c : (a + b)%QN *: c == a *: c + b *: c
  (* algebra rules *)
  | leE_scaleAl a b c : a *: (b * c) == a *: b * c
  (* congruence rules *)
  | leE_add a b a' b' : a == a' -> b == b' -> a + b == a' + b'
  | leE_max a b a' b' : a == a' -> b == b' -> Fmax a b == Fmax a' b'
  | leE_mul a b a' b' : a == a' -> b == b' -> a * b == a' * b'
  | leE_scale c n c' n' : (c == c')%QN -> n == n' -> c *: n == c' *: n'
  | leE_log c n c' n' : (c == c')%QN -> n == n' -> Flog c n == Flog c' n'
  | leE_exp c n c' n' : (c == c')%QN -> n == n' -> Fexp c n == Fexp c' n'
  (* for special operations *)
  | leE_maxC a b : Fmax a b == Fmax b a
  | leE_log_mul bs a b : Flog bs (a * b) == Flog bs a + Flog bs b
  | leE_logcc c : (c != 0)%QN -> Flog c c == 1
  (* for variables *)
  | leE_pair x p i : Fvar (x, Pfst :: p) i + Fvar (x, Psnd :: p) i == Fvar (x, p) i
  | leE_inlinr x p i : Fmax (Fvar (x, Pinl :: p) i) (Fvar (x, Pinr :: p) i) == Fvar (x, p) i
  | leE_inl x p i : Fvar (x, Pinl :: p) i == Fvar (x, p) i
  | leE_inr x p i : Fvar (x, Pinr :: p) i == Fvar (x, p) i
  | leE_unfold x p i : 1 + Fvar (x, Punfold :: p) i == Fvar (x, p) i
                                                            where "a == b" := (leE a b) : leE_scope
  .

  Delimit Scope leE_scope with leE.

  Global Add Relation (cexpr ctx) leE
      reflexivity proved by leE_refl
      symmetry proved by @leE_symm
      transitivity proved by @leE_trans
        as leE_rel.

  (* precise less-than relation on cexprs *)
  Inductive leF : cexpr ctx -> cexpr ctx -> Prop :=
  (* variable rules, interpreting the variable as growing ever larger (symptotic) *)
  | leF_1x x i : 1 <= Fvar x i
  (* preorder rules *)
  | leF_leE a b : leE a b -> a <= b
  | leF_trans a b c : a <= b -> b <= c -> a <= c
  (* base rules *)
  | leF_01 : 0 <= 1
  (* congruent rules *)
  | leF_add a b a' b' : a <= a' -> b <= b' -> a + b <= a' + b'
  | leF_mul a b a' b' : a <= a' -> b <= b' -> a * b <= a' * b'
  | leF_log bs a b : a <= b -> Flog bs a <= Flog bs b
  | leF_exp bs a b : a <= b -> Fexp bs a <= Fexp bs b
  (* max rules *)
  | leF_max1 a b : a <= max a b
  | leF_max2 a b : a <= b -> max a b <= b
  (* log and exp rules *)
  | leF_log_base b1 b2 n : (b1 <= b2)%QN -> Flog b1 n <= Flog b2 n
  | leF_exp_base b1 b2 n : (b1 <= b2)%QN -> Fexp b1 n <= Fexp b2 n
                                                              where "a <= b" := (leF a b) : leF_scope
  .

  Delimit Scope leF_scope with leF.

  Lemma leF_refl (n : cexpr ctx) : (n <= n)%leF.
  Proof.
    simpl; eapply leF_leE; reflexivity.
  Qed.

  Global Add Relation (cexpr ctx) leF
      reflexivity proved by leF_refl
      transitivity proved by @leF_trans
        as leF_rel.

  (* less-than relation on cexprs ignoring constant addend *)
  Inductive leC : cexpr ctx -> cexpr ctx -> Prop :=
  (* ignore constant addend *)
  | leC_addcx c x i : c + Fvar x i <= Fvar x i
  (* preorder rules *)
  | leC_leE a b : leE a b -> a <= b
  | leC_trans a b c : a <= b -> b <= c -> a <= c
  (* base rules *)
  | leC_01 : 0 <= 1
  (* congruent rules *)
  | leC_add a b a' b' : a <= a' -> b <= b' -> a + b <= a' + b'
  | leC_mul a b a' b' : a <= a' -> b <= b' -> a * b <= a' * b'
  | leC_scale c n c' n' : (c <= c')%QN -> n <= n' -> c *: n <= c' *: n'
  | leC_log bs a b : a <= b -> Flog bs a <= Flog bs b
  | leC_exp bs a b : leF a b -> Fexp bs a <= Fexp bs b
  (* max rules *)
  | leC_max_a a b : a <= max a b
  | leC_max_c a b c : a <= c -> b <= c -> max a b <= c
  (* log and exp rules *)
  | leC_log_base b1 b2 n : (b1 <= b2)%QN -> Flog b1 n <= Flog b2 n
  | leC_exp_base b1 b2 n : (b1 <= b2)%QN -> Fexp b1 n <= Fexp b2 n
                                                              where "a <= b" := (leC a b) : leC_scope
  .

  Delimit Scope leC_scope with leC.

  Lemma leC_refl (n : cexpr ctx) : (n <= n)%leC.
  Proof.
    simpl; eapply leC_leE; reflexivity.
  Qed.

  Global Add Relation (cexpr ctx) leC
      reflexivity proved by leC_refl
      transitivity proved by @leC_trans
        as leC_rel.

  (* big-O less-than relation on cexprs *)
  Inductive leO : cexpr ctx -> cexpr ctx -> Prop :=
  (* ignore constant factor *)
  | leO_cn_n c n : c *: n <= n
  (* variable rules, interpreting the variable as growing ever larger (symptotic) *)
  | leO_1x x i : 1 <= Fvar x i
  (* preorder rules *)
  | leO_leE a b : leE a b -> a <= b
  | leO_trans a b c : a <= b -> b <= c -> a <= c
  (* base rules *)
  | leO_01 : 0 <= 1
  (* congruent rules *)
  | leO_add a b a' b' : a <= a' -> b <= b' -> a + b <= a' + b'
  | leO_mul a b a' b' : a <= a' -> b <= b' -> a * b <= a' * b'
  | leO_scale c n c' n' : (c <= c')%QN -> n <= n' -> c *: n <= c' *: n'
  | leO_log bs a b : a <= b -> Flog bs a <= Flog bs b
  | leO_exp bs a b : leC a b -> Fexp bs a <= Fexp bs b
  (* max rules *)
  | leO_max_a a b : a <= max a b
  | leO_max_c a b c : a <= c -> b <= c -> max a b <= c
  (* log and exp rules *)
  | leO_log_base b1 b2 n : (b1 <= b2)%QN -> Flog b1 n <= Flog b2 n
  | leO_exp_base b1 b2 n : (b1 <= b2)%QN -> Fexp b1 n <= Fexp b2 n
                                                              where "a <= b" := (leO a b) : leO_scope
  .

  Delimit Scope leO_scope with leO.

  Lemma leO_refl (n : cexpr ctx) : (n <= n)%leO.
  Proof.
    simpl; eapply leO_leE; reflexivity.
  Qed.

  Global Add Relation (cexpr ctx) leO
      reflexivity proved by leO_refl
      transitivity proved by @leO_trans
        as leO_rel.

  (* the default <= on cexpr will be leF *)
  Global Instance Le_cexpr : Le (cexpr ctx) (cexpr ctx) :=
    {
      le := leF
    }.

  Local Close Scope F01.

  (* less-than relation on sizes based on leC *)
  Definition leS (a b : size ctx) :=
    stats_get 0 (summarize a) <= stats_get 0 (summarize b) /\
    stats_get 1 (summarize a) <= stats_get 1 (summarize b).

  Global Instance Le_size : Le (size ctx) (size ctx) :=
    {
      le := leS
    }.

  Lemma leS_refl (a : size ctx) : a <= a.
  Proof.
    simpl; unfold leS; simpl; split; reflexivity.
  Qed.

  Lemma leS_trans (a b c : size ctx) : a <= b -> b <= c -> a <= c.
  Proof.
    intros H1 H2; simpl in *; unfold leS in *; simpl in *; openhyp; split; etransitivity; eauto.
  Qed.

  Global Add Relation (size ctx) leS
      reflexivity proved by leS_refl
      transitivity proved by @leS_trans
        as leS_rel.

End ctx.

Infix "<=" := leF : F.
Infix "<<=" := leO (at level 70) : F.
Infix "+" := Fadd : F.
Infix "*" := Fmul : F.
Infix "/" := Fdiv : F.
Notation " 0 " := F0 : F01.
Notation " 1 " := F1 : F01.
Infix "*:" := Fscale (at level 40).
Notation log2 := (Flog 2%QN).
