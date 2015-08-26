Set Maximal Implicit Insertion.
Set Implicit Arguments.

Require Import GeneralTactics4.

Definition option_eq_b {A} (eqb : A -> A -> bool) a b :=
  match a, b with
    | Some a, Some b => eqb a b
    | None, None => true
    | _, _ => false
  end.

Lemma option_eq_b_iff {A eqb} (_ : forall (a b : A), eqb a b = true <-> a = b) a b : option_eq_b eqb a b = true <-> a = b.
Proof.
  destruct a; destruct b; simpl in *; split; intros H1; trivial; try discriminate.
  { f_equal; eapply H; eauto. }
  { inject H1; eapply H; eauto. }
Qed.

Inductive CtxEntry :=
| CEtype
| CEexpr
.

Definition context := list CtxEntry.

Definition ce_eq_b a b :=
  match a, b with
    | CEexpr, CEexpr => true
    | CEtype, CEtype => true
    | _, _ => false
  end.

Lemma ce_eq_b_iff a b : ce_eq_b a b = true <-> a = b.
Proof.
  destruct a; destruct b; simpl in *; split; intros; trivial; try discriminate.
Qed.

Definition ceb := option_eq_b ce_eq_b.

Definition ceb_iff : forall a b, ceb a b = true <-> a = b := option_eq_b_iff ce_eq_b_iff.

Lemma ceb_iff_c {a b} : a = b -> ceb a b = true.
  intros; eapply ceb_iff; eauto.
Qed.

Require Import List.

Goal ceb (nth_error (CEexpr :: CEtype :: nil) 1) (Some CEtype) = true. Proof. exact eq_refl. Qed.

Inductive var t ctx : Type :=
| Var n (_ : ceb (nth_error ctx n) (Some t) = true)
.

Arguments Var {t ctx} _ _ .

Coercion get_i {t ctx} (x : var t ctx) :=
  match x with
    | Var i _ => i
  end.

Inductive unvar {t ctx} (x : var t ctx) :=
| unVar n H (_ : x = Var n H)
.

Definition un_var {t ctx} (x : var t ctx) : unvar x.
  destruct x.
  econstructor.
  eauto.
Defined.

Notation "# n" := (Var n _) (at level 3, format "# n").

(*
Definition make_var {m ctx} n (P : ceb (nth_error ctx n) (Some m) = true) : var m ctx := Var n P.
Definition var0 {m ctx} : var m (m :: ctx).
  refine ((make_var (ctx := m%nat :: _) (m := m) 0 _)).
  eapply ce_eq_b_iff.
  eauto.
Defined.
*)
Definition var0 {m ctx} : var m (m :: ctx) := @Var m (m :: ctx) 0 (ceb_iff_c eq_refl).
(* Notation "##0" := var0. *)

