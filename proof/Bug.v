Set Implicit Arguments.

Inductive prop_bin_conn :=
| PBCAnd
| PBCImply
.

(* base sorts *)
Inductive bsort :=
| BSUnit
.

Inductive prop :=
| PBinConn (opr : prop_bin_conn) (p1 p2 : prop)
.

Definition PAnd := PBinConn PBCAnd.
Definition PImply := PBinConn PBCImply.

Delimit Scope idx_scope with idx.

Infix "===>" := PImply (at level 95) : idx_scope.
Infix "/\" := PAnd : idx_scope.

Fixpoint interp_bsort (b : bsort) :=
  match b with
  | BSUnit => unit
  end.

Fixpoint interp_bsorts arg_ks res :=
  match arg_ks with
  | nil => res
  | cons arg_k arg_ks => interp_bsorts arg_ks (interp_bsort arg_k -> res)
  end.

Fixpoint lift1 arg_ks t1 t : (t1 -> t) -> interp_bsorts arg_ks t1 -> interp_bsorts arg_ks t :=
  match arg_ks return (t1 -> t) -> interp_bsorts arg_ks t1 -> interp_bsorts arg_ks t with
  | nil =>
    fun f x1 => f x1
  | cons arg_k arg_ks =>
    fun f x1 => lift1 arg_ks (fun a1 ak => f (a1 ak)) x1
  end.

Fixpoint lift2 arg_ks : forall t1 t2 t, (t1 -> t2 -> t) -> interp_bsorts arg_ks t1 -> interp_bsorts arg_ks t2 -> interp_bsorts arg_ks t :=
  match arg_ks return forall t1 t2 t, (t1 -> t2 -> t) -> interp_bsorts arg_ks t1 -> interp_bsorts arg_ks t2 -> interp_bsorts arg_ks t with
  | nil =>
    fun t1 t2 t f x1 x2 => f x1 x2
  | cons arg_k arg_ks =>
    fun t1 t2 t f x1 x2 => lift2 arg_ks (fun a1 a2 ak => f (a1 ak) (a2 ak)) x1 x2
  end.

Definition imply (A B : Prop) : Prop := A -> B.

Definition for_all {A} (P : A -> Prop) : Prop := forall a, P a.

Definition interp_binconn opr : Prop -> Prop -> Prop :=
  match opr with
  | PBCAnd => and
  | PBCImply => imply
  end.

Fixpoint interp_p arg_ks p : interp_bsorts arg_ks Prop :=
  match p with
  | PBinConn opr p1 p2 =>
    lift2 arg_ks (interp_binconn opr) (interp_p arg_ks p1) (interp_p arg_ks p2)
  end.

Fixpoint forall_ arg_ks : interp_bsorts arg_ks Prop -> Prop :=
  match arg_ks with
  | nil => fun x => x
  | cons arg_k arg_ks => fun P => forall_ arg_ks (lift1 arg_ks for_all P)
  end.

Definition interp_prop bs (p : prop) : Prop :=
  let p := (p /\ p)%idx in
  let P := interp_p bs p in
  forall_ bs P.

Axiom admit : forall P : Prop, P.

Lemma interp_prop_subset_imply_minimal (b : bsort) (L : list bsort) (p p0 : prop) :
  interp_prop (b :: L) (p ===> p0)%idx.
Proof.
  cbn in *.
  eapply admit.
  (* Qed will trigger the error *)
Qed.
(* "Anomaly: conversion was given ill-typed terms (FProd). Please report." *)
