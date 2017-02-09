Set Implicit Arguments.

Axiom admit : forall P : Prop, P.
  
Module Type TIME.
  Parameter time_type : Set.
  Parameter Time0 : time_type.
  Parameter Time1 : time_type.
  Parameter TimeAdd : time_type -> time_type -> time_type.
  (* A 'minus' bounded below by zero *)
  Parameter TimeMinus : time_type -> time_type -> time_type.
  Parameter TimeLe : time_type -> time_type -> Prop.
  Parameter TimeMax : time_type -> time_type -> time_type.
  
  Delimit Scope time_scope with time.
  Notation "0" := Time0 : time_scope.
  Notation "1" := Time1 : time_scope.
  Infix "+" := TimeAdd : time_scope.
  Infix "-" := TimeMinus : time_scope.
  Infix "<=" := TimeLe : time_scope.

  Axiom Time_add_le_elim :
    forall a b c,
      (a + b <= c -> a <= c /\ b <= c)%time.
  Axiom Time_minus_move_left :
    forall a b c,
      (c <= b ->
       a + c <= b ->
       a <= b - c)%time.
  Axiom Time_add_assoc : forall a b c, (a + (b + c) = a + b + c)%time.
  Axiom lhs_rotate :
    forall a b c,
      (b + a <= c ->
       a + b <= c)%time.
  Axiom Time_add_cancel :
    forall a b c,
      (a <= b ->
       a + c <= b + c)%time.
  Axiom rhs_rotate :
    forall a b c,
      (a <= c + b->
       a <= b + c)%time.
  Axiom Time_a_le_ba : forall a b, (a <= b + a)%time.
  Axiom Time_minus_cancel :
    forall a b c,
      (a <= b -> a - c <= b - c)%time.
  Axiom Time_a_minus_a : forall a, (a - a = 0)%time.
  Axiom Time_0_le_x : forall x, (0 <= x)%time.
  Axiom Time_minus_0 : forall x, (x - 0 = x)%time.
  Axiom Time_0_add : forall x, (0 + x = x)%time.
  Axiom Time_le_refl : forall x, (x <= x)%time.
  Axiom Time_le_trans :
    forall a b c,
      (a <= b -> b <= c -> a <= c)%time.
  Axiom Time_add_cancel2 :
    forall a b c d,
      (c <= d ->
       a <= b ->
       a + c <= b + d)%time.
  Axiom Time_a_le_maxab : forall a b, (a <= TimeMax a b)%time.
  Axiom Time_b_le_maxab : forall a b, (b <= TimeMax a b)%time.
  Axiom Time_add_minus_assoc :
    forall a b c,
      (c <= b -> a + (b - c) = a + b - c)%time.
  Axiom Time_minus_le : forall a b, (a - b <= a)%time.
  Axiom Time_minus_add_cancel :
    forall a b,
      (b <= a -> a - b + b = a)%time.
  Axiom Time_minus_move_right :
    forall a b c,
      (c <= a ->
       a <= b + c ->
       a - c <= b)%time.
  Axiom Time_le_add_minus :
    forall a b c,
      (a + b - c <= a + (b - c))%time.
  Axiom Time_add_comm : forall a b, (a + b = b + a)%time.
  Axiom Time_add_minus_cancel : forall a b, (a + b - b = a)%time.
  Axiom Time_minus_minus_cancel : forall a b, (b <= a -> a - (a - b) = b)%time.

End TIME.

Require Import Datatypes.

Definition option_dec A (x : option A) : {a | x = Some a} + {x = None}.
  destruct x.
  left.
  exists a.
  eauto.
  right.
  eauto.
Qed.

Require Import Frap.

Module NatTime <: TIME.
  Definition time_type := nat.
  Definition Time0 := 0.
  Definition Time1 := 1.
  Definition TimeAdd := plus.
  Definition TimeMinus := Peano.minus.
  Definition TimeLe := le.
  Definition TimeMax := max.
  
  Delimit Scope time_scope with time.
  Notation "0" := Time0 : time_scope.
  Notation "1" := Time1 : time_scope.
  Infix "+" := TimeAdd : time_scope.
  Infix "-" := TimeMinus : time_scope.
  Infix "<=" := TimeLe : time_scope.

  Require Import Omega.

  Ltac unfold_time := unfold TimeAdd, TimeMinus, TimeMax, Time0, Time1, TimeLe in *.
  Ltac linear := unfold_time; omega.

  Lemma Time_add_le_elim a b c :
    (a + b <= c -> a <= c /\ b <= c)%time.
  Proof.
    intros; linear.
  Qed.

  Lemma Time_minus_move_left a b c :
    (c <= b ->
     a + c <= b ->
     a <= b - c)%time.
  Proof.
    intros; linear.
  Qed.
  
  Lemma Time_add_assoc a b c : (a + (b + c) = a + b + c)%time.
  Proof.
    intros; linear.
  Qed.

  Lemma lhs_rotate a b c :
    (b + a <= c ->
     a + b <= c)%time.
  Proof.
    intros; linear.
  Qed.

  Lemma Time_add_cancel a b c :
    (a <= b ->
     a + c <= b + c)%time.
  Proof.
    intros; linear.
  Qed.

  Lemma rhs_rotate a b c :
    (a <= c + b->
     a <= b + c)%time.
  Proof.
    intros; linear.
  Qed.

  Lemma Time_a_le_ba a b : (a <= b + a)%time.
  Proof.
    intros; linear.
  Qed.

  Lemma Time_minus_cancel a b c :
    (a <= b -> a - c <= b - c)%time.
  Proof.
    intros; linear.
  Qed.

  Lemma Time_a_minus_a a : (a - a = 0)%time.
  Proof.
    intros; linear.
  Qed.

  Lemma Time_0_le_x x : (0 <= x)%time.
  Proof.
    intros; linear.
  Qed.

  Lemma Time_minus_0 x : (x - 0 = x)%time.
  Proof.
    intros; linear.
  Qed.

  Lemma Time_0_add x : (0 + x = x)%time.
  Proof.
    intros; linear.
  Qed.

  Lemma Time_le_refl x : (x <= x)%time.
  Proof.
    intros; linear.
  Qed.

  Lemma Time_le_trans a b c :
    (a <= b -> b <= c -> a <= c)%time.
  Proof.
    intros; linear.
  Qed.

  Lemma Time_add_cancel2 a b c d :
    (c <= d ->
     a <= b ->
     a + c <= b + d)%time.
  Proof.
    intros; linear.
  Qed.

  Lemma Time_a_le_maxab a b : (a <= TimeMax a b)%time.
  Proof.
    intros; unfold_time; linear_arithmetic.
  Qed.

  Lemma Time_b_le_maxab a b : (b <= TimeMax a b)%time.
    intros; unfold_time; linear_arithmetic.
  Qed.

  Lemma Time_add_minus_assoc a b c :
    (c <= b -> a + (b - c) = a + b - c)%time.
  Proof.
    intros; linear.
  Qed.

  Lemma Time_minus_le a b : (a - b <= a)%time.
  Proof.
    intros; linear.
  Qed.

  Lemma Time_minus_add_cancel a b :
    (b <= a -> a - b + b = a)%time.
  Proof.
    intros; linear.
  Qed.

  Lemma Time_minus_move_right a b c :
    (c <= a ->
     a <= b + c ->
     a - c <= b)%time.
  Proof.
    intros; linear.
  Qed.

  Lemma Time_le_add_minus a b c :
    (a + b - c <= a + (b - c))%time.
  Proof.
    intros; linear.
  Qed.

  Lemma Time_add_comm a b : (a + b = b + a)%time.
  Proof.
    intros; linear.
  Qed.

  Lemma Time_add_minus_cancel a b : (a + b - b = a)%time.
  Proof.
    intros; linear.
  Qed.

  Lemma Time_minus_minus_cancel a b : (b <= a -> a - (a - b) = b)%time.
  Proof.
    intros; linear.
  Qed.

End NatTime.

(* Some common utilities *)

Ltac copy h h2 := generalize h; intro h2.

Ltac try_eexists := try match goal with | |- exists _, _ => eexists end.

Ltac try_split := try match goal with | |- _ /\ _ => split end.

Ltac eexists_split :=
  try match goal with
      | |- exists _, _ => eexists
      | |- _ /\ _ => split
      end.

Ltac apply_all e := 
  repeat match goal with
           H : _ |- _ => eapply e in H
         end.

Ltac openhyp :=
  repeat match goal with
         | H : _ /\ _ |- _  => destruct H
         | H : _ \/ _ |- _ => destruct H
         | H : exists x, _ |- _ => destruct H
         | H : exists ! x, _ |- _ => destruct H
         | H : unique _ _ |- _ => destruct H
         end.

Lemma nth_error_nil A n : @nth_error A [] n = None.
Proof.
  induction n; simplify; eauto.
Qed.

Lemma nth_error_Forall2 A B P ls1 ls2 :
  Forall2 P ls1 ls2 ->
  forall n (a : A),
    nth_error ls1 n = Some a ->
    exists b : B,
      nth_error ls2 n = Some b /\
      P a b.
Proof.
  induct 1; destruct n; simplify; repeat rewrite nth_error_nil in *; try discriminate; eauto.
  invert H1.
  eexists; eauto.
Qed.

Lemma map_firstn A B (f : A -> B) ls :
  forall n,
    map f (firstn n ls) = firstn n (map f ls).
Proof.
  induction ls; destruct n; simplify; eauto.
  f_equal; eauto.
Qed.

Definition fmap_map {K A B} (f : A -> B) (m : fmap K A) : fmap K B.
Admitted.

Lemma fmap_map_lookup K A B (f : A -> B) m (k : K) (a : A) :
  m $? k = Some a ->
  fmap_map f m $? k = Some (f a).
Admitted.
Lemma fmap_map_lookup_elim K A B (f : A -> B) m (k : K) (b : B) :
  fmap_map f m $? k = Some b ->
  exists a : A,
    f a = b /\
    m $? k = Some a.
Admitted.

Lemma fmap_ext2 K A (m m' : fmap K A) :
  (forall k v, m $? k = Some v -> m' $? k = Some v) ->
  (forall k v, m' $? k = Some v -> m $? k = Some v) ->
  m = m'.
Proof.
  intros H1 H2.
  eapply fmap_ext.
  intros k.
  cases (m $? k).
  {
    eapply H1 in Heq.
    eauto.
  }
  cases (m' $? k); eauto.
  {
    eapply H2 in Heq0.
    erewrite Heq0 in Heq.
    discriminate.
  }
Qed.

Lemma fmap_map_ext A B (f g : A -> B) :
  (forall a, f a = g a) ->
  forall K (m : fmap K A), fmap_map f m = fmap_map g m.
Proof.
  intros Hfg K m.
  eapply fmap_ext2.
  {
    intros k v Hk.
    eapply fmap_map_lookup_elim in Hk.
    destruct Hk as (a & Hga & Hk).
    subst.
    erewrite fmap_map_lookup; eauto.
    f_equal; eauto.
  }
  {
    intros k v Hk.
    eapply fmap_map_lookup_elim in Hk.
    destruct Hk as (a & Hga & Hk).
    subst.
    erewrite fmap_map_lookup; eauto.
    f_equal; eauto.
  }
Qed.

Lemma fmap_map_fmap_map K A B C (f : A -> B) (g : B -> C) (m : fmap K A) :
  fmap_map g (fmap_map f m) = fmap_map (fun x => g (f x)) m.
Proof.
  eapply fmap_ext2.
  {
    intros k v Hk.
    eapply fmap_map_lookup_elim in Hk.
    destruct Hk as (b & Hgb & Hk).
    subst.
    eapply fmap_map_lookup_elim in Hk.
    destruct Hk as (a & Hfa & Hk).
    subst.
    erewrite fmap_map_lookup; eauto.
  }
  {
    intros k v Hk.
    eapply fmap_map_lookup_elim in Hk.
    destruct Hk as (a & Hgfa & Hk).
    subst.
    erewrite fmap_map_lookup; eauto.
    erewrite fmap_map_lookup; eauto.
  }
Qed.

Lemma fmap_map_id K A (m : fmap K A) :
  fmap_map (fun x => x) m = m.
Proof.
  eapply fmap_ext2.
  {
    intros k v Hk.
    eapply fmap_map_lookup_elim in Hk.
    destruct Hk as (a & ? & Hk).
    subst.
    eauto.
  }
  {
    intros k v Hk.
    erewrite fmap_map_lookup; eauto.
  }
Qed.

Lemma incl_fmap_map K A B (f : A -> B) (m m' : fmap K A) :
  m $<= m' ->
  fmap_map f m $<= fmap_map f m'.
Proof.
  intros Hincl.
  eapply includes_intro.
  intros k v Hk.
  eapply fmap_map_lookup_elim in Hk.
  destruct Hk as (a & ? & Hk).
  subst.
  eapply includes_lookup in Hincl; eauto.
  erewrite fmap_map_lookup; eauto.
Qed.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.

Global Add Parametric Morphism A B : (@List.map A B)
    with signature pointwise_relation A eq ==> eq ==> eq as list_map_m.
Proof.
  intros; eapply map_ext; eauto.
Qed.

Global Add Parametric Morphism K A B : (@fmap_map K A B)
    with signature pointwise_relation A eq ==> eq ==> eq as fmap_map_m.
Proof.
  intros.
  eapply fmap_map_ext; eauto.
Qed.

(* a reformulation of [skipn] that has a better reduction behavior *)
Fixpoint my_skipn A (ls : list A) n :=
  match ls with
  | [] => []
  | a :: ls =>
    match n with
    | 0 => a :: ls
    | S n => my_skipn ls n
    end
  end.

Lemma my_skipn_0 A (ls : list A) : my_skipn ls 0 = ls.
Proof.
  induction ls; simplify; eauto.
Qed.

Lemma nth_error_Some_lt A ls :
  forall n (a : A),
    nth_error ls n = Some a ->
    n < length ls.
Proof.
  induction ls; simplify; eauto.
  {
    rewrite nth_error_nil in *.
    discriminate.
  }
  destruct n; simplify; try linear_arithmetic.
  eapply IHls in H.
  linear_arithmetic.
Qed.

Lemma length_firstn_le A (L : list A) n :
  n <= length L ->
  length (firstn n L) = n.
Proof.
  intros.
  rewrite firstn_length.
  linear_arithmetic.
Qed.

Lemma nth_error_my_skipn A (ls : list A) :
  forall x n,
    n <= length ls ->
    nth_error (my_skipn ls n) x = nth_error ls (n + x).
Proof.
  induction ls; simplify.
  {
    repeat rewrite nth_error_nil in *.
    eauto.
  }
  destruct n as [|n]; simplify; eauto.
  eapply IHls; linear_arithmetic.
Qed.

Lemma nth_error_length_firstn A L n (a : A) :
  nth_error L n = Some a ->
  length (firstn n L) = n.
Proof.
  intros Hnth.
  eapply length_firstn_le.
  eapply nth_error_Some_lt in Hnth.
  linear_arithmetic.
Qed.

Lemma nth_error_firstn A (ls : list A) :
  forall n x,
    x < n ->
    nth_error (firstn n ls) x = nth_error ls x.
Proof.
  induction ls; destruct n as [|n]; simplify; eauto; try linear_arithmetic.
  destruct x as [|x]; simplify; eauto.
  eapply IHls; linear_arithmetic.
Qed.

(* Lemma nth_error_app1 A (l : list A) l' n : n < length l -> nth_error (l++l') n = nth_error l n. *)
(* Admitted. *)

(* Lemma nth_error_app2 A (l : list A) l' n : length l <= n -> nth_error (l++l') n = nth_error l' (n-length l). *)
(* Admitted. *)

Lemma nth_error_insert A G :
  forall x y ls (t : A),
    nth_error G y = Some t ->
    x <= y ->
    nth_error (firstn x G ++ ls ++ my_skipn G x) (length ls + y) = Some t.
Proof.
  intros x y ls t Hnth Hle.
  copy Hnth Hlt.
  eapply nth_error_Some_lt in Hlt.
  rewrite nth_error_app2;
    erewrite length_firstn_le; try linear_arithmetic.
  rewrite nth_error_app2; try linear_arithmetic.
  rewrite nth_error_my_skipn by linear_arithmetic.
  rewrite <- Hnth.
  f_equal.
  linear_arithmetic.
Qed.

Lemma nth_error_before_insert A G y (t : A) x ls :
  nth_error G y = Some t ->
  y < x ->
  nth_error (firstn x G ++ ls ++ my_skipn G x) y = Some t.
Proof.
  intros Hnth Hlt.
  copy Hnth HltG.
  eapply nth_error_Some_lt in HltG.
  rewrite nth_error_app1;
    try erewrite firstn_length; try linear_arithmetic.
  rewrite nth_error_firstn; eauto.
Qed.

Lemma map_my_skipn A B (f : A -> B) ls :
  forall n,
    map f (my_skipn ls n) = my_skipn (map f ls) n.
Proof.
  induction ls; destruct n; simplify; eauto.
Qed.

(* Definition removen A n (ls : list A) := firstn n ls ++ skipn (1 + n) ls. *)
Fixpoint removen A n (ls : list A) {struct ls} :=
  match ls with
  | [] => []
  | a :: ls =>
    match n with
    | 0 => ls
    | S n => a :: removen n ls
    end
  end.

Hint Extern 0 (_ <= _) => linear_arithmetic : db_la.
Hint Extern 0 (_ = _) => linear_arithmetic : db_la.

Lemma removen_lt A ls :
  forall n (a : A) n',
    nth_error ls n = Some a ->
    n' < n ->
    nth_error (removen n ls) n' = nth_error ls n'.
Proof.
  induction ls; simplify.
  {
    rewrite nth_error_nil in *; discriminate.
  }
  destruct n as [|n]; destruct n' as [|n']; simplify; eauto with db_la.
Qed.

Require Import NPeano.
  
Lemma removen_gt' A ls :
  forall n (a : A) n',
    nth_error ls (S n') = Some a ->
    n' >= n ->
    nth_error (removen n ls) n' = nth_error ls (S n').
Proof.
  induction ls; simplify; try discriminate.
  destruct n as [|n]; destruct n' as [|n']; simplify; repeat rewrite Nat.sub_0_r in *; eauto with db_la.
Qed.

Lemma removen_gt A ls :
  forall n (a : A) n',
    nth_error ls n' = Some a ->
    n' > n ->
    nth_error (removen n ls) (n' - 1) = nth_error ls n'.
Proof.
  intros.
  destruct n' as [|n']; simplify; try linear_arithmetic.
  repeat rewrite Nat.sub_0_r in *; eauto with db_la.
  eapply removen_gt'; eauto with db_la.
Qed.

Lemma map_removen A B (f : A -> B) ls : forall n, map f (removen n ls) = removen n (map f ls).
Proof.
  induction ls; destruct n; simplify; f_equal; eauto.
Qed.

Module NNRealTime <: TIME.
  Require RIneq.
  Definition nnreal := RIneq.nonnegreal.
  Definition time_type := nnreal.
  Definition Time0 : time_type.
    Require Rdefinitions.
    Module R := Rdefinitions.
    refine (RIneq.mknonnegreal R.R0 _).
    eauto with rorders.
  Defined.
  Definition Time1 : time_type.
    refine (RIneq.mknonnegreal R.R1 _).
    eauto with rorders.
    admit.
  Admitted.
  Definition TimeAdd (a b : time_type) : time_type.
    Import RIneq.
    refine (mknonnegreal (R.Rplus (nonneg a) (nonneg b)) _).
    destruct a.
    destruct b.
    simplify.
    admit.
  Admitted.
  Definition TimeMinus (a b : time_type) : time_type.
  Admitted.
  Definition TimeLe (a b : time_type) : Prop.
    refine (R.Rle (nonneg a) (nonneg b)).
  Defined.
  Definition TimeMax : time_type -> time_type -> time_type.
  Admitted.
  
  Delimit Scope time_scope with time.
  Notation "0" := Time0 : time_scope.
  Notation "1" := Time1 : time_scope.
  Infix "+" := TimeAdd : time_scope.
  Infix "-" := TimeMinus : time_scope.
  Infix "<=" := TimeLe : time_scope.

  Lemma Time_add_le_elim a b c :
    (a + b <= c -> a <= c /\ b <= c)%time.
  Admitted.
  Lemma Time_minus_move_left a b c :
    (c <= b ->
     a + c <= b ->
     a <= b - c)%time.
  Admitted.
  Lemma Time_add_assoc a b c : (a + (b + c) = a + b + c)%time.
  Admitted.
  Lemma lhs_rotate a b c :
    (b + a <= c ->
     a + b <= c)%time.
  Admitted.
  Lemma Time_add_cancel a b c :
    (a <= b ->
     a + c <= b + c)%time.
  Admitted.
  Lemma rhs_rotate a b c :
    (a <= c + b->
     a <= b + c)%time.
  Admitted.
  Lemma Time_a_le_ba a b : (a <= b + a)%time.
  Admitted.
  Lemma Time_minus_cancel a b c :
    (a <= b -> a - c <= b - c)%time.
  Admitted.
  Lemma Time_a_minus_a a : (a - a = 0)%time.
  Admitted.
  Lemma Time_0_le_x x : (0 <= x)%time.
  Admitted.
  Lemma Time_minus_0 x : (x - 0 = x)%time.
  Admitted.
  Lemma Time_0_add x : (0 + x = x)%time.
  Admitted.
  Lemma Time_le_refl x : (x <= x)%time.
  Admitted.
  Lemma Time_le_trans a b c :
    (a <= b -> b <= c -> a <= c)%time.
  Admitted.
  Lemma Time_add_cancel2 a b c d :
    (c <= d ->
     a <= b ->
     a + c <= b + d)%time.
  Admitted.
  Lemma Time_a_le_maxab a b : (a <= TimeMax a b)%time.
  Admitted.
  Lemma Time_b_le_maxab a b : (b <= TimeMax a b)%time.
  Admitted.
  Lemma Time_add_minus_assoc a b c :
    (c <= b -> a + (b - c) = a + b - c)%time.
  Admitted.
  Lemma Time_minus_le a b : (a - b <= a)%time.
  Admitted.
  Lemma Time_minus_add_cancel a b :
    (b <= a -> a - b + b = a)%time.
  Admitted.
  Lemma Time_minus_move_right a b c :
    (c <= a ->
     a <= b + c ->
     a - c <= b)%time.
  Admitted.
  Lemma Time_le_add_minus a b c :
    (a + b - c <= a + (b - c))%time.
  Admitted.
  Lemma Time_add_comm a b : (a + b = b + a)%time.
  Admitted.
  Lemma Time_add_minus_cancel a b : (a + b - b = a)%time.
  Admitted.
  Lemma Time_minus_minus_cancel a b : (b <= a -> a - (a - b) = b)%time.
  Admitted.

End NNRealTime.

(*
Module RealTime <: TIME.
  Require Rdefinitions.
  Module R := Rdefinitions.
  Definition real := R.R.
  (* Require RIneq. *)
  (* Definition nnreal := RIneq.nonnegreal. *)
  Definition time_type := real.
  (* Definition time_type := nnreal. *)
  Definition Time0 := R.R0.
  Definition Time1 := R.R1.
  Definition TimeAdd := R.Rplus.
  Definition TimeMinus := R.Rminus.
  Definition TimeLe := R.Rle.
End RealTime.
 *)

(* Module Time := RealTime. *)
(* Module Time := NatTime. *)

Section Forall3.

  Variables A B C : Type.
  Variable R : A -> B -> C -> Prop.

  Inductive Forall3 : list A -> list B -> list C -> Prop :=
  | Forall3_nil : Forall3 [] [] []
  | Forall3_cons : forall x y z l l' l'',
      R x y z -> Forall3 l l' l'' -> Forall3 (x::l) (y::l') (z::l'').

End Forall3.

Hint Constructors Forall3.

Ltac think' ext solver :=
  repeat (match goal with
          | [ H : Some _ = Some _ |- _ ] => inversion H ; clear H ; subst
          | [ H : inl _ = inr _ |- _ ] => inversion H ; clear H ; subst
          | [ H : inr _ = inr _ |- _ ] => inversion H ; clear H ; subst
          | [ H : _ |- _ ] => erewrite H in * |- by solver
          | [ H : _ |- _ ] => erewrite H by solver
          | [ H : andb _ _ = true |- _ ] =>
            apply andb_true_iff in H ; destruct H
          | [ H : orb _ _ = false |- _ ] =>
            apply orb_false_iff in H ; destruct H
          | [ H : Equivalence.equiv _ _ |- _ ] =>
            unfold Equivalence.equiv in H ; subst
          | [ H : _ /\ _ |- _ ] => destruct H
          | [ H : exists x, _ |- _ ] => destruct H
          end || (progress ext)).

Ltac think := think' idtac ltac:(eauto).

Lemma map_nth_error_full : forall T U (F : T -> U) ls n,
    nth_error (map F ls) n = match nth_error ls n with
                             | None => None
                             | Some v => Some (F v)
                             end.
Proof.
  induction ls; destruct n; simpl; intros; think; auto.
Qed.

Lemma nth_error_map_elim : forall A B (f : A -> B) ls i b, nth_error (List.map f ls) i = Some b -> exists a, nth_error ls i = Some a /\ f a = b.
  intros.
  rewrite map_nth_error_full in H.
  destruct (option_dec (nth_error ls i)).
  destruct s; rewrite e in *; invert H; eexists; eauto.
  rewrite e in *; discriminate.
Qed.

Module M (Time : TIME).
  Import Time.

  Delimit Scope time_scope with time.
  Notation "0" := Time0 : time_scope.
  Notation "1" := Time1 : time_scope.
  Infix "+" := TimeAdd : time_scope.
  Infix "-" := TimeMinus : time_scope.
  Infix "<=" := TimeLe : time_scope.

  Module OpenScope.
    Open Scope time_scope.
  End OpenScope.

  Module CloseScope.
    Close Scope time_scope.
  End CloseScope.

  Hint Resolve Time_le_refl : time_order.
  Hint Resolve Time_le_trans : time_order.
  Hint Resolve Time_0_le_x : time_order.
  Hint Resolve Time_a_le_maxab Time_b_le_maxab : time_order.
  Hint Resolve Time_minus_le : time_order.

  Ltac rotate_lhs := eapply lhs_rotate; repeat rewrite Time_add_assoc.
  Ltac rotate_rhs := eapply rhs_rotate; repeat rewrite Time_add_assoc.
  Ltac cancel := eapply Time_add_cancel.
  Ltac finish := eapply Time_a_le_ba.
  Ltac trans_rhs h := eapply Time_le_trans; [|eapply h].
  Ltac cancel2 := eapply Time_add_cancel2; [eauto with time_order | ..].
  Ltac clear_non_le := 
    repeat match goal with
             H : _ |- _ =>
             match type of H with
             | (_ <= _)%time => fail 1
             | _ => clear H
             end
           end.

  (* The index language *)

  Inductive idx_const :=
  | ICTT
  | ICBool (b : bool)
  | ICNat (n : nat)
  | ICTime (r : time_type)
  .

  Inductive idx_un_op :=
  | IUBoolNeg
  .

  Inductive idx_bin_op :=
  | IBTimeAdd
  | IBTimeMinus
  | IBTimeMax
  .

  Inductive quan :=
  | QuanForall
  | QuanExists
  .

  Inductive prop_bin_conn :=
  | PBCAnd
  | PBCOr
  | PBCImply
  | PBCIff
  .

  Inductive prop_bin_pred :=
  | PBTimeLe
  (* | PBTimeEq *)
  | PBBigO (arity : nat)
  .

  (* base sorts *)
  Inductive bsort :=
  | BSNat
  | BSUnit
  | BSBool
  | BSTimeFun (arity : nat)
  .

  Definition var := nat.

  Inductive idx :=
  | IVar (x : var)
  | IConst (cn : idx_const)
  | IUnOp (opr : idx_un_op) (c : idx)
  | IBinOp (opr : idx_bin_op) (c1 c2 : idx)
  | IIte (i1 i2 i3 : idx)
  | ITimeAbs (i : idx)
  | ITimeApp (arity : nat) (c1 c2 : idx)
  .
  
  Inductive prop :=
  | PTrueFalse (b : bool)
  | PBinConn (opr : prop_bin_conn) (p1 p2 : prop)
  | PNot (p : prop)
  | PBinPred (opr : prop_bin_pred) (i1 i2 : idx)
  | PEq (b : bsort) (i1 i2 : idx)
  | PQuan (q : quan) (b : bsort) (p : prop)
  .
  
  Inductive sort :=
  | SBaseSort (b : bsort)
  | SSubset (s : bsort) (p : prop)
  .

  (* the type language *)
  
  Inductive ty_const :=
  | TCUnit
  | TCInt
  .

  Inductive ty_un_op :=
  | TURef
  .

  Inductive ty_bin_op :=
  | TBProd
  | TBSum
  .

  Definition kind := list bsort.
  Definition KType := @nil bsort.
  Definition KArrow := @cons bsort.
  
  (* Inductive kind := *)
  (* | KType *)
  (* | KArrow (s : bsort) (k : kind) *)
  (* . *)
  
  Inductive ty :=
  | TVar (x : var)
  | TConst (cn : ty_const)
  | TUnOp (opr : ty_un_op) (c : ty)
  | TBinOp (opr : ty_bin_op) (c1 c2 : ty)
  | TArrow (t1 : ty) (i : idx) (t2 : ty)
  | TAbs (s : bsort) (t : ty)
  | TApp (t : ty) (b : bsort) (i : idx)
  | TQuan (q : quan) (k : kind) (t : ty)
  | TQuanI (q : quan) (s : sort) (t : ty)
  | TRec (k : kind) (t : ty) (args : list (bsort * idx))
  .

  Definition SUnit := SBaseSort BSUnit.
  Definition SBool := SBaseSort BSBool.
  Definition SNat := SBaseSort BSNat.
  Definition STimeFun arity := SBaseSort (BSTimeFun arity).
  Definition STime := STimeFun 0.
  Definition BSTime := BSTimeFun 0.

  Notation Tconst r := (IConst (ICTime r)).
  Notation T0 := (Tconst Time0).
  Notation T1 := (Tconst Time1).
  Definition Tadd := IBinOp IBTimeAdd.
  Definition Tminus := IBinOp IBTimeMinus.
  Definition Tmax := IBinOp IBTimeMax.

  Definition PTrue := PTrueFalse true.
  Definition PFalse := PTrueFalse false.
  Definition PAnd := PBinConn PBCAnd.
  Definition POr := PBinConn PBCOr.
  Definition PImply := PBinConn PBCImply.
  Definition PIff := PBinConn PBCIff.

  Delimit Scope idx_scope with idx.
  Infix "+" := Tadd : idx_scope.
  (* Notation "0" := T0 : idx_scope. *)
  (* Notation "1" := T1 : idx_scope. *)

  Definition TForall := TQuan QuanForall.
  Definition TExists := TQuan QuanExists.

  Definition TUnit := TConst TCUnit.

  Definition TProd := TBinOp TBProd.
  Definition TSum := TBinOp TBSum.

  Definition Tle := PBinPred PBTimeLe.
  Definition TEq := PEq BSTime.
  Infix "<=" := Tle : idx_scope.
  Infix "==" := TEq (at level 70) : idx_scope.
  Infix "===>" := PImply (at level 95) : idx_scope.
  Infix "<===>" := PIff (at level 95) : idx_scope.
  Infix "/\" := PAnd : idx_scope.
  
  Require BinIntDef.
  Definition int := BinIntDef.Z.t.

  Definition TInt := TConst TCInt.

  Definition const_bsort cn :=
    match cn with
    | ICTT => BSUnit
    | ICBool _ => BSBool
    | ICNat _ => BSNat
    | ICTime _ => BSTime
    end
  .

  Definition iunop_arg_bsort opr :=
    match opr with
    | IUBoolNeg => BSBool
    end.

  Definition iunop_result_bsort opr :=
    match opr with
    | IUBoolNeg => BSBool
    end.

  Definition ibinop_arg1_bsort opr :=
    match opr with
    | IBTimeAdd => BSTime
    | IBTimeMinus => BSTime
    | IBTimeMax => BSTime
    end.

  Definition ibinop_arg2_bsort opr :=
    match opr with
    | IBTimeAdd => BSTime
    | IBTimeMinus => BSTime
    | IBTimeMax => BSTime
    end.

  Definition ibinop_result_bsort opr :=
    match opr with
    | IBTimeAdd => BSTime
    | IBTimeMinus => BSTime
    | IBTimeMax => BSTime
    end.

  Definition binpred_arg1_bsort opr :=
    match opr with
    | PBTimeLe => BSTime
    (* | PBTimeEq => BSTime *)
    | PBBigO n => BSTimeFun n
    end
  .

  Definition binpred_arg2_bsort opr :=
    match opr with
    | PBTimeLe => BSTime
    (* | PBTimeEq => BSTime *)
    | PBBigO n => BSTimeFun n
    end
  .

  Definition sctx := list sort.
  Definition kctx := list kind.
  
  Section shift.

    Variable n : nat.
    
    Fixpoint shift_i_i (x : var) (b : idx) : idx :=
      match b with
      | IVar y =>
        if x <=? y then
          IVar (n + y)
        else
          IVar y
      | IConst cn => IConst cn
      | IUnOp opr i => IUnOp opr (shift_i_i x i)
      | IBinOp opr c1 c2 => IBinOp opr (shift_i_i x c1) (shift_i_i x c2)
      | IIte i1 i2 i3 => IIte (shift_i_i x i1) (shift_i_i x i2) (shift_i_i x i3)
      | ITimeAbs i => ITimeAbs (shift_i_i (1 + x) i)
      | ITimeApp n c1 c2 => ITimeApp n (shift_i_i x c1) (shift_i_i x c2)
      end.
    
    Fixpoint shift_i_p (x : var) (b : prop) : prop :=
      match b with
      | PTrueFalse cn => PTrueFalse cn
      | PBinConn opr p1 p2 => PBinConn opr (shift_i_p x p1) (shift_i_p x p2)
      | PNot p => PNot (shift_i_p x p)
      | PBinPred opr i1 i2 => PBinPred opr (shift_i_i x i1) (shift_i_i x i2)
      | PEq b i1 i2 => PEq b (shift_i_i x i1) (shift_i_i x i2)
      | PQuan q b p => PQuan q b (shift_i_p (1 + x) p)
      end.

    Definition shift_i_s (x : var) (b : sort) : sort :=
      match b with
      | SBaseSort b => SBaseSort b
      | SSubset s p => SSubset s (shift_i_p (1 + x) p)
      end.

    Definition map_snd A B1 B2 (f : B1 -> B2) (a : A * B1) := (fst a, f (snd a)).
    
    Fixpoint shift_i_t (x : var) (b : ty) : ty :=
      match b with
      | TVar y => TVar y
      | TConst cn => TConst cn
      | TUnOp opr t => TUnOp opr (shift_i_t x t)
      | TBinOp opr c1 c2 => TBinOp opr (shift_i_t x c1) (shift_i_t x c2)
      | TArrow t1 i t2 => TArrow (shift_i_t x t1) (shift_i_i x i) (shift_i_t x t2)
      | TAbs b t => TAbs b (shift_i_t (1 + x) t)
      | TApp t b i => TApp (shift_i_t x t) b (shift_i_i x i)
      | TQuan q k c => TQuan q k (shift_i_t x c)
      | TQuanI q s c => TQuanI q (shift_i_s x s) (shift_i_t (1 + x) c)
      | TRec k t args => TRec k (shift_i_t x t) (map (map_snd (shift_i_i x)) args)
      end.

    Fixpoint shift_t_t (x : var) (b : ty) : ty :=
      match b with
      | TVar y =>
        if x <=? y then
          TVar (n + y)
        else
          TVar y
      | TConst cn => TConst cn
      | TUnOp opr t => TUnOp opr (shift_t_t x t)
      | TBinOp opr c1 c2 => TBinOp opr (shift_t_t x c1) (shift_t_t x c2)
      | TArrow t1 i t2 => TArrow (shift_t_t x t1) i (shift_t_t x t2)
      | TAbs s t => TAbs s (shift_t_t x t)
      | TApp t b i => TApp (shift_t_t x t) b i
      | TQuan q k c => TQuan q k (shift_t_t (1 + x) c)
      | TQuanI q s c => TQuanI q s (shift_t_t x c)
      | TRec k t args => TRec k (shift_t_t (1 + x) t) args
      end.
        
  End shift.
  
  Definition shift0_i_i := shift_i_i 1 0.
  Definition shift0_i_s := shift_i_s 1 0.
  Definition shift0_i_p := shift_i_p 1 0.
  Definition shift0_i_t := shift_i_t 1 0.
  Definition shift0_t_t := shift_t_t 1 0.

  Require Import Datatypes.

  Inductive LtEqGt (a b : nat) :=
    | MyLt : a < b -> LtEqGt a b
    | MyEq : a = b -> LtEqGt a b
    | MyGt : a > b -> LtEqGt a b
  .
  
  Definition lt_eq_gt_dec a b : LtEqGt a b :=
    match lt_eq_lt_dec a b with
    | inleft (left H) => MyLt H
    | inleft (right H) => MyEq H
    | inright H => MyGt H
    end.
  
  Infix "<=>?" := lt_eq_gt_dec (at level 70).

  Fixpoint subst_i_i (x : var) (v : idx) (b : idx) : idx :=
    match b with
    | IVar y =>
      match y <=>? x with
      | MyLt _ => IVar y
      | MyEq _ => v
      | MyGt _ => IVar (y - 1)
      end
    | IConst cn => IConst cn
    | IUnOp opr i => IUnOp opr (subst_i_i x v i)
    | IBinOp opr c1 c2 => IBinOp opr (subst_i_i x v c1) (subst_i_i x v c2)
    | IIte i1 i2 i3 => IIte (subst_i_i x v i1) (subst_i_i x v i2) (subst_i_i x v i3)
    | ITimeAbs i => ITimeAbs (subst_i_i (1 + x) (shift0_i_i v) i)
    | ITimeApp n c1 c2 => ITimeApp n (subst_i_i x v c1) (subst_i_i x v c2)
    end.
  
  Fixpoint subst_i_p (x : var) (v : idx) (b : prop) : prop :=
    match b with
    | PTrueFalse cn => PTrueFalse cn
    | PBinConn opr p1 p2 => PBinConn opr (subst_i_p x v p1) (subst_i_p x v p2)
    | PNot p => PNot (subst_i_p x v p)
    | PBinPred opr i1 i2 => PBinPred opr (subst_i_i x v i1) (subst_i_i x v i2)
    | PEq b i1 i2 => PEq b (subst_i_i x v i1) (subst_i_i x v i2)
    | PQuan q b p => PQuan q b (subst_i_p (1 + x) (shift0_i_i v) p)
    end.

  Definition subst_i_s (x : var) (v : idx) (b : sort) : sort :=
    match b with
    | SBaseSort b => SBaseSort b
    | SSubset b p => SSubset b (subst_i_p (1 + x) (shift0_i_i v) p)
    end.
  
  Fixpoint subst_i_t (x : var) (v : idx) (b : ty) : ty :=
    match b with
    | TVar y => TVar y
    | TConst cn => TConst cn
    | TUnOp opr i => TUnOp opr (subst_i_t x v i)
    | TBinOp opr c1 c2 => TBinOp opr (subst_i_t x v c1) (subst_i_t x v c2)
    | TArrow t1 i t2 => TArrow (subst_i_t x v t1) (subst_i_i x v i) (subst_i_t x v t2)
    | TAbs b t => TAbs b (subst_i_t (1 + x) (shift0_i_i v) t)
    | TApp t b i => TApp (subst_i_t x v t) b (subst_i_i x v i)
    | TQuan q k c => TQuan q k (subst_i_t x v c)
    | TQuanI q s c => TQuanI q (subst_i_s x v s) (subst_i_t (1 + x) (shift0_i_i v) c)
    | TRec k t args => TRec k (subst_i_t x v t) (map (map_snd (subst_i_i x v)) args)
    end.
      
  Fixpoint subst_t_t (x : var) (v : ty) (b : ty) : ty :=
    match b with
    | TVar y =>
      match y <=>? x with
      | MyLt _ => TVar y
      | MyEq _ => v
      | MyGt _ => TVar (y - 1)
      end
    | TConst cn => TConst cn
    | TUnOp opr t => TUnOp opr (subst_t_t x v t)
    | TBinOp opr c1 c2 => TBinOp opr (subst_t_t x v c1) (subst_t_t x v c2)
    | TArrow t1 i t2 => TArrow (subst_t_t x v t1) i (subst_t_t x v t2)
    | TAbs s t => TAbs s (subst_t_t x v t)
    | TApp t b i => TApp (subst_t_t x v t) b i
    | TQuan q k c => TQuan q k (subst_t_t (1 + x) (shift0_t_t v) c)
    | TQuanI q s c => TQuanI q s (subst_t_t x v c)
    | TRec k t args => TRec k (subst_t_t (1 + x) (shift0_t_t v) t) args
    end.
  
  Definition subst0_i_i v b := subst_i_i 0 v b.
  Definition subst0_i_t v b := subst_i_t 0 v b.
  Definition subst0_t_t v b := subst_t_t 0 v b.
  
  Ltac la := linear_arithmetic.

  Section shift_proofs.
    
    Lemma shift_i_i_0 : forall b x, shift_i_i 0 x b = b.
    Proof.
      induct b;
        simplify; cbn in *;
          try solve [f_equal; eauto].
      {
        (* Case CVar *)
        repeat match goal with
                 |- context [?a <=? ?b] => cases (a <=? b); simplify; cbn
               end; f_equal; eauto with db_la.
      }
    Qed.

    Hint Resolve shift_i_i_0.
    
    Lemma shift_i_p_0 : forall b x, shift_i_p 0 x b = b.
    Proof.
      induct b;
        simplify; cbn in *;
          try solve [f_equal; eauto].
    Qed.
    
    Hint Resolve shift_i_p_0.
    
    Lemma shift_i_s_0 : forall b x, shift_i_s 0 x b = b.
    Proof.
      induct b;
        simplify; cbn in *;
          try solve [f_equal; eauto].
    Qed.
    
    Hint Resolve shift_i_s_0.
    
    Lemma map_shift_i_i_0 x b : map (shift_i_i 0 x) b = b.
    Proof.
      induct b; simpl; f_equal; eauto.
    Qed.

    Hint Resolve map_shift_i_i_0.
    
    Arguments map_snd {A B1 B2} f a / .
    
    Lemma map_map_snd_shift_i_i_0 A x b : map (map_snd (A := A) (shift_i_i 0 x)) b = b.
    Proof.
      induct b; simpl; f_equal; eauto.
      destruct a; simpl; f_equal; eauto.
    Qed.

    Hint Resolve map_map_snd_shift_i_i_0.
    
    Lemma shift_i_t_0 :
      forall b x, shift_i_t 0 x b = b.
    Proof.
      induct b;
        simplify; cbn in *;
          try solve [f_equal; eauto].
    Qed.
    
    Lemma shift_t_t_0 :
      forall b x, shift_t_t 0 x b = b.
    Proof.
      induct b;
        simplify; cbn in *;
          try solve [f_equal; eauto].
      {
        (* Case CVar *)
        repeat match goal with
                 |- context [?a <=? ?b] => cases (a <=? b); simplify; cbn
               end; f_equal; eauto with db_la.
      }
    Qed.
    
    Lemma shift_i_i_shift_merge n1 n2 :
      forall b x y,
        x <= y ->
        y <= x + n1 ->
        shift_i_i n2 y (shift_i_i n1 x b) = shift_i_i (n1 + n2) x b.
    Proof.
      induct b;
        simplify; cbn in *;
          try solve [eauto |
                     f_equal; eauto |
                     erewrite H by la; f_equal; eauto with db_la |
                     f_equal;
                     match goal with
                       H : _ |- _ => eapply H; eauto with db_la
                     end].
      {
        (* Case CVar *)
        repeat match goal with
                 |- context [?a <=? ?b] => cases (a <=? b); simplify; cbn
               end; f_equal; la.
      }
    Qed.

    Hint Resolve shift_i_i_shift_merge.
    
    Lemma shift_i_p_shift_merge n1 n2 :
      forall b x y,
        x <= y ->
        y <= x + n1 ->
        shift_i_p n2 y (shift_i_p n1 x b) = shift_i_p (n1 + n2) x b.
    Proof.
      induct b;
        simplify; cbn in *;
          try solve [eauto |
                     f_equal; eauto |
                     erewrite H by la; f_equal; eauto with db_la |
                     f_equal;
                     match goal with
                       H : _ |- _ => eapply H; eauto with db_la
                     end].
    Qed.
    
    Hint Resolve shift_i_p_shift_merge.
    
    Lemma shift_i_s_shift_merge n1 n2 :
      forall b x y,
        x <= y ->
        y <= x + n1 ->
        shift_i_s n2 y (shift_i_s n1 x b) = shift_i_s (n1 + n2) x b.
    Proof.
      induct b;
        simplify; cbn in *;
          try solve [eauto |
                     f_equal; eauto with db_la |
                     erewrite H by la; f_equal; eauto with db_la |
                     f_equal;
                     match goal with
                       H : _ |- _ => eapply H; eauto with db_la
                     end].
    Qed.
    
    Hint Resolve shift_i_s_shift_merge.
    
    Lemma map_shift_i_i_shift_merge n1 n2 :
      forall x y,
        x <= y ->
        y <= x + n1 ->
        forall b,
          map (shift_i_i n2 y) (map (shift_i_i n1 x) b) = map (shift_i_i (n1 + n2) x) b.
    Proof.
      induct b; simpl; f_equal; eauto.
    Qed.

    Hint Resolve map_shift_i_i_shift_merge.
    
    Lemma map_map_snd_shift_i_i_shift_merge A n1 n2 :
      forall x y,
        x <= y ->
        y <= x + n1 ->
        forall b,
          map (map_snd (A := A) (shift_i_i n2 y)) (map (map_snd (shift_i_i n1 x)) b) = map (map_snd (shift_i_i (n1 + n2) x)) b.
    Proof.
      induct b; simpl; f_equal; eauto.
      destruct a; simpl; f_equal; eauto.
    Qed.

    Hint Resolve map_map_snd_shift_i_i_shift_merge.
    
    Lemma shift_i_t_shift_merge n1 n2 :
      forall b x y,
        x <= y ->
        y <= x + n1 ->
        shift_i_t n2 y (shift_i_t n1 x b) = shift_i_t (n1 + n2) x b.
    Proof.
      induct b;
        simplify; cbn in *;
          try solve [eauto |
                     f_equal; eauto |
                     erewrite H by la; f_equal; eauto with db_la |
                     f_equal;
                     eauto with db_la
                    ].
    Qed.
    
    Lemma shift_t_t_shift_merge n1 n2 :
      forall b x y,
        x <= y ->
        y <= x + n1 ->
        shift_t_t n2 y (shift_t_t n1 x b) = shift_t_t (n1 + n2) x b.
    Proof.
      induct b;
        simplify; cbn in *;
          try solve [eauto |
                     f_equal; eauto |
                     erewrite H by la; f_equal; eauto with db_la |
                     f_equal;
                     match goal with
                       H : _ |- _ => eapply H; eauto with db_la
                     end].
      {
        (* Case CVar *)
        repeat match goal with
                 |- context [?a <=? ?b] => cases (a <=? b); simplify; cbn
               end; f_equal; la.
      }
    Qed.

    Lemma shift_i_s_shift_0 b :
      forall n1 n2 x,
        x <= n1 ->
        shift_i_s n2 x (shift_i_s n1 0 b) = shift_i_s (n1 + n2) 0 b.
    Proof.
      intros.
      eapply shift_i_s_shift_merge; la.
    Qed.
    
    Lemma shift_i_i_shift_cut n1 n2 :
      forall b x y,
        x + n1 <= y ->
        shift_i_i n2 y (shift_i_i n1 x b) = shift_i_i n1 x (shift_i_i n2 (y - n1) b).
    Proof.
      induct b;
        simplify; cbn in *;
          try solve [eauto |
                     f_equal; eauto |
                     erewrite H by la; repeat f_equal; eauto with db_la |
                     try replace (S (y - n1)) with (S y - n1) by la;
                     f_equal;
                     match goal with
                       H : _ |- _ => eapply H; eauto with db_la
                     end].
      {
        (* Case CVar *)
        repeat match goal with
                 |- context [?a <=? ?b] => cases (a <=? b); simplify; cbn
               end; f_equal; la.
      }
    Qed.

    Hint Resolve shift_i_i_shift_cut.
    
    Lemma shift_i_p_shift_cut n1 n2 :
      forall b x y,
        x + n1 <= y ->
        shift_i_p n2 y (shift_i_p n1 x b) = shift_i_p n1 x (shift_i_p n2 (y - n1) b).
    Proof.
      induct b;
        simplify; cbn in *;
          try solve [eauto |
                     f_equal; eauto |
                     erewrite H by la; repeat f_equal; eauto with db_la |
                     try replace (S (y - n1)) with (S y - n1) by la;
                     f_equal;
                     match goal with
                       H : _ |- _ => eapply H; eauto with db_la
                     end].
    Qed.
    
    Hint Resolve shift_i_p_shift_cut.
    
    Lemma shift_i_s_shift_cut n1 n2 :
      forall b x y,
        x + n1 <= y ->
        shift_i_s n2 y (shift_i_s n1 x b) = shift_i_s n1 x (shift_i_s n2 (y - n1) b).
    Proof.
      induct b;
        simplify; cbn in *;
          try solve [eauto |
                     f_equal; eauto with db_la |
                     erewrite H by la; repeat f_equal; eauto with db_la |
                     try replace (S (y - n1)) with (S y - n1) by la; f_equal; eauto with db_la
                    ].
    Qed.
    
    Hint Resolve shift_i_s_shift_cut.
    
    Lemma map_shift_i_i_shift_cut n1 n2 :
      forall x y,
        x + n1 <= y ->
        forall b,
          map (shift_i_i n2 y) (map (shift_i_i n1 x) b) = map (shift_i_i n1 x) (map (shift_i_i n2 (y - n1)) b).
    Proof.
      induct b; simpl; f_equal; eauto.
    Qed.

    Hint Resolve map_shift_i_i_shift_cut.
    
    Lemma map_map_snd_shift_i_i_shift_cut A n1 n2 :
      forall x y,
        x + n1 <= y ->
        forall b,
          map (map_snd (A := A) (shift_i_i n2 y)) (map (map_snd (shift_i_i n1 x)) b) = map (map_snd (shift_i_i n1 x)) (map (map_snd (shift_i_i n2 (y - n1))) b).
    Proof.
      induct b; simpl; f_equal; eauto.
      destruct a; simpl; f_equal; eauto.
    Qed.

    Hint Resolve map_map_snd_shift_i_i_shift_cut.
    
    Lemma shift_i_t_shift_cut n1 n2 :
      forall b x y,
        x + n1 <= y ->
        shift_i_t n2 y (shift_i_t n1 x b) = shift_i_t n1 x (shift_i_t n2 (y - n1) b).
    Proof.
      induct b;
        simplify; cbn in *;
          try solve [eauto |
                     f_equal; eauto |
                     erewrite H by la; repeat f_equal; eauto with db_la |
                     try replace (S (y - n1)) with (S y - n1) by la; f_equal; eauto with db_la
                    ].
    Qed.
    
    Lemma shift_t_t_shift_cut n1 n2 :
      forall b x y,
        x + n1 <= y ->
        shift_t_t n2 y (shift_t_t n1 x b) = shift_t_t n1 x (shift_t_t n2 (y - n1) b).
    Proof.
      induct b;
        simplify; cbn in *;
          try solve [eauto |
                     f_equal; eauto |
                     erewrite H by la; repeat f_equal; eauto with db_la |
                     try replace (S (y - n1)) with (S y - n1) by la; f_equal; eauto with db_la
                    ].
      {
        (* Case CVar *)
        repeat match goal with
                 |- context [?a <=? ?b] => cases (a <=? b); simplify; cbn
               end; f_equal; la.
      }
    Qed.
    
    Lemma shift_i_s_shift_2 b :
      forall n1 n2 x,
        n1 <= x ->
        shift_i_s n2 x (shift_i_s n1 0 b) = shift_i_s n1 0 (shift_i_s n2 (x - n1) b).
    Proof.
      intros.
      eapply shift_i_s_shift_cut; la.
    Qed.
    
    Lemma shift_i_i_shift b :
      forall n1 n2 x,
        shift_i_i n2 x (shift_i_i n1 x b) = shift_i_i (n1 + n2) x b.
    Proof.
      intros.
      eapply shift_i_i_shift_merge; la.
    Qed.
    
    Lemma shift_i_i_shift0 n b :
      shift_i_i n 0 (shift0_i_i b) = shift_i_i (S n) 0 b.
    Proof.
      intros.
      eapply shift_i_i_shift_merge; la.
    Qed.
    
    Lemma shift0_i_i_shift_0 n c :
      shift0_i_i (shift_i_i n 0 c) = shift_i_i (1 + n) 0 c.
    Proof.
      unfold shift0_i_i; intros.
      rewrite shift_i_i_shift_merge; f_equal; la.
    Qed.
    
    Lemma shift0_t_t_shift_0 n c :
      shift0_t_t (shift_t_t n 0 c) = shift_t_t (1 + n) 0 c.
    Proof.
      unfold shift0_t_t; intros.
      rewrite shift_t_t_shift_merge; f_equal; la.
    Qed.
    
    Lemma shift0_i_i_shift n x b :
      shift0_i_i (shift_i_i n x b) = shift_i_i n (1 + x) (shift0_i_i b).
    Proof.
      unfold shift0_i_i; intros.
      symmetry.
      rewrite shift_i_i_shift_cut; repeat f_equal; la.
    Qed.

    Lemma shift0_t_t_shift n x b :
      shift0_t_t (shift_t_t n x b) = shift_t_t n (1 + x) (shift0_t_t b).
    Proof.
      unfold shift0_t_t; intros.
      symmetry.
      rewrite shift_t_t_shift_cut; repeat f_equal; la.
    Qed.

  End shift_proofs.

  Section subst_proofs.
    
    Lemma subst0_i_i_Const v cn : subst0_i_i v (IConst cn) = IConst cn.
    Proof.
      cbn in *; eauto.
    Qed.

    Lemma subst_i_i_shift_avoid n :
      forall b v x y,
        x <= y ->
        y < x + n ->
        subst_i_i y v (shift_i_i n x b) = shift_i_i (n - 1) x b.
    Proof.
      induct b;
        simplify; cbn in *;
          try solve [eauto |
                     f_equal; eauto |
                     erewrite H by la; repeat f_equal; eauto with db_la |
                     repeat replace (S (y - n)) with (S y - n) by la;
                     f_equal;
                     match goal with
                       H : _ |- _ => eapply H; eauto with db_la
                     end].
      {
        (* Case CVar *)
        repeat match goal with
               | |- context [?a <=? ?b] => cases (a <=? b); simplify; cbn
               | |- context [?a <=>? ?b] => cases (a <=>? b); simplify; cbn
               end; try solve [f_equal; la].
      }
    Qed.

    Hint Resolve subst_i_i_shift_avoid.
    
    Lemma subst_i_p_shift_avoid n :
      forall b v x y,
        x <= y ->
        y < x + n ->
        subst_i_p y v (shift_i_p n x b) = shift_i_p (n - 1) x b.
    Proof.
      induct b;
        simplify; cbn in *;
          try solve [eauto |
                     f_equal; eauto |
                     erewrite H by la; repeat f_equal; eauto with db_la |
                     repeat replace (S (y - n)) with (S y - n) by la;
                     f_equal;
                     match goal with
                       H : _ |- _ => eapply H; eauto with db_la
                     end].
    Qed.
    
    Hint Resolve subst_i_p_shift_avoid.
    
    Lemma subst_i_s_shift_avoid n :
      forall b v x y,
        x <= y ->
        y < x + n ->
        subst_i_s y v (shift_i_s n x b) = shift_i_s (n - 1) x b.
    Proof.
      induct b;
        simplify; cbn in *;
          try solve [eauto |
                     f_equal; eauto with db_la |
                     erewrite H by la; repeat f_equal; eauto with db_la |
                     repeat replace (S (y - n)) with (S y - n) by la;
                     f_equal;
                     match goal with
                       H : _ |- _ => eapply H; eauto with db_la
                     end].
    Qed.
    
    Hint Resolve subst_i_s_shift_avoid.
    
    Lemma map_subst_i_i_shift_avoid n :
      forall v x y,
        x <= y ->
        y < x + n ->
        forall b,
          map (subst_i_i y v) (map (shift_i_i n x) b) = map (shift_i_i (n - 1) x) b.
    Proof.
      induct b; simpl; f_equal; eauto.
    Qed.

    Hint Resolve map_subst_i_i_shift_avoid.
    
    Arguments map_snd {A B1 B2} f a / .
    
    Lemma map_map_snd_subst_i_i_shift_avoid A n :
      forall v x y,
        x <= y ->
        y < x + n ->
        forall b,
          map (map_snd (A := A) (subst_i_i y v)) (map (map_snd (shift_i_i n x)) b) = map (map_snd (shift_i_i (n - 1) x)) b.
    Proof.
      induct b; simpl; f_equal; eauto.
      destruct a; simpl; f_equal; eauto.
    Qed.

    Hint Resolve map_map_snd_subst_i_i_shift_avoid.
    
    Lemma subst_i_t_shift_avoid n :
      forall b v x y,
        x <= y ->
        y < x + n ->
        subst_i_t y v (shift_i_t n x b) = shift_i_t (n - 1) x b.
    Proof.
      induct b;
        simplify; cbn in *;
          try solve [eauto |
                     f_equal; eauto |
                     erewrite H by la; repeat f_equal; eauto with db_la |
                     repeat replace (S (y - n)) with (S y - n) by la;
                     f_equal;
                     eauto with db_la
                    ].
    Qed.
    
    Lemma subst_t_t_shift_avoid n :
      forall b v x y,
        x <= y ->
        y < x + n ->
        subst_t_t y v (shift_t_t n x b) = shift_t_t (n - 1) x b.
    Proof.
      induct b;
        simplify; cbn in *;
          try solve [eauto |
                     f_equal; eauto |
                     erewrite H by la; repeat f_equal; eauto with db_la |
                     repeat replace (S (y - n)) with (S y - n) by la;
                     f_equal;
                     match goal with
                       H : _ |- _ => eapply H; eauto with db_la
                     end].
      {
        (* Case CVar *)
        repeat match goal with
               | |- context [?a <=? ?b] => cases (a <=? b); simplify; cbn
               | |- context [?a <=>? ?b] => cases (a <=>? b); simplify; cbn
               end; try solve [f_equal; la].
      }
    Qed.
    
    Lemma subst_i_s_shift_0_avoid x y v b :
      y < x ->
      subst_i_s y (shift_i_i y 0 v) (shift_i_s x 0 b) = shift_i_s (x - 1) 0 b.
    Proof.
      intros.
      eapply subst_i_s_shift_avoid; la.
    Qed.
    
    Lemma subst0_i_i_shift0 v b :
      subst0_i_i v (shift0_i_i b) = b.
    Proof.
      unfold shift0_i_i, subst0_i_i.
      specialize (@subst_i_i_shift_avoid 1 b v 0 0); intros H; simplify.
      repeat rewrite shift_i_i_0 in *.
      eauto with db_la.
    Qed.
    
    Lemma subst_i_i_shift_hit v n :
      forall b x y,
        x + n <= y ->
        subst_i_i y (shift_i_i y 0 v) (shift_i_i n x b) = shift_i_i n x (subst_i_i (y - n) (shift_i_i (y - n) 0 v) b).
    Proof.
      induct b;
        simplify; cbn in *;
          try solve [eauto |
                     f_equal; eauto |
                     erewrite H by la; repeat f_equal; eauto with db_la |
                     repeat rewrite shift0_i_i_shift_0; simplify;
                     repeat replace (S (y - n)) with (S y - n) by la;
                     f_equal;
                     match goal with
                       H : _ |- _ => eapply H; eauto with db_la
                     end].
      {
        (* Case CVar *)
        repeat match goal with
               | |- context [?a <=? ?b] => cases (a <=? b); simplify; cbn
               | |- context [?a <=>? ?b] => cases (a <=>? b); simplify; cbn
               end; try solve [f_equal; la].
        rewrite shift_i_i_shift_merge by la.
        f_equal; eauto with db_la.
      }
    Qed.
    
    Hint Resolve subst_i_i_shift_hit.
    
    Lemma subst_i_p_shift_hit v n :
      forall b x y,
        x + n <= y ->
        subst_i_p y (shift_i_i y 0 v) (shift_i_p n x b) = shift_i_p n x (subst_i_p (y - n) (shift_i_i (y - n) 0 v) b).
    Proof.
      induct b;
        simplify; cbn in *;
          try solve [eauto |
                     f_equal; eauto |
                     erewrite H by la; repeat f_equal; eauto with db_la |
                     repeat rewrite shift0_i_i_shift_0; simplify;
                     repeat replace (S (y - n)) with (S y - n) by la;
                     f_equal;
                     match goal with
                       H : _ |- _ => eapply H; eauto with db_la
                     end].
    Qed.
    
    Hint Resolve subst_i_p_shift_hit.
    
    Lemma subst_i_s_shift_hit v n :
      forall b x y,
        x + n <= y ->
        subst_i_s y (shift_i_i y 0 v) (shift_i_s n x b) = shift_i_s n x (subst_i_s (y - n) (shift_i_i (y - n) 0 v) b).
    Proof.
      induct b;
        simplify; cbn in *;
          try solve [eauto |
                     f_equal; eauto with db_la |
                     erewrite H by la; repeat f_equal; eauto with db_la |
                     repeat rewrite shift0_i_i_shift_0; simplify;
                     repeat replace (S (y - n)) with (S y - n) by la;
                     f_equal;
                     eauto with db_la
                    ].
    Qed.
    
    Hint Resolve subst_i_s_shift_hit.
    
    Lemma map_subst_i_i_shift_hit v n :
      forall x y,
        x + n <= y ->
        forall b,
          map (subst_i_i y (shift_i_i y 0 v)) (map (shift_i_i n x) b) = map (shift_i_i n x) (map (subst_i_i (y - n) (shift_i_i (y - n) 0 v)) b).
    Proof.
      induct b; simpl; f_equal; eauto.
    Qed.
    
    Hint Resolve map_subst_i_i_shift_hit.
    
    Lemma map_map_snd_subst_i_i_shift_hit A v n :
      forall x y,
        x + n <= y ->
        forall b,
          map (map_snd (A := A) (subst_i_i y (shift_i_i y 0 v))) (map (map_snd (shift_i_i n x)) b) = map (map_snd (shift_i_i n x)) (map (map_snd (subst_i_i (y - n) (shift_i_i (y - n) 0 v))) b).
    Proof.
      induct b; simpl; f_equal; eauto.
      destruct a; simpl; f_equal; eauto.
    Qed.
    
    Hint Resolve map_map_snd_subst_i_i_shift_hit.
    
    Lemma subst_i_t_shift_hit v n :
      forall b x y,
        x + n <= y ->
        subst_i_t y (shift_i_i y 0 v) (shift_i_t n x b) = shift_i_t n x (subst_i_t (y - n) (shift_i_i (y - n) 0 v) b).
    Proof.
      induct b;
        simplify; cbn in *;
          try solve [eauto |
                     f_equal; eauto |
                     erewrite H by la; repeat f_equal; eauto with db_la |
                     repeat rewrite shift0_i_i_shift_0; simplify;
                     repeat replace (S (y - n)) with (S y - n) by la;
                     f_equal;
                     eauto with db_la 
                    ].
    Qed.
    
    Lemma subst_t_t_shift_hit v n :
      forall b x y,
        x + n <= y ->
        subst_t_t y (shift_t_t y 0 v) (shift_t_t n x b) = shift_t_t n x (subst_t_t (y - n) (shift_t_t (y - n) 0 v) b).
    Proof.
      induct b;
        simplify; cbn in *;
          try solve [eauto |
                     f_equal; eauto |
                     erewrite H by la; repeat f_equal; eauto with db_la |
                     repeat rewrite shift0_t_t_shift_0; simplify;
                     repeat replace (S (y - n)) with (S y - n) by la;
                     f_equal;
                     eauto with db_la 
                    ].
      {
        (* Case CVar *)
        repeat match goal with
               | |- context [?a <=? ?b] => cases (a <=? b); simplify; cbn
               | |- context [?a <=>? ?b] => cases (a <=>? b); simplify; cbn
               end; try solve [f_equal; la].
        rewrite shift_t_t_shift_merge by la.
        f_equal; eauto with db_la.
      }
    Qed.
    
    Lemma subst_i_s_shift x y v b :
      x <= y ->
      subst_i_s y (shift_i_i y 0 v) (shift_i_s x 0 b) = shift_i_s x 0 (subst_i_s (y - x) (shift_i_i (y - x) 0 v) b).
    Proof.
      intros.
      eapply subst_i_s_shift_hit; la.
    Qed.

    Lemma shift_i_i_subst_in n :
      forall b v x y,
        y <= x ->
        shift_i_i n y (subst_i_i x v b) = subst_i_i (x + n) (shift_i_i n y v) (shift_i_i n y b).
    Proof.
      induct b;
        simplify; cbn in *;
          try solve [eauto |
                     f_equal; eauto |
                     erewrite H by la; repeat f_equal; eauto with db_la |
                     repeat rewrite shift0_i_i_shift; simplify;
                     repeat replace (S (y - n)) with (S y - n) by la;
                     f_equal;
                     match goal with
                       H : _ |- _ => eapply H; eauto with db_la
                     end].
      {
        (* Case CVar *)
        repeat match goal with
               | |- context [?a <=? ?b] => cases (a <=? b); simplify; cbn
               | |- context [?a <=>? ?b] => cases (a <=>? b); simplify; cbn
               end; try solve [f_equal; la].
      }
    Qed.
    
    Hint Resolve shift_i_i_subst_in.
    
    Lemma shift_i_p_subst_in n :
      forall b v x y,
        y <= x ->
        shift_i_p n y (subst_i_p x v b) = subst_i_p (x + n) (shift_i_i n y v) (shift_i_p n y b).
    Proof.
      induct b;
        simplify; cbn in *;
          try solve [eauto |
                     f_equal; eauto |
                     erewrite H by la; repeat f_equal; eauto with db_la |
                     repeat rewrite shift0_i_i_shift; simplify;
                     repeat replace (S (y - n)) with (S y - n) by la;
                     f_equal;
                     match goal with
                       H : _ |- _ => eapply H; eauto with db_la
                     end].
    Qed.
    
    Hint Resolve shift_i_p_subst_in.
    
    Lemma shift_i_s_subst_in n :
      forall b v x y,
        y <= x ->
        shift_i_s n y (subst_i_s x v b) = subst_i_s (x + n) (shift_i_i n y v) (shift_i_s n y b).
    Proof.
      induct b;
        simplify; cbn in *;
          try solve [eauto |
                     f_equal; eauto with db_la |
                     erewrite H by la; repeat f_equal; eauto with db_la |
                     repeat rewrite shift0_i_i_shift; simplify;
                     repeat replace (S (x + n)) with (S x + n) by la;
                     f_equal;
                     eauto with db_la
                    ].
    Qed.
    
    Hint Resolve shift_i_s_subst_in.
    
    Lemma map_shift_i_i_subst_in n :
      forall v x y,
        y <= x ->
        forall b,
          map (shift_i_i n y) (map (subst_i_i x v) b) = map (subst_i_i (x + n) (shift_i_i n y v)) (map (shift_i_i n y) b).
    Proof.
      induct b; simpl; f_equal; eauto.
    Qed.
    
    Hint Resolve map_shift_i_i_subst_in.
    
    Lemma map_map_snd_shift_i_i_subst_in A n :
      forall v x y,
        y <= x ->
        forall b,
          map (map_snd (A := A) (shift_i_i n y)) (map (map_snd (subst_i_i x v)) b) = map (map_snd (subst_i_i (x + n) (shift_i_i n y v))) (map (map_snd (shift_i_i n y)) b).
    Proof.
      induct b; simpl; f_equal; eauto.
      destruct a; simpl; f_equal; eauto.
    Qed.
    
    Hint Resolve map_map_snd_shift_i_i_subst_in.
    
    Lemma shift_i_t_subst_in n :
      forall b v x y,
        y <= x ->
        shift_i_t n y (subst_i_t x v b) = subst_i_t (x + n) (shift_i_i n y v) (shift_i_t n y b).
    Proof.
      induct b;
        simplify; cbn in *;
          try solve [eauto |
                     f_equal; eauto with db_la |
                     erewrite H by la; repeat f_equal; eauto with db_la |
                     repeat rewrite shift0_i_i_shift; simplify;
                     repeat replace (S (x + n)) with (S x + n) by la;
                     f_equal;
                     eauto with db_la
                    ].
    Qed.
    
    Lemma shift_t_t_subst_in n :
      forall b v x y,
        y <= x ->
        shift_t_t n y (subst_t_t x v b) = subst_t_t (x + n) (shift_t_t n y v) (shift_t_t n y b).
    Proof.
      induct b;
        simplify; cbn in *;
          try solve [eauto |
                     f_equal; eauto with db_la |
                     erewrite H by la; repeat f_equal; eauto with db_la |
                     repeat rewrite shift0_t_t_shift; simplify;
                     repeat replace (S (x + n)) with (S x + n) by la;
                     f_equal;
                     eauto with db_la
                    ].
      {
        (* Case CVar *)
        repeat match goal with
               | |- context [?a <=? ?b] => cases (a <=? b); simplify; cbn
               | |- context [?a <=>? ?b] => cases (a <=>? b); simplify; cbn
               end; try solve [f_equal; la].
      }
    Qed.
    
    Lemma shift0_i_i_subst x v b :
      shift0_i_i (subst_i_i x (shift_i_i x 0 v) b) = subst_i_i (1 + x) (shift_i_i (1 + x) 0 v) (shift0_i_i b).
    Proof.
      unfold shift0_i_i, subst0_i_i.
      rewrite shift_i_i_subst_in by la.
      rewrite shift_i_i_shift_merge by la.
      repeat (f_equal; try la).
    Qed.

    Lemma shift0_i_i_subst_2 x v b :
      shift0_i_i (subst_i_i x v b) = subst_i_i (1 + x) (shift0_i_i v) (shift0_i_i b).
    Proof.
      unfold shift0_i_i, subst0_i_i.
      rewrite shift_i_i_subst_in by la.
      repeat (f_equal; try la).
    Qed.

    Lemma shift0_t_t_subst_2 x v b :
      shift0_t_t (subst_t_t x v b) = subst_t_t (1 + x) (shift0_t_t v) (shift0_t_t b).
    Proof.
      unfold shift0_t_t, subst0_t_t.
      rewrite shift_t_t_subst_in by la.
      repeat (f_equal; try la).
    Qed.

    Opaque le_lt_dec.
    
    Lemma shift_i_i_subst_out n :
      forall b v x y,
        x <= y ->
        shift_i_i n y (subst_i_i x v b) = subst_i_i x (shift_i_i n y v) (shift_i_i n (S y) b).
    Proof.
      induct b;
        simplify;
        cbn in *;
        try solve [eauto |
                   f_equal; eauto |
                   erewrite H by la; repeat f_equal; eauto with db_la |
                   repeat rewrite shift0_i_i_shift; simplify;
                   repeat replace (S (y - n)) with (S y - n) by la;
                   f_equal;
                   match goal with
                     H : _ |- _ => eapply H; eauto with db_la
                   end].
      {
        (* Case CVar *)
        repeat match goal with
               | |- context [?a <=? ?b] => cases (a <=? b); simplify; cbn
               | |- context [?a <=>? ?b] => cases (a <=>? b); simplify; cbn
               end; try solve [f_equal; la].
      }
    Qed.
    
    Hint Resolve shift_i_i_subst_out.
    
    Lemma shift_i_p_subst_out n :
      forall b v x y,
        x <= y ->
        shift_i_p n y (subst_i_p x v b) = subst_i_p x (shift_i_i n y v) (shift_i_p n (S y) b).
    Proof.
      induct b;
        simplify;
        cbn in *;
        try solve [eauto |
                   f_equal; eauto |
                   erewrite H by la; repeat f_equal; eauto with db_la |
                   repeat rewrite shift0_i_i_shift; simplify;
                   f_equal;
                   eauto with db_la
                  ].
    Qed.
    
    Hint Resolve shift_i_p_subst_out.
    
    Lemma shift_i_s_subst_out n :
      forall b v x y,
        x <= y ->
        shift_i_s n y (subst_i_s x v b) = subst_i_s x (shift_i_i n y v) (shift_i_s n (S y) b).
    Proof.
      induct b;
        simplify;
        cbn in *;
        try solve [eauto |
                   f_equal; eauto |
                   erewrite H by la; repeat f_equal; eauto with db_la |
                   repeat rewrite shift0_i_i_shift; simplify;
                   f_equal;
                   eauto with db_la
                  ].
    Qed.
    
    Hint Resolve shift_i_s_subst_out.
    
    Lemma map_shift_i_i_subst_out n :
      forall v x y,
        x <= y ->
        forall b,
          map (shift_i_i n y) (map (subst_i_i x v) b) = map (subst_i_i x (shift_i_i n y v)) (map (shift_i_i n (S y)) b).
    Proof.
      induct b; simpl; f_equal; eauto.
    Qed.
    
    Hint Resolve map_shift_i_i_subst_out.
    
    Lemma map_map_snd_shift_i_i_subst_out A n :
      forall v x y,
        x <= y ->
        forall b,
          map (map_snd (A := A) (shift_i_i n y)) (map (map_snd (subst_i_i x v)) b) = map (map_snd (subst_i_i x (shift_i_i n y v))) (map (map_snd (shift_i_i n (S y))) b).
    Proof.
      induct b; simpl; f_equal; eauto.
      destruct a; simpl; f_equal; eauto.
    Qed.
    
    Hint Resolve map_map_snd_shift_i_i_subst_out.
    
    Lemma shift_i_t_subst_out n :
      forall b v x y,
        x <= y ->
        shift_i_t n y (subst_i_t x v b) = subst_i_t x (shift_i_i n y v) (shift_i_t n (S y) b).
    Proof.
      induct b;
        simplify;
        cbn in *;
        try solve [eauto |
                   f_equal; eauto |
                   erewrite H by la; repeat f_equal; eauto with db_la |
                   repeat rewrite shift0_i_i_shift; simplify;
                   repeat replace (S (y - n)) with (S y - n) by la;
                   f_equal;
                   eauto with db_la
                  ].
    Qed.
    
    Lemma shift_t_t_subst_out n :
      forall b v x y,
        x <= y ->
        shift_t_t n y (subst_t_t x v b) = subst_t_t x (shift_t_t n y v) (shift_t_t n (S y) b).
    Proof.
      induct b;
        simplify;
        cbn in *;
        try solve [eauto |
                   f_equal; eauto |
                   erewrite H by la; repeat f_equal; eauto with db_la |
                   repeat rewrite shift0_t_t_shift; simplify;
                   repeat replace (S (y - n)) with (S y - n) by la;
                   f_equal;
                   eauto with db_la
                  ].
      {
        (* Case CVar *)
        repeat match goal with
               | |- context [?a <=? ?b] => cases (a <=? b); simplify; cbn
               | |- context [?a <=>? ?b] => cases (a <=>? b); simplify; cbn
               end; try solve [f_equal; la].
      }
    Qed.
    
    Lemma shift_i_i_subst0 n x v b : shift_i_i n x (subst0_i_i v b) = subst0_i_i (shift_i_i n x v) (shift_i_i n (S x) b).
    Proof.
      unfold shift0_i_i, subst0_i_i.
      rewrite shift_i_i_subst_out; repeat (f_equal; try la).
    Qed.
    
    Lemma subst_i_i_subst :
      forall b v1 v2 x y,
        x <= y ->
        subst_i_i y v2 (subst_i_i x v1 b) = subst_i_i x (subst_i_i y v2 v1) (subst_i_i (S y) (shift_i_i 1 x v2) b).
    Proof.
      induct b;
        simplify;
        cbn in *;
        try solve [eauto |
                   f_equal; eauto |
                   erewrite H by la; repeat f_equal; eauto with db_la |
                   repeat rewrite shift0_i_i_shift; simplify;
                   repeat rewrite shift0_i_i_subst_2; simplify;
                   repeat replace (S (y - n)) with (S y - n) by la;
                   f_equal;
                   match goal with
                     H : _ |- _ => eapply H; eauto with db_la
                   end].
      {
        (* Case CVar *)
        repeat match goal with
               | |- context [?a <=? ?b] => cases (a <=? b); simplify; cbn
               | |- context [?a <=>? ?b] => cases (a <=>? b); simplify; cbn
               end; try solve [f_equal; la].
        rewrite subst_i_i_shift_avoid by la.
        simplify.
        rewrite shift_i_i_0.
        eauto.
      }
    Qed.

    Hint Resolve subst_i_i_subst.
    
    Lemma subst_i_p_subst :
      forall b v1 v2 x y,
        x <= y ->
        subst_i_p y v2 (subst_i_p x v1 b) = subst_i_p x (subst_i_i y v2 v1) (subst_i_p (S y) (shift_i_i 1 x v2) b).
    Proof.
      induct b;
        simplify;
        cbn in *;
        try solve [eauto |
                   f_equal; eauto |
                   erewrite H by la; repeat f_equal; eauto with db_la |
                   repeat rewrite shift0_i_i_shift; simplify;
                   repeat rewrite shift0_i_i_subst_2; simplify;
                   repeat replace (S (y - n)) with (S y - n) by la;
                   f_equal;
                   match goal with
                     H : _ |- _ => eapply H; eauto with db_la
                   end].
    Qed.

    Hint Resolve subst_i_p_subst.
    
    Lemma subst_i_s_subst :
      forall b v1 v2 x y,
        x <= y ->
        subst_i_s y v2 (subst_i_s x v1 b) = subst_i_s x (subst_i_i y v2 v1) (subst_i_s (S y) (shift_i_i 1 x v2) b).
    Proof.
      induct b;
        simplify;
        cbn in *;
        try solve [eauto |
                   f_equal; eauto |
                   erewrite H by la; repeat f_equal; eauto with db_la |
                   repeat rewrite shift0_i_i_shift; simplify;
                   repeat rewrite shift0_i_i_subst_2; simplify;
                   repeat replace (S (y - n)) with (S y - n) by la;
                   f_equal;
                   eauto with db_la
                  ].
    Qed.

    Hint Resolve subst_i_s_subst.
    
    Lemma map_subst_i_i_subst :
      forall v1 v2 x y,
        x <= y ->
        forall b,
          map (subst_i_i y v2) (map (subst_i_i x v1) b) = map (subst_i_i x (subst_i_i y v2 v1)) (map (subst_i_i (S y) (shift_i_i 1 x v2)) b).
    Proof.
      induct b; simpl; f_equal; eauto.
    Qed.

    Hint Resolve map_subst_i_i_subst.
    
    Lemma map_map_snd_subst_i_i_subst A :
      forall v1 v2 x y,
        x <= y ->
        forall b,
          map (map_snd (A := A) (subst_i_i y v2)) (map (map_snd (subst_i_i x v1)) b) = map (map_snd (subst_i_i x (subst_i_i y v2 v1))) (map (map_snd (subst_i_i (S y) (shift_i_i 1 x v2))) b).
    Proof.
      induct b; simpl; f_equal; eauto.
      destruct a; simpl; f_equal; eauto.
    Qed.

    Hint Resolve map_map_snd_subst_i_i_subst.
    
    Lemma subst_i_t_subst :
      forall b v1 v2 x y,
        x <= y ->
        subst_i_t y v2 (subst_i_t x v1 b) = subst_i_t x (subst_i_i y v2 v1) (subst_i_t (S y) (shift_i_i 1 x v2) b).
    Proof.
      induct b;
        simplify;
        cbn in *;
        try solve [eauto |
                   f_equal; eauto |
                   erewrite H by la; repeat f_equal; eauto with db_la |
                   repeat rewrite shift0_i_i_shift; simplify;
                   repeat rewrite shift0_i_i_subst_2; simplify;
                   repeat replace (S (y - n)) with (S y - n) by la;
                   f_equal;
                   eauto with db_la
                  ].
    Qed.
    
    Lemma subst_t_t_subst :
      forall b v1 v2 x y,
        x <= y ->
        subst_t_t y v2 (subst_t_t x v1 b) = subst_t_t x (subst_t_t y v2 v1) (subst_t_t (S y) (shift_t_t 1 x v2) b).
    Proof.
      induct b;
        simplify;
        cbn in *;
        try solve [eauto |
                   f_equal; eauto |
                   erewrite H by la; repeat f_equal; eauto with db_la |
                   repeat rewrite shift0_t_t_shift; simplify;
                   repeat rewrite shift0_t_t_subst_2; simplify;
                   repeat replace (S (y - n)) with (S y - n) by la;
                   f_equal;
                   eauto with db_la
                  ].
      {
        (* Case CVar *)
        repeat match goal with
               | |- context [?a <=? ?b] => cases (a <=? b); simplify; cbn
               | |- context [?a <=>? ?b] => cases (a <=>? b); simplify; cbn
               end; try solve [f_equal; la].
        rewrite subst_t_t_shift_avoid by la.
        simplify.
        rewrite shift_t_t_0.
        eauto.
      }
    Qed.
    
    Lemma subst_i_i_subst0 n c c' t : subst_i_i n c (subst0_i_i c' t) = subst0_i_i (subst_i_i n c c') (subst_i_i (S n) (shift0_i_i c) t).
    Proof.
      eapply subst_i_i_subst.
      la.
    Qed.
    
    Lemma map_shift0_subst n c ls :
      map shift0_i_i (map (subst_i_i n (shift_i_i n 0 c)) ls) =
      map (subst_i_i (1 + n) (shift_i_i (1 + n) 0 c)) (map shift0_i_i ls).
    Proof.
      repeat rewrite map_map.
      setoid_rewrite shift0_i_i_subst.
      eauto.
    Qed.

  End subst_proofs.
  
  Fixpoint time_fun (arity : nat) :=
    match arity with
    | 0 => time_type
    | S n => nat -> time_fun n
    end.

  Definition interp_bsort (b : bsort) :=
    match b with
    | BSNat => nat
    | BSUnit => unit
    | BSBool => bool
    | BSTimeFun arity => time_fun arity
    end.

  Fixpoint time_fun_default_value arity : time_fun arity :=
    match arity with
    | 0 => 0%time
    | S n => fun _ : nat => time_fun_default_value n
    end.
  
  Definition sort_default_value (b : bsort) : interp_bsort b :=
    match b with
    | BSNat => 0%nat
    | BSUnit => tt
    | BSBool => false
    | BSTimeFun arity => time_fun_default_value arity
    end.

  Fixpoint interp_bsorts arg_ks res :=
    match arg_ks with
    | [] => res
    | arg_k :: arg_ks => interp_bsorts arg_ks (interp_bsort arg_k -> res)
    end.

  Fixpoint lift0 arg_ks t : t -> interp_bsorts arg_ks t :=
    match arg_ks return t -> interp_bsorts arg_ks t with
    | [] => id
    | arg_k :: arg_ks =>
      fun f => lift0 arg_ks (fun ak => f)
    end.

  Fixpoint lift1 arg_ks t1 t : (t1 -> t) -> interp_bsorts arg_ks t1 -> interp_bsorts arg_ks t :=
    match arg_ks return (t1 -> t) -> interp_bsorts arg_ks t1 -> interp_bsorts arg_ks t with
    | [] =>
      fun f x1 => f x1
    | arg_k :: arg_ks =>
      fun f x1 => lift1 arg_ks (fun a1 ak => f (a1 ak)) x1
    end.
  
  Fixpoint lift2 arg_ks : forall t1 t2 t, (t1 -> t2 -> t) -> interp_bsorts arg_ks t1 -> interp_bsorts arg_ks t2 -> interp_bsorts arg_ks t :=
    match arg_ks return forall t1 t2 t, (t1 -> t2 -> t) -> interp_bsorts arg_ks t1 -> interp_bsorts arg_ks t2 -> interp_bsorts arg_ks t with
    | [] =>
      fun t1 t2 t f x1 x2 => f x1 x2
    | arg_k :: arg_ks =>
      fun t1 t2 t f x1 x2 => lift2 arg_ks (fun a1 a2 ak => f (a1 ak) (a2 ak)) x1 x2
    end.
  
  Fixpoint lift3 arg_ks : forall t1 t2 t3 t, (t1 -> t2 -> t3 -> t) -> interp_bsorts arg_ks t1 -> interp_bsorts arg_ks t2 -> interp_bsorts arg_ks t3 -> interp_bsorts arg_ks t :=
    match arg_ks return forall t1 t2 t3 t, (t1 -> t2 -> t3 -> t) -> interp_bsorts arg_ks t1 -> interp_bsorts arg_ks t2 -> interp_bsorts arg_ks t3 -> interp_bsorts arg_ks t with
    | [] =>
      fun t1 t2 t3 t f x1 x2 x3 => f x1 x2 x3
    | arg_k :: arg_ks =>
      fun t1 t2 t3 t f x1 x2 x3 => lift3 arg_ks (fun a1 a2 a3 ak => f (a1 ak) (a2 ak) (a3 ak)) x1 x2 x3
    end.

  Fixpoint lift4 arg_ks : forall t1 t2 t3 t4 t, (t1 -> t2 -> t3 -> t4 -> t) -> interp_bsorts arg_ks t1 -> interp_bsorts arg_ks t2 -> interp_bsorts arg_ks t3 -> interp_bsorts arg_ks t4 -> interp_bsorts arg_ks t :=
    match arg_ks return forall t1 t2 t3 t4 t, (t1 -> t2 -> t3 -> t4 -> t) -> interp_bsorts arg_ks t1 -> interp_bsorts arg_ks t2 -> interp_bsorts arg_ks t3 -> interp_bsorts arg_ks t4 -> interp_bsorts arg_ks t with
    | [] =>
      fun t1 t2 t3 t4 t f x1 x2 x3 x4 => f x1 x2 x3 x4
    | arg_k :: arg_ks =>
      fun t1 t2 t3 t4 t f x1 x2 x3 x4 => lift4 arg_ks (fun a1 a2 a3 a4 ak => f (a1 ak) (a2 ak) (a3 ak) (a4 ak)) x1 x2 x3 x4
    end.

  Fixpoint lift5 arg_ks : forall t1 t2 t3 t4 t5 t, (t1 -> t2 -> t3 -> t4 -> t5 -> t) -> interp_bsorts arg_ks t1 -> interp_bsorts arg_ks t2 -> interp_bsorts arg_ks t3 -> interp_bsorts arg_ks t4 -> interp_bsorts arg_ks t5 -> interp_bsorts arg_ks t :=
    match arg_ks return forall t1 t2 t3 t4 t5 t, (t1 -> t2 -> t3 -> t4 -> t5 -> t) -> interp_bsorts arg_ks t1 -> interp_bsorts arg_ks t2 -> interp_bsorts arg_ks t3 -> interp_bsorts arg_ks t4 -> interp_bsorts arg_ks t5 -> interp_bsorts arg_ks t with
    | [] =>
      fun t1 t2 t3 t4 t5 t f x1 x2 x3 x4 x5 => f x1 x2 x3 x4 x5
    | arg_k :: arg_ks =>
      fun t1 t2 t3 t4 t5 t f x1 x2 x3 x4 x5 => lift5 arg_ks (fun a1 a2 a3 a4 a5 ak => f (a1 ak) (a2 ak) (a3 ak) (a4 ak) (a5 ak)) x1 x2 x3 x4 x5
    end.

  Fixpoint lift6 arg_ks : forall t1 t2 t3 t4 t5 t6 t, (t1 -> t2 -> t3 -> t4 -> t5 -> t6 -> t) -> interp_bsorts arg_ks t1 -> interp_bsorts arg_ks t2 -> interp_bsorts arg_ks t3 -> interp_bsorts arg_ks t4 -> interp_bsorts arg_ks t5 -> interp_bsorts arg_ks t6 -> interp_bsorts arg_ks t :=
    match arg_ks return forall t1 t2 t3 t4 t5 t6 t, (t1 -> t2 -> t3 -> t4 -> t5 -> t6 -> t) -> interp_bsorts arg_ks t1 -> interp_bsorts arg_ks t2 -> interp_bsorts arg_ks t3 -> interp_bsorts arg_ks t4 -> interp_bsorts arg_ks t5 -> interp_bsorts arg_ks t6 -> interp_bsorts arg_ks t with
    | [] =>
      fun t1 t2 t3 t4 t5 t6 t f x1 x2 x3 x4 x5 x6 => f x1 x2 x3 x4 x5 x6
    | arg_k :: arg_ks =>
      fun t1 t2 t3 t4 t5 t6 t f x1 x2 x3 x4 x5 x6 => lift6 arg_ks (fun a1 a2 a3 a4 a5 a6 ak => f (a1 ak) (a2 ak) (a3 ak) (a4 ak) (a5 ak) (a6 ak)) x1 x2 x3 x4 x5 x6
    end.

  Lemma fuse_lift1_id ks :
    forall A a,
      lift1 ks (@id A) a = a.
  Proof.
    induct ks; simplify; eauto.
  Qed.
  
  Lemma fuse_lift1_lift0 ks :
    forall A B (f : A -> B) (g : A),
      lift1 ks f (lift0 ks g) = lift0 ks (f g).
  Proof.
    induct ks; simplify; eauto.
    eapply IHks.
  Qed.
  
  Lemma fuse_lift1_lift1 ks :
    forall A B C (f : B -> C) (g : A -> B) a,
      lift1 ks f (lift1 ks g a) = lift1 ks (fun a => f (g a)) a.
  Proof.
    induct ks; simplify; eauto.
    eapply IHks.
  Qed.
  
  Lemma fuse_lift1_lift2 ks :
    forall A B C D (f : C -> D) (g : A -> B -> C) a b,
      lift1 ks f (lift2 ks g a b) = lift2 ks (fun a b => f (g a b)) a b.
  Proof.
    induct ks; simplify; eauto.
    eapply IHks.
  Qed.
  
  Lemma fuse_lift1_lift3 ks :
    forall A B C D E (f : D -> E) (g : A -> B -> C -> D) a b c,
      lift1 ks f (lift3 ks g a b c) = lift3 ks (fun a b c => f (g a b c)) a b c.
  Proof.
    induct ks; simplify; eauto.
    eapply IHks.
  Qed.
  
  Lemma fuse_lift1_lift4 ks :
    forall A B C D E F (f : E -> F) (g : A -> B -> C -> D -> E) a b c d,
      lift1 ks f (lift4 ks g a b c d) = lift4 ks (fun a b c d => f (g a b c d)) a b c d.
  Proof.
    induct ks; simplify; eauto.
    eapply IHks.
  Qed.
  
  Lemma fuse_lift1_lift6 ks :
    forall A B C D E F G H (h : G -> H) (g : A -> B -> C -> D -> E -> F -> G) a b c d e f,
      lift1 ks h (lift6 ks g a b c d e f) = lift6 ks (fun a b c d e f => h (g a b c d e f)) a b c d e f.
  Proof.
    induct ks; simplify; eauto.
    eapply IHks.
  Qed.
  
  Lemma fuse_lift2_lift0_2 ks :
    forall A B C (f : A -> B -> C) (g : B) a,
      lift2 ks f a (lift0 ks g) = lift1 ks (fun a => f a g) a.
  Proof.
    induct ks; simplify; eauto.
    eapply IHks.
  Qed.
  
  Lemma fuse_lift2_lift1_1 ks :
    forall A B C D (f : B -> C -> D) (g : A -> B) a b,
      lift2 ks f (lift1 ks g a) b = lift2 ks (fun a b => f (g a) b) a b.
  Proof.
    induct ks; simplify; eauto.
    eapply IHks.
  Qed.
  
  Lemma fuse_lift2_lift1_2 ks :
    forall A B C D (f : A -> C -> D) (g : B -> C) a b,
      lift2 ks f a (lift1 ks g b) = lift2 ks (fun a b => f a (g b)) a b.
  Proof.
    induct ks; simplify; eauto.
    eapply IHks.
  Qed.
  
  Lemma fuse_lift2_lift2_1 ks :
    forall A B C D E (f : C -> D -> E) (g : A -> B -> C) a b c,
      lift2 ks f (lift2 ks g a b) c = lift3 ks (fun a b c => f (g a b) c) a b c.
  Proof.
    induct ks; simplify; eauto.
    eapply IHks.
  Qed.
  
  Lemma fuse_lift2_lift2_2 ks :
    forall A B C D E (f : A -> D -> E) (g : B -> C -> D) a b c,
      lift2 ks f a (lift2 ks g b c) = lift3 ks (fun a b c => f a (g b c)) a b c.
  Proof.
    induct ks; simplify; eauto.
    eapply IHks.
  Qed.
  
  Lemma fuse_lift2_lift2_1_2 ks :
    forall A B C D E F G (f : E -> F -> G) (g : A -> B -> E) (h : C -> D -> F) a b c d,
      lift2 ks f (lift2 ks g a b) (lift2 ks h c d) = lift4 ks (fun a b c d  => f (g a b) (h c d)) a b c d.
  Proof.
    induct ks; simplify; eauto.
    eapply IHks.
  Qed.
  
  Lemma fuse_lift3_lift2_3 ks :
    forall A B C D E F (f : A -> B -> E -> F) (g : C -> D -> E) a b c d,
      lift3 ks f a b (lift2 ks g c d) = lift4 ks (fun a b c d => f a b (g c d)) a b c d.
  Proof.
    induct ks; simplify; eauto.
    eapply IHks.
  Qed.
  
  Lemma fuse_lift4_lift2_3_4 ks :
    forall A B C D E F G H I (i : A -> B -> G -> H -> I) (g : C -> D -> G) (h : E -> F -> H) a b c d e f,
      lift4 ks i a b (lift2 ks g c d) (lift2 ks h e f) = lift6 ks (fun a b c d e f => i a b (g c d) (h e f)) a b c d e f.
  Proof.
    induct ks; simplify; eauto.
    eapply IHks.
  Qed.
  
  Lemma dedup_lift2 ks :
    forall A B (f : A -> A -> B) a,
      lift2 ks f a a = lift1 ks (fun a => f a a) a.
  Proof.
    induct ks; simplify; eauto.
    eapply IHks.
  Qed.
  
  Lemma dedup_lift3_1_3 ks :
    forall A B C (f : A -> B -> A -> C) a b,
      lift3 ks f a b a = lift2 ks (fun a b => f a b a) a b.
  Proof.
    induct ks; simplify; eauto.
    eapply IHks.
  Qed.
  
  Lemma dedup_lift3_2_3 ks :
    forall A B C (f : A -> B -> B -> C) a b,
      lift3 ks f a b b = lift2 ks (fun a b => f a b b) a b.
  Proof.
    induct ks; simplify; eauto.
    eapply IHks.
  Qed.
  
  Lemma dedup_lift4_1_3 ks :
    forall A B C D (f : A -> B -> A -> C -> D) a b c,
      lift4 ks f a b a c = lift3 ks (fun a b c => f a b a c) a b c.
  Proof.
    induct ks; simplify; eauto.
    eapply IHks.
  Qed.
  
  Lemma dedup_lift4_1_4 ks :
    forall A B C D (f : A -> B -> C -> A -> D) a b c,
      lift4 ks f a b c a = lift3 ks (fun a b c => f a b c a) a b c.
  Proof.
    induct ks; simplify; eauto.
    eapply IHks.
  Qed.
  
  Lemma dedup_lift4_3_4 ks :
    forall A B C D (f : A -> B -> C -> C -> D) a b c,
      lift4 ks f a b c c = lift3 ks (fun a b c => f a b c c) a b c.
  Proof.
    induct ks; simplify; eauto.
    eapply IHks.
  Qed.
  
  Lemma dedup_lift5_2_3 ks :
    forall A B C D E (f : A -> B -> B -> C -> D -> E) a b c d,
      lift5 ks f a b b c d = lift4 ks (fun a b c d => f a b b c d) a b c d.
  Proof.
    induct ks; simplify; eauto.
    eapply IHks.
  Qed.
  
  Lemma dedup_lift6_1_5 ks :
    forall A B C D E F (f : A -> B -> C -> D -> A -> E -> F) a b c d e,
      lift6 ks f a b c d a e = lift5 ks (fun a b c d e => f a b c d a e) a b c d e.
  Proof.
    induct ks; simplify; eauto.
    eapply IHks.
  Qed.
  
  Fixpoint insert A new n (ls : list A) :=
    match n with
    | 0 => new ++ ls
    | S n => 
      match ls with
      | [] => new
      | a :: ls => a :: insert new n ls
      end
    end.

  Definition sort_dec : forall (b b' : bsort), sumbool (b = b') (b <> b').
  Proof.
    induction b; destruct b'; simpl; try solve [left; f_equal; eauto | right; intro Heq; discriminate].
    {
      destruct (arity ==n arity0); subst; simplify; try solve [left; f_equal; eauto | right; intro Heq; invert Heq; subst; eauto].
    }
  Defined.
  
  Definition convert_sort_value k1 k2 : interp_bsort k1 -> interp_bsort k2.
  Proof.
    cases (sort_dec k1 k2); subst; eauto.
    intros.
    eapply sort_default_value.
  Defined.
  
  Fixpoint interp_var (x : var) arg_bs ret_b {struct arg_bs} : interp_bsorts arg_bs (interp_bsort ret_b) :=
    match arg_bs return interp_bsorts arg_bs (interp_bsort ret_b) with
    | [] => sort_default_value ret_b
    | arg_b :: arg_bs =>
      match x with
      | 0 => lift0 arg_bs (convert_sort_value arg_b ret_b)
      | S x => lift1 arg_bs (fun (x : interp_bsort ret_b) (_ : interp_bsort arg_b) => x) (interp_var x arg_bs ret_b)
      end
    end.

(*  
  Section interp_var.

    Variables (k_in : bsort).
    
    Fixpoint interp_var (x : var) arg_ks k_out (k : interp_bsort k_in -> k_out) {struct arg_ks} : interp_bsorts arg_ks k_out :=
    match arg_ks with
    | [] => k (sort_default_value k_in)
    | arg_k :: arg_ks =>
      match x with
      | 0 => lift0 arg_ks (fun x : interp_bsort arg_k => k (convert_sort_value arg_k k_in x))
      | S x => @interp_var x arg_ks (interp_bsort arg_k -> k_out) (fun (x : interp_bsort k_in) (_ : interp_bsort arg_k) => k x)
      end
    end.

  End interp_var.
 *)
  
  Definition interp_iunop opr : interp_bsort (iunop_arg_bsort opr) -> interp_bsort (iunop_result_bsort opr) :=
    match opr with
    | IUBoolNeg => negb
    end.

  Definition interp_ibinop opr : interp_bsort (ibinop_arg1_bsort opr) -> interp_bsort (ibinop_arg2_bsort opr) -> interp_bsort (ibinop_result_bsort opr) :=
    match opr with
    | IBTimeAdd => TimeAdd
    | IBTimeMinus => TimeMinus
    | IBTimeMax => TimeMax
    end.

  Definition ite {A} (x : bool) (x1 x2 : A) := if x then x1 else x2.

  Definition interp_iconst cn arg_ks res_k : interp_bsorts arg_ks (interp_bsort res_k) :=
    match cn with
    | ICTime cn => lift0 arg_ks (convert_sort_value BSTime res_k cn)
    | ICNat cn => lift0 arg_ks (convert_sort_value BSNat res_k cn)
    | ICBool cn => lift0 arg_ks (convert_sort_value BSBool res_k cn)
    | ICTT => lift0 arg_ks (convert_sort_value BSUnit res_k tt)
    end.

  Fixpoint interp_idx c arg_ks res_k : interp_bsorts arg_ks (interp_bsort res_k) :=
    match c with
    (* | IVar x => interp_var res_k x arg_ks id *)
    | IVar x => interp_var x arg_ks res_k
    | IConst cn => interp_iconst cn arg_ks res_k 
    | IUnOp opr c =>
      let f x := convert_sort_value (iunop_result_bsort opr) res_k (interp_iunop opr x) in
      lift1 arg_ks f (interp_idx c arg_ks (iunop_arg_bsort opr))
    | IBinOp opr c1 c2 =>
      let f x1 x2 := convert_sort_value (ibinop_result_bsort opr) res_k (interp_ibinop opr x1 x2) in
      lift2 arg_ks f (interp_idx c1 arg_ks (ibinop_arg1_bsort opr)) (interp_idx c2 arg_ks (ibinop_arg2_bsort opr))
    | IIte c c1 c2 =>
      lift3 arg_ks ite (interp_idx c arg_ks BSBool) (interp_idx c1 arg_ks res_k) (interp_idx c2 arg_ks res_k)
    | ITimeAbs c =>
      match res_k return interp_bsorts arg_ks (interp_bsort res_k) with
      | BSTimeFun (S n) =>
        interp_idx c (BSNat :: arg_ks) (BSTimeFun n)
      | res_k => lift0 arg_ks (sort_default_value res_k)
      end
    | ITimeApp n c1 c2 => 
      let f x1 x2 := convert_sort_value (BSTimeFun n) res_k (x1 x2) in
      lift2 arg_ks f (interp_idx c1 arg_ks (BSTimeFun (S n))) (interp_idx c2 arg_ks BSNat)
  end.

  Definition interp_time i : time_type := interp_idx i [] BSTime.
  
  Lemma interp_time_const a : interp_time (Tconst a) = a.
  Proof.
    cbn in *; eauto.
  Qed.
  
  Lemma interp_time_0 : interp_time T0 = 0%time.
  Proof.
    cbn in *; eauto.
  Qed.

  Lemma interp_time_1 : interp_time T1 = 1%time.
  Proof.
    cbn in *; eauto.
  Qed.

  Lemma interp_time_distr a b : interp_time (a + b)%idx = (interp_time a + interp_time b)%time.
  Proof.
    cbn in *; eauto.
  Qed.
  
  Lemma interp_time_minus_distr a b :
    interp_time (Tminus a b) = (interp_time a - interp_time b)%time.
  Proof.
    cbn in *; eauto.
  Qed.

  Lemma interp_time_max a b : interp_time (Tmax a b) = TimeMax (interp_time a) (interp_time b).
  Proof.
    cbn in *; eauto.
  Qed.

  Notation imply := (fun A B : Prop => A -> B).
  (* Definition imply (A B : Prop) := A -> B. *)
  Definition iff (A B : Prop) := A <-> B.
  Definition for_all {A} (P : A -> Prop) : Prop := forall a, P a.
  
  (* Arguments imply / . *)
  Arguments iff / .
  Arguments for_all / .
  Arguments id / .
  
  Definition interp_binconn opr : Prop -> Prop -> Prop :=
    match opr with
    | PBCAnd => and
    | PBCOr => or
    | PBCImply => imply
    | PBCIff => iff
    end.

  Definition Time_BigO (arity : nat) : time_fun arity -> time_fun arity -> Prop.
  Admitted.

  Definition interp_binpred opr : interp_bsort (binpred_arg1_bsort opr) -> interp_bsort (binpred_arg2_bsort opr) -> Prop :=
    match opr with
    | PBTimeLe => TimeLe
    (* | PBTimeEq => eq *)
    | PBBigO n => Time_BigO n
    end.

  Definition interp_quan {A} q (P : A -> Prop) : Prop :=
    match q with
    | QuanForall => forall a, P a
    | QuanExists => exists a, P a
    end.

  Definition interp_true_false_Prop (b : bool) := if b then True else False.

  Fixpoint interp_p arg_ks p : interp_bsorts arg_ks Prop :=
    match p with
    | PTrueFalse cn => lift0 arg_ks (interp_true_false_Prop cn)
    | PBinConn opr p1 p2 =>
      lift2 arg_ks (interp_binconn opr) (interp_p arg_ks p1) (interp_p arg_ks p2)
    | PNot p =>
      lift1 arg_ks not (interp_p arg_ks p)
    | PBinPred opr c1 c2 =>
      let f x1 x2 := interp_binpred opr x1 x2 in
      lift2 arg_ks f (interp_idx c1 arg_ks (binpred_arg1_bsort opr)) (interp_idx c2 arg_ks (binpred_arg2_bsort opr))
    | PEq b c1 c2 =>
      lift2 arg_ks eq (interp_idx c1 arg_ks b) (interp_idx c2 arg_ks b)
    | PQuan q b p => lift1 arg_ks (interp_quan q) (interp_p (b :: arg_ks) p)
    end.

  Fixpoint forall_ arg_ks : interp_bsorts arg_ks Prop -> Prop :=
    match arg_ks with
    | [] => id
    | arg_k :: arg_ks => fun P => forall_ arg_ks (lift1 arg_ks for_all P)
    end.

  Fixpoint strip_subset k :=
    match k with
    | SBaseSort b => []
    | SSubset b p => [p]
    end.

  Definition get_bsort (s : sort) :=
    match s with
    | SBaseSort b => b
    | SSubset b _ => b
    end.
  
  Fixpoint strip_subsets (ss : list sort) : list prop :=
    match ss with
    | [] => []
    | s :: ss =>
      let ps1 := strip_subset s in
      let ps2 := strip_subsets ss in
      let ps2 := map shift0_i_p ps2 in
      ps1 ++ ps2
    end.

  Fixpoint and_all ps :=
    match ps with
    | [] => PTrue
    | p :: ps => (p /\ and_all ps) % idx
    end.
  
  Definition interp_prop (ss : sctx) (p : prop) : Prop :=
    let bs := map get_bsort ss in
    let ps := strip_subsets ss in
    let p := (and_all ps ===> p)%idx in
    let P := interp_p bs p in
    forall_ bs P.

  Lemma interp_prop_le_interp_time a b :
    interp_prop [] (a <= b)%idx ->
    (interp_time a <= interp_time b)%time.
  Proof.
    unfold interp_prop.
    cbn in *.
    eauto.
  Qed.

  Lemma interp_time_interp_prop_le a b :
    (interp_time a <= interp_time b)%time ->
    interp_prop [] (a <= b)%idx.
  Proof.
    unfold interp_prop.
    cbn in *.
    eauto.
  Qed.

  Lemma interp_prop_eq_interp_time a b :
    interp_prop [] (a == b)%idx -> interp_time a = interp_time b.
  Proof.
    unfold interp_prop.
    cbn in *.
    eauto.
  Qed.

  Lemma interp_time_interp_prop_eq a b :
    interp_time a = interp_time b -> interp_prop [] (a == b)%idx.
  Proof.
    unfold interp_prop.
    cbn in *.
    eauto.
  Qed.

  Lemma forall_lift0 ks : forall (P : Prop), P -> forall_ ks (lift0 ks P).
  Proof.
    induct ks; intros; cbn in *; eauto.
    rewrite fuse_lift1_lift0.
    eauto.
  Qed.
  
  Lemma forall_lift1 ks : forall A (P : A -> Prop), (forall a, P a) -> forall a, forall_ ks (lift1 ks P a).
  Proof.
    induct ks; intros; cbn in *; eauto.
    rewrite fuse_lift1_lift1.
    eauto.
  Qed.
  
  Lemma forall_lift2 ks : forall A B (P : A -> B -> Prop), (forall a b, P a b) -> forall a b, forall_ ks (lift2 ks P a b).
  Proof.
    induct ks; intros; cbn in *; eauto.
    rewrite fuse_lift1_lift2.
    eauto.
  Qed.
  
  Lemma forall_lift3 ks : forall A B C (P : A -> B -> C -> Prop), (forall a b c, P a b c) -> forall a b c, forall_ ks (lift3 ks P a b c).
  Proof.
    induct ks; intros; cbn in *; eauto.
    rewrite fuse_lift1_lift3.
    eauto.
  Qed.

  Lemma forall_ignore_premise' ks :
    forall A B P1 P2 (f : B -> Prop) (g : A -> B -> Prop),
      (forall a b, f b -> g a b) ->
      forall_ ks (lift1 ks f P2) ->
      forall_ ks (lift2 ks g P1 P2).
  Proof.
    induct ks; simplify; eauto.
    rewrite fuse_lift1_lift2.
    rewrite fuse_lift1_lift1 in *.
    eapply IHks; eauto.
    simplify.
    eauto.
  Qed.
  
  Lemma forall_ignore_premise ks :
    forall P1 P2,
      forall_ ks P2 ->
      forall_ ks (lift2 ks imply P1 P2).
  Proof.
    intros.
    eapply forall_ignore_premise' with (f := id); simplify; eauto.
    rewrite fuse_lift1_id.
    eauto.
  Qed.
  
  Lemma forall_use_premise' ks :
    forall A B P1 P2 (f : A -> Prop) (g : A -> B -> Prop) (h : B -> Prop),
      (forall a b, f a -> g a b -> h b) ->
      forall_ ks (lift1 ks f P1) ->
      forall_ ks (lift2 ks g P1 P2) ->
      forall_ ks (lift1 ks h P2).
  Proof.
    induct ks; simplify; eauto.
    rewrite fuse_lift1_lift1 in *.
    rewrite fuse_lift1_lift2 in *.
    eapply IHks; eauto.
    simplify.
    eauto.
  Qed.
  
  Lemma forall_use_premise ks P1 P2 :
    forall_ ks P1 ->
    forall_ ks (lift2 ks imply P1 P2) ->
    forall_ ks P2.
  Proof.
    intros H1 H2.
    eapply forall_use_premise' with (f := id) (h := id) in H2; simplify; 
      try rewrite fuse_lift1_id in *; eauto.
  Qed.
  
  Lemma forall_same_premise' ks :
    forall A B C P1 P2 P3 (f : A -> B -> Prop) (g : A -> B -> C -> Prop) (h : A -> C -> Prop),
      (forall a b c, f a b -> g a b c -> h a c) ->
      forall_ ks (lift2 ks f P1 P2) ->
      forall_ ks (lift3 ks g P1 P2 P3) ->
      forall_ ks (lift2 ks h P1 P3).
  Proof.
    induct ks; simplify; eauto.
    rewrite fuse_lift1_lift2 in *.
    rewrite fuse_lift1_lift3 in *.
    eapply IHks; eauto.
    simplify.
    eauto.
  Qed.
  
  Lemma forall_same_premise ks P1 P2 P2':
    forall_ ks (lift2 ks imply P1 P2) ->
    forall_ ks (lift2 ks imply P1 (lift2 ks imply P2 P2')) ->
    forall_ ks (lift2 ks imply P1 P2').
  Proof.
    intros.
    rewrite fuse_lift2_lift2_2 in *.
    eapply forall_same_premise'; simplify; eauto.
    eauto.
  Qed.
  
  Lemma forall_trans' ks :
    forall A B C P1 P2 P3 (f : A -> B -> Prop) (g : B -> C -> Prop) (h : A -> C -> Prop),
      (forall a b c, f a b -> g b c -> h a c) ->
      forall_ ks (lift2 ks f P1 P2) ->
      forall_ ks (lift2 ks g P2 P3) ->
      forall_ ks (lift2 ks h P1 P3).
  Proof.
    induct ks; simplify; eauto.
    rewrite fuse_lift1_lift2 in *.
    eapply IHks; eauto.
    simplify.
    eauto.
  Qed.
  
  Lemma forall_trans ks P1 P2 P3:
    forall_ ks (lift2 ks imply P1 P2) ->
    forall_ ks (lift2 ks imply P2 P3) ->
    forall_ ks (lift2 ks imply P1 P3).
  Proof.
    intros.
    eapply forall_trans'; simplify; eauto.
    eauto.
  Qed.
  
  Lemma forall_same_premise_2' ks :
    forall A B C D P1 P2 P3 P4 (f : A -> B -> Prop) (g : A -> C -> Prop) (h : A -> B -> C -> D -> Prop) (i : A -> D -> Prop),
      (forall a b c d, f a b -> g a c -> h a b c d -> i a d) ->
      forall_ ks (lift2 ks f P1 P2) ->
      forall_ ks (lift2 ks g P1 P3) ->
      forall_ ks (lift4 ks h P1 P2 P3 P4) ->
      forall_ ks (lift2 ks i P1 P4).
  Proof.
    induct ks; simplify; eauto.
    rewrite fuse_lift1_lift2 in *.
    rewrite fuse_lift1_lift4 in *.
    eapply IHks; [ .. | eapply H2]; eauto.
    simplify.
    eauto.
  Qed.
  
  Lemma forall_same_premise_2 ks P1 P2 P2' P2'' :
    forall_ ks (lift2 ks imply P1 P2) ->
    forall_ ks (lift2 ks imply P1 P2') ->
    forall_ ks (lift2 ks imply P1 (lift2 ks imply P2 (lift2 ks imply P2' P2''))) ->
    forall_ ks (lift2 ks imply P1 P2'').
  Proof.
    intros.
    rewrite fuse_lift2_lift2_2 in *.
    rewrite fuse_lift3_lift2_3 in *.
    eapply forall_same_premise_2'; [ .. | eapply H1]; simplify; eauto.
    eauto.
  Qed.
  
  Lemma Time_add_0 i : (i + 0)%time = i.
  Proof.
    etransitivity.
    {
      eapply Time_add_comm.
    }
    eapply Time_0_add.
  Qed.
  
  Lemma interp_prop_eq_refl L : forall i, interp_prop L (i == i)%idx.
  Proof.
    unfold interp_prop.
    cbn in *.
    intros i.
    eapply forall_ignore_premise.
    rewrite dedup_lift2.
    eapply forall_lift1.
    eauto.
  Qed.
  
  Lemma interp_prop_eq_sym L i i' :
    interp_prop L (i == i')%idx ->
    interp_prop L (i' == i)%idx.
  Proof.
    unfold interp_prop.
    intros H.
    cbn in *.
    eapply forall_same_premise; eauto.
    eapply forall_ignore_premise.
    rewrite fuse_lift2_lift2_1_2.
    simplify.
    rewrite dedup_lift4_1_4.
    rewrite dedup_lift3_2_3.
    eapply forall_lift2.
    eauto.
  Qed.

  Lemma interp_prop_eq_trans L a b c :
    interp_prop L (a == b)%idx ->
    interp_prop L (b == c)%idx ->
    interp_prop L (a == c)%idx.
  Proof.
    unfold interp_prop.
    intros Hab Hbc.
    cbn in *.
    eapply forall_same_premise_2; [eapply Hab | eapply Hbc |].
    eapply forall_ignore_premise.
    rewrite fuse_lift2_lift2_1_2.
    rewrite fuse_lift4_lift2_3_4.
    simplify.
    rewrite dedup_lift6_1_5.
    rewrite dedup_lift5_2_3.
    rewrite dedup_lift4_3_4.
    eapply forall_lift3.
    intros.
    equality.
  Qed.
  
  Lemma interp_prop_le_refl L : forall i, interp_prop L (i <= i)%idx.
  Proof.
    unfold interp_prop.
    cbn in *.
    intros i.
    eapply forall_ignore_premise.
    rewrite dedup_lift2.
    eapply forall_lift1.
    intros.
    eapply Time_le_refl.
  Qed.

  Lemma interp_prop_le_trans L a b c :
    interp_prop L (a <= b)%idx ->
    interp_prop L (b <= c)%idx ->
    interp_prop L (a <= c)%idx.
  Proof.
    unfold interp_prop.
    intros Hab Hbc.
    cbn in *.
    eapply forall_same_premise_2; [eapply Hab | eapply Hbc |].
    eapply forall_ignore_premise.
    rewrite fuse_lift2_lift2_1_2.
    rewrite fuse_lift4_lift2_3_4.
    simplify.
    rewrite dedup_lift6_1_5.
    rewrite dedup_lift5_2_3.
    rewrite dedup_lift4_3_4.
    eapply forall_lift3.
    intros.
    eapply Time_le_trans; eauto.
  Qed.

  Lemma interp_prop_iff_refl L p : interp_prop L (p <===> p)%idx.
  Proof.
    unfold interp_prop.
    cbn in *.
    eapply forall_ignore_premise.
    rewrite dedup_lift2.
    eapply forall_lift1.
    intros.
    propositional.
  Qed.

  Lemma interp_prop_iff_sym L p p' :
    interp_prop L (p <===> p')%idx ->
    interp_prop L (p' <===> p)%idx.
  Proof.
    unfold interp_prop.
    intros H.
    cbn in *.
    eapply forall_same_premise; eauto.
    eapply forall_ignore_premise.
    rewrite fuse_lift2_lift2_1_2.
    simplify.
    rewrite dedup_lift4_1_4.
    rewrite dedup_lift3_2_3.
    eapply forall_lift2.
    propositional.
  Qed.
  
  Lemma interp_prop_iff_trans L a b c :
    interp_prop L (a <===> b)%idx ->
    interp_prop L (b <===> c)%idx ->
    interp_prop L (a <===> c)%idx.
  Proof.
    unfold interp_prop.
    intros Hab Hbc.
    cbn in *.
    eapply forall_same_premise_2; [eapply Hab | eapply Hbc |].
    eapply forall_ignore_premise.
    rewrite fuse_lift2_lift2_1_2.
    rewrite fuse_lift4_lift2_3_4.
    simplify.
    rewrite dedup_lift6_1_5.
    rewrite dedup_lift5_2_3.
    rewrite dedup_lift4_3_4.
    eapply forall_lift3.
    intros.
    propositional.
  Qed.

  Lemma interp_prop_eq_interp_prop_le L a b :
    interp_prop L (a == b)%idx ->
    interp_prop L (a <= b)%idx.
  Proof.
    unfold interp_prop.
    intros H.
    cbn in *.
    eapply forall_same_premise; eauto.
    eapply forall_ignore_premise.
    rewrite fuse_lift2_lift2_1_2.
    simplify.
    rewrite dedup_lift4_1_3.
    rewrite dedup_lift3_2_3.
    eapply forall_lift2.
    intros; subst.
    eapply Time_le_refl.
  Qed.
  
  Lemma interp_prop_eq_add_0 L a : interp_prop L (a + T0 == a)%idx.
  Proof.
    unfold interp_prop.
    cbn in *.
    eapply forall_ignore_premise.
    rewrite fuse_lift2_lift2_1.
    rewrite dedup_lift3_1_3.
    rewrite fuse_lift2_lift0_2.
    eapply forall_lift1.
    simplify.
    eapply Time_add_0.
  Qed.
  
  Notation for_all_ A := (fun P : A -> Prop => forall a : A, P a).

  Require Import Datatypes.

  Lemma interp_bsorts_app :
    forall new old t,
      interp_bsorts (new ++ old) t = interp_bsorts old (interp_bsorts new t).
  Proof.
    induct new; simpl; eauto.
  Qed.

  (* Conceptually: *)
  (*
  Definition shift0 new ks t (x : interp_bsorts ks t) : interp_bsorts (new ++ ks) t :=
    lift1 ks (fun x => lift0 new x) x.
   *)
  
  Fixpoint shift0 new ks t : interp_bsorts ks t -> interp_bsorts (new ++ ks) t :=
    match new return interp_bsorts ks t -> interp_bsorts (new ++ ks) t with
    | [] => id
    | new_k :: new' =>
      fun x => shift0 new' ks _ (lift1 ks (fun a _ => a) x)
    end.
  
  Fixpoint shift new n ks t : interp_bsorts ks t -> interp_bsorts (insert new n ks) t :=
    match n return interp_bsorts ks t -> interp_bsorts (insert new n ks) t with
    | 0 => shift0 new ks t
    | S n' => 
        match ks return interp_bsorts ks t -> interp_bsorts (insert new (S n') ks) t with
        | [] => @lift0 new t
        | k :: ks' =>
          fun x => shift new n' ks' _ x
        end
    end.

  Arguments shift0 new ks [t] x .
  Arguments shift new n ks [t] x .
  
  Lemma lift0_shift0 new : forall ks A (f : A), lift0 (new ++ ks) f = shift0 new ks (lift0 ks f).
  Proof.
    induct new; cbn in *; try rename a into a'; intros; eauto.
    rewrite IHnew.
    rewrite !fuse_lift1_lift0.
    eauto.
  Qed.
  
  Lemma lift0_shift x : forall ks new A (f : A), lift0 (insert new x ks) f = shift new x ks (lift0 ks f).
  Proof.
    induct x; cbn in *; intros.
    {
      rewrite lift0_shift0.
      eauto.
    }
    destruct ks; cbn in *; intros.
    {
      eauto.
    }
    {
      eauto.
    }
  Qed.

  Lemma lift1_shift0 new : forall ks A B (f : A -> B) a, lift1 (new ++ ks) f (shift0 new ks a) = shift0 new ks (lift1 ks f a).
  Proof.
    induct new; cbn in *; try rename a into a'; intros ks A B f a; eauto.
    rewrite IHnew.
    rewrite !fuse_lift1_lift1.
    eauto.
  Qed.
  
  Lemma lift1_shift x : forall ks new A B (f : A -> B) a, lift1 (insert new x ks) f (shift new x ks a) = shift new x ks (lift1 ks f a).
  Proof.
    induct x; cbn in *.
    {
      intros ks new A B f a.
      rewrite lift1_shift0.
      eauto.
    }
    destruct ks; cbn in *; intros new A B f a.
    {
      rewrite fuse_lift1_lift0.
      eauto.
    }
    {
      eauto.
    }
  Qed.
  
  Lemma lift2_shift0 new : forall ks A B C (f : A -> B -> C) a b, lift2 (new ++ ks) f (shift0 new ks a) (shift0 new ks b) = shift0 new ks (lift2 ks f a b).
  Proof.
    induct new; cbn in *; try rename a into a'; intros ks A B C f a b; eauto.
    rewrite IHnew.
    rewrite !fuse_lift1_lift2.
    rewrite !fuse_lift2_lift1_1.
    rewrite !fuse_lift2_lift1_2.
    eauto.
  Qed.
  
  Lemma lift2_shift x : forall ks new A B C (f : A -> B -> C) a b, lift2 (insert new x ks) f (shift new x ks a) (shift new x ks b) = shift new x ks (lift2 ks f a b).
  Proof.
    induct x; cbn in *.
    {
      intros ks new A B C f a b.
      rewrite lift2_shift0.
      eauto.
    }
    destruct ks; cbn in *; try rename b into bs; intros new A B C f a b; try la.
    {
      rewrite fuse_lift2_lift0_2.
      rewrite fuse_lift1_lift0.
      eauto.
    }
    {
      eauto.
    }
  Qed.
  
  Lemma forall_shift0 new :
    forall ks p,
      forall_ ks p ->
      forall_ (new ++ ks) (shift0 new ks p).
  Proof.
    induct new; cbn in *; intros ks p H; eauto.
    rewrite lift1_shift0.
    rewrite fuse_lift1_lift1.
    eapply IHnew.
    eapply forall_use_premise; eauto.
    rewrite fuse_lift2_lift1_2.
    rewrite dedup_lift2.
    eapply forall_lift1; eauto.
  Qed.
  
  Lemma forall_shift x :
    forall ks new p,
      forall_ ks p ->
      forall_ (insert new x ks) (shift new x ks p).
  Proof.
    induct x; cbn in *.
    {
      intros ks new p H.
      eapply forall_shift0; eauto.
    }
    destruct ks; cbn in *; intros new p H.
    {
      eapply forall_lift0; eauto.
    }
    {
      rewrite lift1_shift.
      eauto.
    }
  Qed.
    
  Lemma forall_lift2_imply_shift ks x :
    forall new p1 p2 p1' p2',
      let ks' := insert new x ks in
      forall_ ks' (lift2 ks' imply p1' (shift new x ks p1)) ->
      forall_ ks' (lift2 ks' imply (shift new x ks p2) p2') ->
      forall_ ks (lift2 ks imply p1 p2) ->
      forall_ ks' (lift2 ks' imply p1' p2').
  Proof.
    cbn in *; intros new p1 p2 p1' p2' Ha Hb H.
    eapply forall_trans; eauto.
    eapply forall_trans; eauto.
    rewrite lift2_shift.
    eapply forall_shift; eauto.
  Qed.

  Lemma fuse_lift2_lift0_1 ks :
    forall A B C (f : A -> B -> C) (g : A) b,
      lift2 ks f (lift0 ks g) b = lift1 ks (fun b => f g b) b.
  Proof.
    induct ks; simplify; eauto.
    eapply IHks.
  Qed.
  
  Lemma forall_lift2_lift2 :
    forall bs A B P1 P2 (f : A -> B -> Prop) (g : A -> B -> Prop),
      (forall a b, f a b -> g a b) ->
      forall_ bs (lift2 bs f P1 P2) ->
      forall_ bs (lift2 bs g P1 P2).
  Proof.
    induct bs; simplify; eauto.
    rewrite fuse_lift1_lift2 in *.
    eapply IHbs; eauto.
    simplify.
    eauto.
  Qed.
  
  Lemma forall_lift2_lift2_lift4 :
    forall bs A B C D P1 P2 P3 P4 (f : A -> B -> Prop) (g : C -> D -> Prop) (h : A -> C -> B -> D -> Prop),
      (forall a b c d, f a b -> g c d -> h a c b d) ->
      forall_ bs (lift2 bs f P1 P2) ->
      forall_ bs (lift2 bs g P3 P4) ->
      forall_ bs (lift4 bs h P1 P3 P2 P4).
  Proof.
    induct bs; simplify; eauto.
    rewrite fuse_lift1_lift2 in *.
    rewrite fuse_lift1_lift4 in *.
    eapply IHbs; eauto.
    simplify.
    eauto.
  Qed.
  
  Lemma insert_to_nil A (new : list A) : forall x, insert new x [] = new.
  Proof.
    induct x; simpl; eauto.
    rewrite app_nil_r; eauto.
  Qed.
  
  Lemma fuse_lift2_lift3_1 bs :
    forall T A1 A2 B1 B2 B3 (f : A1 -> A2 -> T) (g : B1 -> B2 -> B3 -> A1) b1 b2 b3 a2,
      lift2 bs f (lift3 bs g b1 b2 b3) a2 = lift4 bs (fun b1 b2 b3 a2 => f (g b1 b2 b3) a2) b1 b2 b3 a2.
  Proof.
    induct bs; simplify; eauto.
    eapply IHbs.
  Qed.
  
  Lemma fuse_lift3_lift1_1 bs :
    forall T A1 A2 A3 B (f : A1 -> A2 -> A3 -> T) (g : B -> A1) b a2 a3,
      lift3 bs f (lift1 bs g b) a2 a3 = lift3 bs (fun b a2 a3 => f (g b) a2 a3) b a2 a3.
  Proof.
    induct bs; simplify; eauto.
    eapply IHbs.
  Qed.
  
  Lemma fuse_lift3_lift1_2 bs :
    forall T A1 A2 A3 B (f : A1 -> A2 -> A3 -> T) (g : B -> A2) a1 b a3,
      lift3 bs f a1 (lift1 bs g b) a3 = lift3 bs (fun a1 b a3 => f a1 (g b) a3) a1 b a3.
  Proof.
    induct bs; simplify; eauto.
    eapply IHbs.
  Qed.
  
  Lemma fuse_lift3_lift1_3 bs :
    forall T A1 A2 A3 B (f : A1 -> A2 -> A3 -> T) (g : B -> A3) a1 a2 b,
      lift3 bs f a1 a2 (lift1 bs g b) = lift3 bs (fun a1 a2 b => f a1 a2 (g b)) a1 a2 b.
  Proof.
    induct bs; simplify; eauto.
    eapply IHbs.
  Qed.
  
  Lemma lift3_shift0 new : forall ks A B C D (f : A -> B -> C -> D) a b c, lift3 (new ++ ks) f (shift0 new ks a) (shift0 new ks b) (shift0 new ks c) = shift0 new ks (lift3 ks f a b c).
  Proof.
    induct new; cbn in *; try rename a into a'; intros ks A B C D f a b c; eauto.
    rewrite IHnew.
    rewrite !fuse_lift1_lift3.
    rewrite !fuse_lift3_lift1_1.
    rewrite !fuse_lift3_lift1_2.
    rewrite !fuse_lift3_lift1_3.
    eauto.
  Qed.
  
  Lemma fuse_lift3_lift0_1 bs :
    forall T A1 A2 A3 (f : A1 -> A2 -> A3 -> T) (g : A1) a2 a3,
      lift3 bs f (lift0 bs g) a2 a3 = lift2 bs (fun a2 a3 => f g a2 a3) a2 a3.
  Proof.
    induct bs; simplify; eauto.
    eapply IHbs.
  Qed.
  
  Lemma lift3_shift x : forall ks new A B C D (f : A -> B -> C -> D) a b c, lift3 (insert new x ks) f (shift new x ks a) (shift new x ks b) (shift new x ks c) = shift new x ks (lift3 ks f a b c).
  Proof.
    induct x; cbn in *.
    {
      intros ks new A B C D f a b c.
      rewrite lift3_shift0.
      eauto.
    }
    destruct ks; cbn in *; try rename b into bs; intros new A B C D f a b c; try la.
    {
      rewrite fuse_lift3_lift0_1.
      rewrite fuse_lift2_lift0_2.
      rewrite fuse_lift1_lift0.
      eauto.
    }
    {
      eauto.
    }
  Qed.
  
  Lemma fuse_lift4_lift3_4 bs :
    forall T A1 A2 A3 A4 B1 B2 B3 (f : A1 -> A2 -> A3 -> A4 -> T) (g : B1 -> B2 -> B3 -> A4) a1 a2 a3 b1 b2 b3,
      lift4 bs f a1 a2 a3 (lift3 bs g b1 b2 b3) = lift6 bs (fun a1 a2 a3 b1 b2 b3 => f a1 a2 a3 (g b1 b2 b3)) a1 a2 a3 b1 b2 b3.
  Proof.
    induct bs; simplify; eauto.
    eapply IHbs.
  Qed.
  
  Lemma forall_lift2_lift2_lift2_lift6 :
    forall bs A B C D E F P1 P2 P3 P4 P5 P6 (f1 : A -> D -> Prop) (f2 : B -> E -> Prop) (f3 : C -> F -> Prop) (g : A -> B -> C -> D -> E -> F -> Prop),
      (forall a b c d e f, f1 a d -> f2 b e -> f3 c f -> g a b c d e f) ->
      forall_ bs (lift2 bs f1 P1 P4) ->
      forall_ bs (lift2 bs f2 P2 P5) ->
      forall_ bs (lift2 bs f3 P3 P6) ->
      forall_ bs (lift6 bs g P1 P2 P3 P4 P5 P6).
  Proof.
    induct bs; simplify; eauto.
    rewrite fuse_lift1_lift2 in *.
    rewrite fuse_lift1_lift6 in *.
    eapply IHbs; eauto.
    simplify.
    eauto.
  Qed.
  
  Definition subst0_i_p v b := subst_i_p 0 v b.

  Inductive wellscoped_i : nat -> idx -> Prop :=
  | WsciVar L x :
      x < L ->
      wellscoped_i L (IVar x) 
  | WsciConst L cn :
      wellscoped_i L (IConst cn) 
  | WsciUnOp L opr c :
      wellscoped_i L c ->
      wellscoped_i L (IUnOp opr c) 
  | WsciBinOp L opr c1 c2 :
      wellscoped_i L c1 ->
      wellscoped_i L c2 ->
      wellscoped_i L (IBinOp opr c1 c2) 
  | WsciIte L c c1 c2 :
      wellscoped_i L c ->
      wellscoped_i L c1 ->
      wellscoped_i L c2 ->
      wellscoped_i L (IIte c c1 c2)
  | WsciTimeAbs L i :
      wellscoped_i (1 + L) i ->
      wellscoped_i L (ITimeAbs i) 
  | WsciTimeApp L c1 c2 n :
      wellscoped_i L c1 ->
      wellscoped_i L c2 ->
      wellscoped_i L (ITimeApp n c1 c2) 
  .

  Hint Constructors wellscoped_i.

  Inductive wellscoped_p : nat -> prop -> Prop :=
  | WscpTrueFalse L cn :
      wellscoped_p L (PTrueFalse cn)
  | WscpBinConn L opr p1 p2 :
      wellscoped_p L p1 ->
      wellscoped_p L p2 ->
      wellscoped_p L (PBinConn opr p1 p2)
  | WscpNot L p :
      wellscoped_p L p ->
      wellscoped_p L (PNot p)
  | WscpBinPred L opr i1 i2 :
      wellscoped_i L i1 ->
      wellscoped_i L i2 ->
      wellscoped_p L (PBinPred opr i1 i2)
  | WscpEq L b i1 i2 :
      wellscoped_i L i1 ->
      wellscoped_i L i2 ->
      wellscoped_p L (PEq b i1 i2)
  | WscpQuan L q s p :
      wellscoped_p (1 + L) p ->
      wellscoped_p L (PQuan q s p)
  .
  
  Hint Constructors wellscoped_p.

  Lemma forall_interp_var_eq_shift_gt bs_new :
    forall bs x y b (f : interp_bsort b -> interp_bsort b -> Prop),
      y < x ->
      y < length bs ->
      (forall x, f x x) ->
      forall_
        (insert bs_new x bs)
        (lift2
           (insert bs_new x bs) f
           (interp_var y (insert bs_new x bs) b)
           (shift bs_new x bs (interp_var y bs b))).
  Proof.
    induct bs; simpl; intros x y b f Hcmp Hy Hf; try la.
    destruct x; simpl; try la.
    rewrite fuse_lift1_lift2.
    destruct y as [|y]; simpl in *.
    {
      rewrite fuse_lift2_lift0_1.
      rewrite <- lift0_shift.
      rewrite fuse_lift1_lift0.
      eapply forall_lift0.
      intros; eauto.
    }
    {
      rewrite fuse_lift2_lift1_1.
      rewrite <- lift1_shift.
      rewrite fuse_lift2_lift1_2.
      eauto with db_la.
    }
  Qed.
  
  Lemma forall_interp_var_eq_shift0_le :
    forall bs_new y b (f : interp_bsort b -> interp_bsort b -> Prop) bs,
      y < length bs ->
      (forall x, f x x) ->
      let bs' := bs_new ++ bs in
      forall_
        bs'
        (lift2 bs' f
               (interp_var (length bs_new + y) bs' b)
               (shift0 bs_new bs (interp_var y bs b))).
  Proof.
    simpl.
    induct bs_new; simpl; intros y b f bs Hy Hf.
    {
      rewrite dedup_lift2.
      eapply forall_lift1.
      eauto.
    }
    {
      rewrite fuse_lift1_lift2.
      rewrite <- lift1_shift0.
      rewrite fuse_lift2_lift1_1.
      rewrite fuse_lift2_lift1_2.
      eauto with db_la.
    }
  Qed.
  
  Lemma interp_var_select' :
    forall bs_new a bs b T (f : interp_bsort b -> T -> Prop) (convert : interp_bsort a -> T),
      (forall x, f (convert_sort_value a b x) (convert x)) ->
      (* (forall x, f x x) -> *)
      let bs' := bs_new ++ a :: bs in
      forall_
        bs'
        (lift2 bs' f (interp_var (length bs_new) bs' b)
               (shift0 bs_new (a :: bs) (lift0 bs convert))).
  Proof.
    induct bs_new; simpl; intros tgt_b bs b T f convert Hf.
    {
      rewrite fuse_lift1_lift2.
      rewrite fuse_lift2_lift0_1.
      rewrite fuse_lift1_lift0.
      eapply forall_lift0.
      eauto.
    }
    {
      rename a into b_new.
      rewrite fuse_lift1_lift2.
      rewrite fuse_lift1_lift0.
      rewrite fuse_lift2_lift1_1.
      eapply IHbs_new.
      eauto.
    }
  Qed.

  Lemma interp_var_select :
    forall bs_new a bs b (f : interp_bsort b -> interp_bsort b -> Prop),
      (forall x, f x x) ->
      let bs' := bs_new ++ a :: bs in
      forall_
        bs'
        (lift2 bs' f (interp_var (length bs_new) bs' b)
               (shift0 bs_new (a :: bs) (lift0 bs (convert_sort_value a b)))).
  Proof.
    intros; eapply interp_var_select'; eauto.
  Qed.

  Lemma forall_interp_var_eq_shift_le :
    forall bs x y b (f : interp_bsort b -> interp_bsort b -> Prop) bs_new,
      x <= y ->
      y < length bs ->
      (forall x, f x x) ->
      forall_
        (insert bs_new x bs)
        (lift2
           (insert bs_new x bs) f
           (interp_var (length bs_new + y) (insert bs_new x bs) b)
           (shift bs_new x bs (interp_var y bs b))).
  Proof.
    induct bs; simpl; intros x y b f bs_new Hcmp Hy Hf; try la.
    destruct y as [|y]; simpl in *; eauto with db_la.
    {
      destruct x; simpl; try la.
      rewrite Nat.add_0_r.
      eapply interp_var_select; eauto.
    }
    {
      destruct x; simpl; try la.
      {
        eapply forall_interp_var_eq_shift0_le; eauto with db_la.
      }
      {
        rewrite Nat.add_succ_r.
        rewrite fuse_lift1_lift2.
        rewrite fuse_lift2_lift1_1.
        rewrite <- lift1_shift.
        rewrite fuse_lift2_lift1_2.
        eauto with db_la.
      }
    }
  Qed.
  
  Lemma forall_shift_i_i_iff_shift :
    forall i bs_new x bs b n,
      let bs' := insert bs_new x bs in
      wellscoped_i (length bs) i ->
      n = length bs_new ->
      forall_ bs' (lift2 bs' eq (interp_idx (shift_i_i n x i) bs' b) (shift bs_new x bs (interp_idx i bs b))).
  Proof.
    simpl.
    induct i; try rename x into y; intros bs_new x bs b n Hsc ?; subst; invert Hsc.
    {
      simpl.
      cases (x <=? y); simpl in *.
      {
        eapply forall_interp_var_eq_shift_le; eauto.
      }
      {
        eapply forall_interp_var_eq_shift_gt; eauto.
      }
    }
    {
      simpl.
      cases cn; simpl in *;
      rewrite <- lift0_shift;
      rewrite fuse_lift2_lift0_1;
      rewrite fuse_lift1_lift0;
      eapply forall_lift0; eauto.
    }
    {
      simpl.
      rewrite fuse_lift2_lift1_1.
      rewrite <- lift1_shift.
      rewrite fuse_lift2_lift1_2.
      eapply forall_lift2_lift2; eauto.
      simpl; intros; subst.
      propositional.
    }
    {
      simpl.
      rewrite fuse_lift2_lift2_1.
      rewrite <- lift2_shift.
      rewrite fuse_lift3_lift2_3.
      eapply forall_lift2_lift2_lift4; eauto.
      simpl; intros; subst.
      destruct opr; simpl; propositional.
    }
    {
      simpl.
      rewrite <- lift3_shift.
      rewrite fuse_lift2_lift3_1.
      rewrite fuse_lift4_lift3_4.
      specialize (IHi1 bs_new x bs BSBool (length bs_new)).
      eapply forall_lift2_lift2_lift2_lift6; eauto.
      simpl; intros; subst.
      unfold ite; simpl; propositional.
    }
    {
      simpl.
      cases b; try cases arity;
        try solve [
              rewrite <- lift0_shift;
              rewrite fuse_lift2_lift0_1;
              rewrite fuse_lift1_lift0;
              eapply forall_lift0; eauto
            ].
      specialize (IHi bs_new (S x) (BSNat :: bs) (BSTimeFun arity) (length bs_new)).
      simpl in *.
      rewrite fuse_lift1_lift2 in *.
      eapply forall_lift2_lift2; [ | eapply IHi; eauto].
      simpl; intros.
      Require FunctionalExtensionality.
      eapply FunctionalExtensionality.functional_extensionality.
      eauto.
    }
    {
      simpl.
      rewrite fuse_lift2_lift2_1.
      rewrite <- lift2_shift.
      rewrite fuse_lift3_lift2_3.
      specialize (IHi1 bs_new x bs (BSTimeFun (S arity)) (length bs_new)).
      specialize (IHi2 bs_new x bs BSNat (length bs_new)).
      eapply forall_lift2_lift2_lift4; eauto.
      simpl; intros; subst.
      simpl; propositional.
    }
  Qed.

  Lemma forall_shift_i_p_iff_shift :
    forall p bs_new x bs n,
      let bs' := insert bs_new x bs in
      wellscoped_p (length bs) p ->
      n = length bs_new ->
      forall_ bs' (lift2 bs' iff (interp_p bs' (shift_i_p n x p)) (shift bs_new x bs (interp_p bs p))).
  Proof.
    simpl.
    induct p; simpl; intros bs_new x bs n Hsc ?; subst; invert Hsc.
    {
      rewrite fuse_lift2_lift0_1.
      rewrite <- lift0_shift.
      rewrite fuse_lift1_lift0.
      eapply forall_lift0.
      propositional.
    }
    {
      rewrite fuse_lift2_lift2_1.
      rewrite <- lift2_shift.
      rewrite fuse_lift3_lift2_3.
      eapply forall_lift2_lift2_lift4; eauto.
      simpl; intros.
      destruct opr; simpl; propositional.
    }
    {
      rewrite fuse_lift2_lift1_1.
      rewrite <- lift1_shift.
      rewrite fuse_lift2_lift1_2.
      eapply forall_lift2_lift2; eauto.
      simpl; intros.
      propositional.
    }
    {
      rewrite fuse_lift2_lift2_1.
      rewrite <- lift2_shift.
      rewrite fuse_lift3_lift2_3.
      eapply forall_lift2_lift2_lift4; try eapply forall_shift_i_i_iff_shift; eauto.
      intros; subst.
      propositional.
    }
    {
      rewrite fuse_lift2_lift2_1.
      rewrite <- lift2_shift.
      rewrite fuse_lift3_lift2_3.
      eapply forall_lift2_lift2_lift4; try eapply forall_shift_i_i_iff_shift; eauto.
      intros; subst.
      propositional.
    }
    {
      rename b into bsort.
      rewrite fuse_lift2_lift1_1.
      rewrite <- lift1_shift.
      rewrite fuse_lift2_lift1_2.
      cbn.
      specialize (IHp bs_new (S x) (bsort :: bs) (length bs_new)); simpl in *.
      rewrite fuse_lift1_lift2 in *.
      eapply forall_lift2_lift2; eauto.
      simpl; intros.
      destruct q; simpl; intuition eauto.
      {
        eapply H; eauto.
      }
      {
        eapply H; eauto.
      }
      {
        openhyp; eexists.
        eapply H; eauto.
      }
      {
        openhyp; eexists.
        eapply H; eauto.
      }
    }
  Qed.
  
  Fixpoint shift_i_ss n bs :=
    match bs with
    | [] => []
    | b :: bs => shift_i_s n (length bs) b :: shift_i_ss n bs
    end.

  Fixpoint subst_i_ss v bs :=
    match bs with
    | [] => []
    | b :: bs => subst_i_s (length bs) (shift_i_i (length bs) 0 v) b :: subst_i_ss v bs
    end.

  Lemma length_shift_i_ss bs :
    forall v,
      length (shift_i_ss v bs) = length bs.
  Proof.
    induction bs; simplify; eauto.
  Qed.
  
  Lemma length_subst_i_ss bs :
    forall v,
      length (subst_i_ss v bs) = length bs.
  Proof.
    induction bs; simplify; eauto.
  Qed.
  
  Lemma nth_error_shift_i_ss bs :
    forall x b m,
      nth_error bs x = Some b ->
      let n := length bs in
      nth_error (shift_i_ss m bs) x = Some (shift_i_s m (n - S x) b).
  Proof.
    induction bs; simplify.
    {
      rewrite nth_error_nil in *; discriminate.
    }
    destruct x; simplify; eauto.
    invert H.
    try unfold value; repeat f_equal; la.
  Qed.
  
  Lemma nth_error_subst_i_ss bs :
    forall x b v,
      nth_error bs x = Some b ->
      let n := length bs in
      nth_error (subst_i_ss v bs) x = Some (subst_i_s (n - S x) (shift_i_i (n - S x) 0 v) b).
  Proof.
    induction bs; simplify.
    {
      rewrite nth_error_nil in *; discriminate.
    }
    destruct x; simplify; eauto.
    invert H.
    try unfold value; repeat f_equal; la.
  Qed.
  
  Lemma forall_iff_imply bs p1 p2 :
    forall_ bs (lift2 bs iff p1 p2) ->
    forall_ bs (lift2 bs imply p1 p2).
  Proof.
    intros H.
    eapply forall_lift2_lift2; eauto.
    unfold iff; intros; propositional.
  Qed.
  
  Lemma forall_shift_i_p_shift bs_new x bs p n :
    let bs' := insert bs_new x bs in
    wellscoped_p (length bs) p ->
    n = length bs_new ->
    forall_ bs' (lift2 bs' imply (interp_p bs' (shift_i_p n x p)) (shift bs_new x bs (interp_p bs p))).
  Proof.
    intros.
    eapply forall_iff_imply.
    eapply forall_shift_i_p_iff_shift; eauto.
  Qed.

  Definition swap {A B C} (f : A -> B -> C) b a := f a b.
  
  Lemma swap_lift2 bs :
    forall T A1 A2 (f : A1 -> A2 -> T) a1 a2,
      lift2 bs f a1 a2 = lift2 bs (swap f) a2 a1.
  Proof.
    induct bs; simplify; eauto.
  Qed.
  
  Lemma forall_iff_sym bs p1 p2 :
    forall_ bs (lift2 bs iff p1 p2) ->
    forall_ bs (lift2 bs iff p2 p1).
  Proof.
    intros H.
    rewrite swap_lift2.
    eapply forall_lift2_lift2; [ | eapply H; eauto].
    unfold swap, iff; intros; propositional.
  Qed.
  
  Lemma forall_shift_shift_i_p bs_new x bs p n :
    let bs' := insert bs_new x bs in
    wellscoped_p (length bs) p ->
    n = length bs_new ->
    forall_ bs' (lift2 bs' imply (shift bs_new x bs (interp_p bs p)) (interp_p bs' (shift_i_p n x p))).
  Proof.
    intros.
    eapply forall_iff_imply.
    eapply forall_iff_sym.
    eapply forall_shift_i_p_iff_shift; eauto.
  Qed.

  Lemma get_bsort_shift_i_s :
    forall s n x,
      get_bsort (shift_i_s n x s) = get_bsort s.
  Proof.
    induct s; cbn; eauto; intros; f_equal; eauto.
  Qed.

  Lemma map_insert A B (f : A -> B) new: forall x ls, map f (insert new x ls) = insert (map f new) x (map f ls).
  Proof.
    induct x; simpl; intros.
    {
      rewrite map_app; eauto.
    }
    destruct ls; simpl; f_equal; eauto.
  Qed.
    
  Lemma map_shift_i_ss n : forall L, map get_bsort (shift_i_ss n L) = map get_bsort L.
  Proof.
    induct L; simpl; f_equal; auto.
    rewrite get_bsort_shift_i_s; eauto.
  Qed.

  Lemma insert_firstn_my_skipn A (new : list A) :
    forall x ls,
      insert new x ls = firstn x ls ++ new ++ my_skipn ls x.
  Proof.
    induct x; simpl; intros.
    {
      rewrite my_skipn_0; eauto.
    }
    destruct ls; simpl; f_equal; eauto.
    rewrite app_nil_r; eauto.
  Qed.

  Lemma get_bsort_insert_shift ls :
    forall L x,
      let L' := shift_i_ss (length ls) (firstn x L) ++ ls ++ my_skipn L x in
      map get_bsort L' = insert (map get_bsort ls) x (map get_bsort L).
  Proof.
    simpl.
    intros.
    repeat rewrite map_app.
    rewrite map_shift_i_ss.
    rewrite insert_firstn_my_skipn.
    rewrite map_firstn.
    rewrite map_my_skipn.
    eauto.
  Qed.
  
  Lemma map_id A (ls : list A) : map id ls = ls.
  Proof.
    induct ls; simpl; intros; f_equal; eauto.
  Qed.
  
  Lemma map_shift_i_p_0 x b : map (shift_i_p 0 x) b = b.
  Proof.
    induct b; simpl; f_equal; eauto using shift_i_p_0.
  Qed.

  Lemma strip_subsets_app :
    forall ls1 ls2,
      strip_subsets (ls1 ++ ls2) = strip_subsets ls1 ++ map (shift_i_p (length ls1) 0) (strip_subsets ls2).
  Proof.
    induct ls1; simpl; intros.
    {
      rewrite map_shift_i_p_0; eauto.
    }
    {
      rewrite <- app_assoc.
      f_equal.
      rewrite IHls1.
      rewrite map_app.
      f_equal.
      rewrite map_map.
      eapply map_ext.
      intros b.
      unfold shift0_i_p.
      rewrite shift_i_p_shift_merge by la.
      rewrite plus_comm.
      eauto.
    }
  Qed.
  
  Lemma strip_subsets_insert ls :
    forall L x,
      x <= length L ->
      let n := length ls in
      let L' := shift_i_ss (length ls) (firstn x L) ++ ls ++ my_skipn L x in
      strip_subsets L' =
      map (shift_i_p (length ls) x) (strip_subsets (firstn x L)) ++ map (shift_i_p x 0) (strip_subsets ls) ++ map (shift_i_p (x + length ls) 0) (strip_subsets (my_skipn L x)).
  Proof.
    simpl.
    induct L.
    {
      simpl.
      intros x Hx.
      destruct x; simpl; try la.
      repeat rewrite app_nil_r in *; eauto.
      rewrite map_shift_i_p_0; eauto.
    }
    {
      simpl.
      intros x Hx.
      destruct x.
      {
        simpl.
        rewrite map_shift_i_p_0.
        rewrite strip_subsets_app; simpl.
        f_equal.
      }
      {
        simpl.
        rewrite IHL by la.
        repeat rewrite map_app.
        repeat rewrite <- app_assoc.
        repeat rewrite map_map.
        f_equal.
        {
          rewrite length_firstn_le by la.
          destruct a; simpl; eauto.
        }
        f_equal.
        {
          eapply map_ext.
          intros b.
          unfold shift0_i_p.
          symmetry.
          rewrite shift_i_p_shift_cut by la.
          simpl.
          rewrite Nat.sub_0_r.
          eauto.
        }
        f_equal.
        {
          eapply map_ext.
          intros b.
          unfold shift0_i_p.
          rewrite shift_i_p_shift_merge by la.
          rewrite plus_comm.
          eauto.
        }
        {
          eapply map_ext.
          intros b.
          unfold shift0_i_p.
          rewrite shift_i_p_shift_merge by la.
          f_equal.
          la.
        }
      }
    }
  Qed.
  
  Lemma fuse_lift3_lift2_2 bs :
    forall T A1 A2 A3 B1 B2 (f : A1 -> A2 -> A3 -> T) (g : B1 -> B2 -> A2) a1 b1 b2 a3,
      lift3 bs f a1 (lift2 bs g b1 b2) a3 = lift4 bs (fun a1 b1 b2 a3 => f a1 (g b1 b2) a3) a1 b1 b2 a3.
  Proof.
    induct bs; simplify; eauto.
    eapply IHbs.
  Qed.
  
  Lemma fuse_lift3_lift2_1 ks :
    forall A B C D E F (f : E -> C -> D -> F) (g : A -> B -> E) a b c d,
      lift3 ks f (lift2 ks g a b) c d = lift4 ks (fun a b c d => f (g a b) c d) a b c d.
  Proof.
    induct ks; simplify; eauto.
    eapply IHks.
  Qed.
  
  Lemma fuse_lift4_lift2_4 ks :
    forall A B C D E F G (f : A -> B -> C -> F -> G) (g : D -> E -> F) a b c d e,
      lift4 ks f a b c (lift2 ks g d e) = lift5 ks (fun a b c d e => f a b c (g d e)) a b c d e.
  Proof.
    induct ks; simplify; eauto.
    eapply IHks.
  Qed.
  
  Definition iff_ bs x y := forall_ bs (lift2 bs iff x y).
  
  Lemma forall_iff_lift2 f bs p1 p2 p1' p2' :
    (forall a b c d : Prop, iff a b -> iff c d -> iff (f a c) (f b d)) ->
    iff_ bs p1 p1' ->
    iff_ bs p2 p2' ->
    iff_ bs (lift2 bs f p1 p2) (lift2 bs f p1' p2').
  Proof.
    intros Hf H1 H2.
    unfold iff_ in *.
    rewrite fuse_lift2_lift2_1_2.
    eapply forall_lift2_lift2_lift4; eauto.
  Qed.

  Lemma forall_iff_and bs p1 p2 p1' p2' :
    iff_ bs p1 p1' ->
    iff_ bs p2 p2' ->
    iff_ bs (lift2 bs and p1 p2) (lift2 bs and p1' p2').
  Proof.
    intros; eapply forall_iff_lift2; eauto.
    unfold iff; propositional.
  Qed.
  
  Lemma forall_iff_iff_imply bs p1 p2 p1' p2' :
    iff_ bs p1 p1' ->
    iff_ bs p2 p2' ->
    iff_ bs (lift2 bs imply p1 p2) (lift2 bs imply p1' p2').
  Proof.
    intros; eapply forall_iff_lift2; eauto.
    unfold iff; propositional.
  Qed.

  Lemma forall_iff_refl bs p :
    forall_ bs (lift2 bs iff p p).
  Proof.
    rewrite dedup_lift2.
    eapply forall_lift1.
    unfold iff; propositional.
  Qed.

  Lemma forall_iff_trans ks P1 P2 P3:
    forall_ ks (lift2 ks iff P1 P2) ->
    forall_ ks (lift2 ks iff P2 P3) ->
    forall_ ks (lift2 ks iff P1 P3).
  Proof.
    intros.
    eapply forall_trans'; simplify; eauto.
    simpl in *.
    propositional.
  Qed.
      
  Lemma dedup_lift5_2_4 bs :
    forall T A1 A2 A3 A5 (f : A1 -> A2 -> A3 -> A2 -> A5 -> T) a1 a2 a3 a5,
      lift5 bs f a1 a2 a3 a2 a5 = lift4 bs (fun a1 a2 a3 a5 => f a1 a2 a3 a2 a5) a1 a2 a3 a5.
  Proof.
    induct bs; simplify; eauto.
    eapply IHbs.
  Qed.
  
  Lemma dedup_lift6_1_4 bs :
    forall T A1 A2 A3 A5 A6 (f : A1 -> A2 -> A3 -> A1 -> A5 -> A6 -> T) a1 a2 a3 a5 a6,
      lift6 bs f a1 a2 a3 a1 a5 a6 = lift5 bs (fun a1 a2 a3 a5 a6 => f a1 a2 a3 a1 a5 a6) a1 a2 a3 a5 a6.
  Proof.
    induct bs; simplify; eauto.
    eapply IHbs.
  Qed.
  
  Lemma forall_and_assoc bs p1 p2 p3 :
    iff_ bs (lift2 bs and p1 (lift2 bs and p2 p3)) (lift2 bs and (lift2 bs and p1 p2) p3).
  Proof.
    rewrite fuse_lift2_lift2_1.
    rewrite fuse_lift2_lift2_2.
    unfold iff_.
    rewrite fuse_lift2_lift3_1.
    rewrite fuse_lift4_lift3_4.
    rewrite dedup_lift6_1_4.
    rewrite dedup_lift5_2_4.
    rewrite dedup_lift4_3_4.
    eapply forall_lift3.
    unfold iff; propositional.
  Qed.
  
  Lemma and_all_app_iff bs :
    forall ls1 ls2,
      forall_ bs (lift2 bs iff (interp_p bs (and_all (ls1 ++ ls2))) (lift2 bs and (interp_p bs (and_all ls1)) (interp_p bs (and_all ls2)))).
  Proof.
    induct ls1; simpl; intros.
    {
      rewrite fuse_lift2_lift0_1.
      rewrite fuse_lift2_lift1_2.
      rewrite dedup_lift2.
      eapply forall_lift1.
      propositional.
    }
    {
      eapply forall_iff_trans.
      {
        eapply forall_iff_and; [eapply forall_iff_refl |].
        eapply IHls1.
      }
      eapply forall_and_assoc.
    }
  Qed.

  Lemma and_all_app_imply_no_middle bs ls1 ls2 ls3 :
    forall_ bs (lift2 bs imply (interp_p bs (and_all (ls1 ++ ls2 ++ ls3))) (interp_p bs (and_all (ls1 ++ ls3)))).
  Proof.
    eapply forall_trans.
    {
      eapply forall_iff_imply.
      eapply and_all_app_iff.
    }
    eapply forall_trans.
    {
      eapply forall_iff_imply.
      eapply forall_iff_and; [eapply forall_iff_refl |].
      eapply and_all_app_iff.
    }
    eapply forall_trans.
    Focus 2.
    {
      eapply forall_iff_imply.
      eapply forall_iff_sym.
      eapply and_all_app_iff.
    }
    Unfocus.
    {
      rewrite fuse_lift2_lift2_1.
      rewrite fuse_lift3_lift2_3.
      rewrite dedup_lift4_1_3.
      rewrite fuse_lift3_lift2_2.
      rewrite dedup_lift4_3_4.
      eapply forall_lift3.
      propositional.
    }
  Qed.
  
  Lemma forall_iff_refl' bs p1 p2 :
    p1 = p2 ->
    forall_ bs (lift2 bs iff p1 p2).
  Proof.
    intros; subst.
    eapply forall_iff_refl.
  Qed.

  Lemma skipn_my_skipn A :
    forall (ls : list A) x,
      skipn x ls = my_skipn ls x.
  Proof.
    induct ls; destruct x; simpl; eauto.
  Qed.

  Lemma firstn_my_skipn A n (l : list A) : firstn n l ++ my_skipn l n = l.
  Proof.
    rewrite <- skipn_my_skipn.
    rewrite firstn_skipn.
    eauto.
  Qed.

  Lemma and_all_map_shift_i_p n x ls :
    and_all (map (shift_i_p n x) ls) = shift_i_p n x (and_all ls).
  Proof.
    induct ls; simpl; eauto.
    rewrite IHls; eauto.
  Qed.

  Inductive wellscoped_s : nat -> sort -> Prop :=
  | WscsBaseSort L b :
      wellscoped_s L (SBaseSort b)
  | WscsSubset L b p :
      wellscoped_p (1 + L) p ->
      wellscoped_s L (SSubset b p)
  .

  Hint Constructors wellscoped_s.

  Lemma wellscoped_shift_i_i L i :
    wellscoped_i L i ->
    forall x n L',
      L' = n + L ->
      wellscoped_i L' (shift_i_i n x i).
  Proof.
    induct 1; simpl; try solve [intros; subst; eauto with db_la].
    {
      rename x into y.
      intros x n.
      intros; subst.
      cases (x <=? y); simpl in *; eauto with db_la.
    }
  Qed.
  
  Lemma wellscoped_shift_i_p L p :
    wellscoped_p L p ->
    forall x n L',
      L' = n + L ->
      wellscoped_p L' (shift_i_p n x p).
  Proof.
    induct 1; simpl; try solve [intros; subst; eauto using wellscoped_shift_i_i with db_la].
  Qed.
  
  Inductive all_sorts (P : list sort -> sort -> Prop) : list sort -> Prop :=
  | AllStsNil :
      all_sorts P []
  | AllStsCons s ss :
      all_sorts P ss ->
      P ss s ->
      all_sorts P (s :: ss)
  .

  Hint Constructors all_sorts.

  Definition wellscoped_ss := all_sorts (fun ss s => wellscoped_s (length ss) s).

  Lemma wellscoped_ss_wellscoped_p_strip_subsets L :
    wellscoped_ss L ->
    forall n,
      n = length L ->
      wellscoped_p n (and_all (strip_subsets L)).
  Proof.
    induct 1; simpl; intros n ?; subst; eauto.
    {
      econstructor.
    }
    invert H0; simpl in *.
    {
      unfold shift0_i_p.
      rewrite and_all_map_shift_i_p.
      eapply wellscoped_shift_i_p; eauto.
    }
    {
      econstructor; eauto.
      unfold shift0_i_p.
      rewrite and_all_map_shift_i_p.
      eapply wellscoped_shift_i_p; eauto.
    }
  Qed.

  Lemma interp_prop_shift_i_p L p :
    interp_prop L p ->
    wellscoped_ss L ->
    wellscoped_p (length L) p ->
    forall x ls ,
      let n := length ls in
      x <= length L ->
      interp_prop (shift_i_ss n (firstn x L) ++ ls ++ my_skipn L x) (shift_i_p n x p).
  Proof.
    cbn in *.
    intros H Hscss Hscp x ls Hle.
    unfold interp_prop in *.
    cbn in *.
    rewrite !get_bsort_insert_shift.
    rewrite !strip_subsets_insert by la.
    set (bs := map get_bsort L) in *.
    set (bs_new := map get_bsort ls) in *.
    eapply forall_lift2_imply_shift; eauto.
    {
      eapply forall_trans.
      {
        eapply and_all_app_imply_no_middle.
      }
      {
        eapply forall_iff_imply.
        eapply forall_iff_sym.
        eapply forall_iff_trans.
        {
          eapply forall_iff_sym.
          eapply forall_shift_i_p_iff_shift; eauto.
          subst bs.
          rewrite map_length.
          eapply wellscoped_ss_wellscoped_p_strip_subsets; eauto.
        }
        eapply forall_iff_refl'.
        rewrite <- (firstn_my_skipn x L) at 1.
        rewrite strip_subsets_app.
        rewrite <- and_all_map_shift_i_p.
        rewrite map_app.
        rewrite map_map.
        subst bs.
        subst bs_new.
        repeat rewrite map_length.
        f_equal.
        f_equal.
        f_equal.
        eapply map_ext.
        intros b.
        rewrite length_firstn_le by la.
        rewrite shift_i_p_shift_merge by la.
        eauto.
      }
    }
    {
      eapply forall_iff_imply.
      eapply forall_iff_sym.
      subst bs.
      subst bs_new.
      eapply forall_shift_i_p_iff_shift; try rewrite map_length; eauto.
    }
  Qed.

  Ltac interp_le := try eapply interp_time_interp_prop_le; apply_all interp_prop_le_interp_time.

  Inductive sorteq : sctx -> sort -> sort -> Prop :=
  | SortEqBaseSort L b :
      sorteq L (SBaseSort b) (SBaseSort b)
  | SortEqSubset L b p p' :
      interp_prop (SBaseSort b :: L) (p <===> p')%idx ->
      sorteq L (SSubset b p) (SSubset b p')
  .

  Hint Constructors sorteq.

  Lemma interp_prop_subset_imply' ks :
    forall Kp Kps Kp0
      (f1 : Kp -> Kps -> Kp0 -> Prop)
      (f : Kps -> Kp -> Kp0 -> Prop)
      kp kps kp0,
      (forall kp kps kp0,
          f1 kp kps kp0 ->
          f kps kp kp0
      ) ->
      forall_ ks (lift3 ks f1 kp kps kp0) ->
      forall_ ks (lift3 ks f kps kp kp0).
  Proof.
    induct ks; simplify; eauto.
    rewrite fuse_lift1_lift3 in *.
    eapply IHks; eauto.
    simplify.
    eauto.
  Qed.

  (* Some Coq bug(s)! *)
  
  (* Lemma interp_prop_subset_imply k p L p0 : *)
  (*   interp_prop (KSubset k p :: L) p0 -> *)
  (*   interp_prop (k :: L) (p ===> p0)%idx. *)
  (* Proof. *)
  (*   cbn. *)
  (*   (* Anomaly: conversion was given ill-typed terms (FProd). Please report. *) *)
  (* Qed. *)
  
  (* Lemma do_cbn k L p p0 : *)
  (*   interp_p (fst (strip_subsets (k :: L))) *)
  (*            (and_all (snd (strip_subsets (k :: L))) ===> (p ===> p0))%idx = *)
  (*   lift2 (fst (strip_subsets L)) *)
  (*         (fun (a1 a2 : interp_bsort (kind_to_sort k) -> Prop) (ak : interp_bsort (kind_to_sort k)) *)
  (*          => a1 ak -> a2 ak) *)
  (*         (interp_p (kind_to_sort k :: fst (strip_subsets L)) *)
  (*                   (and_all (strip_subset k ++ map shift0_i_p (snd (strip_subsets L))))) *)
  (*         (lift2 (fst (strip_subsets L)) *)
  (*                (fun (a1 a2 : interp_bsort (kind_to_sort k) -> Prop) *)
  (*                   (ak : interp_bsort (kind_to_sort k)) => a1 ak -> a2 ak) *)
  (*                (interp_p (kind_to_sort k :: fst (strip_subsets L)) p) *)
  (*                (interp_p (kind_to_sort k :: fst (strip_subsets L)) p0)). *)
  (* Proof. *)
  (*   (* Error: Conversion test raised an anomaly *) *)
  (*   apply eq_refl. *)
  (* Qed. *)

  Lemma interp_prop_subset_imply b p L p0 :
    interp_prop (SSubset b p :: L) p0 <->
    interp_prop (SBaseSort b :: L) (p ===> p0)%idx.
  Proof.
    cbn in *.
    rewrite !fuse_lift1_lift2 in *.
    rewrite !fuse_lift2_lift2_1 in *.
    rewrite !fuse_lift2_lift2_2 in *.
    split.
    {
      eapply interp_prop_subset_imply'; eauto.
    }
    {
      eapply interp_prop_subset_imply'; eauto.
      propositional; eauto.
    }
    (* Anomaly: conversion was given ill-typed terms (FProd). Please report. *)
    (* Qed. *)
  Admitted.

  (*
    Lemma interp_prop_subset_imply k p L p0 :
      interp_prop (KSubset k p :: L) p0 <->
      interp_prop (k :: L) (p ===> p0)%idx.
    Proof.
      unfold interp_prop.
      hnf in *.
      Lemma do_cbn k L p p0 :
        interp_p (fst (strip_subsets (k :: L)))
                 (and_all (snd (strip_subsets (k :: L))) ===> (p ===> p0))%idx =
lift2 (fst (strip_subsets L))
          (fun (a1 a2 : interp_bsort (kind_to_sort k) -> Prop) (ak : interp_bsort (kind_to_sort k))
           => a1 ak -> a2 ak)
          (interp_p (kind_to_sort k :: fst (strip_subsets L))
             (and_all (strip_subset k ++ map shift0_i_p (snd (strip_subsets L)))))
          (lift2 (fst (strip_subsets L))
             (fun (a1 a2 : interp_bsort (kind_to_sort k) -> Prop)
                (ak : interp_bsort (kind_to_sort k)) => a1 ak -> a2 ak)
             (interp_p (kind_to_sort k :: fst (strip_subsets L)) p)
             (interp_p (kind_to_sort k :: fst (strip_subsets L)) p0)).
      Proof.
        exact eq_refl.
      Qed.

      rewrite do_cbn.

      Lemma do_cbn2 k L p p0 :
        interp_p (fst (strip_subsets (KSubset k p :: L)))
                 (and_all (snd (strip_subsets (KSubset k p :: L))) ===> p0)%idx =
        lift2 (fst (strip_subsets L))
              (fun (a1 a2 : interp_bsort (kind_to_sort k) -> Prop)
                 (ak : interp_bsort (kind_to_sort k)) => a1 ak -> a2 ak)
              (lift2 (fst (strip_subsets L))
                     (fun (a1 a2 : interp_bsort (kind_to_sort k) -> Prop)
                        (ak : interp_bsort (kind_to_sort k)) => a1 ak /\ a2 ak)
                     (interp_p (kind_to_sort k :: fst (strip_subsets L)) p)
                     (interp_p (kind_to_sort k :: fst (strip_subsets L))
                               (and_all (strip_subset k ++ map shift0_i_p (snd (strip_subsets L))))))
              (interp_p (kind_to_sort k :: fst (strip_subsets L)) p0).
      Proof.
        exact eq_refl.
      Qed.

      rewrite do_cbn2.
      rewrite !fuse_lift2_lift2_1 in *.
      rewrite !fuse_lift2_lift2_2 in *.
      propositional.
      {
        (* eapply admit. *)
        eapply interp_prop_subset_imply'; eauto.
        simplify.
        eauto.
      }
      {
        eapply admit.
        (* eapply interp_prop_subset_imply'; eauto. *)
        (* simplify. *)
        (* eauto. *)
      }
    Qed.
   *)
  
  Lemma sorteq_interp_prop' ks :
    forall P P' Kps P0 K'ps
      (f1 : Kps -> P -> P' -> Prop)
      (f2 : Kps -> P' -> P0 -> Prop)
      (f3 : Kps -> K'ps -> Prop)
      (f : Kps -> P -> P0 -> Prop)
      p p' kps p0 k'ps,
      (forall p p' kps p0 k'ps,
          f1 kps p p' ->
          f2 kps p' p0 ->
          f3 kps k'ps ->
          f kps p p0
      ) ->
      forall_ ks (lift3 ks f1 kps p p') ->
      forall_ ks (lift3 ks f2 kps p' p0) ->
      forall_ ks (lift2 ks f3 kps k'ps) ->
      forall_ ks (lift3 ks f kps p p0).
  Proof.
    induct ks; simplify; eauto.
    rewrite fuse_lift1_lift2 in *.
    rewrite fuse_lift1_lift3 in *.
    eapply IHks; eauto.
    simplify.
    eauto.
  Qed.
  
  Lemma sorteq_interp_prop_rev L k k' :
    sorteq L k k' ->
    forall p,
      interp_prop (k' :: L) p ->
      interp_prop (k :: L) p.
  Proof.
    induct 1; eauto.
    intros p0 Hp.
    (* specialize (IHsorteq p0). *)
    
    eapply interp_prop_subset_imply.
    eapply interp_prop_subset_imply in Hp.
    cbn in *.
    repeat rewrite fuse_lift1_lift2 in *.
    repeat rewrite fuse_lift2_lift2_1 in *.
    repeat rewrite fuse_lift2_lift2_2 in *.
    eapply sorteq_interp_prop' with (f3 := fun P Q => forall a, P a <-> Q a); [ | eapply H | eapply Hp | ].
    {
      simplify.
      specialize (H0 a).
      specialize (H1 a).
      specialize (H2 a).
      propositional; eauto.
    }
    {
      erewrite dedup_lift2.
      eapply forall_lift1.
      propositional.
    }
    (* Anomaly: conversion was given ill-typed terms (FProd). Please report. *)
    (* Qed. *)
  Admitted.
    
  Lemma sorteq_refl : forall L k, sorteq L k k.
  Proof.
    induct k; eauto using interp_prop_iff_refl.
  Qed.

  Lemma sorteq_refl2 : forall L k k', k = k' -> sorteq L k k'.
  Proof.
    intros; subst; eapply sorteq_refl.
  Qed.
  
  Lemma sorteq_sym L a b : sorteq L a b -> sorteq L b a.
  Proof.
    induct 1; eauto using sorteq_interp_prop_rev, interp_prop_iff_sym.
  Qed.

  Lemma sorteq_trans' L a b :
    sorteq L a b ->
    forall c,
      sorteq L b c -> sorteq L a c.
  Proof.
    induct 1; invert 1; eauto 6 using interp_prop_iff_trans, sorteq_interp_prop_rev, sorteq_sym.
  Qed.

  Lemma sorteq_trans L a b c : sorteq L a b -> sorteq L b c -> sorteq L a c.
  Proof.
    intros; eapply sorteq_trans'; eauto.
  Qed.

  Lemma sorteq_interp_prop L k k' :
    sorteq L k k' ->
    forall p,
      interp_prop (k :: L) p ->
      interp_prop (k' :: L) p.
  Proof.
    intros H; intros.
    eapply sorteq_sym in H.
    eapply sorteq_interp_prop_rev; eauto.
  Qed.
  
  Lemma sorteq_get_bsort L k k' :
    sorteq L k k' ->
    get_bsort k' = get_bsort k.
  Proof.
    induct 1; simplify; eauto.
  Qed.
  
  Lemma forall_lift2_lift3_lift2 :
    forall bs A B C P1 P2 P3 (f : A -> B -> Prop) (g : A -> B -> C -> Prop) (h : A -> C -> Prop),
      (forall a b c, f a b -> g a b c -> h a c) ->
      forall_ bs (lift2 bs f P1 P2) ->
      forall_ bs (lift3 bs g P1 P2 P3) ->
      forall_ bs (lift2 bs h P1 P3).
  Proof.
    induct bs; simplify; eauto.
    rewrite fuse_lift1_lift2 in *.
    rewrite fuse_lift1_lift3 in *.
    eapply IHbs; eauto.
    simplify.
    eauto.
  Qed.
  
  Lemma interp_prop_iff_elim L p p' :
    interp_prop L p ->
    interp_prop L (p <===> p')%idx ->
    interp_prop L p'.
  Proof.
    intros Hp Hpp'.
    unfold interp_prop in *; simpl in *.
    rewrite fuse_lift2_lift2_2 in *.
    eapply forall_lift2_lift3_lift2; eauto.
    simpl; propositional.
  Qed.
  
  Lemma forall_iff_elim bs p p' :
    forall_ bs p ->
    iff_ bs p p' ->
    forall_ bs p'.
  Proof.
    intros Hp Hpp'.
    eapply forall_use_premise; [eapply Hp |].
    eapply forall_iff_imply.
    eauto.
  Qed.
  
  Lemma fuse_lift4_lift1_4 bs :
    forall T A1 A2 A3 A4 B1 (f : A1 -> A2 -> A3 -> A4 -> T) (g : B1 -> A4) a1 a2 a3 b1,
      lift4 bs f a1 a2 a3 (lift1 bs g b1) = lift4 bs (fun a1 a2 a3 b1 => f a1 a2 a3 (g b1)) a1 a2 a3 b1.
  Proof.
    induct bs; simplify; eauto.
    eapply IHbs.
  Qed.
  
  Lemma fuse_lift4_lift1_2 bs :
    forall T A1 A2 A3 A4 B1 (f : A1 -> A2 -> A3 -> A4 -> T) (g : B1 -> A2) a1 a3 a4 b1,
      lift4 bs f a1 (lift1 bs g b1) a3 a4 = lift4 bs (fun a1 b1 a3 a4 => f a1 (g b1) a3 a4) a1 b1 a3 a4.
  Proof.
    induct bs; simplify; eauto.
    eapply IHbs.
  Qed.
  
  Inductive equal_sorts : list sort -> list sort -> Prop :=
  | EKNil : equal_sorts [] []
  | EKCons L L' k k' :
      equal_sorts L L' ->
      sorteq L k k' ->
      equal_sorts (k :: L) (k' :: L')
  .

  Hint Constructors equal_sorts.
  
  Lemma equal_sorts_length L L' :
    equal_sorts L L' ->
    length L = length L'.
  Proof.
    induct 1; simpl; eauto.
  Qed.
  
  Lemma equal_sorts_get_bsort L L' :
    equal_sorts L L' ->
    map get_bsort L = map get_bsort L'.
  Proof.
    induct 1; simpl; f_equal; eauto using sorteq_get_bsort, sorteq_sym.
  Qed.
  
  Lemma forall_lift4_lift2_lift2_lift4 :
    forall bs A1 A2 A3 A4 A5 A6 P1 P2 P3 P4 P5 P6 (f1 : A1 -> A2 -> A3 -> A4 -> Prop) (f2 : A5 -> A2 -> Prop) (f3 : A6 -> A4 -> Prop) (f4 : A1 -> A5 -> A3 -> A6 -> Prop),
      (forall a1 a2 a3 a4 a5 a6, f1 a1 a2 a3 a4 -> f2 a5 a2 -> f3 a6 a4 -> f4 a1 a5 a3 a6) ->
      forall_ bs (lift4 bs f1 P1 P2 P3 P4) ->
      forall_ bs (lift2 bs f2 P5 P2) ->
      forall_ bs (lift2 bs f3 P6 P4) ->
      forall_ bs (lift4 bs f4 P1 P5 P3 P6).
  Proof.
    induct bs; simplify; eauto.
    rewrite fuse_lift1_lift2 in *.
    rewrite fuse_lift1_lift4 in *.
    eapply IHbs; eauto.
    simplify.
    eauto.
  Qed.
  
  Lemma forall_lift2_lift2_lift2 ks :
    forall A B C P1 P2 P3 (f : B -> A -> Prop) (g : B -> C -> Prop) (h : A -> C -> Prop),
      (forall a b c, f b a -> g b c -> h a c) ->
      forall_ ks (lift2 ks f P2 P1) ->
      forall_ ks (lift2 ks g P2 P3) ->
      forall_ ks (lift2 ks h P1 P3).
  Proof.
    induct ks; simplify; eauto.
    rewrite fuse_lift1_lift2 in *.
    eapply IHks; eauto.
    simplify.
    eauto.
  Qed.
  
  Lemma forall_lift2_lift3_lift4 :
    forall bs A1 A2 A3 A4 P1 P2 P3 P4 (f1 : A2 -> A4 -> Prop) (f2 : A2 -> A1 -> A3 -> Prop) (f3 : A1 -> A2 -> A3 -> A4 -> Prop),
      (forall a1 a2 a3 a4, f1 a2 a4 -> f2 a2 a1 a3 -> f3 a1 a2 a3 a4) ->
      forall_ bs (lift2 bs f1 P2 P4) ->
      forall_ bs (lift3 bs f2 P2 P1 P3) ->
      forall_ bs (lift4 bs f3 P1 P2 P3 P4).
  Proof.
    induct bs; simplify; eauto.
    rewrite fuse_lift1_lift2 in *.
    rewrite fuse_lift1_lift3 in *.
    rewrite fuse_lift1_lift4 in *.
    eapply IHbs; eauto.
    simplify.
    eauto.
  Qed.
  
  Lemma equal_sorts_strip_subsets L L' :
    equal_sorts L L' ->
    wellscoped_ss L ->
    wellscoped_ss L' ->
    let bs := map get_bsort L in
    let ps := strip_subsets L in
    let ps' := strip_subsets L' in
    iff_ bs (interp_p bs (and_all ps)) (interp_p bs (and_all ps')).
  Proof.
    simpl.
    induct 1; simpl; intros Hsc Hsc'.
    {
      eapply forall_iff_refl.
    }
    invert Hsc.
    invert Hsc'.
    eapply forall_iff_trans.
    {
      eapply and_all_app_iff.
    }
    eapply forall_iff_sym.
    eapply forall_iff_trans.
    {
      eapply and_all_app_iff.
    }
    eapply forall_iff_sym.
    rename H0 into Hsorteq.
    invert Hsorteq.
    {
      eapply forall_iff_and.
      {
        simpl.
        eapply forall_iff_refl.
      }
      {
        simpl.
        unfold shift0_i_p.
        repeat rewrite and_all_map_shift_i_p in *.
        eapply forall_iff_trans.
        {
          eapply forall_shift_i_p_iff_shift with (bs_new := [b]) (x := 0); simpl; eauto.
          eapply wellscoped_ss_wellscoped_p_strip_subsets; eauto.
          rewrite map_length; eauto.
        }
        eapply forall_iff_sym.
        eapply forall_iff_trans.
        {
          eapply forall_shift_i_p_iff_shift with (bs_new := [b]) (x := 0); simpl; eauto.
          eapply wellscoped_ss_wellscoped_p_strip_subsets; eauto.
          rewrite map_length; eauto.
          eapply equal_sorts_length; eauto.
        }
        simpl.
        rewrite fuse_lift2_lift1_1.
        rewrite fuse_lift2_lift1_2.
        rewrite fuse_lift1_lift2.
        eapply forall_lift2_lift2; [| eapply forall_iff_sym; eapply IHequal_sorts; eauto].
        unfold iff; propositional.
      }
    }
    {
      unfold interp_prop in *.
      simpl in *.
      repeat rewrite fuse_lift2_lift0_2 in *.
      repeat rewrite fuse_lift2_lift1_1 in *.
      unfold shift0_i_p in *.
      repeat rewrite and_all_map_shift_i_p in *.
      repeat rewrite fuse_lift1_lift2 in *.
      repeat rewrite fuse_lift2_lift2_1 in *.
      repeat rewrite fuse_lift3_lift2_3 in *.
      eapply forall_lift4_lift2_lift2_lift4.
      Focus 3.
      {
        specialize (@forall_shift_i_p_iff_shift (and_all (strip_subsets L)) [b] 0 (map get_bsort L) 1); intros Hshift.
        simpl in *.
        rewrite fuse_lift1_lift2 in Hshift.
        eapply Hshift; eauto.
        eapply wellscoped_ss_wellscoped_p_strip_subsets; eauto.
        rewrite map_length; eauto.
      }
      Unfocus.
      Focus 3.
      {
        specialize (@forall_shift_i_p_iff_shift (and_all (strip_subsets L')) [b] 0 (map get_bsort L) 1); intros Hshift.
        simpl in *.
        rewrite fuse_lift1_lift2 in Hshift.
        eapply Hshift; eauto.
        eapply wellscoped_ss_wellscoped_p_strip_subsets; eauto.
        rewrite map_length; eauto.
        eapply equal_sorts_length; eauto.
      }
      Unfocus.
      {
        simpl.
        instantiate (1 := fun a1 a2 a3 a4 => forall x, a1 x /\ a2 x <-> a3 x /\ a4 x).
        simpl.
        intros.
        specialize (H1 a).
        specialize (H2 a).
        specialize (H7 a).
        propositional.
      }
      unfold iff_ in *.
      rewrite fuse_lift4_lift1_2 in *.
      rewrite fuse_lift4_lift1_4 in *.
      eapply forall_lift2_lift2_lift2 in H0.
      Focus 3.
      {
        specialize (@forall_shift_i_p_iff_shift (and_all (strip_subsets L)) [b] 0 (map get_bsort L) 1); intros Hshift.
        simpl in *.
        rewrite fuse_lift1_lift2 in Hshift.
        eapply Hshift; eauto.
        eapply wellscoped_ss_wellscoped_p_strip_subsets; eauto.
        rewrite map_length; eauto.
      }
      Unfocus.
      Focus 2.
      {
        instantiate (1 := fun a1 a2  => forall x, a1 x -> a2 x).
        simpl.
        intros.
        specialize (H1 x).
        specialize (H2 x).
        propositional.
      }
      Unfocus.
      
      repeat rewrite fuse_lift2_lift1_1 in *.
      repeat rewrite fuse_lift2_lift2_2 in *.
      eapply forall_lift2_lift3_lift4; eauto.
      simpl.
      intros.
      specialize (H2 x).
      propositional.
    }
  Qed.
  
  Lemma equal_sorts_interp_prop L L' :
    equal_sorts L L' ->
    forall p,
      wellscoped_ss L ->
      wellscoped_ss L' ->
      interp_prop L p ->
      interp_prop L' p.
  Proof.
    intros Heq p Hsc Hsc' Hp.
    unfold interp_prop in *.
    erewrite <- equal_sorts_get_bsort; eauto.
    simpl in *.
    eapply forall_iff_elim; [eapply Hp|].
    eapply forall_iff_iff_imply; [|eapply forall_iff_refl].
    eapply equal_sorts_strip_subsets; eauto.
  Qed.
  
  Lemma get_bsort_subst_i_s :
    forall b x v,
      get_bsort (subst_i_s x v b) = get_bsort b.
  Proof.
    induct b; simpl; eauto.
  Qed.
  
  Lemma get_bsort_subst_i_ss :
    forall L v,
      map get_bsort (subst_i_ss v L) = map get_bsort L.
  Proof.
    induct L; simpl; intros; f_equal; eauto using get_bsort_subst_i_s.
  Qed.

  Lemma removen_firstn_my_skipn A :
    forall (ls : list A) n,
      removen n ls = firstn n ls ++ my_skipn ls (S n).
  Proof.
    induct ls; destruct n; simpl; eauto.
    {
      rewrite my_skipn_0; eauto.
    }
    f_equal.
    eapply IHls.
  Qed.

  Definition apply {A B} (f : A -> B) x := f x.
  
  Fixpoint subst x bs b_v B {struct bs} : interp_bsorts (skipn (S x) bs) (interp_bsort b_v) -> interp_bsorts bs B -> interp_bsorts (removen x bs) B :=
    match bs return interp_bsorts (skipn (S x) bs) (interp_bsort b_v) -> interp_bsorts bs B -> interp_bsorts (removen x bs) B with
    | [] => fun v body => body
    | b :: bs' =>
      match x return interp_bsorts (skipn (S x) (b :: bs')) (interp_bsort b_v) -> interp_bsorts (b :: bs') B -> interp_bsorts (removen x (b :: bs')) B with
      | 0 => fun v body => lift2 bs' (fun body v => body (convert_sort_value b_v b v)) body v
      | S x' => fun v body => subst x' bs' b_v (interp_bsort b -> B) v body
      end
    end.

  Arguments subst x bs {b_v B} v b.

  Lemma lift1_eq_lift0 :
    forall bs A B v f,
      lift1 bs (fun _ : A => f : B) v = lift0 bs f.
  Proof.
    induct bs; simpl; eauto.
  Qed.
  
  Lemma subst_lift0 : forall bs x B b_v (v : interp_bsorts (skipn (S x) bs) (interp_bsort b_v)) (f : B), subst x bs v (lift0 bs f) = lift0 (removen x bs) f.
  Proof.
    induct bs; cbn in *; intros; eauto.
    destruct x; cbn in *; intros.
    {
      rewrite fuse_lift2_lift0_1.
      eapply lift1_eq_lift0.
    }
    {
      eauto.
    }
  Qed.
  
  Lemma dedup_lift4_2_4 bs :
    forall T A1 A2 A3 (f : A1 -> A2 -> A3 -> A2  -> T) a1 a2 a3,
      lift4 bs f a1 a2 a3 a2 = lift3 bs (fun a1 a2 a3 => f a1 a2 a3 a2) a1 a2 a3.
  Proof.
    induct bs; simplify; eauto.
    eapply IHbs.
  Qed.
  
  Lemma swap_lift3_2_3 :
    forall bs T A1 A2 A3 (f1 : A1 -> A2 -> A3 -> T) (f2 : A1 -> A3 -> A2 -> T) a1 a2 a3,
      (forall a1 a2 a3, f1 a1 a2 a3 = f2 a1 a3 a2) ->
      lift3 bs f1 a1 a2 a3 = lift3 bs f2 a1 a3 a2.
  Proof.
    induct bs; simpl; intros; eauto.
    eapply IHbs.
    intros.
    eapply FunctionalExtensionality.functional_extensionality.
    eauto.
  Qed.
  
  Lemma subst_lift2 : forall bs x A1 A2 B b_v (v : interp_bsorts (skipn (S x) bs) (interp_bsort b_v)) (f : A1 -> A2 -> B) a1 a2, subst x bs v (lift2 bs f a1 a2) = lift2 (removen x bs) f (subst x bs v a1) (subst x bs v a2).
  Proof.
    induct bs; cbn in *; intros; eauto.
    destruct x; cbn in *; intros.
    {
      rewrite !fuse_lift2_lift2_1.
      rewrite fuse_lift3_lift2_3.
      rewrite dedup_lift4_2_4.
      erewrite swap_lift3_2_3; eauto.
    }
    {
      eauto.
    }
  Qed.

  Lemma subst_lift1 : forall bs x A1 B b_v (v : interp_bsorts (skipn (S x) bs) (interp_bsort b_v)) (f : A1 -> B) a1, subst x bs v (lift1 bs f a1) = lift1 (removen x bs) f (subst x bs v a1).
  Proof.
    induct bs; cbn in *; intros; eauto.
    destruct x; cbn in *; intros.
    {
      rewrite !fuse_lift2_lift1_1.
      rewrite fuse_lift1_lift2.
      eauto.
    }
    {
      eauto.
    }
  Qed.

  Lemma forall_eq_trans bs T (P1 P2 P3 : interp_bsorts bs T):
    forall_ bs (lift2 bs eq P1 P2) ->
    forall_ bs (lift2 bs eq P2 P3) ->
    forall_ bs (lift2 bs eq P1 P3).
  Proof.
    intros.
    eapply forall_trans'; simplify; eauto.
    subst.
    eauto.
  Qed.
  
  Lemma removen_firstn_skipn A :
    forall (ls : list A) n,
      removen n ls = firstn n ls ++ skipn (S n) ls.
  Proof.
    induct ls; destruct n; simpl; f_equal; eauto.
  Qed.

  Definition invert_eq_cons A (a1 : A) ls1 a2 ls2 (Heq : a1 :: ls1 = a2 :: ls2) : (a1 = a2) * (ls1 = ls2).
  Proof.
    inversion Heq.
    econstructor; eauto.
  Defined.
  
  Definition cast : forall bs1 bs2 T, bs1 = bs2 -> interp_bsorts bs1 T -> interp_bsorts bs2 T.
  Proof.
    refine
      (fix cast bs1 bs2 T {struct bs1} : bs1 = bs2 -> interp_bsorts bs1 T -> interp_bsorts bs2 T :=
         match bs1 return bs1 = bs2 -> interp_bsorts bs1 T -> interp_bsorts bs2 T with
         | [] =>
           match bs2 return [] = bs2 -> interp_bsorts [] T -> interp_bsorts bs2 T with
           | [] => fun _ a => a
           | _ :: _ => _
           end
         | b1 :: bs1' =>
           match bs2 return b1 :: bs1' = bs2 -> interp_bsorts (b1 :: bs1') T -> interp_bsorts bs2 T with
           | [] => _
           | b2 :: bs2' =>
             fun Heq v =>
               lift1 bs2' (fun v x => v (eq_rect b2 _ x b1 _)) (cast bs1' bs2' (interp_bsort b1 -> T) _ v)
                     (* lift1 bs2' (fun v x => v (eq_rect (interp_bsort b2) (fun T => T) x (interp_bsort b1) _)) (cast bs1' bs2' (interp_bsort b1 -> T) _ v) *)
           end
         end
      ).
    {
      intros; discriminate.
    }
    {
      intros; discriminate.
    }
    {
      congruence.
    }
    {
      congruence.
    }
  Defined.

  Arguments cast bs1 bs2 {T} Heq v .

(*          
          Definition cast : forall bs1 bs2 T1 T2, bs1 = bs2 -> T1 = T2 -> interp_bsorts bs1 T1 -> interp_bsorts bs2 T2.
          Proof.
            refine
              (fix cast bs1 bs2 T1 T2 {struct bs1} : bs1 = bs2 -> T1 = T2 -> interp_bsorts bs1 T1 -> interp_bsorts bs2 T2 :=
                 match bs1 return bs1 = bs2 -> T1 = T2 -> interp_bsorts bs1 T1 -> interp_bsorts bs2 T2 with
                 | [] =>
                   match bs2 return [] = bs2 -> T1 = T2 -> interp_bsorts [] T1 -> interp_bsorts bs2 T2 with
                   | [] => fun _ Heq a => eq_rect T1 _ a T2 Heq
                   | _ :: _ => _
                   end
                 | b1 :: bs1' =>
                   match bs2 return b1 :: bs1' = bs2 -> T1 = T2 -> interp_bsorts (b1 :: bs1') T1 -> interp_bsorts bs2 T2 with
                   | [] => _
                   | b2 :: bs2' =>
                     fun Heqs Heq v =>
                       cast bs1' bs2' (interp_bsort b1 -> T1) (interp_bsort b2 -> T2) _ _ v
                   end
                 end
              ).
            {
              intros; discriminate.
            }
            {
              intros; discriminate.
            }
            {
              invert Heqs; eauto.
            }
            {
              invert Heqs; eauto.
            }
          Defined.

          Arguments cast bs1 bs2 {T1 T2} Heqs Heq v .
          
          Definition cast1 bs1 bs2 T (H : bs1 = bs2) v := @cast bs1 bs2 T T H eq_refl v.
          Arguments cast1 bs1 bs2 {T} H v .
*)          
(*
          Lemma cast_eq_intro :
            forall bs1 bs2 (Heq Heq' : bs1 = bs2) T (a a' : interp_bsorts bs1 T),
              a = a' ->
              cast bs1 bs2 Heq a = cast bs1 bs2 Heq' a'.
          Proof.
            induct bs1; destruct bs2; simpl; intros; eauto; try discriminate.
            subst.
            f_equal; eauto.
            eapply FunctionalExtensionality.functional_extensionality.
            intros f.
            eapply FunctionalExtensionality.functional_extensionality.
            intros x.
            f_equal; eauto.
            inversion Heq.
            subst.
            Require Eqdep.
            repeat rewrite <- Eqdep.EqdepTheory.eq_rect_eq.
            eauto.
          Qed.

          Lemma lift1_cast :
            forall bs1 bs2 A T (f : A -> T) (a : interp_bsorts bs1 A) (Heq : bs1 = bs2),
              lift1 bs2 f (cast bs1 bs2 Heq a) = cast bs1 bs2 Heq (lift1 bs1 f a).
          Proof.
            induct bs1; destruct bs2; simpl; intros; eauto; try discriminate.
            rewrite fuse_lift1_lift1.
            repeat rewrite IHbs1.
            eapply cast_eq_intro.
            rewrite fuse_lift1_lift1.
            eauto.
          Qed.
 *)
          
  Lemma cast_lift1 :
    forall bs1 bs2 A T (f : A -> T) (a : interp_bsorts bs1 A) (Heq : bs1 = bs2),
      cast bs1 bs2 Heq (lift1 bs1 f a) = lift1 bs2 f (cast bs1 bs2 Heq a).
  Proof.
    induct bs1; destruct bs2; simpl; intros; eauto; try discriminate.
    rewrite fuse_lift1_lift1.
    rewrite IHbs1.
    rewrite fuse_lift1_lift1.
    eauto.
  Qed.

  Lemma cast_lift2 :
    forall bs1 bs2 A1 A2 T (f : A1 -> A2 -> T) a1 a2 (Heq : bs1 = bs2),
      cast bs1 bs2 Heq (lift2 bs1 f a1 a2) = lift2 bs2 f (cast bs1 bs2 Heq a1) (cast bs1 bs2 Heq a2).
  Proof.
    induct bs1; destruct bs2; simpl; intros; eauto; try discriminate.
    repeat rewrite fuse_lift2_lift1_1 in *.
    repeat rewrite fuse_lift2_lift1_2 in *.
    rewrite IHbs1.
    repeat rewrite fuse_lift1_lift2 in *.
    eauto.
  Qed.

  Lemma forall_cast_intro :
    forall bs1 bs2 p (H : bs1 = bs2),
      forall_ bs1 p ->
      forall_ bs2 (cast _ _ H p).
  Proof.
    induct bs1; destruct bs2; simpl; intros p Heq Hp; eauto; try discriminate.
    rewrite fuse_lift1_lift1.
    rewrite <- cast_lift1.
    eapply IHbs1.
    eapply forall_use_premise; eauto.
    rewrite fuse_lift2_lift1_1.
    rewrite fuse_lift2_lift1_2.
    rewrite dedup_lift2.
    eapply forall_lift1.
    intros f Hf x.
    eauto.
  Qed.

  Lemma forall_cast_elim :
    forall bs1 bs2 p (H : bs1 = bs2),
      forall_ bs2 (cast _ _ H p) ->
      forall_ bs1 p.
  Proof.
    induct bs1; destruct bs2; simpl; intros p Heq Hp; eauto; try discriminate.
    rewrite fuse_lift1_lift1 in *.
    rewrite <- cast_lift1 in *.
    eapply IHbs1 in Hp.
    eapply forall_use_premise; eauto.
    rewrite fuse_lift2_lift1_1.
    rewrite fuse_lift2_lift1_2.
    rewrite dedup_lift2.
    eapply forall_lift1.
    intros f Hf x.
    inversion Heq; subst.
    specialize (Hf x).
    rewrite <- Eqdep.EqdepTheory.eq_rect_eq in *.
    eauto.
  Qed.

  Lemma cast_refl_eq :
    forall bs (Heq : bs = bs) T (a : interp_bsorts bs T),
      cast bs bs Heq a = a.
  Proof.
    induct bs; simpl; intros; eauto.
    inversion Heq; subst.
    rewrite IHbs.
    etransitivity; [| eapply fuse_lift1_id].
    f_equal.
    simpl.
    eapply FunctionalExtensionality.functional_extensionality.
    intros f.
    eapply FunctionalExtensionality.functional_extensionality.
    intros x.
    f_equal.
    rewrite <- Eqdep.EqdepTheory.eq_rect_eq.
    eauto.
  Qed.
  
  Lemma cast_roundtrip :
    forall bs1 bs2 (Heq : bs1 = bs2) (Heq' : bs2 = bs1) T (v : interp_bsorts bs1 T),
      cast bs2 bs1 Heq' (cast bs1 bs2 Heq v) = v.
    induct bs1; destruct bs2; simpl; intros; eauto; try discriminate.
    rewrite cast_lift1.
    rewrite IHbs1.
    rewrite fuse_lift1_lift1.
    etransitivity; [| eapply fuse_lift1_id].
    f_equal.
    simpl.
    eapply FunctionalExtensionality.functional_extensionality.
    intros f.
    eapply FunctionalExtensionality.functional_extensionality.
    intros x.
    f_equal.
    inversion Heq; subst.
    repeat rewrite <- Eqdep.EqdepTheory.eq_rect_eq.
    eauto.
  Qed.

  Lemma cast_interp_idx :
    forall i bs1 bs2 (Heq : bs1 = bs2) b,
      cast bs1 bs2 Heq (interp_idx i bs1 b) = interp_idx i bs2 b.
  Proof.
    intros.
    subst.
    rewrite cast_refl_eq; eauto.
  Qed.

  Lemma convert_sort_value_refl_eq :
    forall b v, convert_sort_value b b v = v.
  Proof.
    intros.
    unfold convert_sort_value.
    cases (sort_dec b b); propositional.
    unfold eq_rec_r.
    unfold eq_rec.
    rewrite <- Eqdep.EqdepTheory.eq_rect_eq.
    eauto.
  Qed.

  Lemma forall_interp_var_eq_subst_eq' :
    forall bs x b (f : interp_bsort b -> interp_bsort b -> Prop) b_v (v : interp_bsorts (skipn (S x) bs) (interp_bsort b_v)) (Heq : firstn x bs ++ skipn (S x) bs = removen x bs),
      nth_error bs x = Some b_v ->
      (forall x, f x x) ->
      let bs' := removen x bs in
      forall_
        bs'
        (lift2
           bs' (fun a1 a2 => f (convert_sort_value b_v b a1) a2)
           (cast _ _ Heq (shift0 (firstn x bs) (skipn (S x) bs) v))
           (subst x bs v (interp_var x bs b))).
  Proof.
    simpl.
    induct bs; simpl; intros x b f b_v v Heq Hx Hf; try la.
    {
      rewrite nth_error_nil in *.
      discriminate.
    }
    destruct x; simpl in *.
    {
      invert Hx.
      rewrite fuse_lift2_lift0_1.
      rewrite fuse_lift2_lift1_2.
      rewrite cast_refl_eq.
      rewrite dedup_lift2.
      eapply forall_lift1.
      intros a.
      rewrite convert_sort_value_refl_eq.
      eauto.
    }
    {
      rewrite fuse_lift2_lift1_1.
      rewrite fuse_lift1_lift2.
      rewrite subst_lift1.
      rewrite fuse_lift2_lift1_2.
      rewrite <- lift1_shift0.
      rewrite cast_lift1.
      rewrite fuse_lift2_lift1_1.
      eapply IHbs with (f := fun x y => interp_bsort a -> f x y); eauto.
    }
  Qed.

  Lemma forall_interp_var_eq_subst_eq_2' :
    forall bs x b (f : interp_bsort b -> interp_bsort b -> Prop) b_v (v : interp_bsorts (skipn (S x) bs) (interp_bsort b_v)) (Heq : removen x bs = firstn x bs ++ skipn (S x) bs),
      nth_error bs x = Some b_v ->
      (forall x, f x x) ->
      let bs' := firstn x bs ++ skipn (S x) bs in
      forall_
        bs'
        (lift2
           bs' (fun a1 a2 => f (convert_sort_value b_v b a1) a2)
           (shift0 (firstn x bs) (skipn (S x) bs) v)
           (cast _ _ Heq (subst x bs v (interp_var x bs b)))).
  Proof.
    intros.
    eapply forall_cast_elim with (bs2 := removen x bs).
    rewrite cast_lift2.
    rewrite cast_roundtrip.
    eapply forall_interp_var_eq_subst_eq'; eauto.
    Grab Existential Variables.
    subst bs'.
    rewrite <- removen_firstn_skipn.
    eauto.
  Qed.
  
  Lemma forall_interp_var_eq_subst_eq :
    forall bs x b b_v (v : interp_bsorts (skipn (S x) bs) (interp_bsort b_v)) (Heq : firstn x bs ++ skipn (S x) bs = removen x bs),
      nth_error bs x = Some b_v ->
      let bs' := removen x bs in
      forall_
        bs'
        (lift2
           bs' eq
           (lift1 _ (convert_sort_value b_v b) (cast _ _ Heq (shift0 (firstn x bs) (skipn (S x) bs) v)))
           (subst x bs v (interp_var x bs b))).
  Proof.
    intros.
    rewrite fuse_lift2_lift1_1.
    eapply forall_interp_var_eq_subst_eq'; eauto.
  Qed.
  
  Lemma forall_interp_var_eq_subst :
    forall bs x b_v (v : interp_bsorts (skipn (S x) bs) (interp_bsort b_v)) (Heq : firstn x bs ++ skipn (S x) bs = removen x bs),
      nth_error bs x = Some b_v ->
      let bs' := removen x bs in
      forall_
        bs'
        (lift2
           bs' eq
           (cast _ _ Heq (shift0 (firstn x bs) (skipn (S x) bs) v))
           (subst x bs v (interp_var x bs b_v))).
  Proof.
    intros.
    eapply forall_eq_trans; [ | eapply forall_interp_var_eq_subst_eq; eauto].
    rewrite fuse_lift2_lift1_2.
    rewrite dedup_lift2.
    eapply forall_lift1.
    intros.
    rewrite convert_sort_value_refl_eq.
    eauto.
  Qed.
  
  Lemma forall_interp_var_eq_subst_eq_2 :
    forall bs x b b_v (v : interp_bsorts (skipn (S x) bs) (interp_bsort b_v)) (Heq : removen x bs = firstn x bs ++ skipn (S x) bs),
      nth_error bs x = Some b_v ->
      let bs' := firstn x bs ++ skipn (S x) bs in
      forall_
        bs'
        (lift2
           bs' eq
           (lift1 _ (convert_sort_value b_v b) (shift0 (firstn x bs) (skipn (S x) bs) v))
           (cast _ _ Heq (subst x bs v (interp_var x bs b)))).
  Proof.
    intros.
    rewrite fuse_lift2_lift1_1.
    eapply forall_interp_var_eq_subst_eq_2'; eauto.
  Qed.
  
  Lemma convert_sort_value_sort_default_value b1 b2 :
    convert_sort_value b1 b2 (sort_default_value b1) = sort_default_value b2.
  Proof.
    unfold convert_sort_value.
    destruct b1; destruct b2; simpl; eauto.
    cases (arity ==n arity0); subst; simpl; eauto.
  Qed.
  
  Inductive bsorting : list bsort -> idx -> bsort -> Prop :=
  | BStgVar L x s :
      nth_error L x = Some s ->
      bsorting L (IVar x) s
  | BStgConst L cn :
      bsorting L (IConst cn) (const_bsort cn)
  | BStgUnOp L opr c :
      bsorting L c (iunop_arg_bsort opr) ->
      bsorting L (IUnOp opr c) (iunop_result_bsort opr)
  | BStgBinOp L opr c1 c2 :
      bsorting L c1 (ibinop_arg1_bsort opr) ->
      bsorting L c2 (ibinop_arg2_bsort opr) ->
      bsorting L (IBinOp opr c1 c2) (ibinop_result_bsort opr)
  | BStgIte L c c1 c2 s :
      bsorting L c BSBool ->
      bsorting L c1 s ->
      bsorting L c2 s ->
      bsorting L (IIte c c1 c2) s
  | BStgTimeAbs L i n :
      bsorting (BSNat :: L) i (BSTimeFun n) ->
      bsorting L (ITimeAbs i) (BSTimeFun (1 + n))
  | BStgTimeApp L c1 c2 n :
      bsorting L c1 (BSTimeFun (S n)) ->
      bsorting L c2 BSNat ->
      bsorting L (ITimeApp n c1 c2) (BSTimeFun n)
  .

  Hint Constructors bsorting.
  
  Inductive bwfprop : list bsort -> prop -> Prop :=
  | BWfPropTrueFalse L cn :
      bwfprop L (PTrueFalse cn)
  | BWfPropBinConn L opr p1 p2 :
      bwfprop L p1 ->
      bwfprop L p2 ->
      bwfprop L (PBinConn opr p1 p2)
  | BWfPropNot L p :
      bwfprop L p ->
      bwfprop L (PNot p)
  | BWfPropBinPred L opr i1 i2 :
      bsorting L i1 (binpred_arg1_bsort opr) ->
      bsorting L i2 (binpred_arg2_bsort opr) ->
      bwfprop L (PBinPred opr i1 i2)
  | BWfPropEq L b i1 i2 :
      bsorting L i1 b ->
      bsorting L i2 b ->
      bwfprop L (PEq b i1 i2)
  | BWfPropQuan L q s p :
      bwfprop (s :: L) p ->
      bwfprop L (PQuan q s p)
  .
  
  Hint Constructors bwfprop.

  Lemma bsorting_wellscoped_i L i s :
    bsorting L i s ->
    wellscoped_i (length L) i.
  Proof.
    induct 1; simpl; eauto.
    econstructor.
    eapply nth_error_Some_lt; eauto.
  Qed.

  Lemma bwfprop_wellscoped_p L p :
    bwfprop L p ->
    wellscoped_p (length L) p.
  Proof.
    induct 1; simpl; eauto using bsorting_wellscoped_i.
  Qed.
  
  Lemma forall_interp_var_eq_subst_lt :
    forall bs x y b (f : interp_bsort b -> interp_bsort b -> Prop) b_v (v : interp_bsorts (skipn (S x) bs) (interp_bsort b_v)),
      y < x ->
      (* y < length bs -> *)
      (forall x, f x x) ->
      let bs' := removen x bs in
      forall_
        bs'
        (lift2
           bs' f
           (interp_var y bs' b)
           (subst x bs v (interp_var y bs b))).
  Proof.
    induct bs; simpl; intros x y b f b_v v Hcmp (* Hy *) Hf; eauto with db_la.
    destruct x; simpl; try la.
    rewrite fuse_lift1_lift2.
    destruct y as [|y]; simpl in *.
    {
      rewrite fuse_lift2_lift0_1.
      rewrite <- subst_lift1.
      rewrite fuse_lift1_lift0.
      rewrite subst_lift0.
      eapply forall_lift0.
      intros; eauto.
    }
    {
      rewrite fuse_lift2_lift1_1.
      rewrite subst_lift1.
      rewrite fuse_lift2_lift1_2.
      eauto with db_la.
    }
  Qed.
  
  Lemma dedup_lift3_1_2 bs :
    forall T A1 A3 (f : A1 -> A1 -> A3 -> T) a1 a3,
      lift3 bs f a1 a1 a3 = lift2 bs (fun a1 a3 => f a1 a1 a3) a1 a3.
  Proof.
    induct bs; simplify; eauto.
    eapply IHbs.
  Qed.
  
  Lemma forall_interp_var_eq_subst_gt :
    forall bs x y b (f : interp_bsort b -> interp_bsort b -> Prop) b_v (v : interp_bsorts (skipn (S x) bs) (interp_bsort b_v)) y',
      x < y ->
      (forall x, f x x) ->
      y' = y - 1 ->
      let bs' := removen x bs in
      forall_
        bs'
        (lift2
           bs' f
           (interp_var y' bs' b)
           (subst x bs v (interp_var y bs b))).
  Proof.
    induct bs; simpl; intros x y b f b_v v y' Hcmp Hf ?; subst; eauto with db_la.
    destruct x; simpl; try la.
    {
      destruct y; simpl in *; try la.
      {
        rewrite fuse_lift2_lift1_1.
        rewrite Nat.sub_0_r.
        rewrite fuse_lift2_lift2_2.
        rewrite dedup_lift3_1_2.
        eapply forall_lift2.
        intros; eauto.
      }
    }
    rewrite fuse_lift1_lift2.
    destruct y; simpl in *.
    {
      rewrite fuse_lift2_lift0_1.
      rewrite <- subst_lift1.
      rewrite fuse_lift1_lift0.
      rewrite subst_lift0.
      eapply forall_lift0.
      intros; eauto.
    }
    {
      rewrite Nat.sub_0_r.
      destruct y; simpl in *; try la.
      rewrite subst_lift1.
      rewrite fuse_lift2_lift1_1.
      rewrite fuse_lift2_lift1_2.
      eauto with db_la.
    }
  Qed.
  
  Lemma bsorting_IUnOp_invert' L i b :
    bsorting L i b ->
    forall opr c,
      i = IUnOp opr c ->
      bsorting L c (iunop_arg_bsort opr) /\
      b = iunop_result_bsort opr.
  Proof.
    induct 1; intros; try discriminate.
    assert (opr = opr0).
    {
      congruence.
    }
    invert H0.
    eauto.
  Qed.

  Lemma bsorting_IUnOp_invert L opr c b :
    bsorting L (IUnOp opr c) b ->
    bsorting L c (iunop_arg_bsort opr) /\
    b = iunop_result_bsort opr.
  Proof.
    intros.
    eapply bsorting_IUnOp_invert'; eauto.
  Qed.

  Lemma dedup_lift5_2_5 bs :
    forall T A1 A2 A3 A4 (f : A1 -> A2 -> A3 -> A4 -> A2 -> T) a1 a2 a3 a4,
      lift5 bs f a1 a2 a3 a4 a2 = lift4 bs (fun a1 a2 a3 a4 => f a1 a2 a3 a4 a2) a1 a2 a3 a4.
  Proof.
    induct bs; simplify; eauto.
    eapply IHbs.
  Qed.
  
  Lemma dedup_lift6_2_4 bs :
    forall T A1 A2 A3 A5 A6 (f : A1 -> A2 -> A3 -> A2 -> A5 -> A6 -> T) a1 a2 a3 a5 a6,
      lift6 bs f a1 a2 a3 a2 a5 a6 = lift5 bs (fun a1 a2 a3 a5 a6 => f a1 a2 a3 a2 a5 a6) a1 a2 a3 a5 a6.
  Proof.
    induct bs; simplify; eauto.
    eapply IHbs.
  Qed.
  
  Lemma swap_lift4_2_3_4 :
    forall bs T A1 A2 A3 A4 (f1 : A1 -> A2 -> A3 -> A4 -> T) (f2 : A1 -> A4 -> A2 -> A3 -> T) a1 a2 a3 a4,
      (forall a1 a2 a3 a4, f1 a1 a2 a3 a4 = f2 a1 a4 a2 a3) ->
      lift4 bs f1 a1 a2 a3 a4 = lift4 bs f2 a1 a4 a2 a3.
  Proof.
    induct bs; simpl; intros; eauto.
    eapply IHbs.
    intros.
    eapply FunctionalExtensionality.functional_extensionality.
    eauto.
  Qed.
  
  Lemma subst_lift3 : forall bs x A1 A2 A3 B b_v (v : interp_bsorts (skipn (S x) bs) (interp_bsort b_v)) (f : A1 -> A2 -> A3 -> B) a1 a2 a3, subst x bs v (lift3 bs f a1 a2 a3) = lift3 (removen x bs) f (subst x bs v a1) (subst x bs v a2) (subst x bs v a3).
  Proof.
    induct bs; cbn in *; intros; eauto.
    destruct x; cbn in *; intros.
    {
      rewrite !fuse_lift3_lift2_1.
      rewrite fuse_lift4_lift2_3_4.
      rewrite dedup_lift6_2_4.
      rewrite dedup_lift5_2_5.
      rewrite fuse_lift2_lift3_1.
      erewrite swap_lift4_2_3_4; eauto.
    }
    {
      eauto.
    }
  Qed.

  Lemma forall_subst_i_i_iff_subst :
    forall body x bs v b_v b_b,
      let bs' := removen x bs in
      nth_error bs x = Some b_v ->
      bsorting (skipn (S x) bs) v b_v ->
      bsorting bs body b_b ->
      forall_ bs' (lift2 bs' eq (interp_idx (subst_i_i x (shift_i_i x 0 v) body) bs' b_b) (subst x bs (interp_idx v (skipn (S x) bs) b_v) (interp_idx body bs b_b))).
  Proof.
    simpl.
    induct body; try rename x into y; intros x bs v b_v b_b Hx Hv Hbody.
    {
      simpl.
      copy Hx Hcmp.
      eapply nth_error_Some_lt in Hcmp.
      cases (y <=>? x); simpl in *.
      {
        eapply forall_interp_var_eq_subst_lt; eauto.
      }
      {
        subst.
        invert Hbody.
        rewrite Hx in H1.
        symmetry in H1.
        invert H1.
          
        eapply forall_eq_trans.
        Focus 2.
        {
          eapply forall_interp_var_eq_subst; eauto.
        }
        Unfocus.
        {
          eapply forall_cast_elim with (bs2 := firstn x bs ++ skipn (S x) bs).
            
          rewrite cast_lift2.
          rewrite cast_interp_idx.
          eapply forall_eq_trans.
          {
            eapply forall_shift_i_i_iff_shift with (x := 0); eauto.
            {
              eapply bsorting_wellscoped_i; eauto.
            }
            {
              rewrite length_firstn_le by la.
              eauto.
            }
          }
          rewrite cast_roundtrip.
          rewrite dedup_lift2.
          eapply forall_lift1.
          eauto.
        }
      }
      {
        eapply forall_interp_var_eq_subst_gt; eauto.
      }
    }
    {
      simpl.
      cases cn; simpl in *;
      rewrite subst_lift0;
      rewrite fuse_lift2_lift0_1;
      rewrite fuse_lift1_lift0;
      eapply forall_lift0; eauto.
    }
    {
      simpl.
      eapply bsorting_IUnOp_invert in Hbody; openhyp.
      rewrite fuse_lift2_lift1_1.
      rewrite subst_lift1.
      rewrite fuse_lift2_lift1_2.
      eapply forall_lift2_lift2; eauto.
      simpl; intros; subst.
      propositional.
    }
    {
      simpl.
      invert Hbody.
      rewrite fuse_lift2_lift2_1.
      rewrite subst_lift2.
      rewrite fuse_lift3_lift2_3.
      eapply forall_lift2_lift2_lift4; eauto.
      simpl; intros; subst.
      destruct opr; simpl; propositional.
    }
    {
      simpl.
      invert Hbody.
      rewrite subst_lift3.
      rewrite fuse_lift2_lift3_1.
      rewrite fuse_lift4_lift3_4.
      specialize (IHbody1 x bs v b_v BSBool).
      eapply forall_lift2_lift2_lift2_lift6; eauto.
      simpl; intros; subst.
      unfold ite; simpl; propositional.
    }
    {
      simpl.
      invert Hbody.
      simpl.
      specialize (IHbody (S x) (BSNat :: bs) v b_v (BSTimeFun n)).
      simpl in *.
      rewrite fuse_lift1_lift2 in *.
      rewrite shift0_i_i_shift_0.
      eapply forall_lift2_lift2; [ | eapply IHbody; eauto].
      simpl; intros.
      eapply FunctionalExtensionality.functional_extensionality.
      eauto.
    }
    {
      simpl.
      invert Hbody.
      rewrite fuse_lift2_lift2_1.
      rewrite subst_lift2.
      rewrite fuse_lift3_lift2_3.
      specialize (IHbody1 x bs v b_v (BSTimeFun (S arity))).
      specialize (IHbody2 x bs v b_v BSNat).
      simpl in *.
      eapply forall_lift2_lift2_lift4; eauto.
      simpl; intros; subst.
      simpl; propositional.
    }
    Grab Existential Variables.
    {
      rewrite <- removen_firstn_skipn.
      eauto.
    }
    {
      rewrite <- removen_firstn_skipn.
      eauto.
    }
  Qed.

  Lemma forall_subst_i_p_iff_subst :
    forall p x bs v b_v,
      let bs' := removen x bs in
      nth_error bs x = Some b_v ->
      bsorting (skipn (S x) bs) v b_v ->
      bwfprop bs p ->
      forall_ bs' (lift2 bs' iff (interp_p bs' (subst_i_p x (shift_i_i x 0 v) p)) (subst x bs (interp_idx v (skipn (S x) bs) b_v) (interp_p bs p))).
  Proof.
    simpl.
    induct p; simpl; intros x bs v b_v Hx Hv Hp; invert Hp.
    {
      rewrite fuse_lift2_lift0_1.
      rewrite subst_lift0.
      rewrite fuse_lift1_lift0.
      eapply forall_lift0.
      propositional.
    }
    {
      rewrite subst_lift2.
      rewrite fuse_lift2_lift2_1.
      rewrite fuse_lift3_lift2_3.
      eapply forall_lift2_lift2_lift4; eauto.
      simpl; intros.
      destruct opr; simpl; propositional.
    }
    {
      rewrite subst_lift1.
      rewrite fuse_lift2_lift1_1.
      rewrite fuse_lift2_lift1_2.
      eapply forall_lift2_lift2; eauto.
      simpl; intros.
      propositional.
    }
    {
      rewrite subst_lift2.
      rewrite fuse_lift2_lift2_1.
      rewrite fuse_lift3_lift2_3.
      eapply forall_lift2_lift2_lift4; try eapply forall_subst_i_i_iff_subst; eauto.
      intros; subst.
      propositional.
    }
    {
      rewrite subst_lift2.
      rewrite fuse_lift2_lift2_1.
      rewrite fuse_lift3_lift2_3.
      eapply forall_lift2_lift2_lift4; try eapply forall_subst_i_i_iff_subst; eauto.
      intros; subst.
      propositional.
    }
    {
      rename b into bsort.
      rewrite fuse_lift2_lift1_1.
      rewrite subst_lift1.
      rewrite fuse_lift2_lift1_2.
      rewrite shift0_i_i_shift_0.
      specialize (IHp (S x) (bsort :: bs) v b_v); simpl in *.
      rewrite fuse_lift1_lift2 in *.
      eapply forall_lift2_lift2; eauto.
      simpl; intros.
      destruct q; simpl; intuition eauto.
      {
        eapply H; eauto.
      }
      {
        eapply H; eauto.
      }
      {
        openhyp; eexists.
        eapply H; eauto.
      }
      {
        openhyp; eexists.
        eapply H; eauto.
      }
    }
  Qed.
  
  Lemma forall_lift1_lift2 :
    forall bs A1 A2 P1 P2 (f1 : A1 -> Prop) (f2 : A1 -> A2 -> Prop),
      (forall a1 a2, f1 a1 -> f2 a1 a2) ->
      forall_ bs (lift1 bs f1 P1) ->
      forall_ bs (lift2 bs f2 P1 P2).
  Proof.
    induct bs; simplify; eauto.
    rewrite fuse_lift1_lift2 in *.
    rewrite fuse_lift1_lift1 in *.
    eapply IHbs; eauto.
    simplify.
    eauto.
  Qed.
  
  Lemma map_skipn A B (f : A -> B) ls :
    forall n,
      map f (skipn n ls) = skipn n (map f ls).
  Proof.
    induction ls; destruct n; simplify; eauto.
  Qed.

  Lemma forall_subst :
    forall bs x b_v v p,
      forall_ bs p ->
      forall_ (removen x bs) (subst x bs (b_v := b_v) v p).
  Proof.
    induct bs; cbn in *; intros; eauto.
    destruct x; cbn in *.
    {
      eapply forall_lift1_lift2; eauto.
      simpl; eauto.
    }
    {
      rewrite <- subst_lift1.
      eauto.
    }
  Qed.
  
  Lemma forall_subst_i_p_intro bs x b_v v p :
    forall_ bs (interp_p bs p) ->
    nth_error bs x = Some b_v ->
    bsorting (skipn (S x) bs) v b_v ->
    bwfprop bs p ->
    let bs' := removen x bs in
    forall_ bs' (interp_p bs' (subst_i_p x (shift_i_i x 0 v) p)).
  Proof.
    simpl.
    intros H Hx Hv Hp.
    eapply forall_iff_elim.
    Focus 2.
    {
      eapply forall_iff_sym.
      eapply forall_subst_i_p_iff_subst; eauto.
    }
    Unfocus.
    eapply forall_subst; eauto.
  Qed.
  
  Lemma forall_subst_i_p_intro_imply bs x b_v v p1 p2 :
    forall_ bs (lift2 bs imply (interp_p bs p1) (interp_p bs p2)) ->
    nth_error bs x = Some b_v ->
    bsorting (skipn (S x) bs) v b_v ->
    bwfprop bs p1 ->
    bwfprop bs p2 ->
    let bs' := removen x bs in
    forall_ bs' (lift2 bs' imply (interp_p bs' (subst_i_p x (shift_i_i x 0 v) p1)) (interp_p bs' (subst_i_p x (shift_i_i x 0 v) p2))).
  Proof.
    simpl; intros.
    eapply forall_subst_i_p_intro with (p := (p1 ===> p2)%idx); eauto.
    econstructor; eauto.
  Qed.

  Lemma wellscoped_subst_i_i :
    forall L b,
        wellscoped_i L b ->
        forall x v L',
          x < L ->
          wellscoped_i (L - (1 + x)) v ->
          L' = L - 1 ->
          wellscoped_i L' (subst_i_i x (shift_i_i x 0 v) b).
  Proof.
    induct 1;
      simpl; try rename x into y; intros x v ? Hx Hv ?; subst; try solve [econstructor; eauto].
    {
      (* Case Var *)
      cases (y <=>? x); eauto with db_la.
      eapply wellscoped_shift_i_i; eauto with db_la.
    }
    {
      (* Case TimeAbs *)
      rewrite shift0_i_i_shift_0.
      econstructor; eauto with db_la.
    }
  Qed.
  
  Lemma wellscoped_subst_i_p :
    forall L b,
        wellscoped_p L b ->
        forall x v L',
          x < L ->
          wellscoped_i (L - (1 + x)) v ->
          L' = L - 1 ->
          wellscoped_p L' (subst_i_p x (shift_i_i x 0 v) b).
  Proof.
    induct 1;
      simpl; intros x v ? Hx Hv ?; subst; try solve [econstructor; eauto using wellscoped_subst_i_i with db_la].
    rewrite shift0_i_i_shift_0.
    econstructor; eauto with db_la.
  Qed.
  
  Lemma wellscoped_subst_i_p_0 L b v :
    wellscoped_p (S L) b ->
    wellscoped_i L v ->
    wellscoped_p L (subst_i_p 0 v b).
  Proof.
    intros Hb Hv.
    eapply wellscoped_subst_i_p with (x := 0) (v := v) in Hb; eauto with db_la; simpl in *; try rewrite Nat.sub_0_r in *; eauto.
    rewrite shift_i_i_0 in *.
    eauto.
  Qed.
  
  Lemma length_my_skipn_le A (L : list A) n :
    n <= length L ->
    length (my_skipn L n) = length L - n.
  Proof.
    intros.
    symmetry.
    rewrite <- (firstn_my_skipn n) at 1.
    rewrite app_length.
    rewrite length_firstn_le by la.
    la.
  Qed.

  Lemma bsorting_shift_i_i :
    forall L c s,
      bsorting L c s ->
      forall x ls,
        let n := length ls in
        x <= length L ->
        bsorting (firstn x L ++ ls ++ my_skipn L x) (shift_i_i n x c) s.
  Proof.
    simpl.
    induct 1;
      simpl; try rename x into y; intros x ls Hx; cbn in *; try solve [econstructor; eauto].
    {
      (* Case Var *)
      copy H HnltL.
      eapply nth_error_Some_lt in HnltL.
      cases (x <=? y).
      {
        eapply BStgVar.
        {
          rewrite nth_error_app2;
          erewrite length_firstn_le; try la.
          rewrite nth_error_app2 by la.
          rewrite nth_error_my_skipn by la.
          erewrite <- H.
          f_equal.
          la.
        }
      }
      {
        eapply BStgVar.
        {
          rewrite nth_error_app1;
          try erewrite length_firstn_le; try la.
          rewrite nth_error_firstn; eauto.
        }          
      }
    }
    {
      (* Case TimeAbs *)
      econstructor; eauto.
      {
        eapply IHbsorting with (x := S x); eauto with db_la.
      }
    }
  Qed.

  Lemma bwfprop_shift_i_p :
    forall L p,
      bwfprop L p ->
      forall x ls,
        let n := length ls in
        x <= length L ->
        bwfprop (firstn x L ++ ls ++ my_skipn L x) (shift_i_p n x p).
  Proof.
    simpl.
    induct 1;
      simpl; intros x ls Hx; cbn in *; try solve [econstructor; eauto using bsorting_shift_i_i].
    econstructor.
    eapply IHbwfprop with (x := S x); eauto with db_la.
  Qed.
  
  Lemma bwfprop_shift_i_p_1_0 L p s :
    bwfprop L p ->
    bwfprop (s :: L) (shift_i_p 1 0 p).
  Proof.
    intros Hp.
    eapply bwfprop_shift_i_p with (x := 0) (ls := [s]) in Hp; eauto with db_la.
    simpl in *.
    rewrite my_skipn_0 in *.
    eauto.
  Qed.
  
  Inductive bwfsort : list bsort -> sort -> Prop :=
  | BWfStBaseSort L b :
      bwfsort L (SBaseSort b)
  | BWfStSubset L b p :
      bwfprop (b :: L) p ->
      bwfsort L (SSubset b p)
  .

  Hint Constructors bwfsort.

  Definition bwfsorts := all_sorts (fun L s => bwfsort (map get_bsort L) s).

  Lemma bwfsorts_bwfprop_strip_subsets L :
    bwfsorts L ->
    forall n,
      n = length L ->
      bwfprop (map get_bsort L) (and_all (strip_subsets L)).
  Proof.
    induct 1; simpl; intros n ?; subst; eauto.
    {
      econstructor.
    }
    rename H0 into Hwfsort.
    invert Hwfsort; simpl in *.
    {
      unfold shift0_i_p.
      rewrite and_all_map_shift_i_p.
      eapply bwfprop_shift_i_p_1_0; eauto.
    }
    {
      unfold shift0_i_p.
      rewrite and_all_map_shift_i_p.
      econstructor; eauto.
      eapply bwfprop_shift_i_p_1_0; eauto.
    }
  Qed.

  Lemma and_all_map_subst_i_p x v ls :
    and_all (map (subst_i_p x v) ls) = subst_i_p x v (and_all ls).
  Proof.
    induct ls; simpl; eauto.
    rewrite IHls; eauto.
  Qed.

  Lemma nth_error_split_firstn_skipn A :
    forall (ls : list A) n a,
      nth_error ls n = Some a ->
      ls = firstn n ls ++ a :: skipn (S n) ls.
  Proof.
    induct ls; destruct n; simpl; intros; f_equal; eauto; try discriminate.
    congruence.
  Qed.      

  Lemma strip_subsets_subst_i_ss :
    forall L v n,
      n = length L ->
      strip_subsets (subst_i_ss v L) = map (subst_i_p n (shift_i_i n 0 v)) (strip_subsets L).
  Proof.
    induct L; simpl; intros; subst; eauto.
    unfold shift0_i_p.
    destruct a; simpl.
    {
      erewrite IHL; eauto.
      repeat rewrite map_map.
      eapply map_ext.
      intros body.
      rewrite shift_i_p_subst_in by la.
      rewrite shift_i_i_shift_merge by la.
      f_equal; try la.
      f_equal; try la.
    }
    {
      f_equal.
      {
        unfold shift0_i_i.
        rewrite shift_i_i_shift_merge by la.
        f_equal; try la.
        f_equal; try la.
      }
      erewrite IHL; eauto.
      repeat rewrite map_map.
      eapply map_ext.
      intros body.
      rewrite shift_i_p_subst_in by la.
      rewrite shift_i_i_shift_merge by la.
      f_equal; try la.
      f_equal; try la.
    }
  Qed.

  Definition imply_ bs x y := forall_ bs (lift2 bs imply x y).
  
  Lemma forall_replace_imply bs p1 p2 p1' p2' :
    iff_ bs p1 p1' ->
    iff_ bs p2 p2' ->
    imply_ bs p1 p2 ->
    imply_ bs p1' p2'.
  Proof.
    intros.
    eapply forall_iff_elim.
    Focus 2.
    {
      eapply forall_iff_iff_imply; eauto.
    }
    Unfocus.
    eauto.
  Qed.

  Lemma shift_i_p_subst_in_2 n :
    forall b v x y x',
      y <= x ->
      x' = x + n ->
      shift_i_p n y (subst_i_p x v b) = subst_i_p x' (shift_i_i n y v) (shift_i_p n y b).
  Proof.
    intros; subst; rewrite shift_i_p_subst_in by la; eauto.
  Qed.
  
  Lemma forall_imply_refl bs p :
    imply_ bs p p.
  Proof.
    eapply forall_iff_imply.
    eapply forall_iff_refl.
  Qed.

  Lemma forall_subst_i_p_iff_subst_0 :
    forall p bs' v b_v,
      let bs := b_v :: bs' in
      bsorting bs' v b_v ->
      bwfprop bs p ->
      forall_ bs' (lift2 bs' iff (interp_p bs' (subst_i_p 0 v p)) (subst 0 bs (interp_idx v bs' b_v) (interp_p bs p))).
  Proof.
    simpl; intros.
    specialize (@forall_subst_i_p_iff_subst p 0 (b_v :: bs') v b_v); intros Hsubst.
    simpl in *.
    rewrite shift_i_i_0 in *.
    eauto.
  Qed.
  
  Lemma fuse_lift3_lift3_3 bs :
    forall T A1 A2 A3 B1 B2 B3 (f : A1 -> A2 -> A3 -> T) (g : B1 -> B2 -> B3 -> A3) a1 a2 b1 b2 b3,
      lift3 bs f a1 a2 (lift3 bs g b1 b2 b3) = lift5 bs (fun a1 a2 b1 b2 b3 => f a1 a2 (g b1 b2 b3)) a1 a2 b1 b2 b3.
  Proof.
    induct bs; simplify; eauto.
    eapply IHbs.
  Qed.
  
  Lemma fuse_lift1_lift5 bs :
    forall T A1 B1 B2 B3 B4 B5 (f : A1 -> T) (g : B1 -> B2 -> B3 -> B4 -> B5 -> A1) b1 b2 b3 b4 b5,
      lift1 bs f (lift5 bs g b1 b2 b3 b4 b5) = lift5 bs (fun b1 b2 b3 b4 b5 => f (g b1 b2 b3 b4 b5)) b1 b2 b3 b4 b5.
  Proof.
    induct bs; simplify; eauto.
    eapply IHbs.
  Qed.
  
  Lemma forall_lift3_lift3_lift5 :
    forall bs A1 A2 A3 A4 A5 P1 P2 P3 P4 P5 (f1 : A1 -> A2 -> A4 -> Prop) (f2 : A1 -> A2 -> A5 -> Prop) (f3 : A1 -> A2 -> A3 -> A4 -> A5 -> Prop),
      (forall a1 a2 a3 a4 a5, f1 a1 a2 a4 -> f2 a1 a2 a5 -> f3 a1 a2 a3 a4 a5) ->
      forall_ bs (lift3 bs f1 P1 P2 P4) ->
      forall_ bs (lift3 bs f2 P1 P2 P5) ->
      forall_ bs (lift5 bs f3 P1 P2 P3 P4 P5).
  Proof.
    induct bs; simplify; eauto.
    rewrite fuse_lift1_lift3 in *.
    rewrite fuse_lift1_lift5 in *.
    eapply IHbs; eauto.
    simplify.
    eauto.
  Qed.
  
  Lemma forall_lift2_lift3_1_3 :
    forall bs A1 A2 A3 P1 P2 P3 (f1 : A1 -> A3 -> Prop) (f2 : A1 -> A2 -> A3 -> Prop),
      (forall a1 a2 a3, f1 a1 a3 -> f2 a1 a2 a3) ->
      forall_ bs (lift2 bs f1 P1 P3) ->
      forall_ bs (lift3 bs f2 P1 P2 P3).
  Proof.
    induct bs; simplify; eauto.
    rewrite fuse_lift1_lift2 in *.
    rewrite fuse_lift1_lift3 in *.
    eapply IHbs; eauto.
    simplify.
    eauto.
  Qed.
  
  Lemma forall_and_elim_left_imply bs p1 p2 p :
    imply_ bs p1 p ->
    imply_ bs (lift2 bs and p1 p2) p.
  Proof.
    intros H.
    unfold imply_ in *.
    rewrite fuse_lift2_lift2_1.
    eapply forall_lift2_lift3_1_3; eauto.
    unfold imply_; propositional.
  Qed.
  
  Lemma forall_lift2_lift3_2_3 :
    forall bs A1 A2 A3 P1 P2 P3 (f1 : A2 -> A3 -> Prop) (f2 : A1 -> A2 -> A3 -> Prop),
      (forall a1 a2 a3, f1 a2 a3 -> f2 a1 a2 a3) ->
      forall_ bs (lift2 bs f1 P2 P3) ->
      forall_ bs (lift3 bs f2 P1 P2 P3).
  Proof.
    induct bs; simplify; eauto.
    rewrite fuse_lift1_lift2 in *.
    rewrite fuse_lift1_lift3 in *.
    eapply IHbs; eauto.
    simplify.
    eauto.
  Qed.
  
  Lemma forall_and_elim_right_imply bs p1 p2 p :
    imply_ bs p2 p ->
    imply_ bs (lift2 bs and p1 p2) p.
  Proof.
    intros H.
    unfold imply_ in *.
    rewrite fuse_lift2_lift2_1.
    eapply forall_lift2_lift3_2_3; eauto.
    unfold imply_; propositional.
  Qed.

  Lemma forall_imply_shift_i_p_imply bs p1 p2 bs_new x n :
    imply_ bs (interp_p bs p1) (interp_p bs p2) ->
    wellscoped_p (length bs) p1 ->
    wellscoped_p (length bs) p2 ->
    let bs' := insert bs_new x bs in
    n = length bs_new ->
    imply_ bs' (interp_p bs' (shift_i_p n x p1)) (interp_p bs' (shift_i_p n x p2)).
  Proof.
    simpl; intros H Hp1 Hp2 ?; subst.
    eapply forall_replace_imply.
    {
      eapply forall_iff_sym.
      eapply forall_shift_i_p_iff_shift; eauto.
    }
    {
      eapply forall_iff_sym.
      eapply forall_shift_i_p_iff_shift; eauto.
    }
    unfold imply_.
    rewrite lift2_shift.
    eapply forall_shift.
    eauto.
  Qed.

  Lemma skipn_removen A : forall (ls : list A) n, skipn n (removen n ls) = skipn (S n) ls.
  Proof.
    induct ls; destruct n; simpl; eauto.
  Qed.
  
  Lemma length_removen_lt A :
    forall (ls : list A) x,
      x < length ls ->
      length (removen x ls) = length ls - 1.
  Proof.
    induct ls; destruct x; simpl; intros Hcmp; eauto with db_la.
    rewrite IHls by la.
    la.
  Qed.
  
  Lemma all_sorts_nth_error_Some f :
    forall n L s,
      all_sorts f L ->
      nth_error L n = Some s ->
      f (skipn (S n) L) s.
  Proof.
    induct n; destruct L; simpl; intros s' H Hnth; try discriminate; invert H; eauto.
    invert Hnth.
    eauto.
  Qed.

  Lemma all_sorts_skipn f :
    forall n L,
      all_sorts f L ->
      all_sorts f (skipn n L).
  Proof.
    induct n; destruct L; simpl; intros H; invert H; eauto.
  Qed.

  Ltac dis := discriminate.
  
  Lemma nth_error_0_my_skipn_1 A ls (a : A) :
    nth_error ls 0 = Some a ->
    ls = a :: my_skipn ls 1.
  Proof.
    destruct ls; simpl in *; try dis; intros H.
    invert H.
    rewrite my_skipn_0.
    eauto.
  Qed.

  Lemma nth_error_Some_my_skipn A bs x (b : A) :
    nth_error bs x = Some b ->
    let bs' := my_skipn bs x in
    bs' = b :: my_skipn bs' 1.
  Proof.
    intros Hnth; intros.
    copy Hnth Hcmp.
    eapply nth_error_Some_lt in Hcmp.
    assert (Hnth'' : nth_error bs' 0 = Some b).
    {
      unfold bs'.
      rewrite nth_error_my_skipn by la.
      rewrite Nat.add_0_r.
      eauto.
    }
    eapply nth_error_0_my_skipn_1; eauto.
  Qed.
  
  Ltac cases_le_dec :=
    match goal with
      H : context [?a <=? ?b] |- _ => cases (a <=? b)
    end.
  
  Lemma bsorting_shift_i_i_rev :
    forall L i b,
      bsorting L i b ->
      forall n x i' L1 L2 L3,
        i = shift_i_i n x i' ->
        L = L1 ++ L2 ++ L3 ->
        x = length L1 ->
        n = length L2 ->
        bsorting (L1 ++ L3) i' b.
  Proof.
    induct 1;
      simpl; intros ? ? i' L1 L2 L3 Hi; intros; subst; cbn in *;
        try solve [
              destruct i'; simpl in *; try cases_le_dec; try dis;
              invert Hi; eauto
            ].
    {
      (* Case Var *)
      destruct i'; simpl in *; try dis.
      rename x0 into y.
      econstructor.
      cases (length L1 <=? y).
      {
        invert Hi.
        repeat rewrite nth_error_app2 in * by la.
        rewrite <- H.
        f_equal.
        la.
      }
      {
        invert Hi.
        repeat rewrite nth_error_app1 in * by la.
        eauto.
      }
    }
    {
      destruct i'; simpl in *; try cases_le_dec; try dis.
      assert (opr = opr0).
      {
        congruence.
      }
      invert Hi; eauto.
    }
    {
      (* Case TimeAbs *)
      destruct i'; simpl in *; try cases_le_dec; try dis.
      invert Hi; eauto.
      econstructor; eauto.
      eapply IHbsorting with (L4 := _ :: _); eauto with db_la.
      eauto.
    }
  Qed.

  Lemma bwfprop_shift_i_p_rev :
    forall L p,
      bwfprop L p ->
      forall n x p' L1 L2 L3,
        p = shift_i_p n x p' ->
        L = L1 ++ L2 ++ L3 ->
        x = length L1 ->
        n = length L2 ->
        bwfprop (L1 ++ L3) p'.
  Proof.
    induct 1;
      simpl; intros ? ? p' L1 L2 L3 Hp; intros; subst; cbn in *;
        try solve [
              destruct p'; simpl in *; try cases_le_dec; try dis;
              invert Hp; eauto using bsorting_shift_i_i_rev
            ].
    destruct p'; simpl in *; try cases_le_dec; try dis;
      invert Hp; eauto.
    econstructor; eauto.
    eapply IHbwfprop with (L4 := _ :: _); eauto with db_la.
    eauto.
  Qed.    
  
  Lemma my_skipn_my_skipn A :
    forall (ls : list A) n2 n1,
      my_skipn (my_skipn ls n2) n1 = my_skipn ls (n2 + n1).
  Proof.
    induct ls; destruct n2; simpl; eauto.
  Qed.

  Lemma bwfsort_wellscoped_s L s :
    bwfsort L s ->
    wellscoped_s (length L) s.
  Proof.
    induct 1; simpl; econstructor; eauto.
    eapply bwfprop_wellscoped_p in H.
    eauto.
  Qed.
  
  Lemma bwfsorts_wellscoped_ss L :
    bwfsorts L ->
    wellscoped_ss L.
  Proof.
    induct 1; simpl; intros; econstructor; eauto using bwfsort_wellscoped_s.
    eapply bwfsort_wellscoped_s in H0.
    rewrite map_length in *.
    eauto.
  Qed.

  Lemma forall_imply_shift_i_p_1_1_var0 b bs' bs p :
    wellscoped_p (1 + length bs') p ->
    bs = b :: bs' ->
    imply_ bs (interp_p bs p) (lift2 bs (fun body v => body (convert_sort_value b b v)) (interp_p (b :: bs) (shift_i_p 1 1 p)) (interp_var 0 bs b)).
  Proof.
    intros Hp ?; subst.
    unfold imply_.
    simpl.
    rewrite fuse_lift1_lift2.
    rewrite fuse_lift2_lift0_2.
    specialize (@forall_shift_i_p_iff_shift p [b] 1 (b :: bs') 1); intros Hshift.
    simpl in *.
    rewrite fuse_lift1_lift1 in *.
    rewrite fuse_lift1_lift2 in *.
    rewrite fuse_lift2_lift1_2 in *.
    rewrite swap_lift2.
    eapply forall_lift2_lift2; [|eapply Hshift; eauto].
    unfold swap; simpl.
    intros.
    repeat rewrite convert_sort_value_refl_eq.
    specialize (H a0 a0).
    propositional.
    (* Anomaly: conversion was given ill-typed terms (FProd). Please report. *)
    (* Qed. *)
  Admitted.

  Lemma nth_error_Some_interp_prop_subst_i_p_var L x b p :
    nth_error L x = Some (SSubset b p) ->
    bwfprop (my_skipn (map get_bsort L) x) p ->
    interp_prop L (subst_i_p 0 (IVar x) (shift_i_p (S x) 1 p)).
  Proof.
    intros Hnth Hp.
    copy Hnth Hcmp.
    eapply nth_error_Some_lt in Hcmp.
    replace (subst_i_p 0 (IVar x) (shift_i_p (S x) 1 p)) with (shift_i_p x 0 (subst_i_p 0 (IVar 0) (shift_i_p 1 1 p))).
    Focus 2.
    {
      rewrite shift_i_p_subst_out by la.
      rewrite shift_i_p_shift_merge by la.
      simpl.
      rewrite Nat.add_0_r.
      eauto.
    }
    Unfocus.
    
    unfold interp_prop.
    simpl.
    set (bs := map get_bsort L) in *.
    assert (Hcmp' : x < length bs).
    {
      subst bs.
      rewrite map_length; eauto.
    }
    
    erewrite (nth_error_split_firstn_skipn L) at 1 by eauto.
    rewrite strip_subsets_app.
    Opaque skipn.
    simpl.
    Transparent skipn.
    rewrite length_firstn_le by la.
    repeat rewrite map_app.
    repeat rewrite map_map.
    eapply forall_replace_imply.
    {
      eapply forall_iff_sym.
      eapply and_all_app_iff.
    }
    {
      eapply forall_iff_refl.
    }
    Opaque skipn.
    simpl.
    Transparent skipn.
    unfold imply_.

    set (p' := shift_i_p x 0 p) in *.
    eapply forall_trans with (P2 := interp_p _ p').
    {
      eapply forall_and_elim_right_imply.
      eapply forall_and_elim_left_imply.
      eapply forall_imply_refl.
    }

    subst p'.
    rewrite <- (firstn_my_skipn x bs).
    
    set (bs' := my_skipn bs x) in *.
    assert (Hbs' : bs' = b :: my_skipn bs' 1).
    {
      eapply nth_error_Some_my_skipn; eauto.
      unfold bs.
      erewrite map_nth_error; eauto.
      eauto.
    }
    
    eapply forall_imply_shift_i_p_imply with (x := 0).
    Focus 2.
    {
      eapply bwfprop_wellscoped_p; eauto.
    }
    Unfocus.
    Focus 2.
    {
      eapply wellscoped_subst_i_p_0.
      {
        eapply wellscoped_shift_i_p; eauto.
        eapply bwfprop_wellscoped_p; eauto.
      }
      {
        rewrite Hbs'.
        econstructor; simpl; la.
      }
    }
    Unfocus.
    Focus 2.
    {
      rewrite length_firstn_le by la.
      eauto.
    }
    Unfocus.
    {
      eapply forall_replace_imply; [eapply forall_iff_refl | |].
      {
        eapply forall_iff_sym.
        eapply forall_subst_i_p_iff_subst_0 with (b_v := b); eauto.
        {
          econstructor.
          rewrite Hbs'.
          eauto.
        }
        {
          rewrite Hbs'.
          rewrite Hbs' in Hp.
          eapply bwfprop_shift_i_p with (ls := [b]) (x := 1) in Hp; simpl; eauto with db_la.
          simpl in *.
          rewrite my_skipn_0 in *.
          eauto.
        }
      }
      simpl.

      eapply forall_imply_shift_i_p_1_1_var0; eauto.
      rewrite Hbs' in Hp.
      eapply bwfprop_wellscoped_p in Hp; eauto.
    }
  Qed.
  
  Definition monotone : idx -> Prop.
  Admitted.

  Inductive sorting : sctx -> idx -> sort -> Prop :=
  | StgVar L x s :
      nth_error L x = Some s ->
      sorting L (IVar x) (shift_i_s (1 + x) 0 s)
  | StgConst L cn :
      sorting L (IConst cn) (SBaseSort (const_bsort cn))
  | StgUnOp L opr c :
      sorting L c (SBaseSort (iunop_arg_bsort opr)) ->
      sorting L (IUnOp opr c) (SBaseSort (iunop_result_bsort opr))
  | StgBinOp L opr c1 c2 :
      sorting L c1 (SBaseSort (ibinop_arg1_bsort opr)) ->
      sorting L c2 (SBaseSort (ibinop_arg2_bsort opr)) ->
      sorting L (IBinOp opr c1 c2) (SBaseSort (ibinop_result_bsort opr))
  | StgIte L c c1 c2 s :
      sorting L c SBool ->
      sorting L c1 s ->
      sorting L c2 s ->
      sorting L (IIte c c1 c2) s
  | StgTimeAbs L i n :
      sorting (SNat :: L) i (STimeFun n) ->
      monotone i ->
      sorting L (ITimeAbs i) (STimeFun (1 + n))
  | StgTimeApp L c1 c2 n :
      sorting L c1 (STimeFun (S n)) ->
      sorting L c2 SNat ->
      sorting L (ITimeApp n c1 c2) (STimeFun n)
  | StgSubsetI L c b p :
      sorting L c (SBaseSort b) ->
      (* wellscoped_p (1 + length L) p -> *)
      interp_prop L (subst0_i_p c p) ->
      sorting L c (SSubset b p)
  | StgSubsetE L c b p :
      sorting L c (SSubset b p) ->
      wellscoped_p (1 + length L) p ->
      sorting L c (SBaseSort b)
  .

  Hint Constructors sorting.
  
  Lemma StgVar' L x s s' :
    nth_error L x = Some s ->
    s' = shift_i_s (1 + x) 0 s ->
    sorting L (IVar x) s'.
  Proof.
    intros; subst; eauto.
  Qed.
  
  Lemma sorting_bsorting L i s :
    sorting L i s ->
    bsorting (map get_bsort L) i (get_bsort s).
  Proof.
    induct 1; simpl; eauto.
    econstructor.
    rewrite get_bsort_shift_i_s.
    erewrite map_nth_error; eauto.
  Qed.
  
  Lemma sorting_bsorting' L i s b :
    sorting L i s ->
    b = get_bsort s ->
    bsorting (map get_bsort L) i b.
  Proof.
    intros; subst; eapply sorting_bsorting; eauto.
  Qed.
  
  Lemma sorting_wellscoped_i L i s :
    sorting L i s ->
    wellscoped_i (length L) i.
  Proof.
    induct 1; simpl; eauto.
    econstructor.
    eapply nth_error_Some_lt; eauto.
  Qed.
  
  Lemma sorting_Subset_elim L i s :
    sorting L i s ->
    forall b p,
      s = SSubset b p ->
      bwfprop (b :: map get_bsort L) p ->
      interp_prop L (subst_i_p 0 i p).
  Proof.
    induct 1; simpl; try rename b into b'; try rename p into p'; intros b p Hs Hp; subst; eauto; try discriminate.
    {
      (* Case Var *)
      destruct s; simpl in *; try discriminate.
      invert Hs.
      rename H into Hnth.
      copy Hnth Hcmp.
      eapply nth_error_Some_lt in Hcmp.
      rename p0 into p.

      eapply nth_error_Some_interp_prop_subst_i_p_var; eauto.
      erewrite (nth_error_split_firstn_skipn L x) in Hp by eauto.
      rewrite map_app in *.
      rewrite skipn_my_skipn in *.
      simpl in *.
      eapply bwfprop_shift_i_p_rev with (L1 := [b]) (L2 := map get_bsort (firstn x L) ++ [b]) (L3 := map get_bsort (my_skipn L (S x))) in Hp; simpl; eauto.
      {
        simpl in *.
        rewrite <- map_my_skipn.
        erewrite nth_error_Some_my_skipn by eauto.
        simpl.
        rewrite my_skipn_my_skipn.
        rewrite plus_comm.
        eauto.
      }
      {
        rewrite <- app_assoc.
        eauto.
      }
      {
        rewrite app_length.
        rewrite map_length.
        rewrite length_firstn_le by la.
        simpl.
        la.
      }
    }
    {
      (* Case Ite *)
      unfold interp_prop.
      simpl.
      eapply forall_replace_imply; [eapply forall_iff_refl | |].
      {
        eapply forall_iff_sym.
        eapply forall_subst_i_p_iff_subst_0;
          eauto using sorting_bsorting.
      }
      unfold interp_prop in IHsorting2.
      simpl in IHsorting2.
      set (bs := map get_bsort L) in *.
      set (ps := interp_p bs (and_all (strip_subsets L))) in *.
      assert (IHsorting2' : imply_ bs ps (subst 0 (b :: bs) (interp_idx c1 bs b) (interp_p (b :: bs) p))).
      {
        eapply forall_replace_imply; [eapply forall_iff_refl | |].
        {
          eapply forall_subst_i_p_iff_subst_0;
          eauto.
          eapply sorting_bsorting'; eauto.
        }
        eapply IHsorting2; eauto.
      }
      assert (IHsorting3' : imply_ bs ps (subst 0 (b :: bs) (interp_idx c2 bs b) (interp_p (b :: bs) p))).
      {
        eapply forall_replace_imply; [eapply forall_iff_refl | |].
        {
          eapply forall_subst_i_p_iff_subst_0;
          eauto.
          eapply sorting_bsorting'; eauto.
        }
        eapply IHsorting3; eauto.
      }
      unfold imply_ in *.
      simpl in *.
      rewrite fuse_lift2_lift2_2 in *.
      rewrite fuse_lift3_lift3_3.
      eapply forall_lift3_lift3_lift5; eauto.
      unfold ite; intros.
      rewrite convert_sort_value_refl_eq in *.
      cases a3; eauto.
    }
    {
      invert Hs.
      eauto.
    }
  Qed.
  
  Lemma interp_prop_subst_i_p L p :
    interp_prop L p ->
    forall n s c ,
      nth_error L n = Some s ->
      sorting (my_skipn L (1 + n)) c s ->
      bwfprop (map get_bsort L) p ->
      bwfsorts L ->
      interp_prop (subst_i_ss c (firstn n L) ++ my_skipn L (1 + n)) (subst_i_p n (shift_i_i n 0 c) p).
  Proof.
    intros Hp n s c Hnth Hc Hwfp Hss.
    unfold interp_prop in *.
    simpl in *.
    copy Hnth Hn.
    eapply nth_error_Some_lt in Hn.
    rewrite !strip_subsets_app by la.
    rewrite !map_app.
    rewrite !get_bsort_subst_i_ss.

    rewrite <- !map_app.
    rewrite length_subst_i_ss.
    rewrite length_firstn_le by la.

    rewrite <- !removen_firstn_my_skipn.
    rewrite !map_removen.
    set (bs := map get_bsort L) in *.
    set (bs' := removen n bs) in *.

    rewrite <- skipn_my_skipn in *.

    set (bsort := get_bsort s) in *.
    assert (Hnth' : nth_error bs n = Some bsort).
    {
      unfold bs, bsort.
      erewrite map_nth_error; eauto.
    }
    assert (Hc' : bsorting (skipn (S n) bs) c bsort).
    {
      unfold bs, bsort.
      rewrite <- map_skipn.
      eapply sorting_bsorting; eauto.
    }
    eapply forall_subst_i_p_intro_imply in Hp; eauto.
    Focus 2.
    {
      eapply bwfsorts_bwfprop_strip_subsets; eauto.
    }
    Unfocus.
    subst bs'.
    set (bs' := removen n bs) in *.

    eapply forall_trans; [ | eassumption].
    set (c' := shift_i_i n 0 c) in *.
    rewrite <- and_all_map_subst_i_p.
    
    erewrite (nth_error_split_firstn_skipn L) at 3 by eauto.
    rewrite strip_subsets_app.
    Opaque skipn.
    simpl.
    Transparent skipn.
    repeat rewrite map_app.
    unfold shift0_i_p.
    repeat rewrite map_map.
    rewrite length_firstn_le by la.
    erewrite (map_ext (fun x => subst_i_p n c' (shift_i_p n 0 (shift_i_p 1 0 x)))).
    Focus 2.
    {
      intros b.
      rewrite shift_i_p_shift_merge by la.
      rewrite subst_i_p_shift_avoid by la.
      simpl.
      rewrite Nat.sub_0_r.
      eauto.
    }
    Unfocus.
    
    erewrite strip_subsets_subst_i_ss; eauto.
    rewrite length_firstn_le by la.
    subst c'.
    set (c' := shift_i_i n 0 c) in *.
    destruct s.
    {
      Opaque skipn.
      simpl.
      Transparent skipn.
      eapply forall_iff_imply.
      eapply forall_iff_refl.
    }
    Opaque skipn.
    simpl.
    Transparent skipn.
    eapply forall_replace_imply.
    {
      eapply forall_iff_sym.
      eapply and_all_app_iff.
    }
    {
      eapply forall_iff_sym.
      eapply and_all_app_iff.
    }
    
    Opaque skipn.
    simpl.
    Transparent skipn.
    unfold imply_.
    rewrite fuse_lift2_lift2_1.
    rewrite fuse_lift3_lift2_3.
    rewrite dedup_lift4_1_3.
    rewrite fuse_lift3_lift2_3.
    rewrite dedup_lift4_2_4.
    subst c'.
    erewrite <- (@shift_i_p_subst_in_2 _ _ _ 0) by la.
    eapply sorting_Subset_elim in Hc; eauto.
    Focus 2.
    {
      eapply all_sorts_nth_error_Some in Hnth; eauto.
      invert Hnth.
      rewrite skipn_my_skipn in *.
      simpl in *.
      eauto.
    }
    Unfocus.

    rewrite and_all_map_shift_i_p.
    unfold interp_prop in Hc.
    Opaque skipn.
    simpl in *.
    Transparent skipn.
    assert (Hc'' : imply_ bs' (interp_p bs' (shift_i_p n 0 (and_all (strip_subsets (skipn (S n) L))))) (interp_p bs' (shift_i_p n 0 (subst_i_p 0 c p0)))).
    {
      rewrite <- (firstn_my_skipn n bs').
      assert (Hskipn : my_skipn bs' n = map get_bsort (skipn (S n) L)).
      {
        subst bs'.
        subst bs.
        rewrite <- map_removen.
        rewrite <- map_my_skipn.
        f_equal.
        rewrite <- skipn_my_skipn.
        eapply skipn_removen.
      }
      rewrite Hskipn.
      assert (Hn' : n < length bs) by (subst bs; rewrite map_length; la).
      eapply forall_imply_shift_i_p_imply with (x := 0); eauto.
      {
        rewrite map_length.
        eapply wellscoped_ss_wellscoped_p_strip_subsets; eauto.
        eapply bwfsorts_wellscoped_ss.
        eapply all_sorts_skipn; eauto.
      }
      {
        rewrite map_length.
        eapply all_sorts_nth_error_Some in Hnth; eauto.
        invert Hnth.
        eapply bwfprop_wellscoped_p in H1.
        eapply bsorting_wellscoped_i in Hc'.
        rewrite skipn_my_skipn in *.
        simpl in *.
        rewrite map_length in *.
        repeat rewrite length_my_skipn_le in * by la.
        eapply wellscoped_subst_i_p_0; eauto.
        subst bs.
        rewrite map_length in *.
        eauto.
      }
      {
        rewrite length_firstn_le; eauto.
        subst bs'.
        rewrite length_removen_lt by la.
        la.
      }
    }
    eapply forall_lift2_lift3_2_3; eauto.
    intros.
    intuition.
  Qed.
  
  Lemma interp_prop_subst0_i_p s L p v :
    interp_prop (s :: L) p ->
    sorting L v s ->
    bwfprop (get_bsort s :: map get_bsort L) p ->
    bwfsorts (s :: L) ->
    interp_prop L (subst0_i_p v p).
  Proof.
    intros Hp Hv Hwfp HL.
    specialize (@interp_prop_subst_i_p (s :: L) p Hp 0 s v).
    intros H.
    simpl in *.
    rewrite my_skipn_0 in *.
    rewrite shift_i_i_0 in *.
    eapply H; eauto.
  Qed.

  Lemma bwfprop_wellscoped_p' L p n :
    bwfprop L p ->
    n = length L ->
    wellscoped_p n p.
  Proof.
    intros; subst; eapply bwfprop_wellscoped_p; eauto.
  Qed.
  
  Lemma StgEq L i s :
    sorting L i s ->
    forall s',
      sorteq L s' s ->
      bwfsorts L ->
      let bs := map get_bsort L in
      bwfsort bs s ->
      bwfsort bs s' ->
      sorting L i s'.
  Proof.
    simpl.
    induct 1; simpl; try solve [intros; eauto | induct 1; simpl in *; econstructor; eauto].
    {
      (* Case Var *)
      intros s' Heq HL Hs Hs'.
      invert Heq; simpl in *.
      {
        destruct s; simpl in *; try discriminate.
        invert H3.
        eapply StgVar'; eauto.
      }
      {
        destruct s as [ ? | b' p'']; simpl in *; try discriminate.
        symmetry in H0.
        invert H0.
        rename p'' into p'.
        eapply StgSubsetI.
        {
          eapply StgSubsetE.
          {
            eapply StgVar'; eauto.
            simpl.
            eauto.
          }
          {
            invert Hs.
            eapply bwfprop_wellscoped_p'; eauto; simpl; rewrite map_length; eauto.
          }
        }
        {
          rename H into Hnth.
          copy Hnth Hnth'.
          eapply nth_error_Some_interp_prop_subst_i_p_var in Hnth.
          Focus 2.
          {
            eapply all_sorts_nth_error_Some in Hnth; eauto.
            invert Hnth.
            rewrite skipn_my_skipn in *.
            rewrite <- map_my_skipn.
            erewrite nth_error_Some_my_skipn by eauto.
            simpl.
            rewrite my_skipn_my_skipn.
            rewrite plus_comm.
            eauto.
          }
          Unfocus.
          rename H3 into Hiff.
          eapply interp_prop_subst0_i_p with (v := IVar x) in Hiff; eauto.
          unfold subst0_i_p in *.
          {
            simpl in *.
            eapply interp_prop_iff_sym in Hiff.
            eapply interp_prop_iff_elim; eauto.
          }
          {
            eapply StgSubsetE.
            {
              eapply StgVar'; eauto.
              simpl.
              eauto.
            }
            {
              invert Hs.
              eapply bwfprop_wellscoped_p'; eauto; simpl; rewrite map_length; eauto.
            }
          }
          {
            simpl in *.
            invert Hs'.
            invert Hs.
            econstructor; eauto.
          }
          {
            econstructor; eauto.
          }
        }
      }
    }
    {
      intros s' Heq HL Hs Hs'.
      invert Heq; simpl in *.
      rename H4 into Hiff.
      eapply StgSubsetI; eauto.
      eapply interp_prop_subst0_i_p in Hiff; eauto.
      {
        unfold subst0_i_p in *.
        simpl in *.
        eapply interp_prop_iff_sym in Hiff.
        eauto using interp_prop_iff_elim. 
      }
      {
        simpl in *.
        invert Hs'.
        invert Hs.
        econstructor; eauto.
      }
      {
        econstructor; eauto.
      }
    }
  Qed.

  Lemma monotone_shift_i_i x v b :
    monotone b ->
    monotone (shift_i_i x v b).
  Admitted.
  
  Lemma sorting_shift_i_i :
    forall L c s,
      sorting L c s ->
      forall x ls,
        let n := length ls in
        x <= length L ->
        wellscoped_ss L ->
        wellscoped_s (length L) s ->
        sorting (shift_i_ss n (firstn x L) ++ ls ++ my_skipn L x) (shift_i_i n x c) (shift_i_s n x s).
  Proof.
    simpl.
    induct 1;
      simpl; try rename x into y; intros x ls Hx HL Hs; cbn in *; try solve [econstructor; eauto].
    {
      (* Case Var *)
      copy H HnltL.
      eapply nth_error_Some_lt in HnltL.
      cases (x <=? y).
      {
        eapply StgVar'.
        {
          rewrite nth_error_app2;
          rewrite length_shift_i_ss; erewrite length_firstn_le; try la.
          rewrite nth_error_app2 by la.
          rewrite nth_error_my_skipn by la.
          erewrite <- H.
          f_equal.
          la.
        }
        {
          rewrite shift_i_s_shift_merge by la.
          f_equal.
          la.
        }
      }
      {
        eapply StgVar'.
        {
          rewrite nth_error_app1;
          try rewrite length_shift_i_ss; try erewrite length_firstn_le; try la.
          erewrite nth_error_shift_i_ss; eauto.
          rewrite nth_error_firstn; eauto.
        }          
        {
          erewrite length_firstn_le by la. 
          rewrite shift_i_s_shift_cut by la.
          eauto.
        }
      }
    }
    {
      econstructor; eauto.
      eapply IHsorting1; eauto; econstructor; eauto.
    }
    {
      (* Case TimeAbs *)
      econstructor; eauto.
      {
        unfold SNat, STimeFun in *.
        eapply IHsorting with (x := S x); eauto with db_la.
        econstructor; eauto.
      }
      eapply monotone_shift_i_i; eauto.
    }
    {
      econstructor; eauto.
      {
        eapply IHsorting1; eauto; econstructor; eauto.
      }
      {
        eapply IHsorting2; eauto; econstructor; eauto.
      }
    }
    {
      (* Case SubsetI *)
      econstructor; eauto.
      unfold subst0_i_p in *.
      rewrite <- shift_i_p_subst_out by la.
      invert Hs.
      eapply interp_prop_shift_i_p; eauto.
      eapply wellscoped_subst_i_p_0; eauto using sorting_wellscoped_i.
    }
    {
      (* Case SubsetE *)
      eapply StgSubsetE; eauto.
      eapply wellscoped_shift_i_p; eauto.
      repeat rewrite app_length.
      rewrite length_shift_i_ss.
      rewrite length_firstn_le by la.
      rewrite length_my_skipn_le by la.
      la.
    }
  Qed.

  Inductive wfprop : sctx -> prop -> Prop :=
  | WfPropTrueFalse L cn :
      wfprop L (PTrueFalse cn)
  | WfPropBinConn L opr p1 p2 :
      wfprop L p1 ->
      wfprop L p2 ->
      wfprop L (PBinConn opr p1 p2)
  | WfPropNot L p :
      wfprop L p ->
      wfprop L (PNot p)
  | WfPropBinPred L opr i1 i2 :
      sorting L i1 (SBaseSort (binpred_arg1_bsort opr)) ->
      sorting L i2 (SBaseSort (binpred_arg2_bsort opr)) ->
      wfprop L (PBinPred opr i1 i2)
  | WfPropEq L b i1 i2 :
      sorting L i1 (SBaseSort b) ->
      sorting L i2 (SBaseSort b) ->
      wfprop L (PEq b i1 i2)
  | WfPropQuan L q s p :
      wfprop (SBaseSort s :: L) p ->
      wfprop L (PQuan q s p)
  .
  
  Hint Constructors wfprop.

  Inductive wfsort : sctx -> sort -> Prop :=
  | WfStBaseSort L b :
      wfsort L (SBaseSort b)
  | WfStSubset L b p :
      wfprop (SBaseSort b :: L) p ->
      wfsort L (SSubset b p)
  .

  Hint Constructors wfsort.

  Lemma wfprop_bwfprop L p :
    wfprop L p ->
    bwfprop (map get_bsort L) p.
  Proof.
    induct 1; simpl; eauto using sorting_bsorting.
    {
      eapply sorting_bsorting in H; simpl in *.
      eapply sorting_bsorting in H0; simpl in *.
      eauto.
    }
    {
      eapply sorting_bsorting in H; simpl in *.
      eapply sorting_bsorting in H0; simpl in *.
      eauto.
    }
  Qed.
  
  Lemma wfsort_bwfsort L s :
    wfsort L s ->
    bwfsort (map get_bsort L) s.
  Proof.
    induct 1; simpl; econstructor; eauto.
    eapply wfprop_bwfprop in H.
    eauto.
  Qed.
  
  Lemma wfprop_wellscoped_p L p :
    wfprop L p ->
    wellscoped_p (length L) p.
  Proof.
    induct 1; simpl; eauto using sorting_wellscoped_i.
  Qed.
  
  Lemma wfsort_wellscoped_s L s :
    wfsort L s ->
    wellscoped_s (length L) s.
  Proof.
    induct 1; simpl; econstructor; eauto.
    eapply wfprop_wellscoped_p in H.
    eauto.
  Qed.
  
  Definition wfsorts := all_sorts wfsort.
  
  Lemma wfsorts_bwfsorts L :
    wfsorts L ->
    bwfsorts L.
  Proof.
    induct 1; simpl; intros; econstructor; eauto using wfsort_bwfsort.
  Qed.

  Lemma wfsorts_wellscoped_ss L :
    wfsorts L ->
    wellscoped_ss L.
  Proof.
    induct 1; simpl; intros; econstructor; eauto using wfsort_wellscoped_s.
  Qed.

  Lemma wfprop_shift_i_p :
    forall L p,
      wfprop L p ->
      forall x ls,
        let n := length ls in
        x <= length L ->
        wellscoped_ss L ->
        wfprop (shift_i_ss n (firstn x L) ++ ls ++ my_skipn L x) (shift_i_p n x p).
  Proof.
    simpl.
    induct 1;
      simpl; intros x ls Hx HL; cbn in *; try solve [econstructor; eauto].
    {
      econstructor;
      eapply sorting_shift_i_i with (s := SBaseSort _); eauto.
    }
    {
      econstructor;
      eapply sorting_shift_i_i with (s := SBaseSort _); eauto.
    }
    {
      econstructor.
      eapply IHwfprop with (x := S x); eauto with db_la.
      econstructor; eauto.
    }
  Qed.
  
  Lemma wfprop_shift_i_p_1_0 L p s :
    wfprop L p ->
    wellscoped_ss L ->
    wfprop (s :: L) (shift_i_p 1 0 p).
  Proof.
    intros Hp HL.
    eapply wfprop_shift_i_p with (x := 0) (ls := [s]) in Hp; eauto with db_la.
    simpl in *.
    rewrite my_skipn_0 in *.
    eauto.
  Qed.
  
(*  
  Lemma wfsorts_wfprop_strip_subsets L :
    wfsorts L ->
    forall n,
      n = length L ->
      wfprop L (and_all (strip_subsets L)).
  Proof.
    induct 1; simpl; intros n ?; subst; eauto.
    {
      econstructor.
    }
    rename H0 into Hwfsort.
    invert Hwfsort; simpl in *.
    {
      unfold shift0_i_p.
      rewrite and_all_map_shift_i_p.
      eapply wfprop_shift_i_p_1_0; eauto.
      eapply wfsorts_wellscoped_ss; eauto.
    }
    {
      unfold shift0_i_p.
      rewrite and_all_map_shift_i_p.
      econstructor; eauto.
      {
        eapply admit.
      }
      {
        eapply wfprop_shift_i_p_1_0; eauto.
        eapply wfsorts_wellscoped_ss; eauto.
      }
    }
  Qed.
 *)

  Lemma sorteq_shift_i_k L s s' :
    sorteq L s s' ->
    forall x ls,
      let n := length ls in
      x <= length L ->
      wellscoped_ss L ->
      wellscoped_s (length L) s ->
      wellscoped_s (length L) s' ->
      sorteq (shift_i_ss n (firstn x L) ++ ls ++ my_skipn L x) (shift_i_s n x s) (shift_i_s n x s').
  Proof.
    induct 1; simpl; eauto.
    intros x ls Hx HL Hs Hs'.
    econstructor; eauto.
    invert Hs.
    invert Hs'.
    eapply interp_prop_shift_i_p with (x := S x) (ls := ls) in H; simpl; eauto with db_la;
      econstructor; eauto.
  Qed.        

  Hint Extern 0 (wellscoped_ss (_ :: _)) => econstructor.
  
  Lemma wellscoped_shift_i_s L p :
    wellscoped_s L p ->
    forall x n L',
      L' = n + L ->
      wellscoped_s L' (shift_i_s n x p).
  Proof.
    induct 1; simpl; try solve [intros; subst; eauto using wellscoped_shift_i_p with db_la].
  Qed.

  Inductive kinding : sctx -> kctx -> ty -> kind -> Prop :=
  | KdgVar L K x k :
      nth_error K x = Some k ->
      kinding L K (TVar x) k
  | KdgConst L K cn :
      kinding L K (TConst cn) KType
  | KdgUnOp L K opr t :
      kinding L K t KType ->
      kinding L K (TUnOp opr t) KType
  | KdgBinOp L K opr c1 c2 :
      kinding L K c1 KType ->
      kinding L K c2 KType ->
      kinding L K (TBinOp opr c1 c2) KType
  | KdgArrow L K t1 i t2 :
      kinding L K t1 KType ->
      sorting L i STime ->
      kinding L K t2 KType ->
      kinding L K (TArrow t1 i t2) KType
  | KdgAbs L K b t k :
      kinding (SBaseSort b :: L) K t k ->
      kinding L K (TAbs b t) (KArrow b k)
  | KdgApp L K t b i k :
      kinding L K t (KArrow b k) ->
      sorting L i (SBaseSort b) ->
      kinding L K (TApp t b i) k
  | KdgQuan L K quan k c :
      kinding L (k :: K) c KType ->
      kinding L K (TQuan quan k c) KType
  | KdgQuanI L K quan s c :
      wfsort L s ->
      kinding (s :: L) K c KType ->
      kinding L K (TQuanI quan s c) KType
  | KdgRec L K c args :
      let k := map fst args in
      kinding L (k :: K) c k ->
      Forall (fun p => sorting L (snd p) (SBaseSort (fst p))) args ->
      kinding L K (TRec k c args) KType
  .

  Hint Constructors kinding.

  (* values for denotational semantics *)

  Record idx_arg :=
    {
      arg_bsort : bsort;
      arg_value : interp_bsort arg_bsort
    }.

  Definition interp_idx_arg bs (p : bsort * idx) : interp_bsorts bs idx_arg :=
    let b := fst p in
    let i := snd p in
    lift1 bs (fun x => Build_idx_arg b x) (interp_idx i bs b).

  Fixpoint lift_ls bs {A B} f (ls : list A) : interp_bsorts bs (list B) :=
    match ls with
    | [] => lift0 bs []
    | a :: ls' => lift2 bs cons (f a) (lift_ls bs f ls')
    end.

  Definition interp_idx_args bs := lift_ls bs (interp_idx_arg bs).
  
  Definition sortv b := option (interp_bsort b -> Prop).

  Fixpoint interp_bsorts_tuple bs :=
    match bs with
    | [] => unit
    | b :: bs' => (interp_bsort b * interp_bsorts_tuple bs')%type
    end.
  
  Inductive tyv :=
  | TVVar (x : var)
  | TVConst (cn : ty_const)
  | TVUnOp (opr : ty_un_op) (c : tyv)
  | TVBinOp (opr : ty_bin_op) (c1 c2 : tyv)
  | TVArrow (t1 : tyv) (i : time_type) (t2 : tyv)
  | TVQuan (q : quan) (k : kind) (t : tyv)
  | TVQuanI (q : quan) (b : bsort) (p : sortv b) (t : interp_bsort b -> tyv)
  | TVRec (k : kind) (t : interp_bsorts_tuple k -> tyv) (args : list idx_arg)
  .

  Inductive tyveq : tyv -> tyv -> Prop :=
  | TVEVar x : tyveq (TVVar x) (TVVar x)
  | TVEConst cn : tyveq (TVConst cn) (TVConst cn)
  | TVEUnOp opr t t' :
      tyveq t t' ->
      tyveq (TVUnOp opr t) (TVUnOp opr t')
  | TVEBinOp opr t1 t2 t1' t2' :
      tyveq t1 t1' ->
      tyveq t2 t2' ->
      tyveq (TVBinOp opr t1 t2) (TVBinOp opr t1' t2')
  | TVEArrow t1 i t2 t1' t2' :
      tyveq t1 t1' ->
      tyveq t2 t2' ->
      tyveq (TVArrow t1 i t2) (TVArrow t1' i t2')
  | TVEQuan q k t t' :
      tyveq t t' ->
      tyveq (TVQuan q k t) (TVQuan q k t')
  | TVEQuanIBaseSort q b t t' :
      (forall x, tyveq (t x) (t' x)) ->
      tyveq (@TVQuanI q b None t) (@TVQuanI q b None t')
  | TVEQuanISubset q b p t p' t' :
      (forall x, p x <-> p' x) ->
      (forall x, p x -> tyveq (t x) (t' x)) ->
      tyveq (@TVQuanI q b (Some p) t) (@TVQuanI q b (Some p') t')
  | TVERec k t t' args :
      (forall x, tyveq (t x) (t' x)) ->
      tyveq (TVRec k t args) (TVRec k t' args)
  .

  Hint Constructors tyveq.
  
  Lemma tyveq_refl t : tyveq t t.
  Proof.
    induct t; simpl; eauto.
    destruct p; simpl; eauto.
    econstructor; eauto.
    propositional.
  Qed.

  Lemma tyveq_sym a b : tyveq a b -> tyveq b a.
  Proof.
    induct 1; simpl; eauto.
    econstructor; eauto.
    {
      intros x.
      specialize (H x).
      propositional.
    }
    {
      intros x Hp'.
      eapply H in Hp'.
      eauto.
    }
  Qed.

  Lemma invert_tyveq_TUnOp t t' :
    tyveq t t' ->
    forall opr c,
      t = TVUnOp opr c ->
      exists c',
        t' = TVUnOp opr c' /\
        tyveq c c'.
  Proof.
    induct 1; simpl; intros opr' c Ht; try dis.
    assert (opr = opr').
    {
      congruence.
    }
    subst.
    invert Ht.
    eexists; eauto.
  Qed.
  
  Definition kind_dec : forall (b b' : kind), sumbool (b = b') (b <> b').
  Proof.
    intros; eapply list_eq_dec.
    intros; eapply sort_dec.
  Defined.
  
  Lemma tyveq_trans a b : tyveq a b -> forall c, tyveq b c -> tyveq a c.
  Proof.
    induct 1; simpl; intros c Hbc; try solve [invert Hbc; eauto].
    {
      eapply invert_tyveq_TUnOp in Hbc; eauto.
      openhyp; subst.
      eauto.
    }
    {
      invert Hbc.
      eapply Eqdep_dec.inj_pair2_eq_dec in H4; [|intros; eapply sort_dec]; subst.
      eauto.
    }
    {
      invert Hbc.
      eapply Eqdep_dec.inj_pair2_eq_dec in H5; [|intros; eapply sort_dec]; subst.
      eapply Eqdep_dec.inj_pair2_eq_dec in H6; [|intros; eapply sort_dec]; subst.
      econstructor; eauto.
      {
        intros x.
        specialize (H x).
        specialize (H7 x).
        propositional.
      }
      {
        intros x.
        specialize (H x).
        specialize (H7 x).
        specialize (H1 x).
        specialize (H8 x).
        intros Hp.
        eapply H1; eauto.
        propositional.
      }
    }
    {
      invert Hbc.
      eapply Eqdep_dec.inj_pair2_eq_dec in H3; [|intros; eapply kind_dec]; subst.
      econstructor; eauto.
    }
  Qed.
  
  Fixpoint interp_k k :=
    match k with
    | [] => tyv
    | b :: k => interp_bsort b -> interp_k k
    end.

  Definition interp_sort s bs b : interp_bsorts bs (sortv b) :=
    match s with
    | SBaseSort _ => lift0 _ None
    | SSubset _ p => lift1 bs (fun p => Some p) (interp_p (b :: bs) p)
    end.

  Fixpoint complete_var k (t : tyv) : interp_k k :=
    match k with
    | [] => t
    | b :: k' => fun _ => complete_var k' t
    end.
  
  Fixpoint kind_default_value (b : kind) : interp_k b :=
    match b with
    | [] => TVConst TCUnit
    | b :: k' => fun _ => kind_default_value k'
    end.
                                       
  Definition convert_kind_value k1 k2 : interp_k k1 -> interp_k k2.
  Proof.
    cases (kind_dec k1 k2); subst; eauto.
    intros.
    eapply kind_default_value.
  Defined.

  Fixpoint uncurrys bs : interp_k bs -> interp_bsorts_tuple bs -> tyv :=
    match bs return interp_k bs -> interp_bsorts_tuple bs -> tyv with
    | [] => fun f _ => f
    | b :: bs' => fun f p => uncurrys bs' (f (fst p)) (snd p)
    end.

  Fixpoint interp_ty ty bs k_ret : interp_bsorts bs (interp_k k_ret) :=
    match ty with
    | TVar x =>
      let r := lift0 bs (TVVar x) in
      lift1 bs (complete_var k_ret) r
    | TConst cn =>
      let r := lift0 bs (TVConst cn) in
      lift1 bs (convert_kind_value KType k_ret) r
    | TUnOp opr c =>
      let r := lift1 bs (TVUnOp opr) (interp_ty c bs KType) in
      lift1 bs (convert_kind_value KType k_ret) r
    | TBinOp opr c1 c2 =>
      let r := lift2 bs (TVBinOp opr) (interp_ty c1 bs KType) (interp_ty c2 bs KType) in
      lift1 bs (convert_kind_value KType k_ret) r
    | TArrow t1 i t2 =>
      let r := lift3 bs TVArrow (interp_ty t1 bs KType) (interp_idx i bs BSTime) (interp_ty t2 bs KType) in
      lift1 bs (convert_kind_value KType k_ret) r
    | TAbs _ t =>
      match k_ret with
      | b' :: k_ret' => interp_ty t (b' :: bs) k_ret'
      | [] => lift0 bs (kind_default_value KType)
      end
    | TApp t b i =>
      lift2 bs apply (interp_ty t bs (KArrow b k_ret)) (interp_idx i bs b)
    | TQuan q k t =>
      let r := lift1 bs (TVQuan q k) (interp_ty t bs KType) in
      lift1 bs (convert_kind_value KType k_ret) r
    | TQuanI q s t =>
      let b := get_bsort s in
      let r := lift2 bs (@TVQuanI q b) (interp_sort s bs b) (interp_ty t (b :: bs) KType) in
      lift1 bs (convert_kind_value KType k_ret) r
    | TRec k t args =>
      let r := lift2 bs (fun (t : interp_k k) args => TVRec k (uncurrys k t) args) (interp_ty t bs k) (interp_idx_args bs args) in
      lift1 bs (convert_kind_value KType k_ret) r
    end.

  Fixpoint gtyveq k : interp_k k -> interp_k k -> Prop :=
    match k with
    | [] => tyveq
    | b :: k' => fun t t' => forall x, gtyveq k' (t x) (t' x)
    end.
  
  Definition tyeq L t t' k :=
    let bs := map get_bsort L in
    let ps := strip_subsets L in
    let p := and_all ps in
    forall_ bs (lift3 bs (fun (p : Prop) t t' => p -> gtyveq k t t') (interp_p bs p) (interp_ty t bs k) (interp_ty t' bs k)).

  Lemma gtyveq_refl : forall k b, gtyveq k b b.
  Proof.
    induct k; simpl; eauto using tyveq_refl.
  Qed.
  
  Lemma tyeq_refl L t k : tyeq L t t k.
  Proof.
    unfold tyeq.
    rewrite dedup_lift3_2_3.
    eapply forall_lift2.
    intros.
    eauto using gtyveq_refl.    
  Qed.

  Lemma swap_lift3_2_3_b :
    forall bs T A1 A2 A3 (f1 : A1 -> A2 -> A3 -> T) a1 a2 a3,
      lift3 bs f1 a1 a2 a3 = lift3 bs (fun a1 a2 a3 => f1 a1 a3 a2) a1 a3 a2.
  Proof.
    intros; eapply swap_lift3_2_3; eauto.
  Qed.
  
  Lemma forall_lift3_lift3 :
    forall bs A1 A2 A3 P1 P2 P3 (f1 : A1 -> A2 -> A3 -> Prop) (f2 : A1 -> A2 -> A3 -> Prop),
      (forall a1 a2 a3, f1 a1 a2 a3 -> f2 a1 a2 a3) ->
      forall_ bs (lift3 bs f1 P1 P2 P3) ->
      forall_ bs (lift3 bs f2 P1 P2 P3).
  Proof.
    induct bs; simplify; eauto.
    rewrite fuse_lift1_lift3 in *.
    eapply IHbs; eauto.
    simplify.
    eauto.
  Qed.
  
  Lemma tyeq_sym L t1 t2 k : tyeq L t1 t2 k -> tyeq L t2 t1 k.
  Proof.
    unfold tyeq.
    intros H.
    erewrite swap_lift3_2_3_b.
    eapply forall_lift3_lift3; eauto.
    simpl.
    intros.
    Lemma gtyveq_sym : forall k a b, gtyveq k a b -> gtyveq k b a.
    Proof.
      induct k; simpl; eauto using tyveq_sym.
    Qed.
    
    eauto using gtyveq_sym.
  Qed.

  Lemma forall_lift3_lift3_lift3 :
    forall bs A1 A2 A3 A4 P1 P2 P3 P4 (f1 : A1 -> A2 -> A3 -> Prop) (f2 : A1 -> A3 -> A4 -> Prop) (f3 : A1 -> A2 -> A4 -> Prop),
      (forall a1 a2 a3 a4, f1 a1 a2 a3 -> f2 a1 a3 a4 -> f3 a1 a2 a4) ->
      forall_ bs (lift3 bs f1 P1 P2 P3) ->
      forall_ bs (lift3 bs f2 P1 P3 P4) ->
      forall_ bs (lift3 bs f3 P1 P2 P4).
  Proof.
    induct bs; simplify; eauto.
    rewrite fuse_lift1_lift3 in *.
    eapply IHbs; eauto.
    simplify.
    eauto.
  Qed.
  
  Lemma tyeq_trans L a b c k :
    tyeq L a b k ->
    tyeq L b c k ->
    tyeq L a c k.
  Proof.
    unfold tyeq.
    intros H1 H2.
    eapply forall_lift3_lift3_lift3; eauto.
    simpl.
    intros.
    Lemma gtyveq_trans : forall k a b c, gtyveq k a b -> gtyveq k b c -> gtyveq k a c.
    Proof.
      induct k; simpl; eauto using tyveq_trans.
    Qed.
    
    eauto using gtyveq_trans.
  Qed.
  
  Lemma fuse_lift3_lift3_2 bs :
    forall T A1 A2 A3 B1 B2 B3 (f : A1 -> A2 -> A3 -> T) (g : B1 -> B2 -> B3 -> A2) a1 a3 b1 b2 b3,
      lift3 bs f a1 (lift3 bs g b1 b2 b3) a3 = lift5 bs (fun a1 b1 b2 b3 a3 => f a1 (g b1 b2 b3) a3) a1 b1 b2 b3 a3.
  Proof.
    induct bs; simplify; eauto.
    eapply IHbs.
  Qed.
  
  Fixpoint lift7 arg_ks : forall t1 t2 t3 t4 t5 t6 t7 t, (t1 -> t2 -> t3 -> t4 -> t5 -> t6 -> t7 -> t) -> interp_bsorts arg_ks t1 -> interp_bsorts arg_ks t2 -> interp_bsorts arg_ks t3 -> interp_bsorts arg_ks t4 -> interp_bsorts arg_ks t5 -> interp_bsorts arg_ks t6 -> interp_bsorts arg_ks t7 -> interp_bsorts arg_ks t :=
    match arg_ks return forall t1 t2 t3 t4 t5 t6 t7 t, (t1 -> t2 -> t3 -> t4 -> t5 -> t6 -> t7 -> t) -> interp_bsorts arg_ks t1 -> interp_bsorts arg_ks t2 -> interp_bsorts arg_ks t3 -> interp_bsorts arg_ks t4 -> interp_bsorts arg_ks t5 -> interp_bsorts arg_ks t6 -> interp_bsorts arg_ks t7 -> interp_bsorts arg_ks t with
    | [] =>
      fun t1 t2 t3 t4 t5 t6 t7 t f x1 x2 x3 x4 x5 x6 x7 => f x1 x2 x3 x4 x5 x6 x7
    | arg_k :: arg_ks =>
      fun t1 t2 t3 t4 t5 t6 t7 t f x1 x2 x3 x4 x5 x6 x7 => lift7 arg_ks (fun a1 a2 a3 a4 a5 a6 a7 ak => f (a1 ak) (a2 ak) (a3 ak) (a4 ak) (a5 ak) (a6 ak) (a7 ak)) x1 x2 x3 x4 x5 x6 x7
    end.

  Lemma fuse_lift5_lift3_5 bs :
    forall T A1 A2 A3 A4 A5 B1 B2 B3 (f : A1 -> A2 -> A3 -> A4 -> A5 -> T) (g : B1 -> B2 -> B3 -> A5) a1 a2 a3 a4 b1 b2 b3,
      lift5 bs f a1 a2 a3 a4 (lift3 bs g b1 b2 b3) = lift7 bs (fun a1 a2 a3 a4 b1 b2 b3 => f a1 a2 a3 a4 (g b1 b2 b3)) a1 a2 a3 a4 b1 b2 b3.
  Proof.
    induct bs; simplify; eauto.
    eapply IHbs.
  Qed.
  
  Lemma fuse_lift1_lift7 bs :
    forall T A1 B1 B2 B3 B4 B5 B6 B7 (f : A1 -> T) (g : B1 -> B2 -> B3 -> B4 -> B5 -> B6 -> B7 -> A1) b1 b2 b3 b4 b5 b6 b7,
      lift1 bs f (lift7 bs g b1 b2 b3 b4 b5 b6 b7) = lift7 bs (fun b1 b2 b3 b4 b5 b6 b7 => f (g b1 b2 b3 b4 b5 b6 b7)) b1 b2 b3 b4 b5 b6 b7.
  Proof.
    induct bs; simplify; eauto.
    eapply IHbs.
  Qed.
  
  Lemma forall_lift7_lift3_1_2_5 :
    forall bs A1 A2 A3 A4 A5 A6 A7 P1 P2 P3 P4 P5 P6 P7 (f1 : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> Prop) (f2 : A1 -> A2 -> A5 -> Prop),
      (forall a1 a2 a3 a4 a5 a6 a7, f1 a1 a2 a3 a4 a5 a6 a7 -> f2 a1 a2 a5) ->
      forall_ bs (lift7 bs f1 P1 P2 P3 P4 P5 P6 P7) ->
      forall_ bs (lift3 bs f2 P1 P2 P5).
  Proof.
    induct bs; simplify; eauto.
    rewrite fuse_lift1_lift3 in *.
    rewrite fuse_lift1_lift7 in *.
    eapply IHbs; eauto.
    simplify.
    eauto.
  Qed.
  
  Lemma convert_kind_value_refl_eq :
    forall b v, convert_kind_value b b v = v.
  Proof.
    intros.
    unfold convert_kind_value.
    cases (kind_dec b b); propositional.
    unfold eq_rect_r.
    rewrite <- Eqdep.EqdepTheory.eq_rect_eq.
    eauto.
  Qed.

  Lemma forall_lift7_lift3_1_3_6 :
    forall bs A1 A2 A3 A4 A5 A6 A7 P1 P2 P3 P4 P5 P6 P7 (f1 : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> Prop) (f2 : A1 -> A3 -> A6 -> Prop),
      (forall a1 a2 a3 a4 a5 a6 a7, f1 a1 a2 a3 a4 a5 a6 a7 -> f2 a1 a3 a6) ->
      forall_ bs (lift7 bs f1 P1 P2 P3 P4 P5 P6 P7) ->
      forall_ bs (lift3 bs f2 P1 P3 P6).
  Proof.
    induct bs; simplify; eauto.
    rewrite fuse_lift1_lift3 in *.
    rewrite fuse_lift1_lift7 in *.
    eapply IHbs; eauto.
    simplify.
    eauto.
  Qed.
  
  Lemma forall_lift7_lift3_1_4_7 :
    forall bs A1 A2 A3 A4 A5 A6 A7 P1 P2 P3 P4 P5 P6 P7 (f1 : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> Prop) (f2 : A1 -> A4 -> A7 -> Prop),
      (forall a1 a2 a3 a4 a5 a6 a7, f1 a1 a2 a3 a4 a5 a6 a7 -> f2 a1 a4 a7) ->
      forall_ bs (lift7 bs f1 P1 P2 P3 P4 P5 P6 P7) ->
      forall_ bs (lift3 bs f2 P1 P4 P7).
  Proof.
    induct bs; simplify; eauto.
    rewrite fuse_lift1_lift3 in *.
    rewrite fuse_lift1_lift7 in *.
    eapply IHbs; eauto.
    simplify.
    eauto.
  Qed.
  
  Lemma invert_tyeq_TArrow L t1 i t2 t1' i' t2' :
    tyeq L (TArrow t1 i t2) (TArrow t1' i' t2') KType ->
    (* kinding L K (TArrow t1 i t2) KType -> *)
    tyeq L t1 t1' KType /\
    interp_prop L (TEq i i') /\
    tyeq L t2 t2' KType.
  Proof.
    intros H (* Hkd *).
    unfold tyeq, interp_prop in *.
    simpl in *.
    repeat rewrite fuse_lift1_lift3 in *.
    rewrite fuse_lift3_lift3_2 in *.
    rewrite fuse_lift5_lift3_5 in *.
    rewrite fuse_lift2_lift2_2 in *.
    (* invert Hkd. *)
    split.
    {
      eapply forall_lift7_lift3_1_2_5; eauto.
      simpl.
      intros.
      repeat rewrite convert_kind_value_refl_eq in *.
      eapply H0 in H1.
      invert H1.
      eauto.
    }
    split.
    {
      eapply forall_lift7_lift3_1_3_6; eauto.
      simpl.
      intros.
      repeat rewrite convert_kind_value_refl_eq in *.
      eapply H0 in H1.
      invert H1.
      eauto.
    }
    {
      eapply forall_lift7_lift3_1_4_7; eauto.
      simpl.
      intros.
      repeat rewrite convert_kind_value_refl_eq in *.
      eapply H0 in H1.
      invert H1.
      eauto.
    }
  Qed.

  Lemma forall_lift5_pure :
    forall bs A1 A2 A3 A4 A5 P1 P2 P3 P4 P5 (f1 : A1 -> A2 -> A3 -> A4 -> A5 -> Prop) (f2 : Prop),
      (forall a1 a2 a3 a4 a5, f1 a1 a2 a3 a4 a5 -> f2) ->
      forall_ bs (lift5 bs f1 P1 P2 P3 P4 P5) ->
      f2.
  Proof.
    induct bs; simplify; eauto.
    rewrite fuse_lift1_lift5 in *.
    eapply IHbs in H0; eauto.
    Grab Existential Variables.
    eapply sort_default_value.
  Qed.
  
  Lemma forall_lift5_lift1_1 :
    forall bs A1 A2 A3 A4 A5 P1 P2 P3 P4 P5 (f1 : A1 -> A2 -> A3 -> A4 -> A5 -> Prop) (f2 : A1 -> Prop),
      (forall a1 a2 a3 a4 a5, f1 a1 a2 a3 a4 a5 -> f2 a1) ->
      forall_ bs (lift5 bs f1 P1 P2 P3 P4 P5) ->
      forall_ bs (lift1 bs f2 P1).
  Proof.
    induct bs; simplify; eauto.
    rewrite fuse_lift1_lift1 in *.
    rewrite fuse_lift1_lift5 in *.
    eapply IHbs; eauto.
    simplify.
    eauto.
  Qed.
  
  Lemma TQuan_TArrow_false L q k t t1 i t2 :
    tyeq L (TQuan q k t) (TArrow t1 i t2) KType ->
    interp_prop L PFalse.
  Proof.
    intros H.
    unfold tyeq, interp_prop in *.
    simpl in *.
    repeat rewrite fuse_lift1_lift3 in *.
    repeat rewrite fuse_lift1_lift1 in *.
    rewrite fuse_lift3_lift1_2 in *.
    rewrite fuse_lift3_lift3_3 in *.
    rewrite fuse_lift2_lift0_2 in *.
    eapply forall_lift5_lift1_1; [|eapply H].
    simpl.
    intros.
    repeat rewrite convert_kind_value_refl_eq in *.
    eapply H0 in H1.
    invert H1.
  Qed.
  
  Lemma TQuan_TArrow_false_empty q k t t1 i t2 :
    tyeq [] (TQuan q k t) (TArrow t1 i t2) KType ->
    False.
  Proof.
    intros H.
    eapply TQuan_TArrow_false in H.
    unfold interp_prop in *.
    simpl in *.
    eauto.
  Qed.
  
  Lemma TUnOp_TArrow_false opr t t1 i t2 :
    tyeq [] (TUnOp opr t) (TArrow t1 i t2) KType ->
    False.
  Proof.
    intros H.
    unfold tyeq in *.
    simpl in *.
    repeat rewrite convert_kind_value_refl_eq in *.
    specialize (H I).
    invert H.
  Qed.

  Lemma TBinOp_TArrow_false opr ta tb t1 i t2 :
    tyeq [] (TBinOp opr ta tb) (TArrow t1 i t2) KType ->
    False.
  Proof.
    intros H.
    unfold tyeq in *.
    simpl in *.
    repeat rewrite convert_kind_value_refl_eq in *.
    specialize (H I).
    invert H.
  Qed.

  (* conditional eq *)
  Definition cond_eq A L (k k' : A) := 
    let bs := map get_bsort L in
    let ps := strip_subsets L in
    let p := and_all ps in
    forall_ bs (lift1 bs (fun p : Prop => p -> k = k') (interp_p bs p)).

  Notation kdeq := cond_eq.
  
  Lemma forall_lift3_lift1_1 :
    forall bs A1 A2 A3 P1 P2 P3 (f1 : A1 -> A2 -> A3 -> Prop) (f2 : A1 -> Prop),
      (forall a1 a2 a3, f1 a1 a2 a3 -> f2 a1) ->
      forall_ bs (lift3 bs f1 P1 P2 P3) ->
      forall_ bs (lift1 bs f2 P1).
  Proof.
    induct bs; simplify; eauto.
    rewrite fuse_lift1_lift1 in *.
    rewrite fuse_lift1_lift3 in *.
    eapply IHbs; eauto.
    simplify.
    eauto.
  Qed.
  
  Lemma invert_tyeq_TQuan L q1 k1 t1 q2 k2 t2 :
    tyeq L (TQuan q1 k1 t1) (TQuan q2 k2 t2) KType ->
    cond_eq L q1 q2 /\
    kdeq L k1 k2 /\
    tyeq L t1 t2 KType.
  Proof.
    intros H.
    unfold tyeq, cond_eq in *.
    simpl in *.
    repeat rewrite fuse_lift1_lift1 in *.
    rewrite fuse_lift3_lift1_2 in *.
    rewrite fuse_lift3_lift1_3 in *.
    split.
    {
      eapply forall_lift3_lift1_1; [|eapply H].
      simpl.
      intros.
      repeat rewrite convert_kind_value_refl_eq in *.
      eapply H0 in H1.
      invert H1.
      eauto.
    }
    split.
    {
      eapply forall_lift3_lift1_1; [|eapply H].
      simpl.
      intros.
      repeat rewrite convert_kind_value_refl_eq in *.
      eapply H0 in H1.
      invert H1.
      eauto.
    }
    {
      eapply forall_lift3_lift3; [|eapply H].
      simpl.
      intros.
      repeat rewrite convert_kind_value_refl_eq in *.
      eapply H0 in H1.
      invert H1.
      eauto.
    }
  Qed.
  
  Lemma invert_tyeq_TUnOp L opr t opr' t' :
    tyeq L (TUnOp opr t) (TUnOp opr' t') KType ->
    cond_eq L opr opr' /\
    tyeq L t t' KType.
  Proof.
    intros H.
    unfold tyeq, cond_eq in *.
    simpl in *.
    repeat rewrite fuse_lift1_lift1 in *.
    rewrite fuse_lift3_lift1_2 in *.
    rewrite fuse_lift3_lift1_3 in *.
    split.
    {
      eapply forall_lift3_lift1_1; [|eapply H].
      simpl.
      intros.
      repeat rewrite convert_kind_value_refl_eq in *.
      eapply H0 in H1.
      eapply invert_tyveq_TUnOp in H1; eauto.
      openhyp.
      congruence.
    }
    {
      eapply forall_lift3_lift3; [|eapply H].
      simpl.
      intros.
      repeat rewrite convert_kind_value_refl_eq in *.
      eapply H0 in H1.
      invert H1.
      eauto.
    }
  Qed.
  
  Lemma forall_lift5_lift3_1_2_4 :
    forall bs A1 A2 A3 A4 A5 P1 P2 P3 P4 P5 (f1 : A1 -> A2 -> A3 -> A4 -> A5 -> Prop) (f2 : A1 -> A2 -> A4 -> Prop),
      (forall a1 a2 a3 a4 a5, f1 a1 a2 a3 a4 a5 -> f2 a1 a2 a4) ->
      forall_ bs (lift5 bs f1 P1 P2 P3 P4 P5) ->
      forall_ bs (lift3 bs f2 P1 P2 P4).
  Proof.
    induct bs; simplify; eauto.
    rewrite fuse_lift1_lift3 in *.
    rewrite fuse_lift1_lift5 in *.
    eapply IHbs; eauto.
    simplify.
    eauto.
  Qed.
  
  Lemma forall_lift5_lift3_1_3_5 :
    forall bs A1 A2 A3 A4 A5 P1 P2 P3 P4 P5 (f1 : A1 -> A2 -> A3 -> A4 -> A5 -> Prop) (f2 : A1 -> A3 -> A5 -> Prop),
      (forall a1 a2 a3 a4 a5, f1 a1 a2 a3 a4 a5 -> f2 a1 a3 a5) ->
      forall_ bs (lift5 bs f1 P1 P2 P3 P4 P5) ->
      forall_ bs (lift3 bs f2 P1 P3 P5).
  Proof.
    induct bs; simplify; eauto.
    rewrite fuse_lift1_lift3 in *.
    rewrite fuse_lift1_lift5 in *.
    eapply IHbs; eauto.
    simplify.
    eauto.
  Qed.
  
  Lemma invert_tyeq_TBinOp L opr t1 t2 opr' t1' t2' :
    tyeq L (TBinOp opr t1 t2) (TBinOp opr' t1' t2') KType ->
    cond_eq L opr opr' /\
    tyeq L t1 t1' KType /\
    tyeq L t2 t2' KType.
  Proof.
    intros H.
    unfold tyeq, cond_eq in *.
    simpl in *.
    repeat rewrite fuse_lift1_lift2 in *.
    rewrite fuse_lift3_lift2_2 in *.
    rewrite fuse_lift4_lift2_4 in *.
    split.
    {
      eapply forall_lift5_lift1_1; [|eapply H].
      simpl.
      intros.
      repeat rewrite convert_kind_value_refl_eq in *.
      eapply H0 in H1.
      invert H1.
      eauto.
    }
    split.
    {
      eapply forall_lift5_lift3_1_2_4; [|eapply H].
      simpl.
      intros.
      repeat rewrite convert_kind_value_refl_eq in *.
      eapply H0 in H1.
      invert H1.
      eauto.
    }
    {
      eapply forall_lift5_lift3_1_3_5; [|eapply H].
      simpl.
      intros.
      repeat rewrite convert_kind_value_refl_eq in *.
      eapply H0 in H1.
      invert H1.
      eauto.
    }
  Qed.

  Lemma fuse_lift3_lift0_2 bs :
    forall T A1 A2 A3 (f : A1 -> A2 -> A3 -> T) (g : A2) a1 a3,
      lift3 bs f a1 (lift0 bs g) a3 = lift2 bs (fun a1 a3 => f a1 g a3) a1 a3.
  Proof.
    induct bs; simplify; eauto.
    eapply IHbs.
  Qed.
  
  Definition idxeq L i i' b := interp_prop L (PEq b i i').
  
  Lemma interp_idx_args_eq_Forall2 :
    forall cs cs',
      lift_ls [] (interp_idx_arg []) cs = lift_ls [] (interp_idx_arg []) cs' ->
      Forall2 (fun p p' => fst p = fst p' /\ idxeq [] (snd p) (snd p') (fst p)) cs cs'.
  Proof.
    unfold idxeq, interp_prop.
    simpl.
    induct cs; destruct cs'; simpl; intros H; try dis; eauto.
    destruct a as (b1 & i1).
    destruct p as (b2 & i2).
    invert H.
    econstructor; eauto.
    simpl.
    split; eauto.
    intros Htrue.
    eapply Eqdep_dec.inj_pair2_eq_dec; eauto.
    intros; eapply sort_dec.
  Qed.

(*  
  Lemma invert_tyeq_TRec L cs cs' k t k' t' :
    tyeq L (TRec k t cs) (TRec k' t' cs') KType ->
    kdeq L k k' /\
    tyeq L t t' k /\
    let bs := map get_bsort L in
    forall_ bs (lift3 bs (fun (p : Prop) cs cs' => p -> cs = cs') (interp_p bs (and_all (strip_subsets L))) (lift_ls bs (interp_idx_arg bs) cs) (lift_ls bs (interp_idx_arg bs) cs')).
  Proof.
    intros H.
    unfold tyeq, cond_eq, idxeq, interp_prop in *.
    simpl in *.
    repeat rewrite fuse_lift1_lift2 in *.
    rewrite fuse_lift3_lift2_2 in *.
    rewrite fuse_lift4_lift2_4 in *.
    split.
    {
      eapply forall_lift5_lift1_1; [|eapply H].
      simpl.
      intros.
      repeat rewrite convert_kind_value_refl_eq in *.
      eapply H0 in H1.
      invert H1.
      eapply get_bsorts_inj; eauto.
    }
    split.
    {
      repeat rewrite KArrows_get_bsorts in *.
      set (bs := map get_bsort L) in *.
      assert (Him : forall_ bs
                            (lift5 bs (fun (p : Prop) t t' t1 t1' => p -> t1 = convert_kind_value _ _ t1' /\ t = convert_kind_value _ _ t1 /\ t' = convert_kind_value _ _ t1' /\ t = t')
                                   (interp_p bs (and_all (strip_subsets L)))
                                   (interp_ty t bs k)
                                   (interp_ty t' bs k)
                                   (interp_ty t bs (KArrows (get_bsorts k)))
                                   (interp_ty t' bs (KArrows (get_bsorts k')))
             )).
      {
      }
      eapply forall_lift5_lift3_1_2_4; [|eapply H].
      simpl.
      intros.
      repeat rewrite convert_kind_value_refl_eq in *.
      equality.
    }
    {
      unfold interp_idx_args in *.
      set (bs := map get_bsort L) in *.
      eapply forall_lift5_lift3_1_3_5; [|eapply H].
      simpl.
      intros.
      repeat rewrite convert_kind_value_refl_eq in *.
      equality.
    }
  Qed.
  
  Lemma invert_tyeq_TRec_empty cs cs' k t k' t' :
    tyeq [] (TRec k t cs) (TRec k' t' cs') KType ->
    kdeq [] k k' /\
    tyeq [] t t' KType /\
    Forall2 (fun p p' => fst p = fst p' /\ idxeq [] (snd p) (snd p') (fst p)) cs cs'.
  Proof.
    intros H.
    eapply invert_tyeq_TRec in H.
    simpl in *.
    destruct H as (Hk & Ht & Ha).
    repeat try_split; eauto.
    specialize (Ha I).
    eapply interp_idx_args_eq_Forall2; eauto.
  Qed.
 *)

  Lemma uncurrys_inj : forall bs f f', uncurrys bs f = uncurrys bs f' -> f = f'.
  Proof.
    induct bs; simpl; eauto; intros f f' H.
    {
      eapply (f_equal (fun f => f tt)) in H.
      eauto.
    }
    {
      eapply FunctionalExtensionality.functional_extensionality.
      intros x.
      eapply IHbs.
      eapply FunctionalExtensionality.functional_extensionality.
      intros y.
      eapply (f_equal (fun f => f (x, y))) in H.
      simpl in *.
      eauto.
    }
  Qed.

  Lemma uncurrys_inj_tyveq : forall bs f f', (forall x, tyveq (uncurrys bs f x) (uncurrys bs f' x)) -> (gtyveq bs f f').
  Proof.
    induct bs; simpl; eauto; intros f f' H; eauto.
    {
      eapply H.
      eapply tt.
    }
    {
      intros x.
      eapply IHbs.
      intros y.
      specialize (H (x, y)).
      simpl in *.
      eauto.
    }
  Qed.

  Lemma invert_tyeq_TRec_empty cs cs' k t k' t' :
    tyeq [] (TRec k t cs) (TRec k' t' cs') KType ->
    kdeq [] k k' /\
    tyeq [] t t' k /\
    Forall2 (fun p p' => fst p = fst p' /\ idxeq [] (snd p) (snd p') (fst p)) cs cs'.
  Proof.
    intros H.
    unfold tyeq, cond_eq, idxeq, interp_prop in *.
    simpl in *.
    repeat rewrite convert_kind_value_refl_eq in *.
    specialize (H I).
    invert H.
    rename k' into k.
    eapply Eqdep_dec.inj_pair2_eq_dec in H2; [|intros; eapply kind_dec]; subst.
    eapply Eqdep_dec.inj_pair2_eq_dec in H5; [|intros; eapply kind_dec]; subst.
    repeat try_split; eauto.
    {
      intros Htrue.
      eapply uncurrys_inj_tyveq.
      eauto.
    }
    eapply interp_idx_args_eq_Forall2; eauto.
  Qed.

  Lemma tyeq_TRec_TArrow_false cs k3 t3 t1 i t2 :
    tyeq [] (TRec k3 t3 cs) (TArrow t1 i t2) KType ->
    False.
  Proof.
    intros H.
    unfold tyeq in *.
    simpl in *.
    repeat rewrite convert_kind_value_refl_eq in *.
    specialize (H I).
    invert H.
  Qed.

  Lemma typeq_TRec_TQuan_false cs k3 t3 q k t  :
    tyeq [] (TRec k3 t3 cs) (TQuan q k t) KType ->
    False.
  Proof.
    intros H.
    unfold tyeq in *.
    simpl in *.
    repeat rewrite convert_kind_value_refl_eq in *.
    specialize (H I).
    invert H.
  Qed.

  Lemma tyeq_TRec_TUnOp_false cs k3 t3 opr t :
    tyeq [] (TRec k3 t3 cs) (TUnOp opr t) KType ->
    False.
  Proof.
    intros H.
    unfold tyeq in *.
    simpl in *.
    repeat rewrite convert_kind_value_refl_eq in *.
    specialize (H I).
    invert H.
  Qed.

  Lemma tyeq_TRec_TBinOp_false cs k3 t3 opr t1 t2  :
    tyeq [] (TRec k3 t3 cs) (TBinOp opr t1 t2) KType ->
    False.
  Proof.
    intros H.
    unfold tyeq in *.
    simpl in *.
    repeat rewrite convert_kind_value_refl_eq in *.
    specialize (H I).
    invert H.
  Qed.

  Lemma tyeq_TRec_TConst_false cs k3 t3 cn  :
    tyeq [] (TRec k3 t3 cs) (TConst cn) KType ->
    False.
  Proof.
    intros H.
    unfold tyeq in *.
    simpl in *.
    repeat rewrite convert_kind_value_refl_eq in *.
    specialize (H I).
    invert H.
  Qed.
  
  Inductive bkinding : list bsort -> ty -> kind -> Prop :=
  | BKdgVar L x k :
      bkinding L (TVar x) k
  | BKdgConst L cn :
      bkinding L (TConst cn) KType
  | BKdgUnOp L opr t :
      bkinding L t KType ->
      bkinding L (TUnOp opr t) KType
  | BKdgBinOp L opr c1 c2 :
      bkinding L c1 KType ->
      bkinding L c2 KType ->
      bkinding L (TBinOp opr c1 c2) KType
  | BKdgArrow L t1 i t2 :
      bkinding L t1 KType ->
      bsorting L i BSTime ->
      bkinding L t2 KType ->
      bkinding L (TArrow t1 i t2) KType
  | BKdgAbs L b t k :
      bkinding (b :: L) t k ->
      bkinding L (TAbs b t) (KArrow b k)
  | BKdgApp L t b i k :
      bkinding L t (KArrow b k) ->
      bsorting L i b ->
      bkinding L (TApp t b i) k
  | BKdgQuan L quan k c :
      bkinding L c KType ->
      bkinding L (TQuan quan k c) KType
  | BKdgQuanI L quan s c :
      bwfsort L s ->
      bkinding (get_bsort s :: L) c KType ->
      bkinding L (TQuanI quan s c) KType
  | BKdgRec L c args :
      let k := map fst args in
      bkinding L c k ->
      Forall (fun p => bsorting L (snd p) (fst p)) args ->
      bkinding L (TRec k c args) KType
  .

  Hint Constructors bkinding.

  Inductive tyeq2 : sctx -> ty -> ty -> kind -> Prop :=
  (* | TyEqVar L x : *)
  (*     tyeq2 L (CVar x) (CVar x) *)
  (* | TyEqConst L cn : *)
  (*     tyeq2 L (CConst cn) (CConst cn) *)
  | TyEqUnOp L opr t t' :
      tyeq2 L t t' KType ->
      tyeq2 L (TUnOp opr t) (TUnOp opr t') KType
  | TyEqBinOp L opr t1 t2 t1' t2' :
      tyeq2 L t1 t1' KType ->
      tyeq2 L t2 t2' KType ->
      tyeq2 L (TBinOp opr t1 t2) (TBinOp opr t1' t2') KType
  | TyEqArrow L t1 i t2 t1' i' t2':
      tyeq2 L t1 t1' KType ->
      idxeq L i i' BSTime ->
      tyeq2 L t2 t2' KType ->
      tyeq2 L (TArrow t1 i t2) (TArrow t1' i' t2') KType
  | TyEqAbs L b t t' k :
      tyeq2 (SBaseSort b :: L) t t' k ->
      tyeq2 L (TAbs b t) (TAbs b t') (KArrow b k)
  | TyEqApp L t b i t' i' k :
      tyeq2 L t t' (KArrow b k ) ->
      idxeq L i i' b ->
      tyeq2 L (TApp t b i) (TApp t' b i') k
  | TyEqBeta L s t b i k :
      tyeq2 L (TApp (TAbs s t) b i) (subst0_i_t i t) k
  (* | TyEqBetaRev L t1 t2  : *)
  (*     tyeq2 L (subst0_c_c t2 t1) (CApp (CAbs t1) t2) *)
  | TyEqQuan L quan k t t' :
      tyeq2 L t t' KType ->
      tyeq2 L (TQuan quan k t) (TQuan quan k t') KType
  | TyEqQuanI L quan s t s' t' :
      sorteq L s s' ->
      (* s = s' -> *)
      tyeq2 (s :: L) t t' KType ->
      tyeq2 L (TQuanI quan s t) (TQuanI quan s' t') KType
  | TyEqRec L c args c' args' :
      let k := map fst args in
      tyeq2 L c c' k ->
      Forall2 (fun p p' => fst p = fst p' /\ idxeq L (snd p) (snd p') (fst p)) args args' ->
      tyeq2 L (TRec k c args) (TRec k c' args') KType
  (* the following rules are just here to satisfy reflexivity *)
  (* don't do deep equality test of two CAbs's *)
  (* | TyEqAbs L t : *)
  (*     tyeq2 L (CAbs t) (CAbs t) *)
  (* | TyEqApp L c1 c2 : *)
  (*     tyeq2 L (CApp c1 c2) (CApp c1 c2) *)
  (* structural rules *)
  | TyEqRefl L t k :
      tyeq2 L t t k
  | TyEqSym L a b k :
      tyeq2 L a b k ->
      tyeq2 L b a k
  | TyEqTrans L a b c k :
      tyeq2 L a b k ->
      tyeq2 L b c k ->
      bkinding (map get_bsort L) b k ->
      tyeq2 L a c k
  .

  Hint Constructors tyeq2.

  Lemma forall_lift3_lift3_lift5_2_4_3_5 :
    forall bs A1 A2 A3 A4 A5 P1 P2 P3 P4 P5 (f1 : A1 -> A2 -> A4 -> Prop) (f2 : A1 -> A3 -> A5 -> Prop) (f3 : A1 -> A2 -> A3 -> A4 -> A5 -> Prop),
      (forall a1 a2 a3 a4 a5, f1 a1 a2 a4 -> f2 a1 a3 a5 -> f3 a1 a2 a3 a4 a5) ->
      forall_ bs (lift3 bs f1 P1 P2 P4) ->
      forall_ bs (lift3 bs f2 P1 P3 P5) ->
      forall_ bs (lift5 bs f3 P1 P2 P3 P4 P5).
  Proof.
    induct bs; simplify; eauto.
    rewrite fuse_lift1_lift3 in *.
    rewrite fuse_lift1_lift5 in *.
    eapply IHbs; eauto.
    simplify.
    eauto.
  Qed.
  
  Lemma tyeq_TUnOp L opr t t' :
    tyeq L t t' KType -> 
    tyeq L (TUnOp opr t) (TUnOp opr t') KType.
  Proof.
    intros H.
    unfold tyeq in *.
    simpl in *.
    repeat rewrite fuse_lift1_lift1 in *.
    repeat rewrite fuse_lift3_lift1_2 in *.
    repeat rewrite fuse_lift3_lift1_3 in *.
    eapply forall_lift3_lift3; eauto.
    simpl; intros.
    repeat rewrite convert_kind_value_refl_eq in *.
    eauto.
  Qed.

  Lemma tyeq_TBinOp L opr t1 t2 t1' t2' :
    tyeq L t1 t1' KType -> 
    tyeq L t2 t2' KType -> 
    tyeq L (TBinOp opr t1 t2) (TBinOp opr t1' t2') KType.
  Proof.
    intros H1 H2.
    unfold tyeq in *.
    simpl in *.
    repeat rewrite fuse_lift1_lift2 in *.
    repeat rewrite fuse_lift3_lift2_2 in *.
    repeat rewrite fuse_lift4_lift2_4 in *.
    eapply forall_lift3_lift3_lift5_2_4_3_5; eauto.
    simpl; intros.
    repeat rewrite convert_kind_value_refl_eq in *.
    eauto.
  Qed.

  Lemma forall_lift3_lift3_lift3_lift7 :
    forall bs A1 A2 A3 A4 A5 A6 A7 P1 P2 P3 P4 P5 P6 P7 (f1 : A1 -> A2 -> A5 -> Prop) (f2 : A1 -> A3 -> A6 -> Prop) (f3 : A1 -> A4 -> A7 -> Prop) (f4 : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> Prop),
      (forall a1 a2 a3 a4 a5 a6 a7, f1 a1 a2 a5 -> f2 a1 a3 a6 -> f3 a1 a4 a7 -> f4 a1 a2 a3 a4 a5 a6 a7) ->
      forall_ bs (lift3 bs f1 P1 P2 P5) ->
      forall_ bs (lift3 bs f2 P1 P3 P6) ->
      forall_ bs (lift3 bs f3 P1 P4 P7) ->
      forall_ bs (lift7 bs f4 P1 P2 P3 P4 P5 P6 P7).
  Proof.
    induct bs; simplify; eauto.
    rewrite fuse_lift1_lift3 in *.
    rewrite fuse_lift1_lift7 in *.
    eapply IHbs; eauto.
    simplify.
    eauto.
  Qed.
  
  Lemma tyeq_TArrow L t1 i t2 t1' i' t2' :
    tyeq L t1 t1' KType -> 
    idxeq L i i' BSTime ->
    tyeq L t2 t2' KType -> 
    tyeq L (TArrow t1 i t2) (TArrow t1' i' t2') KType.
  Proof.
    intros H1 H2 H3.
    unfold tyeq, idxeq, interp_prop in *.
    simpl in *.
    repeat rewrite fuse_lift1_lift3 in *.
    repeat rewrite fuse_lift3_lift3_2 in *.
    repeat rewrite fuse_lift5_lift3_5 in *.
    repeat rewrite fuse_lift2_lift2_2 in *.
    
    eapply forall_lift3_lift3_lift3_lift7; eauto.
    simpl; intros.
    repeat rewrite convert_kind_value_refl_eq in *.
    Lemma TVEArrow' t1 i t2 t1' i' t2' :
      tyveq t1 t1' ->
      i = i' ->
      tyveq t2 t2' ->
      tyveq (TVArrow t1 i t2) (TVArrow t1' i' t2').
    Proof.
      intros; subst; eauto.
    Qed.
    
    eapply TVEArrow'; eauto.
  Qed.
  
  Lemma forall_lift2_lift2_lift2_lift3_lift3 :
    forall bs A1 A2 A3 A4 A5 A6 P1 P2 P3 P4 P5 P6 (f1 : A1 -> A4 -> Prop) (f2 : A2 -> A5 -> Prop) (f3 : A3 -> A6 -> Prop) (f4 : A1 -> A2 -> A3 -> Prop) (f5 : A4 -> A5 -> A6 -> Prop),
      (forall a1 a2 a3 a4 a5 a6, f1 a1 a4 -> f2 a2 a5 -> f3 a3 a6 -> f4 a1 a2 a3 -> f5 a4 a5 a6) ->
      forall_ bs (lift2 bs f1 P1 P4) ->
      forall_ bs (lift2 bs f2 P2 P5) ->
      forall_ bs (lift2 bs f3 P3 P6) ->
      forall_ bs (lift3 bs f4 P1 P2 P3) ->
      forall_ bs (lift3 bs f5 P4 P5 P6).
  Proof.
    induct bs; simplify; eauto.
    rewrite fuse_lift1_lift3 in *.
    rewrite fuse_lift1_lift2 in *.
    eapply IHbs; eauto.
    simplify.
    eauto.
  Qed.
  
  Lemma forall_replace_lift3 bs p1 p2 p3 p1' p2' p3' (f : Prop -> Prop -> Prop -> Prop) :
    iff_ bs p1 p1' ->
    iff_ bs p2 p2' ->
    iff_ bs p3 p3' ->
    (forall p1 p2 p3 p1' p2' p3', (p1 <-> p1') -> (p2 <-> p2') -> (p3 <-> p3') -> f p1 p2 p3 -> f p1' p2' p3') ->
    forall_ bs (lift3 bs f p1 p2 p3) ->
    forall_ bs (lift3 bs f p1' p2' p3').
  Proof.
    intros.
    unfold iff_ in *.
    eapply forall_lift2_lift2_lift2_lift3_lift3; eauto.
  Qed.
  
  Lemma forall_lift3_lift2_lift1 :
    forall bs A1 A2 A3 A4 P1 P2 P3 P4 (f1 : A1 -> A2 -> A3 -> Prop) (f2 : A1 -> A4 -> Prop) (f3 : A4 -> Prop),
      (forall a1 a2 a3 a4, f1 a1 a2 a3 -> f2 a1 a4 -> f3 a4) ->
      forall_ bs (lift3 bs f1 P1 P2 P3) ->
      forall_ bs (lift2 bs f2 P1 P4) ->
      forall_ bs (lift1 bs f3 P4).
  Proof.
    induct bs; simplify; eauto.
    rewrite fuse_lift1_lift3 in *.
    rewrite fuse_lift1_lift2 in *.
    rewrite fuse_lift1_lift1 in *.
    eapply IHbs; eauto.
    simplify.
    eauto.
  Qed.
  
  Lemma forall_lift3_lift2_lift3 :
    forall bs A1 A2 A3 A4 P1 P2 P3 P4 (f1 : A1 -> A2 -> A3 -> Prop) (f2 : A1 -> A4 -> Prop) (f3 : A4 -> A2 -> A3 -> Prop),
      (forall a1 a2 a3 a4, f1 a1 a2 a3 -> f2 a1 a4 -> f3 a4 a2 a3) ->
      forall_ bs (lift3 bs f1 P1 P2 P3) ->
      forall_ bs (lift2 bs f2 P1 P4) ->
      forall_ bs (lift3 bs f3 P4 P2 P3).
  Proof.
    induct bs; simplify; eauto.
    rewrite fuse_lift1_lift3 in *.
    rewrite fuse_lift1_lift2 in *.
    eapply IHbs; eauto.
    simplify.
    eauto.
  Qed.
  
  Lemma tyeq_TAbs L b t t' k :
    tyeq (SBaseSort b :: L) t t' k ->
    wellscoped_ss L ->
    tyeq L (TAbs b t) (TAbs b t') (KArrow b k).
  Proof.
    intros H HL.
    unfold tyeq in *.
    simpl in *.
    repeat rewrite fuse_lift1_lift3 in *.
    repeat rewrite fuse_lift3_lift0_2 in *.
    repeat rewrite fuse_lift2_lift0_2 in *.
    unfold shift0_i_p in *.
    rewrite and_all_map_shift_i_p in *.
    set (bs := map get_bsort L) in *.
    set (ps := and_all (strip_subsets L)) in *.
    specialize (@forall_shift_i_p_iff_shift ps [b] 0 bs 1); intros Hshift.
    simpl in *.
    repeat rewrite fuse_lift1_lift2 in *.
    repeat rewrite fuse_lift2_lift1_2 in *.
    eapply forall_lift3_lift2_lift3; [| eapply H | eapply Hshift]; eauto.
    {
      simpl; intros.
      specialize (H0 x).
      specialize (H1 x).
      propositional.
    }
    {
      eapply wellscoped_ss_wellscoped_p_strip_subsets; eauto.
      subst bs; rewrite map_length; eauto.
    }
  Qed.

  Lemma tyeq_TApp L t b i t' i' k :
    tyeq L t t' (KArrow b k) -> 
    idxeq L i i' b -> 
    tyeq L (TApp t b i) (TApp t' b i') k.
  Proof.
    intros H1 H2.
    unfold tyeq, idxeq, interp_prop in *.
    simpl in *.
    repeat rewrite fuse_lift2_lift2_2 in *.
    repeat rewrite fuse_lift3_lift2_2 in *.
    repeat rewrite fuse_lift4_lift2_4 in *.
    eapply forall_lift3_lift3_lift5_2_4_3_5; eauto.
    simpl; intros.
    copy H3 Ha1.
    eapply H0 in H3; subst.
    eauto.
  Qed.

  Lemma bkinding_TUnOp_invert' L t k :
    bkinding L t k ->
    forall opr c,
      t = TUnOp opr c ->
      bkinding L c KType /\
      k = KType.
  Proof.
    induct 1; intros; try discriminate.
    assert (opr = opr0).
    {
      congruence.
    }
    invert H0.
    eauto.
  Qed.

  Lemma bkinding_TUnOp_invert L opr c k :
    bkinding L (TUnOp opr c) k ->
    bkinding L c KType /\
    k = KType.
  Proof.
    intros.
    eapply bkinding_TUnOp_invert'; eauto.
  Qed.

  Inductive ForSome {A} (P : A -> A -> Prop) : option A -> option A -> Prop :=
  | FSNone : ForSome P None None
  | FSSome a a' :
      P a a' ->
      ForSome P (Some a) (Some a')
  .

  Hint Constructors ForSome.
  
  Lemma forall_subst_i_s_iff_subst :
    forall body x bs v b_v b_b,
      let bs' := removen x bs in
      nth_error bs x = Some b_v ->
      bsorting (skipn (S x) bs) v b_v ->
      bwfsort bs body ->
      b_b = get_bsort body ->
      forall_ bs' (lift2 bs' (ForSome (fun p p' => forall x, p x <-> p' x)) (interp_sort (subst_i_s x (shift_i_i x 0 v) body) bs' b_b) (subst x bs (interp_idx v (skipn (S x) bs) b_v) (interp_sort body bs b_b))).
  Proof.
    simpl.
    induct body; simpl; intros x bs v b_v b_b Hx Hv Hbody ?; subst; invert Hbody.
    {
      rewrite fuse_lift2_lift0_1.
      rewrite subst_lift0.
      rewrite fuse_lift1_lift0.
      eapply forall_lift0.
      eauto.
    }
    {
      rewrite subst_lift1.
      rewrite fuse_lift2_lift1_1.
      rewrite fuse_lift2_lift1_2.
      repeat rewrite shift0_i_i_shift_0.
      rename s into b.
      specialize (@forall_subst_i_p_iff_subst p (S x) (b :: bs) v b_v); intros Hsubst.
      simpl in *.
      rewrite fuse_lift1_lift2 in *.
      eapply forall_lift2_lift2; [| eapply Hsubst]; eauto.
    }
  Qed.

  Lemma forall_interp_idx_arg_subst_i_i_iff_subst :
    forall body x bs v b_v,
      let bs' := removen x bs in
      nth_error bs x = Some b_v ->
      bsorting (skipn (S x) bs) v b_v ->
      bsorting bs (snd body) (fst body) ->
      forall_ bs' (lift2 bs' eq (interp_idx_arg bs' (map_snd (subst_i_i x (shift_i_i x 0 v)) body)) (subst x bs (interp_idx v (skipn (S x) bs) b_v) (interp_idx_arg bs body))).
  Proof.
    unfold interp_idx_arg; simpl.
    destruct body as (b & i); simpl; intros x bs v b_v Hx Hv Hbody.
    rewrite subst_lift1.
    rewrite fuse_lift2_lift1_1.
    rewrite fuse_lift2_lift1_2.
    eapply forall_lift2_lift2; [| eapply forall_subst_i_i_iff_subst]; eauto.
    simpl; intros; subst.
    eauto.
  Qed.
  
  Lemma forall_interp_idx_args_subst_i_i_iff_subst :
    forall body x bs v b_v,
      let bs' := removen x bs in
      nth_error bs x = Some b_v ->
      bsorting (skipn (S x) bs) v b_v ->
      Forall (fun p => bsorting bs (snd p) (fst p)) body ->
      forall_ bs' (lift2 bs' eq (interp_idx_args bs' (map (map_snd (subst_i_i x (shift_i_i x 0 v))) body)) (subst x bs (interp_idx v (skipn (S x) bs) b_v) (interp_idx_args bs body))).
  Proof.
    unfold interp_idx_args; simpl.
    induct body; simpl; intros x bs v b_v Hx Hv Hbody; invert Hbody.
    {
      rewrite fuse_lift2_lift0_1.
      rewrite subst_lift0.
      rewrite fuse_lift1_lift0.
      eapply forall_lift0.
      propositional.
    }
    {
      rewrite subst_lift2.
      rewrite fuse_lift2_lift2_1.
      rewrite fuse_lift3_lift2_3.
      eapply forall_lift2_lift2_lift4; [|eapply forall_interp_idx_arg_subst_i_i_iff_subst|eapply IHbody]; eauto.
      simpl; intros; subst.
      eauto.
    }
  Qed.

  Lemma forall_subst_i_t_iff_subst :
    forall body x bs v b_v k,
      let bs' := removen x bs in
      nth_error bs x = Some b_v ->
      bsorting (skipn (S x) bs) v b_v ->
      bkinding bs body k ->
      forall_ bs' (lift2 bs' (gtyveq k) (interp_ty (subst_i_t x (shift_i_i x 0 v) body) bs' k) (subst x bs (interp_idx v (skipn (S x) bs) b_v) (interp_ty body bs k))).
  Proof.
    simpl.
    induct body; try rename x into y; try rename k into k'; intros x bs v b_v k Hx Hv Hbody.
    {
      (* Case Var *)
      simpl.
      rewrite fuse_lift2_lift1_1 in *.
      rewrite fuse_lift2_lift0_1 in *.
      rewrite fuse_lift1_lift0 in *.
      rewrite subst_lift0.
      rewrite fuse_lift1_lift0 in *.
      eapply forall_lift0.
      eauto using gtyveq_refl.
    }
    {
      (* Case Const *)
      simpl.
      repeat rewrite fuse_lift1_lift0 in *.
      rewrite fuse_lift2_lift0_1 in *.
      rewrite subst_lift0.
      rewrite fuse_lift1_lift0 in *.
      eapply forall_lift0.
      eauto using gtyveq_refl.
    }
    {
      (* Case UnOp *)
      simpl.
      invert Hbody.
      (* eapply bkinding_TUnOp_invert in Hbody; openhyp; subst. *)
      repeat rewrite fuse_lift2_lift1_1 in *.
      rewrite fuse_lift1_lift1 in *.
      rewrite subst_lift1.
      rewrite fuse_lift2_lift1_2.
      eapply forall_lift2_lift2; [|eapply IHbody with (k := KType)]; eauto.
      simpl; intros; subst.
      repeat rewrite convert_kind_value_refl_eq in *.
      eauto.
    }
    {
      (* Case BinOp *)
      simpl.
      invert Hbody.
      repeat rewrite fuse_lift1_lift2 in *.
      repeat rewrite fuse_lift2_lift2_1 in *.
      rewrite subst_lift2.
      rewrite fuse_lift3_lift2_3.
      eapply forall_lift2_lift2_lift4; [|eapply IHbody1 with (k := KType)|eapply IHbody2 with (k := KType)]; eauto.
      simpl; intros; subst.
      repeat rewrite convert_kind_value_refl_eq in *.
      eauto.
    }
    {
      (* Case Arrow *)
      simpl.
      invert Hbody.
      repeat rewrite fuse_lift1_lift3 in *.
      rewrite subst_lift3.
      rewrite fuse_lift2_lift3_1.
      rewrite fuse_lift4_lift3_4.
      eapply forall_lift2_lift2_lift2_lift6; [|eapply IHbody1 with (k := KType)| eapply forall_subst_i_i_iff_subst with (b_b := BSTime) | eapply IHbody2 with (k := KType)]; eauto.
      simpl; intros; subst.
      repeat rewrite convert_kind_value_refl_eq in *.
      eauto.
    }
    {
      (* Case Abs *)
      simpl.
      invert Hbody.
      rename s into b.
      rename k0 into k.
      specialize (IHbody (S x) (b :: bs) v b_v k).
      simpl in *.
      rewrite fuse_lift1_lift2 in *.
      rewrite shift0_i_i_shift_0.
      eapply forall_lift2_lift2; [ | eapply IHbody; eauto].
      simpl; intros.
      eauto.
    }
    {
      (* Case App *)
      simpl.
      invert Hbody.
      rewrite fuse_lift2_lift2_1.
      rewrite subst_lift2.
      rewrite fuse_lift3_lift2_3.
      simpl in *.
      eapply forall_lift2_lift2_lift4; [|eapply IHbody with (k := KArrow b k)| eapply forall_subst_i_i_iff_subst with (b_b := b)]; eauto.
      simpl; intros; subst.
      eauto.
    }
    {
      (* Case Quan *)
      simpl.
      invert Hbody.
      repeat rewrite fuse_lift2_lift1_1 in *.
      rewrite fuse_lift1_lift1 in *.
      rewrite subst_lift1.
      rewrite fuse_lift2_lift1_2.
      eapply forall_lift2_lift2; [|eapply IHbody with (k := KType)]; eauto.
      simpl; intros; subst.
      repeat rewrite convert_kind_value_refl_eq in *.
      eauto.
    }
    {
      (* Case QuanI *)
      simpl.
      invert Hbody.
      specialize (IHbody (S x) (get_bsort s :: bs) v b_v KType).
      simpl in *.
      repeat rewrite fuse_lift1_lift2 in *.
      repeat rewrite shift0_i_i_shift_0.
      repeat rewrite fuse_lift2_lift2_1 in *.
      rewrite subst_lift2.
      rewrite fuse_lift3_lift2_3.
      repeat rewrite get_bsort_subst_i_s in *.
      eapply forall_lift2_lift2_lift4; [|eapply forall_subst_i_s_iff_subst|eapply IHbody]; eauto.
      simpl; intros; subst.
      repeat rewrite convert_kind_value_refl_eq in *.
      Lemma TVEQuanISubset' q b p t p' t' :
        ForSome (fun p p' => forall x, p x <-> p' x) p p' ->
        (forall x, tyveq (t x) (t' x)) ->
        tyveq (@TVQuanI q b p t) (@TVQuanI q b p' t').
      Proof.
        induct 1; simpl; eauto.
      Qed.

      eapply TVEQuanISubset'; eauto.
    }
    {
      (* Case Rec *)
      simpl.
      invert Hbody.
      repeat rewrite fuse_lift1_lift2 in *.
      repeat rewrite fuse_lift2_lift2_1 in *.
      rewrite subst_lift2.
      rewrite fuse_lift3_lift2_3.
      eapply forall_lift2_lift2_lift4; [|eapply IHbody|eapply forall_interp_idx_args_subst_i_i_iff_subst]; eauto.
      simpl; intros; subst.
      repeat rewrite convert_kind_value_refl_eq in *.
      econstructor; eauto.
      intros y.
  Lemma gtyveq_tyveq_uncurrys : forall bs f f', gtyveq bs f f' -> forall x, tyveq (uncurrys bs f x) (uncurrys bs f' x).
  Proof.
    induct bs; simpl; eauto; intros f f' H; eauto.
  Qed.

      eapply gtyveq_tyveq_uncurrys; eauto.
    }
  Qed.

  Lemma forall_lift3_lift4_4_2_3 :
    forall bs A1 A2 A3 A4 P1 P2 P3 P4 (f1 : A4 -> A2 -> A3 -> Prop) (f2 : A1 -> A2 -> A3 -> A4 -> Prop),
      (forall a1 a2 a3 a4, f1 a4 a2 a3 -> f2 a1 a2 a3 a4) ->
      forall_ bs (lift3 bs f1 P4 P2 P3) ->
      forall_ bs (lift4 bs f2 P1 P2 P3 P4).
  Proof.
    induct bs; simplify; eauto.
    rewrite fuse_lift1_lift3 in *.
    rewrite fuse_lift1_lift4 in *.
    eapply IHbs; eauto.
    simplify.
    eauto.
  Qed.
  
  Lemma tyeq_TQuan L q k t t' :
    tyeq L t t' KType ->
    (* wellscoped_ss L -> *)
    tyeq L (TQuan q k t) (TQuan q k t') KType.
  Proof.
    intros H (* HL *).
    unfold tyeq in *.
    simpl in *.
    repeat rewrite fuse_lift1_lift1 in *.
    repeat rewrite fuse_lift3_lift1_2 in *.
    repeat rewrite fuse_lift3_lift1_3 in *.
    eapply forall_lift3_lift3; eauto.
    simpl; intros.
    repeat rewrite convert_kind_value_refl_eq in *.
    eauto.
  Qed.

  Lemma fuse_lift5_lift0_4 bs :
    forall T A1 A2 A3 A4 A5 (f : A1 -> A2 -> A3 -> A4 -> A5 -> T) (g : A4) a1 a2 a3 a5,
      lift5 bs f a1 a2 a3 (lift0 bs g) a5 = lift4 bs (fun a1 a2 a3 a5 => f a1 a2 a3 g a5) a1 a2 a3 a5.
  Proof.
    induct bs; simplify; eauto.
    eapply IHbs.
  Qed.
  
  Lemma fuse_lift4_lift0_2 bs :
    forall T A1 A2 A3 A4 (f : A1 -> A2 -> A3 -> A4 -> T) (g : A2) a1 a3 a4,
      lift4 bs f a1 (lift0 bs g) a3 a4 = lift3 bs (fun a1 a3 a4 => f a1 g a3 a4) a1 a3 a4.
  Proof.
    induct bs; simplify; eauto.
    eapply IHbs.
  Qed.
  
  Lemma fuse_lift5_lift1_4 bs :
    forall T A1 A2 A3 A4 A5 B1 (f : A1 -> A2 -> A3 -> A4 -> A5 -> T) (g : B1 -> A4) a1 a2 a3 b1 a5,
      lift5 bs f a1 a2 a3 (lift1 bs g b1) a5 = lift5 bs (fun a1 a2 a3 b1 a5 => f a1 a2 a3 (g b1) a5) a1 a2 a3 b1 a5.
  Proof.
    induct bs; simplify; eauto.
    eapply IHbs.
  Qed.
  
  Lemma fuse_lift5_lift1_2 bs :
    forall T A1 A2 A3 A4 A5 B1 (f : A1 -> A2 -> A3 -> A4 -> A5 -> T) (g : B1 -> A2) a1 a3 a4 a5 b1,
      lift5 bs f a1 (lift1 bs g b1) a3 a4 a5 = lift5 bs (fun a1 b1 a3 a4 a5 => f a1 (g b1) a3 a4 a5) a1 b1 a3 a4 a5.
  Proof.
    induct bs; simplify; eauto.
    eapply IHbs.
  Qed.
  
  Lemma forall_lift3_lift4_lift2_lift5 :
    forall bs A1 A2 A3 A4 A5 A6 P1 P2 P3 P4 P5 P6 (f1 : _ -> _ -> _ -> Prop) (f2 : _ -> _ -> _ -> _ -> Prop) (f3 : _ -> _ -> Prop) (f4 : _ -> _ -> _ -> _ -> _ -> Prop),
      (forall (a1 : A1) (a2 : A2) (a3 : A3) (a4 : A4) (a5 : A5) (a6 : A6), f1 a6 a2 a4 -> f2 a2 a6 a3 a5 -> f3 a6 a1 -> f4 a1 a2 a3 a4 a5) ->
      forall_ bs (lift3 bs f1 P6 P2 P4) ->
      forall_ bs (lift4 bs f2 P2 P6 P3 P5) ->
      forall_ bs (lift2 bs f3 P6 P1) ->
      forall_ bs (lift5 bs f4 P1 P2 P3 P4 P5).
  Proof.
    induct bs; simplify; eauto.
    rewrite fuse_lift1_lift3 in *.
    rewrite fuse_lift1_lift5 in *.
    rewrite fuse_lift1_lift2 in *.
    rewrite fuse_lift1_lift4 in *.
    eapply IHbs; eauto.
    simplify.
    eauto.
  Qed.
  
  Lemma tyeq_TQuanI L q s t s' t' :
    sorteq L s s' ->
    tyeq (s :: L) t t' KType ->
    wellscoped_ss L ->
    tyeq L (TQuanI q s t) (TQuanI q s' t') KType.
  Proof.
    intros Hss' H HL.
    unfold tyeq in *.
    simpl in *.
    repeat rewrite fuse_lift1_lift2 in *.
    repeat rewrite fuse_lift1_lift3 in *.
    repeat rewrite fuse_lift3_lift2_2 in *.
    repeat rewrite fuse_lift4_lift2_4 in *.
    set (bs := map get_bsort L) in *.
    set (ps := and_all (strip_subsets L)) in *.
    specialize (@forall_shift_i_p_iff_shift ps [get_bsort s] 0 bs 1); intros Hshift.
    simpl in *.
    repeat rewrite fuse_lift1_lift2 in *.
    repeat rewrite fuse_lift2_lift1_2 in *.
    assert (Hps : wellscoped_p (length bs) ps).
    {
      eapply wellscoped_ss_wellscoped_p_strip_subsets; eauto.
      subst bs; rewrite map_length; eauto.
    }
    invert Hss'; simpl in *.
    {
      unfold shift0_i_p in *.
      rewrite and_all_map_shift_i_p in *.
      rewrite dedup_lift5_2_4.
      rewrite fuse_lift4_lift0_2.
      eapply forall_lift3_lift2_lift3; [| eapply H | eapply Hshift]; eauto.
      simpl; intros.
      repeat rewrite convert_kind_value_refl_eq in *.
      econstructor; eauto.
      intros x.
      specialize (H0 x).
      specialize (H1 x).
      propositional.
    }
    {
      rewrite fuse_lift3_lift2_1 in *.
      unfold interp_prop in *.
      simpl in *.
      repeat rewrite fuse_lift1_lift2 in *.
      repeat rewrite fuse_lift2_lift2_2 in *.
      unfold shift0_i_p in *.
      rewrite and_all_map_shift_i_p in *.
      rewrite fuse_lift5_lift1_2.
      rewrite fuse_lift5_lift1_4.
      eapply forall_lift3_lift4_lift2_lift5 ; [| eapply H0 | eapply H | eapply Hshift]; eauto.
      simpl; intros.
      repeat rewrite convert_kind_value_refl_eq in *.
      econstructor; eauto.
      {
        intros x.
        specialize (H1 x).
        specialize (H3 x).
        propositional.
      }
      {
        intros x.
        specialize (H1 x).
        specialize (H2 x).
        specialize (H3 x).
        propositional.
      }
    }
  Qed.

  Lemma bwfsort_wellscoped_s' L s n :
    bwfsort L s ->
    n = length L ->
    wellscoped_s n s.
  Proof.
    intros; subst; eapply bwfsort_wellscoped_s; eauto.
  Qed.
  
  Arguments interp_idx_arg bs p / .
    
  Lemma Forall2_interp_idx_args_eq :
    forall args args' L,
      Forall2 (fun p p' => fst p = fst p' /\ idxeq L (snd p) (snd p') (fst p)) args args' ->
      let bs := map get_bsort L in
      forall_ bs (lift3 bs (fun (p : Prop) args args' => p -> args = args') (interp_p bs (and_all (strip_subsets L))) (lift_ls bs (interp_idx_arg bs) args) (lift_ls bs (interp_idx_arg bs) args')).
  Proof.
    unfold idxeq, interp_prop.
    simpl.
    induct 1; simpl; eauto.
    {
      rewrite fuse_lift3_lift0_2.
      rewrite fuse_lift2_lift0_2.
      eapply forall_lift1.
      eauto.
    }
    destruct x as (b1 & i1).
    destruct y as (b2 & i2).
    simpl in *.
    invert H.
    repeat rewrite fuse_lift2_lift1_1 in *.
    rewrite fuse_lift3_lift2_2.
    rewrite fuse_lift4_lift2_4.
    rewrite fuse_lift2_lift2_2 in *.
    eapply forall_lift3_lift3_lift5_2_4_3_5; [| eapply H2 | eapply IHForall2]; eauto.
    simpl; intros.
    specialize (H H3).
    specialize (H1 H3).
    subst.
    eauto.
  Qed.

  Lemma tyeq_TRec L t k args t' args' :
    tyeq L t t' k ->
    Forall2 (fun p p' => fst p = fst p' /\ idxeq L (snd p) (snd p') (fst p)) args args' ->
    tyeq L (TRec k t args) (TRec k t' args') KType.
  Proof.
    intros Hss' H (* HL *).
    unfold tyeq in *.
    simpl in *.
    repeat rewrite fuse_lift1_lift2 in *.
    repeat rewrite fuse_lift3_lift2_2 in *.
    repeat rewrite fuse_lift4_lift2_4 in *.
    unfold interp_idx_args in *.
    
    eapply Forall2_interp_idx_args_eq in H.
    eapply forall_lift3_lift3_lift5_2_4_3_5; [| eapply Hss' | eapply H]; eauto.
    simpl; intros.
    repeat rewrite convert_kind_value_refl_eq in *.
    specialize (H1 H2).
    subst.
    econstructor; eauto.
    intros x.
    eapply gtyveq_tyveq_uncurrys; eauto.
  Qed.

  Lemma tyeq2_tyeq L t t' k :
    tyeq2 L t t' k ->
    wellscoped_ss L ->
    bkinding (map get_bsort L) t k ->
    bkinding (map get_bsort L) t' k ->
    tyeq L t t' k.
  Proof.
    induct 1; intros HL Ht Ht'; simpl.
    {
      invert Ht.
      invert Ht'.
      eapply tyeq_TUnOp; eauto.
    }
    {
      invert Ht.
      invert Ht'.
      eapply tyeq_TBinOp; eauto.
    }
    {
      invert Ht.
      invert Ht'.
      eapply tyeq_TArrow; eauto.
    }
    {
      invert Ht.
      invert Ht'.
      eapply tyeq_TAbs; eauto.
    }
    {
      invert Ht.
      invert Ht'.
      eapply tyeq_TApp; eauto.
    }
    {
      (* Case TyEqBeta *)
      invert Ht.
      invert H4.
      unfold tyeq in *.
      unfold subst0_i_t.
      simpl.
      repeat rewrite fuse_lift3_lift2_2 in *.
      set (bs := map get_bsort L) in *.
      set (ps := and_all (strip_subsets L)) in *.
      specialize (@forall_subst_i_t_iff_subst t 0 (b :: bs) i b k); intros Hsubst.
      simpl in *.
      rewrite shift_i_i_0 in *.
      rewrite fuse_lift2_lift2_2 in *.
      eapply forall_lift3_lift4_4_2_3; [| eapply Hsubst]; eauto.
      unfold apply.
      simpl; eauto; intros.
      repeat rewrite convert_sort_value_refl_eq in *.
      subst.
      eauto using gtyveq_sym.
    }
    {
      invert Ht.
      invert Ht'.
      eapply tyeq_TQuan; eauto.
    }
    {
      invert Ht.
      invert Ht'.
      simpl in *.
      eapply tyeq_TQuanI; eauto.
      eapply IHtyeq2; eauto.
      {
        econstructor; eauto.
        eapply bwfsort_wellscoped_s'; eauto.
        rewrite map_length in *.
        eauto.
      }
      {
        eapply sorteq_get_bsort in H.
        rewrite <- H.
        eauto.
      }
    }
    {
      invert Ht.
      invert Ht'.
      eapply tyeq_TRec; eauto.
      eapply IHtyeq2; eauto.
      subst k2.
      rewrite <- H2.
      eauto.
    }
    {
      eauto using tyeq_refl.
    }
    {
      eauto using tyeq_sym.
    }
    {
      eauto using tyeq_trans.
    }
  Qed.
  
  Definition map_fst {A B C} (f : A -> C) (p : A * B) := (f (fst p), snd p).

  Arguments length {_} _ .
  Arguments map_fst {_ _ _} _ _ / .
  
  Lemma equal_sorts_sorteq L k1 k2 :
    sorteq L k1 k2 ->
    forall L',
      equal_sorts L L' ->
      wellscoped_ss L ->
      wellscoped_ss L' ->
      sorteq L' k1 k2.
  Proof.
    induct 1; simpl; eauto.
    intros L' Hek HL HL'.
    econstructor; eauto.
    eapply equal_sorts_interp_prop; eauto using sorteq_refl.
  Qed.
  
  Lemma equal_sorts_refl L : equal_sorts L L.
  Proof.
    induct L; simpl; eauto using sorteq_refl.
  Qed.
  
(*    
    Lemma sorteq_tyeq' L t1 t2 k :
      tyeq L t1 t2 k ->
      forall L',
        equal_sorts L L' ->
        tyeq L' t1 t2 k.
    Proof.
      induct 1; simpl; eauto using sorteq_refl, equal_sorts_sorteq, equal_sorts_interp_prop.
    Qed.

    Lemma sorteq_tyeq L k k' t t' :
      sorteq L k k' ->
      tyeq (k :: L) t t' ->
      tyeq (k' :: L) t t'.
    Proof.
      eauto using sorteq_tyeq', equal_sorts_refl.
    Qed.

*)
  Definition isSome A (a : option A) :=
    match a with
    | Some _ => true
    | None => false
    end.
  Arguments isSome {_} _ / .
  
  Lemma isSome_option_map A B (f : A -> B) a :
    isSome (option_map f a) = isSome a.
  Proof.
    destruct a; simpl; eauto.
  Qed.

(*  
  Lemma shift_c_c_0_tyeq :
    forall L'' n L' c1 c2,
      tyeq L' c1 c2 ->
      n = length L'' ->
      tyeq (L'' ++ L') (shift_c_c n 0 c1) (shift_c_c n 0 c2).
  Proof.
    eapply admit.
  Qed.
*)  

  (*
          Lemma shift_c_c_0_interp_idx_eq :
            forall L'' n L' c1 c2 s,
              interp_idx c1 L' s = interp_idx c2 L' s ->
              n = length L'' ->
              interp_idx (shift_c_c n 0 c1) (L'' ++ L') s = interp_idx (shift_c_c n 0 c2) (L'' ++ L') s.
          Admitted.
*)
  Lemma map_eq_nth_error A1 A2 B (f1 : A1 -> B) (f2 : A2 -> B) :
    forall ls1 ls2 x a2,
      nth_error ls2 x = Some a2 ->
      map f1 ls1 = map f2 ls2 ->
      exists a1,
        nth_error ls1 x = Some a1 /\
        f1 a1 = f2 a2.
  Proof.
    induct ls1; destruct ls2; simpl; try solve [intros; try rewrite nth_error_nil in *; discriminate | eauto].
    intros x a2 Hnth Hmap.
    invert Hmap.
    destruct x as [|x]; simpl in *.
    {
      invert Hnth.
      repeat eexists_split; eauto.
    }
    {
      eauto.
    }
  Qed.
      
  Lemma app_1_neq_nil A ls (a : A) : ls ++ [a] = [] -> False.
  Proof.
    destruct ls; simpl; discriminate.
  Qed.
  Ltac app_1_neq_nil := exfalso; eapply app_1_neq_nil; eauto.
  
  Ltac not_not :=
    match goal with
    | H : ~ _ |- ~ _ => unfold not; intro; contradict H
    end.
  
  Lemma Forall2_map A1 B1 A2 B2 (P : A1 -> A2 -> Prop) (Q : B1 -> B2 -> Prop) f1 f2 :
    (forall a1 a2, P a1 a2 -> Q (f1 a1) (f2 a2)) ->
    forall ls1 ls2,
      Forall2 P ls1 ls2 ->
      Forall2 Q (map f1 ls1) (map f2 ls2).
  Proof.
    induct 2; simpl; eauto.
  Qed.

(*  
  Lemma interp_idx_interp_prop_eq L' a b :
    interp_idx a (map kind_to_sort L') BSTime = interp_idx b (map kind_to_sort L') BSTime -> interp_prop L' (a == b)%idx.
  Admitted.
  
          Lemma interp_prop_BinConn_iff L' opr p1 p2 p1' p2' :
            interp_prop L' (p1 <===> p1')%idx ->
            interp_prop L' (p2 <===> p2')%idx ->
            interp_prop L' (PBinConn opr p1 p2 <===> PBinConn opr p1' p2')%idx.
          Admitted.
          
          Lemma interp_prop_Not_iff L' p p' :
            interp_prop L' (p <===> p')%idx ->
            interp_prop L' (PNot p <===> PNot p')%idx.
          Admitted.
  
          Lemma interp_prop_BinPred_iff L' opr i1 i2 i1' i2' :
            interp_idx i1 (map kind_to_sort L') (binpred_arg1_sort opr) = interp_idx i1' (map kind_to_sort L') (binpred_arg1_sort opr) ->
            interp_idx i2 (map kind_to_sort L') (binpred_arg2_sort opr) = interp_idx i2' (map kind_to_sort L') (binpred_arg2_sort opr) ->
            interp_prop L' (PBinPred opr i1 i2 <===> PBinPred opr i1' i2')%idx.
          Admitted.
  
          Lemma interp_prop_Quan_iff L' q s p p' :
            interp_prop (KBaseSort s :: L') (p <===> p')%idx ->
            interp_prop L' (PQuan q s p <===> PQuan q s p')%idx.
          Admitted.
  
        Lemma interp_prop_eq_interp_idx L a b :
          interp_prop L (a == b)%idx -> interp_idx a (map kind_to_sort L) BSTime = interp_idx b ((map kind_to_sort L)) BSTime.
        Admitted.
 *)
  
  Hint Resolve tyeq_refl tyeq_sym tyeq_trans interp_prop_le_refl interp_prop_le_trans : db_tyeq.

(*  
  Lemma kinding_tyeq L k t1 t2 :
    kinding L t1 k ->
    tyeq L t1 t2 ->
    kinding L t2 k.
  Admitted.
  
  Lemma monotone_subst_c_c x v b :
    monotone b ->
    monotone (subst_c_c x v b).
  Admitted.
  
  Lemma tyeq_shift0_c_c L c c' k :
    tyeq L c c' ->
    tyeq (k :: L) (shift0_c_c c) (shift0_c_c c').
  Admitted.
  
  Lemma tyeq_subst0_c_c k L v b v' b' :
    tyeq L v v' ->
    tyeq (k :: L) b b' ->
    tyeq L (subst0_c_c v b) (subst0_c_c v' b').
  Admitted.
  
  Lemma tyeq_shift_c_c L c1 c2 :
    tyeq L c1 c2 ->
    forall x ls ,
      let n := length ls in
      x <= length L ->
      tyeq (shift_c_ks n (firstn x L) ++ ls ++ my_skipn L x) (shift_c_c n x c1) (shift_c_c n x c2).
  Admitted.
  Lemma tyeq_subst_c_c L c1' c2' :
    tyeq L c1' c2' ->
    forall n k c1 c2 ,
      nth_error L n = Some k ->
      kinding (my_skipn L (1 + n)) c1 k ->
      kinding (my_skipn L (1 + n)) c2 k ->
      tyeq (my_skipn L (1 + n)) c1 c2 ->
      tyeq (subst_c_ks c1 (firstn n L) ++ my_skipn L (1 + n)) (subst_c_c n (shift_c_c n 0 c1) c1') (subst_c_c n (shift_c_c n 0 c2) c2').
  Admitted.
  
  Lemma sorteq_shift_c_k L k1 k2 :
    sorteq L k1 k2 ->
    forall x ls ,
      let n := length ls in
      x <= length L ->
      sorteq (shift_c_ks n (firstn x L) ++ ls ++ my_skipn L x) (shift_c_k n x k1) (shift_c_k n x k2).
  Proof.
    induct 1; simpl; 
      (* try rename x into x'; *)
      intros x ls Hle;
      simplify;
      cbn in *;
      try solve [cbn in *; econstructor; eauto].
    {
      (* Case Subset *)
      econstructor; eauto.
      specialize (@interp_prop_shift_c_p (k :: L) (p <===> p')%idx H0 (S x) ls); intros HH.
      simplify; cbn in *.
      repeat erewrite length_firstn_le in * by la.
      eauto with db_la.
    }
  Qed.
  
  Lemma sorteq_subst_c_k L k1 k2 :
    sorteq L k1 k2 ->
    forall n k c ,
      nth_error L n = Some k ->
      kinding (my_skipn L (1 + n)) c k ->
      sorteq (subst_c_ks c (firstn n L) ++ my_skipn L (1 + n)) (subst_c_k n (shift_c_c n 0 c) k1) (subst_c_k n (shift_c_c n 0 c) k2).
  Proof.
    induct 1;
      try rename n into n';
      try rename k into k'';
      try rename c into c';
      intros n k c Hnth Hkd;
      simplify;
      try solve [econstructor; eauto].
    {
      (* Case Subset *)
      econstructor; eauto.
      specialize (@interp_prop_subst_c_p (k'' :: L) (p <===> p')%idx H0 (S n) k c); intros HH.
      simplify.
      repeat erewrite nth_error_length_firstn in * by eauto.
      repeat rewrite shift0_c_c_shift_0.
      simplify.
      eauto with db_la.
    }
  Qed.
  
  Lemma kd_wfkind_wfprop_shift_c_c :
    (forall L c k,
        kinding L c k ->
        forall x ls,
          let n := length ls in
          x <= length L ->
          kinding (shift_c_ks n (firstn x L) ++ ls ++ my_skipn L x) (shift_c_c n x c) (shift_c_k n x k)) /\
    (forall L k,
        wfkind L k ->
        forall x ls,
          let n := length ls in
          x <= length L ->
          wfkind (shift_c_ks n (firstn x L) ++ ls ++ my_skipn L x) (shift_c_k n x k)) /\
    (forall L p,
        wfprop L p ->
        forall x ls,
          let n := length ls in
          x <= length L ->
          wfprop (shift_c_ks n (firstn x L) ++ ls ++ my_skipn L x) (shift_c_p n x p))
  .
  Proof.
    eapply kinding_wfkind_wfprop_mutind;
      simplify; cbn in *; try solve [econstructor; eauto].
    {
      (* Case Var *)
      copy H HnltL.
      eapply nth_error_Some_lt in HnltL.
      rename x0 into y.
      cases (y <=? x).
      {
        eapply KdEq.
        {
          eapply KdVar.
          rewrite nth_error_app2;
            rewrite length_shift_c_ks; erewrite length_firstn_le; try la.
          rewrite nth_error_app2 by la.
          rewrite nth_error_my_skipn by la.
          erewrite <- H.
          f_equal.
          la.
        }
        eapply sorteq_refl2.
        rewrite shift_c_k_shift_0 by la.
        simplify.
        f_equal.
        la.
      }
      {
        eapply KdEq.
        {
          eapply KdVar.
          rewrite nth_error_app1;
            try rewrite length_shift_c_ks; try erewrite length_firstn_le; try la.
          erewrite nth_error_shift_c_ks; eauto.
          rewrite nth_error_firstn; eauto.
        }
        eapply sorteq_refl2.
        erewrite length_firstn_le by la.
        rewrite shift_c_k_shift_2 by la.
        eauto.
      }
    }
    {
      (* Case Const *)
      cases cn; simplify; econstructor.
    }
    {
      (* Case BinOp *)
      rewrite shift_c_k_cbinop_result_kind.
      rename H0 into IHkinding1.
      rename H2 into IHkinding2.
      specialize (IHkinding1 x ls).
      rewrite shift_c_k_cbinop_arg1_kind in *.
      specialize (IHkinding2 x ls).
      rewrite shift_c_k_cbinop_arg2_kind in *.
      eapply KdBinOp; eauto.
    }
    {
      (* Case Abs *)
      econstructor; eauto.
      rename H2 into IHkinding.
      specialize (IHkinding (S x) ls).
      simplify.
      repeat erewrite length_firstn_le in * by la.
      rewrite shift_c_k_shift_2 in * by la.
      simplify.
      repeat rewrite Nat.sub_0_r in *.
      eauto with db_la.
    }
    {
      (* Case TimeAbs *)
      econstructor; eauto.
      {
        rename H0 into IHkinding.
        eapply IHkinding with (x := S x).
        la.
      }
      eapply monotone_shift_c_c; eauto.
    }
    {
      (* Case Quan *)
      econstructor; eauto.
      {
        rename H0 into IHwfkind.
        eapply IHwfkind; eauto.
      }
      rename H2 into IHkinding.
      specialize (IHkinding (S x) ls).
      simplify.
      repeat erewrite length_firstn_le in * by eauto.
      eauto with db_la.
    }
    {
      (* Case Rec *)
      econstructor; eauto.
      rename H2 into IHkinding.
      specialize (IHkinding (S x) ls).
      simplify.
      repeat erewrite length_firstn_le in * by eauto.
      rewrite shift_c_k_shift_2 in * by la.
      simplify.
      repeat rewrite Nat.sub_0_r in *.
      eauto with db_la.
    }
    {
      (* Case Eq *)
      econstructor; eauto.
      eapply sorteq_shift_c_k; eauto with db_tyeq.
    }
    {
      (* Case Subset *)
      econstructor; eauto.
      rename H2 into IHwfprop.
      specialize (IHwfprop (S x) ls).
      simplify.
      repeat erewrite length_firstn_le in * by eauto.
      eauto with db_la.
    }
    {
      (* Case BinPred *)
      rename H0 into IHwfprop1.
      rename H2 into IHwfprop2.
      specialize (IHwfprop1 x ls).
      rewrite shift_c_k_binpred_arg1_kind in *.
      specialize (IHwfprop2 x ls).
      rewrite shift_c_k_binpred_arg2_kind in *.
      econstructor; eauto.
    }
    {
      (* Case PQuan *)
      econstructor; eauto.
      rename H0 into IHwfprop.
      specialize (IHwfprop (S x) ls).
      simplify.
      repeat erewrite length_firstn_le in * by eauto.
      eauto with db_la.
    }
  Qed.

  Lemma kd_shift_c_c :
    forall L c k,
      kinding L c k ->
      forall x ls,
        let n := length ls in
        x <= length L ->
        kinding (shift_c_ks n (firstn x L) ++ ls ++ my_skipn L x) (shift_c_c n x c) (shift_c_k n x k).
  Proof.
    eapply kd_wfkind_wfprop_shift_c_c.
  Qed.
  
  Lemma wfkind_shift_c_k :
    forall L k,
      wfkind L k ->
      forall x ls,
        let n := length ls in
        x <= length L ->
        wfkind (shift_c_ks n (firstn x L) ++ ls ++ my_skipn L x) (shift_c_k n x k).
  Proof.
    eapply kd_wfkind_wfprop_shift_c_c.
  Qed.
  
  Lemma wfkind_shift_c_p :
    forall L p,
      wfprop L p ->
      forall x ls,
        let n := length ls in
        x <= length L ->
        wfprop (shift_c_ks n (firstn x L) ++ ls ++ my_skipn L x) (shift_c_p n x p).
  Proof.
    eapply kd_wfkind_wfprop_shift_c_c.
  Qed.
  
  Lemma kd_wfkind_wfprop_subst_c_c :
    (forall L c' k',
        kinding L c' k' ->
        forall n k c ,
          nth_error L n = Some k ->
          kinding (my_skipn L (1 + n)) c k ->
          kinding (subst_c_ks c (firstn n L) ++ my_skipn L (1 + n)) (subst_c_c n (shift_c_c n 0 c) c') (subst_c_k n (shift_c_c n 0 c) k')) /\
    (forall L k',
        wfkind L k' ->
        forall n k c ,
          nth_error L n = Some k ->
          kinding (my_skipn L (1 + n)) c k ->
          wfkind (subst_c_ks c (firstn n L) ++ my_skipn L (1 + n)) (subst_c_k n (shift_c_c n 0 c) k')) /\
    (forall L p,
        wfprop L p ->
        forall n k c ,
          nth_error L n = Some k ->
          kinding (my_skipn L (1 + n)) c k ->
          wfprop (subst_c_ks c (firstn n L) ++ my_skipn L (1 + n)) (subst_c_p n (shift_c_c n 0 c) p)).
  Proof.
    eapply kinding_wfkind_wfprop_mutind;
      simplify; try solve [econstructor; eauto].
    {
      (* Case Var *)
      copy H0 HnltL.
      eapply nth_error_Some_lt in HnltL.
      cases (x <=>? n).
      {
        rewrite subst_c_k_shift by la.
        econstructor.
        rewrite nth_error_app1.
        {
          erewrite nth_error_subst_c_ks.
          {
            repeat erewrite nth_error_length_firstn by eauto.
            eauto.
          }
          rewrite nth_error_firstn by la.
          eauto.
        }
        rewrite length_subst_c_ks.
        repeat erewrite nth_error_length_firstn by eauto.
        eauto.
      }
      {
        subst.
        rewrite H0 in H.
        invert H.
        rewrite subst_c_k_shift_0_avoid by la.
        simplify.
        repeat rewrite Nat.sub_0_r in *.
        eapply kd_shift_c_c with (x := 0) (ls := subst_c_ks c (firstn n L)) in H1; try la.
        rewrite length_subst_c_ks in *.
        repeat erewrite nth_error_length_firstn in * by eauto.
        simplify.
        rewrite my_skipn_0 in *.
        eapply H1.
      }
      {
        rewrite subst_c_k_shift_0_avoid by la.
        simplify.
        repeat rewrite Nat.sub_0_r in *.
        destruct x as [| x]; simplify; try la.
        repeat rewrite Nat.sub_0_r in *.
        eapply KdVar.
        rewrite nth_error_app2; repeat rewrite length_subst_c_ks in *.
        {
          rewrite nth_error_my_skipn; repeat erewrite nth_error_length_firstn by eauto; try la.
          replace (S n + (x - n)) with (S x); eauto.
          la.
        }
        {
          repeat erewrite nth_error_length_firstn by eauto.
          la.
        }
      }
    }
    {
      (* Case Const *)
      cases cn; simplify; econstructor.
    }
    {
      (* Case BinOp *)
      rewrite subst_c_k_cbinop_result_kind.
      rename H0 into IHkinding1.
      rename H2 into IHkinding2.
      specialize (IHkinding1 n k c).
      rewrite subst_c_k_cbinop_arg1_kind in *.
      specialize (IHkinding2 n k c).
      rewrite subst_c_k_cbinop_arg2_kind in *.
      eapply KdBinOp; eauto.
    }
    {
      (* Case Abs *)
      rewrite shift0_c_c_shift_0.
      econstructor; eauto.
      rename H2 into IHkinding.
      specialize (IHkinding (S n) k c0).
      simplify.
      repeat erewrite nth_error_length_firstn in * by eauto.
      rewrite subst_c_k_shift in * by la.
      simplify.
      repeat rewrite Nat.sub_0_r in *.
      eauto.
    }
    {
      (* Case TimeAbs *)
      rewrite shift0_c_c_shift_0.
      econstructor; eauto.
      {
        rename H0 into IHkinding.
        eapply IHkinding with (n0 := S n0); eauto.
      }
      eapply monotone_subst_c_c; eauto.
    }
    {
      (* Case Quan *)
      rewrite shift0_c_c_shift_0.
      econstructor; eauto.
      rename H2 into IHkinding.
      specialize (IHkinding (S n) k0 c0).
      simplify.
      repeat erewrite nth_error_length_firstn in * by eauto.
      eauto.
    }
    {
      (* Case Rec *)
      rewrite shift0_c_c_shift_0.
      econstructor; eauto.
      rename H2 into IHkinding.
      specialize (IHkinding (S n) k0 c0).
      simplify.
      repeat erewrite nth_error_length_firstn in * by eauto.
      rewrite subst_c_k_shift in * by la.
      simplify.
      repeat rewrite Nat.sub_0_r in *.
      eauto.
    }
    {
      (* Case Eq *)
      econstructor; eauto.
      eapply sorteq_subst_c_k; eauto with db_tyeq.
    }
    {
      (* Case Subset *)
      rewrite shift0_c_c_shift_0.
      econstructor; eauto.
      rename H2 into IHwfprop.
      specialize (IHwfprop (S n) k0 c).
      simplify.
      repeat erewrite nth_error_length_firstn in * by eauto.
      eauto.
    }
    {
      (* Case BinPred *)
      rename H0 into IHwfprop1.
      rename H2 into IHwfprop2.
      specialize (IHwfprop1 n k c).
      rewrite subst_c_k_binpred_arg1_kind in *.
      specialize (IHwfprop2 n k c).
      rewrite subst_c_k_binpred_arg2_kind in *.
      econstructor; eauto.
    }
    {
      (* Case PQuan *)
      rewrite shift0_c_c_shift_0.
      econstructor; eauto.
      rename H0 into IHwfprop.
      specialize (IHwfprop (S n) k c).
      simplify.
      repeat erewrite nth_error_length_firstn in * by eauto.
      eauto.
    }
  Qed.
  
  Lemma kd_subst_c_c :
    forall L c' k',
      kinding L c' k' ->
      forall n k c ,
        nth_error L n = Some k ->
        kinding (my_skipn L (1 + n)) c k ->
        kinding (subst_c_ks c (firstn n L) ++ my_skipn L (1 + n)) (subst_c_c n (shift_c_c n 0 c) c') (subst_c_k n (shift_c_c n 0 c) k').
  Proof.
    eapply kd_wfkind_wfprop_subst_c_c.
  Qed.
    
  Lemma wfkind_subst_c_k :
    forall L k',
      wfkind L k' ->
      forall n k c ,
        nth_error L n = Some k ->
        kinding (my_skipn L (1 + n)) c k ->
        wfkind (subst_c_ks c (firstn n L) ++ my_skipn L (1 + n)) (subst_c_k n (shift_c_c n 0 c) k').
  Proof.
    eapply kd_wfkind_wfprop_subst_c_c.
  Qed.

  Lemma wfprop_subst_c_p :
    forall L p,
      wfprop L p ->
      forall n k c ,
        nth_error L n = Some k ->
        kinding (my_skipn L (1 + n)) c k ->
        wfprop (subst_c_ks c (firstn n L) ++ my_skipn L (1 + n)) (subst_c_p n (shift_c_c n 0 c) p).
  Proof.
    eapply kd_wfkind_wfprop_subst_c_c.
  Qed.
 *)
  
  (*from*)
    
  (* ============================================================= *)
  (* The term language *)
  (* ============================================================= *)
  
  
  Inductive expr_const :=
  | ECTT
  | ECInt (i : int)
  .

  Inductive prim_expr_bin_op :=
  | PEBIntAdd
  .

  Inductive projector :=
  | ProjFst
  | ProjSnd
  .

  Inductive injector :=
  | InjInl
  | InjInr
  .

  Definition loc := nat.

  Definition hctx := fmap loc ty.
  Definition tctx := list ty.
  Definition ctx := (sctx * kctx * hctx * tctx)%type.
  
  Inductive expr_un_op :=
  | EUProj (p : projector)
  | EUInj (inj : injector)
  | EUFold
  | EUUnfold
  | EUNew 
  | EURead 
  .

  Inductive expr_bin_op :=
  | EBPrim (opr : prim_expr_bin_op)
  | EBApp
  | EBPair
  | EBWrite
  .

  Inductive expr :=
  | EVar (x : var)
  | EConst (cn : expr_const)
  | ELoc (l : loc)
  | EUnOp (opr : expr_un_op) (e : expr)
  | EBinOp (opr : expr_bin_op) (e1 e2 : expr)
  | ECase (e e1 e2 : expr)
  | EAbs (e : expr)
  | ERec (e : expr)
  | EAbsT (e : expr)
  | EAppT (e : expr) (t : ty)
  | EAbsI (e : expr)
  | EAppI (e : expr) (i : idx)
  | EPack (t : ty) (e : expr)
  | EUnpack (e1 e2 : expr)
  | EPackI (i : idx) (e : expr)
  | EUnpackI (e1 e2 : expr)
  (* | EAsc (e : expr) (t : cstr) *)
  (* | EAstTime (e : expr) (i : cstr) *)
  .

  Definition EProj p e := EUnOp (EUProj p) e.
  Definition EInj c e := EUnOp (EUInj c) e.
  Definition EFold e := EUnOp EUFold e.
  Definition EUnfold e := EUnOp EUUnfold e.
  Definition ENew e := EUnOp EUNew e.
  Definition ERead e := EUnOp EURead e.

  Definition EApp := EBinOp EBApp.
  Definition EPair := EBinOp EBPair.
  Definition EWrite := EBinOp EBWrite.

  Inductive value : expr -> Prop :=
  (* | VVar x : *)
  (*     value (EVar x) *)
  | VConst cn :
      value (EConst cn)
  | VPair v1 v2 :
      value v1 ->
      value v2 ->
      value (EPair v1 v2)
  | VInj c v :
      value v ->
      value (EInj c v)
  | VAbs e :
      value (EAbs e)
  | VAbsT e :
      value (EAbsT e)
  | VAbsI e :
      value (EAbsI e)
  | VPack c v :
      value v ->
      value (EPack c v)
  | VPackI c v :
      value v ->
      value (EPackI c v)
  | VFold v :
      value v ->
      value (EFold v)
  | VLoc l :
      value (ELoc l)
  .

  Definition EFst := EProj ProjFst.
  Definition ESnd := EProj ProjSnd.
  Definition EInl := EInj InjInl.
  Definition EInr := EInj InjInr.

  Definition ETT := EConst ECTT.

  Definition add_sorting_ctx s (C : ctx) : ctx :=
    match C with
      (L, K, W, G) => (s :: L, K, fmap_map shift0_i_t W, map shift0_i_t G)
    end
  .

  Definition add_kinding_ctx k (C : ctx) :=
    match C with
      (L, K, W, G) => (L, k :: K, fmap_map shift0_t_t W, map shift0_t_t G)
    end
  .

  Definition add_typing_ctx t (C : ctx) :=
    match C with
      (L, K, W, G) => (L, K, W, t :: G)
    end
  .

  Definition get_sctx (C : ctx) : sctx :=
    match C with
      (L, K, W, G) => L
    end.
  Definition get_kctx (C : ctx) : kctx := 
    match C with
      (L, K, W, G) => K
    end.
  Definition get_hctx (C : ctx) : hctx := 
    match C with
      (L, K, W, G) => W
    end.
  Definition get_tctx (C : ctx) : tctx := 
    match C with
      (L, K, W, G) => G
    end.

  Definition proj {A} (p : A * A) pr :=
    match pr with
    | ProjFst => fst p
    | ProjSnd => snd p
    end
  .

  Definition choose {A} (p : A * A) inj :=
    match inj with
    | InjInl => fst p
    | InjInr => snd p
    end
  .

  Definition const_type cn :=
    match cn with
    | ECTT => TUnit
    | ECInt _ => TInt
    end
  .

  Fixpoint EAbsTIs ls e :=
    match ls with
    | [] => e
    | b :: ls =>
      match b with
      | true => EAbsT (EAbsTIs ls e)
      | false => EAbsI (EAbsTIs ls e)
      end
    end
  .

  Local Open Scope idx_scope.

  Definition TForallI := TQuanI QuanForall.
  Definition TExistsI := TQuanI QuanExists.

  Fixpoint TApps t args :=
    match args with
    | nil => t
    | (b, i) :: args => TApps (TApp t b i) args
    end
  .

  Fixpoint is_TApps_TRec t :=
    match t with
    | TApp t b i => 
      match is_TApps_TRec t with
      | Some (k, t, args) => Some (k, t, args ++ [(b, i)])
      | None => None
      end
    | TRec k t args => Some (k, t, args)
    | _ => None
    end.

  Fixpoint contract t := 
    match t with
    | TVar y => TVar y
    | TConst cn => TConst cn
    | TUnOp opr i => TUnOp opr (contract i)
    | TBinOp opr c1 c2 => TBinOp opr (contract c1) (contract c2)
    | TArrow t1 i t2 => TArrow (contract t1) i (contract t2)
    | TAbs b t => TAbs b (contract t)
    | TApp t b i =>
      let t := contract t in
      match is_TApps_TRec t with
      | Some (k, t, args) => TRec k t (args ++ [(b, i)])
      | None => TApp t b i
      end
    | TQuan q k c => TQuan q k (contract c)
    | TQuanI q s c => TQuanI q s (contract c)
    | TRec k t args => TRec k (contract t) args
    end.

  Definition unroll (k : kind) (t : ty) (args : list (bsort * idx)) : ty :=
    let r := subst0_t_t (TRec k t []) t in
    let r := TApps r args in
    contract r.

  Definition TRef := TUnOp TURef.
  
  Inductive typing : ctx -> expr -> ty -> idx -> Prop :=
  | TyVar C x t :
      nth_error (get_tctx C) x = Some t ->
      typing C (EVar x) t T0
  | TyApp C e1 e2 t i1 i2 i t2 :
      typing C e1 (TArrow t2 i t) i1 ->
      typing C e2 t2 i2 ->
      typing C (EApp e1 e2) t (i1 + i2 + T1 + i)
  | TyAbs C e t1 i t :
      kinding (get_sctx C) (get_kctx C) t1 KType ->
      typing (add_typing_ctx t1 C) e t i ->
      typing C (EAbs e) (TArrow t1 i t) T0
  | TyAppT C e t t1 i k :
      typing C e (TForall k t1) i ->
      kinding (get_sctx C) (get_kctx C) t k -> 
      typing C (EAppT e t) (subst0_t_t t t1) i
  | TyAbsT C e t k :
      value e ->
      typing (add_kinding_ctx k C) e t T0 ->
      typing C (EAbsT e) (TForall k t) T0
  | TyAppI C e c t i s :
      typing C e (TForallI s t) i ->
      sorting (get_sctx C) c s -> 
      typing C (EAppI e c) (subst0_i_t c t) i
  | TyAbsI C e t s :
      value e ->
      wfsort (get_sctx C) s ->
      typing (add_sorting_ctx s C) e t T0 ->
      typing C (EAbsI e) (TForallI s t) T0
  | TyRec C e t tis e1 :
      e = EAbsTIs tis (EAbs e1) ->
      kinding (get_sctx C) (get_kctx C) t KType ->
      typing (add_typing_ctx t C) e t T0 ->
      typing C (ERec e) t T0
  | TyFold C e k t cs i :
      let t_rec := TRec k t cs in
      kinding (get_sctx C) (get_kctx C) t_rec KType ->
      typing C e (unroll k t cs) i ->
      typing C (EFold e) t_rec i
  | TyUnfold C e k t cs i :
      typing C e (TRec k t cs) i ->
      typing C (EUnfold e) (unroll k t cs) i
  | TyPack C c e i t1 k :
      kinding (get_sctx C) (get_kctx C) (TExists k t1) KType ->
      kinding (get_sctx C) (get_kctx C) c k ->
      typing C e (subst0_t_t c t1) i ->
      typing C (EPack c e) (TExists k t1) i
  | TyUnpack C e1 e2 t2 i1 i2 t k :
      typing C e1 (TExists k t) i1 ->
      typing (add_typing_ctx t (add_kinding_ctx k C)) e2 (shift0_t_t t2) i2 ->
      typing C (EUnpack e1 e2) t2 (i1 + i2)
  | TyPackI C c e i t1 s :
      kinding (get_sctx C) (get_kctx C) (TExistsI s t1) KType ->
      sorting (get_sctx C) c s ->
      typing C e (subst0_i_t c t1) i ->
      typing C (EPackI c e) (TExistsI s t1) i
  | TyUnpackI C e1 e2 t2 i1 i2 t s :
      typing C e1 (TExistsI s t) i1 ->
      typing (add_typing_ctx t (add_sorting_ctx s C)) e2 (shift0_i_t t2) (shift0_i_i i2) ->
      typing C (EUnpackI e1 e2) t2 (i1 + i2)
  | TyConst C cn :
      typing C (EConst cn) (const_type cn) T0
  | TyPair C e1 e2 t1 t2 i1 i2 :
      typing C e1 t1 i1 ->
      typing C e2 t2 i2 ->
      typing C (EPair e1 e2) (TProd t1 t2) (i1 + i2)
  | TyProj C pr e t1 t2 i :
      typing C e (TProd t1 t2) i ->
      typing C (EProj pr e) (proj (t1, t2) pr) i
  | TyInj C inj e t t' i :
      typing C e t i ->
      kinding (get_sctx C) (get_kctx C) t' KType ->
      typing C (EInj inj e) (choose (TSum t t', TSum t' t) inj) i
  | TyCase C e e1 e2 t i i1 i2 t1 t2 :
      typing C e (TSum t1 t2) i ->
      typing (add_typing_ctx t1 C) e1 t i1 ->
      typing (add_typing_ctx t2 C) e2 t i2 ->
      typing C (ECase e e1 e2) t (i + Tmax i1 i2)
  | TyNew C e t i :
      typing C e t i ->
      typing C (ENew e) (TRef t) i
  | TyRead C e t i :
      typing C e (TRef t) i ->
      typing C (ERead e) t i
  | TyWrite C e1 e2 i1 i2 t :
      typing C e1 (TRef t) i1 ->
      typing C e2 t i2 ->
      typing C (EWrite e1 e2) TUnit (i1 + i2)
  | TyLoc C l t :
      get_hctx C $? l = Some t ->
      typing C (ELoc l) (TRef t) T0
  | TySub C e t2 i2 t1 i1 :
      typing C e t1 i1 ->
      tyeq (get_sctx C) t1 t2 KType ->
      interp_prop (get_sctx C) (i1 <= i2) ->
      typing C e t2 i2 
  .

  Local Close Scope idx_scope.

  Section shift_e.

    Variable n : nat.

    Fixpoint shift_i_e (x : var) (b : expr) : expr :=
      match b with
      | EVar y => EVar y
      | EConst cn => EConst cn
      | ELoc l => ELoc l
      | EUnOp opr e => EUnOp opr (shift_i_e x e)
      | EBinOp opr e1 e2 => EBinOp opr (shift_i_e x e1) (shift_i_e x e2)
      | ECase e e1 e2 => ECase (shift_i_e x e) (shift_i_e x e1) (shift_i_e x e2)
      | EAbs e => EAbs (shift_i_e x e)
      | ERec e => ERec (shift_i_e x e)
      | EAbsT e => EAbsT (shift_i_e x e)
      | EAppT e t => EAppT (shift_i_e x e) (shift_i_t n x t)
      | EAbsI e => EAbsI (shift_i_e (1 + x) e)
      | EAppI e i => EAppI (shift_i_e x e) (shift_i_i n x i)
      | EPack t e => EPack (shift_i_t n x t) (shift_i_e x e)
      | EUnpack e1 e2 => EUnpack (shift_i_e x e1) (shift_i_e x e2)
      | EPackI i e => EPackI (shift_i_i n x i) (shift_i_e x e)
      | EUnpackI e1 e2 => EUnpackI (shift_i_e x e1) (shift_i_e (1 + x) e2)
      end.
    
    Fixpoint shift_t_e (x : var) (b : expr) : expr :=
      match b with
      | EVar y => EVar y
      | EConst cn => EConst cn
      | ELoc l => ELoc l
      | EUnOp opr e => EUnOp opr (shift_t_e x e)
      | EBinOp opr e1 e2 => EBinOp opr (shift_t_e x e1) (shift_t_e x e2)
      | ECase e e1 e2 => ECase (shift_t_e x e) (shift_t_e x e1) (shift_t_e x e2)
      | EAbs e => EAbs (shift_t_e x e)
      | ERec e => ERec (shift_t_e x e)
      | EAbsT e => EAbsT (shift_t_e (1 + x) e)
      | EAppT e t => EAppT (shift_t_e x e) (shift_t_t n x t)
      | EAbsI e => EAbsI (shift_t_e x e)
      | EAppI e i => EAppI (shift_t_e x e) i
      | EPack t e => EPack (shift_t_t n x t) (shift_t_e x e)
      | EUnpack e1 e2 => EUnpack (shift_t_e x e1) (shift_t_e (1 + x) e2)
      | EPackI i e => EPackI i (shift_t_e x e)
      | EUnpackI e1 e2 => EUnpackI (shift_t_e x e1) (shift_t_e x e2)
      end.
    
    Fixpoint shift_e_e (x : var) (b : expr) : expr :=
      match b with
      | EVar y =>
        if x <=? y then
          EVar (n + y)
        else
          EVar y
      | EConst cn => EConst cn
      | ELoc l => ELoc l
      | EUnOp opr e => EUnOp opr (shift_e_e x e)
      | EBinOp opr e1 e2 => EBinOp opr (shift_e_e x e1) (shift_e_e x e2)
      | ECase e e1 e2 => ECase (shift_e_e x e) (shift_e_e (1 + x) e1) (shift_e_e (1 + x) e2)
      | EAbs e => EAbs (shift_e_e (1 + x) e)
      | ERec e => ERec (shift_e_e (1 + x) e)
      | EAbsT e => EAbsT (shift_e_e x e)
      | EAppT e t => EAppT (shift_e_e x e) t
      | EAbsI e => EAbsI (shift_e_e x e)
      | EAppI e i => EAppI (shift_e_e x e) i
      | EPack t e => EPack t (shift_e_e x e)
      | EUnpack e1 e2 => EUnpack (shift_e_e x e1) (shift_e_e (1 + x) e2)
      | EPackI i e => EPackI i (shift_e_e x e)
      | EUnpackI e1 e2 => EUnpackI (shift_e_e x e1) (shift_e_e (1 + x) e2)
      end.
    
  End shift_e.
  
  Definition shift0_i_e := shift_i_e 1 0.
  Definition shift0_t_e := shift_t_e 1 0.
  Definition shift0_e_e := shift_e_e 1 0.
  
  Fixpoint subst_i_e (x : var) (v : idx) (b : expr) : expr :=
    match b with
    | EVar y => EVar y
    | EConst cn => EConst cn
    | ELoc l => ELoc l
    | EUnOp opr e => EUnOp opr (subst_i_e x v e)
    | EBinOp opr e1 e2 => EBinOp opr (subst_i_e x v e1) (subst_i_e x v e2)
    | ECase e e1 e2 => ECase (subst_i_e x v e) (subst_i_e x v e1) (subst_i_e x v e2)
    | EAbs e => EAbs (subst_i_e x v e)
    | ERec e => ERec (subst_i_e x v e)
    | EAbsT e => EAbsT (subst_i_e x v e)
    | EAppT e t => EAppT (subst_i_e x v e) (subst_i_t x v t)
    | EAbsI e => EAbsI (subst_i_e (1 + x) (shift0_i_i v) e)
    | EAppI e i => EAppI (subst_i_e x v e) (subst_i_i x v i)
    | EPack t e => EPack (subst_i_t x v t) (subst_i_e x v e)
    | EUnpack e1 e2 => EUnpack (subst_i_e x v e1) (subst_i_e x v e2)
    | EPackI i e => EPackI (subst_i_i x v i) (subst_i_e x v e)
    | EUnpackI e1 e2 => EUnpackI (subst_i_e x v e1) (subst_i_e (1 + x) (shift0_i_i v) e2)
    end.
  
  Fixpoint subst_t_e (x : var) (v : ty) (b : expr) : expr :=
    match b with
    | EVar y => EVar y
    | EConst cn => EConst cn
    | ELoc l => ELoc l
    | EUnOp opr e => EUnOp opr (subst_t_e x v e)
    | EBinOp opr e1 e2 => EBinOp opr (subst_t_e x v e1) (subst_t_e x v e2)
    | ECase e e1 e2 => ECase (subst_t_e x v e) (subst_t_e x v e1) (subst_t_e x v e2)
    | EAbs e => EAbs (subst_t_e x v e)
    | ERec e => ERec (subst_t_e x v e)
    | EAbsT e => EAbsT (subst_t_e (1 + x) (shift0_t_t v) e)
    | EAppT e t => EAppT (subst_t_e x v e) (subst_t_t x v t)
    | EAbsI e => EAbsI (subst_t_e x (shift0_i_t v) e)
    | EAppI e i => EAppI (subst_t_e x v e) i
    | EPack t e => EPack (subst_t_t x v t) (subst_t_e x v e)
    | EUnpack e1 e2 => EUnpack (subst_t_e x v e1) (subst_t_e (1 + x) (shift0_t_t v) e2)
    | EPackI i e => EPackI i (subst_t_e x v e)
    | EUnpackI e1 e2 => EUnpackI (subst_t_e x v e1) (subst_t_e x (shift0_i_t v) e2)
    end.

  Fixpoint subst_e_e (x : var) (v : expr) (b : expr) : expr :=
    match b with
    | EVar y => 
      match y <=>? x with
      | MyLt _ => EVar y
      | MyEq _ => v
      | MyGt _ => EVar (y - 1)
      end
    | EConst cn => EConst cn
    | ELoc l => ELoc l
    | EUnOp opr e => EUnOp opr (subst_e_e x v e)
    | EBinOp opr e1 e2 => EBinOp opr (subst_e_e x v e1) (subst_e_e x v e2)
    | ECase e e1 e2 => ECase (subst_e_e x v e) (subst_e_e (1 + x) (shift0_e_e v) e1) (subst_e_e (1 + x) (shift0_e_e v) e2)
    | EAbs e => EAbs (subst_e_e (1 + x) (shift0_e_e v) e)
    | ERec e => ERec (subst_e_e (1 + x) (shift0_e_e v) e)
    | EAbsT e => EAbsT (subst_e_e x (shift0_t_e v) e)
    | EAppT e t => EAppT (subst_e_e x v e) t
    | EAbsI e => EAbsI (subst_e_e x (shift0_i_e v) e)
    | EAppI e i => EAppI (subst_e_e x v e) i
    | EPack t e => EPack t (subst_e_e x v e)
    | EUnpack e1 e2 => EUnpack (subst_e_e x v e1) (subst_e_e (1 + x) (shift0_e_e (shift0_t_e v)) e2)
    | EPackI i e => EPackI i (subst_e_e x v e)
    | EUnpackI e1 e2 => EUnpackI (subst_e_e x v e1) (subst_e_e (1 + x) (shift0_e_e (shift0_i_e v)) e2)
    end.
  
  Definition subst0_i_e (v : idx) b := subst_i_e 0 v b.
  Definition subst0_t_e (v : ty) b := subst_t_e 0 v b.
  Definition subst0_e_e v b := subst_e_e 0 v b.

  Inductive ectx :=
  | ECHole
  | ECUnOp (opr : expr_un_op) (E : ectx)
  | ECBinOp1 (opr : expr_bin_op) (E : ectx) (e : expr)
  | ECBinOp2 (opr : expr_bin_op) (v : expr) (E : ectx)
  | ECCase (E : ectx) (e1 e2 : expr)
  | ECAppT (E : ectx) (t : ty)
  | ECAppI (E : ectx) (i : idx)
  | ECPack (t : ty) (E : ectx)
  | ECUnpack (E : ectx) (e : expr)
  | ECPackI (i : idx) (E : ectx)
  | ECUnpackI (E : ectx) (e : expr)
  .

  Inductive plug : ectx -> expr -> expr -> Prop :=
  | PlugHole e :
      plug ECHole e e
  | PlugUnOp E e e' opr :
      plug E e e' ->
      plug (ECUnOp opr E) e (EUnOp opr e')
  | PlugBinOp1 E e e' opr e2 :
      plug E e e' ->
      plug (ECBinOp1 opr E e2) e (EBinOp opr e' e2)
  | PlugBinOp2 E e e' opr v :
      plug E e e' ->
      value v ->
      plug (ECBinOp2 opr v E) e (EBinOp opr v e')
  | PlugCase E e e' e1 e2 :
      plug E e e' ->
      plug (ECCase E e1 e2) e (ECase e' e1 e2)
  | PlugAppT E e e' t :
      plug E e e' ->
      plug (ECAppT E t) e (EAppT e' t)
  | PlugAppI E e e' i :
      plug E e e' ->
      plug (ECAppI E i) e (EAppI e' i)
  | PlugPack E e e' t :
      plug E e e' ->
      plug (ECPack t E) e (EPack t e')
  | PlugUnpack E e e' e2 :
      plug E e e' ->
      plug (ECUnpack E e2) e (EUnpack e' e2)
  | PlugPackI E e e' i :
      plug E e e' ->
      plug (ECPackI i E) e (EPackI i e')
  | PlugUnpackI E e e' e2 :
      plug E e e' ->
      plug (ECUnpackI E e2) e (EUnpackI e' e2)
  .

  Definition heap := fmap loc expr.

  Definition fuel := time_type.

  Definition config := (heap * expr * fuel)%type.

  (* Require Import Reals. *)

  (* Local Open Scope R_scope. *)

  (* Local Open Scope time_scope. *)

  Import OpenScope.

  Inductive astep : config -> config -> Prop :=
  | ABeta h e v t :
      value v ->
      1 <= t ->
      astep (h, EApp (EAbs e) v, t) (h, subst0_e_e v e, t - 1)
  | AUnfoldFold h v t :
      value v ->
      astep (h, EUnfold (EFold v), t) (h, v, t)
  | ARec h e t :
      astep (h, ERec e, t) (h, subst0_e_e (ERec e) e, t)
  | AUnpackPack h c v e t :
      value v ->
      astep (h, EUnpack (EPack c v) e, t) (h, subst0_e_e v (subst0_t_e c e), t)
  | AUnpackPackI h c v e t :
      value v ->
      astep (h, EUnpackI (EPackI c v) e, t) (h, subst0_e_e v (subst0_i_e c e), t)
  | ARead h l t v :
      h $? l = Some v ->
      astep (h, ERead (ELoc l), t) (h, v, t)
  | AWrite h l v t v' :
      value v ->
      h $? l = Some v' ->
      astep (h, EWrite (ELoc l) v, t) (h $+ (l, v), ETT, t)
  | ANew h v t l :
      value v ->
      h $? l = None ->
      astep (h, ENew v, t) (h $+ (l, v), ELoc l, t)
  | ABetaT h e c t :
      astep (h, EAppT (EAbsT e) c, t) (h, subst0_t_e c e, t)
  | ABetaI h e c t :
      astep (h, EAppI (EAbsI e) c, t) (h, subst0_i_e c e, t)
  | AProj h pr v1 v2 t :
      value v1 ->
      value v2 ->
      astep (h, EProj pr (EPair v1 v2), t) (h, proj (v1, v2) pr, t)
  | AMatch h inj v e1 e2 t :
      value v ->
      astep (h, ECase (EInj inj v) e1 e2, t) (h, subst0_e_e v (choose (e1, e2) inj), t)
  .

  Inductive step : config -> config -> Prop :=
  | StepPlug h e1 t h' e1' t' e e' E :
      astep (h, e, t) (h', e', t') ->
      plug E e e1 ->
      plug E e' e1' ->
      step (h, e1, t) (h', e1', t')
  .

  Definition empty_ctx : ctx := ([], [], $0, []).
  Notation "${}" := empty_ctx.

  Definition allocatable (h : heap) := exists l_alloc, forall l, l >= l_alloc -> h $? l = None.
  
  Definition htyping (h : heap) (W : hctx) :=
    (forall l t,
        W $? l = Some t ->
        exists v,
          h $? l = Some v /\
          value v /\
          typing ([], [], W, []) v t T0) /\
    allocatable h.

  Definition ctyping W (s : config) t i :=
    let '(h, e, f) := s in
    typing ([], [], W, []) e t i /\
    htyping h W /\
    interp_time i <= f
  .

  Definition get_expr (s : config) : expr := snd (fst s).
  Definition get_fuel (s : config) : fuel := snd s.

  Definition finished s := value (get_expr s).

  Definition unstuck s :=
    finished s \/
    exists s', step s s'.

  Definition safe s := forall s', step^* s s' -> unstuck s'.

  (* Local Close Scope time_scope. *)

  Import CloseScope.

  Arguments get_sctx _ / .
  Arguments get_kctx _ / .
  Arguments get_hctx _ / .

  Hint Constructors step astep plug value.

  Arguments finished / .
  Arguments get_expr / .


  (* ============================================================= *)
  (* Term language proofs *)
  (* ============================================================= *)

  
  Lemma TyETT C : typing C ETT TUnit T0.
  Proof.
    eapply TyConst.
  Qed.

  Lemma TyTyeq C e t2 i t1 :
    typing C e t1 i ->
    tyeq (get_sctx C) t1 t2 KType ->
    typing C e t2 i.
  Proof.
    intros.
    eapply TySub; eauto.
    eapply interp_prop_le_refl.
  Qed.

  Lemma TyLe C e t i1 i2 :
    typing C e t i1 ->
    interp_prop (get_sctx C) (i1 <= i2)%idx ->
    typing C e t i2.
  Proof.
    intros.
    eapply TySub; eauto.
    eauto with db_tyeq.
  Qed.
  
  Lemma TyIdxEq C e t i1 i2 :
    typing C e t i1 ->
    interp_prop (get_sctx C) (i1 == i2)%idx ->
    typing C e t i2.
  Proof.
    intros.
    eapply TyLe; eauto.
    eapply interp_prop_eq_interp_prop_le; eauto.
  Qed.
  
  Lemma TRec_const_type_false cs k3 t3 cn  :
    tyeq [] (TRec k3 t3 cs) (const_type cn) KType ->
    False.
  Proof.
    cases cn; simplify;
      eapply tyeq_TRec_TConst_false; eauto.
  Qed.

  Lemma const_type_CArrow_false cn t1 i t2 :
    tyeq [] (const_type cn) (TArrow t1 i t2) KType ->
    False.
  Proof.
    intros H.
    unfold tyeq in *.
    simpl in *.
    repeat rewrite convert_kind_value_refl_eq in *.
    specialize (H I).
    destruct cn; simpl in *;
      invert H.
  Qed.

  Lemma subst_i_t_const_type x v cn :
    subst_i_t x v (const_type cn) = const_type cn.
  Proof.
    cases cn; simplify; eauto.
  Qed.
  
  Lemma subst_t_t_const_type x v cn :
    subst_t_t x v (const_type cn) = const_type cn.
  Proof.
    cases cn; simplify; eauto.
  Qed.

  Definition sum_ls := fold_right plus 0.
  
  Lemma shift_i_e_AbsTIs tis :
    forall n x e,
      let m := length (filter negb tis) in
      shift_i_e n x (EAbsTIs tis e) = EAbsTIs tis (shift_i_e n (m + x) e).
  Proof.
    simpl.
    induct tis; simplify; eauto.
    destruct a; simpl.
    {
      f_equal; eauto.
    }
    {
      f_equal; eauto.
      rewrite IHtis.
      f_equal.
      f_equal.
      la.
    }
  Qed.
  
  Lemma shift_t_e_AbsTIs tis :
    forall n x e,
      let m := length (filter id tis) in
      shift_t_e n x (EAbsTIs tis e) = EAbsTIs tis (shift_t_e n (m + x) e).
  Proof.
    simpl.
    induct tis; simplify; eauto.
    destruct a; simpl.
    {
      f_equal; eauto.
      rewrite IHtis.
      f_equal.
      f_equal.
      la.
    }
    {
      f_equal; eauto.
    }
  Qed.
  
  Lemma shift_e_e_AbsTIs m :
    forall n x e,
      shift_e_e n x (EAbsTIs m e) = EAbsTIs m (shift_e_e n x e).
  Proof.
    induct m; simplify; eauto.
    destruct a; simpl;
      rewrite IHm;
      repeat f_equal; eauto.
  Qed.
  
  Lemma shift_i_e_0 b : forall x, shift_i_e 0 x b = b.
  Proof.
    induct b; simplify; try rewrite IHb; try rewrite IHb1; try rewrite IHb2; try rewrite IHb3; try rewrite shift_i_i_0; try rewrite shift_i_t_0; eauto.
  Qed.
  
  Lemma shift_t_e_0 b : forall x, shift_t_e 0 x b = b.
  Proof.
    induct b; simplify; try rewrite IHb; try rewrite IHb1; try rewrite IHb2; try rewrite IHb3; try rewrite shift_t_t_0; eauto.
  Qed.
  
  Lemma shift_i_e_shift b :
    forall n1 n2 x,
      shift_i_e n2 x (shift_i_e n1 x b) = shift_i_e (n1 + n2) x b.
  Proof.
    induct b; simplify; try rewrite IHb; try rewrite IHb1; try rewrite IHb2; try rewrite IHb3; try rewrite shift_i_i_shift_merge by la; try rewrite shift_i_t_shift_merge by la; eauto.
  Qed.
  
  Lemma shift_t_e_shift b :
    forall n1 n2 x,
      shift_t_e n2 x (shift_t_e n1 x b) = shift_t_e (n1 + n2) x b.
  Proof.
    induct b; simplify; try rewrite IHb; try rewrite IHb1; try rewrite IHb2; try rewrite IHb3; try rewrite shift_t_t_shift_merge by la; eauto.
  Qed.
  
  Lemma shift_i_e_shift0 n b :
    shift_i_e n 0 (shift0_i_e b) = shift_i_e (S n) 0 b.
  Proof.
    unfold shift0_i_e.
    rewrite shift_i_e_shift.
    eauto.
  Qed.
  
  Lemma shift_t_e_shift0 n b :
    shift_t_e n 0 (shift0_t_e b) = shift_t_e (S n) 0 b.
  Proof.
    unfold shift0_t_e.
    rewrite shift_t_e_shift.
    eauto.
  Qed.
  
  Lemma shift0_i_t_shift n x b :
    shift0_i_t (shift_i_t n x b) = shift_i_t n (1 + x) (shift0_i_t b).
  Proof.
    unfold shift0_i_t; intros.
    symmetry.
    rewrite shift_i_t_shift_cut; repeat f_equal; la.
  Qed.

  Lemma fmap_map_shift0_i_t_shift n x (W : hctx) :
    fmap_map shift0_i_t (fmap_map (shift_i_t n x) W) =
    fmap_map (shift_i_t n (1 + x)) (fmap_map shift0_i_t W).
  Proof.
    repeat rewrite fmap_map_fmap_map.
    setoid_rewrite shift0_i_t_shift.
    eauto.
  Qed.

  Lemma fmap_map_shift0_t_t_shift n x (W : hctx) :
    fmap_map shift0_t_t (fmap_map (shift_t_t n x) W) =
    fmap_map (shift_t_t n (1 + x)) (fmap_map shift0_t_t W).
  Proof.
    repeat rewrite fmap_map_fmap_map.
    setoid_rewrite shift0_t_t_shift.
    eauto.
  Qed.

  Lemma shift0_i_t_subst x v b :
    shift0_i_t (subst_i_t x (shift_i_i x 0 v) b) = subst_i_t (1 + x) (shift_i_i (1 + x) 0 v) (shift0_i_t b).
  Proof.
    unfold shift0_i_t, subst0_i_i.
    rewrite shift_i_t_subst_in by la.
    rewrite shift_i_i_shift_merge by la.
    repeat (f_equal; try la).
  Qed.

  Lemma fmap_map_shift0_i_t_subst n c (W : hctx) :
    fmap_map shift0_i_t (fmap_map (subst_i_t n (shift_i_i n 0 c)) W) =
    fmap_map (subst_i_t (1 + n) (shift_i_i (1 + n) 0 c)) (fmap_map shift0_i_t W).
  Proof.
    repeat rewrite fmap_map_fmap_map.
    setoid_rewrite shift0_i_t_subst.
    eauto.
  Qed.
  
  Lemma shift0_t_t_subst x v b :
    shift0_t_t (subst_t_t x (shift_t_t x 0 v) b) = subst_t_t (1 + x) (shift_t_t (1 + x) 0 v) (shift0_t_t b).
  Proof.
    unfold shift0_t_t, subst0_t_t.
    rewrite shift_t_t_subst_in by la.
    rewrite shift_t_t_shift_merge by la.
    repeat (f_equal; try la).
  Qed.

  Lemma fmap_map_shift0_t_t_subst n c (W : hctx) :
    fmap_map shift0_t_t (fmap_map (subst_t_t n (shift_t_t n 0 c)) W) =
    fmap_map (subst_t_t (1 + n) (shift_t_t (1 + n) 0 c)) (fmap_map shift0_t_t W).
  Proof.
    repeat rewrite fmap_map_fmap_map.
    setoid_rewrite shift0_t_t_subst.
    eauto.
  Qed.
  
  Lemma subst0_i_t_shift0 v b :
    subst0_i_t v (shift0_i_t b) = b.
  Proof.
    unfold shift0_i_t, subst0_i_t.
    specialize (@subst_i_t_shift_avoid 1 b v 0 0); intros H; simplify.
    repeat rewrite shift_i_t_0 in *.
    eauto with db_la.
  Qed.
  
  Lemma fmap_map_subst0_i_t_shift0 k c W : fmap_map (K := k) (subst0_i_t c) (fmap_map shift0_i_t W) = W.
  Proof.
    repeat rewrite fmap_map_fmap_map.
    setoid_rewrite subst0_i_t_shift0.
    eapply fmap_map_id.
  Qed.
  
  Lemma subst0_t_t_shift0 v b :
    subst0_t_t v (shift0_t_t b) = b.
  Proof.
    unfold shift0_t_t, subst0_t_t.
    specialize (@subst_t_t_shift_avoid 1 b v 0 0); intros H; simplify.
    repeat rewrite shift_t_t_0 in *.
    eauto with db_la.
  Qed.
  
  Lemma fmap_map_subst0_t_t_shift0 k c W : fmap_map (K := k) (subst0_t_t c) (fmap_map shift0_t_t W) = W.
  Proof.
    repeat rewrite fmap_map_fmap_map.
    setoid_rewrite subst0_t_t_shift0.
    eapply fmap_map_id.
  Qed.

  Lemma shift_i_t_shift_t_t_commute :
    forall b x2 n2 x1 n1,
      shift_i_t x2 n2 (shift_t_t x1 n1 b) = shift_t_t x1 n1 (shift_i_t x2 n2 b).
  Proof.
    induct b;
      simplify; cbn in *;
        try solve [eauto |
                   f_equal; eauto |
                   erewrite H by la; repeat f_equal; eauto with db_la |
                   try replace (S (y - n1)) with (S y - n1) by la;
                   f_equal;
                   match goal with
                     H : _ |- _ => eapply H; eauto with db_la
                   end].
    {
      (* Case CVar *)
      repeat match goal with
               |- context [?a <=? ?b] => cases (a <=? b); simplify; cbn
             end; f_equal; la.
    }
  Qed.

  Lemma subst_t_e_AbsTIs tis :
    forall x v e,
      let n_t := length (filter id tis) in
      let n_i := length (filter negb tis) in
      subst_t_e x v (EAbsTIs tis e) = EAbsTIs tis (subst_t_e (n_t + x) (shift_t_t n_t 0 (shift_i_t n_i 0 v)) e).
  Proof.
    simpl.
    induct tis; simplify.
    {
      rewrite shift_i_t_0.
      rewrite shift_t_t_0.
      eauto.
    }
    destruct a; simpl.
    {
      f_equal.
      rewrite IHtis.
      f_equal.
      f_equal; try la.
      unfold shift0_t_t.
      rewrite shift_i_t_shift_t_t_commute.
      rewrite shift_t_t_shift_merge by la.
      eauto.
    }
    {
      f_equal.
      rewrite IHtis.
      f_equal.
      f_equal; try la.
      unfold shift0_i_t.
      rewrite shift_i_t_shift_merge by la.
      eauto.
    }
  Qed.
  
  Lemma subst_i_e_AbsTIs tis :
    forall x v e,
      let n_i := length (filter negb tis) in
      subst_i_e x v (EAbsTIs tis e) = EAbsTIs tis (subst_i_e (n_i + x) (shift_i_i n_i 0 v) e).
  Proof.
    simpl.
    induct tis; simplify.
    {
      rewrite shift_i_i_0.
      eauto.
    }
    destruct a; simpl.
    {
      f_equal.
      rewrite IHtis.
      eauto.
    }
    {
      f_equal.
      rewrite IHtis.
      f_equal.
      f_equal; try la.
      unfold shift0_i_i.
      rewrite shift_i_i_shift_merge by la.
      eauto.
    }
  Qed.
  
  Lemma subst_e_e_AbsTIs tis :
    forall x v e,
      let n_t := length (filter id tis) in
      let n_i := length (filter negb tis) in
      subst_e_e x v (EAbsTIs tis e) = EAbsTIs tis (subst_e_e x (shift_t_e n_t 0 (shift_i_e n_i 0 v)) e).
  Proof.
    induct tis; simplify.
    {
      rewrite shift_i_e_0.
      rewrite shift_t_e_0.
      eauto.
    }
    destruct a; simpl.
    {
      f_equal.
      rewrite IHtis.
      f_equal.
      f_equal; try la.
      unfold shift0_t_e.
  Lemma shift_i_e_shift_t_e_commute :
    forall b x2 n2 x1 n1,
      shift_i_e x2 n2 (shift_t_e x1 n1 b) = shift_t_e x1 n1 (shift_i_e x2 n2 b).
  Proof.
    induct b; simplify; try rewrite IHb; try rewrite IHb1; try rewrite IHb2; try rewrite IHb3; try rewrite shift_i_t_shift_t_t_commute by la; eauto.
  Qed.

      rewrite shift_i_e_shift_t_e_commute.
      rewrite shift_t_e_shift by la.
      eauto.
    }
    {
      f_equal.
      rewrite IHtis.
      f_equal.
      f_equal; try la.
      unfold shift0_i_e.
      rewrite shift_i_e_shift by la.
      eauto.
    }
  Qed.
  
  Lemma value_subst_i_e v :
    value v ->
    forall n c,
      value (subst_i_e n c v).
  Proof.
    induct 1; intros n e'; simplify; try econstructor; eauto.
  Qed.
  
  Lemma value_subst_t_e v :
    value v ->
    forall n c,
      value (subst_t_e n c v).
  Proof.
    induct 1; intros n e'; simplify; try econstructor; eauto.
  Qed.
  
  Lemma value_subst_e_e v :
    value v ->
    forall n e,
      value (subst_e_e n e v).
  Proof.
    induct 1; intros n e'; simplify; try econstructor; eauto.
  Qed.
  
  Lemma value_typing_T0 C e t i :
    typing C e t i ->
    value e ->
    typing C e t T0.
  Proof.
    induct 1;
      invert 1;
      try solve [econstructor; eauto | eapply TyTyeq; eauto].
    {
      clear H H0.
      eapply TyIdxEq; [econstructor; eauto | ].
      eapply interp_prop_eq_add_0.
    }
  Qed.
    
  Lemma get_sctx_add_typing_ctx t C : get_sctx (add_typing_ctx t C) = get_sctx C.
  Proof.
    destruct C as (((L & K) & W) & G); eauto.
  Qed.
  
  Lemma get_sctx_add_kinding_ctx k C : get_sctx (add_kinding_ctx k C) = get_sctx C.
  Proof.
    destruct C as (((L & K) & W) & G); eauto.
  Qed.
  
  Lemma get_kctx_add_typing_ctx t C : get_kctx (add_typing_ctx t C) = get_kctx C.
  Proof.
    destruct C as (((L & K) & W) & G); eauto.
  Qed.
  
  Hint Constructors Forall2.

  Definition tyeq_KType L t t' := tyeq L t t' KType.

  Arguments tyeq_KType / .

  Lemma forall_eq_eq : forall bs A (a b : interp_bsorts bs A), forall_ bs (lift2 bs eq a b) -> a = b.
  Proof.
    induct bs; simpl; eauto.
    rename a into bsort.
    intros A a b H.
    rewrite fuse_lift1_lift2 in *.
    eapply IHbs; eauto.
    eapply forall_lift2_lift2; [| eapply H]; eauto.
    simpl; intros.
    eapply FunctionalExtensionality.functional_extensionality.
    eauto.
  Qed.
  
  Section shift_tv.

    Variable n : nat.

    (* Arguments TVQuanI q b p t . *)
  
    Fixpoint shift_t_tv (x : var) (b : tyv) : tyv :=
      match b with
      | TVVar y =>
        if x <=? y then
          TVVar (n + y)
        else
          TVVar y
      | TVConst cn => TVConst cn
      | TVUnOp opr t => TVUnOp opr (shift_t_tv x t)
      | TVBinOp opr c1 c2 => TVBinOp opr (shift_t_tv x c1) (shift_t_tv x c2)
      | TVArrow t1 i t2 => TVArrow (shift_t_tv x t1) i (shift_t_tv x t2)
      | TVQuan q k c => TVQuan q k (shift_t_tv (1 + x) c)
      | TVQuanI q p c => TVQuanI q p (fun i => shift_t_tv x (c i))
      | TVRec k t args => TVRec k (fun i => shift_t_tv (1 + x) (t i)) args
      end.

  End shift_tv.
        
  Fixpoint shift_t_gtv x n k : interp_k k -> interp_k k :=
    match k with
    | [] => shift_t_tv x n
    | s :: k' => fun body i => shift_t_gtv x n k' (body i)
    end.
  
  Lemma complete_var_shift_t_gtv n x k :
    forall t, complete_var k (shift_t_tv n x t) = shift_t_gtv n x k (complete_var k t).
  Proof.
    induct k; simpl; eauto.
    intros t.
    eapply FunctionalExtensionality.functional_extensionality.
    intros i.
    eauto.
  Qed.

  Lemma shift_t_gtv_kind_default_value n x k :
    shift_t_gtv n x k (kind_default_value k) = kind_default_value k.
  Proof.
    induct k; simpl; eauto.
    eapply FunctionalExtensionality.functional_extensionality.
    eauto.
  Qed.

  Lemma shift_t_gtv_convert_kind_value n x k1 k2 t :
    shift_t_gtv n x k2 (convert_kind_value k1 k2 t) = convert_kind_value k1 k2 (shift_t_gtv n x k1 t).
  Proof.
    unfold convert_kind_value.
    cases (kind_dec k1 k2); subst.
    {
      unfold eq_rect_r.
      rewrite <- Eqdep.EqdepTheory.eq_rect_eq.
      eauto.
    }
    {
      rewrite shift_t_gtv_kind_default_value; eauto.
    }
  Qed.

  Lemma forall_shift_t_t :
    forall body x bs k_b n,
      (* wellscoped_i (length bs) body -> *)
      interp_ty (shift_t_t n x body) bs k_b = lift1 bs (shift_t_gtv n x k_b) (interp_ty body bs k_b).
  Proof.
    simpl.
    induct body; try rename x into y; intros x bs k_b n.
    {
      (* Case TVar *)
      simpl.
      repeat rewrite fuse_lift1_lift0 in *.
      rewrite <- complete_var_shift_t_gtv.
      simpl.
      cases (x <=? y); simpl in *;
        repeat rewrite fuse_lift1_lift0 in *;
        eauto.
    }
    {
      (* Case TConst *)
      simpl.
      repeat rewrite fuse_lift1_lift0 in *.
      f_equal.
      rewrite shift_t_gtv_convert_kind_value; eauto.
    }
    {
      (* Case TUnOp *)
      simpl.
      repeat rewrite fuse_lift1_lift0 in *.
      rewrite IHbody.
      repeat rewrite fuse_lift1_lift1 in *.
      simpl.
      f_equal.
      eapply FunctionalExtensionality.functional_extensionality.
      intros i.
      rewrite shift_t_gtv_convert_kind_value; eauto.
    }
    {
      (* Case TBinOp *)
      simpl.
      repeat rewrite fuse_lift1_lift0 in *.
      rewrite IHbody1.
      rewrite IHbody2.
      repeat rewrite fuse_lift1_lift1 in *.
      repeat rewrite fuse_lift1_lift2 in *.
      repeat rewrite fuse_lift2_lift1_1 in *.
      repeat rewrite fuse_lift2_lift1_2 in *.
      simpl.
      f_equal.
      eapply FunctionalExtensionality.functional_extensionality.
      intros a.
      eapply FunctionalExtensionality.functional_extensionality.
      intros b.
      rewrite shift_t_gtv_convert_kind_value; eauto.
    }
    {
      (* Case TArrow *)
      simpl.
      repeat rewrite fuse_lift1_lift0 in *.
      rewrite IHbody1.
      rewrite IHbody2.
      repeat rewrite fuse_lift1_lift1 in *.
      repeat rewrite fuse_lift1_lift3 in *.
      repeat rewrite fuse_lift3_lift1_1 in *.
      repeat rewrite fuse_lift3_lift1_3 in *.
      simpl.
      f_equal.
      eapply FunctionalExtensionality.functional_extensionality.
      intros a.
      eapply FunctionalExtensionality.functional_extensionality.
      intros b.
      eapply FunctionalExtensionality.functional_extensionality.
      intros c.
      rewrite shift_t_gtv_convert_kind_value; eauto.
    }
    {
      (* Case TAbs *)
      simpl.
      destruct k_b; simpl.
      {
        repeat rewrite fuse_lift1_lift0 in *.
        simpl.
        eauto.
      }
      rewrite IHbody.
      simpl.
      eauto.
    }
    {
      (* Case TApp *)
      simpl.
      rewrite IHbody.
      repeat rewrite fuse_lift1_lift2 in *.
      repeat rewrite fuse_lift2_lift1_1 in *.
      unfold apply.
      simpl.
      eauto.
    }
    {
      (* Case TQuan *)
      simpl.
      repeat rewrite fuse_lift1_lift0 in *.
      rewrite IHbody.
      repeat rewrite fuse_lift1_lift1 in *.
      simpl.
      f_equal.
      eapply FunctionalExtensionality.functional_extensionality.
      intros i.
      rewrite shift_t_gtv_convert_kind_value; eauto.
    }
    {
      (* Case TQuanI *)
      simpl.
      rewrite IHbody.
      repeat rewrite fuse_lift1_lift1 in *.
      repeat rewrite fuse_lift1_lift2 in *.
      simpl.
      repeat rewrite fuse_lift2_lift1_2 in *.
      f_equal.
      eapply FunctionalExtensionality.functional_extensionality.
      intros a.
      eapply FunctionalExtensionality.functional_extensionality.
      intros b.
      rewrite shift_t_gtv_convert_kind_value; eauto.
    }
    {
      (* Case TRec *)
      simpl.
      rewrite IHbody.
      repeat rewrite fuse_lift1_lift1 in *.
      repeat rewrite fuse_lift1_lift2 in *.
      repeat rewrite fuse_lift2_lift1_1 in *.
      f_equal.
      eapply FunctionalExtensionality.functional_extensionality.
      intros a.
      eapply FunctionalExtensionality.functional_extensionality.
      intros b.
      rewrite shift_t_gtv_convert_kind_value; eauto.
      simpl.
      f_equal.
      f_equal.
      eapply FunctionalExtensionality.functional_extensionality.
      intros c.
      Lemma uncurrys_shift_t_gtv n x k :
        forall t p, uncurrys k (shift_t_gtv n x k t) p = shift_t_tv n x (uncurrys k t p).
      Proof.
        induct k; simpl; eauto.
      Qed.

      rewrite uncurrys_shift_t_gtv; eauto.
    }
  Qed.
  
  Lemma tyveq_shift t t' :
    tyveq t t' ->
    forall n x,
      tyveq (shift_t_tv n x t) (shift_t_tv n x t').
  Proof.
    induct 1; simpl; eauto.
    rename x into y.
    intros n x.
    cases (x <=? y); eauto.
  Qed.
  
  Lemma gtyveq_shift n x :
    forall k t t',
      gtyveq k t t' ->
      gtyveq k (shift_t_gtv n x k t) (shift_t_gtv n x k t').
  Proof.
    induct k; simpl; eauto.
    intros t t' H.
    eapply tyveq_shift; eauto.
  Qed.

  Lemma tyeq_shift_t_t L c c' k n x :
    tyeq L c c' k ->
    tyeq L (shift_t_t n x c) (shift_t_t n x c') k.
  Proof.
    intros H.
    unfold tyeq in *.
    repeat rewrite forall_shift_t_t.
    rewrite fuse_lift3_lift1_2.
    rewrite fuse_lift3_lift1_3.
    eapply forall_lift3_lift3; [|eapply H]; eauto.
    simpl; intros.
    eapply gtyveq_shift; eauto.
  Qed.
  
  Lemma ty_G_tyeq C e t i :
    typing C e t i ->
    forall G',
    Forall2 (tyeq_KType (get_sctx C)) (get_tctx C) G' ->
    typing (get_sctx C, get_kctx C, get_hctx C, G') e t i.
  Proof.
    induct 1;
      intros G' Htyeq;
      destruct C as (((L & K) & W) & G);
      simplify;
      try solve [econstructor; eauto | econstructor; simplify; eauto with db_tyeq].
    {
      (* Case Var *)
      eapply nth_error_Forall2 in Htyeq; eauto.
      destruct Htyeq as (t' & Ht' & Htyeq).
      eapply TyTyeq.
      {
        econstructor; simplify; eauto.
      }
      simplify.
      eauto with db_tyeq.
    }
    {
      (* Case AbsT *)
      econstructor; simplify; eauto.
      eapply IHtyping.
      eapply Forall2_map; eauto.
      intros c c' Htyeq2.
      eapply tyeq_shift_t_t; eauto.
    }
    {
      (* Case AbsI *)
      econstructor; simplify; eauto.
      eapply IHtyping.
      eapply Forall2_map; eauto.
      intros c c' Htyeq2.
      
      (*here*)
      
    Lemma shift_strip_subsets_imply x ls L :
      let bs := map get_bsort L in
      let bs_new := map get_bsort ls in
      let bs' := insert bs_new x bs in
      x <= length L ->
      wellscoped_ss L ->
      imply_ bs'
             (interp_p bs' (and_all (strip_subsets (shift_i_ss (length ls) (firstn x L) ++ ls ++ my_skipn L x))))
             (shift bs_new x bs (interp_p bs (and_all (strip_subsets L)))).
    Proof.
      intros bs bs_new bs' Hcmp HL.
      rewrite !strip_subsets_insert by la.
      eapply forall_trans.
      {
        eapply and_all_app_imply_no_middle.
      }
      eapply forall_iff_imply.
      eapply forall_iff_sym.
      eapply forall_iff_trans.
      {
        eapply forall_iff_sym.
        eapply forall_shift_i_p_iff_shift; eauto.
        subst bs.
        rewrite map_length.
        eapply wellscoped_ss_wellscoped_p_strip_subsets; eauto.
      }
      eapply forall_iff_refl'.
      rewrite <- (firstn_my_skipn x L) at 1.
      rewrite strip_subsets_app.
      rewrite <- and_all_map_shift_i_p.
      rewrite map_app.
      rewrite map_map.
      subst bs.
      subst bs_new.
      repeat rewrite map_length.
      f_equal.
      f_equal.
      f_equal.
      eapply map_ext.
      intros b.
      rewrite length_firstn_le by la.
      rewrite shift_i_p_shift_merge by la.
      eauto.
    Qed.
    
  Lemma interp_prop_shift_i_p_reprove L p :
    interp_prop L p ->
    wellscoped_ss L ->
    wellscoped_p (length L) p ->
    forall x ls ,
      let n := length ls in
      x <= length L ->
      interp_prop (shift_i_ss n (firstn x L) ++ ls ++ my_skipn L x) (shift_i_p n x p).
  Proof.
    cbn in *.
    intros H Hscss Hscp x ls Hle.
    unfold interp_prop in *.
    cbn in *.
    rewrite !get_bsort_insert_shift.
    set (bs := map get_bsort L) in *.
    set (bs_new := map get_bsort ls) in *.
    eapply forall_shift with (new := bs_new) (x := x) in H.
    rewrite <- lift2_shift in *.
    eapply forall_trans; [eapply shift_strip_subsets_imply|]; eauto.
    eapply forall_trans; [eapply H|]; eauto.
    eapply forall_iff_imply.
    eapply forall_iff_sym.
    eapply forall_shift_i_p_iff_shift; eauto; subst bs bs_new; try rewrite map_length; eauto.
  Qed.

  Lemma lift3_to_imply bs A2 A3 (f : A2 -> A3 -> Prop) a1 a2 a3:
    lift3 bs (fun (a1 : Prop) a2 a3 => a1 -> f a2 a3) a1 a2 a3 = lift2 bs imply a1 (lift2 bs f a2 a3).
  Proof.
    rewrite fuse_lift2_lift2_2; eauto.
  Qed.

  Lemma tyeq_shift_i_t L t t' k :
    tyeq L t t' k ->
    wellscoped_ss L ->
    (* wellscoped_p (length L) p -> *)
    forall x ls ,
      let n := length ls in
      x <= length L ->
      tyeq (shift_i_ss n (firstn x L) ++ ls ++ my_skipn L x) (shift_i_t n x t) (shift_i_t n x t') k.
  Proof.
    simpl.
    intros H HL x ls Hx.
    unfold tyeq in *.
    rewrite !get_bsort_insert_shift.
    set (bs := map get_bsort L) in *.
    set (bs_new := map get_bsort ls) in *.
    eapply forall_shift with (new := bs_new) (x := x) in H.
    rewrite <- lift3_shift in *.
    repeat rewrite lift3_to_imply in *.
    eapply forall_trans; [eapply shift_strip_subsets_imply|]; eauto.
    eapply forall_trans; [eapply H|]; eauto.
    (*here*)
    eapply forall_iff_imply.
    eapply forall_iff_sym.
    eapply forall_shift_i_p_iff_shift; eauto; subst bs bs_new; try rewrite map_length; eauto.
  Qed.

      eapply tyeq_shift0_i_t; eauto.
    }
    {
      (* Case Unpack *)
      econstructor; simplify; eauto.
      eapply IHtyping2.
      econstructor; eauto with db_tyeq.
      eapply Forall2_map; eauto.
      intros c c' Htyeq2.
      eapply tyeq_shift0_c_c; eauto.
    }
  Qed.
  
  Lemma Forall2_refl' A (P : A -> A -> Prop) ls :
    (forall a, P a a) ->
    Forall2 P ls ls.
  Proof.
    induct ls; simplify; eauto.
  Qed.
  
  Lemma add_typing_ctx_tyeq t1 t2 C e t i :
    typing (add_typing_ctx t1 C) e t i ->
    tyeq (get_kctx C) t1 t2 ->
    typing (add_typing_ctx t2 C) e t i.
  Proof.
    intros Hty Htyeq.
    destruct C as ((L & W) & G); simplify.
    eapply ty_G_tyeq in Hty; eauto.
    simplify.
    eauto using Forall2_refl' with db_tyeq.
  Qed.
  
  Lemma value_shift_e_e e :
    value e ->
    forall n x,
      value (shift_e_e n x e).
  Proof.
    induct 1; simplify; econstructor; eauto.
  Qed.
  
  Lemma value_shift_c_e e :
    value e ->
    forall n x,
      value (shift_c_e n x e).
  Proof.
    induct 1; simplify; econstructor; eauto.
  Qed.
  
  Lemma ty_shift_c_e C e t i :
    typing C e t i ->
    forall x ls,
      let n := length ls in
      let L := get_kctx C in
      x <= length L ->
      typing (shift_c_ks n (firstn x L) ++ ls ++ my_skipn L x, fmap_map (shift_c_c n x) (get_hctx C), map (shift_c_c n x) (get_tctx C)) (shift_c_e n x e) (shift_c_c n x t) (shift_c_c n x i).
  Proof.
    induct 1; simpl; 
      try rename x into x';
      intros x ls Hle;
      destruct C as ((L & W) & G);
      simplify;
      cbn in *;
      try solve [cbn in *; econstructor; eauto].
    {
      (* Case Var *)
      econstructor.
      eauto using map_nth_error.
    }
    {
      (* Case Abs *)
      econstructor; simplify.
      {
        eapply kd_shift_c_c with (k := KType); eauto.
      }
      eauto.
    }
    {
      (* Case AppC *)
      eapply TyTyeq.
      {
        eapply TyAppC; simplify.
        {
          eapply IHtyping; eauto.
        }
        {  
          eapply kd_shift_c_c; eauto.
        }
      }
      simplify.
      rewrite shift_c_c_subst0.
      eauto with db_tyeq.
    }
    {
      (* Case AbsC *)
      econstructor; simplify.
      {
        eapply value_shift_c_e; eauto.
      }
      {
        eapply wfkind_shift_c_k; eauto.
      }
      {
        rewrite fmap_map_shift0_t_t_shift.
        rewrite map_shift_i_i_shift_merge.
        specialize (IHtyping (S x) ls); simplify.
        erewrite length_firstn_le in IHtyping by eauto.
        eapply IHtyping; eauto.
        la.
      }
    }
    {
      (* Case Rec *)
      subst.
      econstructor; simplify.
      {
        rewrite shift_c_e_AbsCs.
        simplify.
        eauto.
      }
      {  
        eapply kd_shift_c_c with (k := KType); eauto.
      }
      eapply IHtyping; eauto.
    }
    {
      (* Case Fold *)
      subst.
      econstructor; simplify.
      {
        rewrite shift_c_c_Apps.
        eauto.
      }
      {
        cbn.
        eauto.
      }
      {  
        eapply kd_shift_c_c with (k := KType); eauto.
      }
      eapply TyTyeq.
      {
        eauto.
      }
      rewrite shift_c_c_Apps.
      simplify.
      rewrite shift_c_c_subst0.
      eauto with db_tyeq.
    }
    {
      (* Case Unfold *)
      subst.
      eapply TyTyeq.
      {
        eapply TyUnfold; simplify.
        {
          eauto.
        }
        {
          eapply TyTyeq.
          {
            eauto.
          }
          rewrite shift_c_c_Apps.
          cbn.
          eauto with db_tyeq.
        }
      }
      simplify.
      rewrite shift_c_c_Apps.
      simplify.
      rewrite shift_c_c_subst0.
      eauto with db_tyeq.
    }
    {
      (* Case Pack *)
      eapply TyPack; simplify.
      {
        eapply kd_shift_c_c with (c := CExists k t1) (k := KType); eauto.
      }
      {
        eapply kd_shift_c_c; eauto.
      }
      eapply TyTyeq.
      {
        eapply IHtyping; eauto.
      }
      simplify.
      rewrite shift_c_c_subst0.
      eauto with db_tyeq.
    }
    {
      (* Case Unpack *)
      eapply TyUnpack; simplify.
      {
        eapply IHtyping1; eauto.
      }
      {
        rewrite fmap_map_shift0_t_t_shift.
        rewrite map_shift_i_i_shift_merge.
        specialize (IHtyping2 (S x) ls); simplify.
        erewrite length_firstn_le in IHtyping2 by eauto.
        repeat rewrite shift0_c_c_shift.
        eapply IHtyping2; eauto.
        la.
      }
    }
    {
      (* Case Const *)
      eapply TyTyeq.
      {
        eapply TyConst; simplify.
      }
      simplify.
      {
        cases cn; simplify;
          eauto with db_tyeq.
      }
    }
    {
      (* Case Proj *)
      eapply TyTyeq.
      {
        eapply TyProj; simplify.
        eapply IHtyping; eauto.
      }
      simplify.
      cases pr; simplify;
        eauto with db_tyeq.
    }
    {
      (* Case Inj *)
      eapply TyTyeq.
      {
        eapply TyInj; simplify.
        {
          eapply IHtyping; eauto.
        }
        {  
          eapply kd_shift_c_c with (k := KType); eauto.
        }
      }
      simplify.
      cases inj; simplify;
        eauto with db_tyeq.
    }
    {
      (* Case Loc *)
      eapply TyLoc; simplify.
      eapply fmap_map_lookup; eauto.
    }
    {
      (* Case Sub *)
      eapply TySub.
      {
        eapply IHtyping; eauto.
      }
      {
        simplify.
        eapply tyeq_shift_c_c; eauto with db_tyeq.
      }
      {
        simplify.
        eapply interp_prop_shift_c_p with (p := (i1 <= i2)%idx); eauto.
      }
    }
  Qed.

  Lemma ty_shift0_c_e L W G e t i k :
    typing (L, W, G) e t i ->
    typing (k :: L, fmap_map shift0_c_c W, map shift0_c_c G) (shift0_c_e e) (shift0_c_c t) (shift0_c_c i).
  Proof.
    intros Hty.
    eapply ty_shift_c_e with (C := (L, W, G)) (x := 0) (ls := [k]) in Hty; simplify; try la.
    repeat rewrite my_skipn_0 in *.
    eauto.
  Qed.

  Lemma ty_subst_c_e C e t i :
    typing C e t i ->
    forall n k c ,
      nth_error (get_kctx C) n = Some k ->
      kinding (my_skipn (get_kctx C) (1 + n)) c k ->
      typing (subst_c_ks c (firstn n (get_kctx C)) ++ my_skipn (get_kctx C) (1 + n), fmap_map (subst_c_c n (shift_c_c n 0 c)) (get_hctx C), map (subst_c_c n (shift_c_c n 0 c)) (get_tctx C)) (subst_c_e n (shift_c_c n 0 c) e) (subst_c_c n (shift_c_c n 0 c) t) (subst_c_c n (shift_c_c n 0 c) i).
  Proof.
    induct 1;
      try rename n into n';
      try rename k into k';
      try rename c into c';
      intros n k c Hnth Hkd;
      destruct C as ((L & W) & G);
      simplify;
      try solve [econstructor; eauto].
    {
      (* Case Var *)
      econstructor.
      eauto using map_nth_error.
    }
    {
      (* Case Abs *)
      econstructor; simplify.
      {  
        eapply kd_subst_c_c with (k' := KType); eauto.
      }
      eapply IHtyping; eauto.
    }
    {
      (* Case AppC *)
      eapply TyTyeq.
      {
        eapply TyAppC; simplify.
        {
          eapply IHtyping; eauto.
        }
        {  
          eapply kd_subst_c_c; eauto.
        }
      }
      simplify.
      rewrite subst_c_c_subst0.
      eauto with db_tyeq.
    }
    {
      (* Case AbsC *)
      econstructor; simplify.
      {
        eapply value_subst_c_e; eauto.
      }
      {
        eapply wfkind_subst_c_k; eauto.
      }
      {
        rewrite fmap_map_shift0_subst.
        rewrite map_shift0_subst.
        repeat rewrite shift0_c_c_shift_0.
        specialize (IHtyping (S n)); simplify.
        erewrite nth_error_length_firstn in IHtyping by eauto.
        eapply IHtyping; eauto.
      }
    }
    {
      (* Case Rec *)
      subst.
      econstructor; simplify.
      {
        rewrite subst_c_e_AbsCs.
        simplify.
        eauto.
      }
      {  
        eapply kd_subst_c_c with (k' := KType); eauto.
      }
      eapply IHtyping; eauto.
    }
    {
      (* Case Fold *)
      subst.
      econstructor; simplify.
      {
        rewrite subst_c_c_Apps.
        eauto.
      }
      {
        simplify.
        eauto.
      }
      {  
        eapply kd_subst_c_c with (k' := KType); eauto.
      }
      eapply TyTyeq.
      {
        eauto.
      }
      rewrite subst_c_c_Apps.
      simplify.
      rewrite subst_c_c_subst0.
      eauto with db_tyeq.
    }
    {
      (* Case Unfold *)
      subst.
      eapply TyTyeq.
      {
        eapply TyUnfold; simplify.
        {
          eauto.
        }
        {
          eapply TyTyeq.
          {
            eauto.
          }
          rewrite subst_c_c_Apps.
          simplify.
          eauto with db_tyeq.
        }
      }
      simplify.
      rewrite subst_c_c_Apps.
      simplify.
      rewrite subst_c_c_subst0.
      eauto with db_tyeq.
    }
    {
      (* Case Pack *)
      eapply TyPack; simplify.
      {
        eapply kd_subst_c_c with (c' := CExists k' t1) (k' := KType); eauto.
      }
      {
        eapply kd_subst_c_c; eauto.
      }
      eapply TyTyeq.
      {
        eapply IHtyping; eauto.
      }
      simplify.
      rewrite subst_c_c_subst0.
      eauto with db_tyeq.
    }
    {
      (* Case Unpack *)
      eapply TyUnpack; simplify.
      {
        eapply IHtyping1; eauto.
      }
      {
        rewrite fmap_map_shift0_subst.
        rewrite map_shift0_subst.
        repeat rewrite shift0_c_c_shift_0.
        specialize (IHtyping2 (S n)); simplify.
        erewrite nth_error_length_firstn in IHtyping2 by eauto.
        repeat rewrite shift0_c_c_subst.
        eapply IHtyping2; eauto.
      }
    }
    {
      (* Case Const *)
      eapply TyTyeq.
      {
        eapply TyConst; simplify.
      }
      simplify.
      {
        rewrite subst_c_c_const_type.
        eauto with db_tyeq.
      }
    }
    {
      (* Case Proj *)
      eapply TyTyeq.
      {
        eapply TyProj; simplify.
        eapply IHtyping; eauto.
      }
      simplify.
      cases pr; simplify;
        eauto with db_tyeq.
    }
    {
      (* Case Inj *)
      eapply TyTyeq.
      {
        eapply TyInj; simplify.
        {
          eapply IHtyping; eauto.
        }
        {  
          eapply kd_subst_c_c with (k' := KType); eauto.
        }
      }
      simplify.
      cases inj; simplify;
        eauto with db_tyeq.
    }
    {
      (* Case Case *)
      econstructor; simplify; eauto.
    }
    {
      (* Case Loc *)
      eapply TyLoc; simplify.
      eapply fmap_map_lookup; eauto.
    }
    {
      (* Case Sub *)
      eapply TySub.
      {
        eapply IHtyping; eauto.
      }
      {
        simplify.
        eapply tyeq_subst_c_c; eauto with db_tyeq.
      }
      {
        simplify.
        eapply interp_prop_subst_c_p with (p := (i1 <= i2)%idx); eauto.
      }
    }
  Qed.
  
  Lemma ty_subst0_c_e k L W G e t i c :
    typing (k :: L, W, G) e t i ->
    kinding L c k ->
    typing (L, fmap_map (subst0_c_c c) W, map (subst0_c_c c) G) (subst0_c_e c e) (subst0_c_c c t) (subst0_c_c c i).
  Proof.
    intros Hty Hkd.
    eapply ty_subst_c_e with (C := (k :: L, W, G)) (c := c) (n := 0) in Hty; simplify; 
      repeat rewrite my_skipn_0 in *;
      repeat rewrite shift_c_c_0 in *;
      eauto.
  Qed.

  Lemma ty_shift_e_e C e t i :
    typing C e t i ->
    forall x ls,
      typing (get_kctx C, get_hctx C, firstn x (get_tctx C) ++ ls ++ my_skipn (get_tctx C) x) (shift_e_e (length ls) x e) t i.
  Proof.
    induct 1;
      try rename x into y;
      intros x ls;
      destruct C as ((L & W) & G);
      simplify;
      try solve [econstructor; eauto].
    {
      (* Case Var *)
      cases (x <=? y).
      {
        econstructor; simplify.
        eapply nth_error_insert; eauto.
      }
      {
        econstructor; simplify.
        eapply nth_error_before_insert; eauto.
      }
    }
    {
      (* Case Abs *)
      econstructor; simplify; eauto.
      eapply IHtyping with (x := S x).
    }
    {
      (* Case AbsC *)
      econstructor; simplify; eauto.
      {
        eapply value_shift_e_e; eauto.
      }
      repeat rewrite map_app.
      rewrite map_firstn.
      rewrite map_my_skipn.
      specialize (IHtyping x (map shift0_c_c ls)).
      rewrite map_length in *.
      eauto.
    }
    {
      (* Case Rec *)
      subst.
      specialize (IHtyping (S x) ls); simplify.
      rewrite shift_e_e_AbsCs in *.
      econstructor; simplify; eauto.
    }
    {
      (* Case Unpack *)
      econstructor; simplify; eauto.
      repeat rewrite map_app.
      rewrite map_firstn.
      rewrite map_my_skipn.
      specialize (IHtyping2 (S x) (map shift0_c_c ls)); simplify.
      rewrite map_length in *.
      eauto.
    }
    {
      (* Case Case *)
      econstructor; simplify; eauto.
      {
        eapply IHtyping2 with (x := S x).
      }
      {
        eapply IHtyping3 with (x := S x).
      }
    }
  Qed.
  
  Lemma ty_shift0_e_e L W G e t i t' :
    typing (L, W, G) e t i ->
    typing (L, W, t' :: G) (shift0_e_e e) t i.
  Proof.
    intros Hty.
    eapply ty_shift_e_e with (C := (L, W, G)) (x := 0) (ls := [t']) in Hty.
    simplify.
    repeat rewrite my_skipn_0 in *.
    eauto.
  Qed.
  
  Lemma ty_subst_e_e C e1 t1 i1 :
    typing C e1 t1 i1 ->
    forall n t e2 ,
      nth_error (get_tctx C) n = Some t ->
      typing (get_kctx C, get_hctx C, removen n (get_tctx C)) e2 t T0 ->
      typing (get_kctx C, get_hctx C, removen n (get_tctx C)) (subst_e_e n e2 e1) t1 i1.
      (* typing (get_kctx C, get_hctx C, removen n (get_tctx C)) (subst_e_e e2 n 0 e1) t1 i1. *)
  Proof.
    induct 1;
      try rename n into n';
      intros n t'' e2' Hnth Hty;
      destruct C as ((L & W) & G);
      simplify;
      try solve [econstructor; eauto].
    {
      (* Case Var *)
      cases (x <=>? n).
      {
        econstructor; simplify.
        erewrite removen_lt; eauto.
      }
      {
        subst.
        rewrite H in Hnth.
        invert Hnth.
        eauto.
      }
      {
        econstructor; simplify.
        erewrite removen_gt; eauto.
      }
    }
    {
      (* Case Abs *)
      eapply TyIdxEq.
      {
        eapply TyAbs; simplify; eauto.
        eapply IHtyping with (n := 1 + n); eauto.
        simplify.
        eapply ty_shift0_e_e; eauto.
      }
      {
        simplify.
        eapply interp_prop_eq_refl.
      }
    }
    {
      (* Case Forall *)
      econstructor; eauto.
      {
        eapply value_subst_e_e; eauto.
      }
      simplify.
      rewrite map_removen.
      eapply IHtyping; eauto.
      {
        eapply map_nth_error; eauto.
      }
      rewrite <- map_removen.
      change T0 with (shift0_c_c T0).
      eapply ty_shift0_c_e; eauto.
    }
    {
      (* Case Rec *)
      subst.
      econstructor; eauto; simplify.
      {
        rewrite subst_e_e_AbsCs.
        simplify.
        eauto.
      }
      {
        eapply IHtyping with (n := S n); eauto.
        simplify.
        eapply ty_shift0_e_e; eauto.
      }
    }
    {
      (* Case Unpack *)
      eapply TyUnpack; eauto.
      simplify.
      rewrite map_removen.
      eapply IHtyping2 with (n := S n); eauto; simplify.
      {
        eapply map_nth_error; eauto.
      }
      rewrite <- map_removen.
      eapply ty_shift0_e_e; eauto.
      change T0 with (shift0_c_c T0).
      eapply ty_shift0_c_e; eauto.
    }
    {
      (* Case Case *)
      subst.
      econstructor; eauto; simplify.
      {
        eapply IHtyping2 with (n := S n); eauto.
        simplify.
        eapply ty_shift0_e_e; eauto.
      }
      {
        eapply IHtyping3 with (n := S n); eauto.
        simplify.
        eapply ty_shift0_e_e; eauto.
      }
    }
  Qed.
  
  Lemma ty_subst0_e_e_T0 L W t G e1 t1 i1 e2 :
    typing (L, W, t :: G) e1 t1 i1 ->
    typing (L, W, G) e2 t T0 ->
    typing (L, W, G) (subst0_e_e e2 e1) t1 i1%idx.
  Proof.
    intros Hty1 Hty2.
    eapply ty_subst_e_e with (C := (L, W, t :: G)) (n := 0); eauto.
    simplify.
    eauto.
  Qed.

  Lemma ty_subst0_e_e L W t G e1 t1 i1 e2 i2 :
    typing (L, W, t :: G) e1 t1 i1 ->
    typing (L, W, G) e2 t i2 ->
    value e2 ->
    typing (L, W, G) (subst0_e_e e2 e1) t1 i1%idx.
  Proof.
    intros Hty1 Hty2 Hval.
    eapply ty_subst0_e_e_T0; eauto.
    eapply value_typing_T0; eauto.
  Qed.

  Lemma weaken_W' C e t i :
    typing C e t i ->
    forall W' ,
      get_hctx C $<= W' ->
      typing (get_kctx C, W', get_tctx C) e t i.
  Proof.
    induct 1;
      intros W' Hincl;
      destruct C as ((L & W) & G);
      simplify;
      try solve [econstructor; simplify; eauto using fmap_map_shift0_c_c_incl].
  Qed.
    
  Lemma weaken_W L W G e t i W' :
    typing (L, W, G) e t i ->
    W $<= W' ->
    typing (L, W', G) e t i.
  Proof.
    intros Hty Hincl.
    eapply weaken_W' with (C := (L, W, G)); eauto.
  Qed.

  Lemma allocatable_add h l v :
    allocatable h ->
    allocatable (h $+ (l, v)).
  Proof.
    intros Halloc.
    destruct Halloc as (l_alloc & Halloc).
    exists (max l_alloc (1 + l)).
    intros l' Hge.
    cases (l' ==n l); subst; simplify.
    {
      la.
    }
    {
      eapply Halloc.
      la.
    }
  Qed.
      
  Lemma htyping_fresh h W :
    htyping h W ->
    exists l, h $? l = None.
  Proof.
    intros Hhty.
    unfold htyping in *.
    destruct Hhty as (Hhty & Halloc).
    destruct Halloc as (l_alloc & Halloc).
    exists l_alloc.
    eapply Halloc.
    la.
  Qed.
  
  Lemma htyping_elim_exists h W l t :
    htyping h W ->
    W $? l = Some t ->
    exists v,
      h $? l = Some v /\
      value v /\
      typing ([], W, []) v t T0.
  Proof.
    intros Hhty Hl.
    unfold htyping in *.
    destruct Hhty as (Hhty & Halloc).
    eauto.
  Qed.    

  Lemma htyping_elim h W l v t :
    htyping h W ->
    h $? l = Some v ->
    W $? l = Some t ->
    value v /\
    typing ([], W, []) v t T0.
  Proof.
    intros Hhty Hl HWl.
    unfold htyping in *.
    destruct Hhty as (Hhty & Halloc).
    eapply Hhty in HWl.
    destruct HWl as (v' & Hl' & Hval' & Hty').
    rewrite Hl' in Hl.
    invert Hl.
    eauto.
  Qed.
  
  Lemma htyping_elim_None h W l :
    htyping h W ->
    h $? l = None ->
    W $? l = None.
  Proof.
    intros Hhty Hl.
    unfold htyping in *.
    destruct Hhty as (Hhty & Halloc).
    cases (W $? l); eauto.
    eapply Hhty in Heq.
    destruct Heq as (? & Hl2 & ?).
    rewrite Hl2 in Hl.
    invert Hl.
  Qed.
  
  Lemma htyping_upd h W l t v i :
    htyping h W ->
    W $? l = Some t ->
    value v ->
    typing ([], W, []) v t i ->
    htyping (h $+ (l, v)) W.
  Proof.
    intros Hhty Hl Hval Hty.
    unfold htyping in *.
    destruct Hhty as (Hhty & Halloc).
    split; [ | eapply allocatable_add; eauto].
    intros l' t' Hl'.
    cases (l' ==n l); subst; simplify; eauto.
    rewrite Hl' in Hl.
    invert Hl.
    exists v; repeat eexists_split; eauto.
    eapply value_typing_T0; eauto.
  Qed.
  
  Lemma includes_add_new A (m m' : fmap loc A) k (v : A) :
    m $<= m' ->
    m' $? k = None ->
    m $<= m' $+ (k, v).
  Proof.
    intros Hincl Hk.
    eapply includes_intro.
    intros k' v' Hk'.
    cases (k' ==n k); subst; simplify; eauto.
    eapply includes_lookup in Hincl; eauto.
    rewrite Hincl in Hk; invert Hk.
  Qed.
  
  Lemma htyping_new h W l t v i :
    htyping h W ->
    h $? l = None ->
    value v ->
    typing ([], W, []) v t i ->
    htyping (h $+ (l, v)) (W $+ (l, t)).
  Proof.
    intros Hhty Hl Hval Hty.
    copy Hhty Hhty'.
    unfold htyping.
    destruct Hhty as (Hhty & Halloc).
    split; [ | eapply allocatable_add; eauto].
    assert (Hincl : W $<= W $+ (l, t)).
    {
      eapply htyping_elim_None in Hl; eauto.
      eapply includes_add_new; eauto.
      eapply includes_intro; eauto.
    }
    intros l' t' Hl'.
    cases (l' ==n l); subst; simplify.
    {
      symmetry in Hl'.
      invert Hl'.
      exists v; repeat eexists_split; eauto.
      eapply weaken_W; eauto.
      eapply value_typing_T0; eauto.
    }
    {
      eapply Hhty in Hl'.
      destruct Hl' as (v' & Hl' & Hval' & Hty').
      exists v'; repeat eexists_split; eauto.
      eapply weaken_W; eauto.
    }
  Qed.
  
  Lemma canon_CArrow' C v t i :
    typing C v t i ->
    get_kctx C = [] ->
    get_tctx C = [] ->
    forall t1 i' t2 ,
      tyeq [] t (CArrow t1 i' t2) ->
      value v ->
      exists e,
        v = EAbs e.
  Proof.
    induct 1; intros Hknil Htnil ta i' tb Htyeq Hval; try solve [invert Hval | eexists; eauto]; subst.
    (* { *)
    (*   rewrite Htnil in H. *)
    (*   rewrite nth_error_nil in H. *)
    (*   invert H. *)
    (* } *)
    {
      eapply CForall_CArrow_false in Htyeq; propositional.
    }
    {
      eapply CApps_CRec_CArrow_false in Htyeq; propositional.
    }
    {
      eapply CExists_CArrow_false in Htyeq; propositional.
    }
    {
      eapply const_type_CArrow_false in Htyeq; propositional.
    }
    {
      eapply CProd_CArrow_false in Htyeq; propositional.
    }
    {
      cases inj; simplify; eapply CSum_CArrow_false in Htyeq; propositional.
    }
    {
      eapply CRef_CArrow_false in Htyeq; propositional.
    }
    {
      destruct C as ((L & W) & G); simplify; subst.
      eapply IHtyping; eauto with db_tyeq.
    }
  Qed.

  Lemma canon_CArrow W v t1 i' t2 i :
    typing ([], W, []) v (CArrow t1 i' t2) i ->
    value v ->
    exists e,
      v = EAbs e.
  Proof.
    intros; eapply canon_CArrow'; eauto with db_tyeq.
  Qed.

  Lemma canon_CForall' C v t i :
    typing C v t i ->
    get_kctx C = [] ->
    get_tctx C = [] ->
    forall k t' ,
      tyeq [] t (CForall k t') ->
      value v ->
      exists e,
        v = EAbsC e.
  Proof.
    induct 1; intros Hknil Htnil k' t'' Htyeq Hval; try solve [invert Hval | eexists; eauto | invert Htyeq]; subst.
    (* { *)
    (*   rewrite Htnil in H. *)
    (*   rewrite nth_error_nil in H. *)
    (*   invert H. *)
    (* } *)
  (*   { *)
  (*     eapply CApps_CRec_CForall_false in Htyeq; propositional. *)
  (*   } *)
  (*   { *)
  (*     cases cn; simplify; invert Htyeq. *)
  (*   } *)
  (*   { *)
  (*     cases inj; simplify; invert Htyeq. *)
  (*   } *)
  (*   { *)
  (*     destruct C as ((L & W) & G); simplify; subst. *)
  (*     eapply IHtyping; eauto with db_tyeq. *)
  (*   } *)
    (* Qed. *)
  Admitted.

  Lemma canon_CForall W v k t i :
    typing ([], W, []) v (CForall k t) i ->
    value v ->
    exists e,
      v = EAbsC e.
  Proof.
    intros; eapply canon_CForall'; eauto with db_tyeq.
  Qed.

  Lemma canon_CRec' C v t i :
    typing C v t i ->
    get_kctx C = [] ->
    get_tctx C = [] ->
    forall k t' cs ,
      tyeq [] t (CApps (CRec k t') cs) ->
      value v ->
      exists e,
        v = EFold e /\
        value e.
  Proof.
    induct 1; intros Hknil Htnil k'' t'' cs' Htyeq Hval; try solve [invert Hval | eexists; eauto | invert Hval; eexists; eauto | invert Htyeq]; subst.
    (* { *)
    (*   rewrite Htnil in H. *)
    (*   rewrite nth_error_nil in H. *)
    (*   invert H. *)
    (* } *)
    {
      eapply tyeq_sym in Htyeq.
      eapply CApps_CRec_CArrow_false in Htyeq; propositional.
    }
    {
      eapply tyeq_sym in Htyeq.
      eapply CApps_CRec_CForall_false in Htyeq; propositional.
    }
    {
      eapply tyeq_sym in Htyeq.
      eapply CApps_CRec_CExists_false in Htyeq; propositional.
    }
    {
      eapply tyeq_sym in Htyeq.
      eapply CApps_CRec_const_type_false in Htyeq; propositional.
    }
    {
      eapply tyeq_sym in Htyeq.
      eapply CApps_CRec_CProd_false in Htyeq; propositional.
    }
    {
      eapply tyeq_sym in Htyeq.
      cases inj; simplify;
        eapply CApps_CRec_CSum_false in Htyeq; propositional.
    }
    {
      eapply tyeq_sym in Htyeq.
      eapply CApps_CRec_CRef_false in Htyeq; propositional.
    }
    {
      destruct C as ((L & W) & G); simplify; subst.
      eapply IHtyping; eauto with db_tyeq.
    }
  Qed.

  Lemma canon_CRec W v k t cs i :
    typing ([], W, []) v (CApps (CRec k t) cs) i ->
    value v ->
    exists e,
      v = EFold e /\
      value e.
  Proof.
    intros; eapply canon_CRec'; eauto with db_tyeq.
  Qed.

  Lemma canon_CExists' C v t i :
    typing C v t i ->
    get_kctx C = [] ->
    get_tctx C = [] ->
    forall k t' ,
      tyeq [] t (CExists k t') ->
      value v ->
      exists c e,
        v = EPack c e /\
        value e.
  Proof.
    induct 1; intros Hknil Htnil k' t'' Htyeq Hval; try solve [invert Hval | eexists; eauto | invert Hval; eexists; eauto | invert Htyeq]; subst.
    (* { *)
    (*   rewrite Htnil in H. *)
    (*   rewrite nth_error_nil in H. *)
    (*   invert H. *)
    (* } *)
  (*   { *)
  (*     eapply CApps_CRec_CExists_false in Htyeq; propositional. *)
  (*   } *)
  (*   { *)
  (*     cases cn; simplify; invert Htyeq. *)
  (*   } *)
  (*   { *)
  (*     cases inj; simplify; invert Htyeq. *)
  (*   } *)
  (*   { *)
  (*     destruct C as ((L & W) & G); simplify; subst. *)
  (*     eapply IHtyping; eauto with db_tyeq. *)
  (*   } *)
  (* Qed. *)
  Admitted.
  
  Lemma canon_CExists W v k t i :
    typing ([], W, []) v (CExists k t) i ->
    value v ->
    exists c e,
      v = EPack c e /\
      value e.
  Proof.
    intros; eapply canon_CExists'; eauto with db_tyeq.
  Qed.

  Lemma canon_CProd' C v t i :
    typing C v t i ->
    get_kctx C = [] ->
    get_tctx C = [] ->
    forall t1 t2 ,
      tyeq [] t (CProd t1 t2) ->
      value v ->
      exists v1 v2,
        v = EPair v1 v2 /\
        value v1 /\
        value v2.
  Proof.
    induct 1; intros Hknil Htnil t1'' t2'' Htyeq Hval; try solve [invert Hval | eexists; eauto | invert Hval; eexists; eauto | invert Htyeq]; subst.
    (* { *)
    (*   rewrite Htnil in H. *)
    (*   rewrite nth_error_nil in H. *)
    (*   invert H. *)
    (* } *)
  (*   { *)
  (*     eapply CApps_CRec_CProd_false in Htyeq; propositional. *)
  (*   } *)
  (*   { *)
  (*     cases cn; simplify; invert Htyeq. *)
  (*   } *)
  (*   { *)
  (*     cases inj; simplify; invert Htyeq. *)
  (*   } *)
  (*   { *)
  (*     destruct C as ((L & W) & G); simplify; subst. *)
  (*     eapply IHtyping; eauto with db_tyeq. *)
  (*   } *)
  (* Qed. *)
  Admitted.
  
  Lemma canon_CProd W v t1 t2 i :
    typing ([], W, []) v (CProd t1 t2) i ->
    value v ->
    exists v1 v2,
      v = EPair v1 v2 /\
      value v1 /\
      value v2.
  Proof.
    intros; eapply canon_CProd'; eauto with db_tyeq.
  Qed.

  Lemma canon_CSum' C v t i :
    typing C v t i ->
    get_kctx C = [] ->
    get_tctx C = [] ->
    forall t1 t2 ,
      tyeq [] t (CSum t1 t2) ->
      value v ->
      exists inj v',
        v = EInj inj v' /\
        value v'.
  Proof.
    induct 1; intros Hknil Htnil t1'' t2'' Htyeq Hval; try solve [invert Hval | eexists; eauto | invert Hval; eexists; eauto | invert Htyeq]; subst.
    (* { *)
    (*   rewrite Htnil in H. *)
    (*   rewrite nth_error_nil in H. *)
    (*   invert H. *)
    (* } *)
  (*   { *)
  (*     eapply CApps_CRec_CSum_false in Htyeq; propositional. *)
  (*   } *)
  (*   { *)
  (*     cases cn; simplify; invert Htyeq. *)
  (*   } *)
  (*   { *)
  (*     destruct C as ((L & W) & G); simplify; subst. *)
  (*     eapply IHtyping; eauto with db_tyeq. *)
  (*   } *)
  (* Qed. *)
  Admitted.
  
  Lemma canon_CSum W v t1 t2 i :
    typing ([], W, []) v (CSum t1 t2) i ->
    value v ->
    exists inj v',
      v = EInj inj v' /\
      value v'.
  Proof.
    intros; eapply canon_CSum'; eauto with db_tyeq.
  Qed.

  Lemma canon_CRef' C v t i :
    typing C v t i ->
    get_kctx C = [] ->
    get_tctx C = [] ->
    forall t' ,
      tyeq [] t (CRef t') ->
      value v ->
      exists l t',
        v = ELoc l /\
        get_hctx C $? l = Some t'.
  Proof.
    induct 1; intros Hknil Htnil t'' Htyeq Hval; try solve [invert Hval | eexists; eauto | invert Hval; eexists; eauto | invert Htyeq]; subst.
    (* { *)
    (*   rewrite Htnil in H. *)
    (*   rewrite nth_error_nil in H. *)
    (*   invert H. *)
    (* } *)
  (*   { *)
  (*     eapply CApps_CRec_CRef_false in Htyeq; propositional. *)
  (*   } *)
  (*   { *)
  (*     cases cn; simplify; invert Htyeq. *)
  (*   } *)
  (*   { *)
  (*     cases inj; simplify; invert Htyeq. *)
  (*   } *)
  (*   { *)
  (*     destruct C as ((L & W) & G); simplify; subst. *)
  (*     eapply IHtyping; eauto with db_tyeq. *)
  (*   } *)
  (* Qed. *)
  Admitted.
  
  Lemma canon_CRef W v t i :
    typing ([], W, []) v (CRef t) i ->
    value v ->
    exists l t',
      v = ELoc l /\
      W $? l = Some t'.
  Proof.
    intros Hty ?; eapply canon_CRef' in Hty; eauto with db_tyeq.
  Qed.

  Lemma progress' C e t i :
    typing C e t i ->
    get_kctx C = [] ->
    get_tctx C = [] ->
    forall h f ,
      htyping h (get_hctx C) ->
      (interp_time i <= f)%time ->
      unstuck (h, e, f).
  Proof.
    induct 1.
    {
      (* Case Var *)
      intros ? ? h f Hhty Hle.
      destruct C as ((L & W) & G).
      simplify.
      subst.
      rewrite nth_error_nil in H.
      invert H.
    }
    {
      (* Case App *)
      intros ? ? h f Hhty Hle.
      destruct C as ((L & W) & G).
      simplify.
      subst.
      assert (Hi1 : (interp_time i1 <= f)%time).
      {
        repeat rewrite interp_time_distr in Hle.
        repeat (eapply Time_add_le_elim in Hle; destruct Hle as (Hle & ?)).
        eauto.
      }
      assert (Hi2 : (interp_time i2 <= f)%time).
      {
        repeat rewrite interp_time_distr in Hle.
        repeat (eapply Time_add_le_elim in Hle; destruct Hle as (Hle & ?)).
        eauto.
      }
      eapply IHtyping1 in Hi1; eauto.
      cases Hi1; simplify.
      {
        eapply canon_CArrow in H1; eauto.
        destruct H1 as (e & ?).
        subst.
        eapply IHtyping2 in Hi2; eauto.
        cases Hi2; simplify.
        {
          right.
          exists (h, subst0_e_e e2 e, (f - 1)%time).
          econstructor; eauto.
          econstructor; eauto.
          repeat rewrite interp_time_distr in Hle.
          repeat rewrite interp_time_1 in Hle.
          repeat (eapply Time_add_le_elim in Hle; destruct Hle as (Hle & ?)).
          eauto.
        }
        {
          destruct H1 as (((h' & e2') & f') & Hstep).
          invert Hstep.
          rename e' into e0'.
          right.
          exists (h', EApp (EAbs e) e2', f').
          eapply StepPlug with (E := ECBinOp2 _ (EAbs e) E); repeat econstructor; eauto.
        }
      }
      {
        destruct H1 as (((h' & e1') & f') & Hstep).
        invert Hstep.
        right.
        exists (h', EApp e1' e2, f').
        eapply StepPlug with (E := ECBinOp1 _ E e2); repeat econstructor; eauto.
      }
    }
    {
      (* Case Abs *)
      intros.
      left.
      simplify; eauto.
    }
    {
      (* Case AppC *)
      intros ? ? h f Hhty Hle.
      destruct C as ((L & W) & G).
      simplify.
      subst.
      eapply IHtyping in Hle; eauto.
      cases Hle; simplify.
      {
        eapply canon_CForall in H1; eauto.
        destruct H1 as (e1 & ?).
        subst.
        right.
        exists (h, subst0_c_e c e1, f).
        eapply StepPlug with (E := ECHole); try eapply PlugHole.
        eauto.
      }
      {
        destruct H1 as (((h' & e1') & f') & Hstep).
        invert Hstep.
        rename e' into e0'.
        rename e1' into e'.
        right.
        exists (h', EAppC e' c, f').
        eapply StepPlug with (E := ECAppC E c); repeat econstructor; eauto.
      }
    }
    {
      (* Case AbsC *)
      intros.
      left.
      simplify; eauto.
    }
    {
      (* Case Rec *)
      intros.
      right.
      exists (h, subst0_e_e (ERec e) e, f).
      eapply StepPlug with (E := ECHole); try eapply PlugHole.
      eauto.
    }
    {
      (* Case Fold *)
      intros ? ? h f Hhty Hle.
      destruct C as ((L & W) & G).
      simplify.
      subst.
      eapply IHtyping in Hle; eauto.
      cases Hle; simplify.
      {
        left.
        simplify; eauto.
      }
      {
        destruct H as (((h' & e1') & f') & Hstep).
        invert Hstep.
        rename e' into e0'.
        rename e1' into e'.
        right.
        exists (h', EFold e', f').
        eapply StepPlug with (E := ECUnOp _ E); repeat econstructor; eauto.
      }
    }
    {
      (* Case Unfold *)
      intros ? ? h f Hhty Hle.
      destruct C as ((L & W) & G).
      simplify.
      subst.
      eapply IHtyping in Hle; eauto.
      cases Hle; simplify.
      {
        eapply canon_CRec in H; eauto.
        destruct H as (e1 & ? & Hv).
        subst.
        right.
        exists (h, e1, f).
        eapply StepPlug with (E := ECHole); try eapply PlugHole.
        eauto.
      }
      {
        destruct H as (((h' & e1') & f') & Hstep).
        invert Hstep.
        rename e' into e0'.
        rename e1' into e'.
        right.
        exists (h', EUnfold e', f').
        eapply StepPlug with (E := ECUnOp _ E); repeat econstructor; eauto.
      }
    }
    {
      (* Case Pack *)
      intros ? ? h f Hhty Hle.
      destruct C as ((L & W) & G).
      simplify.
      subst.
      eapply IHtyping in Hle; eauto.
      cases Hle; simplify.
      {
        left.
        simplify; eauto.
      }
      {
        destruct H2 as (((h' & e1') & f') & Hstep).
        invert Hstep.
        rename e' into e0'.
        rename e1' into e'.
        right.
        exists (h', EPack c e', f').
        eapply StepPlug with (E := ECPack c E); repeat econstructor; eauto.
      }
    }
    {
      (* Case Unpack *)
      intros ? ? h f Hhty Hle.
      destruct C as ((L & W) & G).
      simplify.
      subst.
      assert (Hi1 : (interp_time i1 <= f)%time).
      {
        repeat rewrite interp_time_distr in Hle.
        repeat (eapply Time_add_le_elim in Hle; destruct Hle as (Hle & ?)).
        eauto.
      }
      eapply IHtyping1 in Hi1; eauto.
      cases Hi1; simplify.
      {
        rename H into Hty.
        eapply canon_CExists in Hty; eauto.
        destruct Hty as (c & e & ? & Hv).
        subst.
        right.
        exists (h, subst0_e_e e (subst0_c_e c e2), f).
        eapply StepPlug with (E := ECHole); try eapply PlugHole.
        eauto.
      }
      {
        rename H1 into Hstep.
        destruct Hstep as (((h' & e1') & f') & Hstep).
        invert Hstep.
        right.
        exists (h', EUnpack e1' e2, f').
        eapply StepPlug with (E := ECUnpack E e2); repeat econstructor; eauto.
      }
    }
    {
      (* Case Const *)
      intros.
      left.
      simplify; eauto.
    }
    {
      (* Case Pair *)
      intros ? ? h f Hhty Hle.
      destruct C as ((L & W) & G).
      simplify.
      subst.
      assert (Hi1 : (interp_time i1 <= f)%time).
      {
        repeat rewrite interp_time_distr in Hle.
        repeat (eapply Time_add_le_elim in Hle; destruct Hle as (Hle & ?)).
        eauto.
      }
      assert (Hi2 : (interp_time i2 <= f)%time).
      {
        repeat rewrite interp_time_distr in Hle.
        repeat (eapply Time_add_le_elim in Hle; destruct Hle as (Hle & ?)).
        eauto.
      }
      eapply IHtyping1 in Hi1; eauto.
      cases Hi1; simplify.
      {
        eapply IHtyping2 in Hi2; eauto.
        cases Hi2; simplify.
        {
          left.
          simplify; eauto.
        }
        {
          destruct H2 as (((h' & e2') & f') & Hstep).
          invert Hstep.
          right.
          exists (h', EPair e1 e2', f').
          eapply StepPlug with (E := ECBinOp2 _ e1 E); repeat econstructor; eauto.
        }
      }
      {
        destruct H1 as (((h' & e1') & f') & Hstep).
        invert Hstep.
        right.
        exists (h', EPair e1' e2, f').
        eapply StepPlug with (E := ECBinOp1 _ E e2); repeat econstructor; eauto.
      }
    }
    {
      (* Case Proj *)
      intros ? ? h f Hhty Hle.
      destruct C as ((L & W) & G).
      simplify.
      subst.
      eapply IHtyping in Hle; eauto.
      destruct Hle as [He | He]; simplify.
      {
        eapply canon_CProd in He; eauto.
        destruct He as (v1 & v2 & ? & Hv1 & Hv2).
        subst.
        right.
        exists (h, proj (v1, v2) pr, f).
        eapply StepPlug with (E := ECHole); try eapply PlugHole.
        eauto.
      }
      {
        destruct He as (((h' & e') & f') & Hstep).
        invert Hstep.
        rename e'0 into e0'.
        right.
        exists (h', EProj pr e', f').
        eapply StepPlug with (E := ECUnOp _ E); repeat econstructor; eauto.
      }
    }
    {
      (* Case Inj *)
      intros ? ? h f Hhty Hle.
      destruct C as ((L & W) & G).
      simplify.
      subst.
      eapply IHtyping in Hle; eauto.
      destruct Hle as [He | He]; simplify.
      {
        left.
        simplify; eauto.
      }
      {
        destruct He as (((h' & e') & f') & Hstep).
        invert Hstep.
        rename e'0 into e0'.
        right.
        exists (h', EInj inj e', f').
        eapply StepPlug with (E := ECUnOp _ E); repeat econstructor; eauto.
      }
    }
    {
      (* Case Case *)
      intros ? ? h f Hhty Hle.
      destruct C as ((L & W) & G).
      simplify.
      subst.
      assert (Hile : (interp_time i <= f)%time).
      {
        repeat rewrite interp_time_distr in Hle.
        repeat (eapply Time_add_le_elim in Hle; destruct Hle as (Hle & ?)).
        eauto.
      }
      eapply IHtyping1 in Hile; eauto.
      destruct Hile as [He | He]; simplify.
      {
        eapply canon_CSum in He; eauto.
        destruct He as (inj & v & ? & Hv).
        subst.
        right.
        exists (h, subst0_e_e v (choose (e1, e2) inj), f).
        eapply StepPlug with (E := ECHole); try eapply PlugHole.
        eauto.
      }
      {
        destruct He as (((h' & e') & f') & Hstep).
        invert Hstep.
        rename e3 into e0.
        rename e'0 into e0'.
        right.
        exists (h', ECase e' e1 e2, f').
        eapply StepPlug with (E := ECCase E e1 e2); repeat econstructor; eauto.
      }
    }
    {
      (* Case New *)
      intros ? ? h f Hhty Hle.
      destruct C as ((L & W) & G).
      simplify.
      subst.
      eapply IHtyping in Hle; eauto.
      destruct Hle as [He | He]; simplify.
      {
        right.
        eapply htyping_fresh in Hhty.
        destruct Hhty as (l & Hl).
        exists (h $+ (l, e), ELoc l, f).
        eapply StepPlug with (E := ECHole); try eapply PlugHole.
        eauto.
      }
      {
        destruct He as (((h' & e') & f') & Hstep).
        invert Hstep.
        rename e'0 into e0'.
        right.
        exists (h', ENew e', f').
        eapply StepPlug with (E := ECUnOp _ E); repeat econstructor; eauto.
      }
    }
    {
      (* Case Read *)
      intros ? ? h f Hhty Hle.
      destruct C as ((L & W) & G).
      simplify.
      subst.
      eapply IHtyping in Hle; eauto.
      destruct Hle as [He | He]; simplify.
      {
        eapply canon_CRef in He; eauto.
        destruct He as (l & t' & ? & Hl).
        subst.
        eapply htyping_elim_exists in Hl; eauto.
        destruct Hl as (v & Hl & Hv & Hty).
        right.
        exists (h, v, f).
        eapply StepPlug with (E := ECHole); try eapply PlugHole.
        eauto.
      }
      {
        destruct He as (((h' & e') & f') & Hstep).
        invert Hstep.
        rename e'0 into e0'.
        right.
        exists (h', ERead e', f').
        eapply StepPlug with (E := ECUnOp _ E); repeat econstructor; eauto.
      }
    }
    {
      (* Case Write *)
      intros ? ? h f Hhty Hle.
      destruct C as ((L & W) & G).
      simplify.
      subst.
      assert (Hi1 : (interp_time i1 <= f)%time).
      {
        repeat rewrite interp_time_distr in Hle.
        repeat (eapply Time_add_le_elim in Hle; destruct Hle as (Hle & ?)).
        eauto.
      }
      assert (Hi2 : (interp_time i2 <= f)%time).
      {
        repeat rewrite interp_time_distr in Hle.
        repeat (eapply Time_add_le_elim in Hle; destruct Hle as (Hle & ?)).
        eauto.
      }
      eapply IHtyping1 in Hi1; eauto.
      destruct Hi1 as [He1 | He1]; simplify.
      {
        eapply IHtyping2 in Hi2; eauto.
        destruct Hi2 as [He2 | He2]; simplify.
        {
          eapply canon_CRef in He1; eauto.
          destruct He1 as (l & t' & ? & Hl).
          subst.
          eapply htyping_elim_exists in Hl; eauto.
          destruct Hl as (v & Hl & Hv & Hty).
          right.
          exists (h $+ (l, e2), ETT, f).
          eapply StepPlug with (E := ECHole); try eapply PlugHole.
          eauto.
        }
        {
          destruct He2 as (((h' & e2') & f') & Hstep).
          invert Hstep.
          right.
          exists (h', EWrite e1 e2', f').
          eapply StepPlug with (E := ECBinOp2 _ e1 E); repeat econstructor; eauto.
        }
      }
      {
        destruct He1 as (((h' & e1') & f') & Hstep).
        invert Hstep.
        right.
        exists (h', EWrite e1' e2, f').
        eapply StepPlug with (E := ECBinOp1 _ E e2); repeat econstructor; eauto.
      }
    }
    {
      (* Case Loc *)
      intros.
      left.
      simplify; eauto.
    }
    {
      (* Case Sub *)
      intros ? ? h f Hhty Hle.
      destruct C as ((L & W) & G).
      simplify.
      subst.
      eapply IHtyping; eauto.
      eapply interp_prop_le_interp_time in H1.
      eauto with time_order.
    }
  Qed.

  Lemma progress W s t i :
    ctyping W s t i ->
    unstuck s.
  Proof.
    unfold ctyping in *.
    simplify.
    destruct s as ((h & e) & f).
    propositional.
    eapply progress'; eauto.
  Qed.

  Fixpoint KArrows args result :=
    match args with
    | [] => result
    | arg :: args => KArrow arg (KArrows args result)
    end.

  Lemma invert_typing_App C e1 e2 t i :
    typing C (EApp e1 e2) t i ->
    exists t' t2 i1 i2 i3 ,
      tyeq (get_kctx C) t t' /\
      typing C e1 (CArrow t2 i3 t') i1 /\
      typing C e2 t2 i2 /\
      interp_prop (get_kctx C) (i1 + i2 + T1 + i3 <= i)%idx.
  Proof.
    induct 1; openhyp; repeat eexists_split;
      eauto;
      eauto with db_tyeq.
  Qed.  

  Lemma invert_typing_Abs C e t i :
    typing C (EAbs e) t i ->
    exists t1 i' t2 ,
      tyeq (get_kctx C) t (CArrow t1 i' t2) /\
      kinding (get_kctx C) t1 KType /\
      typing (add_typing_ctx t1 C) e t2 i'.
  Proof.
    induct 1; openhyp; repeat eexists_split; eauto; eauto with db_tyeq.
  Qed.  

  Lemma invert_typing_Unfold C e t2 i :
    typing C (EUnfold e) t2 i ->
    exists t k t1 cs i',
      tyeq (get_kctx C) t2 (CApps (subst0_c_c t t1) cs) /\
      t = CRec k t1 /\
      typing C e (CApps t cs) i' /\
      interp_prop (get_kctx C) (i' <= i)%idx.
  Proof.
    induct 1; openhyp; repeat eexists_split; eauto; eauto with db_tyeq.
  Qed.  

  Lemma invert_typing_Fold C e t' i :
    typing C (EFold e) t' i ->
    exists t t1 cs k t2 i',
      tyeq (get_kctx C) t' t /\
      t = CApps t1 cs /\
      t1 = CRec k t2 /\
      kinding (get_kctx C) t KType /\
      typing C e (CApps (subst0_c_c t1 t2) cs) i' /\
      interp_prop (get_kctx C) (i' <= i)%idx.
  Proof.
    induct 1; openhyp; repeat eexists_split; eauto; eauto with db_tyeq.
  Qed.  

  Lemma invert_typing_Rec C e t i :
    typing C (ERec e) t i ->
    exists n e1 ,
      e = EAbsCs n (EAbs e1) /\
      kinding (get_kctx C) t KType /\
      typing (add_typing_ctx t C) e t T0.
  Proof.
    induct 1; openhyp; repeat eexists_split; eauto; eauto with db_tyeq.
    {
      subst.
      eapply kinding_tyeq; eauto.
    }
    {
      subst.
      eapply add_typing_ctx_tyeq; eauto.
      eapply TyTyeq; eauto.
      rewrite get_kctx_add_typing_ctx.
      eauto.
    }
  Qed.  

  Lemma invert_typing_Unpack C e1 e2 t2'' i :
    typing C (EUnpack e1 e2) t2'' i ->
    exists t2 t i1 k i2 ,
      tyeq (get_kctx C) t2'' t2 /\
      typing C e1 (CExists k t) i1 /\
      typing (add_typing_ctx t (add_kinding_ctx k C)) e2 (shift0_c_c t2) (shift0_c_c i2) /\
      interp_prop (get_kctx C) (i1 + i2 <= i)%idx.
  Proof.
    induct 1; openhyp; repeat eexists_split; eauto; eauto with db_tyeq.
  Qed.

  Lemma invert_typing_Pack C c e t i :
    typing C (EPack c e) t i ->
    exists t1 k i' ,
      tyeq (get_kctx C) t (CExists k t1) /\
      kinding (get_kctx C) (CExists k t1) KType /\
      kinding (get_kctx C) c k /\
      typing C e (subst0_c_c c t1) i' /\
      interp_prop (get_kctx C) (i' <= i)%idx.
  Proof.
    induct 1; openhyp; repeat eexists_split; eauto; eauto with db_tyeq.
  Qed.

  Lemma invert_typing_Read C e t i :
    typing C (ERead e) t i ->
    exists i' ,
      typing C e (CRef t) i' /\
      interp_prop (get_kctx C) (i' <= i)%idx.
  Proof.
    induct 1; openhyp; repeat eexists_split; eauto; eauto with db_tyeq.
    eapply TySub; try eapply H2; try econstructor; eauto.
  Qed.

  Lemma invert_typing_Loc C l t i :
    typing C (ELoc l) t i ->
    exists t' ,
      tyeq (get_kctx C) t (CRef t') /\
      get_hctx C $? l = Some t'.
  Proof.
    induct 1; openhyp; repeat eexists_split; eauto; eauto with db_tyeq.
  Qed.

  Lemma invert_typing_Write C e1 e2 t i :
    typing C (EWrite e1 e2) t i ->
    exists t' i1 i2 ,
      tyeq (get_kctx C) t CTypeUnit /\
      typing C e1 (CRef t') i1 /\
      typing C e2 t' i2 /\
      interp_prop (get_kctx C) (i1 + i2 <= i)%idx.
  Proof.
    induct 1; openhyp; repeat eexists_split; eauto; eauto with db_tyeq.
  Qed.

  Lemma invert_typing_New C e t i :
    typing C (ENew e) t i ->
    exists t' i' ,
      tyeq (get_kctx C) t (CRef t') /\
      typing C e t' i' /\
      interp_prop (get_kctx C) (i' <= i)%idx.
  Proof.
    induct 1; openhyp; repeat eexists_split; eauto; eauto with db_tyeq.
  Qed.

  Lemma invert_typing_AppC C e c t i :
    typing C (EAppC e c) t i ->
    exists t' i' k ,
      tyeq (get_kctx C) t (subst0_c_c c t') /\
      typing C e (CForall k t') i' /\
      kinding (get_kctx C) c k /\
      interp_prop (get_kctx C) (i' <= i)%idx.
  Proof.
    induct 1; openhyp; repeat eexists_split; eauto; eauto with db_tyeq.
  Qed.

  Lemma invert_typing_AbsC C e t i :
    typing C (EAbsC e) t i ->
    exists t' k ,
      tyeq (get_kctx C) t (CForall k t') /\
      value e /\
      wfkind (get_kctx C) k /\
      typing (add_kinding_ctx k C) e t' T0.
  Proof.
    induct 1; openhyp; repeat eexists_split; eauto; eauto with db_tyeq.
  Qed.

  Lemma invert_typing_Proj C pr e t i :
    typing C (EProj pr e) t i ->
    exists t1 t2 i' ,
      tyeq (get_kctx C) t (proj (t1, t2) pr) /\
      typing C e (CProd t1 t2) i' /\
      interp_prop (get_kctx C) (i' <= i)%idx.
  Proof.
    induct 1; openhyp; repeat eexists_split; eauto; eauto with db_tyeq.
  Qed.

  Lemma invert_typing_Pair C e1 e2 t i :
    typing C (EPair e1 e2) t i ->
    exists t1 t2 i1 i2 ,
      tyeq (get_kctx C) t (CProd t1 t2) /\
      typing C e1 t1 i1 /\
      typing C e2 t2 i2 /\
      interp_prop (get_kctx C) (i1 + i2 <= i)%idx.
  Proof.
    induct 1; openhyp; repeat eexists_split; eauto; eauto with db_tyeq.
  Qed.

  Lemma invert_typing_Case C e e1 e2 t i :
    typing C (ECase e e1 e2) t i ->
    exists t1 t2 i0 i1 i2 ,
      typing C e (CSum t1 t2) i0 /\
      typing (add_typing_ctx t1 C) e1 t i1 /\
      typing (add_typing_ctx t2 C) e2 t i2 /\
      interp_prop (get_kctx C) (i0 + Tmax i1 i2 <= i)%idx.
  Proof.
    induct 1; openhyp; repeat eexists_split; eauto; eauto with db_tyeq.
    {
      eapply TyTyeq; eauto.
      rewrite get_kctx_add_typing_ctx.
      eauto.
    }
    {
      eapply TyTyeq; eauto.
      rewrite get_kctx_add_typing_ctx.
      eauto.
    }
  Qed.

  Lemma invert_typing_Inj C inj e t i :
    typing C (EInj inj e) t i ->
    exists t' t'' i' ,
      tyeq (get_kctx C) t (choose (CSum t' t'', CSum t'' t') inj) /\
      typing C e t' i' /\
      kinding (get_kctx C) t'' KType /\
      interp_prop (get_kctx C) (i' <= i)%idx.
  Proof.
    induct 1; openhyp; repeat eexists_split; eauto; eauto with db_tyeq.
  Qed.

  Lemma invert_typing_BinOpPrim C opr e1 e2 t i : typing C (EBinOp (EBPrim opr) e1 e2) t i -> False.
  Proof.
    induct 1; openhyp; repeat eexists_split; eauto; eauto with db_tyeq.
  Qed.

  Lemma preservation0 s s' :
    astep s s' ->
    forall W t i,
      ctyping W s t i ->
      let df := (get_fuel s - get_fuel s')%time in
      (df <= interp_time i)%time /\
      exists W',
        ctyping W' s' t (Tminus i (Tconst df)) /\
        (W $<= W').
  Proof.
    invert 1; simplify.
    {
      (* Case Beta *)
      destruct H as (Hty & Hhty & Hle).
      rename t into f.
      rename t0 into t.
      eapply invert_typing_App in Hty.
      destruct Hty as (t' & t2 & i1 & i2 & i3 & Htyeq & Hty1 & Hty2 & Hle2).
      simplify.
      eapply invert_typing_Abs in Hty1.
      destruct Hty1 as (t1 & i' & t3 & Htyeq2 & Hkd & Hty1).
      simplify.
      eapply invert_tyeq_CArrow in Htyeq2.
      destruct Htyeq2 as (Htyeq2 & Hieq & Htyeq3).
      split.
      {
        rewrite Time_minus_minus_cancel by eauto.
        eapply interp_prop_le_interp_time in Hle2.
        repeat rewrite interp_time_distr in Hle2.
        repeat rewrite interp_time_1 in Hle2.
        repeat (eapply Time_add_le_elim in Hle2; destruct Hle2 as (Hle2 & ?)).
        eauto.
      }
      exists W.
      repeat try_split.
      {
        eapply TySub.
        {
          eapply ty_subst0_e_e with (G := []) in Hty1; eauto.
          eapply TyTyeq; eauto.
        }
        {
          simplify.
          eapply tyeq_sym.
          eapply tyeq_trans; eauto.
        }
        {
          simplify.
          rewrite Time_minus_minus_cancel by eauto.
          eapply interp_prop_le_interp_time in Hle2.
          repeat rewrite interp_time_distr in Hle2.
          repeat rewrite interp_time_1 in Hle2.
          copy Hle2 Hle2'.
          repeat (eapply Time_add_le_elim in Hle2; destruct Hle2 as (Hle2 & ?)).
          eapply interp_time_interp_prop_le.
          rewrite interp_time_minus_distr.
          rewrite interp_time_1.
          eapply Time_minus_move_left; eauto.
          eapply interp_prop_eq_interp_time in Hieq.
          rewrite <- Hieq in *.
          eapply Time_le_trans; [| eapply Hle2'].
          rotate_lhs.
          cancel.
          finish.
        }
      }
      {
        eapply Hhty.
      }
      {
        rewrite Time_minus_minus_cancel by eauto.
        rewrite interp_time_minus_distr.
        rewrite interp_time_1.
        eapply Time_minus_cancel.
        eauto.
      }
      {
        eapply includes_intro.
        eauto.
      }
    }
    {
      (* Case Unfold-Fold *)
      destruct H as (Hty & Hhty & Hle).
      rename t into f.
      rename t0 into t.
      eapply invert_typing_Unfold in Hty.
      destruct Hty as (t1 & k & t2 & cs& i'& Htyeq & ? & Hty & Hle2).
      subst.
      simplify.
      subst.
      eapply invert_typing_Fold in Hty.
      destruct Hty as (? & ? & cs' & k' & t2' & i'' & Htyeq2 & ? & ? & Hkd & Hty & Hle3).
      subst.
      simplify.
      eapply invert_tyeq_CApps_CRec in Htyeq2.
      destruct Htyeq2 as (Hsorteq & Htyeq2 & Htyeqcs).
      split.
      {
        rewrite Time_a_minus_a.
        eapply Time_0_le_x.
      }
      exists W.
      repeat try_split.
      {
        eapply TySub.
        {
          eapply Hty.
        }
        {
          (* tyeq *)
          simplify.
          eapply tyeq_sym.
          eapply tyeq_trans; [eapply Htyeq |].
          Lemma TyEqApps L cs cs' :
            Forall2 (tyeq L) cs cs' ->
            forall t t',
              tyeq L t t' ->
              tyeq L (CApps t cs) (CApps t' cs').
          Proof.
            induct 1; simplify; eauto.
            eapply IHForall2.
          (* Admitted. *)
            eapply TyEqApp; eauto.
            (* econstructor; eauto. *)
          Qed.
          
          eapply TyEqApps; eauto.
          eapply tyeq_subst0_c_c; eauto.
          econstructor; eauto.
        }
        {
          simplify.
          rewrite Time_a_minus_a.
          eapply interp_time_interp_prop_le.
          rewrite interp_time_minus_distr.
          rewrite interp_time_0.
          rewrite Time_minus_0.
          eapply interp_prop_le_interp_time in Hle2.
          eapply interp_prop_le_interp_time in Hle3.
          eauto with time_order.
        }
      }
      {
        eapply Hhty.
      }
      {
        simplify.
        rewrite Time_a_minus_a.
        rewrite interp_time_minus_distr.
        rewrite interp_time_0.
        rewrite Time_minus_0.
        eauto.
      }
      {
        eapply includes_intro.
        eauto.
      }
    }
    {
      (* Case Rec *)
      destruct H as (Hty & Hhty & Hle).
      rename t into f.
      rename t0 into t.
      generalize Hty; intro Hty0.
      eapply invert_typing_Rec in Hty.
      destruct Hty as (n & e1 & ? & Hkd & Hty).
      simplify.
      split.
      {
        rewrite Time_a_minus_a.
        eapply Time_0_le_x.
      }
      exists W.
      repeat try_split.
      {
        eapply ty_subst0_e_e_T0 with (G := []) in Hty; eauto.
        {
          eapply TySub.
          {
            eapply Hty.
          }
          {
            eapply tyeq_refl.
          }
          {
            simplify.
            rewrite Time_a_minus_a.
            eapply interp_time_interp_prop_le.
            rewrite interp_time_minus_distr.
            rewrite interp_time_0.
            rewrite Time_minus_0.
            eauto with time_order.
          }
        }
        {
          subst.
          econstructor; eauto.
        }
      }
      {
        eapply Hhty.
      }
      {
        simplify.
        rewrite Time_a_minus_a.
        rewrite interp_time_minus_distr.
        rewrite interp_time_0.
        rewrite Time_minus_0.
        eauto.
      }
      {
        eapply includes_intro.
        eauto.
      }
    }
    {
      (* Case Unpack-Pack *)
      destruct H as (Hty & Hhty & Hle).
      rename t into f.
      rename t0 into t.
      eapply invert_typing_Unpack in Hty.
      destruct Hty as (t2 & t0 & i1 & k & i2 & Htyeq & Hty1 & Hty2 & Hle2).
      subst.
      simplify.
      eapply invert_typing_Pack in Hty1.
      destruct Hty1 as (t1 & k' & i' & Htyeq2 & Hkd1 & Hkdc' & Htyv & Hle3).
      subst.
      simplify.
      eapply invert_tyeq_CExists in Htyeq2.
      destruct Htyeq2 as (Htyeq2 & Hsorteq).
      assert (Hkdc : kinding [] c k).
      {
        eapply KdEq; eauto.
      }
      eapply ty_subst0_c_e with (L := []) in Hty2; eauto.
      simplify.
      rewrite fmap_map_subst0_shift0 in Hty2.
      repeat rewrite subst0_c_c_shift0 in Hty2.
      assert (Htyv' : typing ([], W, []) v (subst0_c_c c t0) i').
      {
        eapply TyTyeq; eauto.
        simplify.
        eapply tyeq_subst0_c_c; eauto with db_tyeq.
      }
      eapply ty_subst0_e_e with (G := []) in Hty2; eauto.
      split.
      {
        rewrite Time_a_minus_a.
        eapply Time_0_le_x.
      }
      exists W.
      repeat try_split.
      {
        eapply TySub.
        {
          eapply Hty2.
        }
        {
          (* tyeq *)
          simplify.
          eapply tyeq_sym; eauto.
        }
        {
          simplify.
          rewrite Time_a_minus_a.
          eapply interp_time_interp_prop_le.
          rewrite interp_time_minus_distr.
          rewrite interp_time_0.
          rewrite Time_minus_0.
          eapply interp_prop_le_interp_time in Hle2.
          eapply interp_prop_le_interp_time in Hle3.
          repeat rewrite interp_time_distr in Hle2.
          repeat rewrite interp_time_1 in Hle2.
          trans_rhs Hle2.
          finish.
        }
      }
      {
        eapply Hhty.
      }
      {
        simplify.
        rewrite Time_a_minus_a.
        rewrite interp_time_minus_distr.
        rewrite interp_time_0.
        rewrite Time_minus_0.
        eauto.
      }
      {
        eapply includes_intro.
        eauto.
      }
    }
    {
      (* Case Read *)
      destruct H as (Hty & Hhty & Hle).
      rename t into f.
      rename t0 into t.
      eapply invert_typing_Read in Hty.
      destruct Hty as (i' & Hty & Hle2).
      simplify.
      eapply invert_typing_Loc in Hty.
      destruct Hty as (t' & Htyeq & Hl).
      simplify.
      generalize Hhty; intro Hhty0.
      eapply htyping_elim in Hhty; eauto.
      destruct Hhty as (Hval & Htyv).
      eapply invert_tyeq_CRef in Htyeq.
      split.
      {
        rewrite Time_a_minus_a.
        eapply Time_0_le_x.
      }
      exists W.
      repeat try_split.
      {
        eapply TySub.
        {
          eapply Htyv.
        }
        {
          (* tyeq *)
          simplify.
          eapply tyeq_sym; eauto.
        }
        {
          simplify.
          rewrite Time_a_minus_a.
          eapply interp_time_interp_prop_le.
          rewrite interp_time_minus_distr.
          repeat rewrite interp_time_0.
          rewrite Time_minus_0.
          eauto with time_order.
        }
      }
      {
        eapply Hhty0.
      }
      {
        simplify.
        rewrite Time_a_minus_a.
        rewrite interp_time_minus_distr.
        repeat rewrite interp_time_0.
        rewrite Time_minus_0.
        eauto.
      }
      {
        eapply includes_intro.
        eauto.
      }
    }
    {
      (* Case Write *)
      destruct H as (Hty & Hhty & Hle).
      rename t into f.
      rename t0 into t.
      eapply invert_typing_Write in Hty.
      destruct Hty as (t' & i1 & i2 & Htyeq & Hty1 & Hty2 & Hle2).
      eapply invert_typing_Loc in Hty1.
      destruct Hty1 as (t'' & Htyeq2 & Hl).
      simplify.
      eapply invert_tyeq_CRef in Htyeq2.
      copy Hhty Hhty0.
      eapply htyping_elim in Hhty; eauto.
      destruct Hhty as (Hval' & Htyv').
      split.
      {
        rewrite Time_a_minus_a.
        eauto with time_order.
      }
      exists W.
      repeat try_split.
      {
        eapply TySub.
        {
          eapply TyETT.
        }
        {
          simplify.
          eapply tyeq_sym; eauto.
        }
        {
          simplify.
          rewrite Time_a_minus_a.
          eapply interp_time_interp_prop_le.
          rewrite interp_time_minus_distr.
          repeat rewrite interp_time_0.
          rewrite Time_minus_0.
          eauto with time_order.
        }
      }
      {
        eapply htyping_upd; eauto.
        eapply TyTyeq.
        {
          eapply Hty2.
        }
        {
          simplify.
          eauto.
        }
      }
      {
        simplify.
        rewrite Time_a_minus_a.
        rewrite interp_time_minus_distr.
        repeat rewrite interp_time_0.
        rewrite Time_minus_0.
        eauto.
      }
      {
        eapply includes_intro.
        eauto.
      }
    }
    {
      (* Case New *)
      destruct H as (Hty & Hhty & Hle).
      rename t into f.
      rename t0 into t.
      eapply invert_typing_New in Hty.
      destruct Hty as (t' & i' & Htyeq & Hty & Hle2).
      simplify.
      split.
      {
        rewrite Time_a_minus_a.
        eauto with time_order.
      }
      exists (W $+ (l, t')).
      repeat try_split.
      {
        eapply TySub.
        {
          eapply TyLoc.
          simplify.
          eauto.
        }
        {
          simplify.
          eapply tyeq_sym; eauto.
        }
        {
          simplify.
          rewrite Time_a_minus_a.
          eapply interp_time_interp_prop_le.
          rewrite interp_time_minus_distr.
          repeat rewrite interp_time_0.
          rewrite Time_minus_0.
          eauto with time_order.
        }
      }
      {
        eapply htyping_new in Hhty; eauto.
      }
      {
        simplify.
        rewrite Time_a_minus_a.
        rewrite interp_time_minus_distr.
        repeat rewrite interp_time_0.
        rewrite Time_minus_0.
        eauto.
      }
      {
        eapply includes_intro.
        intros k v' Hk.
        cases (l ==n k); subst.
        {
          assert (HWk : W $? k = None).
          {
            eapply htyping_elim_None; eauto.
          }
          simplify.
          eauto.
        }
        simplify.
        eauto.
      }
    }
    {
      (* Case AppC *)
      destruct H as (Hty & Hhty & Hle).
      rename t into f.
      rename t0 into t.
      eapply invert_typing_AppC in Hty.
      destruct Hty as (t' & i' & k' & Htyeq & Hty & Hkdc & Hle2).
      simplify.
      eapply invert_typing_AbsC in Hty.
      destruct Hty as (t'' & k & Htyeq2 & Hval & Hwfk & Hty).
      simplify.
      eapply invert_tyeq_CForall in Htyeq2.
      destruct Htyeq2 as (Htyeq2 & Hsorteq).
      assert (Hkdck : kinding [] c k).
      {
        eapply KdEq; eauto.
        eapply sorteq_sym; eauto.
      }
      split.
      {
        rewrite Time_a_minus_a.
        eauto with time_order.
      }
      exists W.
      repeat try_split.
      {
        eapply TySub.
        {
          eapply ty_subst0_c_e with (G := []) in Hty; eauto.
          simplify.
          rewrite fmap_map_subst0_shift0 in Hty.
          eauto.
        }
        {
          simplify.
          (* tyeq *)
          eapply tyeq_sym.
          eapply tyeq_trans; eauto.
          eapply tyeq_subst0_c_c; eauto with db_tyeq.
        }
        {
          simplify.
          rewrite subst0_c_c_Const.
          rewrite Time_a_minus_a.
          eapply interp_time_interp_prop_le.
          rewrite interp_time_minus_distr.
          repeat rewrite interp_time_0.
          rewrite Time_minus_0.
          eauto with time_order.
        }
      }
      {
        eapply Hhty.
      }
      {
        simplify.
        rewrite Time_a_minus_a.
        rewrite interp_time_minus_distr.
        repeat rewrite interp_time_0.
        rewrite Time_minus_0.
        eauto.
      }
      {
        eapply includes_intro.
        eauto.
      }
    }
    {
      (* Case Proj-Pair *)
      destruct H as (Hty & Hhty & Hle).
      rename t into f.
      rename t0 into t.
      eapply invert_typing_Proj in Hty.
      destruct Hty as (t1 & t2 & i' & Htyeq & Hty & Hle2).
      simplify.
      eapply invert_typing_Pair in Hty.
      destruct Hty as (t1' & t2' & i1 & i2 & Htyeq2 & Hty1 & Hty2 & Hle3).
      simplify.
      eapply invert_tyeq_CProd in Htyeq2.
      destruct Htyeq2 as (Htyeq2 & Htyeq3).
      split.
      {
        rewrite Time_a_minus_a.
        eauto with time_order.
      }
      exists W.
      repeat try_split.
      {
        cases pr; simplify.
        {
          eapply TySub; eauto.
          {
            simplify.
            eapply tyeq_sym.
            eapply tyeq_trans; eauto.
          }
          {
            simplify.
            rewrite Time_a_minus_a.
            eapply interp_time_interp_prop_le.
            rewrite interp_time_minus_distr.
            repeat rewrite interp_time_0.
            rewrite Time_minus_0.
            eapply interp_prop_le_interp_time in Hle2.
            eapply interp_prop_le_interp_time in Hle3.
            repeat rewrite interp_time_distr in Hle3.
            trans_rhs Hle2.
            trans_rhs Hle3.
            rotate_rhs.
            finish.
          }
        }
        {
          eapply TySub; eauto.
          {
            simplify.
            eapply tyeq_sym.
            eapply tyeq_trans; eauto.
          }
          {
            simplify.
            rewrite Time_a_minus_a.
            eapply interp_time_interp_prop_le.
            rewrite interp_time_minus_distr.
            repeat rewrite interp_time_0.
            rewrite Time_minus_0.
            eapply interp_prop_le_interp_time in Hle2.
            eapply interp_prop_le_interp_time in Hle3.
            repeat rewrite interp_time_distr in Hle3.
            trans_rhs Hle2.
            trans_rhs Hle3.
            finish.
          }
        }
      }
      {
        eapply Hhty.
      }
      {
        simplify.
        rewrite Time_a_minus_a.
        rewrite interp_time_minus_distr.
        repeat rewrite interp_time_0.
        rewrite Time_minus_0.
        eauto.
      }
      {
        eapply includes_intro.
        eauto.
      }
    }
    {
      (* Case Case-Inj *)
      destruct H as (Hty & Hhty & Hle).
      rename t into f.
      rename t0 into t.
      eapply invert_typing_Case in Hty.
      destruct Hty as (t1 & t2 & i0 & i1 & i2 & Hty0 & Hty1 & Hty2 & Hle2).
      simplify.
      eapply invert_typing_Inj in Hty0.
      destruct Hty0 as (t' & t'' & i' & Htyeq & Hty0 & Hkd & Hle3).
      simplify.
      split.
      {
        rewrite Time_a_minus_a.
        eauto with time_order.
      }
      exists W.
      repeat try_split.
      {
        cases inj; simplify.
        {
          eapply invert_tyeq_CSum in Htyeq.
          destruct Htyeq as (Htyeq1 & Htyeq2).
          eapply TyLe; eauto.
          {
            eapply ty_subst0_e_e with (G := []) in Hty1; eauto.
            eapply TyTyeq; eauto.
            simplify.
            eapply tyeq_sym; eauto.
          }
          {
            simplify.
            rewrite Time_a_minus_a.
            eapply interp_time_interp_prop_le.
            rewrite interp_time_minus_distr.
            repeat rewrite interp_time_0.
            rewrite Time_minus_0.
            eapply interp_prop_le_interp_time in Hle2.
            trans_rhs Hle2.
            rewrite interp_time_distr.
            eapply interp_prop_le_interp_time in Hle3.
            rewrite interp_time_max.
            eapply Time_le_trans.
            {
              instantiate (1 := (interp_time i1 + interp_time i0)%time).
              rotate_rhs.
              finish.
            }
            rotate_rhs.
            cancel.
            eauto with time_order.
          }
        }
        {
          eapply invert_tyeq_CSum in Htyeq.
          destruct Htyeq as (Htyeq1 & Htyeq2).
          eapply TyLe; eauto.
          {
            eapply ty_subst0_e_e with (G := []) in Hty2; eauto.
            eapply TyTyeq; eauto.
            simplify.
            eapply tyeq_sym; eauto.
          }
          {
            simplify.
            rewrite Time_a_minus_a.
            eapply interp_time_interp_prop_le.
            rewrite interp_time_minus_distr.
            repeat rewrite interp_time_0.
            rewrite Time_minus_0.
            eapply interp_prop_le_interp_time in Hle2.
            trans_rhs Hle2.
            rewrite interp_time_distr.
            eapply interp_prop_le_interp_time in Hle3.
            rewrite interp_time_max.
            eapply Time_le_trans.
            {
              instantiate (1 := (interp_time i2 + interp_time i0)%time).
              rotate_rhs.
              finish.
            }
            rotate_rhs.
            cancel.
            eauto with time_order.
          }
        }
      }
      {
        eapply Hhty.
      }
      {
        simplify.
        rewrite Time_a_minus_a.
        rewrite interp_time_minus_distr.
        repeat rewrite interp_time_0.
        rewrite Time_minus_0.
        eauto.
      }
      {
        eapply includes_intro.
        eauto.
      }
    }
  Qed.

  Lemma generalize_plug : forall C e e_all,
      plug C e e_all ->
      forall W t i,
        typing ([], W, []) e_all t i ->
        exists t1 i1,
          typing ([], W, []) e t1 i1 /\
          interp_prop [] (i1 <= i)%idx /\
          forall e' e_all' W' i1',
            plug C e' e_all' ->
            typing ([], W', []) e' t1 i1' ->
            interp_prop [] (i1' <= i1)%idx ->
            W $<= W' ->
            typing ([], W', []) e_all' t (i1' + Tminus i i1)%idx.
  Proof.
    induct 1; intros W t i Hty.
    {
      exists t, i.
      repeat split; eauto.
      {
        eapply interp_time_interp_prop_le.
        eauto with time_order.
      }
      intros.
      invert H.
      eapply TyLe; eauto.
      simplify.
      eapply interp_time_interp_prop_le.
      rewrite interp_time_distr.
      rotate_rhs.
      finish.
    }
    {
      cases opr.
      {
        (* Case Proj *)
        eapply invert_typing_Proj in Hty.
        destruct Hty as (t1 & t2 & i' & Htyeq & Hty & Hle).
        simplify.
        eapply IHplug in Hty; eauto.
        destruct Hty as (t0 & i0 & Hty1 & Hle2 & HE).
        exists t0, i0.
        repeat split; eauto.
        {
          eapply interp_time_interp_prop_le.
          eapply interp_prop_le_interp_time in Hle.
          eapply interp_prop_le_interp_time in Hle2.
          eauto with time_order.
        }
        intros e'' e_all' W' i1' Hplug Htye'' Hle3 Hincl.
        invert Hplug.
        rename e'0 into e_all''.
        rename H4 into Hplug.
        eapply HE in Hplug; eauto.
        eapply TySub.
        {
          eapply TyProj; eauto.
        }
        {
          simplify.
          eapply tyeq_sym; eauto.
        }
        {
          simplify.
          eapply interp_time_interp_prop_le.
          repeat rewrite interp_time_distr.
          rotate_lhs.
          rotate_rhs.
          cancel.
          repeat rewrite interp_time_minus_distr.
          eapply Time_minus_cancel.
          eapply interp_prop_le_interp_time in Hle.
          eauto.
        }
      }
      {
        (* Case Inj *)
        eapply invert_typing_Inj in Hty.
        destruct Hty as (t1 & t2 & i' & Htyeq & Hty & Hkd & Hle).
        simplify.
        eapply IHplug in Hty; eauto.
        destruct Hty as (t0 & i0 & Hty1 & Hle2 & HE).
        exists t0, i0.
        repeat split; eauto.
        {
          eapply interp_time_interp_prop_le.
          eapply interp_prop_le_interp_time in Hle.
          eapply interp_prop_le_interp_time in Hle2.
          eauto with time_order.
        }
        intros e'' e_all' W' i1' Hplug Htye'' Hle3 Hincl.
        invert Hplug.
        rename e'0 into e_all''.
        rename H4 into Hplug.
        eapply HE in Hplug; eauto.
        cases inj; simplify.
        {
          eapply TySub.
          {
            eapply TyInj with (t' := t2); eauto.
          }
          {
            simplify.
            eapply tyeq_sym; eauto.
          }
          {
            simplify.
            eapply interp_time_interp_prop_le.
            repeat rewrite interp_time_distr.
            rotate_lhs.
            rotate_rhs.
            cancel.
            repeat rewrite interp_time_minus_distr.
            eapply Time_minus_cancel.
            eapply interp_prop_le_interp_time in Hle.
            eauto.
          }
        }
        {
          eapply TySub.
          {
            eapply TyInj with (t' := t2); eauto.
          }
          {
            simplify.
            eapply tyeq_sym; eauto.
          }
          {
            simplify.
            eapply interp_time_interp_prop_le.
            repeat rewrite interp_time_distr.
            rotate_lhs.
            rotate_rhs.
            cancel.
            repeat rewrite interp_time_minus_distr.
            eapply Time_minus_cancel.
            eapply interp_prop_le_interp_time in Hle.
            eauto.
          }
        }
      }
      {
        (* Case Fold *)
        eapply invert_typing_Fold in Hty.
        destruct Hty as (t0 & t1 & cs & k & t2 & i' & Htyeq & ? & ? & Hkd & Hty & Hle).
        subst.
        simplify.
        eapply IHplug in Hty; eauto.
        destruct Hty as (t0 & i0 & Hty1 & Hle2 & HE).
        exists t0, i0.
        repeat split; eauto.
        {
          eapply interp_time_interp_prop_le.
          eapply interp_prop_le_interp_time in Hle.
          eapply interp_prop_le_interp_time in Hle2.
          eauto with time_order.
        }
        intros e'' e_all' W' i1' Hplug Htye'' Hle3 Hincl.
        invert Hplug.
        rename e'0 into e_all''.
        rename H4 into Hplug.
        eapply HE in Hplug; eauto.
        eapply TySub.
        {
          eapply TyFold; eauto.
        }
        {
          simplify.
          eapply tyeq_sym; eauto.
        }
        {
          simplify.
          eapply interp_time_interp_prop_le.
          repeat rewrite interp_time_distr.
          rotate_lhs.
          rotate_rhs.
          cancel.
          repeat rewrite interp_time_minus_distr.
          eapply Time_minus_cancel.
          eapply interp_prop_le_interp_time in Hle.
          eauto.
        }
      }
      {
        (* Case Unfold *)
        eapply invert_typing_Unfold in Hty.
        destruct Hty as (t0 & k & t1 & cs & i' & Htyeq & ? & Hty & Hle).
        subst.
        simplify.
        eapply IHplug in Hty; eauto.
        destruct Hty as (t0 & i0 & Hty1 & Hle2 & HE).
        exists t0, i0.
        repeat split; eauto.
        {
          eapply interp_time_interp_prop_le.
          eapply interp_prop_le_interp_time in Hle.
          eapply interp_prop_le_interp_time in Hle2.
          eauto with time_order.
        }
        intros e'' e_all' W' i1' Hplug Htye'' Hle3 Hincl.
        invert Hplug.
        rename e'0 into e_all''.
        rename H4 into Hplug.
        eapply HE in Hplug; eauto.
        eapply TySub.
        {
          eapply TyUnfold; eauto.
        }
        {
          simplify.
          eapply tyeq_sym; eauto.
        }
        {
          simplify.
          eapply interp_time_interp_prop_le.
          repeat rewrite interp_time_distr.
          rotate_lhs.
          rotate_rhs.
          cancel.
          repeat rewrite interp_time_minus_distr.
          eapply Time_minus_cancel.
          eapply interp_prop_le_interp_time in Hle.
          eauto.
        }
      }
      {
        (* Case New *)
        eapply invert_typing_New in Hty.
        destruct Hty as (t' & i' & Htyeq & Hty & Hle).
        simplify.
        eapply IHplug in Hty; eauto.
        destruct Hty as (t0 & i0 & Hty1 & Hle2 & HE).
        exists t0, i0.
        repeat split; eauto.
        {
          eapply interp_time_interp_prop_le.
          eapply interp_prop_le_interp_time in Hle.
          eapply interp_prop_le_interp_time in Hle2.
          eauto with time_order.
        }
        intros e'' e_all' W' i1' Hplug Htye'' Hle3 Hincl.
        invert Hplug.
        rename e'0 into e_all''.
        rename H4 into Hplug.
        eapply HE in Hplug; eauto.
        eapply TySub.
        {
          eapply TyNew; eauto.
        }
        {
          simplify.
          eapply tyeq_sym; eauto.
        }
        {
          simplify.
          eapply interp_time_interp_prop_le.
          repeat rewrite interp_time_distr.
          rotate_lhs.
          rotate_rhs.
          cancel.
          repeat rewrite interp_time_minus_distr.
          eapply Time_minus_cancel.
          eapply interp_prop_le_interp_time in Hle.
          eauto.
        }
      }
      {
        (* Case Read *)
        eapply invert_typing_Read in Hty.
        destruct Hty as (i' & Hty & Hle).
        simplify.
        eapply IHplug in Hty; eauto.
        destruct Hty as (t0 & i0 & Hty1 & Hle2 & HE).
        exists t0, i0.
        repeat split; eauto.
        {
          eapply interp_time_interp_prop_le.
          eapply interp_prop_le_interp_time in Hle.
          eapply interp_prop_le_interp_time in Hle2.
          eauto with time_order.
        }
        intros e'' e_all' W' i1' Hplug Htye'' Hle3 Hincl.
        invert Hplug.
        rename e'0 into e_all''.
        rename H4 into Hplug.
        eapply HE in Hplug; eauto.
        eapply TyLe.
        {
          eapply TyRead; eauto.
        }
        {
          simplify.
          eapply interp_time_interp_prop_le.
          repeat rewrite interp_time_distr.
          rotate_lhs.
          rotate_rhs.
          cancel.
          repeat rewrite interp_time_minus_distr.
          eapply Time_minus_cancel.
          eapply interp_prop_le_interp_time in Hle.
          eauto.
        }
      }
    }
    {
      cases opr.
      {
        (* Case BinOpPrim *)
        eapply invert_typing_BinOpPrim in Hty.
        destruct Hty.
      }
      {
        (* Case App *)
        eapply invert_typing_App in Hty.
        destruct Hty as (t' & t2 & i1 & i2 & i3 & Htyeq & Hty1 & Hty2 & Hle).
        simplify.
        eapply IHplug in Hty1; eauto.
        destruct Hty1 as (t1 & i0 & Hty1 & Hle2 & HE).
        exists t1, i0.
        repeat split; eauto.
        {
          eapply interp_time_interp_prop_le.
          eapply interp_prop_le_interp_time in Hle.
          eapply interp_prop_le_interp_time in Hle2.
          repeat rewrite interp_time_distr in Hle.
          repeat rewrite interp_time_1 in Hle.
          repeat (eapply Time_add_le_elim in Hle; destruct Hle as (Hle & ?)).
          eauto with time_order.
        }
        intros e'' e_all' W' i1' Hplug Htye'' Hle3 Hincl.
        invert Hplug.
        rename e'0 into e_all''.
        rename H5 into Hplug.
        eapply HE in Hplug; eauto.
        eapply TySub.
        {
          eapply TyApp; eauto.
          eapply weaken_W; eauto.
        }
        {
          eapply tyeq_sym; eauto.
        }
        {
          simplify.
          eapply interp_time_interp_prop_le.
          repeat rewrite interp_time_distr.
          rotate_rhs.
          do 4 rotate_lhs.
          cancel.
          do 3 rotate_lhs.
          repeat rewrite interp_time_minus_distr.
          eapply interp_prop_le_interp_time in Hle.
          eapply interp_prop_le_interp_time in Hle2.
          eapply interp_prop_le_interp_time in Hle3.
          rewrite Time_add_minus_assoc by eauto.
          eapply Time_minus_cancel.
          trans_rhs Hle.
          repeat rewrite interp_time_distr.
          rotate_lhs.
          cancel.
          eauto with time_order.
        }
      }
      {
        (* Case Pair *)
        eapply invert_typing_Pair in Hty.
        destruct Hty as (t1 & t2 & i1 & i2 & Htyeq & Hty1 & Hty2 & Hle).
        simplify.
        eapply IHplug in Hty1; eauto.
        destruct Hty1 as (t0 & i0 & Hty1 & Hle2 & HE).
        exists t0, i0.
        repeat split; eauto.
        {
          eapply interp_time_interp_prop_le.
          eapply interp_prop_le_interp_time in Hle.
          eapply interp_prop_le_interp_time in Hle2.
          repeat rewrite interp_time_distr in Hle.
          repeat rewrite interp_time_1 in Hle.
          repeat (eapply Time_add_le_elim in Hle; destruct Hle as (Hle & ?)).
          eauto with time_order.
        }
        intros e'' e_all' W' i1' Hplug Htye'' Hle3 Hincl.
        invert Hplug.
        rename e'0 into e_all''.
        rename H5 into Hplug.
        eapply HE in Hplug; eauto.
        eapply TySub.
        {
          eapply TyPair; eauto.
          eapply weaken_W; eauto.
        }
        {
          simplify.
          eapply tyeq_sym; eauto.
        }
        {
          simplify.
          eapply interp_time_interp_prop_le.
          repeat rewrite interp_time_distr.
          rotate_rhs.
          do 2 rotate_lhs.
          cancel.
          rotate_lhs.
          repeat rewrite interp_time_minus_distr.
          eapply interp_prop_le_interp_time in Hle.
          eapply interp_prop_le_interp_time in Hle2.
          eapply interp_prop_le_interp_time in Hle3.
          rewrite Time_add_minus_assoc by eauto.
          eapply Time_minus_cancel.
          trans_rhs Hle.
          repeat rewrite interp_time_distr.
          rotate_lhs.
          eauto with time_order.
        }
      }
      {
        (* Case Write *)
        eapply invert_typing_Write in Hty.
        destruct Hty as (t' & i1 & i2 & Htyeq & Hty1 & Hty2 & Hle).
        simplify.
        eapply IHplug in Hty1; eauto.
        destruct Hty1 as (t0 & i0 & Hty1 & Hle2 & HE).
        exists t0, i0.
        repeat split; eauto.
        {
          eapply interp_time_interp_prop_le.
          eapply interp_prop_le_interp_time in Hle.
          eapply interp_prop_le_interp_time in Hle2.
          repeat rewrite interp_time_distr in Hle.
          repeat rewrite interp_time_1 in Hle.
          repeat (eapply Time_add_le_elim in Hle; destruct Hle as (Hle & ?)).
          eauto with time_order.
        }
        intros e'' e_all' W' i1' Hplug Htye'' Hle3 Hincl.
        invert Hplug.
        rename e'0 into e_all''.
        rename H5 into Hplug.
        eapply HE in Hplug; eauto.
        eapply TySub.
        {
          eapply TyWrite; eauto.
          eapply weaken_W; eauto.
        }
        {
          simplify.
          eapply tyeq_sym; eauto.
        }
        {
          simplify.
          eapply interp_time_interp_prop_le.
          repeat rewrite interp_time_distr.
          rotate_rhs.
          do 2 rotate_lhs.
          cancel.
          rotate_lhs.
          repeat rewrite interp_time_minus_distr.
          eapply interp_prop_le_interp_time in Hle.
          eapply interp_prop_le_interp_time in Hle2.
          eapply interp_prop_le_interp_time in Hle3.
          rewrite Time_add_minus_assoc by eauto.
          eapply Time_minus_cancel.
          trans_rhs Hle.
          repeat rewrite interp_time_distr.
          rotate_lhs.
          eauto with time_order.
        }
      }
    }
    {
      (* Case BinOp2 *)
      cases opr.
      {
        (* Case BinOpPrim *)
        eapply invert_typing_BinOpPrim in Hty.
        destruct Hty.
      }
      {
        (* Case App *)
        eapply invert_typing_App in Hty.
        destruct Hty as (t' & t2 & i1 & i2 & i3 & Htyeq & Hty1 & Hty2 & Hle).
        simplify.
        eapply IHplug in Hty2; eauto.
        destruct Hty2 as (t0 & i0 & Hty2 & Hle2 & HE).
        exists t0, i0.
        repeat split; eauto.
        {
          eapply interp_time_interp_prop_le.
          eapply interp_prop_le_interp_time in Hle.
          eapply interp_prop_le_interp_time in Hle2.
          repeat rewrite interp_time_distr in Hle.
          repeat rewrite interp_time_1 in Hle.
          repeat (eapply Time_add_le_elim in Hle; destruct Hle as (Hle & ?)).
          eauto with time_order.
        }
        intros e'' e_all' W' i1' Hplug Htye'' Hle3 Hincl.
        invert Hplug.
        rename e'0 into e_all''.
        rename H6 into Hplug.
        eapply HE in Hplug; eauto.
        eapply TySub.
        {
          eapply TyApp; eauto.
          eapply weaken_W; eauto.
        }
        {
          eapply tyeq_sym; eauto.
        }
        {
          simplify.
          eapply interp_time_interp_prop_le.
          repeat rewrite interp_time_distr.
          repeat rewrite Time_add_assoc.
          rotate_rhs.
          do 3 rotate_lhs.
          cancel.
          do 3 rotate_lhs.
          repeat rewrite interp_time_minus_distr.
          eapply interp_prop_le_interp_time in Hle.
          eapply interp_prop_le_interp_time in Hle2.
          eapply interp_prop_le_interp_time in Hle3.
          rewrite Time_add_minus_assoc by eauto.
          eapply Time_minus_cancel.
          trans_rhs Hle.
          repeat rewrite interp_time_distr.
          do 2 rotate_lhs.
          cancel.
          eauto with time_order.
        }
      }
      {
        (* Case Pair *)
        eapply invert_typing_Pair in Hty.
        destruct Hty as (t1 & t2 & i1 & i2 & Htyeq & Hty1 & Hty2 & Hle).
        simplify.
        eapply IHplug in Hty2; eauto.
        destruct Hty2 as (t0 & i0 & Hty2 & Hle2 & HE).
        exists t0, i0.
        repeat split; eauto.
        {
          eapply interp_time_interp_prop_le.
          eapply interp_prop_le_interp_time in Hle.
          eapply interp_prop_le_interp_time in Hle2.
          repeat rewrite interp_time_distr in Hle.
          repeat rewrite interp_time_1 in Hle.
          repeat (eapply Time_add_le_elim in Hle; destruct Hle as (Hle & ?)).
          eauto with time_order.
        }
        intros e'' e_all' W' i1' Hplug Htye'' Hle3 Hincl.
        invert Hplug.
        rename e'0 into e_all''.
        rename H6 into Hplug.
        eapply HE in Hplug; eauto.
        eapply TySub.
        {
          eapply TyPair; eauto.
          eapply weaken_W; eauto.
        }
        {
          simplify.
          eapply tyeq_sym; eauto.
        }
        {
          simplify.
          eapply interp_time_interp_prop_le.
          eapply interp_prop_le_interp_time in Hle.
          eapply interp_prop_le_interp_time in Hle2.
          eapply interp_prop_le_interp_time in Hle3.
          repeat rewrite interp_time_distr in *.
          rotate_rhs.
          rotate_lhs.
          cancel.
          rotate_lhs.
          repeat rewrite interp_time_minus_distr.
          rewrite Time_add_minus_assoc by eauto.
          eapply Time_minus_cancel.
          eauto.
        }
      }
      {
        (* Case Write *)
        eapply invert_typing_Write in Hty.
        destruct Hty as (t' & i1 & i2 & Htyeq & Hty1 & Hty2 & Hle).
        simplify.
        eapply IHplug in Hty2; eauto.
        destruct Hty2 as (t0 & i0 & Hty2 & Hle2 & HE).
        exists t0, i0.
        repeat split; eauto.
        {
          eapply interp_time_interp_prop_le.
          eapply interp_prop_le_interp_time in Hle.
          eapply interp_prop_le_interp_time in Hle2.
          repeat rewrite interp_time_distr in Hle.
          repeat rewrite interp_time_1 in Hle.
          repeat (eapply Time_add_le_elim in Hle; destruct Hle as (Hle & ?)).
          eauto with time_order.
        }
        intros e'' e_all' W' i1' Hplug Htye'' Hle3 Hincl.
        invert Hplug.
        rename e'0 into e_all''.
        rename H6 into Hplug.
        eapply HE in Hplug; eauto.
        eapply TySub.
        {
          eapply TyWrite; eauto.
          eapply weaken_W; eauto.
        }
        {
          simplify.
          eapply tyeq_sym; eauto.
        }
        {
          simplify.
          eapply interp_time_interp_prop_le.
          eapply interp_prop_le_interp_time in Hle.
          eapply interp_prop_le_interp_time in Hle2.
          eapply interp_prop_le_interp_time in Hle3.
          repeat rewrite interp_time_distr in *.
          rotate_rhs.
          rotate_lhs.
          cancel.
          rotate_lhs.
          repeat rewrite interp_time_minus_distr.
          rewrite Time_add_minus_assoc by eauto.
          eapply Time_minus_cancel.
          eauto.
        }
      }
    }
    {
      (* Case Case *)
      eapply invert_typing_Case in Hty.
      destruct Hty as (t1 & t2 & i0' & i1 & i2 & Hty0 & Hty1 & Hty2 & Hle).
      simplify.
      eapply IHplug in Hty0; eauto.
      destruct Hty0 as (t0 & i0 & Hty0 & Hle2 & HE).
      exists t0, i0.
      repeat split; eauto.
      {
        eapply interp_time_interp_prop_le.
        eapply interp_prop_le_interp_time in Hle.
        eapply interp_prop_le_interp_time in Hle2.
        repeat rewrite interp_time_distr in Hle.
        repeat rewrite interp_time_1 in Hle.
        repeat (eapply Time_add_le_elim in Hle; destruct Hle as (Hle & ?)).
        eauto with time_order.
      }
      intros e'' e_all' W' i1' Hplug Htye'' Hle3 Hincl.
      invert Hplug.
      rename e'0 into e_all''.
      rename H5 into Hplug.
      eapply HE in Hplug; eauto.
      eapply TyLe.
      {
        eapply TyCase; eauto;
        eapply weaken_W; eauto.
      }
      {
        simplify.
        eapply interp_time_interp_prop_le.
        eapply interp_prop_le_interp_time in Hle.
        eapply interp_prop_le_interp_time in Hle2.
        eapply interp_prop_le_interp_time in Hle3.
        repeat rewrite interp_time_distr in *.
        rotate_rhs.
        do 2 rotate_lhs.
        cancel.
        rotate_lhs.
        repeat rewrite interp_time_minus_distr.
        rewrite Time_add_minus_assoc by eauto.
        eapply Time_minus_cancel.
        rotate_lhs.
        eauto.
      }
    }
    {
      (* Case AppC *)
      eapply invert_typing_AppC in Hty.
      destruct Hty as (t' & i' & k & Htyeq & Hty & Hkd & Hle).
      simplify.
      eapply IHplug in Hty; eauto.
      destruct Hty as (t0 & i0 & Hty1 & Hle2 & HE).
      exists t0, i0.
      repeat split; eauto.
      {
        eapply interp_time_interp_prop_le.
        eapply interp_prop_le_interp_time in Hle.
        eapply interp_prop_le_interp_time in Hle2.
        eauto with time_order.
      }
      intros e'' e_all' W' i1' Hplug Htye'' Hle3 Hincl.
      invert Hplug.
      rename e'0 into e_all''.
      rename H4 into Hplug.
      eapply HE in Hplug; eauto.
      eapply TySub.
      {
        eapply TyAppC; eauto.
      }
      {
        simplify.
        eapply tyeq_sym; eauto.
      }
      {
        simplify.
        eapply interp_time_interp_prop_le.
        repeat rewrite interp_time_distr.
        rotate_lhs.
        rotate_rhs.
        cancel.
        repeat rewrite interp_time_minus_distr.
        eapply Time_minus_cancel.
        eapply interp_prop_le_interp_time in Hle.
        eauto.
      }
    }
    {
      (* Case Pack *)
      eapply invert_typing_Pack in Hty.
      destruct Hty as (t1 & k & i' & Htyeq & Hkd & Hkdc & Hty & Hle).
      simplify.
      eapply IHplug in Hty; eauto.
      destruct Hty as (t0 & i0 & Hty1 & Hle2 & HE).
      exists t0, i0.
      repeat split; eauto.
      {
        eapply interp_time_interp_prop_le.
        eapply interp_prop_le_interp_time in Hle.
        eapply interp_prop_le_interp_time in Hle2.
        eauto with time_order.
      }
      intros e'' e_all' W' i1' Hplug Htye'' Hle3 Hincl.
      invert Hplug.
      rename e'0 into e_all''.
      rename H4 into Hplug.
      eapply HE in Hplug; eauto.
      eapply TySub.
      {
        eapply TyPack; eauto.
      }
      {
        simplify.
        eapply tyeq_sym; eauto.
      }
      {
        simplify.
        eapply interp_time_interp_prop_le.
        repeat rewrite interp_time_distr.
        rotate_lhs.
        rotate_rhs.
        cancel.
        repeat rewrite interp_time_minus_distr.
        eapply Time_minus_cancel.
        eapply interp_prop_le_interp_time in Hle.
        eauto.
      }
    }
    {
      (* Case Unpack *)
      eapply invert_typing_Unpack in Hty.
      destruct Hty as (t2 & t0' & i1 & k & i2 & Htyeq & Hty1 & Hty2 & Hle).
      simplify.
      eapply IHplug in Hty1; eauto.
      destruct Hty1 as (t0 & i0 & Hty1 & Hle2 & HE).
      exists t0, i0.
      repeat split; eauto.
      {
        eapply interp_time_interp_prop_le.
        eapply interp_prop_le_interp_time in Hle.
        eapply interp_prop_le_interp_time in Hle2.
        repeat rewrite interp_time_distr in Hle.
        repeat rewrite interp_time_1 in Hle.
        repeat (eapply Time_add_le_elim in Hle; destruct Hle as (Hle & ?)).
        eauto with time_order.
      }
      intros e'' e_all' W' i1' Hplug Htye'' Hle3 Hincl.
      invert Hplug.
      rename e'0 into e_all''.
      rename H4 into Hplug.
      eapply HE in Hplug; eauto.
      eapply TySub with (t1 := t2).
      {
        eapply TyUnpack; eauto.
        simplify.
        assert (Hincl' : fmap_map shift0_c_c W $<= fmap_map shift0_c_c W').
        {
          eapply fmap_map_shift0_c_c_incl; eauto.
        }
        eapply weaken_W; eauto.
      }
      {
        simplify.
        eapply tyeq_sym; eauto.
      }
      {
        simplify.
        eapply interp_time_interp_prop_le.
        eapply interp_prop_le_interp_time in Hle.
        eapply interp_prop_le_interp_time in Hle2.
        eapply interp_prop_le_interp_time in Hle3.
        repeat rewrite interp_time_distr in *.
        rotate_rhs.
        do 2 rotate_lhs.
        cancel.
        rotate_lhs.
        repeat rewrite interp_time_minus_distr.
        rewrite Time_add_minus_assoc by eauto.
        eapply Time_minus_cancel.
        rotate_lhs.
        eauto.
      }
    }
  Qed.

  Lemma preservation s s' :
    step s s' ->
    (* forall h e f h' e' f', *)
    (*   step (h, e, f) (h', e', f') -> *)
    (*   let s := (h, e, f) in *)
    (*   let s' := (h', e', f') in *)
    forall W t i,
      ctyping W s t i ->
      exists W' i',
        ctyping W' s' t i' /\
        (W $<= W').
  Proof.
    invert 1.
    (* induct 1. *)
    (* induction 1. *)
    simplify.
    destruct H as (Hty & Hhty & Hle).
    (* destruct H3 as [Hty & Hhty & Hle]. *)
    (* generalize H3. *)
    (* intros (Hty & Hhty & Hle). *)
    (* intros (Hty, (Hhty, Hle)). *)
    (* intros (Hty, Hhty). *)
    rename t into f.
    rename t' into f'.
    rename e1 into e_all.
    rename e1' into e_all'.
    rename t0 into t_all.
    eapply generalize_plug in Hty; eauto.
    destruct Hty as (t1 & i1 & Hty & Hle2 & He').
    rename H0 into Hstep.
    eapply preservation0 in Hstep.
    Focus 2.
    {
      unfold ctyping; repeat try_split; eauto.
      eapply interp_prop_le_interp_time in Hle2.
      eauto with time_order.
    }
    Unfocus.
    simplify.
    destruct Hstep as (Hle3 & W' & Hty2 & Hincl).
    destruct Hty2 as (Hty2 & Hhty' & Hle4).
    eapply He' in H2; eauto.
    Focus 2.
    {
      simplify.
      interp_le.
      repeat rewrite interp_time_minus_distr in *.
      rewrite interp_time_const in *.
      eauto with time_order.
    }
    Unfocus.
    exists W'.
    eexists.
    repeat try_split; eauto.
    simplify.
    interp_le.
    repeat rewrite interp_time_distr in *.
    repeat rewrite interp_time_minus_distr in *.
    rewrite interp_time_const in *.
    clear_non_le.
    rotate_lhs.
    rewrite Time_add_minus_assoc by eauto.
    rewrite Time_minus_add_cancel by eauto.
    eapply Time_minus_move_right; eauto with time_order.
    trans_rhs Time_le_add_minus.
    rewrite Time_add_comm.
    rewrite Time_add_minus_cancel.
    eauto.
  Qed.

  Definition trsys_of (s : config) :=
    {|
      Initial := {s};
      Step := step
    |}.

  Lemma unstuck_invariant W s t i :
    ctyping W s t i ->
    invariantFor (trsys_of s) unstuck.
  Proof.
    simplify.
    apply invariant_weaken with (invariant1 := fun s' => exists W' i', ctyping W' s' t i'); eauto.
    {
      apply invariant_induction; simplify; eauto.
      {
        propositional.
        subst; simplify.
        eauto.
      }
      {
        destruct H0 as (W' & i' & Hty).
        propositional.
        eapply preservation in H1; eauto.
        destruct H1 as (W'' & i'' & Hty' & Hle).
        eauto.
      }
    }
    {
      simplify.
      destruct H0 as (W' & i' & Hty).
      eauto using progress.
    }
  Qed.

  Theorem safety W s t i : ctyping W s t i -> safe s.
  Proof.
    intros H.
    eapply unstuck_invariant in H.
    unfold invariantFor, safe in *.
    intros s' Hstep.
    simplify.
    eauto.
  Qed.
  
End M.