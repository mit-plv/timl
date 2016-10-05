Set Implicit Arguments.

Module Type TIME.
  Parameter time_type : Type.
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
  induct ls; simplify; eauto.
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
  induct ls; destruct n as [|n]; simplify; eauto; try linear_arithmetic.
  destruct x as [|x]; simplify; eauto.
  eapply IHls; linear_arithmetic.
Qed.

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
  induct ls; destruct n; simplify; eauto.
Qed.

(* Definition removen A n (ls : list A) := firstn n ls ++ skipn (1 + n) ls. *)
Fixpoint removen A n (ls : list A) :=
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
  induct ls; simplify.
  {
    rewrite nth_error_nil in *; discriminate.
  }
  destruct n as [|n]; destruct n' as [|n']; simplify; eauto with db_la.
Qed.

Lemma removen_gt' A ls :
  forall n (a : A) n',
    nth_error ls (S n') = Some a ->
    n' >= n ->
    nth_error (removen n ls) n' = nth_error ls (S n').
Proof.
  induct ls; simplify; try discriminate.
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
  induct ls; destruct n; simplify; f_equal; eauto.
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

  (* The constructor language *)

  Inductive cstr_const :=
  | CCIdxTT
  | CCIdxNat (n : nat)
  | CCTime (r : time_type)
  | CCTypeUnit
  | CCTypeInt
  .

  (* Inductive cstr_un_op := *)
  (* . *)

  Inductive cstr_bin_op :=
  | CBTimeAdd
  | CBTimeMinus
  | CBTimeMax
  | CBTypeProd
  | CBTypeSum
  (* | CBApp *)
  .

  Inductive quan :=
  | QuanForall
  | QuanExists
  .

  Definition var := nat.

  Inductive prop_bin_conn :=
  | PBCAnd
  | PBCOr
  | PBCImply
  .

  Inductive prop_bin_pred :=
  | PBTimeLe
  | PBBigO (arity : nat)
  .

  Inductive base_sort :=
  | BSNat
  | BSUnit
  | BSBool
  | BSTimeFun (arity : nat)
  .

  Inductive cstr :=
  | CVar (x : var)
  | CConst (cn : cstr_const)
  (* | CUnOp (opr : cstr_un_op) (c : cstr) *)
  | CBinOp (opr : cstr_bin_op) (c1 c2 : cstr)
  | CIte (i1 i2 i3 : cstr)
  | CTimeAbs (i : cstr)
  | CTimeApp (arity : nat) (c1 c2 : cstr)
  | CArrow (t1 i t2 : cstr)
  | CAbs (* (k : kind) *) (t : cstr)
  | CApp (c1 c2 : cstr)
  | CQuan (q : quan) (k : kind) (c : cstr)
  | CRec (k : kind) (t : cstr)
  | CRef (t : cstr)

  with kind :=
       | KType
       | KArrow (k1 k2 : kind)
       | KBaseSort (b : base_sort)
       | KSubset (k : kind) (p : prop)

  with prop :=
       | PTrue
       | PFalse
       | PBinConn (opr : prop_bin_conn) (p1 p2 : prop)
       | PNot (p : prop)
       | PBinPred (opr : prop_bin_pred) (i1 i2 : cstr)
       | PEq (i1 i2 : cstr)
       | PQuan (q : quan) (p : prop)
  .

  Scheme cstr_mutind := Induction for cstr Sort Prop
  with kind_mutind := Induction for kind Sort Prop
  with prop_mutind := Induction for prop Sort Prop.

  Combined Scheme cstr_kind_prop_mutind from cstr_mutind, kind_mutind, prop_mutind. 

  Definition KUnit := KBaseSort BSUnit.
  Definition KBool := KBaseSort BSBool.
  Definition KNat := KBaseSort BSNat.
  Definition KTimeFun arity := KBaseSort (BSTimeFun arity).
  Definition KTime := KTimeFun 0.

  Notation Tconst r := (CConst (CCTime r)).
  Notation T0 := (Tconst Time0).
  Notation T1 := (Tconst Time1).
  Definition Tadd := CBinOp CBTimeAdd.
  Definition Tminus := CBinOp CBTimeMinus.

  Definition PAnd := PBinConn PBCAnd.
  Definition POr := PBinConn PBCOr.
  Definition PImply := PBinConn PBCImply.
  Definition PIff a b := PAnd (PImply a b) (PImply b a).

  Delimit Scope idx_scope with idx.
  Infix "+" := Tadd : idx_scope.
  (* Notation "0" := T0 : idx_scope. *)
  (* Notation "1" := T1 : idx_scope. *)

  Definition Tmax := CBinOp CBTimeMax.

  Definition CForall := CQuan QuanForall.
  Definition CExists := CQuan QuanExists.

  Definition CTypeUnit := CConst CCTypeUnit.

  Definition CProd := CBinOp CBTypeProd.
  Definition CSum := CBinOp CBTypeSum.
  (* Definition CApp := CBinOp CBApp. *)

  Definition Tle := PBinPred PBTimeLe.
  Infix "<=" := Tle : idx_scope.
  Infix "==" := PEq (at level 70) : idx_scope.
  Infix "===>" := PImply (at level 95) : idx_scope.
  Infix "<===>" := PIff (at level 95) : idx_scope.

  Require BinIntDef.
  Definition int := BinIntDef.Z.t.

  Definition CInt := CConst CCTypeInt.

  Definition const_kind cn :=
    match cn with
    | CCIdxTT => KUnit
    | CCIdxNat _ => KNat
    | CCTime _ => KTime
    | CCTypeUnit => KType
    | CCTypeInt => KType
    end
  .

  Definition cbinop_arg1_kind opr :=
    match opr with
    | CBTimeAdd => KTime
    | CBTimeMinus => KTime
    | CBTimeMax => KTime
    | CBTypeProd => KType
    | CBTypeSum => KType
    end.

  Definition cbinop_arg2_kind opr :=
    match opr with
    | CBTimeAdd => KTime
    | CBTimeMinus => KTime
    | CBTimeMax => KTime
    | CBTypeProd => KType
    | CBTypeSum => KType
    end.

  Definition cbinop_result_kind opr :=
    match opr with
    | CBTimeAdd => KTime
    | CBTimeMinus => KTime
    | CBTimeMax => KTime
    | CBTypeProd => KType
    | CBTypeSum => KType
    end.

  Definition binpred_arg1_kind opr :=
    match opr with
    | PBTimeLe => KTime
    | PBBigO n => KTimeFun n
    end
  .

  Definition binpred_arg2_kind opr :=
    match opr with
    | PBTimeLe => KTime
    | PBBigO n => KTimeFun n
    end
  .

  Definition kctx := list kind.
  
  Section shift_c_c.

    Variable n : nat.
    
    Fixpoint shift_c_c (x : var) (b : cstr) : cstr :=
      match b with
      | CVar y =>
        if x <=? y then
          CVar (n + y)
        else
          CVar y
      | CConst cn => CConst cn
      | CBinOp opr c1 c2 => CBinOp opr (shift_c_c x c1) (shift_c_c x c2)
      | CIte i1 i2 i3 => CIte (shift_c_c x i1) (shift_c_c x i2) (shift_c_c x i3)
      | CTimeAbs i => CTimeAbs (shift_c_c (1 + x) i)
      | CTimeApp n c1 c2 => CTimeApp n (shift_c_c x c1) (shift_c_c x c2)
      | CArrow t1 i t2 => CArrow (shift_c_c x t1) (shift_c_c x i) (shift_c_c x t2)
      | CAbs t => CAbs (shift_c_c (1 + x) t)
      | CApp c1 c2 => CApp (shift_c_c x c1) (shift_c_c x c2)
      | CQuan q k c => CQuan q (shift_c_k x k) (shift_c_c (1 + x) c)
      | CRec k t => CRec (shift_c_k x k) (shift_c_c (1 + x) t)
      | CRef t => CRef (shift_c_c x t)
      end
    with shift_c_k (x : var) (b : kind) : kind :=
           match b with
           | KType => KType
           | KArrow k1 k2 => KArrow (shift_c_k x k1) (shift_c_k x k2)
           | KBaseSort b => KBaseSort b
           | KSubset k p => KSubset (shift_c_k x k) (shift_c_p (1 + x) p)
           end
    with shift_c_p (x : var) (b : prop) : prop :=
           match b with
           | PTrue => PTrue
           | PFalse => PFalse
           | PBinConn opr p1 p2 => PBinConn opr (shift_c_p x p1) (shift_c_p x p2)
           | PNot p => PNot (shift_c_p x p)
           | PBinPred opr i1 i2 => PBinPred opr (shift_c_c x i1) (shift_c_c x i2)
           | PEq i1 i2 => PEq (shift_c_c x i1) (shift_c_c x i2)
           | PQuan q p => PQuan q (shift_c_p (1 + x) p)
           end.

  End shift_c_c.
  
  Definition shift0_c_c := shift_c_c 1 0.

  Inductive LtEqGt (a b : nat) :=
    | Lt : a < b -> LtEqGt a b
    | Eq : a = b -> LtEqGt a b
    | Gt : a > b -> LtEqGt a b
  .
  
  Definition lt_eq_gt_dec a b : LtEqGt a b :=
    match lt_eq_lt_dec a b with
    | inleft (left H) => Lt H
    | inleft (right H) => Eq H
    | inright H => Gt H
    end.
  
  Infix "<=>?" := lt_eq_gt_dec (at level 70).
  
  Section subst_c_c.

    Fixpoint subst_c_c (x : var) (v : cstr) (b : cstr) : cstr :=
      match b with
      | CVar y =>
        match y <=>? x with
        | Lt _ => CVar y
        | Eq _ => v
        | Gt _ => CVar (y - 1)
        end
      | CConst cn => CConst cn
      | CBinOp opr c1 c2 => CBinOp opr (subst_c_c x v c1) (subst_c_c x v c2)
      | CIte i1 i2 i3 => CIte (subst_c_c x v i1) (subst_c_c x v i2) (subst_c_c x v i3)
      | CTimeAbs i => CTimeAbs (subst_c_c (1 + x) (shift0_c_c v) i)
      | CTimeApp n c1 c2 => CTimeApp n (subst_c_c x v c1) (subst_c_c x v c2)
      | CArrow t1 i t2 => CArrow (subst_c_c x v t1) (subst_c_c x v i) (subst_c_c x v t2)
      | CAbs t => CAbs (subst_c_c (1 + x) (shift0_c_c v) t)
      | CApp c1 c2 => CApp (subst_c_c x v c1) (subst_c_c x v c2)
      | CQuan q k c => CQuan q (subst_c_k x v k) (subst_c_c (1 + x) (shift0_c_c v) c)
      | CRec k t => CRec (subst_c_k x v k) (subst_c_c (1 + x) (shift0_c_c v) t)
      | CRef t => CRef (subst_c_c x v t)
      end
    with subst_c_k (x : var) (v : cstr) (b : kind) : kind :=
           match b with
           | KType => KType
           | KArrow k1 k2 => KArrow (subst_c_k x v k1) (subst_c_k x v k2)
           | KBaseSort b => KBaseSort b
           | KSubset k p => KSubset (subst_c_k x v k) (subst_c_p (1 + x) (shift0_c_c v) p)
           end
    with subst_c_p (x : var) (v : cstr) (b : prop) : prop :=
           match b with
           | PTrue => PTrue
           | PFalse => PFalse
           | PBinConn opr p1 p2 => PBinConn opr (subst_c_p x v p1) (subst_c_p x v p2)
           | PNot p => PNot (subst_c_p x v p)
           | PBinPred opr i1 i2 => PBinPred opr (subst_c_c x v i1) (subst_c_c x v i2)
           | PEq i1 i2 => PEq (subst_c_c x v i1) (subst_c_c x v i2)
           | PQuan q p => PQuan q (subst_c_p (1 + x) (shift0_c_c v) p)
           end.

  End subst_c_c.
  
  Definition subst0_c_c v b := subst_c_c 0 v b.

  Fixpoint interp_time_fun (arity : nat) : Type :=
    match arity with
    | 0 => time_type
    | S n => nat -> interp_time_fun n
    end.

  Definition interp_base_sort (b : base_sort) : Type :=
    match b with
    | BSNat => nat
    | BSUnit => unit
    | BSBool => bool
    | BSTimeFun arity => interp_time_fun arity
    end.

  Fixpoint time_fun_default_value arity : interp_time_fun arity :=
    match arity with
    | 0 => 0%time
    | S n => fun _ : nat => time_fun_default_value n
    end.
  
  Definition base_sort_default_value (b : base_sort) : interp_base_sort b :=
    match b with
    | BSNat => 0%nat
    | BSUnit => tt
    | BSBool => false
    | BSTimeFun arity => time_fun_default_value arity
    end.

  (* base kinds: kinds that don't have the Subset case *)
  Inductive bkind :=
       | BKType
       | BKArrow (k1 k2 : bkind)
       | BKBaseSort (b : base_sort)
  .
  
  Definition BKUnit := BKBaseSort BSUnit.
  Definition BKBool := BKBaseSort BSBool.
  Definition BKNat := BKBaseSort BSNat.
  Definition BKTimeFun arity := BKBaseSort (BSTimeFun arity).
  Definition BKTime := BKTimeFun 0.

  Fixpoint kind_to_bkind k :=
    match k with
    | KType => BKType
    | KArrow k1 k2 => BKArrow (kind_to_bkind k1) (kind_to_bkind k2)
    | KBaseSort b => BKBaseSort b
    | KSubset k p => kind_to_bkind k
    end.
      
  Fixpoint interp_kind k : Type :=
    match k with
    | BKType => unit
    | BKArrow k1 k2 => interp_kind k1 -> interp_kind k2
    | BKBaseSort b => interp_base_sort b
    end.

  Fixpoint kind_default_value k : interp_kind k :=
    match k with
    | BKType => tt
    | BKArrow k1 k2 => fun _ : interp_kind k1 => kind_default_value k2
    | BKBaseSort b => base_sort_default_value b
    end.

  Fixpoint interp_kinds arg_ks (res : Type) : Type :=
    match arg_ks with
    | [] => res
    | arg_k :: arg_ks => interp_kinds arg_ks (interp_kind arg_k -> res)
    end.

  Fixpoint lift0 arg_ks : forall t, t -> interp_kinds arg_ks t :=
    match arg_ks return forall t, t -> interp_kinds arg_ks t with
    | [] =>
      fun t f => f
    | arg_k :: arg_ks =>
      fun t f => lift0 arg_ks (fun ak => f)
    end.

  Fixpoint lift2 arg_ks : forall t1 t2 t, (t1 -> t2 -> t) -> interp_kinds arg_ks t1 -> interp_kinds arg_ks t2 -> interp_kinds arg_ks t :=
    match arg_ks return forall t1 t2 t, (t1 -> t2 -> t) -> interp_kinds arg_ks t1 -> interp_kinds arg_ks t2 -> interp_kinds arg_ks t with
    | [] =>
      fun t1 t2 t f x1 x2 => f x1 x2
    | arg_k :: arg_ks =>
      fun t1 t2 t f x1 x2 => lift2 arg_ks (fun a1 a2 ak => f (a1 ak) (a2 ak)) x1 x2
    end.
  
  Fixpoint lift3 arg_ks : forall t1 t2 t3 t, (t1 -> t2 -> t3 -> t) -> interp_kinds arg_ks t1 -> interp_kinds arg_ks t2 -> interp_kinds arg_ks t3 -> interp_kinds arg_ks t :=
    match arg_ks return forall t1 t2 t3 t, (t1 -> t2 -> t3 -> t) -> interp_kinds arg_ks t1 -> interp_kinds arg_ks t2 -> interp_kinds arg_ks t3 -> interp_kinds arg_ks t with
    | [] =>
      fun t1 t2 t3 t f x1 x2 x3 => f x1 x2 x3
    | arg_k :: arg_ks =>
      fun t1 t2 t3 t f x1 x2 x3 => lift3 arg_ks (fun a1 a2 a3 ak => f (a1 ak) (a2 ak) (a3 ak)) x1 x2 x3
    end.

  Definition base_sort_dec : forall (b b' : base_sort), sumbool (b = b') (b <> b').
  Proof.
    induction b; destruct b'; simpl; try solve [left; f_equal; eauto | right; intro Heq; discriminate].
    {
      destruct (arity ==n arity0); subst; simplify; try solve [left; f_equal; eauto | right; intro Heq; invert Heq; subst; eauto].
    }
  Defined.
  
  Definition bkind_dec : forall (k k' : bkind), sumbool (k = k') (k <> k').
  Proof.
    induction k; destruct k'; simpl; try solve [left; f_equal; eauto | right; intro Heq; discriminate].
    {
      destruct (IHk1 k'1); destruct (IHk2 k'2); subst; simplify; try solve [left; f_equal; eauto | right; intro Heq; invert Heq; subst; eauto].
    }
    {
      destruct (base_sort_dec b b0); subst; simplify; try solve [left; f_equal; eauto | right; intro Heq; invert Heq; subst; eauto].
    }
  Defined.
  
  Definition convert_kind_value k1 k2 : interp_kind k1 -> interp_kind k2.
  Proof.
    cases (bkind_dec k1 k2); subst; eauto.
    intros.
    eapply kind_default_value.
  Defined.
  
  Section interp_var.

    Variables (k_in : bkind).
    
    Fixpoint interp_var (x : var) arg_ks (k_out : Type) (k : interp_kind k_in -> k_out) : interp_kinds arg_ks k_out :=
    match arg_ks with
    | [] => k (kind_default_value k_in)
    | arg_k :: arg_ks =>
      match x with
      | 0 => lift0 arg_ks (fun x : interp_kind arg_k => k (convert_kind_value arg_k k_in x))
      | S x => @interp_var x arg_ks (interp_kind arg_k -> k_out) (fun (x : interp_kind k_in) (_ : interp_kind arg_k) => k x)
      end
    end.

  End interp_var.
  
  Definition cbinop_arg1_bkind opr := kind_to_bkind (cbinop_arg1_kind opr).
  Definition cbinop_arg2_bkind opr := kind_to_bkind (cbinop_arg2_kind opr).
  Definition cbinop_result_bkind opr := kind_to_bkind (cbinop_result_kind opr).

  Definition interp_cbinop opr : interp_kind (cbinop_arg1_bkind opr) -> interp_kind (cbinop_arg2_bkind opr) -> interp_kind (cbinop_result_bkind opr) :=
    match opr with
    | CBTimeAdd => fun (a b : time_type) => (a + b)%time
    | CBTimeMinus => fun (a b : time_type) => (a - b)%time
    | CBTimeMax => fun (a b : time_type) => TimeMax a b
    | CBTypeProd => fun (_ _ : unit) => tt
    | CBTypeSum => fun (_ _ : unit) => tt
    end.

  Definition ite {A} (x : bool) (x1 x2 : A) := 
            if x then
              x1
            else
              x2.
  
  Fixpoint interp_cstr c arg_ks res_k {struct c} : interp_kinds arg_ks (interp_kind res_k) :=
    match c with
      | CVar x => interp_var res_k x arg_ks id
      | CConst cn =>
        match cn with
        | CCTime cn => lift0 arg_ks (convert_kind_value BKTime res_k cn)
        | CCIdxNat cn => lift0 arg_ks (convert_kind_value BKNat res_k cn)
        | CCIdxTT => lift0 arg_ks (convert_kind_value BKUnit res_k tt)
        | _ => lift0 arg_ks (convert_kind_value BKType res_k tt)
        end
      | CBinOp opr c1 c2 =>
        let f x1 x2 := convert_kind_value (cbinop_result_bkind opr) res_k (interp_cbinop opr x1 x2) in
        lift2 arg_ks f (interp_cstr c1 arg_ks (cbinop_arg1_bkind opr)) (interp_cstr c2 arg_ks (cbinop_arg2_bkind opr))
      | CIte c c1 c2 =>
        lift3 arg_ks ite (interp_cstr c1 arg_ks BKBool) (interp_cstr c1 arg_ks res_k) (interp_cstr c2 arg_ks res_k)
      | CTimeAbs c =>
        match res_k return interp_kinds arg_ks (interp_kind res_k) with
        | BKBaseSort (BSTimeFun (S n)) =>
          interp_cstr c (BKNat :: arg_ks) (BKTimeFun n)
        | res_k => lift0 arg_ks (kind_default_value res_k)
        end
      | CTimeApp n c1 c2 => 
        let f x1 x2 := convert_kind_value (BKTimeFun n) res_k (x1 x2) in
        lift2 arg_ks f (interp_cstr c1 arg_ks (BKTimeFun (S n))) (interp_cstr c2 arg_ks BKNat)
      | CAbs c =>
        match res_k return interp_kinds arg_ks (interp_kind res_k) with
        | BKArrow k1 k2 =>
          interp_cstr c (k1 :: arg_ks) k2
        | res_k => lift0 arg_ks (kind_default_value res_k)
        end
      | CApp c1 c2 => lift0 arg_ks (kind_default_value res_k)
      | CArrow t1 i t2 => lift0 arg_ks (kind_default_value res_k)
      | CQuan q k c => lift0 arg_ks (kind_default_value res_k)
      | CRec k t => lift0 arg_ks (kind_default_value res_k)
      | CRef t => lift0 arg_ks (kind_default_value res_k)
    end.

  Definition interpTime i : time_type := interp_cstr i [] BKTime.
  
  Definition interpP : kctx -> prop -> Prop.
  Admitted.

  Lemma interpP_le_refl L i : interpP L (i <= i)%idx.
  Admitted.
  Lemma interpP_le_trans L a b c :
    interpP L (a <= b)%idx ->
    interpP L (b <= c)%idx ->
    interpP L (a <= c)%idx.
  Admitted.

  Lemma interpP_eq_refl L i : interpP L (i == i)%idx.
  Admitted.
  Lemma interpP_eq_trans L a b c :
    interpP L (a == b)%idx ->
    interpP L (b == c)%idx ->
    interpP L (a == c)%idx.
  Admitted.
  Lemma interpP_eq_sym L i i' :
    interpP L (i == i')%idx ->
    interpP L (i' == i)%idx.
  Admitted.

  Lemma interpP_eq_interpP_le L a b :
    interpP L (a == b)%idx ->
    interpP L (a <= b)%idx.
  Admitted.
  
  Lemma interpP_le_interpTime a b :
    interpP [] (a <= b)%idx ->
    (interpTime a <= interpTime b)%time.
  Admitted.
  Lemma interpTime_interpP_le a b :
    (interpTime a <= interpTime b)%time ->
    interpP [] (a <= b)%idx.
  Admitted.
  Lemma interpTime_distr a b : interpTime (a + b)%idx = (interpTime a + interpTime b)%time.
  Admitted.
  Lemma interpTime_minus_distr a b :
    interpTime (Tminus a b) = (interpTime a - interpTime b)%time.
  Admitted.
  Lemma interpP_eq_interpTime a b :
    interpP [] (a == b)%idx -> interpTime a = interpTime b.
  Admitted.
  Lemma interpTime_0 : interpTime T0 = 0%time.
  Admitted.
  Lemma interpTime_1 : interpTime T1 = 1%time.
  Admitted.
  Lemma interpTime_const a : interpTime (Tconst a) = a.
  Admitted.
  Lemma interpTime_max a b : interpTime (Tmax a b) = TimeMax (interpTime a) (interpTime b).
  Admitted.

  Lemma subst0_c_c_Const v cn : subst0_c_c v (CConst cn) = CConst cn.
  Admitted.

  Ltac interp_le := try eapply interpTime_interpP_le; apply_all interpP_le_interpTime.

  Inductive kdeq : kctx -> kind -> kind -> Prop :=
  | KdEqKType L :
      kdeq L KType KType
  | KdEqKArrow L k1 k2 k1' k2' :
      kdeq L k1 k1' ->
      kdeq L k2 k2' ->
      kdeq L (KArrow k1 k2) (KArrow k1' k2')
  | KdEqBaseSort L b :
      kdeq L (KBaseSort b) (KBaseSort b)
  | KdEqSubset L k p k' p' :
      kdeq L k k' ->
      interpP (k :: L) (p <===> p')%idx ->
      kdeq L (KSubset k p) (KSubset k' p')
  .

  Hint Constructors kdeq.

  Lemma interpP_iff_refl L p : interpP L (p <===> p)%idx.
  Admitted.
  Lemma interpP_iff_trans L a b c :
    interpP L (a <===> b)%idx ->
    interpP L (b <===> c)%idx ->
    interpP L (a <===> c)%idx.
  Admitted.
  Lemma interpP_iff_sym L p p' :
    interpP L (p <===> p')%idx ->
    interpP L (p' <===> p)%idx.
  Admitted.

  Lemma kdeq_interpP L k k' p :
    kdeq L k k' ->
    interpP (k :: L) p ->
    interpP (k' :: L) p.
  Proof.
    (* induct 1; eauto. *)
  Admitted.

  Lemma kdeq_refl : forall L k, kdeq L k k.
  Proof.
    induct k; eauto using interpP_iff_refl.
  Qed.

  Lemma kdeq_sym L a b : kdeq L a b -> kdeq L b a.
  Proof.
    induct 1; eauto using kdeq_interpP, interpP_iff_sym.
  Qed.

  Lemma kdeq_trans' L a b :
    kdeq L a b ->
    forall c,
      kdeq L b c -> kdeq L a c.
  Proof.
    induct 1; invert 1; eauto 6 using interpP_iff_trans, kdeq_interpP, kdeq_sym.
  Qed.

  Lemma kdeq_trans L a b c : kdeq L a b -> kdeq L b c -> kdeq L a c.
  Proof.
    intros; eapply kdeq_trans'; eauto.
  Qed.

  Definition monotone : cstr -> Prop.
  Admitted.

  (* Unset Elimination Schemes. *)

  Inductive kinding : kctx -> cstr -> kind -> Prop :=
       | KdVar L x k :
           nth_error L x = Some k ->
           kinding L (CVar x) (shift_c_k (1 + x) 0 k)
       | KdConst L cn :
           kinding L (CConst cn) (const_kind cn)
       | KdBinOp L opr c1 c2 :
           kinding L c1 (cbinop_arg1_kind opr) ->
           kinding L c2 (cbinop_arg2_kind opr) ->
           kinding L (CBinOp opr c1 c2) (cbinop_result_kind opr)
       | KdIte L c c1 c2 k :
           kinding L c KBool ->
           kinding L c1 k ->
           kinding L c2 k ->
           kinding L (CIte c c1 c2) k
       | KdArrow L t1 i t2 :
           kinding L t1 KType ->
           kinding L i KTime ->
           kinding L t2 KType ->
           kinding L (CArrow t1 i t2) KType
       | KdAbs L c k1 k2 :
           wfkind L k1 ->
           kinding (k1 :: L) c (shift_c_k 1 0 k2) ->
           kinding L (CAbs c) (KArrow k1 k2)
       | KdApp L c1 c2 k1 k2 :
           kinding L c1 (KArrow k1 k2) ->
           kinding L c2 k1 ->
           kinding L (CApp c1 c2) k2
       | KdTimeAbs L i n :
           kinding (KNat :: L) i (KTimeFun n) ->
           monotone i ->
           kinding L (CTimeAbs i) (KTimeFun (1 + n))
       | KdTimeApp L c1 c2 n :
           kinding L c1 (KTimeFun (S n)) ->
           kinding L c2 KNat ->
           kinding L (CTimeApp n c1 c2) (KTimeFun n)
       (* todo: need elimination rule for TimeAbs *)
       | KdQuan L quan k c :
           wfkind L k ->
           kinding (k :: L) c KType ->
           kinding L (CQuan quan k c) KType
       | KdRec L k c :
           wfkind L k ->
           kinding (k :: L) c (shift_c_k 1 0 k) ->
           kinding L (CRec k c) k
       | KdRef L t :
           kinding L t KType ->
           kinding L (CRef t) KType
       | KdEq L c k k' :
           kinding L c k ->
           kdeq L k' k ->
           kinding L c k'
                   
  with wfkind : kctx -> kind -> Prop :=
       | WfKdType L :
           wfkind L KType
       | WfKdArrow L k1 k2 :
           wfkind L k1 ->
           wfkind L k2 ->
           wfkind L (KArrow k1 k2)
       | WfKdBaseSort L b :
           wfkind L (KBaseSort b)
       | WfKdSubset L k p :
           wfkind L k ->
           wfprop (k :: L) p ->
           wfkind L (KSubset k p)

  with wfprop : kctx -> prop -> Prop :=
  | WfPropTrue L :
      wfprop L PTrue
  | WfPropFalse L :
      wfprop L PFalse
  | WfPropBinConn L opr p1 p2 :
      wfprop L p1 ->
      wfprop L p2 ->
      wfprop L (PBinConn opr p1 p2)
  | WfPropNot L p :
      wfprop L p ->
      wfprop L (PNot p)
  | WfPropBinPred L opr i1 i2 :
      kinding L i1 (binpred_arg1_kind opr) ->
      kinding L i2 (binpred_arg2_kind opr) ->
      wfprop L (PBinPred opr i1 i2)
  | WfPropEq L i1 i2 k :
      kinding L i1 k ->
      kinding L i2 k ->
      wfprop L (PEq i1 i2)
  | WfPropQuan L q p k :
      wfkind L k ->
      wfprop (k :: L) p ->
      wfprop L (PQuan q p)
             
  .

  (* Scheme Minimality for kinding Sort Prop *)
  (* with Minimality for wfkind Sort Prop *)
  (* with Minimality for wfprop Sort Prop. *)

  Scheme kinding_mutind := Minimality for kinding Sort Prop
  with wfkind_mutind := Minimality for wfkind Sort Prop
  with wfprop_mutind := Minimality for wfprop Sort Prop.

  Combined Scheme kinding_wfkind_wfprop_mutind from kinding_mutind, wfkind_mutind, wfprop_mutind. 

  (*
Inductive tyeq : kctx -> cstr -> cstr -> Prop :=
(* | TyEqRefl L t : *)
(*     tyeq L t t *)
| TyEqVar L x :
    tyeq L (CVar x) (CVar x)
| TyConst L cn :
    tyeq L (CConst cn) (CConst cn)
(* | TyEqUnOp L opr t t' : *)
(*     tyeq L t t' -> *)
(*     tyeq L (CUnOp opr t) (CUnOp opr t') *)
| TyEqBinOp L opr t1 t2 t1' t2' :
    tyeq L t1 t1' ->
    tyeq L t2 t2' ->
    tyeq L (CBinOp opr t1 t2) (CBinOp opr t1' t2')
| TyEqIte L t1 t2 t3 t1' t2' t3':
    tyeq L t1 t1' ->
    tyeq L t2 t2' ->
    tyeq L t3 t3' ->
    tyeq L (CIte t1 t2 t3) (CIte t1' t2' t3')
| TyEqArrow L t1 i t2 t1' i' t2':
    tyeq L t1 t1' ->
    interpP L (PEq i i') ->
    tyeq L t2 t2' ->
    tyeq L (CArrow t1 i t2) (CArrow t1' i' t2')
| TyEqApp L c1 c2 c1' c2' :
    tyeq L c1 c1' ->
    tyeq L c2 c2' ->
    tyeq L (CApp c1 c2) (CApp c1' c2')
| TyEqBeta L t1 t2  :
    tyeq L (CApp (CAbs t1) t2) (subst0_c_c t2 t1)
| TyEqBetaRev L t1 t2  :
    tyeq L (subst0_c_c t2 t1) (CApp (CAbs t1) t2)
| TyEqQuan L quan k t k' t' :
    kdeq L k k' ->
    tyeq (k :: L) t t' ->
    tyeq L (CQuan quan k t) (CQuan quan k' t')
| TyEqRec L k c k' c' :
    kdeq L k k' ->
    tyeq (k :: L) c c' ->
    tyeq L (CRec k c) (CRec k' c')
| TyEqRef L t t' :
   tyeq L t t' ->
   tyeq L (CRef t) (CRef t')
(* the following rules are just here to satisfy reflexivity *)
| TyEqTimeAbs L i :
    tyeq L (CTimeAbs i) (CTimeAbs i)
(* don't do deep equality test of two CAbs's *)
| TyEqAbs L t :
    tyeq L (CAbs t) (CAbs t)
| TyEqTrans L a b c :
    tyeq L a b ->
    tyeq L b c ->
    tyeq L a c
.

Hint Constructors tyeq.

Lemma tyeq_refl : forall t L, tyeq L t t.
Proof.
  induct t; eauto using interpP_eq_refl, kdeq_refl.
Qed.

Lemma kdeq_tyeq L k k' t t' :
  kdeq L k k' ->
  tyeq (k :: L) t t' ->
  tyeq (k' :: L) t t'.
Admitted.

Lemma tyeq_sym L t1 t2 : tyeq L t1 t2 -> tyeq L t2 t1.
Proof.
  induct 1; eauto using interpP_eq_sym, kdeq_sym.
  {
    econstructor; eauto using interpP_eq_sym, kdeq_sym.
    eapply kdeq_tyeq; eauto using kdeq_trans, kdeq_sym.
  }
  {
    econstructor; eauto using interpP_eq_sym, kdeq_sym.
    eapply kdeq_tyeq; eauto using kdeq_trans, kdeq_sym.
  }
Qed.

Lemma tyeq_trans L a b c :
  tyeq L a b ->
  tyeq L b c ->
  tyeq L a c.
Proof.
  intros; eauto.
Qed.

Lemma invert_tyeq_Arrow L t1 i t2 tb : 
    tyeq L (CArrow t1 i t2) tb ->
      (exists t1' i' t2' ,
          tb = CArrow t1' i' t2' /\
          tyeq L t1 t1' /\
          interpP L (PEq i i') /\
          tyeq L t2 t2') \/
      (exists t1' t2' ,
          tb = CApp t1' t2').
Proof.
  induct 1; eauto.
  {
    left; repeat eexists_split; eauto.
  }
  {
    specialize (Hcneq (CAbs t0) t3).
    propositional.
  }
  induct 1; eauto.
  {
    repeat eexists_split; eauto.
  }
  {
    specialize (Hcneq (CAbs t0) t3).
    propositional.
  }
  eapply IHtyeq2; eauto using tyeq_sym.
  intros Htyeq.
  invert Htyeq.

Qed.

Lemma invert_tyeq_Arrow L ta tb : 
  tyeq L ta tb ->
  forall t1 i t2,
    tyeq L ta (CArrow t1 i t2) ->
    (exists t1' i' t2' ,
        tb = CArrow t1' i' t2' /\
        tyeq L t1 t1' /\
        interpP L (PEq i i') /\
        tyeq L t2 t2') \/
    (exists t1' t2' ,
        tb = CApp t1' t2').
Proof.
  induct 1; eauto.
  intros.
  invert H.
  {
    left; repeat eexists_split; eauto.
  }

Lemma invert_tyeq_Arrow L t1 i t2 tb : 
  tyeq L (CArrow t1 i t2) tb ->
  (forall t1' t2' ,
      tb <> CApp t1' t2') ->
  (exists t1' i' t2' ,
      tb = CArrow t1' i' t2' /\
      tyeq L t1 t1' /\
      interpP L (PEq i i') /\
      tyeq L t2 t2').
Proof.
  induct 1; eauto; intros Hcneq.
  {
    repeat eexists_split; eauto.
  }
  {
    specialize (Hcneq (CAbs t0) t3).
    propositional.
  }
  admit.
  eapply IHtyeq2; eauto using tyeq_sym.
  intros Htyeq.
  invert Htyeq.
Qed.

Lemma CForall_CArrow_false' L ta tb : 
    tyeq L ta tb ->
    forall k t t1 i t2,
      tyeq L ta (CForall k t) ->
      tyeq L tb (CArrow t1 i t2) ->
      False.
Proof.
  induct 1; eauto.
  eapply IHtyeq2; eauto using tyeq_sym.
  intros Htyeq.
  invert Htyeq.
Qed.

Lemma CForall_CArrow_false' L k t t1 i t2 : 
    tyeq L (CForall k t) (CArrow t1 i t2) ->
    False.
Proof.
  induct 1.
Qed.
  
Lemma invert_tyeq_CArrow L t1 i t2 t1' i' t2' :
  tyeq L (CArrow t1 i t2) (CArrow t1' i' t2') ->
  tyeq L t1 t1' /\
  interpP L (PEq i i') /\
  tyeq L t2 t2'.
Admitted.
   *)

  Inductive tyeq : kctx -> cstr -> cstr -> Prop :=
  (* | TyEqRefl L t : *)
  (*     tyeq L t t *)
  | TyEqVar L x :
      tyeq L (CVar x) (CVar x)
  | TyEqConst L cn :
      tyeq L (CConst cn) (CConst cn)
  (* | TyEqUnOp L opr t t' : *)
  (*     tyeq L t t' -> *)
  (*     tyeq L (CUnOp opr t) (CUnOp opr t') *)
  | TyEqBinOp L opr t1 t2 t1' t2' :
      tyeq L t1 t1' ->
      tyeq L t2 t2' ->
      tyeq L (CBinOp opr t1 t2) (CBinOp opr t1' t2')
  | TyEqIte L t1 t2 t3 t1' t2' t3':
      tyeq L t1 t1' ->
      tyeq L t2 t2' ->
      tyeq L t3 t3' ->
      tyeq L (CIte t1 t2 t3) (CIte t1' t2' t3')
  | TyEqArrow L t1 i t2 t1' i' t2':
      tyeq L t1 t1' ->
      interpP L (PEq i i') ->
      tyeq L t2 t2' ->
      tyeq L (CArrow t1 i t2) (CArrow t1' i' t2')
  | TyEqApp L c1 c2 c1' c2' :
      tyeq L c1 c1' ->
      tyeq L c2 c2' ->
      tyeq L (CApp c1 c2) (CApp c1' c2')
  | TyEqTimeApp L n c1 c2 n' c1' c2' :
      n = n' ->
      tyeq L c1 c1' ->
      tyeq L c2 c2' ->
      tyeq L (CTimeApp n c1 c2) (CTimeApp n' c1' c2')
  | TyEqBeta L (* t *) t1 t2 t1' t2' t' :
      (* tyeq L t (CApp t1 t2) -> *)
      tyeq L t1 (CAbs t1') ->
      tyeq L t2 t2' ->
      tyeq L (subst0_c_c t2' t1') t' ->
      tyeq L (CApp t1 t2) t'
  (* | TyEqBetaRev L t1 t2 t1' t2' t' : *)
  (*     tyeq L t1 (CAbs t1') -> *)
  (*     tyeq L t2 t2' -> *)
  (*     tyeq L (subst0_c_c t2' t1') t' -> *)
  (*     tyeq L t' (CApp t1 t2) *)
  | TyEqBetaRev L t1 t2 t1' t2' t' :
      tyeq L (CAbs t1') t1 ->
      tyeq L t2' t2 ->
      tyeq L t' (subst0_c_c t2' t1') ->
      tyeq L t' (CApp t1 t2)
  | TyEqQuan L quan k t k' t' :
      kdeq L k k' ->
      tyeq (k :: L) t t' ->
      tyeq L (CQuan quan k t) (CQuan quan k' t')
  | TyEqRec L k c k' c' :
      kdeq L k k' ->
      tyeq (k :: L) c c' ->
      tyeq L (CRec k c) (CRec k' c')
  | TyEqRef L t t' :
      tyeq L t t' ->
      tyeq L (CRef t) (CRef t')
  (* the following rules are just here to satisfy reflexivity *)
  (* don't do deep equality test of two CAbs's *)
  | TyEqAbs L t :
      tyeq L (CAbs t) (CAbs t)
  | TyEqTimeAbs L i :
      tyeq L (CTimeAbs i) (CTimeAbs i)
  .

  Section tyeq_hint.
    
    Local Hint Constructors tyeq.

    Lemma tyeq_refl : forall t L, tyeq L t t.
    Proof.
      induct t; eauto using interpP_eq_refl, kdeq_refl.
    Qed.

    Lemma kdeq_tyeq L k k' t t' :
      kdeq L k k' ->
      tyeq (k :: L) t t' ->
      tyeq (k' :: L) t t'.
    Admitted.

    Lemma tyeq_sym L t1 t2 : tyeq L t1 t2 -> tyeq L t2 t1.
    Proof.
      induct 1; eauto using interpP_eq_sym, kdeq_sym.
      {
        econstructor; eauto using interpP_eq_sym, kdeq_sym.
        eapply kdeq_tyeq; eauto using kdeq_trans, kdeq_sym.
      }
      {
        econstructor; eauto using interpP_eq_sym, kdeq_sym.
        eapply kdeq_tyeq; eauto using kdeq_trans, kdeq_sym.
      }
    Qed.

    Lemma tyeq_trans' L a b :
      tyeq L a b ->
      forall c,
        tyeq L b c ->
        tyeq L a c.
    Proof.
      induct 1; try solve [intros c Hbc; invert Hbc; eauto 3 using interpP_eq_trans, tyeq_refl].
      (* induct 1; try solve [induct 1; eauto using interpP_eq_trans, tyeq_refl]. *)
      {
        induct 1; eauto using interpP_eq_trans, tyeq_refl.
      }
      {
        induct 1; eauto using interpP_eq_trans, tyeq_refl.
      }
      {
        induct 1; eauto using interpP_eq_trans, tyeq_refl.
      }
      {
        induct 1; eauto using interpP_eq_trans, tyeq_refl.
      }
      {
        induct 1; eauto using interpP_eq_trans, tyeq_refl.
      }
      {
        induct 1; eauto using interpP_eq_trans, tyeq_refl.
      }
      {
        rename t' into a.
        induct 1.
        {
          eauto using interpP_eq_trans, tyeq_refl.
        }
        {
          rename t' into c.
          copy H2_ HH.
          eapply IHtyeq1 in HH.
          invert HH.
          copy H2_0 HH2.
          eapply IHtyeq2 in HH2.
          admit.
          (* may need logical relation here *)
          
          (* eapply IHtyeq3. *)
          (* Lemma subst0_c_c_tyeq : *)
          (*   forall t1 L t2 t2' t, *)
          (*     tyeq L t2' t2 -> *)
          (*     tyeq L (subst0_c_c t2 t1) t -> *)
          (*     tyeq L (subst0_c_c t2' t1) t. *)
          (* Admitted. *)
          (* eapply subst0_c_c_tyeq; eauto. *)
          (* admit. *)
        }
        {
          eauto using interpP_eq_trans, tyeq_refl.
        }
      }
      {
        induct 1; eauto using interpP_eq_trans, tyeq_refl.
        econstructor; eauto using kdeq_trans.
        eapply IHtyeq.
        eapply kdeq_tyeq; eauto using kdeq_trans, kdeq_sym.
      }
      {
        induct 1; eauto using interpP_eq_trans, tyeq_refl.
        econstructor; eauto using kdeq_trans.
        eapply IHtyeq.
        eapply kdeq_tyeq; eauto using kdeq_trans, kdeq_sym.
      }
      {
        induct 1; eauto using interpP_eq_trans, tyeq_refl.
      }
      (* intros c Hbc. *)
      (* invert Hbc. *)
      (* econstructor; eauto using kdeq_trans. *)
      (* eapply IHtyeq. *)
      (* eapply kdeq_tyeq; eauto using kdeq_trans, kdeq_sym. *)
      (* induct 1; eauto using interpP_eq_trans, tyeq_refl, kdeq_tyeq, kdeq_trans, kdeq_sym. *)
      
      (* solve [invert Hbc; eauto 4 using interpP_eq_trans, tyeq_refl]. *)
      (* induct 1; intros c Hbc; try solve [invert Hbc; eauto 4]. *)
      (* induct 1; intros c Hbc; try solve [invert Hbc; eauto using tyeq_refl]. *)
      (* induct 1; intros c Hbc; try solve [invert Hbc; eauto using interpP_eq_trans, tyeq_refl]. *)
      (* { *)
      (*   invert Hbc. *)
      (*   econstructor; eauto using kdeq_trans. *)
      (*   eapply IHtyeq. *)
      (*   eapply kdeq_tyeq; eauto using kdeq_trans, kdeq_sym. *)
      (* } *)
    Admitted.

    Lemma tyeq_trans L a b c :
      tyeq L a b ->
      tyeq L b c ->
      tyeq L a c.
    Proof.
      intros; eapply tyeq_trans'; eauto.
    Qed.

    Lemma CForall_CArrow_false k t t1 i t2 :
      tyeq [] (CForall k t) (CArrow t1 i t2) ->
      False.
    Proof.
      invert 1.
    Qed.

    Lemma invert_tyeq_CArrow L t1 i t2 t1' i' t2' :
      tyeq L (CArrow t1 i t2) (CArrow t1' i' t2') ->
      tyeq L t1 t1' /\
      interpP L (PEq i i') /\
      tyeq L t2 t2'.
    Proof.
      invert 1.
      repeat eexists_split; eauto.
    Qed.

    Lemma CExists_CArrow_false k t t1 i t2 :
      tyeq [] (CExists k t) (CArrow t1 i t2) ->
      False.
    Proof.
      invert 1.
    Qed.

    Lemma CProd_CArrow_false ta tb t1 i t2 :
      tyeq [] (CProd ta tb) (CArrow t1 i t2) ->
      False.
    Proof.
      invert 1.
    Qed.

    Lemma CSum_CArrow_false ta tb t1 i t2 :
      tyeq [] (CSum ta tb) (CArrow t1 i t2) ->
      False.
    Proof.
      invert 1.
    Qed.

    Lemma CRef_CArrow_false t t1 i t2 :
      tyeq [] (CRef t) (CArrow t1 i t2) ->
      False.
    Proof.
      invert 1.
    Qed.

    Lemma invert_tyeq_CExists L k1 t1 k2 t2 :
      tyeq L (CExists k1 t1) (CExists k2 t2) ->
      tyeq (k1 :: L) t1 t2 /\
      kdeq L k1 k2.
    Proof.
      invert 1.
      repeat eexists_split; eauto.
    Qed.

    Lemma invert_tyeq_CForall L k1 t1 k2 t2 :
      tyeq L (CForall k1 t1) (CForall k2 t2) ->
      tyeq (k1 :: L) t1 t2 /\
      kdeq L k1 k2.
    Proof.
      invert 1.
      repeat eexists_split; eauto.
    Qed.

    Lemma invert_tyeq_CRef L t t' :
      tyeq L (CRef t) (CRef t') ->
      tyeq L t t'.
    Proof.
      invert 1.
      repeat eexists_split; eauto.
    Qed.

    Lemma invert_tyeq_CProd L t1 t2 t1' t2' :
      tyeq L (CProd t1 t2) (CProd t1' t2') ->
      tyeq L t1 t1' /\
      tyeq L t2 t2'.
    Proof.
      invert 1.
      repeat eexists_split; eauto.
    Qed.

    Lemma invert_tyeq_CSum L t1 t2 t1' t2' :
      tyeq L (CSum t1 t2) (CSum t1' t2') ->
      tyeq L t1 t1' /\
      tyeq L t2 t2'.
    Proof.
      invert 1.
      repeat eexists_split; eauto.
    Qed.

  End tyeq_hint.

  Hint Resolve tyeq_refl tyeq_sym tyeq_trans interpP_le_refl interpP_le_trans : db_tyeq.

  Lemma interpP_eq_add_0 L a : interpP L (a + T0 == a)%idx.
  Admitted.
  
  Lemma kinding_tyeq L k t1 t2 :
    kinding L t1 k ->
    tyeq L t1 t2 ->
    kinding L t2 k.
  Admitted.
  
  Fixpoint shift_c_ks n bs :=
    match bs with
    | [] => []
    | b :: bs => shift_c_k n (length bs) b :: shift_c_ks n bs
    end.

  Fixpoint subst_c_ks v bs :=
    match bs with
    | [] => []
    | b :: bs => subst_c_k (length bs) (shift_c_c (length bs) 0 v) b :: subst_c_ks v bs
    end.

  Lemma monotone_shift_c_c x v b :
    monotone b ->
    monotone (shift_c_c x v b).
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
  Lemma interpP_shift_c_p L p :
    interpP L p ->
    forall x ls ,
      let n := length ls in
      x <= length L ->
      interpP (shift_c_ks n (firstn x L) ++ ls ++ my_skipn L x) (shift_c_p n x p).
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
  
  Lemma interpP_subst_c_p L p :
    interpP L p ->
    forall n k c ,
      nth_error L n = Some k ->
      kinding (my_skipn L (1 + n)) c k ->
      interpP (subst_c_ks c (firstn n L) ++ my_skipn L (1 + n)) (subst_c_p n (shift_c_c n 0 c) p).
  Admitted.
  
  Lemma nth_error_subst_c_ks bs :
    forall x b v,
      nth_error bs x = Some b ->
      let n := length bs in
      nth_error (subst_c_ks v bs) x = Some (subst_c_k (n - S x) (shift_c_c (n - S x) 0 v) b).
  Proof.
    induction bs; simplify.
    {
      rewrite nth_error_nil in *; discriminate.
    }
    destruct x; simplify; eauto.
    invert H.
    try unfold value; repeat f_equal; linear_arithmetic.
  Qed.
  
  Lemma length_subst_c_ks bs :
    forall v,
      length (subst_c_ks v bs) = length bs.
  Proof.
    induction bs; simplify; eauto.
  Qed.
  
  Lemma shift_c_k_cbinop_result_kind x v opr :
    shift_c_k x v (cbinop_result_kind opr) = cbinop_result_kind opr.
  Proof.
    cases opr; simplify; eauto.
  Qed.
  Lemma shift_c_k_cbinop_arg1_kind x v opr :
    shift_c_k x v (cbinop_arg1_kind opr) = cbinop_arg1_kind opr.
  Proof.
    cases opr; simplify; eauto.
  Qed.
  Lemma shift_c_k_cbinop_arg2_kind x v opr :
    shift_c_k x v (cbinop_arg2_kind opr) = cbinop_arg2_kind opr.
  Proof.
    cases opr; simplify; eauto.
  Qed.
  
  Lemma shift_c_k_binpred_arg1_kind x v opr :
    shift_c_k x v (binpred_arg1_kind opr) = binpred_arg1_kind opr.
  Proof.
    cases opr; simplify; eauto.
  Qed.
  
  Lemma shift_c_k_binpred_arg2_kind x v opr :
    shift_c_k x v (binpred_arg2_kind opr) = binpred_arg2_kind opr.
  Proof.
    cases opr; simplify; eauto.
  Qed.
  
  Lemma subst_c_k_cbinop_result_kind x v opr :
    subst_c_k x v (cbinop_result_kind opr) = cbinop_result_kind opr.
  Proof.
    cases opr; simplify; eauto.
  Qed.
  Lemma subst_c_k_cbinop_arg1_kind x v opr :
    subst_c_k x v (cbinop_arg1_kind opr) = cbinop_arg1_kind opr.
  Proof.
    cases opr; simplify; eauto.
  Qed.
  Lemma subst_c_k_cbinop_arg2_kind x v opr :
    subst_c_k x v (cbinop_arg2_kind opr) = cbinop_arg2_kind opr.
  Proof.
    cases opr; simplify; eauto.
  Qed.
  
  Lemma subst_c_k_binpred_arg1_kind x v opr :
    subst_c_k x v (binpred_arg1_kind opr) = binpred_arg1_kind opr.
  Proof.
    cases opr; simplify; eauto.
  Qed.
  
  Lemma subst_c_k_binpred_arg2_kind x v opr :
    subst_c_k x v (binpred_arg2_kind opr) = binpred_arg2_kind opr.
  Proof.
    cases opr; simplify; eauto.
  Qed.
  
  Require Import NPeano.
  
  Lemma length_shift_c_ks bs :
    forall v,
      length (shift_c_ks v bs) = length bs.
  Proof.
    induction bs; simplify; eauto.
  Qed.
  
  Lemma kdeq_refl2 : forall L k k', k = k' -> kdeq L k k'.
  Proof.
    intros; subst; eapply kdeq_refl.
  Qed.
  
  Lemma nth_error_shift_c_ks bs :
    forall x b m,
      nth_error bs x = Some b ->
      let n := length bs in
      nth_error (shift_c_ks m bs) x = Some (shift_c_k m (n - S x) b).
  Proof.
    induction bs; simplify.
    {
      rewrite nth_error_nil in *; discriminate.
    }
    destruct x; simplify; eauto.
    invert H.
    try unfold value; repeat f_equal; linear_arithmetic.
  Qed.
  
  Lemma shift_c_c_k_p_0 :
    (forall b x, shift_c_c 0 x b = b) /\
    (forall b x, shift_c_k 0 x b = b) /\
    (forall b x, shift_c_p 0 x b = b).
  Proof.
    eapply cstr_kind_prop_mutind;
      simplify; cbn in *;
        try solve [f_equal; eauto].
    {
      (* Case CVar *)
      repeat match goal with
               |- context [?a <=? ?b] => cases (a <=? b); simplify; cbn
             end; f_equal; linear_arithmetic.
    }
  Qed.
  
  Lemma shift_c_c_0 : forall c x, shift_c_c 0 x c = c.
  Proof.
    eapply shift_c_c_k_p_0.
  Qed.
  
  Lemma shift_c_c_k_p_shift_merge n1 n2 :
    (forall b x y,
        x <= y ->
        y <= x + n1 ->
        shift_c_c n2 y (shift_c_c n1 x b) = shift_c_c (n1 + n2) x b) /\
    (forall b x y,
        x <= y ->
        y <= x + n1 ->
        shift_c_k n2 y (shift_c_k n1 x b) = shift_c_k (n1 + n2) x b) /\
    (forall b x y,
        x <= y ->
        y <= x + n1 ->
        shift_c_p n2 y (shift_c_p n1 x b) = shift_c_p (n1 + n2) x b).
  Proof.
    eapply cstr_kind_prop_mutind;
      simplify; cbn in *;
        try solve [eauto |
                   f_equal; eauto |
                   erewrite H by linear_arithmetic; f_equal; eauto with db_la |
                   f_equal;
                   match goal with
                     H : _ |- _ => eapply H; eauto with db_la
                   end].
    {
      (* Case CVar *)
      repeat match goal with
               |- context [?a <=? ?b] => cases (a <=? b); simplify; cbn
             end; f_equal; linear_arithmetic.
    }
  Qed.
  
  Lemma shift_c_c_shift_merge n1 n2 :
    forall b x y,
      x <= y ->
      y <= x + n1 ->
      shift_c_c n2 y (shift_c_c n1 x b) = shift_c_c (n1 + n2) x b.
  Proof.
    eapply shift_c_c_k_p_shift_merge.
  Qed.
    
  Lemma shift_c_k_shift_merge n1 n2 :
    forall b x y,
      x <= y ->
      y <= x + n1 ->
      shift_c_k n2 y (shift_c_k n1 x b) = shift_c_k (n1 + n2) x b.
  Proof.
    eapply shift_c_c_k_p_shift_merge.
  Qed.
    
  Lemma shift_c_p_shift_merge n1 n2 :
    forall b x y,
      x <= y ->
      y <= x + n1 ->
      shift_c_p n2 y (shift_c_p n1 x b) = shift_c_p (n1 + n2) x b.
  Proof.
    eapply shift_c_c_k_p_shift_merge.
  Qed.
    
  Lemma shift_c_k_shift_0 b :
    forall n1 n2 x,
      x <= n1 ->
      shift_c_k n2 x (shift_c_k n1 0 b) = shift_c_k (n1 + n2) 0 b.
  Proof.
    intros.
    eapply shift_c_k_shift_merge; linear_arithmetic.
  Qed.
  
  Lemma shift_c_c_k_p_shift_cut n1 n2 :
    (forall b x y,
        x + n1 <= y ->
        shift_c_c n2 y (shift_c_c n1 x b) = shift_c_c n1 x (shift_c_c n2 (y - n1) b)) /\
    (forall b x y,
        x + n1 <= y ->
        shift_c_k n2 y (shift_c_k n1 x b) = shift_c_k n1 x (shift_c_k n2 (y - n1) b)) /\
    (forall b x y,
        x + n1 <= y ->
        shift_c_p n2 y (shift_c_p n1 x b) = shift_c_p n1 x (shift_c_p n2 (y - n1) b)).
  Proof.
    eapply cstr_kind_prop_mutind;
      simplify; cbn in *;
        try solve [eauto |
                   f_equal; eauto |
                   erewrite H by linear_arithmetic; repeat f_equal; eauto with db_la |
                   try replace (S (y - n1)) with (S y - n1) by linear_arithmetic;
                   f_equal;
                   match goal with
                     H : _ |- _ => eapply H; eauto with db_la
                   end].
    {
      (* Case CVar *)
      repeat match goal with
               |- context [?a <=? ?b] => cases (a <=? b); simplify; cbn
             end; f_equal; linear_arithmetic.
    }
  Qed.
  
  Lemma shift_c_c_shift_cut n1 n2 :
    forall b x y,
      x + n1 <= y ->
      shift_c_c n2 y (shift_c_c n1 x b) = shift_c_c n1 x (shift_c_c n2 (y - n1) b).
  Proof.
    eapply shift_c_c_k_p_shift_cut.
  Qed.
  
  Lemma shift_c_k_shift_cut n1 n2 :
    forall b x y,
      x + n1 <= y ->
      shift_c_k n2 y (shift_c_k n1 x b) = shift_c_k n1 x (shift_c_k n2 (y - n1) b).
  Proof.
    eapply shift_c_c_k_p_shift_cut.
  Qed.
  
  Lemma shift_c_p_shift_cut n1 n2 :
    forall b x y,
      x + n1 <= y ->
      shift_c_p n2 y (shift_c_p n1 x b) = shift_c_p n1 x (shift_c_p n2 (y - n1) b).
  Proof.
    eapply shift_c_c_k_p_shift_cut.
  Qed.
  
  Lemma shift_c_k_shift_2 b :
    forall n1 n2 x,
      n1 <= x ->
      shift_c_k n2 x (shift_c_k n1 0 b) = shift_c_k n1 0 (shift_c_k n2 (x - n1) b).
  Proof.
    intros.
    eapply shift_c_k_shift_cut; linear_arithmetic.
  Qed.
  
  Lemma shift_c_c_shift b :
    forall n1 n2 x,
      shift_c_c n2 x (shift_c_c n1 x b) = shift_c_c (n1 + n2) x b.
  Proof.
    intros.
    eapply shift_c_c_shift_merge; linear_arithmetic.
  Qed.
  
  Lemma shift_c_c_shift0 n b :
    shift_c_c n 0 (shift0_c_c b) = shift_c_c (S n) 0 b.
  Proof.
    intros.
    eapply shift_c_c_shift_merge; linear_arithmetic.
  Qed.
  
  Lemma shift0_c_c_shift_0 n c :
    shift0_c_c (shift_c_c n 0 c) = shift_c_c (1 + n) 0 c.
  Proof.
    unfold shift0_c_c; intros.
    rewrite shift_c_c_shift_merge; f_equal; linear_arithmetic.
  Qed.
  
  Lemma shift0_c_c_shift n x b :
    shift0_c_c (shift_c_c n x b) = shift_c_c n (1 + x) (shift0_c_c b).
  Proof.
    unfold shift0_c_c; intros.
    symmetry.
    rewrite shift_c_c_shift_cut; repeat f_equal; linear_arithmetic.
  Qed.

  Lemma subst_c_c_k_p_shift_avoid n :
    (forall b v x y,
        x <= y ->
        y < x + n ->
        subst_c_c y v (shift_c_c n x b) = shift_c_c (n - 1) x b) /\
    (forall b v x y,
        x <= y ->
        y < x + n ->
        subst_c_k y v (shift_c_k n x b) = shift_c_k (n - 1) x b) /\
    (forall b v x y,
        x <= y ->
        y < x + n ->
        subst_c_p y v (shift_c_p n x b) = shift_c_p (n - 1) x b).
  Proof.
    eapply cstr_kind_prop_mutind;
      simplify; cbn in *;
        try solve [eauto |
                   f_equal; eauto |
                   erewrite H by linear_arithmetic; repeat f_equal; eauto with db_la |
                   repeat rewrite shift0_c_c_shift_0; simplify;
                   repeat replace (S (y - n)) with (S y - n) by linear_arithmetic;
                   f_equal;
                   match goal with
                     H : _ |- _ => eapply H; eauto with db_la
                   end].
    {
      (* Case CVar *)
      repeat match goal with
             | |- context [?a <=? ?b] => cases (a <=? b); simplify; cbn
             | |- context [?a <=>? ?b] => cases (a <=>? b); simplify; cbn
             end; try solve [f_equal; linear_arithmetic].
    }
  Qed.
  
  Lemma subst_c_c_shift_avoid n :
    forall b v x y,
      x <= y ->
      y < x + n ->
      subst_c_c y v (shift_c_c n x b) = shift_c_c (n - 1) x b.
  Proof.
    eapply subst_c_c_k_p_shift_avoid.
  Qed.
  
  Lemma subst_c_k_shift_avoid n :
    forall b v x y,
      x <= y ->
      y < x + n ->
      subst_c_k y v (shift_c_k n x b) = shift_c_k (n - 1) x b.
  Proof.
    eapply subst_c_c_k_p_shift_avoid.
  Qed.
  
  Lemma subst_c_p_shift_avoid n :
    forall b v x y,
      x <= y ->
      y < x + n ->
      subst_c_p y v (shift_c_p n x b) = shift_c_p (n - 1) x b.
  Proof.
    eapply subst_c_c_k_p_shift_avoid.
  Qed.
  
  Lemma subst_c_k_shift_0_avoid x y v b :
    y < x ->
    subst_c_k y (shift_c_c y 0 v) (shift_c_k x 0 b) = shift_c_k (x - 1) 0 b.
  Proof.
    intros.
    eapply subst_c_k_shift_avoid; linear_arithmetic.
  Qed.
  
  Lemma subst0_c_c_shift0 v b :
    subst0_c_c v (shift0_c_c b) = b.
  Proof.
    unfold shift0_c_c, subst0_c_c.
    specialize (@subst_c_c_shift_avoid 1 b v 0 0); intros H; simplify.
    repeat rewrite shift_c_c_0 in *.
    eauto with db_la.
  Qed.
  
  Lemma subst_c_c_k_p_shift_hit v n :
    (forall b x y,
        x + n <= y ->
        subst_c_c y (shift_c_c y 0 v) (shift_c_c n x b) = shift_c_c n x (subst_c_c (y - n) (shift_c_c (y - n) 0 v) b)) /\
    (forall b x y,
        x + n <= y ->
        subst_c_k y (shift_c_c y 0 v) (shift_c_k n x b) = shift_c_k n x (subst_c_k (y - n) (shift_c_c (y - n) 0 v) b)) /\
    (forall b x y,
        x + n <= y ->
        subst_c_p y (shift_c_c y 0 v) (shift_c_p n x b) = shift_c_p n x (subst_c_p (y - n) (shift_c_c (y - n) 0 v) b)).
  Proof.
    eapply cstr_kind_prop_mutind;
      simplify; cbn in *;
        try solve [eauto |
                   f_equal; eauto |
                   erewrite H by linear_arithmetic; repeat f_equal; eauto with db_la |
                   repeat rewrite shift0_c_c_shift_0; simplify;
                   repeat replace (S (y - n)) with (S y - n) by linear_arithmetic;
                   f_equal;
                   match goal with
                     H : _ |- _ => eapply H; eauto with db_la
                   end].
    {
      (* Case CVar *)
      repeat match goal with
             | |- context [?a <=? ?b] => cases (a <=? b); simplify; cbn
             | |- context [?a <=>? ?b] => cases (a <=>? b); simplify; cbn
             end; try solve [f_equal; linear_arithmetic].
      rewrite shift_c_c_shift_merge by linear_arithmetic.
      f_equal; eauto with db_la.
    }
  Qed.
  
  Lemma subst_c_c_shift_hit v n :
    forall b x y,
      x + n <= y ->
      subst_c_c y (shift_c_c y 0 v) (shift_c_c n x b) = shift_c_c n x (subst_c_c (y - n) (shift_c_c (y - n) 0 v) b).
  Proof.
    eapply subst_c_c_k_p_shift_hit.
  Qed.
  
  Lemma subst_c_k_shift_hit v n :
    forall b x y,
      x + n <= y ->
      subst_c_k y (shift_c_c y 0 v) (shift_c_k n x b) = shift_c_k n x (subst_c_k (y - n) (shift_c_c (y - n) 0 v) b).
  Proof.
    eapply subst_c_c_k_p_shift_hit.
  Qed.
  
  Lemma subst_c_p_shift_hit v n :
    forall b x y,
      x + n <= y ->
      subst_c_p y (shift_c_c y 0 v) (shift_c_p n x b) = shift_c_p n x (subst_c_p (y - n) (shift_c_c (y - n) 0 v) b).
  Proof.
    eapply subst_c_c_k_p_shift_hit.
  Qed.
  
  Lemma subst_c_k_shift x y v b :
    x <= y ->
    subst_c_k y (shift_c_c y 0 v) (shift_c_k x 0 b) = shift_c_k x 0 (subst_c_k (y - x) (shift_c_c (y - x) 0 v) b).
  Proof.
    intros.
    eapply subst_c_k_shift_hit; linear_arithmetic.
  Qed.

  Lemma shift_c_c_k_p_subst_in n :
    (forall b v x y,
        y <= x ->
        shift_c_c n y (subst_c_c x v b) = subst_c_c (x + n) (shift_c_c n y v) (shift_c_c n y b)) /\
    (forall b v x y,
        y <= x ->
        shift_c_k n y (subst_c_k x v b) = subst_c_k (x + n) (shift_c_c n y v) (shift_c_k n y b)) /\
    (forall b v x y,
        y <= x ->
        shift_c_p n y (subst_c_p x v b) = subst_c_p (x + n) (shift_c_c n y v) (shift_c_p n y b)).
  Proof.
    eapply cstr_kind_prop_mutind;
      simplify; cbn in *;
        try solve [eauto |
                   f_equal; eauto |
                   erewrite H by linear_arithmetic; repeat f_equal; eauto with db_la |
                   repeat rewrite shift0_c_c_shift; simplify;
                   repeat replace (S (y - n)) with (S y - n) by linear_arithmetic;
                   f_equal;
                   match goal with
                     H : _ |- _ => eapply H; eauto with db_la
                   end].
    {
      (* Case CVar *)
      repeat match goal with
             | |- context [?a <=? ?b] => cases (a <=? b); simplify; cbn
             | |- context [?a <=>? ?b] => cases (a <=>? b); simplify; cbn
             end; try solve [f_equal; linear_arithmetic].
    }
  Qed.
  
  Lemma shift_c_c_subst_in n :
    forall b v x y,
      y <= x ->
      shift_c_c n y (subst_c_c x v b) = subst_c_c (x + n) (shift_c_c n y v) (shift_c_c n y b).
  Proof.
    eapply shift_c_c_k_p_subst_in.
  Qed.
  
  Lemma shift_c_k_subst_in n :
    forall b v x y,
      y <= x ->
      shift_c_k n y (subst_c_k x v b) = subst_c_k (x + n) (shift_c_c n y v) (shift_c_k n y b).
  Proof.
    eapply shift_c_c_k_p_subst_in.
  Qed.
  
  Lemma shift_c_p_subst_in n :
    forall b v x y,
      y <= x ->
      shift_c_p n y (subst_c_p x v b) = subst_c_p (x + n) (shift_c_c n y v) (shift_c_p n y b).
  Proof.
    eapply shift_c_c_k_p_subst_in.
  Qed.
  
  Lemma shift0_c_c_subst x v b :
    shift0_c_c (subst_c_c x (shift_c_c x 0 v) b) = subst_c_c (1 + x) (shift_c_c (1 + x) 0 v) (shift0_c_c b).
  Proof.
    unfold shift0_c_c, subst0_c_c.
    rewrite shift_c_c_subst_in by linear_arithmetic.
    rewrite shift_c_c_shift_merge by linear_arithmetic.
    repeat (f_equal; try linear_arithmetic).
  Qed.

  Lemma shift0_c_c_subst_2 x v b :
    shift0_c_c (subst_c_c x v b) = subst_c_c (1 + x) (shift0_c_c v) (shift0_c_c b).
  Proof.
    unfold shift0_c_c, subst0_c_c.
    rewrite shift_c_c_subst_in by linear_arithmetic.
    repeat (f_equal; try linear_arithmetic).
  Qed.

  Opaque le_lt_dec.
  
  Lemma shift_c_c_k_p_subst_out n :
    (forall b v x y,
        x <= y ->
        shift_c_c n y (subst_c_c x v b) = subst_c_c x (shift_c_c n y v) (shift_c_c n (S y) b)) /\
    (forall b v x y,
        x <= y ->
        shift_c_k n y (subst_c_k x v b) = subst_c_k x (shift_c_c n y v) (shift_c_k n (S y) b)) /\
    (forall b v x y,
        x <= y ->
        shift_c_p n y (subst_c_p x v b) = subst_c_p x (shift_c_c n y v) (shift_c_p n (S y) b)).
  Proof.
    eapply cstr_kind_prop_mutind;
      simplify;
      cbn in *;
        try solve [eauto |
                   f_equal; eauto |
                   erewrite H by linear_arithmetic; repeat f_equal; eauto with db_la |
                   repeat rewrite shift0_c_c_shift; simplify;
                   repeat replace (S (y - n)) with (S y - n) by linear_arithmetic;
                   f_equal;
                   match goal with
                     H : _ |- _ => eapply H; eauto with db_la
                   end].
    {
      (* Case CVar *)
      repeat match goal with
             | |- context [?a <=? ?b] => cases (a <=? b); simplify; cbn
             | |- context [?a <=>? ?b] => cases (a <=>? b); simplify; cbn
             end; try solve [f_equal; linear_arithmetic].
    }
  Qed.
    
  Lemma shift_c_c_subst_out n :
    forall b v x y,
      x <= y ->
      shift_c_c n y (subst_c_c x v b) = subst_c_c x (shift_c_c n y v) (shift_c_c n (S y) b).
  Proof.
    eapply shift_c_c_k_p_subst_out.
  Qed.
    
  Lemma shift_c_k_subst_out n :
    forall b v x y,
      x <= y ->
      shift_c_k n y (subst_c_k x v b) = subst_c_k x (shift_c_c n y v) (shift_c_k n (S y) b).
  Proof.
    eapply shift_c_c_k_p_subst_out.
  Qed.
    
  Lemma shift_c_p_subst_out n :
    forall b v x y,
      x <= y ->
      shift_c_p n y (subst_c_p x v b) = subst_c_p x (shift_c_c n y v) (shift_c_p n (S y) b).
  Proof.
    eapply shift_c_c_k_p_subst_out.
  Qed.
    
  Lemma shift_c_c_subst0 n x v b : shift_c_c n x (subst0_c_c v b) = subst0_c_c (shift_c_c n x v) (shift_c_c n (S x) b).
  Proof.
    unfold shift0_c_c, subst0_c_c.
    rewrite shift_c_c_subst_out; repeat (f_equal; try linear_arithmetic).
  Qed.
  
  Lemma subst_c_c_k_p_subst :
    (forall b v1 v2 x y,
        x <= y ->
        subst_c_c y v2 (subst_c_c x v1 b) = subst_c_c x (subst_c_c y v2 v1) (subst_c_c (S y) (shift_c_c 1 x v2) b)) /\
    (forall b v1 v2 x y,
        x <= y ->
        subst_c_k y v2 (subst_c_k x v1 b) = subst_c_k x (subst_c_c y v2 v1) (subst_c_k (S y) (shift_c_c 1 x v2) b)) /\
    (forall b v1 v2 x y,
        x <= y ->
        subst_c_p y v2 (subst_c_p x v1 b) = subst_c_p x (subst_c_c y v2 v1) (subst_c_p (S y) (shift_c_c 1 x v2) b)).
  Proof.
    eapply cstr_kind_prop_mutind;
      simplify;
      cbn in *;
        try solve [eauto |
                   f_equal; eauto |
                   erewrite H by linear_arithmetic; repeat f_equal; eauto with db_la |
                   repeat rewrite shift0_c_c_shift; simplify;
                   repeat rewrite shift0_c_c_subst_2; simplify;
                   repeat replace (S (y - n)) with (S y - n) by linear_arithmetic;
                   f_equal;
                   match goal with
                     H : _ |- _ => eapply H; eauto with db_la
                   end].
    {
      (* Case CVar *)
      repeat match goal with
             | |- context [?a <=? ?b] => cases (a <=? b); simplify; cbn
             | |- context [?a <=>? ?b] => cases (a <=>? b); simplify; cbn
             end; try solve [f_equal; linear_arithmetic].
      rewrite subst_c_c_shift_avoid by linear_arithmetic.
      simplify.
      rewrite shift_c_c_0.
      eauto.
    }
  Qed.
  
  Lemma subst_c_c_subst :
    forall b v1 v2 x y,
      x <= y ->
      subst_c_c y v2 (subst_c_c x v1 b) = subst_c_c x (subst_c_c y v2 v1) (subst_c_c (S y) (shift_c_c 1 x v2) b).
  Proof.
    eapply subst_c_c_k_p_subst.
  Qed.
  
  Lemma subst_c_k_subst :
    forall b v1 v2 x y,
      x <= y ->
      subst_c_k y v2 (subst_c_k x v1 b) = subst_c_k x (subst_c_c y v2 v1) (subst_c_k (S y) (shift_c_c 1 x v2) b).
  Proof.
    eapply subst_c_c_k_p_subst.
  Qed.
  
  Lemma subst_c_p_subst :
    forall b v1 v2 x y,
      x <= y ->
      subst_c_p y v2 (subst_c_p x v1 b) = subst_c_p x (subst_c_c y v2 v1) (subst_c_p (S y) (shift_c_c 1 x v2) b).
  Proof.
    eapply subst_c_c_k_p_subst.
  Qed.
  
  Lemma subst_c_c_subst0 n c c' t : subst_c_c n c (subst0_c_c c' t) = subst0_c_c (subst_c_c n c c') (subst_c_c (S n) (shift0_c_c c) t).
  Proof.
    eapply subst_c_c_subst.
    linear_arithmetic.
  Qed.
  
  Lemma map_shift0_subst n c ls :
    map shift0_c_c (map (subst_c_c n (shift_c_c n 0 c)) ls) =
    map (subst_c_c (1 + n) (shift_c_c (1 + n) 0 c)) (map shift0_c_c ls).
  Proof.
    repeat rewrite map_map.
    setoid_rewrite shift0_c_c_subst.
    eauto.
  Qed.
  
  Lemma kdeq_shift_c_k L k1 k2 :
    kdeq L k1 k2 ->
    forall x ls ,
      let n := length ls in
      x <= length L ->
      kdeq (shift_c_ks n (firstn x L) ++ ls ++ my_skipn L x) (shift_c_k n x k1) (shift_c_k n x k2).
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
      specialize (@interpP_shift_c_p (k :: L) (p <===> p')%idx H0 (S x) ls); intros HH.
      simplify; cbn in *.
      repeat erewrite length_firstn_le in * by linear_arithmetic.
      eauto with db_la.
    }
  Qed.
  
  Lemma kdeq_subst_c_k L k1 k2 :
    kdeq L k1 k2 ->
    forall n k c ,
      nth_error L n = Some k ->
      kinding (my_skipn L (1 + n)) c k ->
      kdeq (subst_c_ks c (firstn n L) ++ my_skipn L (1 + n)) (subst_c_k n (shift_c_c n 0 c) k1) (subst_c_k n (shift_c_c n 0 c) k2).
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
      specialize (@interpP_subst_c_p (k'' :: L) (p <===> p')%idx H0 (S n) k c); intros HH.
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
            rewrite length_shift_c_ks; erewrite length_firstn_le; try linear_arithmetic.
          rewrite nth_error_app2 by linear_arithmetic.
          rewrite nth_error_my_skipn by linear_arithmetic.
          erewrite <- H.
          f_equal.
          linear_arithmetic.
        }
        eapply kdeq_refl2.
        rewrite shift_c_k_shift_0 by linear_arithmetic.
        simplify.
        f_equal.
        linear_arithmetic.
      }
      {
        eapply KdEq.
        {
          eapply KdVar.
          rewrite nth_error_app1;
            try rewrite length_shift_c_ks; try erewrite length_firstn_le; try linear_arithmetic.
          erewrite nth_error_shift_c_ks; eauto.
          rewrite nth_error_firstn; eauto.
        }
        eapply kdeq_refl2.
        erewrite length_firstn_le by linear_arithmetic.
        rewrite shift_c_k_shift_2 by linear_arithmetic.
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
      repeat erewrite length_firstn_le in * by linear_arithmetic.
      rewrite shift_c_k_shift_2 in * by linear_arithmetic.
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
        linear_arithmetic.
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
      rewrite shift_c_k_shift_2 in * by linear_arithmetic.
      simplify.
      repeat rewrite Nat.sub_0_r in *.
      eauto with db_la.
    }
    {
      (* Case Eq *)
      econstructor; eauto.
      eapply kdeq_shift_c_k; eauto with db_tyeq.
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
      (* Case PEq *)
      rename H0 into IHwfprop1.
      rename H2 into IHwfprop2.
      econstructor; eauto.
      { eapply IHwfprop1; eauto. }
      eapply IHwfprop2; eauto.
    }
    {
      (* Case PQuan *)
      econstructor; eauto.
      rename H2 into IHwfprop.
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
        rewrite subst_c_k_shift by linear_arithmetic.
        econstructor.
        rewrite nth_error_app1.
        {
          erewrite nth_error_subst_c_ks.
          {
            repeat erewrite nth_error_length_firstn by eauto.
            eauto.
          }
          rewrite nth_error_firstn by linear_arithmetic.
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
        rewrite subst_c_k_shift_0_avoid by linear_arithmetic.
        simplify.
        repeat rewrite Nat.sub_0_r in *.
        eapply kd_shift_c_c with (x := 0) (ls := subst_c_ks c (firstn n L)) in H1; try linear_arithmetic.
        rewrite length_subst_c_ks in *.
        repeat erewrite nth_error_length_firstn in * by eauto.
        simplify.
        rewrite my_skipn_0 in *.
        eapply H1.
      }
      {
        rewrite subst_c_k_shift_0_avoid by linear_arithmetic.
        simplify.
        repeat rewrite Nat.sub_0_r in *.
        destruct x as [| x]; simplify; try linear_arithmetic.
        repeat rewrite Nat.sub_0_r in *.
        eapply KdVar.
        rewrite nth_error_app2; repeat rewrite length_subst_c_ks in *.
        {
          rewrite nth_error_my_skipn; repeat erewrite nth_error_length_firstn by eauto; try linear_arithmetic.
          replace (S n + (x - n)) with (S x); eauto.
          linear_arithmetic.
        }
        {
          repeat erewrite nth_error_length_firstn by eauto.
          linear_arithmetic.
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
      rewrite subst_c_k_shift in * by linear_arithmetic.
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
      rewrite subst_c_k_shift in * by linear_arithmetic.
      simplify.
      repeat rewrite Nat.sub_0_r in *.
      eauto.
    }
    {
      (* Case Eq *)
      econstructor; eauto.
      eapply kdeq_subst_c_k; eauto with db_tyeq.
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
      rename H2 into IHwfprop.
      specialize (IHwfprop (S n) k0 c).
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

  Fixpoint CApps t cs :=
    match cs with
    | nil => t
    | c :: cs => CApps (CApp t c) cs
    end
  .

  Lemma TyEqApps L cs cs' :
    Forall2 (tyeq L) cs cs' ->
    forall t t',
      tyeq L t t' ->
      tyeq L (CApps t cs) (CApps t' cs').
  Proof.
    induct 1; simplify; eauto.
    eapply IHForall2.
    econstructor; eauto.
  Qed.
  
  (* Lemma invert_tyeq_CApps cs cs' c c' : *)
  (*     tyeq [] (CApps c cs) (CApps c' cs') -> *)
  (*     tyeq [] c c' /\ *)
  (*     Forall2 (tyeq []) cs cs'. *)
  (* Proof. *)
  (*   induct 1; simplify. *)
  (*   { *)
  (*     destruct cs; destruct cs'; simplify; try discriminate. *)
  (*     admit. *)
  (*   } *)
  (* Qed. *)

  Lemma invert_tyeq_CApps_CRec cs cs' k t k' t' :
    tyeq [] (CApps (CRec k t) cs) (CApps (CRec k' t') cs') ->
    kdeq [] k k' /\
    tyeq [k] t t' /\
    Forall2 (tyeq []) cs cs'.
  Admitted.

  Lemma CApps_CRec_CArrow_false cs k3 t3 t1 i t2 :
    tyeq [] (CApps (CRec k3 t3) cs) (CArrow t1 i t2) ->
    False.
  Proof.
    (* Lemma CArrow_CApps_false cs : *)
    (*   forall t1 i t2 t3, *)
    (*     CArrow t1 i t2 = CApps t3 cs -> *)
    (*     (forall t1' i' t2', t3 <> CArrow t1' i' t2') ->  *)
    (*     False. *)
    (* Proof. *)
    (*   induction cs; simpl; subst; try discriminate; intuition eauto. *)
    (*   eapply IHcs; eauto. *)
    (*   intros; discriminate. *)
    (* Qed. *)
    (* intros; eapply CArrow_CApps_false; eauto. *)
    (* intros; discriminate. *)
  Admitted.

  Lemma CApps_CRec_CForall_false cs k3 t3 k t  :
    tyeq [] (CApps (CRec k3 t3) cs) (CForall k t) ->
    False.
  Proof.
  Admitted.

  Lemma CApps_CRec_CExists_false cs k3 t3 k t  :
    tyeq [] (CApps (CRec k3 t3) cs) (CExists k t) ->
    False.
  Proof.
  Admitted.

  Lemma CApps_CRec_CProd_false cs k3 t3 t1 t2  :
    tyeq [] (CApps (CRec k3 t3) cs) (CProd t1 t2) ->
    False.
  Proof.
  Admitted.

  Lemma CApps_CRec_CSum_false cs k3 t3 t1 t2  :
    tyeq [] (CApps (CRec k3 t3) cs) (CSum t1 t2) ->
    False.
  Proof.
  Admitted.

  Lemma CApps_CRec_CRef_false cs k3 t3 t  :
    tyeq [] (CApps (CRec k3 t3) cs) (CRef t) ->
    False.
  Proof.
  Admitted.

  Lemma CApps_CRec_CConst_false cs k3 t3 cn  :
    tyeq [] (CApps (CRec k3 t3) cs) (CConst cn) ->
    False.
  Admitted.
  
  Lemma shift_c_c_Apps cs :
    forall n x c,
      shift_c_c n x (CApps c cs) = CApps (shift_c_c n x c) (map (shift_c_c n x) cs).
  Proof.
    induct cs; simplify; eauto.
    rewrite IHcs; eauto.
  Qed.
  
  Lemma subst_c_c_Apps cs :
    forall n v c,
      subst_c_c n v (CApps c cs) = CApps (subst_c_c n v c) (map (subst_c_c n v) cs).
  Proof.
    induct cs; simplify; eauto.
    rewrite IHcs; eauto.
  Qed.


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

  Definition hctx := fmap loc cstr.
  Definition tctx := list cstr.
  Definition ctx := (kctx * hctx * tctx)%type.
  
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
  | EAbsC (e : expr)
  | EAppC (e : expr) (c : cstr)
  | EPack (c : cstr) (e : expr)
  | EUnpack (e1 e2 : expr)
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
  | VAbsC e :
      value (EAbsC e)
  | VPack c v :
      value v ->
      value (EPack c v)
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

  Definition add_kinding_ctx k (C : ctx) :=
    match C with
      (L, W, G) => (k :: L, fmap_map shift0_c_c W, map shift0_c_c G)
    end
  .

  Definition add_typing_ctx t (C : ctx) :=
    match C with
      (L, W, G) => (L, W, t :: G)
    end
  .

  Definition get_kctx (C : ctx) : kctx := fst (fst C).
  Definition get_hctx (C : ctx) : hctx := snd (fst C).
  Definition get_tctx (C : ctx) : tctx := snd C.


  Fixpoint EAbsCs n e :=
    match n with
    | 0 => e
    | S n => EAbsC (EAbsCs n e)
    end
  .

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
    | ECTT => CTypeUnit
    | ECInt _ => CInt
    end
  .

  Local Open Scope idx_scope.

  Inductive typing : ctx -> expr -> cstr -> cstr -> Prop :=
  | TyVar C x t :
      nth_error (get_tctx C) x = Some t ->
      typing C (EVar x) t T0
  | TyApp C e1 e2 t i1 i2 i t2 :
      typing C e1 (CArrow t2 i t) i1 ->
      typing C e2 t2 i2 ->
      typing C (EApp e1 e2) t (i1 + i2 + T1 + i)
  | TyAbs C e t1 i t :
      kinding (get_kctx C) t1 KType ->
      typing (add_typing_ctx t1 C) e t i ->
      typing C (EAbs e) (CArrow t1 i t) T0
  | TyAppC C e c t i k :
      typing C e (CForall k t) i ->
      kinding (get_kctx C) c k -> 
      typing C (EAppC e c) (subst0_c_c c t) i
  | TyAbsC C e t k :
      value e ->
      wfkind (get_kctx C) k ->
      typing (add_kinding_ctx k C) e t T0 ->
      typing C (EAbsC e) (CForall k t) T0
  | TyRec C e t n e1 :
      e = EAbsCs n (EAbs e1) ->
      kinding (get_kctx C) t KType ->
      typing (add_typing_ctx t C) e t T0 ->
      typing C (ERec e) t T0
  | TyFold C e t i t1 cs k t2 :
      t = CApps t1 cs ->
      t1 = CRec k t2 ->
      kinding (get_kctx C) t KType ->
      typing C e (CApps (subst0_c_c t1 t2) cs) i ->
      typing C (EFold e) t i
  | TyUnfold C e t k t1 cs i :
      t = CRec k t1 ->
      typing C e (CApps t cs) i ->
      typing C (EUnfold e) (CApps (subst0_c_c t t1) cs) i
  (* | TyAsc L G e t i : *)
  (*     kinding L t KType -> *)
  (*     typing (L, G) e t i -> *)
  (*     typing (L, G) (EAsc e t) t i *)
  | TyPack C c e i t1 k :
      (* kinding (get_kctx C) t1 (KArrow k KType) -> *)
      kinding (get_kctx C) (CExists k t1) KType ->
      kinding (get_kctx C) c k ->
      typing C e (subst0_c_c c t1) i ->
      typing C (EPack c e) (CExists k t1) i
  | TyUnpack C e1 e2 t2 i1 i2 t k :
      typing C e1 (CExists k t) i1 ->
      typing (add_typing_ctx t (add_kinding_ctx k C)) e2 (shift0_c_c t2) (shift0_c_c i2) ->
      typing C (EUnpack e1 e2) t2 (i1 + i2)
  | TyConst C cn :
      typing C (EConst cn) (const_type cn) T0
  | TyPair C e1 e2 t1 t2 i1 i2 :
      typing C e1 t1 i1 ->
      typing C e2 t2 i2 ->
      typing C (EPair e1 e2) (CProd t1 t2) (i1 + i2)
  | TyProj C pr e t1 t2 i :
      typing C e (CProd t1 t2) i ->
      typing C (EProj pr e) (proj (t1, t2) pr) i
  | TyInj C inj e t t' i :
      typing C e t i ->
      kinding (get_kctx C) t' KType ->
      typing C (EInj inj e) (choose (CSum t t', CSum t' t) inj) i
  | TyCase C e e1 e2 t i i1 i2 t1 t2 :
      typing C e (CSum t1 t2) i ->
      typing (add_typing_ctx t1 C) e1 t i1 ->
      typing (add_typing_ctx t2 C) e2 t i2 ->
      typing C (ECase e e1 e2) t (i + Tmax i1 i2)
  | TyNew C e t i :
      typing C e t i ->
      typing C (ENew e) (CRef t) i
  | TyRead C e t i :
      typing C e (CRef t) i ->
      typing C (ERead e) t i
  | TyWrite C e1 e2 i1 i2 t :
      typing C e1 (CRef t) i1 ->
      typing C e2 t i2 ->
      typing C (EWrite e1 e2) CTypeUnit (i1 + i2)
  | TyLoc C l t :
      get_hctx C $? l = Some t ->
      typing C (ELoc l) (CRef t) T0
  | TySub C e t2 i2 t1 i1 :
      typing C e t1 i1 ->
      tyeq (get_kctx C) t1 t2 ->
      interpP (get_kctx C) (i1 <= i2) ->
      typing C e t2 i2 
  .

  Local Close Scope idx_scope.

  Section shift_c_e.

    Variable n : nat.

    Fixpoint shift_c_e (x : var) (b : expr) : expr :=
      match b with
      | EVar y => EVar y
      | EConst cn => EConst cn
      | ELoc l => ELoc l
      | EUnOp opr e => EUnOp opr (shift_c_e x e)
      | EBinOp opr e1 e2 => EBinOp opr (shift_c_e x e1) (shift_c_e x e2)
      | ECase e e1 e2 => ECase (shift_c_e x e) (shift_c_e x e1) (shift_c_e x e2)
      | EAbs e => EAbs (shift_c_e x e)
      | ERec e => ERec (shift_c_e x e)
      | EAbsC e => EAbsC (shift_c_e (1 + x) e)
      | EAppC e c => EAppC (shift_c_e x e) (shift_c_c n x c)
      | EPack c e => EPack (shift_c_c n x c) (shift_c_e x e)
      | EUnpack e1 e2 => EUnpack (shift_c_e x e1) (shift_c_e (1 + x) e2)
      end.
    
  End shift_c_e.
  
  Definition shift0_c_e := shift_c_e 1 0.
  
  Section shift_e_e.

    Variable n : nat.

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
      | EAbsC e => EAbsC (shift_e_e x e)
      | EAppC e c => EAppC (shift_e_e x e) c
      | EPack c e => EPack c (shift_e_e x e)
      | EUnpack e1 e2 => EUnpack (shift_e_e x e1) (shift_e_e (1 + x) e2)
      end.
    
  End shift_e_e.
  
  Definition shift0_e_e := shift_e_e 1 0.
  
  Section subst_c_e.

    Fixpoint subst_c_e (x : var) (v : cstr) (b : expr) : expr :=
      match b with
      | EVar y => EVar y
      | EConst cn => EConst cn
      | ELoc l => ELoc l
      | EUnOp opr e => EUnOp opr (subst_c_e x v e)
      | EBinOp opr e1 e2 => EBinOp opr (subst_c_e x v e1) (subst_c_e x v e2)
      | ECase e e1 e2 => ECase (subst_c_e x v e) (subst_c_e x v e1) (subst_c_e x v e2)
      | EAbs e => EAbs (subst_c_e x v e)
      | ERec e => ERec (subst_c_e x v e)
      | EAbsC e => EAbsC (subst_c_e (1 + x) (shift0_c_c v) e)
      | EAppC e c => EAppC (subst_c_e x v e) (subst_c_c x v c)
      | EPack c e => EPack (subst_c_c x v c) (subst_c_e x v e)
      | EUnpack e1 e2 => EUnpack (subst_c_e x v e1) (subst_c_e (1 + x) (shift0_c_c v) e2)
      end.
    
  End subst_c_e.

  Definition subst0_c_e (v : cstr) b := subst_c_e 0 v b.

  Section subst_e_e.

    Fixpoint subst_e_e (x : var) (v : expr) (b : expr) : expr :=
      match b with
      | EVar y => 
        match y <=>? x with
        | Lt _ => EVar y
        | Eq _ => v
        | Gt _ => EVar (y - 1)
        end
      | EConst cn => EConst cn
      | ELoc l => ELoc l
      | EUnOp opr e => EUnOp opr (subst_e_e x v e)
      | EBinOp opr e1 e2 => EBinOp opr (subst_e_e x v e1) (subst_e_e x v e2)
      | ECase e e1 e2 => ECase (subst_e_e x v e) (subst_e_e (1 + x) (shift0_e_e v) e1) (subst_e_e (1 + x) (shift0_e_e v) e2)
      | EAbs e => EAbs (subst_e_e (1 + x) (shift0_e_e v) e)
      | ERec e => ERec (subst_e_e (1 + x) (shift0_e_e v) e)
      | EAbsC e => EAbsC (subst_e_e x (shift0_c_e v) e)
      | EAppC e c => EAppC (subst_e_e x v e) c
      | EPack c e => EPack c (subst_e_e x v e)
      | EUnpack e1 e2 => EUnpack (subst_e_e x v e1) (subst_e_e (1 + x) (shift0_e_e (shift0_c_e v)) e2)
      end.
    
  End subst_e_e.

  Definition subst0_e_e v b := subst_e_e 0 v b.

  Inductive ectx :=
  | ECHole
  | ECUnOp (opr : expr_un_op) (E : ectx)
  | ECBinOp1 (opr : expr_bin_op) (E : ectx) (e : expr)
  | ECBinOp2 (opr : expr_bin_op) (v : expr) (E : ectx)
  | ECCase (E : ectx) (e1 e2 : expr)
  | ECAppC (E : ectx) (c : cstr)
  | ECPack (c : cstr) (E : ectx)
  | ECUnpack (E : ectx) (e : expr)
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
  | PlugAppC E e e' c :
      plug E e e' ->
      plug (ECAppC E c) e (EAppC e' c)
  | PlugPack E e e' c :
      plug E e e' ->
      plug (ECPack c E) e (EPack c e')
  | PlugUnpack E e e' e2 :
      plug E e e' ->
      plug (ECUnpack E e2) e (EUnpack e' e2)
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
      astep (h, EUnpack (EPack c v) e, t) (h, subst0_e_e v (subst0_c_e c e), t)
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
  | ABetaC h e c t :
      astep (h, EAppC (EAbsC e) c, t) (h, subst0_c_e c e, t)
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

  Definition empty_ctx : ctx := ([], $0, []).
  Notation "${}" := empty_ctx.

  Definition allocatable (h : heap) := exists l_alloc, forall l, l >= l_alloc -> h $? l = None.
  
  Definition htyping (h : heap) (W : hctx) :=
    (forall l t,
        W $? l = Some t ->
        exists v,
          h $? l = Some v /\
          value v /\
          typing ([], W, []) v t T0) /\
    allocatable h.

  Definition ctyping W (s : config) t i :=
    let '(h, e, f) := s in
    typing ([], W, []) e t i /\
    htyping h W /\
    interpTime i <= f
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

  Arguments get_kctx _ / .
  Arguments get_hctx _ / .

  Hint Constructors step astep plug value.

  Arguments finished / .
  Arguments get_expr / .


  (* ============================================================= *)
  (* Term language proofs *)
  (* ============================================================= *)

  
  Lemma TyETT C : typing C ETT CTypeUnit T0.
  Proof.
    eapply TyConst.
  Qed.

  Lemma TyTyeq C e t2 i t1 :
    typing C e t1 i ->
    tyeq (get_kctx C) t1 t2 ->
    typing C e t2 i.
  Proof.
    intros.
    eapply TySub; eauto.
    eapply interpP_le_refl.
  Qed.

  Lemma TyLe C e t i1 i2 :
    typing C e t i1 ->
    interpP (get_kctx C) (i1 <= i2)%idx ->
    typing C e t i2.
  Proof.
    intros.
    eapply TySub; eauto.
    eauto with db_tyeq.
  Qed.
  
  Lemma TyIdxEq C e t i1 i2 :
    typing C e t i1 ->
    interpP (get_kctx C) (i1 == i2)%idx ->
    typing C e t i2.
  Proof.
    intros.
    eapply TyLe; eauto.
    eapply interpP_eq_interpP_le; eauto.
  Qed.
  
  Lemma CApps_CRec_const_type_false cs k3 t3 cn  :
    tyeq [] (CApps (CRec k3 t3) cs) (const_type cn) ->
    False.
  Proof.
    cases cn; simplify;
      eapply CApps_CRec_CConst_false; eauto.
  Qed.

  Lemma const_type_CArrow_false cn t1 i t2 :
    tyeq [] (const_type cn) (CArrow t1 i t2) ->
    False.
  Proof.
    cases cn; intros Htyeq; simplify;
      invert Htyeq.
  Qed.

  Lemma subst_c_c_const_type x v cn :
    subst_c_c x v (const_type cn) = const_type cn.
  Proof.
    cases cn; simplify; eauto.
  Qed.
  
  Lemma shift_c_e_AbsCs m :
    forall n x e,
      shift_c_e n x (EAbsCs m e) = EAbsCs m (shift_c_e n (m + x) e).
  Proof.
    induct m; simplify; eauto.
    rewrite IHm.
    repeat f_equal; eauto.
  Qed.
  
  Lemma shift_e_e_AbsCs m :
    forall n x e,
      shift_e_e n x (EAbsCs m e) = EAbsCs m (shift_e_e n x e).
  Proof.
    induct m; simplify; eauto.
    rewrite IHm.
    repeat f_equal; eauto.
  Qed.
  
  Lemma shift_c_e_0 b : forall x, shift_c_e 0 x b = b.
  Proof.
    induct b; simplify; try rewrite IHb; try rewrite IHb1; try rewrite IHb2; try rewrite IHb3; try rewrite shift_c_c_0; eauto.
  Qed.
  
  Lemma shift_c_e_shift b :
    forall n1 n2 x,
      shift_c_e n2 x (shift_c_e n1 x b) = shift_c_e (n1 + n2) x b.
  Proof.
    induct b; simplify; try rewrite IHb; try rewrite IHb1; try rewrite IHb2; try rewrite IHb3; try rewrite shift_c_c_shift; eauto.
  Qed.
  
  Lemma shift_c_e_shift0 n b :
    shift_c_e n 0 (shift0_c_e b) = shift_c_e (S n) 0 b.
  Proof.
    unfold shift0_c_e.
    rewrite shift_c_e_shift.
    eauto.
  Qed.
  
  Lemma map_shift0_shift n x G :
    map shift0_c_c (map (shift_c_c n x) G) =
    map (shift_c_c n (1 + x)) (map shift0_c_c G).
  Proof.
    repeat rewrite map_map.
    setoid_rewrite shift0_c_c_shift.
    eauto.
  Qed.

  Lemma fmap_map_shift0_shift n x (W : hctx) :
    fmap_map shift0_c_c (fmap_map (shift_c_c n x) W) =
    fmap_map (shift_c_c n (1 + x)) (fmap_map shift0_c_c W).
  Proof.
    repeat rewrite fmap_map_fmap_map.
    setoid_rewrite shift0_c_c_shift.
    eauto.
  Qed.

  Lemma fmap_map_shift0_subst n c (W : hctx) :
    fmap_map shift0_c_c (fmap_map (subst_c_c n (shift_c_c n 0 c)) W) =
    fmap_map (subst_c_c (1 + n) (shift_c_c (1 + n) 0 c)) (fmap_map shift0_c_c W).
  Proof.
    repeat rewrite fmap_map_fmap_map.
    setoid_rewrite shift0_c_c_subst.
    eauto.
  Qed.
  
  Lemma fmap_map_subst0_shift0 k c W : fmap_map (K := k) (subst0_c_c c) (fmap_map shift0_c_c W) = W.
  Proof.
    repeat rewrite fmap_map_fmap_map.
    setoid_rewrite subst0_c_c_shift0.
    eapply fmap_map_id.
  Qed.
  
  Lemma fmap_map_shift0_c_c_incl (W W' : hctx) :
    W $<= W' ->
    fmap_map shift0_c_c W $<= fmap_map shift0_c_c W'.
  Proof.
    intros; eapply incl_fmap_map; eauto.
  Qed.
  
  Lemma subst_c_e_AbsCs m :
    forall x v e,
      subst_c_e x v (EAbsCs m e) = EAbsCs m (subst_c_e (m + x) (shift_c_c m 0 v) e).
  Proof.
    induct m; simplify.
    {
      rewrite shift_c_c_0; eauto.
    }
    rewrite IHm.
    rewrite shift_c_c_shift0.
    repeat f_equal; eauto.
  Qed.
  
  Lemma subst_e_e_AbsCs m :
    forall x v e,
      subst_e_e x v (EAbsCs m e) = EAbsCs m (subst_e_e x (shift_c_e m 0 v) e).
  Proof.
    induct m; simplify.
    {
      rewrite shift_c_e_0; eauto.
    }
    rewrite IHm.
    rewrite shift_c_e_shift0.
    repeat f_equal; eauto.
  Qed.
  
  Lemma value_subst_c_e v :
    value v ->
    forall n c,
      value (subst_c_e n c v).
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
      eapply interpP_eq_add_0.
    }
  Qed.
    
  Lemma get_kctx_add_typing_ctx t C : get_kctx (add_typing_ctx t C) = get_kctx C.
  Proof.
    destruct C as ((L & W) & G); eauto.
  Qed.
  
  Hint Constructors Forall2.
  Lemma Forall2_map A B A' B' (P : A -> B -> Prop) (Q : A' -> B' -> Prop) f1 f2 ls1 ls2 :
    (forall a b, P a b -> Q (f1 a) (f2 b)) -> 
    Forall2 P ls1 ls2 ->
    Forall2 Q (map f1 ls1) (map f2 ls2).
  Proof.
    induct 2; simplify; eauto.
  Qed.
  
  Lemma ty_G_tyeq C e t i :
    typing C e t i ->
    forall G',
    Forall2 (tyeq (get_kctx C)) (get_tctx C) G' ->
    typing (get_kctx C, get_hctx C, G') e t i.
  Proof.
    induct 1;
      intros G' Htyeq;
      destruct C as ((L & W) & G);
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
      (* Case AbsC *)
      econstructor; simplify; eauto.
      eapply IHtyping.
      eapply Forall2_map; eauto.
      intros c c' Htyeq2.
      eapply tyeq_shift0_c_c; eauto.
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
        rewrite fmap_map_shift0_shift.
        rewrite map_shift0_shift.
        specialize (IHtyping (S x) ls); simplify.
        erewrite length_firstn_le in IHtyping by eauto.
        eapply IHtyping; eauto.
        linear_arithmetic.
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
        rewrite fmap_map_shift0_shift.
        rewrite map_shift0_shift.
        specialize (IHtyping2 (S x) ls); simplify.
        erewrite length_firstn_le in IHtyping2 by eauto.
        repeat rewrite shift0_c_c_shift.
        eapply IHtyping2; eauto.
        linear_arithmetic.
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
        eapply interpP_shift_c_p with (p := (i1 <= i2)%idx); eauto.
      }
    }
  Qed.

  Lemma ty_shift0_c_e L W G e t i k :
    typing (L, W, G) e t i ->
    typing (k :: L, fmap_map shift0_c_c W, map shift0_c_c G) (shift0_c_e e) (shift0_c_c t) (shift0_c_c i).
  Proof.
    intros Hty.
    eapply ty_shift_c_e with (C := (L, W, G)) (x := 0) (ls := [k]) in Hty; simplify; try linear_arithmetic.
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
        eapply interpP_subst_c_p with (p := (i1 <= i2)%idx); eauto.
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
        eapply interpP_eq_refl.
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
      linear_arithmetic.
    }
    {
      eapply Halloc.
      linear_arithmetic.
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
    linear_arithmetic.
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
    {
      eapply CApps_CRec_CForall_false in Htyeq; propositional.
    }
    {
      cases cn; simplify; invert Htyeq.
    }
    {
      cases inj; simplify; invert Htyeq.
    }
    {
      destruct C as ((L & W) & G); simplify; subst.
      eapply IHtyping; eauto with db_tyeq.
    }
  Qed.

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
    {
      eapply CApps_CRec_CExists_false in Htyeq; propositional.
    }
    {
      cases cn; simplify; invert Htyeq.
    }
    {
      cases inj; simplify; invert Htyeq.
    }
    {
      destruct C as ((L & W) & G); simplify; subst.
      eapply IHtyping; eauto with db_tyeq.
    }
  Qed.

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
    {
      eapply CApps_CRec_CProd_false in Htyeq; propositional.
    }
    {
      cases cn; simplify; invert Htyeq.
    }
    {
      cases inj; simplify; invert Htyeq.
    }
    {
      destruct C as ((L & W) & G); simplify; subst.
      eapply IHtyping; eauto with db_tyeq.
    }
  Qed.

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
    {
      eapply CApps_CRec_CSum_false in Htyeq; propositional.
    }
    {
      cases cn; simplify; invert Htyeq.
    }
    {
      destruct C as ((L & W) & G); simplify; subst.
      eapply IHtyping; eauto with db_tyeq.
    }
  Qed.
  
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
    {
      eapply CApps_CRec_CRef_false in Htyeq; propositional.
    }
    {
      cases cn; simplify; invert Htyeq.
    }
    {
      cases inj; simplify; invert Htyeq.
    }
    {
      destruct C as ((L & W) & G); simplify; subst.
      eapply IHtyping; eauto with db_tyeq.
    }
  Qed.
  
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
      (interpTime i <= f)%time ->
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
      assert (Hi1 : (interpTime i1 <= f)%time).
      {
        repeat rewrite interpTime_distr in Hle.
        repeat (eapply Time_add_le_elim in Hle; destruct Hle as (Hle & ?)).
        eauto.
      }
      assert (Hi2 : (interpTime i2 <= f)%time).
      {
        repeat rewrite interpTime_distr in Hle.
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
          repeat rewrite interpTime_distr in Hle.
          repeat rewrite interpTime_1 in Hle.
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
      assert (Hi1 : (interpTime i1 <= f)%time).
      {
        repeat rewrite interpTime_distr in Hle.
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
      assert (Hi1 : (interpTime i1 <= f)%time).
      {
        repeat rewrite interpTime_distr in Hle.
        repeat (eapply Time_add_le_elim in Hle; destruct Hle as (Hle & ?)).
        eauto.
      }
      assert (Hi2 : (interpTime i2 <= f)%time).
      {
        repeat rewrite interpTime_distr in Hle.
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
      assert (Hile : (interpTime i <= f)%time).
      {
        repeat rewrite interpTime_distr in Hle.
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
      assert (Hi1 : (interpTime i1 <= f)%time).
      {
        repeat rewrite interpTime_distr in Hle.
        repeat (eapply Time_add_le_elim in Hle; destruct Hle as (Hle & ?)).
        eauto.
      }
      assert (Hi2 : (interpTime i2 <= f)%time).
      {
        repeat rewrite interpTime_distr in Hle.
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
      eapply interpP_le_interpTime in H1.
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

  Section Forall3.

    Variables A B C : Type.
    Variable R : A -> B -> C -> Prop.

    Inductive Forall3 : list A -> list B -> list C -> Prop :=
    | Forall3_nil : Forall3 [] [] []
    | Forall3_cons : forall x y z l l' l'',
        R x y z -> Forall3 l l' l'' -> Forall3 (x::l) (y::l') (z::l'').

    Hint Constructors Forall3.

  End Forall3.

  Lemma invert_typing_App C e1 e2 t i :
    typing C (EApp e1 e2) t i ->
    exists t' t2 i1 i2 i3 ,
      tyeq (get_kctx C) t t' /\
      typing C e1 (CArrow t2 i3 t') i1 /\
      typing C e2 t2 i2 /\
      interpP (get_kctx C) (i1 + i2 + T1 + i3 <= i)%idx.
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
      interpP (get_kctx C) (i' <= i)%idx.
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
      interpP (get_kctx C) (i' <= i)%idx.
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
      interpP (get_kctx C) (i1 + i2 <= i)%idx.
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
      interpP (get_kctx C) (i' <= i)%idx.
  Proof.
    induct 1; openhyp; repeat eexists_split; eauto; eauto with db_tyeq.
  Qed.

  Lemma invert_typing_Read C e t i :
    typing C (ERead e) t i ->
    exists i' ,
      typing C e (CRef t) i' /\
      interpP (get_kctx C) (i' <= i)%idx.
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
      interpP (get_kctx C) (i1 + i2 <= i)%idx.
  Proof.
    induct 1; openhyp; repeat eexists_split; eauto; eauto with db_tyeq.
  Qed.

  Lemma invert_typing_New C e t i :
    typing C (ENew e) t i ->
    exists t' i' ,
      tyeq (get_kctx C) t (CRef t') /\
      typing C e t' i' /\
      interpP (get_kctx C) (i' <= i)%idx.
  Proof.
    induct 1; openhyp; repeat eexists_split; eauto; eauto with db_tyeq.
  Qed.

  Lemma invert_typing_AppC C e c t i :
    typing C (EAppC e c) t i ->
    exists t' i' k ,
      tyeq (get_kctx C) t (subst0_c_c c t') /\
      typing C e (CForall k t') i' /\
      kinding (get_kctx C) c k /\
      interpP (get_kctx C) (i' <= i)%idx.
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
      interpP (get_kctx C) (i' <= i)%idx.
  Proof.
    induct 1; openhyp; repeat eexists_split; eauto; eauto with db_tyeq.
  Qed.

  Lemma invert_typing_Pair C e1 e2 t i :
    typing C (EPair e1 e2) t i ->
    exists t1 t2 i1 i2 ,
      tyeq (get_kctx C) t (CProd t1 t2) /\
      typing C e1 t1 i1 /\
      typing C e2 t2 i2 /\
      interpP (get_kctx C) (i1 + i2 <= i)%idx.
  Proof.
    induct 1; openhyp; repeat eexists_split; eauto; eauto with db_tyeq.
  Qed.

  Lemma invert_typing_Case C e e1 e2 t i :
    typing C (ECase e e1 e2) t i ->
    exists t1 t2 i0 i1 i2 ,
      typing C e (CSum t1 t2) i0 /\
      typing (add_typing_ctx t1 C) e1 t i1 /\
      typing (add_typing_ctx t2 C) e2 t i2 /\
      interpP (get_kctx C) (i0 + Tmax i1 i2 <= i)%idx.
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
      interpP (get_kctx C) (i' <= i)%idx.
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
      (df <= interpTime i)%time /\
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
        eapply interpP_le_interpTime in Hle2.
        repeat rewrite interpTime_distr in Hle2.
        repeat rewrite interpTime_1 in Hle2.
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
          eapply interpP_le_interpTime in Hle2.
          repeat rewrite interpTime_distr in Hle2.
          repeat rewrite interpTime_1 in Hle2.
          copy Hle2 Hle2'.
          repeat (eapply Time_add_le_elim in Hle2; destruct Hle2 as (Hle2 & ?)).
          eapply interpTime_interpP_le.
          rewrite interpTime_minus_distr.
          rewrite interpTime_1.
          eapply Time_minus_move_left; eauto.
          eapply interpP_eq_interpTime in Hieq.
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
        rewrite interpTime_minus_distr.
        rewrite interpTime_1.
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
      destruct Htyeq2 as (Hkdeq & Htyeq2 & Htyeqcs).
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
          eapply TyEqApps; eauto.
          eapply tyeq_subst0_c_c; eauto.
          econstructor; eauto.
        }
        {
          simplify.
          rewrite Time_a_minus_a.
          eapply interpTime_interpP_le.
          rewrite interpTime_minus_distr.
          rewrite interpTime_0.
          rewrite Time_minus_0.
          eapply interpP_le_interpTime in Hle2.
          eapply interpP_le_interpTime in Hle3.
          eauto with time_order.
        }
      }
      {
        eapply Hhty.
      }
      {
        simplify.
        rewrite Time_a_minus_a.
        rewrite interpTime_minus_distr.
        rewrite interpTime_0.
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
            eapply interpTime_interpP_le.
            rewrite interpTime_minus_distr.
            rewrite interpTime_0.
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
        rewrite interpTime_minus_distr.
        rewrite interpTime_0.
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
      destruct Htyeq2 as (Htyeq2 & Hkdeq).
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
          eapply interpTime_interpP_le.
          rewrite interpTime_minus_distr.
          rewrite interpTime_0.
          rewrite Time_minus_0.
          eapply interpP_le_interpTime in Hle2.
          eapply interpP_le_interpTime in Hle3.
          repeat rewrite interpTime_distr in Hle2.
          repeat rewrite interpTime_1 in Hle2.
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
        rewrite interpTime_minus_distr.
        rewrite interpTime_0.
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
          eapply interpTime_interpP_le.
          rewrite interpTime_minus_distr.
          repeat rewrite interpTime_0.
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
        rewrite interpTime_minus_distr.
        repeat rewrite interpTime_0.
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
          eapply interpTime_interpP_le.
          rewrite interpTime_minus_distr.
          repeat rewrite interpTime_0.
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
        rewrite interpTime_minus_distr.
        repeat rewrite interpTime_0.
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
          eapply interpTime_interpP_le.
          rewrite interpTime_minus_distr.
          repeat rewrite interpTime_0.
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
        rewrite interpTime_minus_distr.
        repeat rewrite interpTime_0.
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
      destruct Htyeq2 as (Htyeq2 & Hkdeq).
      assert (Hkdck : kinding [] c k).
      {
        eapply KdEq; eauto.
        eapply kdeq_sym; eauto.
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
          eapply interpTime_interpP_le.
          rewrite interpTime_minus_distr.
          repeat rewrite interpTime_0.
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
        rewrite interpTime_minus_distr.
        repeat rewrite interpTime_0.
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
            eapply interpTime_interpP_le.
            rewrite interpTime_minus_distr.
            repeat rewrite interpTime_0.
            rewrite Time_minus_0.
            eapply interpP_le_interpTime in Hle2.
            eapply interpP_le_interpTime in Hle3.
            repeat rewrite interpTime_distr in Hle3.
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
            eapply interpTime_interpP_le.
            rewrite interpTime_minus_distr.
            repeat rewrite interpTime_0.
            rewrite Time_minus_0.
            eapply interpP_le_interpTime in Hle2.
            eapply interpP_le_interpTime in Hle3.
            repeat rewrite interpTime_distr in Hle3.
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
        rewrite interpTime_minus_distr.
        repeat rewrite interpTime_0.
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
            eapply interpTime_interpP_le.
            rewrite interpTime_minus_distr.
            repeat rewrite interpTime_0.
            rewrite Time_minus_0.
            eapply interpP_le_interpTime in Hle2.
            trans_rhs Hle2.
            rewrite interpTime_distr.
            eapply interpP_le_interpTime in Hle3.
            rewrite interpTime_max.
            eapply Time_le_trans.
            {
              instantiate (1 := (interpTime i1 + interpTime i0)%time).
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
            eapply interpTime_interpP_le.
            rewrite interpTime_minus_distr.
            repeat rewrite interpTime_0.
            rewrite Time_minus_0.
            eapply interpP_le_interpTime in Hle2.
            trans_rhs Hle2.
            rewrite interpTime_distr.
            eapply interpP_le_interpTime in Hle3.
            rewrite interpTime_max.
            eapply Time_le_trans.
            {
              instantiate (1 := (interpTime i2 + interpTime i0)%time).
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
        rewrite interpTime_minus_distr.
        repeat rewrite interpTime_0.
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
          interpP [] (i1 <= i)%idx /\
          forall e' e_all' W' i1',
            plug C e' e_all' ->
            typing ([], W', []) e' t1 i1' ->
            interpP [] (i1' <= i1)%idx ->
            W $<= W' ->
            typing ([], W', []) e_all' t (i1' + Tminus i i1)%idx.
  Proof.
    induct 1; intros W t i Hty.
    {
      exists t, i.
      repeat split; eauto.
      {
        eapply interpTime_interpP_le.
        eauto with time_order.
      }
      intros.
      invert H.
      eapply TyLe; eauto.
      simplify.
      eapply interpTime_interpP_le.
      rewrite interpTime_distr.
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
          eapply interpTime_interpP_le.
          eapply interpP_le_interpTime in Hle.
          eapply interpP_le_interpTime in Hle2.
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
          eapply interpTime_interpP_le.
          repeat rewrite interpTime_distr.
          rotate_lhs.
          rotate_rhs.
          cancel.
          repeat rewrite interpTime_minus_distr.
          eapply Time_minus_cancel.
          eapply interpP_le_interpTime in Hle.
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
          eapply interpTime_interpP_le.
          eapply interpP_le_interpTime in Hle.
          eapply interpP_le_interpTime in Hle2.
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
            eapply interpTime_interpP_le.
            repeat rewrite interpTime_distr.
            rotate_lhs.
            rotate_rhs.
            cancel.
            repeat rewrite interpTime_minus_distr.
            eapply Time_minus_cancel.
            eapply interpP_le_interpTime in Hle.
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
            eapply interpTime_interpP_le.
            repeat rewrite interpTime_distr.
            rotate_lhs.
            rotate_rhs.
            cancel.
            repeat rewrite interpTime_minus_distr.
            eapply Time_minus_cancel.
            eapply interpP_le_interpTime in Hle.
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
          eapply interpTime_interpP_le.
          eapply interpP_le_interpTime in Hle.
          eapply interpP_le_interpTime in Hle2.
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
          eapply interpTime_interpP_le.
          repeat rewrite interpTime_distr.
          rotate_lhs.
          rotate_rhs.
          cancel.
          repeat rewrite interpTime_minus_distr.
          eapply Time_minus_cancel.
          eapply interpP_le_interpTime in Hle.
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
          eapply interpTime_interpP_le.
          eapply interpP_le_interpTime in Hle.
          eapply interpP_le_interpTime in Hle2.
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
          eapply interpTime_interpP_le.
          repeat rewrite interpTime_distr.
          rotate_lhs.
          rotate_rhs.
          cancel.
          repeat rewrite interpTime_minus_distr.
          eapply Time_minus_cancel.
          eapply interpP_le_interpTime in Hle.
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
          eapply interpTime_interpP_le.
          eapply interpP_le_interpTime in Hle.
          eapply interpP_le_interpTime in Hle2.
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
          eapply interpTime_interpP_le.
          repeat rewrite interpTime_distr.
          rotate_lhs.
          rotate_rhs.
          cancel.
          repeat rewrite interpTime_minus_distr.
          eapply Time_minus_cancel.
          eapply interpP_le_interpTime in Hle.
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
          eapply interpTime_interpP_le.
          eapply interpP_le_interpTime in Hle.
          eapply interpP_le_interpTime in Hle2.
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
          eapply interpTime_interpP_le.
          repeat rewrite interpTime_distr.
          rotate_lhs.
          rotate_rhs.
          cancel.
          repeat rewrite interpTime_minus_distr.
          eapply Time_minus_cancel.
          eapply interpP_le_interpTime in Hle.
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
          eapply interpTime_interpP_le.
          eapply interpP_le_interpTime in Hle.
          eapply interpP_le_interpTime in Hle2.
          repeat rewrite interpTime_distr in Hle.
          repeat rewrite interpTime_1 in Hle.
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
          eapply interpTime_interpP_le.
          repeat rewrite interpTime_distr.
          rotate_rhs.
          do 4 rotate_lhs.
          cancel.
          do 3 rotate_lhs.
          repeat rewrite interpTime_minus_distr.
          eapply interpP_le_interpTime in Hle.
          eapply interpP_le_interpTime in Hle2.
          eapply interpP_le_interpTime in Hle3.
          rewrite Time_add_minus_assoc by eauto.
          eapply Time_minus_cancel.
          trans_rhs Hle.
          repeat rewrite interpTime_distr.
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
          eapply interpTime_interpP_le.
          eapply interpP_le_interpTime in Hle.
          eapply interpP_le_interpTime in Hle2.
          repeat rewrite interpTime_distr in Hle.
          repeat rewrite interpTime_1 in Hle.
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
          eapply interpTime_interpP_le.
          repeat rewrite interpTime_distr.
          rotate_rhs.
          do 2 rotate_lhs.
          cancel.
          rotate_lhs.
          repeat rewrite interpTime_minus_distr.
          eapply interpP_le_interpTime in Hle.
          eapply interpP_le_interpTime in Hle2.
          eapply interpP_le_interpTime in Hle3.
          rewrite Time_add_minus_assoc by eauto.
          eapply Time_minus_cancel.
          trans_rhs Hle.
          repeat rewrite interpTime_distr.
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
          eapply interpTime_interpP_le.
          eapply interpP_le_interpTime in Hle.
          eapply interpP_le_interpTime in Hle2.
          repeat rewrite interpTime_distr in Hle.
          repeat rewrite interpTime_1 in Hle.
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
          eapply interpTime_interpP_le.
          repeat rewrite interpTime_distr.
          rotate_rhs.
          do 2 rotate_lhs.
          cancel.
          rotate_lhs.
          repeat rewrite interpTime_minus_distr.
          eapply interpP_le_interpTime in Hle.
          eapply interpP_le_interpTime in Hle2.
          eapply interpP_le_interpTime in Hle3.
          rewrite Time_add_minus_assoc by eauto.
          eapply Time_minus_cancel.
          trans_rhs Hle.
          repeat rewrite interpTime_distr.
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
          eapply interpTime_interpP_le.
          eapply interpP_le_interpTime in Hle.
          eapply interpP_le_interpTime in Hle2.
          repeat rewrite interpTime_distr in Hle.
          repeat rewrite interpTime_1 in Hle.
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
          eapply interpTime_interpP_le.
          repeat rewrite interpTime_distr.
          repeat rewrite Time_add_assoc.
          rotate_rhs.
          do 3 rotate_lhs.
          cancel.
          do 3 rotate_lhs.
          repeat rewrite interpTime_minus_distr.
          eapply interpP_le_interpTime in Hle.
          eapply interpP_le_interpTime in Hle2.
          eapply interpP_le_interpTime in Hle3.
          rewrite Time_add_minus_assoc by eauto.
          eapply Time_minus_cancel.
          trans_rhs Hle.
          repeat rewrite interpTime_distr.
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
          eapply interpTime_interpP_le.
          eapply interpP_le_interpTime in Hle.
          eapply interpP_le_interpTime in Hle2.
          repeat rewrite interpTime_distr in Hle.
          repeat rewrite interpTime_1 in Hle.
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
          eapply interpTime_interpP_le.
          eapply interpP_le_interpTime in Hle.
          eapply interpP_le_interpTime in Hle2.
          eapply interpP_le_interpTime in Hle3.
          repeat rewrite interpTime_distr in *.
          rotate_rhs.
          rotate_lhs.
          cancel.
          rotate_lhs.
          repeat rewrite interpTime_minus_distr.
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
          eapply interpTime_interpP_le.
          eapply interpP_le_interpTime in Hle.
          eapply interpP_le_interpTime in Hle2.
          repeat rewrite interpTime_distr in Hle.
          repeat rewrite interpTime_1 in Hle.
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
          eapply interpTime_interpP_le.
          eapply interpP_le_interpTime in Hle.
          eapply interpP_le_interpTime in Hle2.
          eapply interpP_le_interpTime in Hle3.
          repeat rewrite interpTime_distr in *.
          rotate_rhs.
          rotate_lhs.
          cancel.
          rotate_lhs.
          repeat rewrite interpTime_minus_distr.
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
        eapply interpTime_interpP_le.
        eapply interpP_le_interpTime in Hle.
        eapply interpP_le_interpTime in Hle2.
        repeat rewrite interpTime_distr in Hle.
        repeat rewrite interpTime_1 in Hle.
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
        eapply interpTime_interpP_le.
        eapply interpP_le_interpTime in Hle.
        eapply interpP_le_interpTime in Hle2.
        eapply interpP_le_interpTime in Hle3.
        repeat rewrite interpTime_distr in *.
        rotate_rhs.
        do 2 rotate_lhs.
        cancel.
        rotate_lhs.
        repeat rewrite interpTime_minus_distr.
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
        eapply interpTime_interpP_le.
        eapply interpP_le_interpTime in Hle.
        eapply interpP_le_interpTime in Hle2.
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
        eapply interpTime_interpP_le.
        repeat rewrite interpTime_distr.
        rotate_lhs.
        rotate_rhs.
        cancel.
        repeat rewrite interpTime_minus_distr.
        eapply Time_minus_cancel.
        eapply interpP_le_interpTime in Hle.
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
        eapply interpTime_interpP_le.
        eapply interpP_le_interpTime in Hle.
        eapply interpP_le_interpTime in Hle2.
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
        eapply interpTime_interpP_le.
        repeat rewrite interpTime_distr.
        rotate_lhs.
        rotate_rhs.
        cancel.
        repeat rewrite interpTime_minus_distr.
        eapply Time_minus_cancel.
        eapply interpP_le_interpTime in Hle.
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
        eapply interpTime_interpP_le.
        eapply interpP_le_interpTime in Hle.
        eapply interpP_le_interpTime in Hle2.
        repeat rewrite interpTime_distr in Hle.
        repeat rewrite interpTime_1 in Hle.
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
        eapply interpTime_interpP_le.
        eapply interpP_le_interpTime in Hle.
        eapply interpP_le_interpTime in Hle2.
        eapply interpP_le_interpTime in Hle3.
        repeat rewrite interpTime_distr in *.
        rotate_rhs.
        do 2 rotate_lhs.
        cancel.
        rotate_lhs.
        repeat rewrite interpTime_minus_distr.
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
      eapply interpP_le_interpTime in Hle2.
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
      repeat rewrite interpTime_minus_distr in *.
      rewrite interpTime_const in *.
      eauto with time_order.
    }
    Unfocus.
    exists W'.
    eexists.
    repeat try_split; eauto.
    simplify.
    interp_le.
    repeat rewrite interpTime_distr in *.
    repeat rewrite interpTime_minus_distr in *.
    rewrite interpTime_const in *.
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