Set Implicit Arguments.

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

Module Type BIG_O (Time : TIME).
  
  Fixpoint time_fun time_type (arity : nat) :=
    match arity with
    | 0 => time_type
    | S n => nat -> time_fun time_type n
    end.

  Parameter Time_BigO : forall arity : nat, time_fun Time.time_type arity -> time_fun Time.time_type arity -> Prop.
  
End BIG_O.

Definition option_dec A (x : option A) : {a | x = Some a} + {x = None}.
  destruct x.
  left.
  exists a.
  eauto.
  right.
  eauto.
Qed.

Require Import Frap.

Require BinIntDef.

Fixpoint insert A new n (ls : list A) :=
  match n with
  | 0 => new ++ ls
  | S n => 
    match ls with
    | [] => new
    | a :: ls => a :: insert new n ls
    end
  end.

Fixpoint removen A n (ls : list A) {struct ls} :=
  match ls with
  | [] => []
  | a :: ls =>
    match n with
    | 0 => ls
    | S n => a :: removen n ls
    end
  end.

Definition fmap_forall K A (p : A -> Prop) (m : fmap K A) : Prop := forall k v, m $? k = Some v -> p v.
  
Require Import Datatypes.

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

Module TiML (Time : TIME) (BigO :BIG_O Time).
  
  Import Time BigO.

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
  | IBNatAdd
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
  | PBNatLt
  (* | PBTimeEq *)
  | PBBigO (arity : nat)
  .

  (* base sorts *)
  Inductive bsort :=
  | BSNat
  | BSUnit
  | BSBool
  | BSTime
  | BSArrow (b1 b2 : bsort)
  .

  Definition var := nat.

  Inductive idx :=
  | IVar (x : var)
  | IConst (cn : idx_const)
  | IUnOp (opr : idx_un_op) (c : idx)
  | IBinOp (opr : idx_bin_op) (c1 c2 : idx)
  | IIte (i1 i2 i3 : idx)
  | IAbs (i : idx)
  | IApp (arg_bsort : bsort) (c1 c2 : idx)
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

  Definition SUnit := SBaseSort BSUnit.
  Definition SBool := SBaseSort BSBool.
  Definition SNat := SBaseSort BSNat.
  Definition STime := SBaseSort BSTime.
  Definition SArrow b1 b2 := SBaseSort (BSArrow b1 b2).
  Fixpoint BSTimeFun arity :=
    match arity with
    | 0 => BSTime
    | S n => BSArrow BSNat (BSTimeFun n)
    end.
  Definition STimeFun arity := SBaseSort (BSTimeFun arity).
  
  Notation Tconst r := (IConst (ICTime r)).
  Notation T0 := (Tconst Time0).
  Notation T1 := (Tconst Time1).
  Definition Tadd := IBinOp IBTimeAdd.
  Definition Tminus := IBinOp IBTimeMinus.
  Definition Tmax := IBinOp IBTimeMax.
  Definition Nadd := IBinOp IBNatAdd.

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

  Definition Tle := PBinPred PBTimeLe.
  Definition TEq := PEq BSTime.
  Infix "<=" := Tle : idx_scope.
  Definition Nlt := PBinPred PBNatLt.
  Infix "<" := Nlt : idx_scope.
  Infix "==" := TEq (at level 70) : idx_scope.
  Infix "===>" := PImply (at level 95) : idx_scope.
  Infix "<===>" := PIff (at level 95) : idx_scope.
  Infix "/\" := PAnd : idx_scope.
  
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
    | IBNatAdd => BSNat
    end.

  Definition ibinop_arg2_bsort opr :=
    match opr with
    | IBTimeAdd => BSTime
    | IBTimeMinus => BSTime
    | IBTimeMax => BSTime
    | IBNatAdd => BSNat
    end.

  Definition ibinop_result_bsort opr :=
    match opr with
    | IBTimeAdd => BSTime
    | IBTimeMinus => BSTime
    | IBTimeMax => BSTime
    | IBNatAdd => BSNat
    end.

  Definition binpred_arg1_bsort opr :=
    match opr with
    | PBTimeLe => BSTime
    | PBNatLt => BSNat
    (* | PBTimeEq => BSTime *)
    | PBBigO n => BSTimeFun n
    end
  .

  Definition binpred_arg2_bsort opr :=
    match opr with
    | PBTimeLe => BSTime
    | PBNatLt => BSNat
    (* | PBTimeEq => BSTime *)
    | PBBigO n => BSTimeFun n
    end
  .

  Definition map_snd A B1 B2 (f : B1 -> B2) (a : A * B1) := (fst a, f (snd a)).
    
  Section shift_i.

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
      | IAbs i => IAbs (shift_i_i (1 + x) i)
      | IApp n c1 c2 => IApp n (shift_i_i x c1) (shift_i_i x c2)
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

  End shift_i.
  
  Definition shift0_i_i := shift_i_i 1 0.
  Definition shift0_i_s := shift_i_s 1 0.
  Definition shift0_i_p := shift_i_p 1 0.

  Require Import Datatypes.

  Ltac la := linear_arithmetic.

  Section shift_i_proofs.
    
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
    
    Lemma shift0_i_i_shift n x b :
      shift0_i_i (shift_i_i n x b) = shift_i_i n (1 + x) (shift0_i_i b).
    Proof.
      unfold shift0_i_i; intros.
      symmetry.
      rewrite shift_i_i_shift_cut; repeat f_equal; la.
    Qed.

  End shift_i_proofs.

  Fixpoint interp_bsort (b : bsort) :=
    match b with
    | BSNat => nat
    | BSUnit => unit
    | BSBool => bool
    | BSTime => time_type
    | BSArrow b1 b2 => interp_bsort b1 -> interp_bsort b2
    end.

  Fixpoint bsort_default_value (b : bsort) : interp_bsort b :=
    match b with
    | BSNat => 0%nat
    | BSUnit => tt
    | BSBool => false
    | BSTime => 0%time
    | BSArrow b1 b2 => fun _ => bsort_default_value b2
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

  Fixpoint lift7 arg_ks : forall t1 t2 t3 t4 t5 t6 t7 t, (t1 -> t2 -> t3 -> t4 -> t5 -> t6 -> t7 -> t) -> interp_bsorts arg_ks t1 -> interp_bsorts arg_ks t2 -> interp_bsorts arg_ks t3 -> interp_bsorts arg_ks t4 -> interp_bsorts arg_ks t5 -> interp_bsorts arg_ks t6 -> interp_bsorts arg_ks t7 -> interp_bsorts arg_ks t :=
    match arg_ks return forall t1 t2 t3 t4 t5 t6 t7 t, (t1 -> t2 -> t3 -> t4 -> t5 -> t6 -> t7 -> t) -> interp_bsorts arg_ks t1 -> interp_bsorts arg_ks t2 -> interp_bsorts arg_ks t3 -> interp_bsorts arg_ks t4 -> interp_bsorts arg_ks t5 -> interp_bsorts arg_ks t6 -> interp_bsorts arg_ks t7 -> interp_bsorts arg_ks t with
    | [] =>
      fun t1 t2 t3 t4 t5 t6 t7 t f x1 x2 x3 x4 x5 x6 x7 => f x1 x2 x3 x4 x5 x6 x7
    | arg_k :: arg_ks =>
      fun t1 t2 t3 t4 t5 t6 t7 t f x1 x2 x3 x4 x5 x6 x7 => lift7 arg_ks (fun a1 a2 a3 a4 a5 a6 a7 ak => f (a1 ak) (a2 ak) (a3 ak) (a4 ak) (a5 ak) (a6 ak) (a7 ak)) x1 x2 x3 x4 x5 x6 x7
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
  
  Lemma fuse_lift1_lift5 bs :
    forall T A1 B1 B2 B3 B4 B5 (f : A1 -> T) (g : B1 -> B2 -> B3 -> B4 -> B5 -> A1) b1 b2 b3 b4 b5,
      lift1 bs f (lift5 bs g b1 b2 b3 b4 b5) = lift5 bs (fun b1 b2 b3 b4 b5 => f (g b1 b2 b3 b4 b5)) b1 b2 b3 b4 b5.
  Proof.
    induct bs; simplify; eauto.
    eapply IHbs.
  Qed.
  
  Lemma fuse_lift1_lift6 ks :
    forall A B C D E F G H (h : G -> H) (g : A -> B -> C -> D -> E -> F -> G) a b c d e f,
      lift1 ks h (lift6 ks g a b c d e f) = lift6 ks (fun a b c d e f => h (g a b c d e f)) a b c d e f.
  Proof.
    induct ks; simplify; eauto.
    eapply IHks.
  Qed.
  
  Lemma fuse_lift1_lift7 bs :
    forall T A1 B1 B2 B3 B4 B5 B6 B7 (f : A1 -> T) (g : B1 -> B2 -> B3 -> B4 -> B5 -> B6 -> B7 -> A1) b1 b2 b3 b4 b5 b6 b7,
      lift1 bs f (lift7 bs g b1 b2 b3 b4 b5 b6 b7) = lift7 bs (fun b1 b2 b3 b4 b5 b6 b7 => f (g b1 b2 b3 b4 b5 b6 b7)) b1 b2 b3 b4 b5 b6 b7.
  Proof.
    induct bs; simplify; eauto.
    eapply IHbs.
  Qed.

  Lemma fuse_lift2_lift0_1 ks :
    forall A B C (f : A -> B -> C) (g : A) b,
      lift2 ks f (lift0 ks g) b = lift1 ks (fun b => f g b) b.
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
  
  Lemma fuse_lift2_lift3_1 bs :
    forall T A1 A2 B1 B2 B3 (f : A1 -> A2 -> T) (g : B1 -> B2 -> B3 -> A1) b1 b2 b3 a2,
      lift2 bs f (lift3 bs g b1 b2 b3) a2 = lift4 bs (fun b1 b2 b3 a2 => f (g b1 b2 b3) a2) b1 b2 b3 a2.
  Proof.
    induct bs; simplify; eauto.
    eapply IHbs.
  Qed.
  
  Lemma fuse_lift2_lift3_2 bs :
    forall T A1 A2 B1 B2 B3 (f : A1 -> A2 -> T) (g : B1 -> B2 -> B3 -> A2) a1 b1 b2 b3,
      lift2 bs f a1 (lift3 bs g b1 b2 b3) = lift4 bs (fun a1 b1 b2 b3 => f a1 (g b1 b2 b3)) a1 b1 b2 b3.
  Proof.
    induct bs; simplify; eauto.
    eapply IHbs.
  Qed.
  
  Lemma fuse_lift3_lift0_1 bs :
    forall T A1 A2 A3 (f : A1 -> A2 -> A3 -> T) (g : A1) a2 a3,
      lift3 bs f (lift0 bs g) a2 a3 = lift2 bs (fun a2 a3 => f g a2 a3) a2 a3.
  Proof.
    induct bs; simplify; eauto.
    eapply IHbs.
  Qed.
  
  Lemma fuse_lift3_lift0_2 bs :
    forall T A1 A2 A3 (f : A1 -> A2 -> A3 -> T) (g : A2) a1 a3,
      lift3 bs f a1 (lift0 bs g) a3 = lift2 bs (fun a1 a3 => f a1 g a3) a1 a3.
  Proof.
    induct bs; simplify; eauto.
    eapply IHbs.
  Qed.
  
  Lemma fuse_lift3_lift0_3 bs :
    forall T A1 A2 A3 f (g : A3) a1 a2,
      lift3 bs f a1 a2 (lift0 bs g) = lift2 bs (fun (a1 : A1) (a2 : A2) => f a1 a2 g : T) a1 a2.
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
  
  Lemma fuse_lift3_lift2_1 ks :
    forall A B C D E F (f : E -> C -> D -> F) (g : A -> B -> E) a b c d,
      lift3 ks f (lift2 ks g a b) c d = lift4 ks (fun a b c d => f (g a b) c d) a b c d.
  Proof.
    induct ks; simplify; eauto.
    eapply IHks.
  Qed.
  
  Lemma fuse_lift3_lift2_2 bs :
    forall T A1 A2 A3 B1 B2 (f : A1 -> A2 -> A3 -> T) (g : B1 -> B2 -> A2) a1 b1 b2 a3,
      lift3 bs f a1 (lift2 bs g b1 b2) a3 = lift4 bs (fun a1 b1 b2 a3 => f a1 (g b1 b2) a3) a1 b1 b2 a3.
  Proof.
    induct bs; simplify; eauto.
    eapply IHbs.
  Qed.
  
  Lemma fuse_lift3_lift2_3 ks :
    forall A B C D E F (f : A -> B -> E -> F) (g : C -> D -> E) a b c d,
      lift3 ks f a b (lift2 ks g c d) = lift4 ks (fun a b c d => f a b (g c d)) a b c d.
  Proof.
    induct ks; simplify; eauto.
    eapply IHks.
  Qed.
  
  Lemma fuse_lift3_lift3_1 bs :
    forall T A1 A2 A3 B1 B2 B3 f g b1 b2 b3 a2 a3,
      lift3 bs f (lift3 bs g b1 b2 b3) a2 a3 = lift5 bs (fun (b1 : B1) (b2 : B2) (b3 : B3) (a2 : A2) (a3 : A3) => f (g b1 b2 b3 : A1) a2 a3 : T) b1 b2 b3 a2 a3.
  Proof.
    induct bs; simplify; eauto.
    eapply IHbs.
  Qed.
  
  Lemma fuse_lift3_lift3_2 bs :
    forall T A1 A2 A3 B1 B2 B3 (f : A1 -> A2 -> A3 -> T) (g : B1 -> B2 -> B3 -> A2) a1 a3 b1 b2 b3,
      lift3 bs f a1 (lift3 bs g b1 b2 b3) a3 = lift5 bs (fun a1 b1 b2 b3 a3 => f a1 (g b1 b2 b3) a3) a1 b1 b2 b3 a3.
  Proof.
    induct bs; simplify; eauto.
    eapply IHbs.
  Qed.
  
  Lemma fuse_lift3_lift3_3 bs :
    forall T A1 A2 A3 B1 B2 B3 (f : A1 -> A2 -> A3 -> T) (g : B1 -> B2 -> B3 -> A3) a1 a2 b1 b2 b3,
      lift3 bs f a1 a2 (lift3 bs g b1 b2 b3) = lift5 bs (fun a1 a2 b1 b2 b3 => f a1 a2 (g b1 b2 b3)) a1 a2 b1 b2 b3.
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
  
  Lemma fuse_lift4_lift1_2 bs :
    forall T A1 A2 A3 A4 B1 (f : A1 -> A2 -> A3 -> A4 -> T) (g : B1 -> A2) a1 a3 a4 b1,
      lift4 bs f a1 (lift1 bs g b1) a3 a4 = lift4 bs (fun a1 b1 a3 a4 => f a1 (g b1) a3 a4) a1 b1 a3 a4.
  Proof.
    induct bs; simplify; eauto.
    eapply IHbs.
  Qed.
  
  Lemma fuse_lift4_lift1_4 bs :
    forall T A1 A2 A3 A4 B1 (f : A1 -> A2 -> A3 -> A4 -> T) (g : B1 -> A4) a1 a2 a3 b1,
      lift4 bs f a1 a2 a3 (lift1 bs g b1) = lift4 bs (fun a1 a2 a3 b1 => f a1 a2 a3 (g b1)) a1 a2 a3 b1.
  Proof.
    induct bs; simplify; eauto.
    eapply IHbs.
  Qed.
  
  Lemma fuse_lift4_lift2_4 ks :
    forall A B C D E F G (f : A -> B -> C -> F -> G) (g : D -> E -> F) a b c d e,
      lift4 ks f a b c (lift2 ks g d e) = lift5 ks (fun a b c d e => f a b c (g d e)) a b c d e.
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
  
  Lemma fuse_lift4_lift3_4 bs :
    forall T A1 A2 A3 A4 B1 B2 B3 (f : A1 -> A2 -> A3 -> A4 -> T) (g : B1 -> B2 -> B3 -> A4) a1 a2 a3 b1 b2 b3,
      lift4 bs f a1 a2 a3 (lift3 bs g b1 b2 b3) = lift6 bs (fun a1 a2 a3 b1 b2 b3 => f a1 a2 a3 (g b1 b2 b3)) a1 a2 a3 b1 b2 b3.
  Proof.
    induct bs; simplify; eauto.
    eapply IHbs.
  Qed.
  
  Lemma fuse_lift4_lift4_4 bs :
    forall T A1 A2 A3 A4 B1 B2 B3 B4 (f : A1 -> A2 -> A3 -> A4 -> T) (g : B1 -> B2 -> B3 -> B4 -> A4) a1 a2 a3 b1 b2 b3 b4,
      lift4 bs f a1 a2 a3 (lift4 bs g b1 b2 b3 b4) = lift7 bs (fun a1 a2 a3 b1 b2 b3 b4 => f a1 a2 a3 (g b1 b2 b3 b4)) a1 a2 a3 b1 b2 b3 b4.
  Proof.
    induct bs; simplify; eauto.
    eapply IHbs.
  Qed.
  
  Lemma fuse_lift5_lift0_4 bs :
    forall T A1 A2 A3 A4 A5 (f : A1 -> A2 -> A3 -> A4 -> A5 -> T) (g : A4) a1 a2 a3 a5,
      lift5 bs f a1 a2 a3 (lift0 bs g) a5 = lift4 bs (fun a1 a2 a3 a5 => f a1 a2 a3 g a5) a1 a2 a3 a5.
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
  
  Lemma fuse_lift5_lift1_4 bs :
    forall T A1 A2 A3 A4 A5 B1 (f : A1 -> A2 -> A3 -> A4 -> A5 -> T) (g : B1 -> A4) a1 a2 a3 b1 a5,
      lift5 bs f a1 a2 a3 (lift1 bs g b1) a5 = lift5 bs (fun a1 a2 a3 b1 a5 => f a1 a2 a3 (g b1) a5) a1 a2 a3 b1 a5.
  Proof.
    induct bs; simplify; eauto.
    eapply IHbs.
  Qed.
  
  Lemma fuse_lift5_lift3_5 bs :
    forall T A1 A2 A3 A4 A5 B1 B2 B3 (f : A1 -> A2 -> A3 -> A4 -> A5 -> T) (g : B1 -> B2 -> B3 -> A5) a1 a2 a3 a4 b1 b2 b3,
      lift5 bs f a1 a2 a3 a4 (lift3 bs g b1 b2 b3) = lift7 bs (fun a1 a2 a3 a4 b1 b2 b3 => f a1 a2 a3 a4 (g b1 b2 b3)) a1 a2 a3 a4 b1 b2 b3.
  Proof.
    induct bs; simplify; eauto.
    eapply IHbs.
  Qed.
  
  Lemma dedup_lift2 ks :
    forall A B (f : A -> A -> B) a,
      lift2 ks f a a = lift1 ks (fun a => f a a) a.
  Proof.
    induct ks; simplify; eauto.
    eapply IHks.
  Qed.
  
  Lemma dedup_lift3_1_2 bs :
    forall T A1 A3 (f : A1 -> A1 -> A3 -> T) a1 a3,
      lift3 bs f a1 a1 a3 = lift2 bs (fun a1 a3 => f a1 a1 a3) a1 a3.
  Proof.
    induct bs; simplify; eauto.
    eapply IHbs.
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
  
  Lemma dedup_lift4_2_4 bs :
    forall T A1 A2 A3 (f : A1 -> A2 -> A3 -> A2  -> T) a1 a2 a3,
      lift4 bs f a1 a2 a3 a2 = lift3 bs (fun a1 a2 a3 => f a1 a2 a3 a2) a1 a2 a3.
  Proof.
    induct bs; simplify; eauto.
    eapply IHbs.
  Qed.
  
  Lemma dedup_lift4_3_4 ks :
    forall A B C D (f : A -> B -> C -> C -> D) a b c,
      lift4 ks f a b c c = lift3 ks (fun a b c => f a b c c) a b c.
  Proof.
    induct ks; simplify; eauto.
    eapply IHks.
  Qed.
  
  Lemma dedup_lift5_1_4 bs :
    forall T A1 A2 A3 A4 f a1 a2 a3 a4,
      lift5 bs f a1 a2 a3 a1 a4 = lift4 bs (fun (a1 : A1) (a2 : A2) (a3 : A3) (a4 : A4) => f a1 a2 a3 a1 a4 : T) a1 a2 a3 a4.
  Proof.
    induct bs; simplify; eauto.
    eapply IHbs.
  Qed.
  
  Lemma dedup_lift5_2_3 ks :
    forall A B C D E (f : A -> B -> B -> C -> D -> E) a b c d,
      lift5 ks f a b b c d = lift4 ks (fun a b c d => f a b b c d) a b c d.
  Proof.
    induct ks; simplify; eauto.
    eapply IHks.
  Qed.
  
  Lemma dedup_lift5_2_4 bs :
    forall T A1 A2 A3 A5 (f : A1 -> A2 -> A3 -> A2 -> A5 -> T) a1 a2 a3 a5,
      lift5 bs f a1 a2 a3 a2 a5 = lift4 bs (fun a1 a2 a3 a5 => f a1 a2 a3 a2 a5) a1 a2 a3 a5.
  Proof.
    induct bs; simplify; eauto.
    eapply IHbs.
  Qed.
  
  Lemma dedup_lift5_2_5 bs :
    forall T A1 A2 A3 A4 (f : A1 -> A2 -> A3 -> A4 -> A2 -> T) a1 a2 a3 a4,
      lift5 bs f a1 a2 a3 a4 a2 = lift4 bs (fun a1 a2 a3 a4 => f a1 a2 a3 a4 a2) a1 a2 a3 a4.
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
  
  Lemma dedup_lift6_1_5 ks :
    forall A B C D E F (f : A -> B -> C -> D -> A -> E -> F) a b c d e,
      lift6 ks f a b c d a e = lift5 ks (fun a b c d e => f a b c d a e) a b c d e.
  Proof.
    induct ks; simplify; eauto.
    eapply IHks.
  Qed.
  
  Lemma dedup_lift6_2_4 bs :
    forall T A1 A2 A3 A5 A6 (f : A1 -> A2 -> A3 -> A2 -> A5 -> A6 -> T) a1 a2 a3 a5 a6,
      lift6 bs f a1 a2 a3 a2 a5 a6 = lift5 bs (fun a1 a2 a3 a5 a6 => f a1 a2 a3 a2 a5 a6) a1 a2 a3 a5 a6.
  Proof.
    induct bs; simplify; eauto.
    eapply IHbs.
  Qed.
  
  Lemma dedup_lift7_2_6 bs :
    forall T A1 A2 A3 A4 A5 A6 f a1 a2 a3 a4 a5 a6,
      lift7 bs f a1 a2 a3 a4 a5 a2 a6 = lift6 bs (fun (a1 : A1) (a2 : A2) (a3 : A3) (a4 : A4) (a5 : A5) (a6 : A6) => f a1 a2 a3 a4 a5 a2 a6 : T) a1 a2 a3 a4 a5 a6.
  Proof.
    induct bs; simplify; eauto.
    eapply IHbs.
  Qed.
  
  Definition swap {A B C} (f : A -> B -> C) b a := f a b.
  
  Lemma swap_lift2 bs :
    forall T A1 A2 (f : A1 -> A2 -> T) a1 a2,
      lift2 bs f a1 a2 = lift2 bs (swap f) a2 a1.
  Proof.
    induct bs; simplify; eauto.
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
  
  Lemma swap_lift3_2_3_b :
    forall bs T A1 A2 A3 (f1 : A1 -> A2 -> A3 -> T) a1 a2 a3,
      lift3 bs f1 a1 a2 a3 = lift3 bs (fun a1 a2 a3 => f1 a1 a3 a2) a1 a3 a2.
  Proof.
    intros; eapply swap_lift3_2_3; eauto.
  Qed.
  
  Lemma swap_lift4_1_3 :
    forall bs T A1 A2 A3 A4 (f1 : A1 -> A2 -> A3 -> A4 -> T) a1 a2 a3 a4,
      lift4 bs f1 a1 a2 a3 a4 = lift4 bs (fun a3 a2 a1 a4 => f1 a1 a2 a3 a4) a3 a2 a1 a4.
  Proof.
    induct bs; simpl; intros; eauto.
  Qed.
  
  Lemma swap_lift4_1_3_b :
    forall bs T A1 A2 A3 A4 (f1 : _ -> _ -> _ -> _ -> T) (f2 : _ -> _ -> _ -> _ -> T) a1 a2 a3 a4,
      (forall (a1 : A1) (a2 : A2) (a3 : A3) (a4 : A4), f1 a1 a2 a3 a4 = f2 a3 a2 a1 a4) ->
      lift4 bs f1 a1 a2 a3 a4 = lift4 bs f2 a3 a2 a1 a4.
  Proof.
    induct bs; simpl; intros; eauto.
    eapply IHbs.
    intros.
    eapply FunctionalExtensionality.functional_extensionality.
    eauto.
  Qed.
  
  Lemma swap_lift4_2_4 :
    forall bs T A1 A2 A3 A4 (f1 : A1 -> A2 -> A3 -> A4 -> T) a1 a2 a3 a4,
      lift4 bs f1 a1 a2 a3 a4 = lift4 bs (fun a1 a4 a3 a2 => f1 a1 a2 a3 a4) a1 a4 a3 a2.
  Proof.
    induct bs; simpl; intros; eauto.
  Qed.
  
  Lemma swap_lift4_2_4_b :
    forall bs T A1 A2 A3 A4 (f1 : _ -> _ -> _ -> _ -> T) (f2 : _ -> _ -> _ -> _ -> T) a1 a2 a3 a4,
      (forall (a1 : A1) (a2 : A2) (a3 : A3) (a4 : A4), f1 a1 a2 a3 a4 = f2 a1 a4 a3 a2) ->
      lift4 bs f1 a1 a2 a3 a4 = lift4 bs f2 a1 a4 a3 a2.
  Proof.
    induct bs; simpl; intros; eauto.
    eapply IHbs.
    intros.
    eapply FunctionalExtensionality.functional_extensionality.
    eauto.
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
  
  Ltac dis := discriminate.
  
  Definition bsort_dec : forall (b b' : bsort), sumbool (b = b') (b <> b').
  Proof.
    induction b; destruct b'; simpl; try solve [left; f_equal; eauto | right; intro Heq; dis].
    destruct (IHb1 b'1); destruct (IHb2 b'2); subst; simplify; try solve [left; f_equal; eauto | right; intro Heq; invert Heq; subst; eauto].
  Defined.
  
  Definition convert_bsort_value k1 k2 : interp_bsort k1 -> interp_bsort k2.
  Proof.
    cases (bsort_dec k1 k2); subst; eauto.
    intros.
    eapply bsort_default_value.
  Defined.
  
  Fixpoint interp_var (x : var) arg_bs ret_b {struct arg_bs} : interp_bsorts arg_bs (interp_bsort ret_b) :=
    match arg_bs return interp_bsorts arg_bs (interp_bsort ret_b) with
    | [] => bsort_default_value ret_b
    | arg_b :: arg_bs =>
      match x with
      | 0 => lift0 arg_bs (convert_bsort_value arg_b ret_b)
      | S x => lift1 arg_bs (fun (x : interp_bsort ret_b) (_ : interp_bsort arg_b) => x) (interp_var x arg_bs ret_b)
      end
    end.

  Definition interp_iunop opr : interp_bsort (iunop_arg_bsort opr) -> interp_bsort (iunop_result_bsort opr) :=
    match opr with
    | IUBoolNeg => negb
    end.

  Definition interp_ibinop opr : interp_bsort (ibinop_arg1_bsort opr) -> interp_bsort (ibinop_arg2_bsort opr) -> interp_bsort (ibinop_result_bsort opr) :=
    match opr with
    | IBTimeAdd => TimeAdd
    | IBTimeMinus => TimeMinus
    | IBTimeMax => TimeMax
    | IBNatAdd => plus
    end.

  Definition ite {A} (x : bool) (x1 x2 : A) := if x then x1 else x2.

  Definition interp_iconst cn arg_ks res_k : interp_bsorts arg_ks (interp_bsort res_k) :=
    match cn with
    | ICTime cn => lift0 arg_ks (convert_bsort_value BSTime res_k cn)
    | ICNat cn => lift0 arg_ks (convert_bsort_value BSNat res_k cn)
    | ICBool cn => lift0 arg_ks (convert_bsort_value BSBool res_k cn)
    | ICTT => lift0 arg_ks (convert_bsort_value BSUnit res_k tt)
    end.

  Definition apply {A B} (f : A -> B) x := f x.
  Arguments apply {_ _} _ _ / .

  Fixpoint interp_idx c arg_ks res_k : interp_bsorts arg_ks (interp_bsort res_k) :=
    match c with
    | IVar x => interp_var x arg_ks res_k
    | IConst cn => interp_iconst cn arg_ks res_k 
    | IUnOp opr c =>
      let f x := convert_bsort_value (iunop_result_bsort opr) res_k (interp_iunop opr x) in
      lift1 arg_ks f (interp_idx c arg_ks (iunop_arg_bsort opr))
    | IBinOp opr c1 c2 =>
      let f x1 x2 := convert_bsort_value (ibinop_result_bsort opr) res_k (interp_ibinop opr x1 x2) in
      lift2 arg_ks f (interp_idx c1 arg_ks (ibinop_arg1_bsort opr)) (interp_idx c2 arg_ks (ibinop_arg2_bsort opr))
    | IIte c c1 c2 =>
      lift3 arg_ks ite (interp_idx c arg_ks BSBool) (interp_idx c1 arg_ks res_k) (interp_idx c2 arg_ks res_k)
    | IAbs c =>
      match res_k return interp_bsorts arg_ks (interp_bsort res_k) with
      | BSArrow b1 b2 =>
        interp_idx c (b1 :: arg_ks) b2
      | res_k => lift0 arg_ks (bsort_default_value res_k)
      end
    | IApp b c1 c2 => 
      lift2 arg_ks apply (interp_idx c1 arg_ks (BSArrow b res_k)) (interp_idx c2 arg_ks b)
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

  Fixpoint to_time_fun {n} : interp_bsort (BSTimeFun n) -> time_fun time_type n :=
    match n with
    | 0 => id
    | S n' => fun f x => @to_time_fun n' (f x)
    end.
  
  Definition interp_binpred opr : interp_bsort (binpred_arg1_bsort opr) -> interp_bsort (binpred_arg2_bsort opr) -> Prop :=
    match opr return interp_bsort (binpred_arg1_bsort opr) -> interp_bsort (binpred_arg2_bsort opr) -> Prop with
    | PBTimeLe => TimeLe
    | PBNatLt => lt
    (* | PBTimeEq => eq *)
    | PBBigO n => fun f g => Time_BigO n (to_time_fun f) (to_time_fun g)
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
  
  Definition sctx := list sort.
  
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
  | WsciAbs L i :
      wellscoped_i (1 + L) i ->
      wellscoped_i L (IAbs i) 
  | WsciApp L c1 c2 n :
      wellscoped_i L c1 ->
      wellscoped_i L c2 ->
      wellscoped_i L (IApp n c1 c2) 
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
      (forall x, f (convert_bsort_value a b x) (convert x)) ->
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
               (shift0 bs_new (a :: bs) (lift0 bs (convert_bsort_value a b)))).
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
  
  Require FunctionalExtensionality.
  
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
  
  Lemma forall_shift_i_i_eq_shift :
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
      cases b; 
        try solve [
              rewrite <- lift0_shift;
              rewrite fuse_lift2_lift0_1;
              rewrite fuse_lift1_lift0;
              eapply forall_lift0; eauto
            ].
      specialize (IHi bs_new (S x) (b1 :: bs) b2 (length bs_new)).
      simpl in *.
      rewrite fuse_lift1_lift2 in *.
      eapply forall_lift2_lift2; [ | eapply IHi; eauto].
      simpl; intros.
      eapply FunctionalExtensionality.functional_extensionality.
      eauto.
    }
    {
      simpl.
      rewrite fuse_lift2_lift2_1.
      rewrite <- lift2_shift.
      rewrite fuse_lift3_lift2_3.
      specialize (IHi1 bs_new x bs (BSArrow arg_bsort b) (length bs_new)).
      specialize (IHi2 bs_new x bs arg_bsort (length bs_new)).
      eapply forall_lift2_lift2_lift4; eauto.
      simpl; intros; subst.
      simpl; propositional.
    }
  Qed.

  Lemma interp_shift_i_i_eq_shift :
    forall i bs_new x bs b n,
      let bs' := insert bs_new x bs in
      wellscoped_i (length bs) i ->
      n = length bs_new ->
      interp_idx (shift_i_i n x i) bs' b = shift bs_new x bs (interp_idx i bs b).
  Proof.
    simpl.
    intros.
    eapply forall_eq_eq; eapply forall_shift_i_i_eq_shift; eauto.
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
      eapply forall_lift2_lift2_lift4; try eapply forall_shift_i_i_eq_shift; eauto.
      intros; subst.
      propositional.
    }
    {
      rewrite fuse_lift2_lift2_1.
      rewrite <- lift2_shift.
      rewrite fuse_lift3_lift2_3.
      eapply forall_lift2_lift2_lift4; try eapply forall_shift_i_i_eq_shift; eauto.
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

  Lemma length_shift_i_ss bs :
    forall v,
      length (shift_i_ss v bs) = length bs.
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
      rewrite nth_error_nil in *; dis.
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

  Lemma interp_prop_shift_i_p_original_proof L p :
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

  Definition imply_ bs x y := forall_ bs (lift2 bs imply x y).
  
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
    (* Qed triggers this Coq bug that has been reported to Coq development team's issue tracker: *)
    (* Qed. *)
    (* "Anomaly: conversion was given ill-typed terms (FProd). Please report." *)
  Admitted.

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
    (* Qed triggers this Coq bug that has been reported to Coq development team's issue tracker: *)
    (* Qed. *)
    (* "Anomaly: conversion was given ill-typed terms (FProd). Please report." *)
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

  Fixpoint subst x bs b_v B {struct bs} : interp_bsorts (skipn (S x) bs) (interp_bsort b_v) -> interp_bsorts bs B -> interp_bsorts (removen x bs) B :=
    match bs return interp_bsorts (skipn (S x) bs) (interp_bsort b_v) -> interp_bsorts bs B -> interp_bsorts (removen x bs) B with
    | [] => fun v body => body
    | b :: bs' =>
      match x return interp_bsorts (skipn (S x) (b :: bs')) (interp_bsort b_v) -> interp_bsorts (b :: bs') B -> interp_bsorts (removen x (b :: bs')) B with
      | 0 => fun v body => lift2 bs' (fun body v => body (convert_bsort_value b_v b v)) body v
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
      intros; dis.
    }
    {
      intros; dis.
    }
    {
      congruence.
    }
    {
      congruence.
    }
  Defined.

  Arguments cast bs1 bs2 {T} Heq v .

  Lemma cast_lift1 :
    forall bs1 bs2 A T (f : A -> T) (a : interp_bsorts bs1 A) (Heq : bs1 = bs2),
      cast bs1 bs2 Heq (lift1 bs1 f a) = lift1 bs2 f (cast bs1 bs2 Heq a).
  Proof.
    induct bs1; destruct bs2; simpl; intros; eauto; try dis.
    rewrite fuse_lift1_lift1.
    rewrite IHbs1.
    rewrite fuse_lift1_lift1.
    eauto.
  Qed.

  Lemma cast_lift2 :
    forall bs1 bs2 A1 A2 T (f : A1 -> A2 -> T) a1 a2 (Heq : bs1 = bs2),
      cast bs1 bs2 Heq (lift2 bs1 f a1 a2) = lift2 bs2 f (cast bs1 bs2 Heq a1) (cast bs1 bs2 Heq a2).
  Proof.
    induct bs1; destruct bs2; simpl; intros; eauto; try dis.
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
    induct bs1; destruct bs2; simpl; intros p Heq Hp; eauto; try dis.
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
    induct bs1; destruct bs2; simpl; intros p Heq Hp; eauto; try dis.
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
    induct bs1; destruct bs2; simpl; intros; eauto; try dis.
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

  Lemma convert_bsort_value_refl_eq :
    forall b v, convert_bsort_value b b v = v.
  Proof.
    intros.
    unfold convert_bsort_value.
    cases (bsort_dec b b); propositional.
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
           bs' (fun a1 a2 => f (convert_bsort_value b_v b a1) a2)
           (cast _ _ Heq (shift0 (firstn x bs) (skipn (S x) bs) v))
           (subst x bs v (interp_var x bs b))).
  Proof.
    simpl.
    induct bs; simpl; intros x b f b_v v Heq Hx Hf; try la.
    {
      rewrite nth_error_nil in *.
      dis.
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
      rewrite convert_bsort_value_refl_eq.
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
           bs' (fun a1 a2 => f (convert_bsort_value b_v b a1) a2)
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
           (lift1 _ (convert_bsort_value b_v b) (cast _ _ Heq (shift0 (firstn x bs) (skipn (S x) bs) v)))
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
    rewrite convert_bsort_value_refl_eq.
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
           (lift1 _ (convert_bsort_value b_v b) (shift0 (firstn x bs) (skipn (S x) bs) v))
           (cast _ _ Heq (subst x bs v (interp_var x bs b)))).
  Proof.
    intros.
    rewrite fuse_lift2_lift1_1.
    eapply forall_interp_var_eq_subst_eq_2'; eauto.
  Qed.
  
  Lemma convert_bsort_value_bsort_default_value b1 b2 :
    convert_bsort_value b1 b2 (bsort_default_value b1) = bsort_default_value b2.
  Proof.
    unfold convert_bsort_value.
    cases (bsort_dec b1 b2); subst; eauto.
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
  | BStgAbs L i b1 b2 :
      bsorting (b1 :: L) i b2 ->
      bsorting L (IAbs i) (BSArrow b1 b2)
  | BStgApp L c1 c2 b1 b2 :
      bsorting L c1 (BSArrow b1 b2) ->
      bsorting L c2 b1 ->
      bsorting L (IApp b1 c1 c2) b2
  .

  Hint Constructors bsorting.
  
  Inductive wfprop1 : list bsort -> prop -> Prop :=
  | BWfPropTrueFalse L cn :
      wfprop1 L (PTrueFalse cn)
  | BWfPropBinConn L opr p1 p2 :
      wfprop1 L p1 ->
      wfprop1 L p2 ->
      wfprop1 L (PBinConn opr p1 p2)
  | BWfPropNot L p :
      wfprop1 L p ->
      wfprop1 L (PNot p)
  | BWfPropBinPred L opr i1 i2 :
      bsorting L i1 (binpred_arg1_bsort opr) ->
      bsorting L i2 (binpred_arg2_bsort opr) ->
      wfprop1 L (PBinPred opr i1 i2)
  | BWfPropEq L b i1 i2 :
      bsorting L i1 b ->
      bsorting L i2 b ->
      wfprop1 L (PEq b i1 i2)
  | BWfPropQuan L q s p :
      wfprop1 (s :: L) p ->
      wfprop1 L (PQuan q s p)
  .
  
  Hint Constructors wfprop1.

  Lemma bsorting_wellscoped_i L i s :
    bsorting L i s ->
    wellscoped_i (length L) i.
  Proof.
    induct 1; simpl; eauto.
    econstructor.
    eapply nth_error_Some_lt; eauto.
  Qed.

  Lemma wfprop1_wellscoped_p L p :
    wfprop1 L p ->
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
    induct 1; intros; try dis.
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
      (* Case Abs *)
      econstructor; eauto.
      {
        eapply IHbsorting with (x := S x); eauto with db_la.
      }
    }
  Qed.

  Lemma wfprop1_shift_i_p :
    forall L p,
      wfprop1 L p ->
      forall x ls,
        let n := length ls in
        x <= length L ->
        wfprop1 (firstn x L ++ ls ++ my_skipn L x) (shift_i_p n x p).
  Proof.
    simpl.
    induct 1;
      simpl; intros x ls Hx; cbn in *; try solve [econstructor; eauto using bsorting_shift_i_i].
    econstructor.
    eapply IHwfprop1 with (x := S x); eauto with db_la.
  Qed.
  
  Lemma wfprop1_shift_i_p_1_0 L p s :
    wfprop1 L p ->
    wfprop1 (s :: L) (shift_i_p 1 0 p).
  Proof.
    intros Hp.
    eapply wfprop1_shift_i_p with (x := 0) (ls := [s]) in Hp; eauto with db_la.
    simpl in *.
    rewrite my_skipn_0 in *.
    eauto.
  Qed.
  
  Inductive wfsort1 : list bsort -> sort -> Prop :=
  | BWfStBaseSort L b :
      wfsort1 L (SBaseSort b)
  | BWfStSubset L b p :
      wfprop1 (b :: L) p ->
      wfsort1 L (SSubset b p)
  .

  Hint Constructors wfsort1.

  Definition wfsorts1 := all_sorts (fun L s => wfsort1 (map get_bsort L) s).

  Lemma wfsorts1_wfprop1_strip_subsets L :
    wfsorts1 L ->
    forall n,
      n = length L ->
      wfprop1 (map get_bsort L) (and_all (strip_subsets L)).
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
      eapply wfprop1_shift_i_p_1_0; eauto.
    }
    {
      unfold shift0_i_p.
      rewrite and_all_map_shift_i_p.
      econstructor; eauto.
      eapply wfprop1_shift_i_p_1_0; eauto.
    }
  Qed.

  Lemma nth_error_split_firstn_skipn A :
    forall (ls : list A) n a,
      nth_error ls n = Some a ->
      ls = firstn n ls ++ a :: skipn (S n) ls.
  Proof.
    induct ls; destruct n; simpl; intros; f_equal; eauto; try dis.
    congruence.
  Qed.      

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

  Lemma forall_imply_refl bs p :
    imply_ bs p p.
  Proof.
    eapply forall_iff_imply.
    eapply forall_iff_refl.
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
    induct n; destruct L; simpl; intros s' H Hnth; try dis; invert H; eauto.
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
      (* Case Abs *)
      destruct i'; simpl in *; try cases_le_dec; try dis.
      invert Hi; eauto.
      econstructor; eauto.
      eapply IHbsorting with (L4 := _ :: _); eauto with db_la.
      eauto.
    }
  Qed.

  Lemma wfprop1_shift_i_p_rev :
    forall L p,
      wfprop1 L p ->
      forall n x p' L1 L2 L3,
        p = shift_i_p n x p' ->
        L = L1 ++ L2 ++ L3 ->
        x = length L1 ->
        n = length L2 ->
        wfprop1 (L1 ++ L3) p'.
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
    eapply IHwfprop1 with (L4 := _ :: _); eauto with db_la.
    eauto.
  Qed.    
  
  Lemma my_skipn_my_skipn A :
    forall (ls : list A) n2 n1,
      my_skipn (my_skipn ls n2) n1 = my_skipn ls (n2 + n1).
  Proof.
    induct ls; destruct n2; simpl; eauto.
  Qed.

  Lemma wfsort1_wellscoped_s L s :
    wfsort1 L s ->
    wellscoped_s (length L) s.
  Proof.
    induct 1; simpl; econstructor; eauto.
    eapply wfprop1_wellscoped_p in H.
    eauto.
  Qed.
  
  Lemma wfsorts1_wellscoped_ss L :
    wfsorts1 L ->
    wellscoped_ss L.
  Proof.
    induct 1; simpl; intros; econstructor; eauto using wfsort1_wellscoped_s.
    eapply wfsort1_wellscoped_s in H0.
    rewrite map_length in *.
    eauto.
  Qed.

  Lemma forall_imply_shift_i_p_1_1_var0 b bs' bs p :
    wellscoped_p (1 + length bs') p ->
    bs = b :: bs' ->
    imply_ bs (interp_p bs p) (lift2 bs (fun body v => body (convert_bsort_value b b v)) (interp_p (b :: bs) (shift_i_p 1 1 p)) (interp_var 0 bs b)).
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
    repeat rewrite convert_bsort_value_refl_eq.
    specialize (H a0 a0).
    propositional.
    (* Qed triggers this Coq bug that has been reported to Coq development team's issue tracker: *)
    (* Qed. *)
    (* "Anomaly: conversion was given ill-typed terms (FProd). Please report." *)
  Admitted.

End TiML.   
