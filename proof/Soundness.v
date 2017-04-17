(* Coq Formalization of the TiML language and its Soundness *)

Set Implicit Arguments.

(* TiML is parametrized on the choice of the definition of "time" *)

Module Type TIME.
  
  Parameter time_type : Set.
  (* the const 0 *)
  Parameter Time0 : time_type.
  (* the const 1 *)
  Parameter Time1 : time_type.
  Parameter TimeAdd : time_type -> time_type -> time_type.
  (* 'minus' is bounded below by zero *)
  Parameter TimeMinus : time_type -> time_type -> time_type.
  (* less-than-or-equal-to *)
  Parameter TimeLe : time_type -> time_type -> Prop.
  Parameter TimeMax : time_type -> time_type -> time_type.
  
  Delimit Scope time_scope with time.
  Notation "0" := Time0 : time_scope.
  Notation "1" := Time1 : time_scope.
  Infix "+" := TimeAdd : time_scope.
  Infix "-" := TimeMinus : time_scope.
  Infix "<=" := TimeLe : time_scope.

  (* Requirements of 'time' imposed by TiML's soundness proof *)

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

(* 'BigO' is just a binary relation between two time functions. We do not use any of its properties in TiML's soundness proof *)

Module Type BIG_O (Time : TIME).

  (* a n-arith time function is a function from n natural numbers to time *)
  Fixpoint time_fun time_type (arity : nat) :=
    match arity with
    | 0 => time_type
    | S n => nat -> time_fun time_type n
    end.

  (* the bigO relation is parametrized on the arity *)
  Parameter Time_BigO : forall arity : nat, time_fun Time.time_type arity -> time_fun Time.time_type arity -> Prop.
  
End BIG_O.

(* a utility library *)
Require Import Util.

(* Nonnegative real numbers are a candidate instantiation for TIME *)

Module NNRealTime <: TIME.

  Require Import RIneq.
  Local Open Scope R_scope.
  Require Import Fourier.
  
  Ltac cases_ltle :=
    match goal with
      |- context [Rlt_le_dec ?a ?b] => cases (Rlt_le_dec a b)
    end.

  Definition Rlt_le_bool (a b : R) : bool.
    destruct (Rlt_le_dec a b).
    {
      exact true.
    }
    {
      exact false.
    }
  Defined.

  Record nnreal :=
    {
      nonneg : R;
      proof : Rlt_le_bool nonneg 0 = false
    }.

  Definition Rle_Rlt_le_bool a : 0 <= a -> Rlt_le_bool a 0 = false.
  Proof.
    intros H.
    unfold Rlt_le_bool.
    cases_ltle; try fourier.
    eauto.
  Qed.
  
  Definition mknonnegreal (a : R) (H : 0 <= a) : nnreal.
  Proof.
    refine (Build_nnreal a _).
    eapply Rle_Rlt_le_bool; eapply H.
  Defined.

  Ltac dis := discriminate.
  
  Lemma false_UIP (H1 H2 : false = false) : H1 = H2.
  Proof.
    Require Eqdep.
    eapply Eqdep.EqdepTheory.UIP.
  Qed.
  
  Lemma nonneg_eq_eq (a b : nnreal) : nonneg a = nonneg b -> a = b.
  Proof.
    intros H.
    destruct a as (a & Ha).
    destruct b as (b & Hb).
    simpl in *.
    subst.
    assert (Ha = Hb).
    {
      cases (Rlt_le_bool b 0); try dis.
      eapply false_UIP.
    }
    subst.
    eauto.
  Qed.
  
  (* Definition nnreal := nonnegreal. *)
  
  Definition time_type := nnreal.

  Arguments mknonnegreal : clear implicits.
  Arguments mknonnegreal _ _ / .
  
  Definition Time0 : time_type.
    refine (mknonnegreal 0 _).
    fourier.
  Defined.
  
  Definition Time1 : time_type.
    refine (mknonnegreal 1 _).
    eapply Rle_0_1.
  Defined.
  
  Ltac cases_ltle_hyps :=
    match goal with
      H : context [Rlt_le_dec ?a ?b] |- _  => cases (Rlt_le_dec a b)
    end.

  Definition Rlt_le_bool_Rle a : Rlt_le_bool a 0 = false -> 0 <= a.
  Proof.
    intros H.
    unfold Rlt_le_bool in *.
    cases_ltle_hyps; try fourier.
    try dis.
  Qed.

  Ltac les :=
    repeat match goal with
             H : _  |- _ => eapply Rlt_le_bool_Rle in H
           end.
  
  Definition TimeAdd (a b : time_type) : time_type.
    refine (mknonnegreal (nonneg a + nonneg b) _).
    destruct a as (a & Ha).
    destruct b as (b & Hb).
    simpl.
    les.
    fourier.
  Defined.
  
  Definition TimeMinus (a b : time_type) : time_type.
    destruct (Rlt_le_dec (nonneg a) (nonneg b)).
    {
      refine (mknonnegreal 0 _).
      destruct a as (a & Ha).
      destruct b as (b & Hb).
      simpl in *.
      les.
      fourier.
    }
    {
      refine (mknonnegreal (nonneg a - nonneg b) _).
      destruct a as (a & Ha).
      destruct b as (b & Hb).
      simpl in *.
      les.
      fourier.
    }
  Defined.
  
  Definition TimeLe (a b : time_type) : Prop.
    refine (Rle (nonneg a) (nonneg b)).
  Defined.
  
  Definition TimeMax (a b : time_type) : time_type.
    destruct (Rlt_le_dec (nonneg a) (nonneg b)).
    {
      refine (mknonnegreal (nonneg b) _).
      destruct a as (a & Ha).
      destruct b as (b & Hb).
      simpl in *.
      les.
      fourier.
    }
    {
      refine (mknonnegreal (nonneg a) _).
      destruct a as (a & Ha).
      destruct b as (b & Hb).
      simpl in *.
      les.
      fourier.
    }
  Defined.
  
  Delimit Scope time_scope with time.
  Notation "0" := Time0 : time_scope.
  Notation "1" := Time1 : time_scope.
  Infix "+" := TimeAdd : time_scope.
  Infix "-" := TimeMinus : time_scope.
  Infix "<=" := TimeLe : time_scope.

  Lemma Time_add_le_elim a b c :
    (a + b <= c -> a <= c /\ b <= c)%time.
  Proof.
    intros H.
    destruct a as (a & Ha).
    destruct b as (b & Hb).
    destruct c as (c & Hc).
    unfold TimeLe in *.
    simpl in *.
    les.
    split; fourier.
  Qed.

  Lemma Time_minus_move_left a b c :
    (c <= b ->
     a + c <= b ->
     a <= b - c)%time.
  Proof.
    intros H1 H2.
    unfold TimeLe in *.
    destruct a as (a & Ha).
    destruct b as (b & Hb).
    destruct c as (c & Hc).
    unfold TimeMinus in *.
    simpl in *.
    cases_ltle; simpl in *; les; fourier.
  Qed.

  Lemma Time_add_assoc a b c : (a + (b + c) = a + b + c)%time.
  Proof.
    destruct a as (a & Ha).
    destruct b as (b & Hb).
    destruct c as (c & Hc).
    unfold TimeAdd in *.
    simpl in *.
    eapply nonneg_eq_eq.
    simpl.
    les.
    ring.
  Qed.
  
  Lemma lhs_rotate a b c :
    (b + a <= c ->
     a + b <= c)%time.
  Proof.
    intros H.
    destruct a as (a & Ha).
    destruct b as (b & Hb).
    destruct c as (c & Hc).
    unfold TimeLe in *.
    simpl in *.
    les.
    fourier.
  Qed.

  Lemma Time_add_cancel a b c :
    (a <= b ->
     a + c <= b + c)%time.
  Proof.
    intros H.
    destruct a as (a & Ha).
    destruct b as (b & Hb).
    destruct c as (c & Hc).
    unfold TimeLe in *.
    simpl in *.
    les.
    fourier.
  Qed.

  Lemma rhs_rotate a b c :
    (a <= c + b->
     a <= b + c)%time.
  Proof.
    intros H.
    destruct a as (a & Ha).
    destruct b as (b & Hb).
    destruct c as (c & Hc).
    unfold TimeLe in *.
    simpl in *.
    les.
    fourier.
  Qed.

  Lemma Time_a_le_ba a b : (a <= b + a)%time.
  Proof.
    destruct a as (a & Ha).
    destruct b as (b & Hb).
    unfold TimeLe in *.
    simpl in *.
    les.
    fourier.
  Qed.

  Lemma Time_minus_cancel a b c :
    (a <= b -> a - c <= b - c)%time.
  Proof.
    intros H.
    destruct a as (a & Ha).
    destruct b as (b & Hb).
    destruct c as (c & Hc).
    unfold TimeLe in *.
    unfold TimeMinus in *.
    simpl in *.
    cases_ltle;
      cases_ltle;
      simpl in *;
      les;
      fourier.
  Qed.

  Lemma Time_a_minus_a a : (a - a = 0)%time.
  Proof.
    eapply nonneg_eq_eq.
    destruct a as (a & Ha).
    unfold TimeMinus in *.
    cases_ltle;
      simpl in *; les; ring.
  Qed.

  Lemma Time_0_le_x x : (0 <= x)%time.
  Proof.
    destruct x as (a & Ha).
    unfold TimeLe in *.
    simpl in *.
    les;
      fourier.
  Qed.

  Lemma Time_minus_0 x : (x - 0 = x)%time.
  Proof.
    eapply nonneg_eq_eq.
    destruct x as (a & Ha).
    unfold TimeMinus in *.
    simpl in *.
    cases_ltle;
      simpl in *;
      les; try ring.
    fourier.
  Qed.

  Lemma Time_0_add x : (0 + x = x)%time.
  Proof.
    eapply nonneg_eq_eq.
    destruct x as (a & Ha).
    simpl in *.
    ring.
  Qed.

  Lemma Time_le_refl x : (x <= x)%time.
  Proof.
    destruct x as (a & Ha).
    unfold TimeLe in *.
    simpl in *.
    fourier.
  Qed.

  Lemma Time_le_trans a b c :
    (a <= b -> b <= c -> a <= c)%time.
  Proof.
    intros H1 H2.
    destruct a as (a & Ha).
    destruct b as (b & Hb).
    destruct c as (c & Hc).
    unfold TimeLe in *.
    simpl in *.
    les.
    fourier.
  Qed.

  Lemma Time_add_cancel2 a b c d :
    (c <= d ->
     a <= b ->
     a + c <= b + d)%time.
  Proof.
    intros H1 H2.
    destruct a as (a & Ha).
    destruct b as (b & Hb).
    destruct c as (c & Hc).
    destruct d as (d & Hd).
    unfold TimeLe in *.
    simpl in *.
    les.
    fourier.
  Qed.

  Lemma Time_a_le_maxab a b : (a <= TimeMax a b)%time.
  Proof.
    destruct a as (a & Ha).
    destruct b as (b & Hb).
    unfold TimeLe in *.
    unfold TimeMax in *.
    simpl in *.
    cases_ltle; simpl in *;
      les;
      fourier.
  Qed.

  Lemma Time_b_le_maxab a b : (b <= TimeMax a b)%time.
  Proof.
    destruct a as (a & Ha).
    destruct b as (b & Hb).
    unfold TimeLe in *.
    unfold TimeMax in *.
    simpl in *.
    cases_ltle; simpl in *;
      les;
      fourier.
  Qed.

  Lemma Time_add_minus_assoc a b c :
    (c <= b -> a + (b - c) = a + b - c)%time.
  Proof.
    intros H1.
    eapply nonneg_eq_eq.
    destruct a as (a & Ha).
    destruct b as (b & Hb).
    destruct c as (c & Hc).
    unfold TimeLe in *.
    simpl in *.
    unfold TimeMinus in *.
    simpl in *.
    cases_ltle; simpl in *;
      cases_ltle; simpl in *;
      les;
      try fourier.
    ring.
  Qed.

  Lemma Time_minus_le a b : (a - b <= a)%time.
  Proof.
    destruct a as (a & Ha).
    destruct b as (b & Hb).
    unfold TimeLe in *.
    unfold TimeMinus in *.
    simpl in *.
    cases_ltle; simpl in *;
      les;
      fourier.
  Qed.

  Lemma Time_minus_add_cancel a b :
    (b <= a -> a - b + b = a)%time.
  Proof.
    intros H1.
    eapply nonneg_eq_eq.
    destruct a as (a & Ha).
    destruct b as (b & Hb).
    unfold TimeLe in *.
    simpl in *.
    unfold TimeMinus in *.
    simpl in *.
    cases_ltle; simpl in *;
      les;
      try fourier.
    ring.
  Qed.

  Lemma Time_minus_move_right a b c :
    (c <= a ->
     a <= b + c ->
     a - c <= b)%time.
  Proof.
    intros H1 H2.
    destruct a as (a & Ha).
    destruct b as (b & Hb).
    destruct c as (c & Hc).
    unfold TimeLe in *.
    simpl in *.
    unfold TimeMinus in *.
    simpl in *.
    cases_ltle; simpl in *;
      les;
      fourier.
  Qed.

  Lemma Time_le_add_minus a b c :
    (a + b - c <= a + (b - c))%time.
  Proof.
    destruct a as (a & Ha).
    destruct b as (b & Hb).
    destruct c as (c & Hc).
    unfold TimeLe in *.
    simpl in *.
    unfold TimeMinus in *.
    simpl in *.
    cases_ltle; simpl in *;
      cases_ltle; simpl in *;
      les;
      fourier.
  Qed.

  Lemma Time_add_comm a b : (a + b = b + a)%time.
  Proof.
    eapply nonneg_eq_eq.
    destruct a as (a & Ha).
    destruct b as (b & Hb).
    simpl in *.
    ring.
  Qed.

  Lemma Time_add_minus_cancel a b : (a + b - b = a)%time.
  Proof.
    eapply nonneg_eq_eq.
    destruct a as (a & Ha).
    destruct b as (b & Hb).
    simpl in *.
    unfold TimeMinus in *.
    simpl in *.
    cases_ltle; simpl in *;
      les;
      try fourier.
    ring.
  Qed.

  Lemma Time_minus_minus_cancel a b : (b <= a -> a - (a - b) = b)%time.
  Proof.
    intros H1.
    eapply nonneg_eq_eq.
    destruct a as (a & Ha).
    destruct b as (b & Hb).
    simpl in *.
    unfold TimeLe in *.
    simpl in *.
    unfold TimeMinus in *.
    simpl in *.
    cases_ltle; simpl in *;
      cases_ltle_hyps; simpl in *;
        les;
        try fourier.
    ring.
  Qed.

End NNRealTime.

(* Natural numbers are also a candidate instantiation for TIME, because we do not include real-number-only operations like logarithm and exponential in TiML's formalization *)

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

Require BinIntDef.

(* The TiML language, with the soundness theorem statement *)

(* TiML is parametrized on the choice of the definition of "time" and the "bigO" relation *)
Module Type TIML (Time : TIME) (BigO :BIG_O Time).
  
  Import Time BigO.

  (* ============================================================= *)
  (* The index language *)
  (* ============================================================= *)

  (* variable (just natural number because we use de Bruijn indices) *)
  Definition var := nat.

  (* index constants *)
  Inductive idx_const :=
  | ICTT
  | ICBool (b : bool)
  | ICNat (n : nat)
  | ICTime (r : time_type)
  .

  (* unary index operations *)
  Inductive idx_un_op :=
  | IUBoolNeg
  .

  (* binary index operations *)
  Inductive idx_bin_op :=
  | IBTimeAdd
  | IBTimeMinus
  | IBTimeMax
  | IBNatAdd
  .

  (* base sorts *)
  Inductive bsort :=
  | BSNat
  | BSUnit
  | BSBool
  | BSTime
  | BSArrow (b1 b2 : bsort)
  .

  (* index *)
  Inductive idx :=
  | IVar (x : var)
  | IConst (cn : idx_const)
  | IUnOp (opr : idx_un_op) (c : idx)
  | IBinOp (opr : idx_bin_op) (c1 c2 : idx)
  | IIte (i1 i2 i3 : idx)
  | IAbs (i : idx)
  | IApp (arg_bsort : bsort) (c1 c2 : idx)
  .

  (* binary logical connectives *)
  Inductive prop_bin_conn :=
  | PBCAnd
  | PBCOr
  | PBCImply
  | PBCIff
  .

  (* binary index predicates (i.e. relations) *)
  Inductive prop_bin_pred :=
  | PBTimeLe
  | PBNatLt
  | PBBigO (arity : nat)
  .

  (* quantifiers *)
  Inductive quan :=
  | QuanForall
  | QuanExists
  .

  (* propositions *)
  Inductive prop :=
  | PTrueFalse (b : bool)
  | PBinConn (opr : prop_bin_conn) (p1 p2 : prop)
  | PNot (p : prop)
  | PBinPred (opr : prop_bin_pred) (i1 i2 : idx)
  | PEq (b : bsort) (i1 i2 : idx) (* todo: why do we need a separate PEq? *)
  | PQuan (q : quan) (b : bsort) (p : prop)
  .

  (* sort: a sort is either a base sort or a refinement sort *)
  Inductive sort :=
  | SBaseSort (b : bsort)
  | SSubset (s : bsort) (p : prop)
  .

  (* ============================================================= *)
  (* the type language *)
  (* ============================================================= *)

  (* type constants *)
  Inductive ty_const :=
  | TCUnit
  | TCInt
  .

  (* binary type constructors *)
  Inductive ty_bin_op :=
  | TBProd
  | TBSum
  .

  (* kind *)
  Inductive kind :=
  | KType
  | KArrow (b : bsort) (k : kind)
  | KArrowT (k1 k2 : kind)
  .

  (* type *)
  Inductive ty :=
  | TVar (x : var)
  | TConst (cn : ty_const)
  | TBinOp (opr : ty_bin_op) (c1 c2 : ty)
  | TArrow (t1 : ty) (i : idx) (t2 : ty)
  | TAbs (s : bsort) (t : ty)
  | TApp (t : ty) (b : bsort) (i : idx)
  | TQuan (q : quan) (k : kind) (t : ty)
  | TQuanI (q : quan) (s : sort) (t : ty)
  | TRec (k : kind) (t : ty)
  | TNat (i : idx)
  | TArr (t : ty) (len : idx)
  | TAbsT (k : kind) (t : ty)
  | TAppT (t1 t2 : ty)
  .

  (* ============================================================= *)
  (* The term language *)
  (* ============================================================= *)
  
  Definition int := BinIntDef.Z.t.

  (* term constants *)
  Inductive expr_const :=
  | ECTT
  | ECInt (i : int)
  | ECNat (n : nat)
  .

  (* location *)
  Definition loc := nat.

  (* projector for product type *)
  Inductive projector :=
  | ProjFst
  | ProjSnd
  .

  (* injector for sum type *)
  Inductive injector :=
  | InjInl
  | InjInr
  .

  (* unary term operators *)
  Inductive expr_un_op :=
  | EUProj (p : projector)
  | EUInj (inj : injector)
  | EUFold
  | EUUnfold
  .

  (* primitive binary term operators *)
  Inductive prim_expr_bin_op :=
  | PEBIntAdd
  | PEBIntMult
  .

  (* binary term operators *)
  Inductive expr_bin_op :=
  | EBPrim (opr : prim_expr_bin_op)
  | EBApp
  | EBPair
  | EBNew 
  | EBRead 
  | EBNatAdd
  .

  (* term *)
  Inductive expr :=
  | EVar (x : var)
  | EConst (cn : expr_const)
  | ELoc (l : loc)
  | EUnOp (opr : expr_un_op) (e : expr)
  | EBinOp (opr : expr_bin_op) (e1 e2 : expr)
  | EWrite (e_arr e_idx e_val : expr)
  | ECase (e e1 e2 : expr)
  | EAbs (e : expr) (* annotation of the argument type is omitted *)
  | ERec (e : expr)
  | EAbsT (e : expr)
  | EAppT (e : expr) (t : ty)
  | EAbsI (e : expr)
  | EAppI (e : expr) (i : idx)
  | EPack (t : ty) (e : expr)
  | EUnpack (e1 e2 : expr)
  | EPackI (i : idx) (e : expr)
  | EUnpackI (e1 e2 : expr)
  .

  (* some shortcuts *)
  Definition EPair := EBinOp EBPair.
  Definition EInj c e := EUnOp (EUInj c) e.
  Definition EFold e := EUnOp EUFold e.
  
  (* ============================================================= *)
  (* Small-step fuel-augmented operational semantics *)
  (* ============================================================= *)

  (* 'value' defines when a term is a value *)
  Inductive value : expr -> Prop :=
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

  Definition heap := fmap loc (list expr).

  Definition fuel := time_type.

  (* configuration *)
  Definition config := (heap * expr * fuel)%type.

  Definition get_expr (s : config) : expr := snd (fst s).

  (* a configuration is finished if the program is a value *)
  Definition finished s := value (get_expr s).

  (* evaluation context (value constraints are put in the next 'plug' relation) *)
  Inductive ectx :=
  | ECHole
  | ECUnOp (opr : expr_un_op) (E : ectx)
  | ECBinOp1 (opr : expr_bin_op) (E : ectx) (e : expr)
  | ECBinOp2 (opr : expr_bin_op) (v : expr) (E : ectx)
  | ECWrite1 (E : ectx) (e2 e3 : expr)
  | ECWrite2 (v1 : expr) (E : ectx) (e3 : expr)
  | ECWrite3 (v1 v2 : expr) (E : ectx)
  | ECCase (E : ectx) (e1 e2 : expr)
  | ECAppT (E : ectx) (t : ty)
  | ECAppI (E : ectx) (i : idx)
  | ECPack (t : ty) (E : ectx)
  | ECUnpack (E : ectx) (e : expr)
  | ECPackI (i : idx) (E : ectx)
  | ECUnpackI (E : ectx) (e : expr)
  .

  (* the plug relation among E, e1 and e2 such that E[e1]=e2 *)
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
  | PlugWrite1 E e e' e2 e3 :
      plug E e e' ->
      plug (ECWrite1 E e2 e3) e (EWrite e' e2 e3)
  | PlugWrite2 E e e' v1 e3 :
      plug E e e' ->
      value v1 ->
      plug (ECWrite2 v1 E e3) e (EWrite v1 e' e3)
  | PlugWrite3 E e e' v1 v2 :
      plug E e e' ->
      value v1 ->
      value v2 ->
      plug (ECWrite3 v1 v2 E) e (EWrite v1 v2 e')
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

  Inductive LtEqGt (a b : nat) :=
    | MyLt : a < b -> LtEqGt a b
    | MyEq : a = b -> LtEqGt a b
    | MyGt : a > b -> LtEqGt a b
  .

  (* a decider for <, = and > *)
  Definition lt_eq_gt_dec a b : LtEqGt a b :=
    match lt_eq_lt_dec a b with
    | inleft (left H) => MyLt H
    | inleft (right H) => MyEq H
    | inright H => MyGt H
    end.
  
  Infix "<=>?" := lt_eq_gt_dec (at level 70).

  (* various versions of shift *)
  
  Section shift_i.

    (* the shifting amount *)
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

  Section shift_t.

    Variable n : nat.
  
    Fixpoint shift_i_t (x : var) (b : ty) : ty :=
      match b with
      | TVar y => TVar y
      | TConst cn => TConst cn
      | TBinOp opr c1 c2 => TBinOp opr (shift_i_t x c1) (shift_i_t x c2)
      | TArrow t1 i t2 => TArrow (shift_i_t x t1) (shift_i_i n x i) (shift_i_t x t2)
      | TAbs b t => TAbs b (shift_i_t (1 + x) t)
      | TApp t b i => TApp (shift_i_t x t) b (shift_i_i n x i)
      | TQuan q k c => TQuan q k (shift_i_t x c)
      | TQuanI q s c => TQuanI q (shift_i_s n x s) (shift_i_t (1 + x) c)
      | TRec k t => TRec k (shift_i_t x t)
      | TNat i => TNat (shift_i_i n x i)
      | TArr t i => TArr (shift_i_t x t) (shift_i_i n x i)
      | TAbsT k t => TAbsT k (shift_i_t x t)
      | TAppT t1 t2 => TAppT (shift_i_t x t1) (shift_i_t x t2)
      end.

    Fixpoint shift_t_t (x : var) (b : ty) : ty :=
      match b with
      | TVar y =>
        TVar (if x <=? y then
                n + y
              else
                y)
      | TConst cn => TConst cn
      | TBinOp opr c1 c2 => TBinOp opr (shift_t_t x c1) (shift_t_t x c2)
      | TArrow t1 i t2 => TArrow (shift_t_t x t1) i (shift_t_t x t2)
      | TAbs s t => TAbs s (shift_t_t x t)
      | TApp t b i => TApp (shift_t_t x t) b i
      | TQuan q k c => TQuan q k (shift_t_t (1 + x) c)
      | TQuanI q s c => TQuanI q s (shift_t_t x c)
      | TRec k t => TRec k (shift_t_t (1 + x) t)
      | TNat i => TNat i
      | TArr t i => TArr (shift_t_t x t) i
      | TAbsT k t => TAbsT k (shift_t_t (1 + x) t)
      | TAppT t1 t2 => TAppT (shift_t_t x t1) (shift_t_t x t2)
      end.
        
  End shift_t.
      
  Definition shift0_i_t := shift_i_t 1 0.
  Definition shift0_t_t := shift_t_t 1 0.
  
  Section shift_e.

    Variable n : nat.

    Fixpoint shift_i_e (x : var) (b : expr) : expr :=
      match b with
      | EVar y => EVar y
      | EConst cn => EConst cn
      | ELoc l => ELoc l
      | EUnOp opr e => EUnOp opr (shift_i_e x e)
      | EBinOp opr e1 e2 => EBinOp opr (shift_i_e x e1) (shift_i_e x e2)
      | EWrite e1 e2 e3 => EWrite (shift_i_e x e1) (shift_i_e x e2) (shift_i_e x e3)
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
      | EWrite e1 e2 e3 => EWrite (shift_t_e x e1) (shift_t_e x e2) (shift_t_e x e3)
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
      | EWrite e1 e2 e3 => EWrite (shift_e_e x e1) (shift_e_e x e2) (shift_e_e x e3)
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

  (* various versions of substitution *)
  
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
    | IAbs i => IAbs (subst_i_i (1 + x) (shift0_i_i v) i)
    | IApp n c1 c2 => IApp n (subst_i_i x v c1) (subst_i_i x v c2)
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
    | TBinOp opr c1 c2 => TBinOp opr (subst_i_t x v c1) (subst_i_t x v c2)
    | TArrow t1 i t2 => TArrow (subst_i_t x v t1) (subst_i_i x v i) (subst_i_t x v t2)
    | TAbs b t => TAbs b (subst_i_t (1 + x) (shift0_i_i v) t)
    | TApp t b i => TApp (subst_i_t x v t) b (subst_i_i x v i)
    | TQuan q k c => TQuan q k (subst_i_t x v c)
    | TQuanI q s c => TQuanI q (subst_i_s x v s) (subst_i_t (1 + x) (shift0_i_i v) c)
    | TRec k t => TRec k (subst_i_t x v t)
    | TNat i => TNat (subst_i_i x v i)
    | TArr t i => TArr (subst_i_t x v t) (subst_i_i x v i)
    | TAbsT k t => TAbsT k (subst_i_t x v t)
    | TAppT t1 t2 => TAppT (subst_i_t x v t1) (subst_i_t x v t2)
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
    | TBinOp opr c1 c2 => TBinOp opr (subst_t_t x v c1) (subst_t_t x v c2)
    | TArrow t1 i t2 => TArrow (subst_t_t x v t1) i (subst_t_t x v t2)
    | TAbs s t => TAbs s (subst_t_t x (shift0_i_t v) t)
    | TApp t b i => TApp (subst_t_t x v t) b i
    | TQuan q k c => TQuan q k (subst_t_t (1 + x) (shift0_t_t v) c)
    | TQuanI q s c => TQuanI q s (subst_t_t x (shift0_i_t v) c)
    | TRec k t => TRec k (subst_t_t (1 + x) (shift0_t_t v) t)
    | TNat i => TNat i
    | TArr t i => TArr (subst_t_t x v t) i
    | TAbsT k t => TAbsT k (subst_t_t (1 + x) (shift0_t_t v) t)
    | TAppT t1 t2 => TAppT (subst_t_t x v t1) (subst_t_t x v t2)
    end.
  
  Fixpoint subst_i_e (x : var) (v : idx) (b : expr) : expr :=
    match b with
    | EVar y => EVar y
    | EConst cn => EConst cn
    | ELoc l => ELoc l
    | EUnOp opr e => EUnOp opr (subst_i_e x v e)
    | EBinOp opr e1 e2 => EBinOp opr (subst_i_e x v e1) (subst_i_e x v e2)
    | EWrite e1 e2 e3 => EWrite (subst_i_e x v e1) (subst_i_e x v e2) (subst_i_e x v e3)
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
  
  Definition subst0_i_e (v : idx) b := subst_i_e 0 v b.
  
  Fixpoint subst_t_e (x : var) (v : ty) (b : expr) : expr :=
    match b with
    | EVar y => EVar y
    | EConst cn => EConst cn
    | ELoc l => ELoc l
    | EUnOp opr e => EUnOp opr (subst_t_e x v e)
    | EBinOp opr e1 e2 => EBinOp opr (subst_t_e x v e1) (subst_t_e x v e2)
    | EWrite e1 e2 e3 => EWrite (subst_t_e x v e1) (subst_t_e x v e2) (subst_t_e x v e3)
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

  Definition subst0_t_e (v : ty) b := subst_t_e 0 v b.
  
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
    | EWrite e1 e2 e3 => EWrite (subst_e_e x v e1) (subst_e_e x v e2) (subst_e_e x v e3)
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
  
  Definition subst0_e_e v b := subst_e_e 0 v b.

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

  (* some shortcuts *)
  Definition EApp := EBinOp EBApp.
  Definition EUnfold e := EUnOp EUUnfold e.
  Definition ENew e1 e2 := EBinOp EBNew e1 e2.
  Definition ERead e1 e2 := EBinOp EBRead e1 e2.
  Definition ENat n := EConst (ECNat n).
  Definition ETT := EConst ECTT.
  Definition EProj p e := EUnOp (EUProj p) e.
  Definition ENatAdd := EBinOp EBNatAdd.
  Definition EPrim opr := EBinOp (EBPrim opr).
  
  Definition upd {A} ls n (v : A) := insert [v] n (removen n ls).

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

  Notation int_add := BinIntDef.Z.add.
  Notation int_mult := BinIntDef.Z.mul.

  (* the interpreter of primitive binary term operations (note that operations can fail on illegal arguments) *)
  Definition exec_prim opr a b :=
    match (opr, a, b) with
    | (PEBIntAdd, ECInt a, ECInt b) => Some (ECInt (int_add a b))
    | (PEBIntMult, ECInt a, ECInt b) => Some (ECInt (int_mult a b))
    | _ => None
    end.

  (* the cost of primitive operations *)
  Definition prim_cost opr :=
    match opr with
    | PEBIntAdd => 0%time
    | PEBIntMult => 0%time
    end.

  (* the cost of natural time addition *)
  Definition nat_add_cost := 0%time.

  Import OpenScope.

  (* atomic step relation *)
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
  | ARead h l n t vs v :
      h $? l = Some vs ->
      nth_error vs n = Some v ->
      astep (h, ERead (ELoc l) (ENat n), t) (h, v, t)
  | AWrite h l n v t vs :
      value v ->
      h $? l = Some vs ->
      n < length vs ->
      astep (h, EWrite (ELoc l) (ENat n) v, t) (h $+ (l, upd vs n v), ETT, t)
  | ANew h v n t l :
      value v ->
      h $? l = None ->
      astep (h, ENew v (ENat n), t) (h $+ (l, repeat v n), ELoc l, t)
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
  | ANatAdd h n1 n2 t :
      nat_add_cost <= t ->
      astep (h, ENatAdd (ENat n1) (ENat n2), t) (h, ENat (n1 + n2), t - nat_add_cost)
  | APrim h opr cn1 cn2 t cn :
      prim_cost opr <= t ->
      exec_prim opr cn1 cn2 = Some cn ->
      astep (h, EPrim opr (EConst cn1) (EConst cn2), t) (h, EConst cn, t - prim_cost opr)
  .

  Import CloseScope.

  (* step relation *)
  Inductive step : config -> config -> Prop :=
  | StepPlug h e1 t h' e1' t' e e' E :
      astep (h, e, t) (h', e', t') ->
      plug E e e1 ->
      plug E e' e1' ->
      step (h, e1, t) (h', e1', t')
  .

  Definition unstuck s :=
    finished s \/
    exists s', step s s'.

  (* ============================================================= *)
  (* safety a.k.a. nonstuckness, which will be the goal of the main theorem *)
  (* ============================================================= *)

  (* R^* is the transitive closure of binary relation R *)
  Definition safe s := forall s', step^* s s' -> unstuck s'.

  (* ============================================================= *)
  (* Type system *)
  (* ============================================================= *)

  (* sorting context *)
  Definition sctx := list sort.
  (* kinding context *)
  Definition kctx := list kind.
  (* heap typing *)
  Definition hctx := fmap loc (ty * idx).
  (* typing context *)
  Definition tctx := list ty.
  (* the total context *)
  Definition ctx := (sctx * kctx * hctx * tctx)%type.

  (* sorts of index constants *)
  Definition const_bsort cn :=
    match cn with
    | ICTT => BSUnit
    | ICBool _ => BSBool
    | ICNat _ => BSNat
    | ICTime _ => BSTime
    end
  .

  (* sorts of unary index operators' arguments *)
  Definition iunop_arg_bsort opr :=
    match opr with
    | IUBoolNeg => BSBool
    end.

  (* sorts of unary index operators' results *)
  Definition iunop_result_bsort opr :=
    match opr with
    | IUBoolNeg => BSBool
    end.

  (* sorts of binary index operators' first arguments *)
  Definition ibinop_arg1_bsort opr :=
    match opr with
    | IBTimeAdd => BSTime
    | IBTimeMinus => BSTime
    | IBTimeMax => BSTime
    | IBNatAdd => BSNat
    end.

  (* sorts of binary index operators' second arguments *)
  Definition ibinop_arg2_bsort opr :=
    match opr with
    | IBTimeAdd => BSTime
    | IBTimeMinus => BSTime
    | IBTimeMax => BSTime
    | IBNatAdd => BSNat
    end.

  (* sorts of binary index operators' results *)
  Definition ibinop_result_bsort opr :=
    match opr with
    | IBTimeAdd => BSTime
    | IBTimeMinus => BSTime
    | IBTimeMax => BSTime
    | IBNatAdd => BSNat
    end.

  (* some shortcuts *)
  Definition SBool := SBaseSort BSBool.
  Definition SArrow b1 b2 := SBaseSort (BSArrow b1 b2).
  
  (* ------------------------------------------------------------- *)
  (* Denotational semantics for indices *)
  (* ------------------------------------------------------------- *)

  Definition get_bsort (s : sort) :=
    match s with
    | SBaseSort b => b
    | SSubset b _ => b
    end.

  (* some shortcuts *)
  Definition PTrue := PTrueFalse true.
  Definition PFalse := PTrueFalse false.
  Definition PAnd := PBinConn PBCAnd.
  Definition POr := PBinConn PBCOr.
  Definition PImply := PBinConn PBCImply.
  
  Delimit Scope idx_scope with idx.
  Infix "===>" := PImply (at level 95) : idx_scope.
  Infix "/\" := PAnd : idx_scope.
  
  Fixpoint and_all ps :=
    match ps with
    | [] => PTrue
    | p :: ps => (p /\ and_all ps) % idx
    end.

  (* interpretation of base sorts *)
  Fixpoint interp_bsort (b : bsort) :=
    match b with
    | BSNat => nat
    | BSUnit => unit
    | BSBool => bool
    | BSTime => time_type
    | BSArrow b1 b2 => interp_bsort b1 -> interp_bsort b2
    end.

  Fixpoint interp_bsorts arg_ks res :=
    match arg_ks with
    | [] => res
    | arg_k :: arg_ks => interp_bsorts arg_ks (interp_bsort arg_k -> res)
    end.

  (* interpretation of unary index operations *)
  Definition interp_iunop opr : interp_bsort (iunop_arg_bsort opr) -> interp_bsort (iunop_result_bsort opr) :=
    match opr with
    | IUBoolNeg => negb
    end.

  Definition interp_true_false_Prop (b : bool) := if b then True else False.

  Notation imply := (fun A B : Prop => A -> B).
  Definition ite {A} (x : bool) (x1 x2 : A) := if x then x1 else x2.
  Definition apply {A B} (f : A -> B) x := f x.

  (* interpretation of binary logical connectives *)
  Definition interp_binconn opr : Prop -> Prop -> Prop :=
    match opr with
    | PBCAnd => and
    | PBCOr => or
    | PBCImply => imply
    | PBCIff => iff
    end.

  Fixpoint BSTimeFun arity :=
    match arity with
    | 0 => BSTime
    | S n => BSArrow BSNat (BSTimeFun n)
    end.
  
  (* sorts of binary index predicates' first arguments *)
  Definition binpred_arg1_bsort opr :=
    match opr with
    | PBTimeLe => BSTime
    | PBNatLt => BSNat
    (* | PBTimeEq => BSTime *)
    | PBBigO n => BSTimeFun n
    end
  .

  (* sorts of binary index predicates' second arguments *)
  Definition binpred_arg2_bsort opr :=
    match opr with
    | PBTimeLe => BSTime
    | PBNatLt => BSNat
    (* | PBTimeEq => BSTime *)
    | PBBigO n => BSTimeFun n
    end
  .

  Fixpoint to_time_fun {n} : interp_bsort (BSTimeFun n) -> time_fun time_type n :=
    match n with
    | 0 => id
    | S n' => fun f x => @to_time_fun n' (f x)
    end.
  
  (* interpretation of binary index predicates *)
  Definition interp_binpred opr : interp_bsort (binpred_arg1_bsort opr) -> interp_bsort (binpred_arg2_bsort opr) -> Prop :=
    match opr return interp_bsort (binpred_arg1_bsort opr) -> interp_bsort (binpred_arg2_bsort opr) -> Prop with
    | PBTimeLe => TimeLe
    | PBNatLt => lt
    | PBBigO n => fun f g => Time_BigO n (to_time_fun f) (to_time_fun g)
    end.

  Definition interp_quan {A} q (P : A -> Prop) : Prop :=
    match q with
    | QuanForall => forall a, P a
    | QuanExists => exists a, P a
    end.

  (* The default value of base sorts. We define the interpreter of indices as a total function, so when encountering error, a default value will be returned. *)
  Fixpoint bsort_default_value (b : bsort) : interp_bsort b :=
    match b with
    | BSNat => 0%nat
    | BSUnit => tt
    | BSBool => false
    | BSTime => 0%time
    | BSArrow b1 b2 => fun _ => bsort_default_value b2
    end.

  (* a decider base sort equality *)
  Definition bsort_dec : forall (b b' : bsort), sumbool (b = b') (b <> b').
  Proof.
    induction b; destruct b'; simpl; try solve [left; f_equal; eauto | right; intro Heq; discriminate].
    destruct (IHb1 b'1); destruct (IHb2 b'2); subst; simplify; try solve [left; f_equal; eauto | right; intro Heq; invert Heq; subst; eauto].
  Defined.

  (* coercion between values of two sorts: if the sorts are equal, the coercion is identity; otherwise return a default value of the target sort *)
  Definition convert_bsort_value k1 k2 : interp_bsort k1 -> interp_bsort k2.
  Proof.
    cases (bsort_dec k1 k2); subst; eauto.
    intros.
    eapply bsort_default_value.
  Defined.

  (* lifting functions for dependent types (technical) *)
  
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

  (* interpretation of index constants *)  
  Definition interp_iconst cn arg_ks res_k : interp_bsorts arg_ks (interp_bsort res_k) :=
    match cn with
    | ICTime cn => lift0 arg_ks (convert_bsort_value BSTime res_k cn)
    | ICNat cn => lift0 arg_ks (convert_bsort_value BSNat res_k cn)
    | ICBool cn => lift0 arg_ks (convert_bsort_value BSBool res_k cn)
    | ICTT => lift0 arg_ks (convert_bsort_value BSUnit res_k tt)
    end.

  (* interpretation of index variable *)  
  Fixpoint interp_var (x : var) arg_bs ret_b {struct arg_bs} : interp_bsorts arg_bs (interp_bsort ret_b) :=
    match arg_bs return interp_bsorts arg_bs (interp_bsort ret_b) with
    | [] => bsort_default_value ret_b
    | arg_b :: arg_bs =>
      match x with
      | 0 => lift0 arg_bs (convert_bsort_value arg_b ret_b)
      | S x => lift1 arg_bs (fun (x : interp_bsort ret_b) (_ : interp_bsort arg_b) => x) (interp_var x arg_bs ret_b)
      end
    end.

  (* interpretation of binary index operations *)  
  Definition interp_ibinop opr : interp_bsort (ibinop_arg1_bsort opr) -> interp_bsort (ibinop_arg2_bsort opr) -> interp_bsort (ibinop_result_bsort opr) :=
    match opr with
    | IBTimeAdd => TimeAdd
    | IBTimeMinus => TimeMinus
    | IBTimeMax => TimeMax
    | IBNatAdd => plus
    end.

  (* ------------------------------------------------------------------ *)
  (* interpretation of indices (i.e. denotational semantics of indices) *)  
  (* ------------------------------------------------------------------ *)
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

  (* interpretation of propositions (auxiliary) *)  
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

  Definition for_all {A} (P : A -> Prop) : Prop := forall a, P a.
  
  Fixpoint forall_ arg_ks : interp_bsorts arg_ks Prop -> Prop :=
    match arg_ks with
    | [] => id
    | arg_k :: arg_ks => fun P => forall_ arg_ks (lift1 arg_ks for_all P)
    end.

  (* ------------------------------------------------------------------ *)
  (* interpretation of propositions *)
  (* ------------------------------------------------------------------ *)
  
  (* Refinements in context are collected and combined as a premise of the proposition. *)
  
  (* collect refinement predicates in refinement sorts *)
  Fixpoint strip_subset k :=
    match k with
    | SBaseSort b => []
    | SSubset b p => [p]
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

  (* interpretation of propositions *)
  Definition interp_prop (ss : sctx) (p : prop) : Prop :=
    let bs := map get_bsort ss in
    let ps := strip_subsets ss in
    let p := (and_all ps ===> p)%idx in
    let P := interp_p bs p in
    forall_ bs P.

  Definition subst0_i_p v b := subst_i_p 0 v b.

  (* the sorting judgment *)
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
  | StgAbs L i b1 b2 :
      sorting (SBaseSort b1 :: L) i (SBaseSort b2) ->
      sorting L (IAbs i) (SArrow b1 b2)
  | StgApp L c1 c2 b1 b2 :
      sorting L c1 (SArrow b1 b2) ->
      sorting L c2 (SBaseSort b1) ->
      sorting L (IApp b1 c1 c2) (SBaseSort b2)
  | StgSubsetI L c b p :
      sorting L c (SBaseSort b) ->
      interp_prop L (subst0_i_p c p) ->
      sorting L c (SSubset b p)
  | StgSubsetE L c b p :
      sorting L c (SSubset b p) ->
      wfprop (SBaseSort b :: L) p ->
      sorting L c (SBaseSort b)

  (* proposition wellformedness *)            
  with wfprop : list sort -> prop -> Prop :=
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

  (* sort wellformedness *)
  Inductive wfsort : list sort -> sort -> Prop :=
  | WfStBaseSort L b :
      wfsort L (SBaseSort b)
  | WfStSubset L b p :
      wfprop (SBaseSort b :: L) p ->
      wfsort L (SSubset b p)
  .

  (* some shortcuts *)
  Definition SNat := SBaseSort BSNat.
  Definition STime := SBaseSort BSTime.

  (* the kinding judgment *)
  Inductive kinding : sctx -> kctx -> ty -> kind -> Prop :=
  | KdgVar L K x k :
      nth_error K x = Some k ->
      kinding L K (TVar x) k
  | KdgConst L K cn :
      kinding L K (TConst cn) KType
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
  | KdgRec L K k c :
      kinding L (k :: K) c k ->
      kinding L K (TRec k c) k
  | KdgNat L K i :
      sorting L i SNat ->
      kinding L K (TNat i) KType
  | KdgArr L K t i :
      kinding L K t KType ->
      sorting L i SNat ->
      kinding L K (TArr t i) KType
  | KdgAbsT L K t k1 k2 :
      kinding L (k1 :: K) t k2 ->
      kinding L K (TAbsT k1 t) (KArrowT k1 k2)
  | KdgAppT L K t1 t2 k1 k2 :
      kinding L K t1 (KArrowT k1 k2) ->
      kinding L K t2 k1 ->
      kinding L K (TAppT t1 t2) k2
  .

  (* some shortcuts *)
  Notation Tconst r := (IConst (ICTime r)).
  Notation T0 := (Tconst Time0).
  Notation T1 := (Tconst Time1).

  Definition shift_i_ti n x b := (shift_i_t n x (fst b), shift_i_i n x (snd b)).
  Definition shift0_i_ti := shift_i_ti 1 0.
  Definition shift_t_ti n x (b : ty * idx) := (shift_t_t n x (fst b), snd b).
  Definition shift0_t_ti := shift_t_ti 1 0.
  
  (* manipulation of typing contexts *)
  
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

  Definition add_sorting_ctx s (C : ctx) : ctx :=
    match C with
      (L, K, W, G) => (s :: L, K, fmap_map shift0_i_ti W, map shift0_i_t G)
    end
  .

  Definition add_kinding_ctx k (C : ctx) :=
    match C with
      (L, K, W, G) => (L, k :: K, fmap_map shift0_t_ti W, map shift0_t_t G)
    end
  .

  Definition add_typing_ctx t (C : ctx) :=
    match C with
      (L, K, W, G) => (L, K, W, t :: G)
    end
  .

  (* some shortcuts *)
  Definition Tadd := IBinOp IBTimeAdd.
  
  Delimit Scope idx_scope with idx.
  Infix "+" := Tadd : idx_scope.
  
  Definition subst0_i_t v b := subst_i_t 0 v b.
  Definition subst0_t_t v b := subst_t_t 0 v b.
  
  Definition TUnit := TConst TCUnit.
  Definition TInt := TConst TCInt.
  Definition TProd := TBinOp TBProd.
  Definition TSum := TBinOp TBSum.
  Definition TForall := TQuan QuanForall.
  Definition TExists := TQuan QuanExists.
  Definition TForallI := TQuanI QuanForall.
  Definition TExistsI := TQuanI QuanExists.

  (* a term wrapped by a series of (type or index) polymorphisms *)
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

  (* a series of type applications *)
  Fixpoint TApps t args :=
    match args with
    | nil => t
    | (b, i) :: args => TApps (TApp t b i) args
    end.

  (* unrolling of a recursive type *)
  Definition unroll (k : kind) (t : ty) (args : list (bsort * idx)) : ty :=
    let r := subst0_t_t (TRec k t) t in
    TApps r args.

  (* types of term constants *)
  Definition const_type cn :=
    match cn with
    | ECTT => TUnit
    | ECInt _ => TInt
    | ECNat n => TNat (IConst (ICNat n))
    end
  .

  (* types of primitive binary term operators' first arguments *)
  Definition prim_arg1_type opr :=
    match opr with
    | PEBIntAdd => TInt
    | PEBIntMult => TInt
    end.
    
  (* types of primitive binary term operators' second arguments *)
  Definition prim_arg2_type opr :=
    match opr with
    | PEBIntAdd => TInt
    | PEBIntMult => TInt
    end.
    
  (* types of primitive binary term operators' results *)
  Definition prim_result_type opr :=
    match opr with
    | PEBIntAdd => TInt
    | PEBIntMult => TInt
    end.

  (* some shortcuts *)
  Definition Tmax := IBinOp IBTimeMax.
  
  Definition Nlt := PBinPred PBNatLt.
  Infix "<" := Nlt : idx_scope.
  
  Definition Tle := PBinPred PBTimeLe.
  Infix "<=" := Tle : idx_scope.
  
  Definition Nadd := IBinOp IBNatAdd.
  
  Local Open Scope idx_scope.

  (* index equality *)
  Notation idxeq L i i' b := (interp_prop L (PEq b i i')).
  
  Definition PIff := PBinConn PBCIff.
  Infix "<===>" := PIff (at level 95) : idx_scope.

  (* sort equality *)
  Inductive sorteq : sctx -> sort -> sort -> Prop :=
  | SortEqBaseSort L b :
      sorteq L (SBaseSort b) (SBaseSort b)
  | SortEqSubset L b p p' :
      interp_prop (SBaseSort b :: L) (p <===> p')%idx ->
      sorteq L (SSubset b p) (SSubset b p')
  .

  (* type equality *)
  Inductive tyeq : sctx -> kctx -> ty -> ty -> kind -> Prop :=
  (* congruence rules *)
  | TyEqBinOp L K opr t1 t2 t1' t2' :
      tyeq L K t1 t1' KType ->
      tyeq L K t2 t2' KType ->
      tyeq L K (TBinOp opr t1 t2) (TBinOp opr t1' t2') KType
  | TyEqArrow L K t1 i t2 t1' i' t2':
      tyeq L K t1 t1' KType ->
      idxeq L i i' BSTime ->
      tyeq L K t2 t2' KType ->
      tyeq L K (TArrow t1 i t2) (TArrow t1' i' t2') KType
  | TyEqAbs L K b t t' k :
      tyeq (SBaseSort b :: L) K t t' k ->
      tyeq L K (TAbs b t) (TAbs b t') (KArrow b k)
  | TyEqApp L K t b i t' i' k :
      tyeq L K t t' (KArrow b k) ->
      idxeq L i i' b ->
      tyeq L K (TApp t b i) (TApp t' b i') k
  | TyEqQuan L K quan k t t' :
      tyeq L (k :: K) t t' KType ->
      tyeq L K (TQuan quan k t) (TQuan quan k t') KType
  | TyEqQuanI L K quan s t s' t' :
      sorteq L s s' ->
      tyeq (s :: L) K t t' KType ->
      tyeq L K (TQuanI quan s t) (TQuanI quan s' t') KType
  | TyEqRec L K k c c' :
      tyeq L (k :: K) c c' k ->
      tyeq L K (TRec k c) (TRec k c') k
  | TyEqNat L K i i' :
      idxeq L i i' BSNat ->
      tyeq L K (TNat i) (TNat i') KType
  | TyEqArr L K t i t' i' :
      tyeq L K t t' KType ->
      idxeq L i i' BSNat ->
      tyeq L K (TArr t i) (TArr t' i') KType
  | TyEqAbsT L K k t t' k2 :
      tyeq L (k :: K) t t' k2 ->
      tyeq L K (TAbsT k t) (TAbsT k t') (KArrowT k k2)
  | TyEqAppT L K t1 t2 t1' t2' k1 k2 :
      tyeq L K t1 t1' (KArrowT k1 k2) ->
      tyeq L K t2 t2' k1 ->
      tyeq L K (TAppT t1 t2) (TAppT t1' t2') k2
  | TyEqVar L K x k :
      nth_error K x = Some k ->
      tyeq L K (TVar x) (TVar x) k
  | TyEqConst L K cn :
      tyeq L K (TConst cn) (TConst cn) KType
  (* reduction rules *)
  | TyEqBeta L K s t b i k :
      kinding L K (TApp (TAbs s t) b i) k ->
      tyeq L K (TApp (TAbs s t) b i) (subst0_i_t i t) k
  | TyEqBetaT L K k t1 t2 k2 :
      kinding L K (TAppT (TAbsT k t1) t2) k2 ->
      tyeq L K (TAppT (TAbsT k t1) t2) (subst0_t_t t2 t1) k2
  (* equivalence rules *)
  | TyEqRefl L K t k :
      kinding L K t k ->
      tyeq L K t t k
  | TyEqSym L K a b k :
      tyeq L K a b k ->
      tyeq L K b a k
  | TyEqTrans L K a b c k :
      tyeq L K a b k ->
      tyeq L K b c k ->
      kinding L K b k ->
      tyeq L K a c k
  .

  (* the typing judgment *)
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
  | TyRec C tis e1 t :
      let e := EAbsTIs tis (EAbs e1) in
      kinding (get_sctx C) (get_kctx C) t KType ->
      typing (add_typing_ctx t C) e t T0 ->
      typing C (ERec e) t T0
  | TyFold C e k t cs i :
      let t_rec := TApps (TRec k t) cs in
      kinding (get_sctx C) (get_kctx C) t_rec KType ->
      typing C e (unroll k t cs) i ->
      typing C (EFold e) t_rec i
  | TyUnfold C e k t cs i :
      typing C e (TApps (TRec k t) cs) i ->
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
  | TyNew C e1 e2 t len i1 i2 :
      typing C e1 t i1 ->
      typing C e2 (TNat len) i2 ->
      typing C (ENew e1 e2) (TArr t len) (i1 + i2)
  | TyRead C e1 e2 t i1 i2 len i :
      typing C e1 (TArr t len) i1 ->
      typing C e2 (TNat i) i2 ->
      interp_prop (get_sctx C) (i < len) ->
      typing C (ERead e1 e2) t (i1 + i2)
  | TyWrite C e1 e2 e3 i1 i2 i3 t len i :
      typing C e1 (TArr t len) i1 ->
      typing C e2 (TNat i) i2 ->
      interp_prop (get_sctx C) (i < len) ->
      typing C e3 t i3 ->
      typing C (EWrite e1 e2 e3) TUnit (i1 + i2 + i3)
  | TyLoc C l t i :
      get_hctx C $? l = Some (t, i) ->
      typing C (ELoc l) (TArr t i) T0
  | TyPrim C opr e1 e2 i1 i2 :
      typing C e1 (prim_arg1_type opr) i1 ->
      typing C e2 (prim_arg2_type opr) i2 ->
      typing C (EPrim opr e1 e2) (prim_result_type opr) (i1 + i2 + Tconst (prim_cost opr))
  | TyNatAdd C e1 e2 j1 j2 i1 i2 :
      typing C e1 (TNat j1) i1 ->
      typing C e2 (TNat j2) i2 ->
      typing C (ENatAdd e1 e2) (TNat (Nadd j1 j2)) (i1 + i2 + Tconst nat_add_cost)
  | TyTyeq C e t1 i t2 :
      typing C e t1 i ->
      let L := get_sctx C in
      let K := get_kctx C in
      kinding L K t2 KType ->
      tyeq L K t1 t2 KType ->
      typing C e t2 i
  | TyLe C e t i1 i2 :
      typing C e t i1 ->
      let L := get_sctx C in
      sorting L i2 STime ->
      interp_prop L (i1 <= i2) ->
      typing C e t i2 
  .

  Local Close Scope idx_scope.

  (* this predicate says that the heap can allocate fresh locations, i.e. the heap is finite *)
  Definition allocatable (h : heap) := exists l_alloc, forall l, l >= l_alloc -> h $? l = None.

  (* heap typing *)
  Definition htyping (h : heap) (W : hctx) :=
    (forall l t i,
        W $? l = Some (t, i) ->
        exists vs,
          h $? l = Some vs /\
          length vs = interp_idx i [] BSNat /\
          Forall (fun v => value v /\ typing ([], [], W, []) v t T0) vs) /\
    allocatable h.

  (* a shortcut *)
  Definition interp_time i : time_type := interp_idx i [] BSTime.
  
  Inductive all_sorts (P : list sort -> sort -> Prop) : list sort -> Prop :=
  | AllStsNil :
      all_sorts P []
  | AllStsCons s ss :
      all_sorts P ss ->
      P ss s ->
      all_sorts P (s :: ss)
  .

  (* wellformed sort context *)
  Definition wfsorts := all_sorts (fun L s => wfsort L s).

  (* wellformed heap typings *)
  Definition wfhctx L K (W : hctx) := fmap_forall (fun p => kinding L K (fst p) KType /\ sorting L (snd p) SNat) W.

  (* wellformed context *)
  Definition wfctx C :=
    let L := get_sctx C in
    let K := get_kctx C in
    let W := get_hctx C in
    let G := get_tctx C in
    wfsorts L /\
    wfhctx L K W /\
    Forall (fun t => kinding L K t KType) G.

  (* configuration typing *)
  Definition ctyping W (s : config) t i :=
    let '(h, e, f) := s in
    let C := ([], [], W, []) in
    typing C e t i /\
    htyping h W /\
    (interp_time i <= f)%time /\
    wfctx C
  .

  (* ============================================================= *)
  (* The main theorem: Soundness *)
  (* ============================================================= *)
  
  Parameter soundness :  forall W s t i, ctyping W s t i -> safe s.

End TIML.

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

Module TiML (Time : TIME) (BigO :BIG_O Time) <: TIML Time BigO.
  
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
    | IAbs i => IAbs (subst_i_i (1 + x) (shift0_i_i v) i)
    | IApp n c1 c2 => IApp n (subst_i_i x v c1) (subst_i_i x v c2)
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
  
  Definition subst0_i_i v b := subst_i_i 0 v b.
  
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

  Section subst_i_proofs.
    
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

  End subst_i_proofs.
  
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
      rewrite nth_error_nil in *; dis.
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

  Lemma forall_subst_i_i_eq_subst :
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
            eapply forall_shift_i_i_eq_shift with (x := 0); eauto.
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
      specialize (IHbody (S x) (b1 :: bs) v b_v b2).
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
      specialize (IHbody1 x bs v b_v (BSArrow arg_bsort b_b)).
      specialize (IHbody2 x bs v b_v arg_bsort).
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

  Lemma interp_subst_i_i :
    forall body x bs v b_v b_b,
      let bs' := removen x bs in
      nth_error bs x = Some b_v ->
      bsorting (skipn (S x) bs) v b_v ->
      bsorting bs body b_b ->
      interp_idx (subst_i_i x (shift_i_i x 0 v) body) bs' b_b = subst x bs (interp_idx v (skipn (S x) bs) b_v) (interp_idx body bs b_b).
  Proof.
    simpl.
    intros.
    eapply forall_eq_eq; eapply forall_subst_i_i_eq_subst; eauto.
  Qed.
  
  Lemma forall_subst_i_p_iff_subst :
    forall p x bs v b_v,
      let bs' := removen x bs in
      nth_error bs x = Some b_v ->
      bsorting (skipn (S x) bs) v b_v ->
      wfprop1 bs p ->
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
      eapply forall_lift2_lift2_lift4; try eapply forall_subst_i_i_eq_subst; eauto.
      intros; subst.
      propositional.
    }
    {
      rewrite subst_lift2.
      rewrite fuse_lift2_lift2_1.
      rewrite fuse_lift3_lift2_3.
      eapply forall_lift2_lift2_lift4; try eapply forall_subst_i_i_eq_subst; eauto.
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
    wfprop1 bs p ->
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
    wfprop1 bs p1 ->
    wfprop1 bs p2 ->
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
      (* Case Abs *)
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
    induct ls; destruct n; simpl; intros; f_equal; eauto; try dis.
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
      wfprop1 bs p ->
      forall_ bs' (lift2 bs' iff (interp_p bs' (subst_i_p 0 v p)) (subst 0 bs (interp_idx v bs' b_v) (interp_p bs p))).
  Proof.
    simpl; intros.
    specialize (@forall_subst_i_p_iff_subst p 0 (b_v :: bs') v b_v); intros Hsubst.
    simpl in *.
    rewrite shift_i_i_0 in *.
    eauto.
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

  Lemma nth_error_Some_interp_prop_subst_i_p_var L x b p :
    nth_error L x = Some (SSubset b p) ->
    wfprop1 (my_skipn (map get_bsort L) x) p ->
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
      eapply wfprop1_wellscoped_p; eauto.
    }
    Unfocus.
    Focus 2.
    {
      eapply wellscoped_subst_i_p_0.
      {
        eapply wellscoped_shift_i_p; eauto.
        eapply wfprop1_wellscoped_p; eauto.
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
          eapply wfprop1_shift_i_p with (ls := [b]) (x := 1) in Hp; simpl; eauto with db_la.
          simpl in *.
          rewrite my_skipn_0 in *.
          eauto.
        }
      }
      simpl.

      eapply forall_imply_shift_i_p_1_1_var0; eauto.
      rewrite Hbs' in Hp.
      eapply wfprop1_wellscoped_p in Hp; eauto.
    }
  Qed.
  
  Inductive sorting1 : sctx -> idx -> sort -> Prop :=
  | Stg1Var L x s :
      nth_error L x = Some s ->
      sorting1 L (IVar x) (shift_i_s (1 + x) 0 s)
  | Stg1Const L cn :
      sorting1 L (IConst cn) (SBaseSort (const_bsort cn))
  | Stg1UnOp L opr c :
      sorting1 L c (SBaseSort (iunop_arg_bsort opr)) ->
      sorting1 L (IUnOp opr c) (SBaseSort (iunop_result_bsort opr))
  | Stg1BinOp L opr c1 c2 :
      sorting1 L c1 (SBaseSort (ibinop_arg1_bsort opr)) ->
      sorting1 L c2 (SBaseSort (ibinop_arg2_bsort opr)) ->
      sorting1 L (IBinOp opr c1 c2) (SBaseSort (ibinop_result_bsort opr))
  | Stg1Ite L c c1 c2 s :
      sorting1 L c SBool ->
      sorting1 L c1 s ->
      sorting1 L c2 s ->
      sorting1 L (IIte c c1 c2) s
  | Stg1Abs L i b1 b2 :
      sorting1 (SBaseSort b1 :: L) i (SBaseSort b2) ->
      sorting1 L (IAbs i) (SArrow b1 b2)
  | Stg1App L c1 c2 b1 b2 :
      sorting1 L c1 (SArrow b1 b2) ->
      sorting1 L c2 (SBaseSort b1) ->
      sorting1 L (IApp b1 c1 c2) (SBaseSort b2)
  | Stg1SubsetI L c b p :
      sorting1 L c (SBaseSort b) ->
      interp_prop L (subst0_i_p c p) ->
      sorting1 L c (SSubset b p)
  | Stg1SubsetE L c b p :
      sorting1 L c (SSubset b p) ->
      wfprop1 (b :: map get_bsort L) p ->
      sorting1 L c (SBaseSort b)
  .

  Hint Constructors sorting1.

  Lemma Stg1Var' L x s s' :
    nth_error L x = Some s ->
    s' = shift_i_s (1 + x) 0 s ->
    sorting1 L (IVar x) s'.
  Proof.
    intros; subst; eauto.
  Qed.
  
  Lemma sorting1_bsorting L i s :
    sorting1 L i s ->
    bsorting (map get_bsort L) i (get_bsort s).
  Proof.
    induct 1; simpl; eauto.
    econstructor.
    rewrite get_bsort_shift_i_s.
    erewrite map_nth_error; eauto.
  Qed.
  
  Lemma sorting1_bsorting' L i s b :
    sorting1 L i s ->
    b = get_bsort s ->
    bsorting (map get_bsort L) i b.
  Proof.
    intros; subst; eapply sorting1_bsorting; eauto.
  Qed.
  
  Lemma sorting1_wellscoped_i L i s :
    sorting1 L i s ->
    wellscoped_i (length L) i.
  Proof.
    induct 1; simpl; eauto.
    econstructor.
    eapply nth_error_Some_lt; eauto.
  Qed.
  
  Lemma sorting1_Subset_elim L i s :
    sorting1 L i s ->
    forall b p,
      s = SSubset b p ->
      wfprop1 (b :: map get_bsort L) p ->
      interp_prop L (subst_i_p 0 i p).
  Proof.
    induct 1; simpl; try rename b into b'; try rename p into p'; intros b p Hs Hp; subst; eauto; try dis.
    {
      (* Case Var *)
      destruct s; simpl in *; try dis.
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
      eapply wfprop1_shift_i_p_rev with (L1 := [b]) (L2 := map get_bsort (firstn x L) ++ [b]) (L3 := map get_bsort (my_skipn L (S x))) in Hp; simpl; eauto.
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
          eauto using sorting1_bsorting.
      }
      unfold interp_prop in IHsorting1_2.
      simpl in IHsorting1_2.
      set (bs := map get_bsort L) in *.
      set (ps := interp_p bs (and_all (strip_subsets L))) in *.
      assert (IHsorting1_2' : imply_ bs ps (subst 0 (b :: bs) (interp_idx c1 bs b) (interp_p (b :: bs) p))).
      {
        eapply forall_replace_imply; [eapply forall_iff_refl | |].
        {
          eapply forall_subst_i_p_iff_subst_0;
          eauto.
          eapply sorting1_bsorting'; eauto.
        }
        eapply IHsorting1_2; eauto.
      }
      assert (IHsorting1_3' : imply_ bs ps (subst 0 (b :: bs) (interp_idx c2 bs b) (interp_p (b :: bs) p))).
      {
        eapply forall_replace_imply; [eapply forall_iff_refl | |].
        {
          eapply forall_subst_i_p_iff_subst_0;
          eauto.
          eapply sorting1_bsorting'; eauto.
        }
        eapply IHsorting1_3; eauto.
      }
      unfold imply_ in *.
      simpl in *.
      rewrite fuse_lift2_lift2_2 in *.
      rewrite fuse_lift3_lift3_3.
      eapply forall_lift3_lift3_lift5; eauto.
      unfold ite; intros.
      rewrite convert_bsort_value_refl_eq in *.
      cases a3; eauto.
    }
    {
      invert Hs.
      eauto.
    }
  Qed.
  
  Lemma get_bsort_remove_subst L x v :
    let L' := subst_i_ss v (firstn x L) ++ my_skipn L (S x) in
    map get_bsort L' = removen x (map get_bsort L).
  Proof.
    simpl.
    rewrite !map_app.
    rewrite !get_bsort_subst_i_ss.
    rewrite <- !map_app.
    rewrite <- !removen_firstn_my_skipn.
    rewrite !map_removen.
    eauto.
  Qed.
  
  Lemma forall_subst_i_p_intro_imply_my_skipn bs x b_v v p1 p2 :
    forall_ bs (lift2 bs imply (interp_p bs p1) (interp_p bs p2)) ->
    nth_error bs x = Some b_v ->
    bsorting (my_skipn bs (S x)) v b_v ->
    wfprop1 bs p1 ->
    wfprop1 bs p2 ->
    let bs' := removen x bs in
    forall_ bs' (lift2 bs' imply (interp_p bs' (subst_i_p x (shift_i_i x 0 v) p1)) (interp_p bs' (subst_i_p x (shift_i_i x 0 v) p2))).
  Proof.
    simpl; intros.
    eapply forall_subst_i_p_intro_imply; eauto.
    rewrite skipn_my_skipn; eauto.
  Qed.

  Lemma subst_strip_subsets_imply L n c s :
    let bs := map get_bsort L in
    let bs' := removen n bs in
    nth_error L n = Some s ->
    sorting1 (my_skipn L (1 + n)) c s ->
    wfsorts1 L ->
    imply_ bs'
           (interp_p bs' (and_all (strip_subsets (subst_i_ss c (firstn n L) ++ my_skipn L (S n)))))
           (interp_p bs' (subst_i_p n (shift_i_i n 0 c) (and_all (strip_subsets L)))).
  Proof.
    intros bs bs' Hnth Hc Hss.
    copy Hnth Hn.
    eapply nth_error_Some_lt in Hn.
    rewrite !strip_subsets_app by la.
    rewrite length_subst_i_ss.
    rewrite length_firstn_le by la.
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
      eapply sorting1_bsorting; eauto.
    }
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
    eapply sorting1_Subset_elim in Hc; eauto.
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
    assert (Hc'' : imply_ bs' (interp_p bs' (shift_i_p n 0 (and_all (strip_subsets (skipn (S n) L))))) (interp_p bs' (shift_i_p n 0 (subst_i_p 0 c p)))).
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
        eapply wfsorts1_wellscoped_ss.
        eapply all_sorts_skipn; eauto.
      }
      {
        rewrite map_length.
        eapply all_sorts_nth_error_Some in Hnth; eauto.
        invert Hnth.
        eapply wfprop1_wellscoped_p in H1.
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
  
  Lemma interp_subst_i_p L p :
    interp_prop L p ->
    forall n s c ,
      nth_error L n = Some s ->
      sorting1 (my_skipn L (1 + n)) c s ->
      wfprop1 (map get_bsort L) p ->
      wfsorts1 L ->
      interp_prop (subst_i_ss c (firstn n L) ++ my_skipn L (1 + n)) (subst_i_p n (shift_i_i n 0 c) p).
  Proof.
    intros Hp n s c Hnth Hc Hwfp Hss.
    unfold interp_prop in *.
    simpl in *.
    rewrite get_bsort_remove_subst.
    copy Hnth Hnth'.
    eapply map_nth_error with (f := get_bsort) in Hnth'.
    eapply forall_subst_i_p_intro_imply_my_skipn in Hp; eauto.
    {
      eapply forall_trans; [ | eassumption].
      eapply subst_strip_subsets_imply; eauto.
    }
    {
      rewrite <- map_my_skipn.
      eapply sorting1_bsorting; eauto.
    }
    {
      eapply wfsorts1_wfprop1_strip_subsets; eauto.
    }
  Qed.
  
  Lemma interp_prop_subst0_i_p s L p v :
    interp_prop (s :: L) p ->
    sorting1 L v s ->
    wfprop1 (get_bsort s :: map get_bsort L) p ->
    wfsorts1 (s :: L) ->
    interp_prop L (subst0_i_p v p).
  Proof.
    intros Hp Hv Hwfp HL.
    specialize (@interp_subst_i_p (s :: L) p Hp 0 s v).
    intros H.
    simpl in *.
    rewrite my_skipn_0 in *.
    rewrite shift_i_i_0 in *.
    eapply H; eauto.
  Qed.

  Lemma wfprop1_wellscoped_p' L p n :
    wfprop1 L p ->
    n = length L ->
    wellscoped_p n p.
  Proof.
    intros; subst; eapply wfprop1_wellscoped_p; eauto.
  Qed.
  
  Lemma Stg1Eq L i s :
    sorting1 L i s ->
    forall s',
      sorteq L s' s ->
      wfsorts1 L ->
      let bs := map get_bsort L in
      wfsort1 bs s ->
      wfsort1 bs s' ->
      sorting1 L i s'.
  Proof.
    simpl.
    induct 1; simpl; try solve [intros; eauto | induct 1; simpl in *; econstructor; eauto].
    {
      (* Case Var *)
      intros s' Heq HL Hs Hs'.
      invert Heq; simpl in *.
      {
        destruct s; simpl in *; try dis.
        invert H3.
        eapply Stg1Var'; eauto.
      }
      {
        destruct s as [ ? | b' p'']; simpl in *; try dis.
        symmetry in H0.
        invert H0.
        rename p'' into p'.
        eapply Stg1SubsetI.
        {
          eapply Stg1SubsetE.
          {
            eapply Stg1Var'; eauto.
            simpl.
            eauto.
          }
          {
            invert Hs.
            eauto.
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
            eapply Stg1SubsetE.
            {
              eapply Stg1Var'; eauto.
              simpl.
              eauto.
            }
            {
              invert Hs.
              eauto.
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
      eapply Stg1SubsetI; eauto.
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

  Lemma get_bsort_shift_i_ss :
    forall L v,
      map get_bsort (shift_i_ss v L) = map get_bsort L.
  Proof.
    induct L; simpl; intros; f_equal; eauto using get_bsort_shift_i_s.
  Qed.

  Lemma wfprop1_shift_i_p' L p x ls n :
    wfprop1 L p ->
    n = length ls ->
    x <= length L ->
    wfprop1 (firstn x L ++ ls ++ my_skipn L x) (shift_i_p n x p).
  Proof.
    intros; subst; eapply wfprop1_shift_i_p; eauto.
  Qed.
  
  Lemma sorting1_shift_i_i :
    forall L c s,
      sorting1 L c s ->
      forall x ls,
        let n := length ls in
        x <= length L ->
        wellscoped_ss L ->
        wellscoped_s (length L) s ->
        sorting1 (shift_i_ss n (firstn x L) ++ ls ++ my_skipn L x) (shift_i_i n x c) (shift_i_s n x s).
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
        eapply Stg1Var'.
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
        eapply Stg1Var'.
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
      eapply IHsorting1_1; eauto; econstructor; eauto.
    }
    {
      (* Case Abs *)
      econstructor; eauto.
      unfold SNat, STimeFun in *.
      eapply IHsorting1 with (x := S x); eauto with db_la.
      econstructor; eauto.
    }
    {
      econstructor; eauto.
      {
        eapply IHsorting1_1; eauto; econstructor; eauto.
      }
    }
    {
      (* Case SubsetI *)
      econstructor; eauto.
      unfold subst0_i_p in *.
      rewrite <- shift_i_p_subst_out by la.
      invert Hs.
      eapply interp_prop_shift_i_p; eauto.
      eapply wellscoped_subst_i_p_0; eauto using sorting1_wellscoped_i.
    }
    {
      (* Case SubsetE *)
      eapply Stg1SubsetE; [eapply IHsorting1 |]; eauto.
      {
        econstructor.
        eapply wfprop1_wellscoped_p'; eauto.
        simpl.
        rewrite map_length.
        eauto.
      }
      repeat rewrite map_app.
      rewrite get_bsort_shift_i_ss.
      rewrite map_firstn.
      rewrite map_my_skipn.
      eapply wfprop1_shift_i_p' with (x := S x) (L := b :: map get_bsort L); simpl; try rewrite map_length; eauto with db_la.
    }
  Qed.

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

  Lemma wfsort1_wellscoped_s' L s n :
    wfsort1 L s ->
    n = length L ->
    wellscoped_s n s.
  Proof.
    intros; subst; eapply wfsort1_wellscoped_s; eauto.
  Qed.
  
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
  
  Lemma wellscoped_subst_i_s :
    forall L b,
      wellscoped_s L b ->
      forall x v L',
        x < L ->
        wellscoped_i (L - (1 + x)) v ->
        L' = L - 1 ->
        wellscoped_s L' (subst_i_s x (shift_i_i x 0 v) b).
  Proof.
    induct 1;
      simpl; try rename x into y; intros x v ? Hx Hv ?; subst; try solve [econstructor; eauto using wellscoped_subst_i_i].
    unfold shift0_i_i.
    rewrite shift_i_i_shift_merge by la.
    rewrite plus_comm.
    econstructor; eauto with db_la.
    simpl.
    eapply wellscoped_subst_i_p; eauto with db_la.
  Qed.
  
  Lemma wellscoped_shift_i_i_rev :
    forall L body,
      wellscoped_i L body ->
      forall n x body' L',
        body = shift_i_i n x body' ->
        x + n <= L ->
        L' = L - n ->
        wellscoped_i L' body'.
  Proof.
    induct 1;
      simpl; try rename x into x'; try rename n into m; intros n x body' L' Hbody Hcmp; intros; subst; cbn in *;
        try solve [
              destruct body'; simpl in *; try cases_le_dec; try dis;
              invert Hbody; eauto with db_la
            ].
    {
      (* Case Abs *)
      destruct body'; simpl in *; try cases_le_dec; try dis.
      invert Hbody; eauto.
      econstructor; eauto.
      eapply IHwellscoped_i; eauto with db_la.
      destruct n; la.
    }
  Qed.

  Lemma wellscoped_shift_i_p_rev :
    forall L body,
      wellscoped_p L body ->
      forall n x body' L',
        body = shift_i_p n x body' ->
        x + n <= L ->
        L' = L - n ->
        wellscoped_p L' body'.
  Proof.
    induct 1;
      simpl; try rename x into x'; try rename n into m; intros n x body' L' Hbody Hcmp; intros; subst; cbn in *;
        try solve [
              destruct body'; simpl in *; try cases_le_dec; try dis;
              invert Hbody; eauto using wellscoped_shift_i_i_rev with db_la
            ].
    {
      (* Case PQuan *)
      destruct body'; simpl in *; try cases_le_dec; try dis.
      invert Hbody; eauto.
      econstructor; eauto.
      eapply IHwellscoped_p; eauto with db_la.
      destruct n; la.
    }
  Qed.
  
  Lemma wellscoped_shift_i_s_rev :
    forall L body,
      wellscoped_s L body ->
      forall n x body' L',
        body = shift_i_s n x body' ->
        x + n <= L ->
        L' = L - n ->
        wellscoped_s L' body'.
  Proof.
    induct 1;
      simpl; try rename x into x'; try rename n into m; intros n x body' L' Hbody Hcmp; intros; subst; cbn in *;
        try solve [
              destruct body'; simpl in *; try cases_le_dec; try dis;
              invert Hbody; eauto using wellscoped_shift_i_p_rev with db_la
            ].
  Qed.
  
  Lemma wfsort1_shift_i_s :
    forall L s,
      wfsort1 L s ->
      forall x ls,
        let n := length ls in
        x <= length L ->
        wfsort1 (firstn x L ++ ls ++ my_skipn L x) (shift_i_s n x s).
  Proof.
    simpl.
    induct 1;
      simpl; intros x ls Hx; cbn in *; try solve [econstructor; eauto].
    econstructor.
    eapply wfprop1_shift_i_p with (x := S x) (L := _ :: L); simpl; eauto with db_la.
  Qed.
  
  Lemma get_bsort_shift_i_ss_insert x L ls :
    map get_bsort (shift_i_ss (length ls) (firstn x L) ++ ls ++ my_skipn L x) = firstn x (map get_bsort L) ++ map get_bsort ls ++ my_skipn (map get_bsort L) x.
  Proof.
    repeat rewrite map_app.
    rewrite get_bsort_shift_i_ss.
    rewrite map_firstn.
    rewrite map_my_skipn.
    eauto.
  Qed.
  
  Lemma wfsort1_shift_i_s' :
    forall L s,
      wfsort1 L s ->
      forall x ls n,
        x <= length L ->
        n = length ls ->
        wfsort1 (firstn x L ++ ls ++ my_skipn L x) (shift_i_s n x s).
  Proof.
    intros; subst; eapply wfsort1_shift_i_s; eauto.
  Qed.
  
  Hint Extern 0 (_ = length (map _ _)) => rewrite map_length; eauto : db_la.
  Hint Extern 0 (_ <= length (map _ _)) => rewrite map_length; eauto : db_la.
  
  Lemma wfsort1_shift_i_s'' x L s ls :
    wfsort1 (map get_bsort L) s ->
    x <= length L ->
    wfsort1 (map get_bsort (shift_i_ss (length ls) (firstn x L) ++ ls ++ my_skipn L x))
            (shift_i_s (length ls) x s).
  Proof.
    intros.
    rewrite get_bsort_shift_i_ss_insert.
    eapply wfsort1_shift_i_s'; eauto with db_la.
  Qed.
  
  Lemma sorting1_shift_i_i' L c s x ls n :
    sorting1 L c s ->
    n = length ls ->
    x <= length L ->
    wellscoped_ss L ->
    wellscoped_s (length L) s ->
    sorting1 (shift_i_ss n (firstn x L) ++ ls ++ skipn x L) (shift_i_i n x c) (shift_i_s n x s).
  Proof.
    rewrite skipn_my_skipn.
    intros; subst; eapply sorting1_shift_i_i; eauto.
  Qed.
  
  Lemma sorting1_shift_i_i_0 L c s ls n :
    sorting1 L c s ->
    n = length ls ->
    wellscoped_ss L ->
    wellscoped_s (length L) s ->
    sorting1 (ls ++ L) (shift_i_i n 0 c) (shift_i_s n 0 s).
  Proof.
    intros; eapply sorting1_shift_i_i' with (x := 0); eauto with db_la.
  Qed.
  
  Arguments SBool / .
  Arguments SNat / .
  Arguments STimeFun arity / .
  
  Hint Extern 0 (wfsorts1 (_ :: _)) => econstructor.
  
  Lemma bsorting_shift_i_i_0 L c s ls n :
    bsorting L c s ->
    n = length ls ->
    bsorting (ls ++ L) (shift_i_i n 0 c) s.
  Proof.
    intros Hbody ?; subst.
    eapply bsorting_shift_i_i with (x := 0) in Hbody; eauto with db_la.
    simpl in *.
    rewrite my_skipn_0 in *.
    eauto.
  Qed.
  
  Lemma bsorting_subst_i_i :
    forall L body b_b,
      bsorting L body b_b ->
      forall x b_v v ,
        nth_error L x = Some b_v ->
        bsorting (my_skipn L (1 + x)) v b_v ->
        (* wfsorts1 L -> *)
        bsorting (removen x L) (subst_i_i x (shift_i_i x 0 v) body) b_b.
  Proof.
    induct 1;
      simpl; try rename x into y; try rename s into b; intros x b_v v Hx Hv (* HL *); simpl in *; try solve [econstructor; eauto].
    {
      (* Case Stg1Var *)
      copy Hx Hcmp.
      eapply nth_error_Some_lt in Hcmp.
      cases (y <=>? x); eauto with db_la.
      {
        econstructor.
        erewrite removen_lt by eauto with db_la.
        eauto.
      }
      {
        rewrite removen_firstn_my_skipn.
        subst.
        assert (b_v = b) by equality.
        subst.
        eapply bsorting_shift_i_i_0; eauto with db_la; try rewrite length_firstn_le by la; eauto.
      }
      {
        econstructor.
        erewrite removen_gt by eauto with db_la.
        eauto.
      }
    }
    {
      (* Case Stg1Abs *)
      rewrite shift0_i_i_shift_0.
      econstructor; eauto with db_la.
      eapply IHbsorting with (x := S x); eauto.
    }
  Qed.
  
  Lemma wfprop1_subst_i_p :
    forall L body,
      wfprop1 L body ->
      forall x b_v v ,
        nth_error L x = Some b_v ->
        bsorting (my_skipn L (1 + x)) v b_v ->
        (* wfsorts1 L -> *)
        wfprop1 (removen x L) (subst_i_p x (shift_i_i x 0 v) body).
  Proof.
    induct 1;
      simpl; try rename x into y; try rename s into b; intros x b_v v Hx Hv (* HL *); simpl in *; try solve [econstructor; eauto using bsorting_subst_i_i].
    rewrite shift0_i_i_shift_0.
    econstructor; eauto with db_la.
    eapply IHwfprop1 with (x := S x); eauto.
  Qed.
  
  Lemma wfprop1_subst_i_p_0 L body b_v v :
    wfprop1 (b_v :: L) body ->
    bsorting L v b_v ->
    wfprop1 L (subst_i_p 0 v body).
  Proof.
    intros Hbody Hv; eapply wfprop1_subst_i_p with (x := 0) in Hbody; simpl; eauto; try rewrite my_skipn_0; eauto.
    simpl in *.
    rewrite shift_i_i_0 in *.
    eauto.
  Qed.
  
  Lemma sorting1_subst_i_i :
    forall L body s_b,
      sorting1 L body s_b ->
      forall x s_v v ,
        nth_error L x = Some s_v ->
        sorting1 (my_skipn L (1 + x)) v s_v ->
        wfsorts1 L ->
        wfsort1 (map get_bsort L) s_b ->
        sorting1 (subst_i_ss v (firstn x L) ++ my_skipn L (1 + x)) (subst_i_i x (shift_i_i x 0 v) body) (subst_i_s x (shift_i_i x 0 v) s_b).
  Proof.
    induct 1;
      simpl; try rename x into y; intros x s_v v Hx Hv HL Hs_b; simpl in *; try solve [econstructor; eauto].
    {
      (* Case Stg1Var *)
      copy Hx Hcmp.
      eapply nth_error_Some_lt in Hcmp.
      cases (y <=>? x); eauto with db_la.
      {
        eapply Stg1Var'.
        {
          rewrite nth_error_app1;
          try rewrite length_subst_i_ss; try erewrite length_firstn_le by la; try la.
          erewrite nth_error_subst_i_ss; eauto;
            try erewrite nth_error_firstn by la; eauto.
        }
        {
          erewrite length_firstn_le by la.
          rewrite <- subst_i_s_shift by la.
          eauto.
        }
      }
      {
        subst.
        assert (s_v = s) by equality.
        subst.
        rewrite subst_i_s_shift_avoid by la.
        simpl.
        rewrite Nat.sub_0_r.
        eapply sorting1_shift_i_i_0; eauto with db_la.
        {
          rewrite length_subst_i_ss.
          rewrite length_firstn_le by la.
          eauto.
        }
        {
          rewrite <- skipn_my_skipn.
          eapply all_sorts_skipn; eauto.
          eapply wfsorts1_wellscoped_ss; eauto.
        }
        {
          eapply all_sorts_nth_error_Some in Hx; eauto.
          rewrite skipn_my_skipn in *.
          eapply wfsort1_wellscoped_s'; eauto.
          rewrite map_length; eauto.
        }
      }
      {
        eapply Stg1Var'.
        {
          rewrite nth_error_app2;
          try rewrite length_subst_i_ss; try erewrite length_firstn_le by la; try la.
          rewrite nth_error_my_skipn by la.
          erewrite <- H.
          f_equal.
          la.
        }
        {
          rewrite subst_i_s_shift_avoid by la.
          f_equal.
          la.
        }
      }
    }
    {
      (* Case Stg1Abs *)
      rewrite shift0_i_i_shift_0.
      econstructor; eauto with db_la.
      eapply IHsorting1 with (x := S x); eauto.
    }
    {
      (* Case Stg1App *)
      econstructor; simpl; eauto.
      eapply IHsorting1_1; eauto.
      econstructor; eauto.
    }
    {
      (* Case Stg1SubsetI *)
      econstructor; eauto.
      unfold subst0_i_p.
      unfold shift0_i_p.
      rewrite <- subst_i_p_subst by la.
      invert Hs_b.
      eapply interp_subst_i_p; eauto.
      eapply sorting1_bsorting in H.
      eapply wfprop1_subst_i_p_0; eauto.
    }
    {
      (* Case Stg1SubsetE *)
      eapply Stg1SubsetE ; [eapply IHsorting1 |]; eauto.
      rewrite shift0_i_i_shift_0.
      rewrite map_app.
      rewrite get_bsort_subst_i_ss.
      rewrite map_firstn.
      rewrite map_my_skipn.
      rewrite <- removen_firstn_my_skipn.
      eapply sorting1_bsorting in Hv.
      rewrite map_my_skipn in *.
      eapply wfprop1_subst_i_p with (x := S x) (L := b :: _); simpl; eauto.
      erewrite map_nth_error; eauto.
    }
  Qed.

  Arguments STime / .

  Lemma sorting1_subst_i_i' :
    forall L body s_b,
      sorting1 L body s_b ->
      forall x s_v v s_b',
        nth_error L x = Some s_v ->
        sorting1 (my_skipn L (1 + x)) v s_v ->
        wfsorts1 L ->
        wfsort1 (map get_bsort L) s_b ->
        s_b' = subst_i_s x (shift_i_i x 0 v) s_b ->
        sorting1 (subst_i_ss v (firstn x L) ++ my_skipn L (1 + x)) (subst_i_i x (shift_i_i x 0 v) body) s_b'.
  Proof.
    intros; subst; eapply sorting1_subst_i_i; eauto.
  Qed.
  
  Lemma wfsort1_subst_i_s :
    forall L body,
      wfsort1 L body ->
      forall x b_v v ,
        nth_error L x = Some b_v ->
        bsorting (my_skipn L (1 + x)) v b_v ->
        (* wfsorts1 L -> *)
        wfsort1 (removen x L) (subst_i_s x (shift_i_i x 0 v) body).
  Proof.
    induct 1;
      simpl; try rename x into y; intros x b_v v Hx Hv; simpl in *; try solve [econstructor; eauto].
    rewrite shift0_i_i_shift_0.
    econstructor; eauto with db_la.
    eapply wfprop1_subst_i_p with (x := S x) (L := _ :: _); eauto.
  Qed.
  
  Lemma get_bsort_subst_i_ss_remove x L v :
    map get_bsort (subst_i_ss v (firstn x L) ++ my_skipn L (S x)) = removen x (map get_bsort L).
  Proof.
    rewrite map_app.
    rewrite get_bsort_subst_i_ss.
    rewrite map_firstn.
    rewrite map_my_skipn.
    rewrite <- removen_firstn_my_skipn.
    eauto.
  Qed.

  Lemma wfsort1_subst_i_s' x L v s s' :
    wfsort1 (map get_bsort L) s' ->
    nth_error L x = Some s ->
    sorting1 (my_skipn L (S x)) v s ->
    wfsort1 (map get_bsort (subst_i_ss v (firstn x L) ++ my_skipn L (S x)))
           (subst_i_s x (shift_i_i x 0 v) s').
  Proof.
    intros.
    rewrite get_bsort_subst_i_ss_remove; eauto.
    eapply wfsort1_subst_i_s; eauto.
    {
      erewrite map_nth_error; eauto.
    }
    rewrite <- map_my_skipn.
    eapply sorting1_bsorting'; eauto.
  Qed.
  
  Lemma bsorting_sorting1_SBaseSort bs i b :
    bsorting bs i b ->
    forall L,
      bs = map get_bsort L ->
      wfsorts1 L ->
      sorting1 L i (SBaseSort b).
  Proof.
    induct 1; simpl; try rename L into bs; intros L ? HL; subst; try solve [econstructor; eauto].
    {
      (* Case IVar *)
      eapply nth_error_map_elim in H.
      openhyp.
      subst.
      destruct x0; simpl in *.
      {
        eapply Stg1Var'; eauto.
      }
      {
        eapply Stg1SubsetE.
        {
          eapply Stg1Var'; eauto.
          simpl.
          eauto.
        }
        eapply all_sorts_nth_error_Some in HL; eauto.
        eapply nth_error_Some_lt in H.
        rewrite skipn_my_skipn in *.
        invert HL.
        rewrite map_my_skipn in *.
        eapply wfprop1_shift_i_p with (x := 1) in H2; simpl in *; eauto with db_la.
        rewrite my_skipn_0 in *.
        erewrite firstn_my_skipn in *.
        rewrite length_firstn_le in * by (rewrite map_length; la).
        eauto.
      }
    }
  Qed.

  Lemma shift_i_i_inj :
    forall b b' n x,
      shift_i_i n x b = shift_i_i n x b' ->
      b = b'.
  Proof.
    induct b; destruct b'; try rename x into x'; simpl; intros n x Heq; try solve [repeat cases_le_dec; dis | invert Heq; f_equal; eauto].
    {
      rename x0 into x''.
      repeat cases_le_dec; invert Heq; f_equal; try la.
      eapply plus_reg_l; eauto.
    }
    {
      assert (opr = opr0) by congruence; subst.
      invert Heq.
      f_equal; eauto.
    }
  Qed.
  
  Lemma shift_i_p_inj :
    forall b b' n x,
      shift_i_p n x b = shift_i_p n x b' ->
      b = b'.
  Proof.
    induct b; destruct b'; try rename x into x'; simpl; intros n x Heq; try solve [repeat cases_le_dec; dis | invert Heq; f_equal; eauto using shift_i_i_inj].
  Qed.
  
  Lemma shift_i_s_inj :
    forall b b' n x,
      shift_i_s n x b = shift_i_s n x b' ->
      b = b'.
  Proof.
    induct b; destruct b'; try rename x into x'; simpl; intros n x Heq; try solve [repeat cases_le_dec; dis | invert Heq; f_equal; eauto using shift_i_p_inj].
  Qed.

  Lemma nth_error_shift_i_ss_elim bs :
    forall x b' m,
      let n := length bs in
      nth_error (shift_i_ss m bs) x = Some b' ->
      exists b,
        nth_error bs x = Some b /\
        b' = shift_i_s m (n - S x) b.
  Proof.
    simpl.
    induction bs; simpl; intros x b' m Hx.
    {
      rewrite nth_error_nil in *; dis.
    }
    destruct x; simplify; eauto.
    invert Hx.
    repeat eexists_split; eauto; repeat f_equal; la.
  Qed.
  
  Lemma forall_shift0_rev new :
    forall ks p,
      forall_ (new ++ ks) (shift0 new ks p) ->
      forall_ ks p.
  Proof.
    induct new; cbn in *; intros ks p H; eauto.
    rewrite lift1_shift0 in *.
    rewrite fuse_lift1_lift1 in *.
    eapply IHnew in H.
    eapply forall_use_premise; eauto.
    rewrite fuse_lift2_lift1_1.
    rewrite dedup_lift2.
    eapply forall_lift1; eauto.
    intros x f.
    eapply f.
    eapply bsort_default_value.
  Qed.
  
  Lemma forall_lift0_lift0 :
    forall bs (f1 : Prop) (f2 : Prop),
      (f1 -> f2) ->
      forall_ bs (lift0 bs f1) ->
      forall_ bs (lift0 bs f2).
  Proof.
    induct bs; simplify; eauto.
    rewrite fuse_lift1_lift0 in *.
    eapply IHbs; [ | eapply H0].
    simplify.
    eauto.
  Qed.
  
  Lemma forall_lift0_rev ks : forall (P : Prop), forall_ ks (lift0 ks P) -> P.
  Proof.
    induct ks; intros; cbn in *; eauto.
    rewrite fuse_lift1_lift0 in *.
    eapply IHks.
    eapply forall_lift0_lift0; [| eapply H]; eauto.
    intros f.
    eapply f.
    eapply bsort_default_value.
  Qed.
  
  Lemma forall_shift_rev x :
    forall ks new p,
      forall_ (insert new x ks) (shift new x ks p) ->
      forall_ ks p.
  Proof.
    induct x; cbn in *.
    {
      intros ks new p H.
      eapply forall_shift0_rev; eauto.
    }
    destruct ks; cbn in *; intros new p H.
    {
      eapply forall_lift0_rev; eauto.
    }
    {
      rewrite lift1_shift in *.
      eauto.
    }
  Qed.

  (*
  Lemma interp_prop_shift_i_p_rev L p x ls :
    let n := length ls in
    interp_prop (shift_i_ss n (firstn x L) ++ ls ++ my_skipn L x) (shift_i_p n x p) ->
    wellscoped_ss L ->
    wellscoped_p (length L) p ->
    x <= length L ->
    interp_prop L p.
  Proof.
    cbn in *.
    intros H Hscss Hscp Hle.
    unfold interp_prop in *.
    cbn in *.
    rewrite !get_bsort_insert_shift in *.
    set (bs := map get_bsort L) in *.
    set (bs_new := map get_bsort ls) in *.
    eapply forall_shift_rev with (new := bs_new) (x := x).
    rewrite <- lift2_shift in *.
  Qed.
  
  Lemma sorting1_shift_i_i_rev :
    forall L i s,
      sorting1 L i s ->
      forall x L' ls i' s',
        let n := length ls in
        L = shift_i_ss n (firstn x L') ++ ls ++ my_skipn L' x ->
        i = shift_i_i n x i' ->
        s = shift_i_s n x s' ->
        x <= length L' ->
        sorting1 L' i' s'.
  Proof.
    simpl.
    induct 1;
      simpl; try rename x into x'; try rename n into m; intros x L' ls i' s' HL Hi Hs Hx; intros; subst; cbn in *;
        try solve [
              destruct i'; simpl in *; try cases_le_dec; try dis;
              invert Hi; eauto |
              destruct i'; simpl in *; try cases_le_dec; try dis;
              invert Hi;
              destruct s'; simpl in *; try dis;
              invert Hs;
              econstructor; eauto;
              eapply IHsorting; eauto with db_la; simpl; eauto with db_la
            ].
    {
      (* Case IVar *)
      destruct i'; simpl in *; try dis.
      rename x0 into y.
      cases (x <=? y); injection Hi; intros Hi'; subst.
      {
        rewrite nth_error_app2 in *;
        try rewrite length_shift_i_ss in *; try erewrite length_firstn_le in * by la; try la.
        rewrite nth_error_app2 in * by la.
        rewrite nth_error_my_skipn in * by la.
        replace (nth_error L' _) with (nth_error L' y) in *.
        Focus 2.
        {
          f_equal.
          assert (Hyx : length ls + y - x - length ls = y - x) by la.
          rewrite Hyx.
          rewrite le_plus_minus_r; eauto.
        }
        Unfocus.
        eapply Stg1Var'; eauto.
        replace (shift_i_s _ 0 s) with (shift_i_s (length ls) x (shift_i_s (S y) 0 s)) in Hs.
        Focus 2.
        {
          rewrite shift_i_s_shift_merge by la.
          f_equal.
          la.
        }
        Unfocus.
        eapply shift_i_s_inj in Hs.
        subst.
        eauto.
      }
      {
        rewrite nth_error_app1 in *;
        try rewrite length_shift_i_ss in *; try erewrite length_firstn_le in * by la; try la.
        eapply nth_error_shift_i_ss_elim in H; eauto.
        rewrite length_firstn_le in * by la.
        destruct H as (s'' & Hy & ?); subst.
        rewrite nth_error_firstn in * by la.
        eapply Stg1Var'; eauto.
        replace (shift_i_s _ 0 _) with (shift_i_s (length ls) x (shift_i_s (S y) 0 s'')) in Hs.
        Focus 2.
        {
          rewrite shift_i_s_shift_cut by la.
          f_equal.
        }
        Unfocus.
        eapply shift_i_s_inj in Hs.
        subst.
        eauto.
      }
    }
    {
      (* Case IUnOp *)
      destruct i'; simpl in *; try cases_le_dec; try dis.
      assert (opr = opr0) by congruence; subst.
      invert Hi.
      destruct s'; simpl in *; try dis.
      invert Hs.
      eauto.
    }
    {
      (* Case Stg1SubsetI *)
      destruct s'; simpl in *; try dis.
      invert Hs.
      eapply Stg1SubsetI; eauto.
      unfold subst0_i_p in *.
      rewrite <- shift_i_p_subst_out in * by la.
    }
  Qed.
   *)
  
  Lemma sorting1_shift_i_i_rev_SBaseSort L i b x L' ls i' :
      sorting1 L i (SBaseSort b) ->
      let n := length ls in
      L = shift_i_ss n (firstn x L') ++ ls ++ my_skipn L' x ->
      i = shift_i_i n x i' ->
      x <= length L' ->
      wfsorts1 L' ->
      sorting1 L' i' (SBaseSort b).
  Proof.
    simpl.
    intros H HL Hi Hx HL'.
    subst.
    eapply bsorting_sorting1_SBaseSort; eauto.
    eapply sorting1_bsorting in H.
    repeat rewrite map_app in *.
    rewrite get_bsort_shift_i_ss in *.
    rewrite map_firstn in *.
    rewrite map_my_skipn in *.
    eapply bsorting_shift_i_i_rev in H; eauto; try rewrite length_firstn_le; try rewrite map_length; eauto.
    simpl in *.
    rewrite firstn_my_skipn in *.
    eauto.
  Qed.
    
  Lemma sorting1_shift_i_i_rev_SBaseSort_1_0 L i b s :
      sorting1 (s :: L) (shift_i_i 1 0 i) (SBaseSort b) ->
      wfsorts1 L ->
      sorting1 L i (SBaseSort b).
  Proof.
    intros H HL.
    eapply sorting1_shift_i_i_rev_SBaseSort with (x := 0) (ls := [s]) in H; eauto with db_la.
    simpl in *.
    rewrite my_skipn_0.
    eauto.
  Qed.

  Lemma wfsort1_shift_i_s_rev :
    forall L s,
      wfsort1 L s ->
      forall n x s' L1 L2 L3,
        s = shift_i_s n x s' ->
        L = L1 ++ L2 ++ L3 ->
        x = length L1 ->
        n = length L2 ->
        wfsort1 (L1 ++ L3) s'.
  Proof.
    induct 1;
      simpl; intros ? ? s' L1 L2 L3 Hs; intros; subst; cbn in *;
        try solve [
              destruct s'; simpl in *; try cases_le_dec; try dis;
              invert Hs; eauto using wfprop1_shift_i_p_rev
            ].
    destruct s'; simpl in *; try cases_le_dec; try dis;
      invert Hs; eauto.
    econstructor; eauto.
    eapply wfprop1_shift_i_p_rev with (L1 := _ :: _) in H; eauto.
    eauto.
  Qed.    
  
  Lemma wfsort1_shift_i_s_rev' L s ls x n s' :
    wfsort1 (firstn x L ++ ls ++ my_skipn L x) s ->
    x <= length L ->
    s = shift_i_s n x s' ->
    n = length ls ->
    wfsort1 L s'.
  Proof.
    intros H; intros; subst.
    rewrite <- (firstn_my_skipn x L).
    eapply wfsort1_shift_i_s_rev in H; eauto.
    rewrite length_firstn_le by la.
    eauto.
  Qed.
  
  Lemma sorting1_shift_i_i'' :
    forall L c s,
      sorting1 L c s ->
      forall x ls s',
        let n := length ls in
        x <= length L ->
        wellscoped_ss L ->
        wellscoped_s (length L) s ->
        s' = shift_i_s n x s ->
        sorting1 (shift_i_ss n (firstn x L) ++ ls ++ my_skipn L x) (shift_i_i n x c) s'.
  Proof.
    simpl; intros; subst; eapply sorting1_shift_i_i; eauto.
  Qed.
  
  Lemma sorting1_bsorting'' L i s b bs :
    sorting1 L i s ->
    b = get_bsort s ->
    bs = map get_bsort L ->
    bsorting bs i b.
  Proof.
    intros; subst; eapply sorting1_bsorting; eauto.
  Qed.
  
  Lemma wellscoped_ss_cons s L :
    wellscoped_ss L ->
    wellscoped_s (length L) s ->
    wellscoped_ss (s :: L).
  Proof.
    eauto.
  Qed.
  
  (* the type language *)
  
  Inductive ty_const :=
  | TCUnit
  | TCInt
  .

  Inductive ty_bin_op :=
  | TBProd
  | TBSum
  .

  (*
  Definition kind := list bsort.
  Definition KType := @nil bsort.
  Definition KArrow := @cons bsort.
  
  Inductive ty :=
  | TVar (x : var)
  | TConst (cn : ty_const)
  | TBinOp (opr : ty_bin_op) (c1 c2 : ty)
  | TArrow (t1 : ty) (i : idx) (t2 : ty)
  | TAbs (s : bsort) (t : ty)
  | TApp (t : ty) (b : bsort) (i : idx)
  | TQuan (q : quan) (k : kind) (t : ty)
  | TQuanI (q : quan) (s : sort) (t : ty)
  | TRec (k : kind) (t : ty)
  | TNat (i : idx)
  | TArr (t : ty) (len : idx)
  .

  Definition TForall := TQuan QuanForall.
  Definition TExists := TQuan QuanExists.

  Definition TUnit := TConst TCUnit.

  Definition TProd := TBinOp TBProd.
  Definition TSum := TBinOp TBSum.

  Definition TInt := TConst TCInt.

  Require BinIntDef.
  Definition int := BinIntDef.Z.t.

  Definition kctx := list kind.

  Section shift_t.

    Variable n : nat.
  
    Fixpoint shift_i_t (x : var) (b : ty) : ty :=
      match b with
      | TVar y => TVar y
      | TConst cn => TConst cn
      | TBinOp opr c1 c2 => TBinOp opr (shift_i_t x c1) (shift_i_t x c2)
      | TArrow t1 i t2 => TArrow (shift_i_t x t1) (shift_i_i n x i) (shift_i_t x t2)
      | TAbs b t => TAbs b (shift_i_t (1 + x) t)
      | TApp t b i => TApp (shift_i_t x t) b (shift_i_i n x i)
      | TQuan q k c => TQuan q k (shift_i_t x c)
      | TQuanI q s c => TQuanI q (shift_i_s n x s) (shift_i_t (1 + x) c)
      | TRec k t => TRec k (shift_i_t x t)
      | TNat i => TNat (shift_i_i n x i)
      | TArr t i => TArr (shift_i_t x t) (shift_i_i n x i)
      end.

    Fixpoint shift_t_t (x : var) (b : ty) : ty :=
      match b with
      | TVar y =>
        if x <=? y then
          TVar (n + y)
        else
          TVar y
      | TConst cn => TConst cn
      | TBinOp opr c1 c2 => TBinOp opr (shift_t_t x c1) (shift_t_t x c2)
      | TArrow t1 i t2 => TArrow (shift_t_t x t1) i (shift_t_t x t2)
      | TAbs s t => TAbs s (shift_t_t x t)
      | TApp t b i => TApp (shift_t_t x t) b i
      | TQuan q k c => TQuan q k (shift_t_t (1 + x) c)
      | TQuanI q s c => TQuanI q s (shift_t_t x c)
      | TRec k t => TRec k (shift_t_t (1 + x) t)
      | TNat i => TNat i
      | TArr t i => TArr (shift_t_t x t) i
      end.
        
  End shift_t.
*)      

  Inductive kind :=
  | KType
  | KArrow (b : bsort) (k : kind)
  | KArrowT (k1 k2 : kind)
  .
  
  Inductive ty :=
  | TVar (x : var)
  | TConst (cn : ty_const)
  | TBinOp (opr : ty_bin_op) (c1 c2 : ty)
  | TArrow (t1 : ty) (i : idx) (t2 : ty)
  | TAbs (s : bsort) (t : ty)
  | TApp (t : ty) (b : bsort) (i : idx)
  | TQuan (q : quan) (k : kind) (t : ty)
  | TQuanI (q : quan) (s : sort) (t : ty)
  | TRec (k : kind) (t : ty)
  | TNat (i : idx)
  | TArr (t : ty) (len : idx)
  | TAbsT (k : kind) (t : ty)
  | TAppT (t1 t2 : ty)
  .

  Definition TForall := TQuan QuanForall.
  Definition TExists := TQuan QuanExists.

  Definition TUnit := TConst TCUnit.

  Definition TProd := TBinOp TBProd.
  Definition TSum := TBinOp TBSum.

  Definition TInt := TConst TCInt.

  Require BinIntDef.
  Definition int := BinIntDef.Z.t.

  Definition kctx := list kind.

  Section shift_t.

    Variable n : nat.
  
    Fixpoint shift_i_t (x : var) (b : ty) : ty :=
      match b with
      | TVar y => TVar y
      | TConst cn => TConst cn
      | TBinOp opr c1 c2 => TBinOp opr (shift_i_t x c1) (shift_i_t x c2)
      | TArrow t1 i t2 => TArrow (shift_i_t x t1) (shift_i_i n x i) (shift_i_t x t2)
      | TAbs b t => TAbs b (shift_i_t (1 + x) t)
      | TApp t b i => TApp (shift_i_t x t) b (shift_i_i n x i)
      | TQuan q k c => TQuan q k (shift_i_t x c)
      | TQuanI q s c => TQuanI q (shift_i_s n x s) (shift_i_t (1 + x) c)
      | TRec k t => TRec k (shift_i_t x t)
      | TNat i => TNat (shift_i_i n x i)
      | TArr t i => TArr (shift_i_t x t) (shift_i_i n x i)
      | TAbsT k t => TAbsT k (shift_i_t x t)
      | TAppT t1 t2 => TAppT (shift_i_t x t1) (shift_i_t x t2)
      end.

    Fixpoint shift_t_t (x : var) (b : ty) : ty :=
      match b with
      | TVar y =>
        TVar (if x <=? y then
                n + y
              else
                y)
      | TConst cn => TConst cn
      | TBinOp opr c1 c2 => TBinOp opr (shift_t_t x c1) (shift_t_t x c2)
      | TArrow t1 i t2 => TArrow (shift_t_t x t1) i (shift_t_t x t2)
      | TAbs s t => TAbs s (shift_t_t x t)
      | TApp t b i => TApp (shift_t_t x t) b i
      | TQuan q k c => TQuan q k (shift_t_t (1 + x) c)
      | TQuanI q s c => TQuanI q s (shift_t_t x c)
      | TRec k t => TRec k (shift_t_t (1 + x) t)
      | TNat i => TNat i
      | TArr t i => TArr (shift_t_t x t) i
      | TAbsT k t => TAbsT k (shift_t_t (1 + x) t)
      | TAppT t1 t2 => TAppT (shift_t_t x t1) (shift_t_t x t2)
      end.
        
  End shift_t.
      
  Definition shift0_i_t := shift_i_t 1 0.
  Definition shift0_t_t := shift_t_t 1 0.
  
  Fixpoint subst_i_t (x : var) (v : idx) (b : ty) : ty :=
    match b with
    | TVar y => TVar y
    | TConst cn => TConst cn
    | TBinOp opr c1 c2 => TBinOp opr (subst_i_t x v c1) (subst_i_t x v c2)
    | TArrow t1 i t2 => TArrow (subst_i_t x v t1) (subst_i_i x v i) (subst_i_t x v t2)
    | TAbs b t => TAbs b (subst_i_t (1 + x) (shift0_i_i v) t)
    | TApp t b i => TApp (subst_i_t x v t) b (subst_i_i x v i)
    | TQuan q k c => TQuan q k (subst_i_t x v c)
    | TQuanI q s c => TQuanI q (subst_i_s x v s) (subst_i_t (1 + x) (shift0_i_i v) c)
    | TRec k t => TRec k (subst_i_t x v t)
    | TNat i => TNat (subst_i_i x v i)
    | TArr t i => TArr (subst_i_t x v t) (subst_i_i x v i)
    | TAbsT k t => TAbsT k (subst_i_t x v t)
    | TAppT t1 t2 => TAppT (subst_i_t x v t1) (subst_i_t x v t2)
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
    | TBinOp opr c1 c2 => TBinOp opr (subst_t_t x v c1) (subst_t_t x v c2)
    | TArrow t1 i t2 => TArrow (subst_t_t x v t1) i (subst_t_t x v t2)
    | TAbs s t => TAbs s (subst_t_t x (shift0_i_t v) t)
    | TApp t b i => TApp (subst_t_t x v t) b i
    | TQuan q k c => TQuan q k (subst_t_t (1 + x) (shift0_t_t v) c)
    | TQuanI q s c => TQuanI q s (subst_t_t x (shift0_i_t v) c)
    | TRec k t => TRec k (subst_t_t (1 + x) (shift0_t_t v) t)
    | TNat i => TNat i
    | TArr t i => TArr (subst_t_t x v t) i
    | TAbsT k t => TAbsT k (subst_t_t (1 + x) (shift0_t_t v) t)
    | TAppT t1 t2 => TAppT (subst_t_t x v t1) (subst_t_t x v t2)
    end.
  
  Definition subst0_i_t v b := subst_i_t 0 v b.
  Definition subst0_t_t v b := subst_t_t 0 v b.
  
  Section shift_t_proofs.
    
    Hint Resolve shift_i_i_0.
    Hint Resolve shift_i_s_0.
    
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

    Hint Resolve shift_i_i_shift_merge.
    Hint Resolve shift_i_s_shift_merge.
    
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

    Hint Resolve shift_i_i_shift_cut.
    Hint Resolve shift_i_s_shift_cut.
    
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
    
    Lemma shift0_t_t_shift_0 n c :
      shift0_t_t (shift_t_t n 0 c) = shift_t_t (1 + n) 0 c.
    Proof.
      unfold shift0_t_t; intros.
      rewrite shift_t_t_shift_merge; f_equal; la.
    Qed.
    
    Lemma shift0_t_t_shift n x b :
      shift0_t_t (shift_t_t n x b) = shift_t_t n (1 + x) (shift0_t_t b).
    Proof.
      unfold shift0_t_t; intros.
      symmetry.
      rewrite shift_t_t_shift_cut; repeat f_equal; la.
    Qed.

  End shift_t_proofs.
    
  Section subst_t_proofs.
    
    Hint Resolve subst_i_i_shift_avoid.
    Hint Resolve subst_i_s_shift_avoid.
    
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
    
    Hint Resolve subst_i_i_shift_hit.
    Hint Resolve subst_i_s_shift_hit.
    
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
    
    Lemma shift_i_t_shift_t_t :
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
    Qed.

    Lemma subst_t_t_shift_hit n :
      forall b x y v,
        x + n <= y ->
        subst_t_t y (shift_t_t y 0 v) (shift_t_t n x b) = shift_t_t n x (subst_t_t (y - n) (shift_t_t (y - n) 0 v) b).
    Proof.
      induct b;
        simplify; cbn in *;
          try unfold shift0_i_t; repeat rewrite shift_i_t_shift_t_t;
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
    
    Hint Resolve shift_i_i_subst_in.
    Hint Resolve shift_i_s_subst_in.
    
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
          try unfold shift0_i_t; repeat rewrite shift_i_t_shift_t_t;
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
    
    Lemma shift0_t_t_subst_2 x v b :
      shift0_t_t (subst_t_t x v b) = subst_t_t (1 + x) (shift0_t_t v) (shift0_t_t b).
    Proof.
      unfold shift0_t_t, subst0_t_t.
      rewrite shift_t_t_subst_in by la.
      repeat (f_equal; try la).
    Qed.

    Hint Resolve shift_i_i_subst_out.
    Hint Resolve shift_i_s_subst_out.
    
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
    
    Opaque le_lt_dec.
    
    Lemma shift_t_t_subst_out n :
      forall b v x y,
        x <= y ->
        shift_t_t n y (subst_t_t x v b) = subst_t_t x (shift_t_t n y v) (shift_t_t n (S y) b).
    Proof.
      induct b;
        simplify;
        cbn in *;
        try unfold shift0_i_t; repeat rewrite shift_i_t_shift_t_t;
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
    
    Hint Resolve subst_i_i_subst.
    Hint Resolve subst_i_s_subst.
    
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
    
    Lemma shift_i_t_subst_t_t :
      forall b x2 n x1 v,
        shift_i_t x2 n (subst_t_t x1 v b) = subst_t_t x1 (shift_i_t x2 n v) (shift_i_t x2 n b).
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
        (* Case TVar *)
        repeat match goal with
               | |- context [?a <=? ?b] => cases (a <=? b); simplify; cbn
               | |- context [?a <=>? ?b] => cases (a <=>? b); simplify; cbn
               end; try solve [f_equal; la].
      }
      {
        (* Case TAbs *)
        rewrite IHb by la.
        unfold shift0_i_t.
        repeat rewrite shift_i_t_shift_cut by la.
        simpl.
        repeat f_equal.
        la.
      }
      {
        (* Case TQuan *)
        rewrite IHb by la.
        unfold shift0_t_t.
        repeat rewrite shift_i_t_shift_t_t.
        eauto.
      }      
      {
        (* Case TQuanI *)
        rewrite IHb by la.
        unfold shift0_i_t.
        repeat rewrite shift_i_t_shift_cut by la.
        simpl.
        repeat f_equal.
        la.
      }      
      {
        (* Case TRec *)
        rewrite IHb by la.
        unfold shift0_t_t.
        repeat rewrite shift_i_t_shift_t_t.
        eauto.
      }      
      {
        (* Case TAbsT *)
        rewrite IHb by la.
        unfold shift0_t_t.
        repeat rewrite shift_i_t_shift_t_t.
        eauto.
      }      
    Qed.

    Lemma subst_t_t_subst :
      forall b v1 v2 x y,
        x <= y ->
        subst_t_t y v2 (subst_t_t x v1 b) = subst_t_t x (subst_t_t y v2 v1) (subst_t_t (S y) (shift_t_t 1 x v2) b).
    Proof.
      induct b;
        simplify;
        cbn in *;
        try unfold shift0_i_t; repeat rewrite shift_i_t_shift_t_t;
        try solve [eauto |
                   f_equal; eauto |
                   erewrite H by la; repeat f_equal; eauto with db_la |
                   rewrite IHb by la; rewrite shift_i_t_subst_t_t; eauto |
                   repeat rewrite shift0_t_t_shift; simplify;
                   repeat rewrite shift0_t_t_subst_2; simplify;
                   repeat replace (S (y - n)) with (S y - n) by la;
                   f_equal;
                   eauto with db_la
                  ].
      {
        (* Case TVar *)
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
    
  End subst_t_proofs.

  Notation idxeq L i i' b := (interp_prop L (PEq b i i')).
  
  (* parallel reduction *)
  
  Inductive par : ty -> ty -> Prop :=
  | PaRBinOp opr t1 t2 t1' t2' :
      par t1 t1' ->
      par t2 t2' ->
      par (TBinOp opr t1 t2) (TBinOp opr t1' t2')
  | PaRArrow t1 i t2 t1' t2':
      par t1 t1' ->
      par t2 t2' ->
      par (TArrow t1 i t2) (TArrow t1' i t2')
  | PaRAbs b t t' :
      par t t' ->
      par (TAbs b t) (TAbs b t')
  | PaRApp t b i t' :
      par t t' ->
      par (TApp t b i) (TApp t' b i)
  | PaRQuan quan k t t' :
      par t t' ->
      par (TQuan quan k t) (TQuan quan k t')
  | PaRQuanI quan s t t' :
      par t t' ->
      par (TQuanI quan s t) (TQuanI quan s t')
  | PaRRec k c c' :
      par c c' ->
      par (TRec k c) (TRec k c')
  | PaRArr t i t' :
      par t t' ->
      par (TArr t i) (TArr t' i)
  | PaRBeta s t b i t' :
      par t t' ->
      par (TApp (TAbs s t) b i) (subst0_i_t i t')
  | PaRRefl t :
      par t t
  | PaRAbsT k t t' :
      par t t' ->
      par (TAbsT k t) (TAbsT k t')
  | PaRAppT t1 t2 t1' t2' :
      par t1 t1' ->
      par t2 t2' ->
      par (TAppT t1 t2) (TAppT t1' t2')
  | PaRBetaT k t1 t2 t1' t2' :
      par t1 t1' ->
      par t2 t2' ->
      par (TAppT (TAbsT k t1) t2) (subst0_t_t t2' t1')
  .

  Hint Constructors par.

  (* congruence *)

  Inductive cong : sctx -> ty -> ty -> Prop :=
  | CongBinOp L opr t1 t2 t1' t2' :
      cong L t1 t1' ->
      cong L t2 t2' ->
      cong L (TBinOp opr t1 t2) (TBinOp opr t1' t2')
  | CongArrow L t1 i t2 t1' i' t2':
      cong L t1 t1' ->
      idxeq L i i' BSTime ->
      cong L t2 t2' ->
      cong L (TArrow t1 i t2) (TArrow t1' i' t2')
  | CongAbs L b t t' :
      cong (SBaseSort b :: L) t t' ->
      cong L (TAbs b t) (TAbs b t')
  | CongApp L t b i t' i' :
      cong L t t' ->
      idxeq L i i' b ->
      cong L (TApp t b i) (TApp t' b i')
  | CongQuan L quan k t t' :
      cong L t t' ->
      cong L (TQuan quan k t) (TQuan quan k t')
  | CongQuanI L quan s t s' t' :
      sorteq L s s' ->
      cong (s :: L) t t' ->
      cong L (TQuanI quan s t) (TQuanI quan s' t')
  | CongRec L k c c' :
      cong L c c' ->
      cong L (TRec k c) (TRec k c')
  | CongNat L i i' :
      idxeq L i i' BSNat ->
      cong L (TNat i) (TNat i')
  | CongArr L t i t' i' :
      cong L t t' ->
      idxeq L i i' BSNat ->
      cong L (TArr t i) (TArr t' i')
  | CongVar L x :
      cong L (TVar x) (TVar x)
  | CongConst L cn :
      cong L (TConst cn) (TConst cn)
  | CongAbsT L k t t' :
      cong L t t' ->
      cong L (TAbsT k t) (TAbsT k t')
  | CongAppT L t1 t2 t1' t2' :
      cong L t1 t1' ->
      cong L t2 t2' ->
      cong L (TAppT t1 t2) (TAppT t1' t2')
  .

  Hint Constructors cong.

  Lemma idxeq_refl L b i : interp_prop L (PEq b i i).
  Proof.
    unfold interp_prop.
    cbn in *.
    eapply forall_ignore_premise.
    rewrite dedup_lift2.
    eapply forall_lift1.
    eauto.
  Qed.
  
  Lemma idxeq_sym L b i i' :
    interp_prop L (PEq b i i') ->
    interp_prop L (PEq b i' i).
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

  Lemma idxeq_trans L bsort a b c :
    interp_prop L (PEq bsort a b) ->
    interp_prop L (PEq bsort b c)%idx ->
    interp_prop L (PEq bsort a c)%idx.
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

  Hint Resolve idxeq_refl idxeq_sym idxeq_trans : db_idxeq.
  Hint Resolve sorteq_refl sorteq_sym sorteq_trans : db_sorteq.
  
  Hint Extern 0 (wellscoped_ss []) => econstructor.
  Hint Extern 0 (wfsorts1 []) => econstructor.
  
  Lemma forall_lift4_lift4 :
    forall bs A1 A2 A3 A4 P1 P2 P3 P4 (f1 : A1 -> A2 -> A3 -> A4 -> Prop) (f2 : A1 -> A2 -> A3 -> A4 -> Prop),
      (forall a1 a2 a3 a4, f1 a1 a2 a3 a4 -> f2 a1 a2 a3 a4) ->
      forall_ bs (lift4 bs f1 P1 P2 P3 P4) ->
      forall_ bs (lift4 bs f2 P1 P2 P3 P4).
  Proof.
    induct bs; simplify; eauto.
    rewrite fuse_lift1_lift4 in *.
    eapply IHbs; eauto.
    simplify.
    eauto.
  Qed.
  
  Lemma forall_subst_eqv_reflex :
    forall bs x b_b (f : _ -> _ -> Prop) (body : interp_bsorts bs b_b) b_v (v v' : interp_bsorts (skipn (S x) bs) (interp_bsort b_v)) (Heq : firstn x bs ++ skipn (S x) bs = removen x bs),
      (forall x, f x x) ->
      let bs' := removen x bs in
      imply_
        bs'
        (lift2 _ eq (cast _ _ Heq (shift0 _ _ v)) (cast _ _ Heq (shift0 _ _ v')))
        (lift2 _ f (subst x bs v body) (subst x bs v' body)).
  Proof.
    simpl.
    induct bs; simpl; intros x b_b f body b_v v v' Heq Hf; try la.
    {
      eapply forall_ignore_premise.
      simpl.
      eauto.
    }
    destruct x; simpl in *.
    {
      rewrite fuse_lift2_lift2_1.
      rewrite fuse_lift3_lift2_3.
      repeat rewrite cast_refl_eq.
      rewrite dedup_lift4_1_3.
      unfold imply_.
      rewrite fuse_lift2_lift2_1.
      rewrite fuse_lift3_lift3_3.
      rewrite dedup_lift5_1_4.
      rewrite dedup_lift4_2_4.
      eapply forall_lift3.
      simpl; intros.
      subst.
      eauto.
    }
    {
      unfold imply_ in *.
      simpl in *.
      repeat rewrite <- lift1_shift0.
      repeat rewrite cast_lift1.
      repeat rewrite fuse_lift1_lift1.
      rewrite fuse_lift1_lift2.
      repeat rewrite fuse_lift2_lift1_1.
      repeat rewrite fuse_lift2_lift1_2.
      set (skipn_bs := match bs with
                                        | [] => []
                                        | _ :: l => skipn x l
                                        end) in *.
      set (Heq' := f_equal
                (fun t : list bsort =>
                 match t with
                 | [] => firstn x bs ++ skipn_bs
                 | _ :: x0 => x0
                 end) Heq) in *.
      specialize (IHbs x _ (fun a b => forall x, f (a x) (b x)) body b_v v v' Heq').
      subst skipn_bs Heq'.
      set (skipn_bs := match bs with
                                        | [] => []
                                        | _ :: l => skipn x l
                                        end) in *.
      set (Heq' := f_equal
                (fun t : list bsort =>
                 match t with
                 | [] => firstn x bs ++ skipn_bs
                 | _ :: x0 => x0
                 end) Heq) in *.
      repeat rewrite fuse_lift2_lift2_1 in *.
      repeat rewrite fuse_lift3_lift2_3 in *.
      eapply forall_lift4_lift4; [| eapply IHbs]; eauto.
    }
  Qed.

  Lemma forall_subst_eqv_eq :
    forall bs x b_b (body : interp_bsorts bs b_b) b_v (v v' : interp_bsorts (skipn (S x) bs) (interp_bsort b_v)) (Heq : firstn x bs ++ skipn (S x) bs = removen x bs),
      let bs' := removen x bs in
      imply_
        bs'
        (lift2 _ eq (cast _ _ Heq (shift0 _ _ v)) (cast _ _ Heq (shift0 _ _ v')))
        (lift2 _ eq (subst x bs v body) (subst x bs v' body)).
  Proof.
    simpl.
    intros; eapply forall_subst_eqv_reflex; eauto.
  Qed.

  Lemma forall_subst_eqv_iff :
    forall bs x (body : interp_bsorts bs Prop) b_v (v v' : interp_bsorts (skipn (S x) bs) (interp_bsort b_v)) (Heq : firstn x bs ++ skipn (S x) bs = removen x bs),
      let bs' := removen x bs in
      imply_
        bs'
        (lift2 _ eq (cast _ _ Heq (shift0 _ _ v)) (cast _ _ Heq (shift0 _ _ v')))
        (lift2 _ iff (subst x bs v body) (subst x bs v' body)).
  Proof.
    simpl.
    intros; eapply forall_subst_eqv_reflex; eauto.
    propositional.
  Qed.

  Lemma interp_shift_i_i_eq_shift_0 i bs_new bs b n :
    let bs' := bs_new ++ bs in
    wellscoped_i (length bs) i ->
    n = length bs_new ->
    interp_idx (shift_i_i n 0 i) bs' b = shift0 bs_new bs (interp_idx i bs b).
  Proof.
    simpl.
    intros.
    eapply interp_shift_i_i_eq_shift with (x := 0); eauto.
  Qed.
  
  Lemma subst_i_i_eqv_eqv L body body' b_b  x s v v' :
    idxeq L body body' b_b->
    nth_error L x = Some s ->
    idxeq (my_skipn L (1 + x)) v v' (get_bsort s) ->
    sorting1 (my_skipn L (1 + x)) v s ->
    sorting1 (my_skipn L (1 + x)) v' s ->
    bsorting (map get_bsort L) body b_b ->
    bsorting (map get_bsort L) body' b_b ->
    wfsorts1 L ->
    idxeq (subst_i_ss v (firstn x L) ++ my_skipn L (1 + x)) (subst_i_i x (shift_i_i x 0 v) body) (subst_i_i x (shift_i_i x 0 v') body') b_b.
  Proof.
    intros Hbb' Hx Hvv' Hv Hv' Hb Hb' HL.
    assert (HL2 : wfsorts1 (my_skipn L (1 + x))).
    {
      rewrite <- skipn_my_skipn.
      eapply all_sorts_skipn; eauto.
    }
    eapply idxeq_trans.
    {
      eapply interp_subst_i_p in Hbb'; eauto.
    }
    eapply interp_prop_shift_i_p with (x := 0) (ls := subst_i_ss v (firstn x L))in Hvv'; eauto using wfsorts1_wellscoped_ss, sorting1_wellscoped_i with db_la.
    copy Hx Hcmp.
    eapply nth_error_Some_lt in Hcmp.
    repeat rewrite length_subst_i_ss in *.
    repeat rewrite length_firstn_le in * by la.
    simpl in *.
    repeat rewrite my_skipn_0 in *.
    set (L' := subst_i_ss v (firstn x L) ++ my_skipn L (S x)) in *.
    unfold idxeq in *.
    simpl in *.
    set (bs' := map get_bsort L') in *.
    set (bs := map get_bsort L) in *.
    eapply forall_trans; [eapply Hvv' |].
    assert (Hbs' : bs' = removen x bs).
    {
      subst bs bs' L'.
      rewrite map_app.
      rewrite get_bsort_subst_i_ss.
      rewrite <- map_app.
      rewrite <- removen_firstn_my_skipn.
      rewrite map_removen.
      eauto.
    }
    assert (wellscoped_i (length (skipn (S x) bs)) v).
    {
      rewrite skipn_my_skipn in *.
      subst bs.
      rewrite <- map_my_skipn.
      rewrite map_length.
      eapply sorting1_wellscoped_i; eauto.
    }
    assert (wellscoped_i (length (skipn (S x) bs)) v').
    {
      rewrite skipn_my_skipn in *.
      subst bs.
      rewrite <- map_my_skipn.
      rewrite map_length.
      eapply sorting1_wellscoped_i; eauto.
    }
    assert (x = length (firstn x bs)).
    {
      subst bs.
      rewrite <- map_firstn.
      rewrite map_length.
      rewrite length_firstn_le by la.
      eauto.
    }
    assert (nth_error bs x = Some (get_bsort s)).
    {
      subst bs.
      erewrite map_nth_error; eauto.
    }
    assert (bsorting (skipn (S x) bs) v (get_bsort s)).
    {
      rewrite skipn_my_skipn in *.
      subst bs.
      rewrite <- map_my_skipn.
      eapply sorting1_bsorting; eauto.
    }
    assert (bsorting (skipn (S x) bs) v' (get_bsort s)).
    {
      rewrite skipn_my_skipn in *.
      subst bs.
      rewrite <- map_my_skipn.
      eapply sorting1_bsorting; eauto.
    }
    rewrite Hbs' in *.
    repeat erewrite interp_subst_i_i; eauto.
    eapply forall_trans; [| eapply forall_subst_eqv_eq].
    symmetry in Hbs'.
    eapply forall_cast_elim with (bs2 := firstn x bs ++ skipn (S x) bs).
    repeat rewrite cast_lift2.
    repeat rewrite cast_roundtrip.
    repeat rewrite cast_interp_idx.
    repeat rewrite interp_shift_i_i_eq_shift_0; eauto.
    eapply forall_imply_refl.
    Grab Existential Variables.
    {
      rewrite removen_firstn_skipn; eauto.
    }
    {
      rewrite removen_firstn_skipn; eauto.
    }
  Qed.

  Notation propeq L p p' := (interp_prop L (p <===> p')%idx).
    
  Lemma subst_i_p_eqv_eqv L body body' x s v v' :
    propeq L body body' ->
    nth_error L x = Some s ->
    idxeq (my_skipn L (1 + x)) v v' (get_bsort s) ->
    sorting1 (my_skipn L (1 + x)) v s ->
    sorting1 (my_skipn L (1 + x)) v' s ->
    wfprop1 (map get_bsort L) body ->
    wfprop1 (map get_bsort L) body' ->
    wfsorts1 L ->
    propeq (subst_i_ss v (firstn x L) ++ my_skipn L (1 + x)) (subst_i_p x (shift_i_i x 0 v) body) (subst_i_p x (shift_i_i x 0 v') body').
  Proof.
    intros Hbb' Hx Hvv' Hv Hv' Hb Hb' HL.
    assert (HL2 : wfsorts1 (my_skipn L (1 + x))).
    {
      rewrite <- skipn_my_skipn.
      eapply all_sorts_skipn; eauto.
    }
    eapply interp_prop_iff_trans.
    {
      eapply interp_subst_i_p with (c := v) in Hbb'; simpl in *; eauto.
      econstructor; eauto.
    }
    eapply interp_prop_shift_i_p with (x := 0) (ls := subst_i_ss v (firstn x L))in Hvv'; eauto using wfsorts1_wellscoped_ss, sorting1_wellscoped_i with db_la.
    copy Hx Hcmp.
    eapply nth_error_Some_lt in Hcmp.
    repeat rewrite length_subst_i_ss in *.
    repeat rewrite length_firstn_le in * by la.
    simpl in *.
    repeat rewrite my_skipn_0 in *.
    set (L' := subst_i_ss v (firstn x L) ++ my_skipn L (S x)) in *.
    unfold idxeq in *.
    simpl in *.
    set (bs' := map get_bsort L') in *.
    set (bs := map get_bsort L) in *.
    eapply forall_trans; [eapply Hvv' |].
    assert (Hbs' : bs' = removen x bs).
    {
      subst bs bs' L'.
      rewrite map_app.
      rewrite get_bsort_subst_i_ss.
      rewrite <- map_app.
      rewrite <- removen_firstn_my_skipn.
      rewrite map_removen.
      eauto.
    }
    assert (wellscoped_i (length (skipn (S x) bs)) v).
    {
      rewrite skipn_my_skipn in *.
      subst bs.
      rewrite <- map_my_skipn.
      rewrite map_length.
      eapply sorting1_wellscoped_i; eauto.
    }
    assert (wellscoped_i (length (skipn (S x) bs)) v').
    {
      rewrite skipn_my_skipn in *.
      subst bs.
      rewrite <- map_my_skipn.
      rewrite map_length.
      eapply sorting1_wellscoped_i; eauto.
    }
    assert (x = length (firstn x bs)).
    {
      subst bs.
      rewrite <- map_firstn.
      rewrite map_length.
      rewrite length_firstn_le by la.
      eauto.
    }
    assert (nth_error bs x = Some (get_bsort s)).
    {
      subst bs.
      erewrite map_nth_error; eauto.
    }
    assert (bsorting (skipn (S x) bs) v (get_bsort s)).
    {
      rewrite skipn_my_skipn in *.
      subst bs.
      rewrite <- map_my_skipn.
      eapply sorting1_bsorting; eauto.
    }
    assert (bsorting (skipn (S x) bs) v' (get_bsort s)).
    {
      rewrite skipn_my_skipn in *.
      subst bs.
      rewrite <- map_my_skipn.
      eapply sorting1_bsorting; eauto.
    }
    rewrite Hbs' in *.
    eapply forall_trans; [| eapply forall_trans]; [| eapply forall_subst_eqv_iff|].
    Focus 2.
    {
      eapply forall_iff_imply.
      eapply forall_iff_sym.
      eapply forall_iff_lift2; try eapply forall_subst_i_p_iff_subst; eauto.
      unfold iff; propositional.
    }
    Unfocus.
    symmetry in Hbs'.
    eapply forall_cast_elim with (bs2 := firstn x bs ++ skipn (S x) bs).
    repeat rewrite cast_lift2.
    repeat rewrite cast_roundtrip.
    repeat rewrite cast_interp_idx.
    repeat rewrite interp_shift_i_i_eq_shift_0; eauto.
    eapply forall_imply_refl.
    Grab Existential Variables.
    {
      rewrite removen_firstn_skipn; eauto.
    }
    {
      rewrite removen_firstn_skipn; eauto.
    }
  Qed.
    
  Lemma subst_i_s_eqv_eqv L body body' :
    sorteq L body body' ->
    forall x s v v',
      nth_error L x = Some s ->
      idxeq (my_skipn L (1 + x)) v v' (get_bsort s) ->
      sorting1 (my_skipn L (1 + x)) v s ->
      sorting1 (my_skipn L (1 + x)) v' s ->
      wfsort1 (map get_bsort L) body ->
      wfsort1 (map get_bsort L) body' ->
      wfsorts1 L ->
      sorteq (subst_i_ss v (firstn x L) ++ my_skipn L (1 + x)) (subst_i_s x (shift_i_i x 0 v) body) (subst_i_s x (shift_i_i x 0 v') body').
  Proof.
    induct 1;
      simpl; try rename x into y; try rename s into s'; try rename s into s''; intros x s v v' Hx Hvv' Hv Hv' Hb Hb' HL; try solve [invert Hb; invert Hb'; econstructor; eauto using subst_i_i_eqv_eqv].
    repeat rewrite shift0_i_i_shift_0.
    invert Hb; invert Hb'; econstructor; eauto using subst_i_i_eqv_eqv.
    eapply subst_i_p_eqv_eqv with (x := S x) (L := SBaseSort _ :: _); eauto.
  Qed.

  Inductive kinding1 : sctx -> kctx -> ty -> kind -> Prop :=
  | Kdg1Var L K x k :
      nth_error K x = Some k ->
      kinding1 L K (TVar x) k
  | Kdg1Const L K cn :
      kinding1 L K (TConst cn) KType
  | Kdg1BinOp L K opr c1 c2 :
      kinding1 L K c1 KType ->
      kinding1 L K c2 KType ->
      kinding1 L K (TBinOp opr c1 c2) KType
  | Kdg1Arrow L K t1 i t2 :
      kinding1 L K t1 KType ->
      sorting1 L i STime ->
      kinding1 L K t2 KType ->
      kinding1 L K (TArrow t1 i t2) KType
  | Kdg1Abs L K b t k :
      kinding1 (SBaseSort b :: L) K t k ->
      kinding1 L K (TAbs b t) (KArrow b k)
  | Kdg1App L K t b i k :
      kinding1 L K t (KArrow b k) ->
      sorting1 L i (SBaseSort b) ->
      kinding1 L K (TApp t b i) k
  | Kdg1Quan L K quan k c :
      kinding1 L (k :: K) c KType ->
      kinding1 L K (TQuan quan k c) KType
  | Kdg1QuanI L K quan s c :
      wfsort1 (map get_bsort L) s ->
      kinding1 (s :: L) K c KType ->
      kinding1 L K (TQuanI quan s c) KType
  | Kdg1Rec L K k c :
      kinding1 L (k :: K) c k ->
      kinding1 L K (TRec k c) k
  | Kdg1Nat L K i :
      sorting1 L i SNat ->
      kinding1 L K (TNat i) KType
  | Kdg1Arr L K t i :
      kinding1 L K t KType ->
      sorting1 L i SNat ->
      kinding1 L K (TArr t i) KType
  | Kdg1AbsT L K t k1 k2 :
      kinding1 L (k1 :: K) t k2 ->
      kinding1 L K (TAbsT k1 t) (KArrowT k1 k2)
  | Kdg1AppT L K t1 t2 k1 k2 :
      kinding1 L K t1 (KArrowT k1 k2) ->
      kinding1 L K t2 k1 ->
      kinding1 L K (TAppT t1 t2) k2
  .

  Hint Constructors kinding1.

  Inductive bkinding : list bsort -> list kind -> ty -> kind -> Prop :=
  | BKdg1Var L K x k :
      nth_error K x = Some k ->
      bkinding L K (TVar x) k
  | BKdg1Const L K cn :
      bkinding L K (TConst cn) KType
  | BKdg1BinOp L K opr c1 c2 :
      bkinding L K c1 KType ->
      bkinding L K c2 KType ->
      bkinding L K (TBinOp opr c1 c2) KType
  | BKdg1Arrow L K t1 i t2 :
      bkinding L K t1 KType ->
      bsorting L i BSTime ->
      bkinding L K t2 KType ->
      bkinding L K (TArrow t1 i t2) KType
  | BKdg1Abs L K b t k :
      bkinding (b :: L) K t k ->
      bkinding L K (TAbs b t) (KArrow b k)
  | BKdg1App L K t b i k :
      bkinding L K t (KArrow b k) ->
      bsorting L i b ->
      bkinding L K (TApp t b i) k
  | BKdg1Quan L K quan k c :
      bkinding L (k :: K) c KType ->
      bkinding L K (TQuan quan k c) KType
  | BKdg1QuanI L K quan s c :
      wfsort1 L s ->
      bkinding (get_bsort s :: L) K c KType ->
      bkinding L K (TQuanI quan s c) KType
  | BKdg1Rec L K k c :
      bkinding L (k :: K) c k ->
      bkinding L K (TRec k c) k
  | BKdg1Nat L K i :
      bsorting L i BSNat ->
      bkinding L K (TNat i) KType
  | BKdg1Arr L K t i :
      bkinding L K t KType ->
      bsorting L i BSNat ->
      bkinding L K (TArr t i) KType
  | BKdg1AbsT L K t k1 k2 :
      bkinding L (k1 :: K) t k2 ->
      bkinding L K (TAbsT k1 t) (KArrowT k1 k2)
  | BKdg1AppT L K t1 t2 k1 k2 :
      bkinding L K t1 (KArrowT k1 k2) ->
      bkinding L K t2 k1 ->
      bkinding L K (TAppT t1 t2) k2
  .

  Hint Constructors bkinding.

  Lemma kinding1_bkinding L K t k :
    kinding1 L K t k ->
    bkinding (map get_bsort L) K t k.
  Proof.
    induct 1; simpl; eauto using sorting1_bsorting'.
  Qed.

  Lemma cong_subst_i_t :
    forall L body body',
      cong L body body' ->
      forall x s v v' k_b k_b' K K',
        nth_error L x = Some s ->
        idxeq (my_skipn L (1 + x)) v v' (get_bsort s) ->
        sorting1 (my_skipn L (1 + x)) v s ->
        sorting1 (my_skipn L (1 + x)) v' s ->
        bkinding (map get_bsort L) K body k_b ->
        bkinding (map get_bsort L) K' body' k_b' ->
        wfsorts1 L ->
        cong (subst_i_ss v (firstn x L) ++ my_skipn L (1 + x)) (subst_i_t x (shift_i_i x 0 v) body) (subst_i_t x (shift_i_i x 0 v') body').
  Proof.
    induct 1;
      simpl; try rename x into y; try rename s into s'; try rename s into s''; intros x s v v' k_b k_b' K K' Hx Hvv' Hv Hv' Hb Hb' HL; try solve [invert Hb; invert Hb'; econstructor; eauto using subst_i_i_eqv_eqv, subst_i_s_eqv_eqv].
    {
      (* Case TAbs *)
      invert Hb; invert Hb'.
      repeat rewrite shift0_i_i_shift_0.
      econstructor; eauto.
      eapply IHcong with (x := S x); eauto.
    }
    {
      (* Case TQuanI *)
      invert Hb; invert Hb'.
      repeat rewrite shift0_i_i_shift_0.
      econstructor; eauto.
      {
        eapply subst_i_s_eqv_eqv; eauto.
      }
      specialize (IHcong (S x) s v v').
      simpl in *.
      copy Hx Hcmp.
      eapply nth_error_Some_lt in Hcmp.
      rewrite length_firstn_le in * by la.
      eapply IHcong; eauto.
      invert H; simpl in *; eauto.
    }
  Qed.

  Lemma cong_subst_i_t_0 L body body' s v v' k_b k_b' K K' :
    cong (s :: L) body body' ->
    idxeq L v v' (get_bsort s) ->
    sorting1 L v s ->
    sorting1 L v' s ->
    bkinding (map get_bsort (s :: L)) K body k_b ->
    bkinding (map get_bsort (s :: L)) K' body' k_b' ->
    wfsort1 (map get_bsort L) s ->
    wfsorts1 L ->
    cong L (subst_i_t 0 v body) (subst_i_t 0 v' body').
  Proof.
    intros Hbb'; intros; eapply cong_subst_i_t with (x := 0) (L := _ :: _) in Hbb'; simpl in *; try rewrite my_skipn_0 in *; eauto.
    repeat rewrite shift_i_i_0 in *; eauto.
  Qed.

  Lemma bkinding_subst_i_t :
    forall L K body k_b,
      bkinding L K body k_b ->
      forall x b_v v,
        nth_error L x = Some b_v ->
        bsorting (my_skipn L (1 + x)) v b_v ->
        bkinding (removen x L) K (subst_i_t x (shift_i_i x 0 v) body) k_b.
  Proof.
    induct 1;
      simpl; try rename x into y; try rename s into b; intros x b_v v Hx Hv; simpl in *; try solve [econstructor; eauto using bsorting_subst_i_i].
    {
      (* Case TAbs *)
      repeat rewrite shift0_i_i_shift_0.
      econstructor; eauto.
      eapply IHbkinding with (x := S x); eauto.
    }
    {
      (* Case TQuanI *)
      repeat rewrite shift0_i_i_shift_0.
      econstructor; eauto using wfsort1_subst_i_s.
      rewrite get_bsort_subst_i_s.
      eapply IHbkinding with (x := S x); eauto.
    }
  Qed.
  
  Lemma bkinding_subst_i_t_0 L K body k_b b_v v :
    bkinding (b_v :: L) K body k_b ->
    bsorting L v b_v ->
    bkinding L K (subst_i_t 0 v body) k_b.
  Proof.
    intros Hb Hv.
    eapply bkinding_subst_i_t with (x := 0) (L := _ :: _) in Hb; simpl in *; try rewrite my_skipn_0; eauto.
    rewrite shift_i_i_0 in *.
    eauto.
  Qed.
  
  Ltac unfold_all :=
    repeat match goal with
           | H := _ |- _ => unfold H in *; clear H
           end.

  Lemma nth_error_insert' A G :
    forall x y ls (t : A),
      nth_error G y = Some t ->
      x <= y ->
      nth_error (insert ls x G) (length ls + y) = Some t.
  Proof.
    intros.
    rewrite insert_firstn_my_skipn.
    erewrite nth_error_insert; eauto.
  Qed.

  Lemma nth_error_before_insert' A G y (t : A) x ls :
    nth_error G y = Some t ->
    y < x ->
    nth_error (insert ls x G) y = Some t.
  Proof.
    intros.
    rewrite insert_firstn_my_skipn.
    erewrite nth_error_before_insert; eauto.
  Qed.

  Lemma bkinding_shift_t_t :
    forall L K c k,
      bkinding L K c k ->
      forall x ls,
        let n := length ls in
        bkinding L (insert ls x K) (shift_t_t n x c) k.
  Proof.
    induct 1; unfold_all;
      simplify; cbn in *; try solve [econstructor; eauto].
    {
      (* Case TVar *)
      copy H HnltL.
      eapply nth_error_Some_lt in HnltL.
      rename x0 into y.
      cases (y <=? x).
      {
        econstructor.
        erewrite nth_error_insert'; eauto.
      }
      {
        econstructor.
        erewrite nth_error_before_insert'; eauto.
      }
    }
    {
      (* Case TQuan *)
      econstructor; eauto.
      eapply IHbkinding with (x := S x); eauto with db_la.
    }
    {
      (* Case TRec *)
      econstructor; eauto.
      eapply IHbkinding with (x := S x); eauto with db_la.
    }
    {
      (* Case TAbsT *)
      econstructor; eauto.
      eapply IHbkinding with (x := S x); eauto with db_la.
    }
  Qed.

  Lemma bkinding_shift_t_t' :
    forall L K c k x ls n,
      bkinding L K c k ->
      n = length ls ->
      bkinding L (insert ls x K) (shift_t_t n x c) k.
  Proof.
    intros; subst; eapply bkinding_shift_t_t; eauto.
  Qed.

  Lemma bkinding_shift_i_t :
    forall L K c k,
      bkinding L K c k ->
      forall x ls,
        let n := length ls in
        x <= length L ->
        bkinding (firstn x L ++ ls ++ my_skipn L x) K (shift_i_t n x c) k.
  Proof.
    simpl.
    induct 1;
      simpl; try rename x into y; intros x ls Hx; cbn in *; try solve [econstructor; eauto using bsorting_shift_i_i].
    {
      (* Case TAbs *)
      econstructor; eauto.
      eapply IHbkinding with (x := S x); eauto with db_la.
    }
    {
      (* Case TQuanI *)
      econstructor; eauto using wfsort1_shift_i_s.
      specialize (IHbkinding (S x) ls).
      simpl in *.
      rewrite get_bsort_shift_i_s.
      eapply IHbkinding; eauto using wfsort1_wellscoped_s' with db_la.
    }
  Qed.

  Lemma bkinding_shift_i_t_1_0 L K c k s :
    bkinding L K c k ->
    bkinding (s :: L) K (shift_i_t 1 0 c) k.
  Proof.
    intros Hbody.
    eapply bkinding_shift_i_t with (x := 0) (ls := [s]) in Hbody; eauto with db_la.
    simpl in *.
    rewrite my_skipn_0 in *.
    eauto.
  Qed.

  Lemma bkinding_subst_t_t :
    forall L K body k_b,
      bkinding L K body k_b ->
      forall x k_v v ,
        nth_error K x = Some k_v ->
        bkinding L (my_skipn K (1 + x)) v k_v ->
        bkinding L (removen x K) (subst_t_t x (shift_t_t x 0 v) body) k_b.
  Proof.
    induct 1;
      simpl; try rename x into y; intros x k_v v Hx Hv; subst; try solve [econstructor; eauto].
    {
      (* Case TVar *)
      copy Hx Hcmp.
      eapply nth_error_Some_lt in Hcmp.
      cases (y <=>? x); eauto with db_la.
      {
        econstructor.
        erewrite removen_lt by eauto with db_la.
        eauto.
      }
      {
        rewrite removen_firstn_my_skipn.
        subst.
        assert (k_v = k) by equality.
        subst.
        eapply bkinding_shift_t_t' with (x := 0); eauto with db_la; try rewrite length_firstn_le by la; eauto.
      }
      {
        econstructor.
        erewrite removen_gt by eauto with db_la.
        eauto.
      }
    }
    {
      (* Case TAbs *)
      econstructor; eauto with db_la.
      unfold shift0_i_t.
      rewrite shift_i_t_shift_t_t.
      eapply IHbkinding; eauto with db_la.
      eapply bkinding_shift_i_t_1_0; eauto.
    }
    {
      (* Case TQuan *)
      unfold shift0_t_t.
      rewrite shift_t_t_shift_merge by la.
      econstructor; eauto with db_la.
      rewrite plus_comm.
      eapply IHbkinding with (x := S x); eauto with db_la.
    }
    {
      (* Case TQuanI *)
      econstructor; eauto with db_la.
      unfold shift0_i_t.
      rewrite shift_i_t_shift_t_t.
      eapply IHbkinding; eauto using wfsort1_wellscoped_s' with db_la.
      eapply bkinding_shift_i_t_1_0; eauto.
    }
    {
      (* Case TRec *)
      unfold shift0_t_t.
      rewrite shift_t_t_shift_merge by la.
      econstructor; eauto with db_la.
      rewrite plus_comm.
      eapply IHbkinding with (x := S x); eauto with db_la.
    }
    {
      (* Case TAbsT *)
      unfold shift0_t_t.
      rewrite shift_t_t_shift_merge by la.
      econstructor; eauto with db_la.
      rewrite plus_comm.
      eapply IHbkinding with (x := S x); eauto with db_la.
    }
  Qed.
  
  Lemma bkinding_subst_t_t_0 L K body k_b k_v v :
    bkinding L (k_v :: K) body k_b ->
    bkinding L K v k_v ->
    bkinding L K (subst_t_t 0 v body) k_b.
  Proof.
    intros Hb Hv.
    eapply bkinding_subst_t_t with (x := 0) (K := _ :: _) in Hb; simpl in *; try rewrite my_skipn_0; eauto.
    rewrite shift_t_t_0 in *.
    eauto.
  Qed.
  
  Ltac invert_bkindings :=
    repeat match goal with
             H : bkinding _ _ _ _ |- _ => invert1 H
           end.
  
  Lemma par_preserves_bkinding a b :
    par a b ->
    forall L K k,
      bkinding L K a k ->
      bkinding L K b k.
  Proof.
    induct 1; simpl; intros L K k_b Ha; try solve [invert_bkindings; eauto].
    {
      invert_bkindings.
      eapply bkinding_subst_i_t_0; eauto.
    }
    {
      invert_bkindings.
      eapply bkinding_subst_t_t_0; eauto.
    }
  Qed.
  
  Ltac invert_congs :=
    repeat match goal with
             H : cong _ _ _ |- _ => invert1 H
           end.

  Lemma idxeq_shift_i_i L i i' b :
    idxeq L i i' b ->
    forall x ls ,
      let n := length ls in
      x <= length L ->
      wellscoped_ss L ->
      wellscoped_i (length L) i ->
      wellscoped_i (length L) i' ->
      idxeq (shift_i_ss n (firstn x L) ++ ls ++ my_skipn L x) (shift_i_i n x i) (shift_i_i n x i') b.
  Proof.
    simpl.
    intros H x ls Hx HL Hi Hi'.
    eapply interp_prop_shift_i_p in H; eauto.
  Qed.
  
  Inductive wellscoped_t : nat -> ty -> Prop :=
  | WsctVar L x :
      wellscoped_t L (TVar x)
  | WsctConst L cn :
      wellscoped_t L (TConst cn)
  | WsctBinOp L opr c1 c2 :
      wellscoped_t L c1 ->
      wellscoped_t L c2 ->
      wellscoped_t L (TBinOp opr c1 c2)
  | WsctArrow L t1 i t2 :
      wellscoped_t L t1 ->
      wellscoped_i L i ->
      wellscoped_t L t2 ->
      wellscoped_t L (TArrow t1 i t2)
  | WsctAbs L b t :
      wellscoped_t (1 + L) t ->
      wellscoped_t L (TAbs b t)
  | WsctApp L t b i :
      wellscoped_t L t ->
      wellscoped_i L i ->
      wellscoped_t L (TApp t b i)
  | WsctQuan L quan k c :
      wellscoped_t L c ->
      wellscoped_t L (TQuan quan k c)
  | WsctQuanI L quan s c :
      wellscoped_s L s ->
      wellscoped_t (1 + L) c ->
      wellscoped_t L (TQuanI quan s c)
  | WsctRec L k c :
      wellscoped_t L c ->
      wellscoped_t L (TRec k c)
  | WsctNat L i :
      wellscoped_i L i ->
      wellscoped_t L (TNat i)
  | WsctArr L t i :
      wellscoped_t L t ->
      wellscoped_i L i ->
      wellscoped_t L (TArr t i)
  | WsctAbsT L t k1 :
      wellscoped_t L t ->
      wellscoped_t L (TAbsT k1 t)
  | WsctAppT L t1 t2 :
      wellscoped_t L t1 ->
      wellscoped_t L t2 ->
      wellscoped_t L (TAppT t1 t2)
  .

  Hint Constructors wellscoped_t.

  Lemma bkinding_wellscoped_t L K t k :
    bkinding L K t k ->
    wellscoped_t (length L) t.
  Proof.
    induct 1; simpl; eauto using bsorting_wellscoped_i, wfsort1_wellscoped_s.
  Qed.

  Lemma cong_shift_i_t L t t' :
    cong L t t' ->
    forall x ls ,
      let n := length ls in
      x <= length L ->
      wellscoped_ss L ->
      wellscoped_t (length L) t ->
      wellscoped_t (length L) t' ->
      cong (shift_i_ss n (firstn x L) ++ ls ++ my_skipn L x) (shift_i_t n x t) (shift_i_t n x t').
  Proof.
    simpl.
    induct 1; simpl; try rename x into y; intros x ls Hx HL Ht Ht'; try solve [invert Ht; invert Ht'; econstructor; simpl; eauto using idxeq_shift_i_i with db_la].
    {
      (* Case TAbs *)
      invert Ht; invert Ht'.
      econstructor; eauto.
      eapply IHcong with (x := S x); simpl; eauto with db_la.
    }
    {
      (* Case TQuanI *)
      invert Ht; invert Ht'.
      econstructor; eauto using sorteq_shift_i_k.
      specialize (IHcong (S x) ls).
      simpl in *.
      repeat rewrite length_firstn_le in * by la.
      eapply IHcong; simpl; eauto with db_la.
    }
  Qed.
  
  Lemma cong_shift_i_t_1_0 L t t' s :
    cong L t t' ->
    wellscoped_ss L ->
    wellscoped_t (length L) t ->
    wellscoped_t (length L) t' ->
    cong (s :: L) (shift_i_t 1 0 t) (shift_i_t 1 0 t').
  Proof.
    intros H; intros.
    eapply cong_shift_i_t with (x := 0) (ls := [s]) in H; simpl in *; eauto with db_la.
    rewrite my_skipn_0 in *.
    eauto.
  Qed.
  
  Lemma wellscoped_shift_i_t L p :
    wellscoped_t L p ->
    forall x n L',
      L' = n + L ->
      wellscoped_t L' (shift_i_t n x p).
  Proof.
    induct 1; simpl; try solve [intros; subst; eauto using wellscoped_shift_i_i, wellscoped_shift_i_s with db_la].
  Qed.

  Lemma cong_refl t L : cong L t t.
  Proof.
    induct t; simpl; eauto with db_idxeq db_sorteq.
  Qed.

  Lemma cong_shift_t_t :
    forall L body body',
      cong L body body' ->
      forall x n,
        (* wellscoped_ss L -> *)
        (* wellscoped_t (length L) body -> *)
        (* wellscoped_t (length L) body' -> *)
        cong L (shift_t_t n x body) (shift_t_t n x body').
  Proof.
    induct 1; simpl; try rename x into y; intros x n; try solve [econstructor; eauto].
  Qed.
  
  Lemma cong_subst_t_t :
    forall L body body',
      cong L body body' ->
      forall x v v',
        cong L v v' ->
        wellscoped_ss L ->
        wellscoped_t (length L) v ->
        wellscoped_t (length L) v' ->
        wellscoped_t (length L) body ->
        wellscoped_t (length L) body' ->
        cong L (subst_t_t x (shift_t_t x 0 v) body) (subst_t_t x (shift_t_t x 0 v') body').
  Proof.
    induct 1;
      simpl; try rename x into y; intros x v v' Hvv' HL Hv Hv' Hb Hb'; try solve [invert Hb; invert Hb'; econstructor; eauto].
    {
      (* Case TAbs *)
      invert Hb; invert Hb'.
      econstructor.
      unfold shift0_i_t.
      repeat rewrite shift_i_t_shift_t_t.
      eapply IHcong; eauto using wellscoped_shift_i_t.
      eapply cong_shift_i_t_1_0; eauto.
    }
    {
      (* Case TQuan *)
      invert Hb; invert Hb'.
      econstructor.
      repeat rewrite shift0_t_t_shift_0.
      eauto.
    }
    {
      (* Case TQuanI *)
      invert Hb; invert Hb'.
      econstructor; eauto.
      unfold shift0_i_t.
      repeat rewrite shift_i_t_shift_t_t.
      eapply IHcong; eauto using wellscoped_shift_i_t.
      eapply cong_shift_i_t_1_0; eauto.
    }
    {
      (* Case TRec *)
      invert Hb; invert Hb'.
      econstructor.
      repeat rewrite shift0_t_t_shift_0.
      eauto.
    }
    {
      (* Case TVar *)
      invert Hb; invert Hb'.
      cases (y <=>? x); eauto using cong_refl.
      eapply cong_shift_t_t; eauto.
    }
    {
      (* Case TAbsT *)
      invert Hb; invert Hb'.
      econstructor.
      repeat rewrite shift0_t_t_shift_0.
      eauto.
    }
  Qed.
  
  Lemma cong_subst_t_t_0 L body body' v v' :
    cong L body body' ->
    cong L v v' ->
    wellscoped_ss L ->
    wellscoped_t (length L) v ->
    wellscoped_t (length L) v' ->
    wellscoped_t (length L) body ->
    wellscoped_t (length L) body' ->
    cong L (subst_t_t 0 v body) (subst_t_t 0 v' body').
  Proof.
    intros H; intros.
    eapply cong_subst_t_t with (x := 0) (v := v) (v' := v') in H; simpl in *; eauto.
    repeat rewrite shift_t_t_0 in *.
    eauto.
  Qed.
  
  Lemma bkinding_wellscoped_t' L K t k n :
    bkinding L K t k ->
    n = length L ->
    wellscoped_t n t.
  Proof.
    intros; subst; eapply bkinding_wellscoped_t; eauto.
  Qed.

  Lemma par_transports_cong a b :
    par a b ->
    forall L K K' a' k k',
      let bs := map get_bsort L in
      cong L a a' ->
      bkinding bs K a k ->
      bkinding bs K' a' k' ->
      wfsorts1 L ->
      exists b',
        cong L b b' /\
        par a' b' /\
        bkinding bs K' b' k'.
  Proof.
    simpl.
    induct 1; simpl; try rename k into k''; intros L K K' a' k k' Haa' Ha Ha' HL;
      try solve [
            invert Haa'; invert Ha; invert Ha';
            repeat match goal with
                     H : context [exists _ : _, _] |- _ => edestruct H; eauto; clear H
                   end;
            openhyp;
            repeat eexists_split; eauto with db_idxeq db_sorteq
          ].
    {
      (* Case PaRQuanI *)
      invert Haa'; invert Ha; invert Ha';
      repeat match goal with
               H : context [exists _ : _, _] |- _ => edestruct H; eauto; clear H
             end;
      openhyp;
      repeat eexists_split; eauto with db_idxeq db_sorteq;
      invert H5; simpl in *; eauto.
    }
    {
      (* Case PaRBeta *)
      invert Haa'; invert Ha; invert Ha'.
      invert H5.
      invert_bkindings.
      repeat match goal with
               H : context [exists _ : _, _] |- _ => edestruct H; simpl; eauto; clear H
             end.
      openhyp.
      repeat eexists_split.
      {
        eapply cong_subst_i_t_0; eauto using bsorting_sorting1_SBaseSort.
        simpl.
        eapply par_preserves_bkinding; eauto.
      }
      {
        eauto.
      }
      {
        eauto using bkinding_subst_i_t_0 with db_idxeq db_sorteq.
      }
    }
    {
      (* Case PaRBetaT *)
      invert Haa'; invert Ha; invert Ha'.
      invert H4.
      invert_bkindings.
      repeat match goal with
               H : context [exists _ : _, _] |- _ => edestruct H; simpl; eauto; clear H
             end.
      openhyp.
      repeat eexists_split.
      {
        eapply cong_subst_t_t_0; eauto using wfsorts1_wellscoped_ss, bkinding_wellscoped_t', par_preserves_bkinding with db_la.
      }
      {
        eauto.
      }
      {
        eauto using bkinding_subst_t_t_0 with db_idxeq db_sorteq.
      }
    }
  Qed.

  Hint Constructors trc.
  
  Lemma pars_transports_cong a b :
    par^* a b ->
    forall L K K' a' k k',
      let bs := map get_bsort L in
      cong L a a' ->
      bkinding bs K a k ->
      bkinding bs K' a' k' ->
      wfsorts1 L ->
      exists b',
        cong L b b' /\
        par^* a' b' /\
        bkinding bs K' b' k'.
  Proof.
    simpl.
    induct 1; simpl; intros L K K' a' k k' Haa' Ha Ha' HL; eauto.
    copy H Hy.
    eapply par_preserves_bkinding in Hy; eauto.
    eapply par_transports_cong in H; eauto.
    rename a' into x'.
    destruct H as (y' & Hyy' & Hx'y' & Hy').
    eapply IHtrc in Hyy'; eauto.
    destruct Hyy' as (z' & Hzz' & Hy'z' & Hz').
    eauto.
  Qed.
  
  Lemma PaRBeta' s t b i t' t'' :
    par t t' ->
    t'' = subst0_i_t i t' ->
    par (TApp (TAbs s t) b i) t''.
  Proof.
    intros; subst; eauto.
  Qed.
  
  Lemma PaRBetaT' k t1 t2 t1' t2' t'' :
    par t1 t1' ->
    par t2 t2' ->
    t'' = subst0_t_t t2' t1' ->
    par (TAppT (TAbsT k t1) t2) t''.
  Proof.
    intros; subst; eauto.
  Qed.
  
  Lemma shift_t_t_subst_i_t :
    forall b x2 n x1 v,
      shift_t_t x2 n (subst_i_t x1 v b) = subst_i_t x1 v (shift_t_t x2 n b).
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

  Lemma subst_i_t_subst_t_t :
    forall b x2 v2 x1 v1,
      subst_i_t x2 v2 (subst_t_t x1 v1 b) = subst_t_t x1 (subst_i_t x2 v2 v1) (subst_i_t x2 v2 b).
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
      (* Case TVar *)
      repeat match goal with
             | |- context [?a <=? ?b] => cases (a <=? b); simplify; cbn
             | |- context [?a <=>? ?b] => cases (a <=>? b); simplify; cbn
             end; try solve [f_equal; la].
    }
    {
      (* Case TAbs *)
      rewrite IHb by la.
      unfold shift0_i_t, shift0_i_i.
      rewrite shift_i_t_subst_in by la.
      repeat f_equal.
      la.
    }
    {
      (* Case TQuan *)
      rewrite IHb by la.
      unfold shift0_t_t.
      rewrite shift_t_t_subst_i_t.
      eauto.
    }      
    {
      (* Case TQuanI *)
      rewrite IHb by la.
      unfold shift0_i_t, shift0_i_i.
      rewrite shift_i_t_subst_in by la.
      repeat f_equal.
      la.
    }      
    {
      (* Case TRec *)
      rewrite IHb by la.
      unfold shift0_t_t.
      rewrite shift_t_t_subst_i_t.
      eauto.
    }      
    {
      (* Case TAbsT *)
      rewrite IHb by la.
      unfold shift0_t_t.
      rewrite shift_t_t_subst_i_t.
      eauto.
    }      
  Qed.

  Lemma par_subst_i_t t1 t2 :
    par t1 t2 ->
    forall x v,
      par (subst_i_t x v t1)  (subst_i_t x v t2).
  Proof.
    induct 1; simpl; intros x v; eauto.
    {
      eapply PaRBeta'; eauto.
      unfold subst0_i_t.
      rewrite subst_i_t_subst by la.
      eauto.
    }
    {
      eapply PaRBetaT'; eauto.
      unfold subst0_t_t.
      rewrite subst_i_t_subst_t_t.
      eauto.
    }
  Qed.
  
  Lemma par_shift_i_t t1 t2 :
    par t1 t2 ->
    forall n x,
      par (shift_i_t n x t1)  (shift_i_t n x t2).
  Proof.
    induct 1; simpl; intros n x; eauto.
    {
      eapply PaRBeta'; eauto.
      unfold subst0_i_t.
      rewrite shift_i_t_subst_out by la.
      eauto.
    }
    {
      eapply PaRBetaT'; eauto.
      unfold subst0_t_t.
      rewrite shift_i_t_subst_t_t.
      eauto.
    }
  Qed.
  
  Lemma par_shift_t_t t1 t2 :
    par t1 t2 ->
    forall n x,
      par (shift_t_t n x t1)  (shift_t_t n x t2).
  Proof.
    induct 1; simpl; intros n x; eauto.
    {
      eapply PaRBeta'; eauto.
      unfold subst0_i_t.
      rewrite shift_t_t_subst_i_t.
      eauto.
    }
    {
      eapply PaRBetaT'; eauto.
      unfold subst0_t_t.
      rewrite shift_t_t_subst_out by la.
      eauto.
    }
  Qed.
  
  Lemma par_subst_t_t_eqv_eq body x v1 v2 :
    par v1 v2 ->
    par (subst_t_t x v1 body)  (subst_t_t x v2 body).
  Proof.
    induct body; simpl; intros Hv1v2; eauto using par_shift_i_t, par_shift_t_t.
    cases (x <=>? x0); eauto.
  Qed.
  
  Lemma par_subst_t_t_eq_eqv t1 t2 :
    par t1 t2 ->
    forall x v,
      par (subst_t_t x v t1)  (subst_t_t x v t2).
  Proof.
    induct 1; simpl; intros x v; eauto.
    {
      eapply PaRBeta'; eauto.
      unfold subst0_i_t, shift0_i_t.
      rewrite subst_i_t_subst_t_t.
      rewrite subst_i_t_shift_avoid by la.
      simpl.
      rewrite shift_i_t_0.
      eauto.
    }
    {
      eapply PaRBetaT'; eauto.
      unfold subst0_t_t, shift0_t_t.
      rewrite subst_t_t_subst by la.
      eauto.
    }
  Qed.
  
  Lemma par_subst_t_t_eqv_eqv t1 t2 :
    par t1 t2 ->
    forall x v1 v2,
      par v1 v2 ->
      par (subst_t_t x v1 t1)  (subst_t_t x v2 t2).
  Proof.
    induct 1; simpl; intros x v1 v2 Hv1v2; eauto using par_shift_i_t, par_shift_t_t, par_subst_t_t_eqv_eq.
    {
      eapply PaRBeta'.
      {
        eapply IHpar.
        eapply par_shift_i_t; eauto.
      }
      unfold subst0_i_t, shift0_i_t.
      rewrite subst_i_t_subst_t_t.
      rewrite subst_i_t_shift_avoid by la.
      simpl.
      rewrite shift_i_t_0.
      eauto.
    }
    {
      eapply PaRBetaT'.
      {
        eapply IHpar1.
        eapply par_shift_t_t; eauto.
      }
      {
        eapply IHpar2; eauto.
      }
      unfold subst0_t_t, shift0_t_t.
      rewrite subst_t_t_subst by la.
      eauto.
    }
  Qed.
  
  Lemma par_diamond a b :
    par a b ->
    forall c,
      par a c ->
      exists d,
        par b d /\
        par c d.
  Proof.
    induct 1; simpl; try rename c into t; intros c Hac;
      try solve [
            invert Hac;
            repeat match goal with
                     H : context [exists _ : _, _] |- _ => edestruct H; eauto; clear H
                   end;
            openhyp;
            eauto using par_subst_i_t
          ].
    {
      invert Hac;
      try solve [
            repeat match goal with
                     H : context [exists _ : _, _] |- _ => edestruct H; eauto; clear H
                   end;
            openhyp;
            eauto using par_subst_i_t
          ].
      invert H; eauto.
      rename t0 into a.
      rename b into bsort.
      rename t'1 into b.
      rename t'0 into c.
      specialize (IHpar (TAbs s c)).
      edestruct IHpar as (d & Hbd & Hcd); eauto.
      invert Hbd; invert Hcd;
        try solve [
              repeat match goal with
                       H : context [exists _ : _, _] |- _ => edestruct H; eauto; clear H
                     end;
              openhyp;
              eauto using par_subst_i_t
            ].
    }
    {
      rename b into bsort.
      rename t into a.
      rename t' into b.
      invert Hac;
      try solve [
            repeat match goal with
                     H : context [exists _ : _, _] |- _ => edestruct H; eauto; clear H
                   end;
            openhyp;
            eauto using par_subst_i_t
          ].
      invert H4;
        try solve [
              repeat match goal with
                       H : context [exists _ : _, _] |- _ => edestruct H; eauto; clear H
                     end;
              openhyp;
              eauto using par_subst_i_t
            ].
    }
    {
      invert Hac;
      try solve [
            repeat match goal with
                     H : context [exists _ : _, _] |- _ => edestruct H; eauto; clear H
                   end;
            openhyp;
            eauto using par_subst_i_t
          ].
      invert H.
      {
        rename t0 into a1.
        rename t1'0 into c1.
        rename t2 into a2.
        rename t2' into b2.
        rename t2'0 into c2.
        specialize (IHpar2 c2).
        edestruct IHpar2 as (d2 & Hb2d2 & Hc2d2); eauto.
        try solve [
              repeat match goal with
                       H : context [exists _ : _, _] |- _ => edestruct H; eauto; clear H
                     end;
              openhyp;
              eauto using par_subst_t_t_eqv_eqv
            ].
      }
      {
        rename t0 into a1.
        rename t' into b1.
        rename t1'0 into c1.
        rename t2 into a2.
        rename t2' into b2.
        rename t2'0 into c2.
        specialize (IHpar1 (TAbsT k c1)).
        edestruct IHpar1 as (d1 & Hb1d1 & Hc1d1); eauto.
        specialize (IHpar2 c2).
        edestruct IHpar2 as (d2 & Hb2d2 & Hc2d2); eauto.
        invert Hb1d1; invert Hc1d1;
          try solve [
                repeat match goal with
                         H : context [exists _ : _, _] |- _ => edestruct H; eauto; clear H
                       end;
                openhyp;
                eauto using par_subst_t_t_eqv_eqv
              ].
      }
    }
    {
      rename t1 into a1.
      rename t2 into a2.
      rename t1' into b1.
      rename t2' into b2.
      invert Hac;
      try solve [
            repeat match goal with
                     H : context [exists _ : _, _] |- _ => edestruct H; eauto; clear H
                   end;
            openhyp;
            eauto using par_subst_t_t_eqv_eqv
          ].
      rename t1' into c1.
      rename t2' into c2.
      invert H3;
        try solve [
              repeat match goal with
                       H : context [exists _ : _, _] |- _ => edestruct H; eauto; clear H
                     end;
              openhyp;
              eauto using par_subst_t_t_eqv_eqv
            ].
    }
  Qed.
    
  Lemma pars_diamond_oneside a b :
    par^* a b ->
    forall c,
      par a c ->
      exists d,
        par^* b d /\
        par^* c d.
  Proof.
    induct 1; simpl; intros c Hac; eauto.
    rename c into y'.
    eapply par_diamond in H; [|eapply Hac].
    destruct H as (yy' & Hy'yy' & Hyyy').
    eapply IHtrc in Hyyy'.
    openhyp.
    eauto.
  Qed.
  
  Lemma pars_diamond a b :
    par^* a b ->
    forall c,
      par^* a c ->
      exists d,
        par^* b d /\
        par^* c d.
  Proof.
    induct 1; simpl; intros c Hac; eauto.
    eapply pars_diamond_oneside in Hac; eauto.
    openhyp.
    eapply IHtrc in H2; eauto.
    openhyp.
    eauto using trc_trans.
  Qed.

  (* symmetric closure *)
  
  Section symc.
    Variable A : Type.
    Variable R : A -> A -> Prop.

    Inductive symc : A -> A -> Prop :=
    | SymcSame x y :
        R x y ->
        symc x y
    | SymcRev x y :
        R y x ->
        symc x y
    .
  End symc.

  Hint Constructors symc.

  Notation "R ^~" := (symc R) (at level 0).
  Notation symtrc R := (trc (symc R)).
  Notation "R ^~*" := (symtrc R) (at level 0).

  Lemma par_confluent a b :
    par^~* a b ->
    exists c,
        par^* a c /\
        par^* b c.
  Proof.
    induct 1; simpl; eauto.
    destruct IHtrc as (yz & Hyyz & Hzyz).
    invert H; eauto.
    eapply pars_diamond_oneside in Hyyz; eauto.
    openhyp.
    eauto using trc_trans.
  Qed.

  Lemma equal_sorts_idxeq L L' i i' b :
    idxeq L i i' b ->
    equal_sorts L L' ->
    wellscoped_ss L ->
    wellscoped_ss L' ->
    idxeq L' i i' b.
  Proof.
    intros Hii' HLL' HL HL'.
    eapply equal_sorts_interp_prop in Hii'; eauto.
  Qed.

  Hint Resolve equal_sorts_idxeq : db_idxeq.
  Hint Resolve equal_sorts_sorteq : db_sorteq.
   
  Lemma equal_sorts_cong L a b :
    cong L a b ->
    forall L' K1 K2 k1 k2,
      equal_sorts L L' ->
      bkinding (map get_bsort L) K1 a k1 ->
      bkinding (map get_bsort L) K2 b k2 ->
      wfsorts1 L ->
      wfsorts1 L' ->
      cong L' a b.
  Proof.
    induct 1; simpl; intros L' K1 K2 k1 k2 HLL' Ha Hb HL HL'; try invert1 HLL'; try invert1 Ha; try invert1 Hb; econstructor; eauto using wfsorts1_wellscoped_ss with db_idxeq db_sorteq.
    eapply IHcong; eauto with db_idxeq db_sorteq.
    {
      invert H; simpl in *; eauto.
    }
    econstructor; eauto with db_idxeq db_sorteq.
    eapply equal_sorts_get_bsort in HLL'.
    rewrite <- HLL'; eauto.
  Qed.
  
  Lemma cong_sym L a b :
    cong L a b ->
    forall K1 K2 k1 k2,
      bkinding (map get_bsort L) K1 a k1 ->
      bkinding (map get_bsort L) K2 b k2 ->
      wfsorts1 L ->
      cong L b a.
  Proof.
    induct 1; simpl; intros K1 K2 k1 k2 Ha Hb HL; try invert1 Ha; try invert1 Hb; try invert1 HL; econstructor; eauto with db_idxeq db_sorteq.
    eapply equal_sorts_cong; [eapply IHcong | .. ]; eauto using equal_sorts_refl with db_idxeq db_sorteq.
    {
      invert H; simpl in *; eauto.
    }
    {
      invert H; simpl in *; eauto.
    }
  Qed.

  Lemma cong_trans L a b :
    cong L a b ->
    forall c K1 K2 K3 k1 k2 k3,
      cong L b c ->
      bkinding (map get_bsort L) K1 a k1 ->
      bkinding (map get_bsort L) K2 b k2 ->
      bkinding (map get_bsort L) K3 c k3 ->
      wfsorts1 L ->
      cong L a c.
  Proof.
    induct 1; simpl; try rename c into t; intros c K1 K2 K3 k1 k2 k3 Hbc Ha Hb Hc HL; try invert1 Hbc; try invert1 Ha; try invert1 Hb; try invert1 Hc; try invert1 HL; eauto with db_idxeq db_sorteq.
    econstructor; eauto with db_idxeq db_sorteq.
    eapply IHcong; eauto; try solve [invert H; invert H6; simpl in *; eauto].
    eapply equal_sorts_cong; eauto using equal_sorts_refl with db_idxeq db_sorteq.
    invert H; invert H6; simpl in *; eauto.
  Qed.
  
  Lemma pars_preserves_bkinding a b :
    par^* a b ->
    forall L K k,
      bkinding L K a k ->
      bkinding L K b k.
  Proof.
    induct 1; simpl; intros L k_b Ha; eauto using par_preserves_bkinding.
  Qed.
  
  Lemma pars_TBinOp_1 t1 t1' :
    par^* t1 t1' ->
    forall opr t2,
      par^* (TBinOp opr t1 t2) (TBinOp opr t1' t2).
  Proof.
    induct 1; simpl; eauto.
  Qed.
  
  Lemma pars_TBinOp_2 t2 t2' :
    par^* t2 t2' ->
    forall opr t1,
      par^* (TBinOp opr t1 t2) (TBinOp opr t1 t2').
  Proof.
    induct 1; simpl; eauto.
  Qed.
  
  Lemma pars_TBinOp opr t1 t1' t2 t2' :
    par^* t1 t1' ->
    par^* t2 t2' ->
    par^* (TBinOp opr t1 t2) (TBinOp opr t1' t2').
  Proof.
    intros; eauto using trc_trans, pars_TBinOp_1, pars_TBinOp_2.
  Qed.
  
  Lemma pars_TArrow_1 t1 t1' :
    par^* t1 t1' ->
    forall i t2,
      par^* (TArrow t1 i t2) (TArrow t1' i t2).
  Proof.
    induct 1; simpl; eauto.
  Qed.
  
  Lemma pars_TArrow_2 t2 t2' :
    par^* t2 t2' ->
    forall t1 i,
      par^* (TArrow t1 i t2) (TArrow t1 i t2').
  Proof.
    induct 1; simpl; eauto.
  Qed.
  
  Lemma pars_TArrow t1 i t1' t2 t2' :
    par^* t1 t1' ->
    par^* t2 t2' ->
    par^* (TArrow t1 i t2) (TArrow t1' i t2').
  Proof.
    intros; eauto using trc_trans, pars_TArrow_1, pars_TArrow_2.
  Qed.
  
  Lemma pars_TAbs b t1 t1':
    par^* t1 t1' ->
    par^* (TAbs b t1) (TAbs b t1').
  Proof.
    induct 1; simpl; eauto.
  Qed.
  
  Lemma pars_TApp b i t1 t1':
    par^* t1 t1' ->
    par^* (TApp t1 b i) (TApp t1' b i).
  Proof.
    induct 1; simpl; eauto.
  Qed.
  
  Lemma pars_TQuan q k t1 t1':
    par^* t1 t1' ->
    par^* (TQuan q k t1) (TQuan q k t1').
  Proof.
    induct 1; simpl; eauto.
  Qed.
  
  Lemma pars_TQuanI q k t1 t1':
    par^* t1 t1' ->
    par^* (TQuanI q k t1) (TQuanI q k t1').
  Proof.
    induct 1; simpl; eauto.
  Qed.
  
  Lemma pars_TRec k t1 t1':
    par^* t1 t1' ->
    par^* (TRec k t1) (TRec k t1').
  Proof.
    induct 1; simpl; eauto.
  Qed.
  
  Lemma pars_TArr i t1 t1':
    par^* t1 t1' ->
    par^* (TArr t1 i) (TArr t1' i).
  Proof.
    induct 1; simpl; eauto.
  Qed.
  
  Lemma pars_TAbsT b t1 t1':
    par^* t1 t1' ->
    par^* (TAbsT b t1) (TAbsT b t1').
  Proof.
    induct 1; simpl; eauto.
  Qed.
  
  Lemma pars_TAppT_1 t1 t1' :
    par^* t1 t1' ->
    forall t2,
      par^* (TAppT t1 t2) (TAppT t1' t2).
  Proof.
    induct 1; simpl; eauto.
  Qed.
  
  Lemma pars_TAppT_2 t2 t2' :
    par^* t2 t2' ->
    forall t1,
      par^* (TAppT t1 t2) (TAppT t1 t2').
  Proof.
    induct 1; simpl; eauto.
  Qed.
  
  Lemma pars_TAppT t1 t1' t2 t2' :
    par^* t1 t1' ->
    par^* t2 t2' ->
    par^* (TAppT t1 t2) (TAppT t1' t2').
  Proof.
    intros; eauto using trc_trans, pars_TAppT_1, pars_TAppT_2.
  Qed.
  
  Inductive tyeq1 : sctx -> kctx -> ty -> ty -> kind -> Prop :=
  (* congruence rules *)
  | TyEq1BinOp L K opr t1 t2 t1' t2' :
      tyeq1 L K t1 t1' KType ->
      tyeq1 L K t2 t2' KType ->
      tyeq1 L K (TBinOp opr t1 t2) (TBinOp opr t1' t2') KType
  | TyEq1Arrow L K t1 i t2 t1' i' t2':
      tyeq1 L K t1 t1' KType ->
      idxeq L i i' BSTime ->
      tyeq1 L K t2 t2' KType ->
      tyeq1 L K (TArrow t1 i t2) (TArrow t1' i' t2') KType
  | TyEq1Abs L K b t t' k :
      tyeq1 (SBaseSort b :: L) K t t' k ->
      tyeq1 L K (TAbs b t) (TAbs b t') (KArrow b k)
  | TyEq1App L K t b i t' i' k :
      tyeq1 L K t t' (KArrow b k) ->
      idxeq L i i' b ->
      tyeq1 L K (TApp t b i) (TApp t' b i') k
  | TyEq1Quan L K quan k t t' :
      tyeq1 L (k :: K) t t' KType ->
      tyeq1 L K (TQuan quan k t) (TQuan quan k t') KType
  | TyEq1QuanI L K quan s t s' t' :
      sorteq L s s' ->
      tyeq1 (s :: L) K t t' KType ->
      tyeq1 L K (TQuanI quan s t) (TQuanI quan s' t') KType
  | TyEq1Rec L K k c c' :
      tyeq1 L (k :: K) c c' k ->
      tyeq1 L K (TRec k c) (TRec k c') k
  | TyEq1Nat L K i i' :
      idxeq L i i' BSNat ->
      tyeq1 L K (TNat i) (TNat i') KType
  | TyEq1Arr L K t i t' i' :
      tyeq1 L K t t' KType ->
      idxeq L i i' BSNat ->
      tyeq1 L K (TArr t i) (TArr t' i') KType
  | TyEq1AbsT L K k t t' k2 :
      tyeq1 L (k :: K) t t' k2 ->
      tyeq1 L K (TAbsT k t) (TAbsT k t') (KArrowT k k2)
  | TyEq1AppT L K t1 t2 t1' t2' k1 k2 :
      tyeq1 L K t1 t1' (KArrowT k1 k2) ->
      tyeq1 L K t2 t2' k1 ->
      tyeq1 L K (TAppT t1 t2) (TAppT t1' t2') k2
  | TyEq1Var L K x k :
      nth_error K x = Some k ->
      tyeq1 L K (TVar x) (TVar x) k
  | TyEq1Const L K cn :
      tyeq1 L K (TConst cn) (TConst cn) KType
  (* reduction rules *)
  | TyEq1Beta L K s t b i k :
      bkinding (map get_bsort L) K (TApp (TAbs s t) b i) k ->
      tyeq1 L K (TApp (TAbs s t) b i) (subst0_i_t i t) k
  | TyEq1BetaT L K k t1 t2 k2 :
      bkinding (map get_bsort L) K (TAppT (TAbsT k t1) t2) k2 ->
      tyeq1 L K (TAppT (TAbsT k t1) t2) (subst0_t_t t2 t1) k2
  (* structural rules *)
  | TyEq1Refl L K t k :
      bkinding (map get_bsort L) K t k ->
      tyeq1 L K t t k
  | TyEq1Sym L K a b k :
      tyeq1 L K a b k ->
      tyeq1 L K b a k
  | TyEq1Trans L K a b c k :
      tyeq1 L K a b k ->
      tyeq1 L K b c k ->
      bkinding (map get_bsort L) K b k ->
      tyeq1 L K a c k
  .

  Hint Constructors tyeq1.

  Lemma bkinding_unique L K t k :
    bkinding L K t k ->
    forall k',
      bkinding L K t k' ->
      k = k'.
  Proof.
    induct 1; simpl; intros k' Hk'; try invert1 Hk'; f_equal; eauto.
    {
      equality.
    }
    {
      eapply IHbkinding in H7.
      invert H7.
      eauto.
    }
    {
      eapply IHbkinding1 in H5.
      invert H5.
      eauto.
    }
  Qed.
  
  Lemma tyeq1_bkinding_same_k L K t t' k :
    tyeq1 L K t t' k ->
    forall k',
      (bkinding (map get_bsort L) K t k' -> k = k') /\
      (bkinding (map get_bsort L) K t' k' -> k = k').
  Proof.
    induct 1; simpl; intros k'; split; intros Hk'; try invert1 Hk'; f_equal; eauto;
      try solve [
            eapply IHtyeq1 in H5; subst; eauto |
            equality |
            invert_bkindings; eapply bkinding_unique; eauto
          ].
    {
      eapply IHtyeq1 in H7.
      invert H7.
      eauto.
    }
    {
      eapply IHtyeq1 in H7.
      invert H7.
      eauto.
    }
    {
      eapply IHtyeq1_1 in H5.
      invert H5.
      eauto.
    }
    {
      eapply IHtyeq1_1 in H5.
      invert H5.
      eauto.
    }
    {
      invert_bkindings.
      eapply bkinding_subst_i_t_0 in H2; eauto.
      eapply bkinding_unique; eauto.
    }
    {
      invert_bkindings.
      eapply bkinding_subst_t_t_0 with (K := K) in H2; eauto.
      eapply bkinding_unique; eauto.
    }
    {
      eapply IHtyeq1 in Hk'.
      subst.
      eauto.
    }
    {
      eapply IHtyeq1 in Hk'.
      subst.
      eauto.
    }
    {
      eapply IHtyeq1_1 in Hk'.
      subst.
      eauto.
    }
    {
      eapply IHtyeq1_2 in Hk'.
      subst.
      eauto.
    }
  Qed.

  Lemma tyeq1_bkinding_same_k_1 L K t t' k :
    tyeq1 L K t t' k ->
    forall k',
      bkinding (map get_bsort L) K t k' -> k = k'.
  Proof.
    intros H; intros; eapply tyeq1_bkinding_same_k with (t := t'); eauto.
  Qed.
  
  Lemma tyeq1_bkinding_same_k_2 L K t t' k :
    tyeq1 L K t t' k ->
    forall k',
      bkinding (map get_bsort L) K t' k' -> k = k'.
  Proof.
    intros H; intros; eapply tyeq1_bkinding_same_k with (t := t); eauto.
  Qed.
  
  Lemma tyeq1_par L K a a' k :
    tyeq1 L K a a' k ->
    let bs := map get_bsort L in
    bkinding bs K a k ->
    bkinding bs K a' k ->
    wfsorts1 L ->
    exists b b',
      par^* a b /\
      par^* a' b' /\
      cong L b b' /\
      bkinding bs K b k /\
      bkinding bs K b' k.
  Proof.
    simpl.
    induct 1; simpl; intros Ha Hb HL; try invert1 Ha; try invert1 Hb; try invert1 HL.
    {
      edestruct IHtyeq1_1 as (r1 & r1' & Ht1r1 & Ht1'r1' & Hr1r1' & Hr1 & Hr1'); eauto.
      edestruct IHtyeq1_2 as (r2 & r2' & Ht2r2 & Ht2'r2' & Hr2r2' & Hr2 & Hr2'); eauto.
      exists (TBinOp opr r1 r2), (TBinOp opr r1' r2').
      repeat eexists_split;
      eauto using pars_TBinOp.
    }
    {
      edestruct IHtyeq1_1 as (r1 & r1' & Ht1r1 & Ht1'r1' & Hr1r1' & Hr1 & Hr1'); eauto.
      edestruct IHtyeq1_2 as (r2 & r2' & Ht2r2 & Ht2'r2' & Hr2r2' & Hr2 & Hr2'); eauto.
      exists (TArrow r1 i r2), (TArrow r1' i' r2').
      repeat eexists_split;
      eauto using pars_TArrow.
    }
    {
      edestruct IHtyeq1 as (r1 & r1' & Ht1r1 & Ht1'r1' & Hr1r1' & Hr1 & Hr1'); eauto.
      exists (TAbs b r1), (TAbs b r1').
      repeat eexists_split;
      eauto using pars_TAbs.
    }
    {
      edestruct IHtyeq1 as (r1 & r1' & Ht1r1 & Ht1'r1' & Hr1r1' & Hr1 & Hr1'); eauto.
      exists (TApp r1 b i), (TApp r1' b i').
      repeat eexists_split;
      eauto using pars_TApp.
    }
    {
      edestruct IHtyeq1 as (r1 & r1' & Ht1r1 & Ht1'r1' & Hr1r1' & Hr1 & Hr1'); eauto.
      exists (TQuan quan0 k r1), (TQuan quan0 k r1').
      repeat eexists_split;
      eauto using pars_TQuan.
    }
    {
      edestruct IHtyeq1 as (r1 & r1' & Ht1r1 & Ht1'r1' & Hr1r1' & Hr1 & Hr1'); eauto.
      {
        invert H; simpl in *; eauto.
      }
      exists (TQuanI quan0 s r1), (TQuanI quan0 s' r1').
      repeat eexists_split;
      eauto using pars_TQuanI.
      econstructor; eauto.
      {
        invert H; simpl in *; eauto.
      }
    }
    {
      edestruct IHtyeq1 as (r1 & r1' & Ht1r1 & Ht1'r1' & Hr1r1' & Hr1 & Hr1'); eauto.
      exists (TRec k r1), (TRec k r1').
      repeat eexists_split;
      eauto using pars_TRec.
    }
    {
      exists (TNat i), (TNat i').
      repeat eexists_split;
      eauto.
    }
    {
      edestruct IHtyeq1 as (r1 & r1' & Ht1r1 & Ht1'r1' & Hr1r1' & Hr1 & Hr1'); eauto.
      exists (TArr r1 i), (TArr r1' i').
      repeat eexists_split;
      eauto using pars_TArr.
    }
    {
      edestruct IHtyeq1 as (r1 & r1' & Ht1r1 & Ht1'r1' & Hr1r1' & Hr1 & Hr1'); eauto.
      exists (TAbsT k r1), (TAbsT k r1').
      repeat eexists_split;
      eauto using pars_TAbsT.
    }
    {
      assert (k0 = k1 /\ k3 = k1).
      {
        copy H HH.
        eapply tyeq1_bkinding_same_k_1 in H; eauto.
        invert H.
        eapply tyeq1_bkinding_same_k_2 in HH; eauto.
        invert HH.
        eauto.
      }
      openhyp; subst.
      edestruct IHtyeq1_1 as (r1 & r1' & Ht1r1 & Ht1'r1' & Hr1r1' & Hr1 & Hr1'); eauto.
      edestruct IHtyeq1_2 as (r2 & r2' & Ht2r2 & Ht2'r2' & Hr2r2' & Hr2 & Hr2'); eauto.
      exists (TAppT r1 r2), (TAppT r1' r2').
      repeat eexists_split;
      eauto using pars_TAppT.
    }
    {
      exists (TVar x), (TVar x).
      repeat eexists_split;
      eauto using cong_refl.
    }
    {
      exists (TConst cn), (TConst cn).
      repeat eexists_split;
      eauto using cong_refl.
    }
    {
      exists (subst0_i_t i t), (subst0_i_t i t). 
      repeat eexists_split;
      eauto using cong_refl.
    }
    {
      exists (subst0_t_t t2 t1), (subst0_t_t t2 t1).
      repeat eexists_split;
      eauto using cong_refl.
    }
    {
      exists t, t.
      repeat eexists_split;
      eauto using cong_refl.
    }
    {
      edestruct IHtyeq1 as (r1 & r1' & Ht1r1 & Ht1'r1' & Hr1r1' & Hr1 & Hr1'); eauto.
      exists r1', r1.
      repeat eexists_split;
      eauto using cong_sym.
    }
    {
      edestruct IHtyeq1_1 as (a' & b1 & Haa' & Hbb1 & Ha'b1 & Ha' & Hb1); eauto.
      edestruct IHtyeq1_2 as (b2 & c' & Hbb2 & Hcc' & Hb2c' & Hb2 & Hc'); eauto.
      eapply pars_diamond in Hbb1; [|eapply Hbb2].
      destruct Hbb1 as (b3 & Hb2b3 & Hb1b3).
      eapply cong_sym in Ha'b1; eauto.
      copy Hb1b3 Hb3.
      eapply pars_preserves_bkinding in Hb3; eauto.
      eapply pars_transports_cong with (a' := a') in Hb1b3; eauto.
      destruct Hb1b3 as (a'' & Hb3a'' & Ha'a'' & Ha'').
      eapply pars_transports_cong with (a' := c') in Hb2b3; eauto.
      destruct Hb2b3 as (c'' & Hb3c'' & Hc'c'' & Hc'').
      exists a'', c''.
      repeat try_split; eauto using trc_trans.
      eapply cong_sym in Hb3a''; eauto.
      eapply cong_trans; eauto.
    }
  Qed.

  Lemma par_tyeq1 a b :
    par a b ->
    forall L K1 k1,
      let bs := map get_bsort L in
      bkinding bs K1 a k1 ->
      tyeq1 L K1 a b k1.
  Proof.
    simpl.
    induct 1; simpl; intros L K1 k1 Ha; try invert1 Ha; eauto with db_idxeq db_sorteq.
    {
      invert_bkindings.
      eapply TyEq1Trans; [| eapply TyEq1Beta |]; eauto using par_preserves_bkinding with db_idxeq db_sorteq.
    }
    {
      invert_bkindings.
      eapply TyEq1Trans; [| eapply TyEq1BetaT |]; eauto using par_preserves_bkinding with db_idxeq db_sorteq.
    }
  Qed.

  Lemma pars_tyeq1 a b :
    par^* a b ->
    forall L K1 k1,
      let bs := map get_bsort L in
      bkinding bs K1 a k1 ->
      tyeq1 L K1 a b k1.
  Proof.
    simpl.
    induct 1; simpl; intros L K1 k1 Ha; try invert1 Ha; eauto using par_tyeq1.
    copy H Hy.
    eapply par_preserves_bkinding in Hy; eauto.
    eapply TyEq1Trans; [| eapply IHtrc |]; eauto using par_tyeq1.
  Qed.  
  
  Lemma par_preserves_TArrow t1 i t2 t' :
    par (TArrow t1 i t2) t' ->
    exists t1' t2',
      t' = TArrow t1' i t2' /\
      par t1 t1' /\
      par t2 t2'.
  Proof.
    induct 1; simpl; eauto.
  Qed.
  
  Lemma pars_preserves_TArrow t1 i t2 t' :
    par^* (TArrow t1 i t2) t' ->
    exists t1' t2',
      t' = TArrow t1' i t2' /\
      par^* t1 t1' /\
      par^* t2 t2'.
  Proof.
    induct 1; simpl; eauto using par_preserves_TArrow.
    eapply par_preserves_TArrow in H; eauto.
    openhyp.
    subst.
    edestruct IHtrc; eauto.
    openhyp.
    subst.
    repeat eexists_split; eauto.
  Qed.

  Lemma cong_tyeq1 L t t' :
    cong L t t' ->
    forall K k,
      bkinding (map get_bsort L) K t k ->
      tyeq1 L K t t' k.
  Proof.
    induct 1; simpl; try rename k into k'; intros K k Ht; try invert1 Ht; eauto.
  Qed.

  Lemma invert_tyeq_TArrow L t1 i t2 t1' i' t2' K k :
    tyeq1 L K (TArrow t1 i t2) (TArrow t1' i' t2') k ->
    let bs := map get_bsort L in
    bkinding bs K (TArrow t1 i t2) k ->
    bkinding bs K (TArrow t1' i' t2') k ->
    wfsorts1 L ->
    tyeq1 L K t1 t1' k /\
    interp_prop L (TEq i i') /\
    tyeq1 L K t2 t2' k.
  Proof.
    simpl.
    intros H H1 H2 HL.
    invert H1.
    invert H2.
    eapply tyeq1_par in H; eauto.
    edestruct H as (r1 & r1' & Ht1r1 & Ht1'r1' & Hr1r1' & Hr1 & Hr1'); eauto.
    eapply pars_preserves_TArrow in Ht1r1.
    openhyp; subst.
    eapply pars_preserves_TArrow in Ht1'r1'.
    openhyp; subst.
    invert Hr1r1'.
    repeat try_split; eauto.
    {
      eapply TyEq1Trans.
      {
        eapply pars_tyeq1; eauto.
      }
      eapply TyEq1Trans.
      {
        eapply cong_tyeq1; eauto using pars_preserves_bkinding.
      }
      {
        eapply TyEq1Sym.
        eapply pars_tyeq1; eauto using pars_preserves_bkinding.
      }
      {
        eapply pars_preserves_bkinding; eauto.
      }
      {
        eapply pars_preserves_bkinding; eauto.
      }
    }
    {
      eapply TyEq1Trans.
      {
        eapply pars_tyeq1; eauto.
      }
      eapply TyEq1Trans.
      {
        eapply cong_tyeq1; eauto using pars_preserves_bkinding.
      }
      {
        eapply TyEq1Sym.
        eapply pars_tyeq1; eauto using pars_preserves_bkinding.
      }
      {
        eapply pars_preserves_bkinding; eauto.
      }
      {
        eapply pars_preserves_bkinding; eauto.
      }
    }
  Qed.

  Lemma par_preserves_TQuan q k t1 t' :
    par (TQuan q k t1) t' ->
    exists t1',
      t' = TQuan q k t1' /\
      par t1 t1'.
  Proof.
    induct 1; simpl; eauto.
  Qed.
  
  Lemma pars_preserves_TQuan q k t1 t' :
    par^* (TQuan q k t1) t' ->
    exists t1',
      t' = TQuan q k t1' /\
      par^* t1 t1'.
  Proof.
    induct 1; simpl; eauto using par_preserves_TQuan.
    eapply par_preserves_TQuan in H; eauto.
    openhyp.
    subst.
    edestruct IHtrc; eauto.
    openhyp.
    subst.
    repeat eexists_split; eauto.
  Qed.

  Lemma invert_tyeq1_TQuan_TArrow L q k t t1 i t2 K k0 :
    tyeq1 L K (TQuan q k t) (TArrow t1 i t2) k0 ->
    let bs := map get_bsort L in
    bkinding bs K (TQuan q k t) k0 ->
    bkinding bs K (TArrow t1 i t2) k0 ->
    wfsorts1 L ->
    False.
  Proof.
    simpl.
    intros H H1 H2 HL.
    invert H1.
    invert H2.
    eapply tyeq1_par in H; eauto.
    edestruct H as (r1 & r1' & Ht1r1 & Ht1'r1' & Hr1r1' & Hr1 & Hr1'); eauto.
    eapply pars_preserves_TQuan in Ht1r1.
    openhyp.
    subst.
    eapply pars_preserves_TArrow in Ht1'r1'.
    openhyp.
    subst.
    invert Hr1r1'.
  Qed.
  
  Fixpoint TApps t args :=
    match args with
    | nil => t
    | (b, i) :: args => TApps (TApp t b i) args
    end.

  Lemma TApps_TApp args t b i : sig (fun x => TApps (TApp t b i) args = TApp (TApps t (fst x)) (fst (snd x)) (snd (snd x)) /\ (b, i) :: args = fst x ++ [snd x]).
  Proof.
    induct args; simpl; eauto.
    {
      eexists ([], (_, _)); simpl; eauto.
    }
    destruct a as [b' i'].
    specialize (IHargs (TApp t b i) b' i').
    destruct IHargs as (x & H1 & H2).
    destruct x as [front last]; simpl in *.
    eexists ((b, i) :: front, last); simpl in *.
    split; eauto.
    f_equal; eauto.
  Qed.

  Definition TApps_TRec_dec args k t :
    sumor (sig (fun x => TApps (TRec k t) args = TApp (TApps (TRec k t) (fst x)) (fst (snd x)) (snd (snd x)) /\ args = fst x ++ [snd x])) (TApps (TRec k t) args = TRec k t /\ args = []).
  Proof.
    induct args; simpl; eauto.
    destruct a as [b i]; simpl in *.
    left.
    eapply TApps_TApp.
  Qed.
  
  Lemma TApps_app_end args t b i : TApp (TApps t args) b i = TApps t (args ++ [(b, i)]).
  Proof.
    induct args; simpl; eauto.
    destruct a.
    eauto.
  Qed.

  Lemma par_preserves_TApps_TRec k t1 args t' :
    par (TApps (TRec k t1) args) t' ->
    exists t1',
      t' = TApps (TRec k t1') args /\
      par t1 t1'.
  Proof.
    induct 1; simpl; try solve [
                           destruct (TApps_TRec_dec args k t1) as [ [ [? ?] [Heq ?] ] | [Heq ?]]; subst; simpl in * ; try rewrite Heq in *; dis
                         ]; eauto.
    {
      destruct (TApps_TRec_dec args k t1) as [ [ [front [b' i'] ] [Heq Hargs] ] | [Heq Hargs]]; simpl in * ; rewrite Heq in *; try dis.
      invert x.
      edestruct IHpar as (t1' & ? & Ht1t1'); eauto.
      subst.
      exists t1'.
      split; eauto.
      eapply TApps_app_end.
    }
    {
      destruct (TApps_TRec_dec args k t1) as [ [ [front [b' i'] ] [Heq Hargs] ] | [Heq Hargs] ]; subst; simpl in * ; try rewrite Heq in *; try dis.
      invert x.
      eauto.
    }
    {
      destruct (TApps_TRec_dec args k t1) as [ [ [front [b' i'] ] [Heq Hargs] ] | [Heq Hargs] ]; subst; simpl in * ; try rewrite Heq in *; try dis.
      invert x.
      clear Heq.
      destruct (TApps_TRec_dec front k t1) as [ [ [? ?] [Heq ?] ] | [Heq ?]]; simpl in * ; rewrite Heq in *; dis.
    }
  Qed.
  
  Lemma pars_preserves_TApps_TRec k t1 args t' :
    par^* (TApps (TRec k t1) args) t' ->
    exists t1',
      t' = TApps (TRec k t1') args /\
      par^* t1 t1'.
  Proof.
    induct 1; simpl; eauto.
    eapply par_preserves_TApps_TRec in H; eauto.
    openhyp.
    subst.
    edestruct IHtrc; eauto.
    openhyp.
    subst.
    repeat eexists_split; eauto.
  Qed.
  
  Lemma invert_cong_TApps_TRec L k t args k' t' args' :
    let t1 := TApps (TRec k t) args in
    let t1' := TApps (TRec k' t') args' in
    cong L t1 t1' ->
    k = k' /\
    cong L t t' /\
    Forall2 (fun p p' => fst p = fst p' /\ idxeq L (snd p) (snd p') (fst p)) args args'.
  Proof.
    simpl.
    induct 1; simpl; try solve [
                           destruct (TApps_TRec_dec args k t) as [ [ [? ?] [Heq ?] ] | [Heq ?]]; subst; simpl in * ; try rewrite Heq in *; dis
                         ]; eauto.
    {
      destruct (TApps_TRec_dec args k t) as [ [ [? ?] [Heq ?] ] | [Heq ?]]; subst; simpl in * ; try rewrite Heq in *; try dis.
      invert x0.
      clear Heq.
      destruct (TApps_TRec_dec args' k' t') as [ [ [? ?] [Heq ?] ] | [Heq ?]]; subst; simpl in * ; try rewrite Heq in *; try dis.
      invert x.
      destruct p; destruct p0; simpl in *; subst.
      edestruct IHcong as (? & Htt' & Hargs); eauto.
      subst.
      repeat try_split; eauto.
      eapply Forall2_app; eauto.
    }
    {
      destruct (TApps_TRec_dec args k t) as [ [ [? ?] [Heq ?] ] | [Heq ?]]; subst; simpl in * ; try rewrite Heq in *; try dis.
      invert x0.
      clear Heq.
      destruct (TApps_TRec_dec args' k' t') as [ [ [? ?] [Heq ?] ] | [Heq ?]]; subst; simpl in * ; try rewrite Heq in *; try dis.
      invert x.
      repeat try_split; eauto.
    }
  Qed.
  
  Fixpoint KArrows args result :=
    match args with
    | [] => result
    | arg :: args => KArrow arg (KArrows args result)
    end.

  Lemma bkinding_TApps_invert L :
    forall args t K k,
      bkinding L K (TApps t args) k ->
      bkinding L K t (KArrows (map fst args) k) /\
      Forall (fun p => bsorting L (snd p) (fst p)) args.
  Proof.
    induct args; simpl; intros t K k H; eauto.
    destruct a as [b i].
    eapply IHargs in H.
    destruct H as [H1 H2].
    invert H1.
    eauto.
  Qed.

  Lemma invert_tyeq1_TApps_TRec L k t args k' t' args' K k0 :
    let t1 := TApps (TRec k t) args in
    let t1' := TApps (TRec k' t') args' in
    tyeq1 L K t1 t1' k0 ->
    let bs := map get_bsort L in
    bkinding bs K t1 k0 ->
    bkinding bs K t1' k0 ->
    wfsorts1 L ->
    k = k' /\
    let k0' := KArrows (map fst args) k0 in
    tyeq1 L (k0' :: K) t t' k0' /\
    Forall2 (fun p p' => fst p = fst p' /\ idxeq L (snd p) (snd p') (fst p)) args args'.
  Proof.
    simpl.
    intros H H1 H2 HL.
    eapply tyeq1_par in H; eauto.
    edestruct H as (r1 & r1' & Ht1r1 & Ht1'r1' & Hr1r1' & Hr1 & Hr1'); eauto.
    eapply pars_preserves_TApps_TRec in Ht1r1.
    openhyp; subst.
    eapply pars_preserves_TApps_TRec in Ht1'r1'.
    openhyp; subst.
    eapply invert_cong_TApps_TRec in Hr1r1'.
    openhyp; subst.
    eapply bkinding_TApps_invert in H1.
    destruct H1 as [H1 Hargs].
    invert H1.
    eapply bkinding_TApps_invert in H2.
    destruct H2 as [H2 Hargs'].
    invert H2.
    repeat try_split; eauto.
    {
      eapply TyEq1Trans.
      {
        eapply pars_tyeq1; eauto.
      }
      eapply TyEq1Trans.
      {
        eapply cong_tyeq1; eauto using pars_preserves_bkinding.
      }
      {
        eapply TyEq1Sym.
        eapply pars_tyeq1; eauto using pars_preserves_bkinding.
      }
      {
        eapply pars_preserves_bkinding; eauto.
      }
      {
        eapply pars_preserves_bkinding; eauto.
      }
    }
  Qed.

  Lemma bkinding_TApps L :
    forall cs t K k,
      bkinding L K t (KArrows (map fst cs) k)->
      Forall (fun p => bsorting L (snd p) (fst p)) cs ->
      bkinding L K (TApps t cs) k.
  Proof.
    induct cs; simpl; intros t K k Ht Hcs; invert Hcs; eauto.
    destruct a as (b & i); simpl in *.
    eauto.
  Qed.

(*  
  Lemma cong_preserves_TApps_TRec L k t args t1' :
    let t1 := TApps (TRec k t) args in
    cong L t1 t1' ->
    exists t' args',
    t1' = TApps (TRec k t') args' ->
    cong L t t' /\
    Forall2 (fun p p' => fst p = fst p' /\ idxeq L (snd p) (snd p') (fst p)) args args'.
  Proof.
  Qed.
 *)
  
  Lemma invert_tyeq1_TApps_TRec_TArrow L args k3 t3 t1 i t2 K k :
    let t := TApps (TRec k3 t3) args in
    let t' := TArrow t1 i t2 in
    tyeq1 L K t t' k ->
    let bs := map get_bsort L in
    bkinding bs K t k ->
    bkinding bs K t' k ->
    wfsorts1 L ->
    False.
  Proof.
    simpl.
    intros H H1 H2 HL.
    eapply bkinding_TApps_invert in H1.
    destruct H1 as (H1 & Hargs).
    invert H1.
    invert H2.
    eapply tyeq1_par in H; eauto using bkinding_TApps.
    edestruct H as (r1 & r1' & Ht1r1 & Ht1'r1' & Hr1r1' & Hr1 & Hr1'); eauto.
    eapply pars_preserves_TApps_TRec in Ht1r1.
    openhyp; subst.
    eapply pars_preserves_TArrow in Ht1'r1'.
    openhyp; subst.
    set (k' := KArrows (map fst args) KType) in *.
    destruct (TApps_TRec_dec args k' x) as [ [ [? ?] [Heq ?] ] | [Heq ?]]; subst; simpl in * ; try rewrite Heq in *; invert Hr1r1'.
  Qed.

  Lemma TyEq1Beta' L K s t b i t' k :
    t' = subst0_i_t i t ->
    bkinding (map get_bsort L) K (TApp (TAbs s t) b i) k ->
    tyeq1 L K (TApp (TAbs s t) b i) t' k.
  Proof.
    intros; subst; eauto.
  Qed.
  
  Lemma TyEq1BetaT' L K k t1 t2 t' k2 :
    t' = subst0_t_t t2 t1 ->
    bkinding (map get_bsort L) K (TAppT (TAbsT k t1) t2) k2 ->
    tyeq1 L K (TAppT (TAbsT k t1) t2) t' k2.
  Proof.
    intros; subst; eauto.
  Qed.
  
  Lemma tyeq1_shift_t_t L K t t' k :
    tyeq1 L K t t' k ->
    forall ls x,
      let n := length ls in
      (* x <= length K -> *)
      tyeq1 L (insert ls x K) (shift_t_t n x t) (shift_t_t n x t') k.
  Proof.
    simpl.
    induct 1; simpl; try rename x into y; intros ls x (* Hx *); try solve [econstructor; eauto using bkinding_shift_t_t].
    {
      econstructor.
      eapply IHtyeq1 with (x := S x); simpl; eauto with db_la.
    }
    {
      econstructor.
      eapply IHtyeq1 with (x := S x); simpl; eauto with db_la.
    }
    {
      econstructor.
      eapply IHtyeq1 with (x := S x); simpl; eauto with db_la.
    }
    {
      cases (x <=? y); try la.
      {
        econstructor.
        erewrite nth_error_insert'; eauto.
      }
      {
        econstructor.
        erewrite nth_error_before_insert'; eauto.
      }
    }
    {
      eapply TyEq1Beta'.
      {
        unfold subst0_i_t.
        rewrite shift_t_t_subst_i_t.
        eauto.
      }
      {
        invert_bkindings.
        eauto using bkinding_shift_t_t'.
      }
    }
    {
      eapply TyEq1BetaT'.
      {
        unfold subst0_t_t.
        rewrite shift_t_t_subst_out by la.
        eauto.
      }
      {
        invert_bkindings.
        econstructor; eauto using bkinding_shift_t_t'.
        econstructor; eauto.
        eapply bkinding_shift_t_t' with (x := S x) (K := _ :: _); eauto.
      }
    }
  Qed.
  
  Lemma tyeq1_subst_t_t L K t t' k_b :
    tyeq1 L K t t' k_b ->
    forall x k_v v,
      nth_error K x = Some k_v ->
      bkinding (map get_bsort L) (my_skipn K (1 + x)) v k_v ->
      (* kinding1 L K t k -> *)
      (* kinding1 L K t' k -> *)
      tyeq1 L (removen x K) (subst_t_t x (shift_t_t x 0 v) t) (subst_t_t x (shift_t_t x 0 v) t') k_b.
  Proof.
    induct 1;
      simpl; try rename x into y; intros x k_v v Hx Hv; subst; eauto using bkinding_subst_t_t.
    {
      (* Case TAbs *)
      econstructor; eauto with db_la.
      unfold shift0_i_t.
      rewrite shift_i_t_shift_t_t.
      eapply IHtyeq1; eauto with db_la.
      eapply bkinding_shift_i_t_1_0; eauto.
    }
    {
      (* Case TQuan *)
      unfold shift0_t_t.
      rewrite shift_t_t_shift_merge by la.
      econstructor; eauto with db_la.
      rewrite plus_comm.
      eapply IHtyeq1 with (x := S x); eauto with db_la.
    }
    {
      (* Case TQuanI *)
      econstructor; eauto with db_la.
      unfold shift0_i_t.
      rewrite shift_i_t_shift_t_t.
      eapply IHtyeq1; eauto using wfsort1_wellscoped_s' with db_la.
      eapply bkinding_shift_i_t_1_0; eauto.
    }
    {
      (* Case TRec *)
      unfold shift0_t_t.
      rewrite shift_t_t_shift_merge by la.
      econstructor; eauto with db_la.
      rewrite plus_comm.
      eapply IHtyeq1 with (x := S x); eauto with db_la.
    }
    {
      (* Case TAbsT *)
      unfold shift0_t_t.
      rewrite shift_t_t_shift_merge by la.
      econstructor; eauto with db_la.
      rewrite plus_comm.
      eapply IHtyeq1 with (x := S x); eauto with db_la.
    }
    {
      eapply TyEq1Refl.
      cases (y <=>? x); eauto; subst.
      {
        econstructor.
        erewrite removen_lt by eauto with db_la.
        eauto.
      }
      {
        assert (k_v = k) by equality; subst.
        rewrite removen_firstn_my_skipn.
        eapply bkinding_shift_t_t' with (x := 0); eauto.
        eapply nth_error_Some_lt in Hx.
        rewrite length_firstn_le by la.
        eauto.
      }
      {
        econstructor.
        erewrite removen_gt by eauto with db_la.
        eauto.
      }
    }
    {
      eapply TyEq1Beta'.
      {
        unfold subst0_i_t, shift0_i_t.
        rewrite subst_i_t_subst_t_t.
        rewrite subst_i_t_shift_avoid by la.
        simpl.
        rewrite shift_i_t_0.
        eauto.
      }
      {
        invert_bkindings.
        unfold shift0_i_t.
        rewrite shift_i_t_shift_t_t.
        eauto using bkinding_subst_t_t, bkinding_shift_i_t_1_0.
      }
    }
    {
      eapply TyEq1BetaT'.
      {
        unfold subst0_t_t, shift0_t_t.
        rewrite subst_t_t_subst by la.
        eauto.
      }
      {
        invert_bkindings.
        rewrite shift0_t_t_shift_0.
        econstructor; eauto using bkinding_subst_t_t.
        econstructor; eauto.
        eapply bkinding_subst_t_t with (x := S x) (K := _ :: _); eauto.
      }
    }
  Qed.
  
  Lemma bkinding_shift_i_t' :
    forall L K c k,
      bkinding L K c k ->
      forall x ls n,
        x <= length L ->
        n = length ls ->
        bkinding (firstn x L ++ ls ++ my_skipn L x) K (shift_i_t n x c) k.
  Proof.
    intros; subst; eapply bkinding_shift_i_t; eauto.
  Qed.
  
  Lemma tyeq1_shift_i_t L K t t' k :
    tyeq1 L K t t' k ->
    forall x ls ,
      let n := length ls in
      x <= length L ->
      wellscoped_ss L ->
      wellscoped_t (length L) t ->
      wellscoped_t (length L) t' ->
      tyeq1 (shift_i_ss n (firstn x L) ++ ls ++ my_skipn L x) K (shift_i_t n x t) (shift_i_t n x t') k.
  Proof.
    simpl.
    induct 1; simpl; try rename x into y; intros x ls Hx HL Ht Ht'; try invert1 Ht; try invert1 Ht'; try solve [econstructor; simpl; eauto using idxeq_shift_i_i with db_la].
    {
      (* Case TAbs *)
      econstructor; eauto.
      eapply IHtyeq1 with (x := S x); simpl; eauto with db_la.
    }
    {
      (* Case TQuanI *)
      econstructor; eauto using sorteq_shift_i_k.
      specialize (IHtyeq1 (S x) ls).
      simpl in *.
      repeat rewrite length_firstn_le in * by la.
      eapply IHtyeq1; simpl; eauto with db_la.
    }
  Lemma bsorting_shift_i_i' :
    forall L c s,
      bsorting L c s ->
      forall x ls n,
        x <= length L ->
        n = length ls ->
        bsorting (firstn x L ++ ls ++ my_skipn L x) (shift_i_i n x c) s.
  Proof.
    intros; subst; eapply bsorting_shift_i_i; eauto.
  Qed.
  
    {
      eapply TyEq1Beta'.
      {
        unfold subst0_i_t.
        rewrite shift_i_t_subst_out by la.
        eauto.
      }
      {
        invert_bkindings.
        econstructor; eauto.
        {
          econstructor; eauto.
          rewrite get_bsort_shift_i_ss_insert.
          eapply bkinding_shift_i_t' with (x := S x) (L := _ :: _); simpl; eauto with db_la.
          rewrite map_length; la.
        }
        {
          rewrite get_bsort_shift_i_ss_insert.
          eapply bsorting_shift_i_i'; eauto with db_la.
        }
      }
    }
    {
      eapply TyEq1BetaT'.
      {
        unfold subst0_t_t.
        rewrite shift_i_t_subst_t_t.
        eauto.
      }
      {
        invert_bkindings.
        econstructor; eauto.
        {
          econstructor; eauto.
          rewrite get_bsort_shift_i_ss_insert.
          eapply bkinding_shift_i_t'; simpl; eauto with db_la.
        }
        {
          rewrite get_bsort_shift_i_ss_insert.
          eapply bkinding_shift_i_t'; simpl; eauto with db_la.
        }
      }
    }
    {
      eapply TyEq1Refl.
      rewrite get_bsort_shift_i_ss_insert.
      eapply bkinding_shift_i_t'; simpl; eauto with db_la.
    }
    {
      eapply TyEq1Trans; [eapply IHtyeq1_1 | eapply IHtyeq1_2 |];
      eauto using bkinding_wellscoped_t', bkinding_shift_i_t with db_la.
      rewrite get_bsort_shift_i_ss_insert.
      eapply bkinding_shift_i_t'; eauto with db_la.
    }
  Qed.

  Lemma tyeq1_shift0_i_t L K t t' k s :
    tyeq1 L K t t' k ->
    wellscoped_ss L ->
    wellscoped_t (length L) t ->
    wellscoped_t (length L) t' ->
    tyeq1 (s :: L) K (shift0_i_t t) (shift0_i_t t') k.
  Proof.
    intros H; intros.
    eapply tyeq1_shift_i_t with (x := 0) (ls := [s]) in H; eauto with db_la.
    simpl in *.
    rewrite my_skipn_0 in *.
    eauto.
  Qed.
  
  Lemma tyeq1_subst_i_t L K t t' k :
    tyeq1 L K t t' k ->
    forall x s v, 
      nth_error L x = Some s ->
      sorting1 (my_skipn L (1 + x)) v s ->
      let bs := map get_bsort L in
      bkinding bs K t k ->
      bkinding bs K t' k ->
      wfsorts1 L ->
      tyeq1 (subst_i_ss v (firstn x L) ++ my_skipn L (1 + x)) K (subst_i_t x (shift_i_i x 0 v) t) (subst_i_t x (shift_i_i x 0 v) t') k.
  Proof.
    simpl.
    induct 1;
      simpl; try rename x into y; try rename s into s'; try rename s into s''; intros x s v Hx Hv Hb Hb' HL; try invert1 Hb; try invert1 Hb'; try solve [econstructor; eauto using subst_i_i_eqv_eqv with db_idxeq db_sorteq].
    {
      (* Case TAbs *)
      repeat rewrite shift0_i_i_shift_0.
      econstructor; eauto.
      eapply IHtyeq1 with (x := S x); eauto.
    }
    {
      (* Case TQuanI *)
      repeat rewrite shift0_i_i_shift_0.
      econstructor; eauto.
      {
        eapply subst_i_s_eqv_eqv; eauto with db_idxeq.
      }
      specialize (IHtyeq1 (S x) s v).
      simpl in *.
      copy Hx Hcmp.
      eapply nth_error_Some_lt in Hcmp.
      rewrite length_firstn_le in * by la.
      eapply IHtyeq1; eauto.
      invert H; simpl in *; eauto.
    }
    {
      assert (k0 = k1 /\ k3 = k1).
      {
        copy H HH.
        eapply tyeq1_bkinding_same_k_1 in H; eauto.
        invert H.
        eapply tyeq1_bkinding_same_k_2 in HH; eauto.
        invert HH.
        eauto.
      }
      openhyp; subst.
      econstructor; eauto using subst_i_i_eqv_eqv with db_idxeq db_sorteq.
    }
    {
      eapply TyEq1Beta'.
      {
        repeat rewrite shift0_i_i_shift_0.
        unfold subst0_i_t, shift0_i_t.
        rewrite subst_i_t_subst by la.
        repeat rewrite shift0_i_i_shift_0.
        eauto.
      }
      {
        invert_bkindings.
        rewrite shift0_i_i_shift_0.
        econstructor; eauto.
        {
          econstructor; eauto.
          rewrite get_bsort_subst_i_ss_remove.
          eapply bkinding_subst_i_t with (x := S x) (L := _ :: _); simpl; eauto with db_la.
          {
            erewrite map_nth_error; eauto.
          }
          {
            eapply sorting1_bsorting''; eauto.
            rewrite <- map_my_skipn.
            eauto.
          }
        }
        {
          rewrite get_bsort_subst_i_ss_remove.
          eapply bsorting_subst_i_i; eauto with db_la.
          {
            erewrite map_nth_error; eauto.
          }
          {
            eapply sorting1_bsorting''; eauto.
            rewrite <- map_my_skipn.
            eauto.
          }
        }
      }
    }
    {
      eapply TyEq1BetaT'.
      {
        unfold subst0_t_t, shift0_t_t.
        rewrite subst_i_t_subst_t_t.
        eauto.
      }
      {
        invert_bkindings.
        econstructor; eauto.
        {
          econstructor; eauto.
          rewrite get_bsort_subst_i_ss_remove.
          eapply bkinding_subst_i_t; simpl; eauto with db_la.
          {
            erewrite map_nth_error; eauto.
          }
          {
            eapply sorting1_bsorting''; eauto.
            rewrite <- map_my_skipn.
            eauto.
          }
        }
        {
          rewrite get_bsort_subst_i_ss_remove.
          eapply bkinding_subst_i_t; simpl; eauto with db_la.
          {
            erewrite map_nth_error; eauto.
          }
          {
            eapply sorting1_bsorting''; eauto.
            rewrite <- map_my_skipn.
            eauto.
          }
        }
      }
    }
    {
      eapply TyEq1Refl.
      invert_bkindings.
      rewrite get_bsort_subst_i_ss_remove.
      eapply bkinding_subst_i_t; simpl; eauto with db_la.
      {
        erewrite map_nth_error; eauto.
      }
      {
        eapply sorting1_bsorting''; eauto.
        rewrite <- map_my_skipn.
        eauto.
      }
    }
    {
      eapply TyEq1Trans; [eapply IHtyeq1_1 | eapply IHtyeq1_2 |];
      eauto using bkinding_wellscoped_t', bkinding_shift_i_t with db_la.
      rewrite get_bsort_subst_i_ss_remove.
      eapply bkinding_subst_i_t; eauto with db_la.
      {
        erewrite map_nth_error; eauto.
      }
      {
        eapply sorting1_bsorting''; eauto.
        rewrite <- map_my_skipn.
        eauto.
      }
    }
  Qed.

  Lemma tyeq1_shift_t_t' L K t t' k :
    tyeq1 L K t t' k ->
    forall ls x n,
      n = length ls ->
      tyeq1 L (insert ls x K) (shift_t_t n x t) (shift_t_t n x t') k.
  Proof.
    intros; subst; eapply tyeq1_shift_t_t; eauto.
  Qed.
  
  Lemma tyeq1_subst_t_t_eqv_eq t L K k_b x k_v v v' :
      nth_error K x = Some k_v ->
      tyeq1 L (my_skipn K (1 + x)) v v' k_v ->
      let bs := map get_bsort L in
      bkinding bs (my_skipn K (1 + x)) v k_v ->
      bkinding bs (my_skipn K (1 + x)) v' k_v ->
      bkinding bs K t k_b ->
      wellscoped_ss L ->
      tyeq1 L (removen x K) (subst_t_t x (shift_t_t x 0 v) t) (subst_t_t x (shift_t_t x 0 v') t) k_b.
  Proof.
    induct t;
      simpl; intros Hx Hvv' Hv Hv' Ht HL; try invert1 Ht; subst; eauto with db_idxeq db_sorteq.
    {
      cases (x <=>? x0); eauto; subst.
      {
        eapply TyEq1Refl.
        econstructor.
        erewrite removen_lt by eauto with db_la.
        eauto.
      }
      {
        rewrite removen_firstn_my_skipn.
        assert (k_b = k_v) by equality; subst.
        copy Hx Hcmp.
        eapply nth_error_Some_lt in Hcmp.
        eapply tyeq1_shift_t_t' with (x := 0); eauto with db_la.
        rewrite length_firstn_le by la.
        eauto.
      }
      {
        eapply TyEq1Refl.
        econstructor.
        erewrite removen_gt by eauto with db_la.
        eauto.
      }
    }
    {
      (* Case TAbs *)
      econstructor; eauto with db_la.
      unfold shift0_i_t.
      repeat rewrite shift_i_t_shift_t_t.
      eapply IHt; eauto using bkinding_shift_i_t_1_0 with db_la.
      eapply tyeq1_shift0_i_t; eauto using bkinding_wellscoped_t' with db_la.
    }
    {
      (* Case TQuan *)
      repeat rewrite shift0_t_t_shift_0.
      econstructor; eauto with db_la.
      eapply IHt with (x := S x) (K := _ :: _); eauto with db_la.
    }
    {
      (* Case TQuanI *)
      econstructor; eauto with db_la db_idxeq db_sorteq.
      unfold shift0_i_t.
      rewrite shift_i_t_shift_t_t.
      repeat rewrite shift_i_t_shift_t_t.
      eapply IHt; eauto using bkinding_shift_i_t_1_0, wfsort1_wellscoped_s' with db_la.
      {
        eapply tyeq1_shift0_i_t; eauto using bkinding_wellscoped_t' with db_la.
      }
    }
    {
      (* Case TRec *)
      repeat rewrite shift0_t_t_shift_0.
      econstructor; eauto with db_la.
      eapply IHt with (x := S x) (K := _ :: _); eauto with db_la.
    }
    {
      (* Case TAbsT *)
      repeat rewrite shift0_t_t_shift_0.
      econstructor; eauto with db_la.
      eapply IHt with (x := S x) (K := _ :: _); eauto with db_la.
    }
  Qed.
  
  Lemma tyeq1_subst_t_t_eqv_eqv L K t t' k_b :
    tyeq1 L K t t' k_b ->
    forall x k_v v v',
      nth_error K x = Some k_v ->
      tyeq1 L (my_skipn K (1 + x)) v v' k_v ->
      let bs := map get_bsort L in
      bkinding bs (my_skipn K (1 + x)) v k_v ->
      bkinding bs (my_skipn K (1 + x)) v' k_v ->
      bkinding bs K t k_b ->
      bkinding bs K t' k_b ->
      wellscoped_ss L ->
      tyeq1 L (removen x K) (subst_t_t x (shift_t_t x 0 v) t) (subst_t_t x (shift_t_t x 0 v') t') k_b.
  Proof.
    induct 1;
      simpl; try rename x into y; intros x k_v v v' Hx Hvv' Hv Hv' Hb Hb' HL; subst; try invert1 Hb; try invert1 Hb'; eauto using bkinding_subst_t_t.
    {
      (* Case TAbs *)
      econstructor; eauto with db_la.
      unfold shift0_i_t.
      repeat rewrite shift_i_t_shift_t_t.
      eapply IHtyeq1; eauto using bkinding_shift_i_t_1_0 with db_la.
      eapply tyeq1_shift0_i_t; eauto using bkinding_wellscoped_t' with db_la.
    }
    {
      (* Case TQuan *)
      repeat rewrite shift0_t_t_shift_0.
      econstructor; eauto with db_la.
      eapply IHtyeq1 with (x := S x); eauto with db_la.
    }
    {
      (* Case TQuanI *)
      econstructor; eauto with db_la.
      unfold shift0_i_t.
      rewrite shift_i_t_shift_t_t.
      repeat rewrite shift_i_t_shift_t_t.
      eapply IHtyeq1; eauto using bkinding_shift_i_t_1_0, wfsort1_wellscoped_s' with db_la.
      {
        eapply tyeq1_shift0_i_t; eauto using bkinding_wellscoped_t' with db_la.
      }
      {
        invert H; simpl in *; eauto.
      }
    }
    {
      (* Case TRec *)
      repeat rewrite shift0_t_t_shift_0.
      econstructor; eauto with db_la.
      eapply IHtyeq1 with (x := S x); eauto with db_la.
    }
    {
      (* Case TAbsT *)
      repeat rewrite shift0_t_t_shift_0.
      econstructor; eauto with db_la.
      eapply IHtyeq1 with (x := S x); eauto with db_la.
    }
    {
      assert (k0 = k1 /\ k3 = k1).
      {
        copy H HH.
        eapply tyeq1_bkinding_same_k_1 in H; eauto.
        invert H.
        eapply tyeq1_bkinding_same_k_2 in HH; eauto.
        invert HH.
        eauto.
      }
      openhyp; subst.
      eauto using bkinding_subst_t_t.
    }
    {
      cases (y <=>? x); eauto; subst.
      {
        econstructor.
        erewrite removen_lt by eauto with db_la.
        eauto.
      }
      {
        assert (k_v = k) by equality; subst.
        rewrite removen_firstn_my_skipn.
        eapply tyeq1_shift_t_t' with (x := 0); eauto.
        eapply nth_error_Some_lt in Hx.
        rewrite length_firstn_le by la.
        eauto.
      }
      {
        econstructor.
        erewrite removen_gt by eauto with db_la.
        eauto.
      }
    }
    {
      eapply TyEq1Trans; [eapply TyEq1Beta | | ].
      {
        invert_bkindings.
        unfold shift0_i_t.
        rewrite shift_i_t_shift_t_t.
        eauto using bkinding_subst_t_t, bkinding_shift_i_t_1_0.
      }
      {
        unfold subst0_i_t, shift0_i_t.
        rewrite subst_i_t_subst_t_t.
        rewrite subst_i_t_shift_avoid by la.
        simpl.
        rewrite shift_i_t_0.
        eapply tyeq1_subst_t_t_eqv_eq; eauto.
      }
      {
        unfold subst0_i_t, shift0_i_t.
        rewrite subst_i_t_subst_t_t.
        rewrite subst_i_t_shift_avoid by la.
        simpl.
        rewrite shift_i_t_0.
        invert_bkindings.
        eapply bkinding_subst_t_t; eauto.
      }
    }
    {
      eapply TyEq1Trans; [eapply TyEq1BetaT | | ].
      {
        invert_bkindings.
        rewrite shift0_t_t_shift_0.
        econstructor; eauto using bkinding_subst_t_t.
        econstructor; eauto.
        eapply bkinding_subst_t_t with (x := S x) (K := _ :: _); eauto.
      }
      {
        unfold subst0_t_t.
        rewrite <- subst_t_t_subst by la.
        eapply tyeq1_subst_t_t_eqv_eq; eauto.
      }
      {
        invert_bkindings.
        unfold subst0_t_t.
        rewrite <- subst_t_t_subst by la.
        eapply bkinding_subst_t_t; eauto.
      }
    }
    {
      eapply tyeq1_subst_t_t_eqv_eq; eauto.
    }
    {
      eapply TyEq1Trans; eauto.
      eapply bkinding_subst_t_t; eauto.
    }
  Qed.

  Lemma tyeq1_subst_t_t_eqv_eqv_0 L K t t' k v v' k_v :
    tyeq1 L (k_v :: K) t t' k ->
    tyeq1 L K v v' k_v ->
    let bs := map get_bsort L in
    bkinding bs K v k_v ->
    bkinding bs K v' k_v ->
    bkinding bs (k_v :: K) t k ->
    bkinding bs (k_v :: K) t' k ->
    wellscoped_ss L ->
    tyeq1 L K (subst_t_t 0 v t) (subst_t_t 0 v' t') k.
  Proof.
    intros H; intros.
    specialize (@tyeq1_subst_t_t_eqv_eqv L (k_v :: K) t t' k H 0 k_v v v'); intros Hsubst.
    simpl in *.
    repeat rewrite shift_t_t_0 in *.
    rewrite my_skipn_0 in *.
    eapply Hsubst; simpl; eauto.
  Qed.
  
  Lemma tyeq1_subst_t_t_0 L K t t' k_b k_v v :
    tyeq1 L (k_v :: K) t t' k_b ->
    bkinding (map get_bsort L) K v k_v ->
    tyeq1 L K (subst_t_t 0 v t) (subst_t_t 0 v t') k_b.
  Proof.
    intros H; intros.
    specialize (@tyeq1_subst_t_t L (k_v :: K) t t' k_b H 0 k_v v); intros Hsubst.
    simpl in *.
    repeat rewrite shift_t_t_0 in *.
    rewrite my_skipn_0 in *.
    eapply Hsubst; eauto.
  Qed.
  
  Lemma tyeq1_subst_i_t_0 L K t t' k s v :
    tyeq1 (s :: L) K t t' k ->
    sorting1 L v s ->
    let bs := map get_bsort (s :: L) in
    bkinding bs K t k ->
    bkinding bs K t' k ->
    wfsorts1 (s :: L) ->
    tyeq1 L K (subst_i_t 0 v t) (subst_i_t 0 v t') k.
  Proof.
    simpl.
    intros H; intros.
    specialize (@tyeq1_subst_i_t (s :: L) K t t' k H 0 s v); intros Hsubst.
    simpl in *.
    repeat rewrite shift_i_i_0 in *.
    rewrite my_skipn_0 in *.
    eapply Hsubst; eauto.
  Qed.
  
  Lemma par_preserves_TBinOp opr t1 t2 t' :
    par (TBinOp opr t1 t2) t' ->
    exists t1' t2',
      t' = TBinOp opr t1' t2' /\
      par t1 t1' /\
      par t2 t2'.
  Proof.
    induct 1; simpl; eauto.
  Qed.
  
  Lemma pars_preserves_TBinOp opr t1 t2 t' :
    par^* (TBinOp opr t1 t2) t' ->
    exists t1' t2',
      t' = TBinOp opr t1' t2' /\
      par^* t1 t1' /\
      par^* t2 t2'.
  Proof.
    induct 1; simpl; eauto using par_preserves_TBinOp.
    eapply par_preserves_TBinOp in H; eauto.
    openhyp.
    subst.
    edestruct IHtrc; eauto.
    openhyp.
    subst.
    repeat eexists_split; eauto.
  Qed.

  Lemma invert_tyeq1_TBinOp_TArrow L opr ta tb t1 i t2 K k :
    let t := TBinOp opr ta tb in
    let t' := TArrow t1 i t2 in
    tyeq1 L K t t' k ->
    let bs := map get_bsort L in
    bkinding bs K t k ->
    bkinding bs K t' k ->
    wfsorts1 L ->
    False.
  Proof.
    simpl.
    intros H H1 H2 HL.
    invert H1.
    invert H2.
    eapply tyeq1_par in H; eauto.
    edestruct H as (r1 & r1' & Ht1r1 & Ht1'r1' & Hr1r1' & Hr1 & Hr1'); eauto.
    eapply pars_preserves_TBinOp in Ht1r1.
    openhyp.
    subst.
    eapply pars_preserves_TArrow in Ht1'r1'.
    openhyp.
    subst.
    invert Hr1r1'.
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
    eapply bsort_default_value.
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
  
  (* conditional eq *)
  Definition cond_eq A L (k k' : A) := 
    let bs := map get_bsort L in
    let ps := strip_subsets L in
    let p := and_all ps in
    forall_ bs (lift1 bs (fun p : Prop => p -> k = k') (interp_p bs p)).

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
  
  Lemma invert_tyeq1_TQuan L q1 k1 t1 q2 k2 t2 K k :
    let t := TQuan q1 k1 t1 in
    let t' := TQuan q2 k2 t2 in
    tyeq1 L K t t' k ->
    let bs := map get_bsort L in
    bkinding bs K t k ->
    bkinding bs K t' k ->
    wfsorts1 L ->
    q1 = q2 /\
    k1 = k2 /\
    tyeq1 L (k1 :: K) t1 t2 k.
  Proof.
    simpl.
    intros H H1 H2 HL.
    invert H1.
    invert H2.
    eapply tyeq1_par in H; eauto.
    edestruct H as (r1 & r1' & Ht1r1 & Ht1'r1' & Hr1r1' & Hr1 & Hr1'); eauto.
    eapply pars_preserves_TQuan in Ht1r1.
    openhyp; subst.
    eapply pars_preserves_TQuan in Ht1'r1'.
    openhyp; subst.
    invert Hr1r1'.
    repeat try_split; eauto.
    {
      eapply TyEq1Trans.
      {
        eapply pars_tyeq1; eauto.
      }
      eapply TyEq1Trans.
      {
        eapply cong_tyeq1; eauto using pars_preserves_bkinding.
      }
      {
        eapply TyEq1Sym.
        eapply pars_tyeq1; eauto using pars_preserves_bkinding.
      }
      {
        eapply pars_preserves_bkinding; eauto.
      }
      {
        eapply pars_preserves_bkinding; eauto.
      }
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
  
  Lemma invert_tyeq1_TBinOp L opr t1 t2 opr' t1' t2' K k :
    let t := TBinOp opr t1 t2 in
    let t' := TBinOp opr' t1' t2' in
    tyeq1 L K t t' k ->
    let bs := map get_bsort L in
    bkinding bs K t k ->
    bkinding bs K t' k ->
    wfsorts1 L ->
    opr = opr' /\
    tyeq1 L K t1 t1' k /\
    tyeq1 L K t2 t2' k.
  Proof.
    simpl.
    intros H H1 H2 HL.
    invert H1.
    invert H2.
    eapply tyeq1_par in H; eauto.
    edestruct H as (r1 & r1' & Ht1r1 & Ht1'r1' & Hr1r1' & Hr1 & Hr1'); eauto.
    eapply pars_preserves_TBinOp in Ht1r1.
    openhyp; subst.
    eapply pars_preserves_TBinOp in Ht1'r1'.
    openhyp; subst.
    invert Hr1r1'.
    repeat try_split; eauto.
    {
      eapply TyEq1Trans.
      {
        eapply pars_tyeq1; eauto.
      }
      eapply TyEq1Trans.
      {
        eapply cong_tyeq1; eauto using pars_preserves_bkinding.
      }
      {
        eapply TyEq1Sym.
        eapply pars_tyeq1; eauto using pars_preserves_bkinding.
      }
      {
        eapply pars_preserves_bkinding; eauto.
      }
      {
        eapply pars_preserves_bkinding; eauto.
      }
    }
    {
      eapply TyEq1Trans.
      {
        eapply pars_tyeq1; eauto.
      }
      eapply TyEq1Trans.
      {
        eapply cong_tyeq1; eauto using pars_preserves_bkinding.
      }
      {
        eapply TyEq1Sym.
        eapply pars_tyeq1; eauto using pars_preserves_bkinding.
      }
      {
        eapply pars_preserves_bkinding; eauto.
      }
      {
        eapply pars_preserves_bkinding; eauto.
      }
    }
  Qed.

  Ltac elim_existsT_eq decider :=
    repeat match goal with
             H : _ |- _ => eapply Eqdep_dec.inj_pair2_eq_dec in H; [|intros; eapply decider]; subst
           end.

  Lemma lift2_inj :
    forall bs T A1 A2 (f : A1 -> A2 -> T) a1 a2 a1' a2',
      (forall a1 a2 a1' a2', f a1 a2 = f a1' a2' -> a1 = a1' /\ a2 = a2') ->
      lift2 bs f a1 a2 = lift2 bs f a1' a2' ->
      a1 = a1' /\
      a2 = a2'.
  Proof.
    induct bs; simpl; intros ? ? ? ? ? ? ? ? Hf Heq; eauto.
    eapply IHbs in Heq; eauto.
    intros b1 b2 b1' b2' Heq'.
    split.
    {
      eapply FunctionalExtensionality.functional_extensionality.
      intros x.
      eapply f_equal with (f := fun f => f x) in Heq'.
      eapply Hf in Heq'.
      propositional.
    }
    {
      eapply FunctionalExtensionality.functional_extensionality.
      intros x.
      eapply f_equal with (f := fun f => f x) in Heq'.
      eapply Hf in Heq'.
      propositional.
    }
  Qed.

  Arguments length {_} _ .
  
  Lemma Forall3_map_1_2_3_elim A1 A1' A2 A2' A3 A3' (f1 : A1 -> A1') (f2 : A2 -> A2') (f3 : A3 -> A3') p ls1 ls2 ls3 :
    Forall3 p (map f1 ls1) (map f2 ls2) (map f3 ls3) ->
    Forall3 (fun a1 a2 a3 => p (f1 a1) (f2 a2) (f3 a3)) ls1 ls2 ls3.
  Proof.
    induct ls1; destruct ls2; destruct ls3; simpl; intros H; invert H; eauto.
  Qed.

  Lemma Forall3_dedup_1_2_elim A1 A3 (p : A1 -> A1 -> A3 -> Prop) ls1 ls3 :
    Forall3 p ls1 ls1 ls3 ->
    Forall2 (fun a1 a3 => p a1 a1 a3) ls1 ls3.
  Proof.
    induct ls1; destruct ls3; simpl; intros H; invert H; eauto.
  Qed.

  Lemma eq_Forall2_eq A (ls1 ls2 : list A) :
    ls1 = ls2 ->
    Forall2 eq ls1 ls2.
  Proof.
    induct ls1; destruct ls2; simpl; intros H; invert H; eauto.
  Qed.

  Lemma Forall2_map_1_2_elim A1 A1' A2 A2' (f1 : A1 -> A1') (f2 : A2 -> A2') p ls1 ls2 :
    Forall2 p (map f1 ls1) (map f2 ls2) ->
    Forall2 (fun a1 a2 => p (f1 a1) (f2 a2)) ls1 ls2.
  Proof.
    induct ls1; destruct ls2; simpl; intros H; invert H; eauto.
  Qed.

  Lemma Forall2_Forall2_Forall2 A1 A2 (f1 : _ -> _ -> Prop) (f2 : _ -> _ -> Prop) (f3 : _ -> _ -> Prop) ls1 ls2 :
    (forall (a1 : A1) (a2 : A2), f1 a1 a2 -> f2 a1 a2 -> f3 a1 a2) ->
    Forall2 f1 ls1 ls2 ->
    Forall2 f2 ls1 ls2 ->
    Forall2 f3 ls1 ls2.
  Proof.
    induct ls1; destruct ls2; simpl; intros Hf H1 H2; invert H1; invert H2; eauto.
  Qed.

  Lemma invert_tyeq1_TApps_TRec_TQuan L args k1 t1 q k2 t2 K k :
    let t := TApps (TRec k1 t1) args in
    let t' := TQuan q k2 t2 in
    tyeq1 L K t t' k ->
    let bs := map get_bsort L in
    bkinding bs K t k ->
    bkinding bs K t' k ->
    wfsorts1 L ->
    False.
  Proof.
    simpl.
    intros H H1 H2 HL.
    eapply bkinding_TApps_invert in H1.
    destruct H1 as (H1 & Hargs).
    invert H1.
    invert H2.
    eapply tyeq1_par in H; eauto using bkinding_TApps.
    edestruct H as (r1 & r1' & Ht1r1 & Ht1'r1' & Hr1r1' & Hr1 & Hr1'); eauto.
    eapply pars_preserves_TApps_TRec in Ht1r1.
    openhyp; subst.
    eapply pars_preserves_TQuan in Ht1'r1'.
    openhyp; subst.
    set (k' := KArrows (map fst args) KType) in *.
    destruct (TApps_TRec_dec args k' x) as [ [ [? ?] [Heq ?] ] | [Heq ?]]; subst; simpl in * ; try rewrite Heq in *; invert Hr1r1'.
  Qed.

  Lemma invert_tyeq1_TApps_TRec_TBinOp L args k1 t1 opr t1' t2' K k :
    let t := TApps (TRec k1 t1) args in
    let t' := TBinOp opr t1' t2' in
    tyeq1 L K t t' k ->
    let bs := map get_bsort L in
    bkinding bs K t k ->
    bkinding bs K t' k ->
    wfsorts1 L ->
    False.
  Proof.
    simpl.
    intros H H1 H2 HL.
    eapply bkinding_TApps_invert in H1.
    destruct H1 as (H1 & Hargs).
    invert H1.
    invert H2.
    eapply tyeq1_par in H; eauto using bkinding_TApps.
    edestruct H as (r1 & r1' & Ht1r1 & Ht1'r1' & Hr1r1' & Hr1 & Hr1'); eauto.
    eapply pars_preserves_TApps_TRec in Ht1r1.
    openhyp; subst.
    eapply pars_preserves_TBinOp in Ht1'r1'.
    openhyp; subst.
    set (k' := KArrows (map fst args) KType) in *.
    destruct (TApps_TRec_dec args k' x) as [ [ [? ?] [Heq ?] ] | [Heq ?]]; subst; simpl in * ; try rewrite Heq in *; invert Hr1r1'.
  Qed.

  Lemma par_preserves_TConst cn t' :
    par (TConst cn) t' ->
    t' = TConst cn.
  Proof.
    induct 1; simpl; eauto.
  Qed.
  
  Lemma pars_preserves_TConst cn t' :
    par^* (TConst cn) t' ->
    t' = TConst cn.
  Proof.
    induct 1; simpl; eauto using par_preserves_TConst.
  Qed.

  Lemma invert_tyeq1_TApps_TRec_TConst L args k1 t1 cn K k :
    let t := TApps (TRec k1 t1) args in
    let t' := TConst cn in
    tyeq1 L K t t' k ->
    let bs := map get_bsort L in
    bkinding bs K t k ->
    bkinding bs K t' k ->
    wfsorts1 L ->
    False.
  Proof.
    simpl.
    intros H H1 H2 HL.
    eapply bkinding_TApps_invert in H1.
    destruct H1 as (H1 & Hargs).
    invert H1.
    invert H2.
    eapply tyeq1_par in H; eauto using bkinding_TApps.
    edestruct H as (r1 & r1' & Ht1r1 & Ht1'r1' & Hr1r1' & Hr1 & Hr1'); eauto.
    eapply pars_preserves_TApps_TRec in Ht1r1.
    openhyp; subst.
    eapply pars_preserves_TConst in Ht1'r1'.
    openhyp; subst.
    set (k' := KArrows (map fst args) KType) in *.
    destruct (TApps_TRec_dec args k' x) as [ [ [? ?] [Heq ?] ] | [Heq ?]]; subst; simpl in * ; try rewrite Heq in *; invert Hr1r1'.
  Qed.

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
  
  Inductive ForSome {A} (P : A -> A -> Prop) : option A -> option A -> Prop :=
  | FSNone : ForSome P None None
  | FSSome a a' :
      P a a' ->
      ForSome P (Some a) (Some a')
  .

  Hint Constructors ForSome.
  
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
  
  Lemma par_preserves_TArr t1 i t' :
    par (TArr t1 i) t' ->
    exists t1',
      t' = TArr t1' i /\
      par t1 t1'.
  Proof.
    induct 1; simpl; eauto.
  Qed.
  
  Lemma pars_preserves_TArr t1 i t' :
    par^* (TArr t1 i) t' ->
    exists t1',
      t' = TArr t1' i /\
      par^* t1 t1'.
  Proof.
    induct 1; simpl; eauto using par_preserves_TArr.
    eapply par_preserves_TArr in H; eauto.
    openhyp.
    subst.
    edestruct IHtrc; eauto.
    openhyp.
    subst.
    repeat eexists_split; eauto.
  Qed.

  Lemma invert_tyeq1_TArr L t1 i t1' i' K k :
    let t := TArr t1 i in
    let t' := TArr t1' i' in
    tyeq1 L K t t' k ->
    let bs := map get_bsort L in
    bkinding bs K t k ->
    bkinding bs K t' k ->
    wfsorts1 L ->
    tyeq1 L K t1 t1' k /\
    idxeq L i i' BSNat.
  Proof.
    simpl.
    intros H H1 H2 HL.
    invert H1.
    invert H2.
    eapply tyeq1_par in H; eauto.
    edestruct H as (r1 & r1' & Ht1r1 & Ht1'r1' & Hr1r1' & Hr1 & Hr1'); eauto.
    eapply pars_preserves_TArr in Ht1r1.
    openhyp; subst.
    eapply pars_preserves_TArr in Ht1'r1'.
    openhyp; subst.
    invert Hr1r1'.
    repeat try_split; eauto.
    {
      eapply TyEq1Trans.
      {
        eapply pars_tyeq1; eauto.
      }
      eapply TyEq1Trans.
      {
        eapply cong_tyeq1; eauto using pars_preserves_bkinding.
      }
      {
        eapply TyEq1Sym.
        eapply pars_tyeq1; eauto using pars_preserves_bkinding.
      }
      {
        eapply pars_preserves_bkinding; eauto.
      }
      {
        eapply pars_preserves_bkinding; eauto.
      }
    }
  Qed.

  Definition map_fst {A B C} (f : A -> C) (p : A * B) := (f (fst p), snd p).

  Arguments length {_} _ .
  Arguments map_fst {_ _ _} _ _ / .

(*    
    Lemma sorteq_tyeq1' L t1 t2 k :
      tyeq1 L t1 t2 k ->
      forall L',
        equal_sorts L L' ->
        tyeq1 L' t1 t2 k.
    Proof.
      induct 1; simpl; eauto using sorteq_refl, equal_sorts_sorteq, equal_sorts_interp_prop.
    Qed.

    Lemma sorteq_tyeq1 L k k' t t' :
      sorteq L k k' ->
      tyeq1 (k :: L) t t' ->
      tyeq1 (k' :: L) t t'.
    Proof.
      eauto using sorteq_tyeq1', equal_sorts_refl.
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

  Lemma map_eq_nth_error A1 A2 B (f1 : A1 -> B) (f2 : A2 -> B) :
    forall ls1 ls2 x a2,
      nth_error ls2 x = Some a2 ->
      map f1 ls1 = map f2 ls2 ->
      exists a1,
        nth_error ls1 x = Some a1 /\
        f1 a1 = f2 a2.
  Proof.
    induct ls1; destruct ls2; simpl; try solve [intros; try rewrite nth_error_nil in *; dis | eauto].
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
    destruct ls; simpl; dis.
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

  Notation tyeq1_refl := TyEq1Refl.
  Notation tyeq1_sym := TyEq1Sym.
  Notation tyeq1_trans := TyEq1Trans.
  
  Hint Resolve tyeq1_refl tyeq1_sym tyeq1_trans interp_prop_le_refl interp_prop_le_trans : db_tyeq1.

  Lemma shift0_i_t_shift n x b :
    shift0_i_t (shift_i_t n x b) = shift_i_t n (1 + x) (shift0_i_t b).
  Proof.
    unfold shift0_i_t; intros.
    symmetry.
    rewrite shift_i_t_shift_cut; repeat f_equal; la.
  Qed.

  Lemma shift0_i_t_subst x v b :
    shift0_i_t (subst_i_t x (shift_i_i x 0 v) b) = subst_i_t (1 + x) (shift_i_i (1 + x) 0 v) (shift0_i_t b).
  Proof.
    unfold shift0_i_t, subst0_i_i.
    rewrite shift_i_t_subst_in by la.
    rewrite shift_i_i_shift_merge by la.
    repeat (f_equal; try la).
  Qed.

  Lemma shift0_t_t_subst x v b :
    shift0_t_t (subst_t_t x (shift_t_t x 0 v) b) = subst_t_t (1 + x) (shift_t_t (1 + x) 0 v) (shift0_t_t b).
  Proof.
    unfold shift0_t_t, subst0_t_t.
    rewrite shift_t_t_subst_in by la.
    rewrite shift_t_t_shift_merge by la.
    repeat (f_equal; try la).
  Qed.

  Lemma subst0_i_t_shift0 v b :
    subst0_i_t v (shift0_i_t b) = b.
  Proof.
    unfold shift0_i_t, subst0_i_t.
    specialize (@subst_i_t_shift_avoid 1 b v 0 0); intros H; simplify.
    repeat rewrite shift_i_t_0 in *.
    eauto with db_la.
  Qed.
  
  Lemma subst0_t_t_shift0 v b :
    subst0_t_t v (shift0_t_t b) = b.
  Proof.
    unfold shift0_t_t, subst0_t_t.
    specialize (@subst_t_t_shift_avoid 1 b v 0 0); intros H; simplify.
    repeat rewrite shift_t_t_0 in *.
    eauto with db_la.
  Qed.
  
  Hint Constructors Forall2.
  
  Lemma lift3_to_imply bs A2 A3 (f : A2 -> A3 -> Prop) a1 a2 a3:
    lift3 bs (fun (a1 : Prop) a2 a3 => a1 -> f a2 a3) a1 a2 a3 = lift2 bs imply a1 (lift2 bs f a2 a3).
  Proof.
    rewrite fuse_lift2_lift2_2; eauto.
  Qed.

  Lemma kinding1_wellscoped_t L K t k :
    kinding1 L K t k ->
    wellscoped_t (length L) t.
  Proof.
    intros.
    eapply bkinding_wellscoped_t'; 
      eauto using kinding1_bkinding.
    rewrite map_length; eauto.
  Qed.

  Lemma kinding1_wellscoped_t' L K t k n :
    kinding1 L K t k ->
    n = length L ->
    wellscoped_t n t.
  Proof.
    intros; subst; eapply kinding1_wellscoped_t; eauto.
  Qed.

  Lemma wellscoped_shift_t_t L p :
    wellscoped_t L p ->
    forall x n,
      wellscoped_t L (shift_t_t n x p).
  Proof.
    induct 1; simpl; try solve [intros; subst; eauto with db_la].
  Qed.
  
  Hint Constructors Forall.
  
  Lemma Forall_map A B (f : A -> B) p ls : Forall p (map f ls) <-> Forall (fun x => p (f x)) ls.
  Proof.
    induct ls; simpl; split; intros H; invert H; intuition eauto.
  Qed.

  Lemma nth_error_Forall A P ls :
    Forall P ls ->
    forall n (a : A),
      nth_error ls n = Some a ->
      P a.
  Proof.
    induct 1; destruct n; simplify; repeat rewrite nth_error_nil in *; try dis; eauto.
    invert H1.
    eauto.
  Qed.

  Lemma wellscoped_subst_t_t :
    forall L b,
      wellscoped_t L b ->
      forall x v,
        wellscoped_t L v ->
        wellscoped_t L (subst_t_t x (shift_t_t x 0 v) b).
  Proof.
    induct 1;
      simpl; try rename x into y; intros x v Hv; subst; try solve [econstructor; eauto].
    {
      (* Case TVar *)
      cases (y <=>? x); eauto with db_la.
      eapply wellscoped_shift_t_t; eauto with db_la.
    }
    {
      (* Case TAbs *)
      econstructor; eauto with db_la.
      unfold shift0_i_t.
      rewrite shift_i_t_shift_t_t.
      eapply IHwellscoped_t; eauto with db_la.
      eapply wellscoped_shift_i_t; eauto.
    }
    {
      (* Case TQuan *)
      unfold shift0_t_t.
      rewrite shift_t_t_shift_merge by la.
      econstructor; eauto with db_la.
      rewrite plus_comm.
      eapply IHwellscoped_t; eauto with db_la.
    }
    {
      (* Case TQuanI *)
      econstructor; eauto with db_la.
      unfold shift0_i_t.
      rewrite shift_i_t_shift_t_t.
      eapply IHwellscoped_t; eauto with db_la.
      eapply wellscoped_shift_i_t; eauto.
    }
    {
      (* Case TRec *)
      unfold shift0_t_t.
      rewrite shift_t_t_shift_merge by la.
      econstructor; eauto with db_la.
      rewrite plus_comm.
      eapply IHwellscoped_t; eauto with db_la.
    }
    {
      (* Case TAbsT *)
      unfold shift0_t_t.
      rewrite shift_t_t_shift_merge by la.
      econstructor; eauto with db_la.
      rewrite plus_comm.
      eapply IHwellscoped_t; eauto with db_la.
    }
  Qed.
  
  Lemma wellscoped_subst_t_t_0 L b v :
    wellscoped_t L b ->
    wellscoped_t L v ->
    wellscoped_t L (subst_t_t 0 v b).
  Proof.
    intros Hb Hv.
    eapply wellscoped_subst_t_t with (x := 0) (v := v) (b := b) in Hb; eauto.
    rewrite shift_t_t_0 in *.
    eauto.
  Qed.

  Lemma wellscoped_subst_i_t :
    forall L b,
      wellscoped_t L b ->
      forall x v L',
        x < L ->
        wellscoped_i (L - (1 + x)) v ->
        L' = L - 1 ->
        wellscoped_t L' (subst_i_t x (shift_i_i x 0 v) b).
  Proof.
    induct 1;
      simpl; try rename x into y; intros x v ? Hx Hv ?; subst; try solve [econstructor; eauto using wellscoped_subst_i_i].
    {
      (* Case TAbs *)
      unfold shift0_i_i.
      rewrite shift_i_i_shift_merge by la.
      rewrite plus_comm.
      eauto with db_la.
    }
    {
      (* Case TQuanI *)
      unfold shift0_i_i.
      rewrite shift_i_i_shift_merge by la.
      rewrite plus_comm.
      econstructor; eauto with db_la.
      eapply wellscoped_subst_i_s; eauto with db_la.
    }
  Qed.
  
  Lemma wellscoped_subst_i_t_0 L b v L' :
    wellscoped_t L b ->
    0 < L ->
    L' = L - 1 ->
    wellscoped_i L' v ->
    wellscoped_t L' (subst_i_t 0 v b).
  Proof.
    intros Hb; intros; subst.
    eapply wellscoped_subst_i_t with (x := 0) (v := v) (b := b) in Hb; eauto.
    rewrite shift_i_i_0 in *.
    eauto.
  Qed.
  
  Lemma Forall_forall' {A P l} : Forall P l -> (forall x : A, In x l -> P x).
  Proof.
    intros; eapply Forall_forall; eauto.
  Qed.

  Lemma Forall_app A P (ls1 ls2 : list A) :
    Forall P ls1 ->
    Forall P ls2 ->
    Forall P (ls1 ++ ls2).
  Proof.
    intros H1 H2.
    eapply Forall_forall.
    specialize (Forall_forall' H1); intros H1'.
    specialize (Forall_forall' H2); intros H2'.
    intros x Hin.
    eapply in_app_or in Hin.
    intuition eauto.
  Qed.
  
  Lemma wellscoped_t_TApps L :
    forall cs t,
      wellscoped_t L t ->
      Forall (fun p => wellscoped_i L (snd p)) cs ->
      wellscoped_t L (TApps t cs).
  Proof.
    induct cs; simpl; intros t Ht Hcs; invert Hcs; eauto.
    destruct a as (b & i); simpl in *.
    eauto.
  Qed.

  Lemma wellscoped_shift_t_t_rev :
    forall L body,
      wellscoped_t L body ->
      forall n x body',
        body = shift_t_t n x body' ->
        wellscoped_t L body'.
  Proof.
    induct 1;
      simpl; try rename x into y; intros n x body' Hbody; intros; subst; cbn in *;
        try solve [
              destruct body'; simpl in *; try cases_le_dec; try dis;
              invert Hbody; eauto
            ].
  Qed.

  Lemma Forall_map_elim A B (f : A -> B) p ls : Forall p (map f ls) -> Forall (fun x => p (f x)) ls.
  Proof.
    intros; eapply Forall_map; eauto.
  Qed.

  Lemma wellscoped_shift_i_t_rev :
    forall L body,
      wellscoped_t L body ->
      forall n x body' L',
        body = shift_i_t n x body' ->
        x + n <= L ->
        L' = L - n ->
        wellscoped_t L' body'.
  Proof.
    induct 1;
      simpl; try rename x into x'; try rename n into m; intros n x body' L' Hbody Hcmp; intros; subst; cbn in *;
        try solve [
              destruct body'; simpl in *; try cases_le_dec; try dis;
              invert Hbody; eauto using wellscoped_shift_i_i_rev with db_la
            ].
    {
      (* Case TAbs *)
      destruct body'; simpl in *; try cases_le_dec; try dis.
      invert Hbody; eauto.
      econstructor; eauto.
      eapply IHwellscoped_t; eauto with db_la.
      destruct n; la.
    }
    {
      (* Case TQuanI *)
      destruct body'; simpl in *; try cases_le_dec; try dis.
      invert Hbody; eauto.
      econstructor; eauto using wellscoped_shift_i_s_rev.
      eapply IHwellscoped_t; eauto with db_la.
      destruct n; la.
    }
  Qed.

  Lemma wellscoped_t_TApps_invert L :
    forall args t,
      wellscoped_t L (TApps t args) ->
      wellscoped_t L t /\
      Forall (fun p => wellscoped_i L (snd p)) args.
  Proof.
    induct args; simpl; intros t H; eauto.
    destruct a as [b i].
    eapply IHargs in H.
    destruct H as [H1 H2].
    invert H1.
    eauto.
  Qed.

  Lemma kinding1_shift_t_t :
    forall L K c k,
      kinding1 L K c k ->
      forall x ls,
        let n := length ls in
        x <= length K ->
        kinding1 L (insert ls x K) (shift_t_t n x c) k.
  Proof.
    induct 1; unfold_all;
      simplify; cbn in *; try solve [econstructor; eauto].
    {
      (* Case TVar *)
      copy H HnltL.
      eapply nth_error_Some_lt in HnltL.
      rename x0 into y.
      cases (y <=? x).
      {
        econstructor.
        erewrite nth_error_insert'; eauto.
      }
      {
        econstructor.
        erewrite nth_error_before_insert'; eauto.
      }
    }
    {
      (* Case TQuan *)
      econstructor; eauto.
      eapply IHkinding1 with (x := S x); eauto with db_la.
    }
    {
      (* Case TRec *)
      econstructor; eauto.
      eapply IHkinding1 with (x := S x); eauto with db_la.
    }
    {
      (* Case TAbsT *)
      econstructor; eauto.
      eapply IHkinding1 with (x := S x); eauto with db_la.
    }
  Qed.

  Lemma kinding1_shift_t_t_1_0 L K c k k1 :
      kinding1 L K c k ->
      kinding1 L (k1 :: K) (shift_t_t 1 0 c) k.
  Proof.
    intros H; eapply kinding1_shift_t_t with (x := 0) (ls := [k1]) in H; eauto with db_la.
  Qed.

  Lemma kinding1_shift_i_t :
    forall L K c k,
      kinding1 L K c k ->
      forall x ls,
        let n := length ls in
        x <= length L ->
        wellscoped_ss L ->
        kinding1 (shift_i_ss n (firstn x L) ++ ls ++ my_skipn L x) K (shift_i_t n x c) k.
  Proof.
    simpl.
    induct 1;
      simpl; try rename x into y; intros x ls Hx HL; cbn in *; try solve [econstructor; eauto].
    {
      (* Case TArrow *)
      econstructor; eauto.
      eapply sorting1_shift_i_i with (s := STime); eauto.
      econstructor; eauto.
    }
    {
      (* Case TAbs *)
      econstructor; eauto.
      eapply IHkinding1 with (x := S x); eauto with db_la.
    }
    {
      (* Case TApp *)
      econstructor; eauto.
      eapply sorting1_shift_i_i with (s := SBaseSort _); eauto.
    }
    {
      (* Case TQuanI *)
      econstructor; eauto using wfsort1_shift_i_s''.
      specialize (IHkinding1 (S x) ls).
      simpl in *.
      rewrite length_firstn_le in * by la.
      eapply IHkinding1; eauto using wfsort1_wellscoped_s' with db_la.
    }
    {
      (* Case TNat *)
      econstructor; eauto.
      eapply sorting1_shift_i_i with (s := SNat); eauto.
      econstructor; eauto.
    }
    {
      (* Case TArr *)
      econstructor; eauto.
      eapply sorting1_shift_i_i with (s := SNat); eauto.
      econstructor; eauto.
    }
  Qed.

  Lemma kinding1_shift_i_t_1_0 L K c k s :
    kinding1 L K c k ->
    wellscoped_ss L ->
    kinding1 (s :: L) K (shift_i_t 1 0 c) k.
  Proof.
    intros Hbody HL.
    eapply kinding1_shift_i_t with (x := 0) (ls := [s]) in Hbody; eauto with db_la.
    simpl in *.
    rewrite my_skipn_0 in *.
    eauto.
  Qed.

  Lemma kinding1_shift_t_t' :
    forall L K c k x ls n,
      kinding1 L K c k ->
      n = length ls ->
      x <= length K ->
      kinding1 L (insert ls x K) (shift_t_t n x c) k.
  Proof.
    intros; subst; eapply kinding1_shift_t_t; eauto.
  Qed.

  Lemma kinding1_subst_t_t :
    forall L K body k_b,
      kinding1 L K body k_b ->
      forall x k_v v ,
        nth_error K x = Some k_v ->
        kinding1 L (my_skipn K (1 + x)) v k_v ->
        wellscoped_ss L ->
        kinding1 L (removen x K) (subst_t_t x (shift_t_t x 0 v) body) k_b.
  Proof.
    induct 1;
      simpl; try rename x into y; intros x k_v v Hx Hv HL; subst; try solve [econstructor; eauto].
    {
      (* Case TVar *)
      copy Hx Hcmp.
      eapply nth_error_Some_lt in Hcmp.
      cases (y <=>? x); eauto with db_la.
      {
        econstructor.
        erewrite removen_lt by eauto with db_la.
        eauto.
      }
      {
        rewrite removen_firstn_my_skipn.
        subst.
        assert (k_v = k) by equality.
        subst.
        eapply kinding1_shift_t_t' with (x := 0); eauto with db_la; try rewrite length_firstn_le by la; eauto.
      }
      {
        econstructor.
        erewrite removen_gt by eauto with db_la.
        eauto.
      }
    }
    {
      (* Case TAbs *)
      econstructor; eauto with db_la.
      unfold shift0_i_t.
      rewrite shift_i_t_shift_t_t.
      eapply IHkinding1; eauto with db_la.
      eapply kinding1_shift_i_t_1_0; eauto.
    }
    {
      (* Case TQuan *)
      unfold shift0_t_t.
      rewrite shift_t_t_shift_merge by la.
      econstructor; eauto with db_la.
      rewrite plus_comm.
      eapply IHkinding1 with (x := S x); eauto with db_la.
    }
    {
      (* Case TQuanI *)
      econstructor; eauto with db_la.
      unfold shift0_i_t.
      rewrite shift_i_t_shift_t_t.
      eapply IHkinding1; eauto using wfsort1_wellscoped_s' with db_la.
      eapply kinding1_shift_i_t_1_0; eauto.
    }
    {
      (* Case TRec *)
      unfold shift0_t_t.
      rewrite shift_t_t_shift_merge by la.
      econstructor; eauto with db_la.
      rewrite plus_comm.
      eapply IHkinding1 with (x := S x); eauto with db_la.
    }
    {
      (* Case TAbsT *)
      unfold shift0_t_t.
      rewrite shift_t_t_shift_merge by la.
      econstructor; eauto with db_la.
      rewrite plus_comm.
      eapply IHkinding1 with (x := S x); eauto with db_la.
    }
  Qed.
  
  Lemma kinding1_subst_t_t_0 L K body k_b k_v v :
    kinding1 L (k_v :: K) body k_b ->
    kinding1 L K v k_v ->
    wellscoped_ss L ->
    kinding1 L K (subst_t_t 0 v body) k_b.
  Proof.
    intros Hbody Hv HL.
    eapply kinding1_subst_t_t with (x := 0) (k_v := k_v) in Hbody; simpl; eauto; try rewrite my_skipn_0; eauto.
    simpl in *.
    rewrite shift_t_t_0 in *.
    eauto.
  Qed.

  Lemma kinding1_subst_i_t :
    forall L K body k,
      kinding1 L K body k ->
      forall x s v ,
        nth_error L x = Some s ->
        sorting1 (my_skipn L (1 + x)) v s ->
        wfsorts1 L ->
        kinding1 (subst_i_ss v (firstn x L) ++ my_skipn L (1 + x)) K (subst_i_t x (shift_i_i x 0 v) body) k.
  Proof.
    induct 1;
      simpl; try rename x into y; try rename s into s'; intros x s v Hx Hv HL; subst; try solve [econstructor; eauto using sorting1_subst_i_i].
    {
      (* TArrow *)
      econstructor; simpl; eauto using sorting1_subst_i_i.
      eapply sorting1_subst_i_i with (s_b := SBaseSort _); eauto.
    }
    {
      (* Case TAbs *)
      unfold shift0_i_i.
      rewrite shift_i_i_shift_merge by la.
      rewrite plus_comm.
      econstructor; eauto.
      eapply IHkinding1 with (x := S x); eauto.
    }
    {
      (* Case TApp *)
      econstructor; eauto.
      eapply sorting1_subst_i_i with (s_b := SBaseSort _); eauto.
    }
    {
      (* Case TQuanI *)
      unfold shift0_i_i.
      rewrite shift_i_i_shift_merge by la.
      rewrite plus_comm.
      econstructor; eauto using wfsort1_subst_i_s' with db_la.
      specialize (IHkinding1 (S x) s v).
      simpl in *.
      copy Hx Hcmp.
      eapply nth_error_Some_lt in Hcmp.
      rewrite length_firstn_le in * by la.
      eauto.
    }
    {
      (* TNat *)
      econstructor; simpl; eauto using sorting1_subst_i_i.
      eapply sorting1_subst_i_i with (s_b := SBaseSort _); eauto.
    }
    {
      (* TArr *)
      econstructor; simpl; eauto using sorting1_subst_i_i.
      eapply sorting1_subst_i_i with (s_b := SBaseSort _); eauto.
    }
  Qed.

  Lemma kinding1_subst_i_t_0 L K body k s v :
    kinding1 (s :: L) K body k ->
    sorting1 L v s ->
    wfsorts1 (s :: L) ->
    kinding1 L K (subst_i_t 0 v body) k.
  Proof.
    intros Hbody; intros.
    eapply kinding1_subst_i_t with (x := 0) in Hbody; simpl; eauto; simpl in *; try rewrite my_skipn_0 in *; eauto.
    rewrite shift_i_i_0 in *.
    eauto.
  Qed.

  Lemma kinding1_TApps L K :
    forall cs t k,
      kinding1 L K t (KArrows (map fst cs) k)->
      Forall (fun p => sorting1 L (snd p) (SBaseSort (fst p))) cs ->
      kinding1 L K (TApps t cs) k.
  Proof.
    induct cs; simpl; intros t k Ht Hcs; invert Hcs; eauto.
    destruct a as (b & i); simpl in *.
    eauto.
  Qed.

  Lemma kinding1_TApps_invert L K :
    forall args t k,
      kinding1 L K (TApps t args) k ->
      kinding1 L K t (KArrows (map fst args) k) /\
      Forall (fun p => sorting1 L (snd p) (SBaseSort (fst p))) args.
  Proof.
    induct args; simpl; intros t k H; eauto.
    destruct a as [b i].
    eapply IHargs in H.
    destruct H as [H1 H2].
    invert H1.
    eauto.
  Qed.

  Lemma kinding1_shift_t_t_rev :
    forall L K t k,
      kinding1 L K t k ->
      forall n x t' K1 K2 K3,
        t = shift_t_t n x t' ->
        K = K1 ++ K2 ++ K3 ->
        x = length K1 ->
        n = length K2 ->
        kinding1 L (K1 ++ K3) t' k.
  Proof.
    induct 1;
      simpl; intros ? ? t' K1 K2 K3 Ht; intros; subst; cbn in *;
        try solve [
              destruct t'; simpl in *; try cases_le_dec; try dis;
              invert Ht; eauto
            ].
    {
      (* Case TVar *)
      destruct t'; simpl in *; try dis.
      rename x0 into y.
      econstructor.
      cases (length K1 <=? y).
      {
        invert Ht.
        repeat rewrite nth_error_app2 in * by la.
        rewrite <- H.
        f_equal.
        la.
      }
      {
        invert Ht.
        repeat rewrite nth_error_app1 in * by la.
        eauto.
      }
    }
    {
      (* Case TQuan *)
      destruct t'; simpl in *; try cases_le_dec; try dis.
      invert Ht; eauto.
      econstructor; eauto.
      eapply IHkinding1 with (K4 := _ :: _); eauto with db_la.
      eauto.
    }
    {
      (* Case TRec *)
      destruct t'; simpl in *; try cases_le_dec; try dis.
      invert Ht; eauto.
      econstructor; eauto.
      eapply IHkinding1 with (K4 := _ :: _); eauto with db_la.
      eauto.
    }
    {
      (* Case TAbsT *)
      destruct t'; simpl in *; try cases_le_dec; try dis.
      invert Ht; eauto.
      econstructor; eauto.
      eapply IHkinding1 with (K4 := _ :: _); eauto with db_la.
      eauto.
    }
  Qed.

  Lemma kinding1_shift_t_t_rev_1_0 L k1 K t k :
    kinding1 L (k1 :: K) (shift_t_t 1 0 t) k ->
    kinding1 L K t k.
  Proof.
    intros Hp.
    eapply kinding1_shift_t_t_rev with (K1 := []) (K2 := [k1]) in Hp; simpl; eauto.
  Qed.
  
  Lemma kinding1_shift_i_t_rev :
    forall L K i k,
      kinding1 L K i k ->
      forall x L' ls i',
        let n := length ls in
        L = shift_i_ss n (firstn x L') ++ ls ++ my_skipn L' x ->
        i = shift_i_t n x i' ->
        x <= length L' ->
        wfsorts1 L' ->
        kinding1 L' K i' k.
  Proof.
    simpl.
    induct 1;
      simpl; try rename x into x'; try rename n into m; intros x L' ls i' HL Hi Hx HL'; intros; subst; cbn in *;
        try solve [
              destruct i'; simpl in *; try cases_le_dec; try dis;
              invert Hi; eauto |
              destruct i'; simpl in *; try cases_le_dec; try dis;
              invert Hi;
              econstructor; eauto using sorting1_shift_i_i_rev_SBaseSort;
              eapply IHkinding1; eauto with db_la; simpl; eauto with db_la |
              destruct i'; simpl in *; try cases_le_dec; try dis;
              invert Hi;
              econstructor; eauto using sorting1_shift_i_i_rev_SBaseSort;
              eapply sorting1_shift_i_i_rev_SBaseSort; eauto
            ].
    destruct i'; simpl in *; try cases_le_dec; try dis;
      invert Hi;
      econstructor; eauto using sorting1_shift_i_i_rev_SBaseSort, wfsort1_shift_i_s_rev.
    {
      rewrite get_bsort_shift_i_ss_insert in *.
      eapply wfsort1_shift_i_s_rev'; eauto with db_la.
    }
    eapply IHkinding1 with (x0 := S x); eauto; simpl; try rewrite length_firstn_le by la; eauto with db_la.
    econstructor; eauto.
    rewrite get_bsort_shift_i_ss_insert in *.
    eapply wfsort1_shift_i_s_rev'; eauto with db_la.
  Qed.
  
  Lemma kinding1_shift_i_t_rev_1_0 s L K t k :
    kinding1 (s :: L) K (shift_i_t 1 0 t) k ->
    wfsorts1 L ->
    kinding1 L K t k.
  Proof.
    intros H HL.
    eapply kinding1_shift_i_t_rev with (x := 0) (ls := [s]) in H; eauto with db_la.
    simpl in *.
    rewrite my_skipn_0.
    eauto.
  Qed.
  
  (* for setoid_rewrite *)
  Lemma shift_i_t_shift_cut_2 :
    forall n2 y n1 x,
      x + n1 <= y ->
      forall b,
        shift_i_t n2 y (shift_i_t n1 x b) = shift_i_t n1 x (shift_i_t n2 (y - n1) b).
  Proof.
    intros; eapply shift_i_t_shift_cut; eauto.
  Qed.
  
  Lemma shift_i_t_TApps n x args t :
    shift_i_t n x (TApps t args) = TApps (shift_i_t n x t) (map (map_snd (shift_i_i n x)) args).
  Proof.
    induct args; simpl; eauto.
    destruct a as [b i]; simpl.
    rewrite IHargs.
    eauto.
  Qed.
  
  Lemma shift_t_t_shift_cut_setoid n1 n2 x y :
    x + n1 <= y ->
    forall b,
      shift_t_t n2 y (shift_t_t n1 x b) = shift_t_t n1 x (shift_t_t n2 (y - n1) b).
  Proof.
    intros; eapply shift_t_t_shift_cut; eauto.
  Qed.
  
  Lemma shift_t_t_TApps n x args t :
    shift_t_t n x (TApps t args) = TApps (shift_t_t n x t) args.
  Proof.
    induct args; simpl; eauto.
    destruct a as [b i]; simpl.
    rewrite IHargs.
    eauto.
  Qed.
  
  Lemma subst_i_t_shift_hit_setoid v n x y :
    x + n <= y ->
    forall b,
      subst_i_t y (shift_i_i y 0 v) (shift_i_t n x b) = shift_i_t n x (subst_i_t (y - n) (shift_i_i (y - n) 0 v) b).
  Proof.
    intros; eapply subst_i_t_shift_hit; eauto.
  Qed.
  
  Lemma subst_i_t_TApps x v args t :
    subst_i_t x v (TApps t args) = TApps (subst_i_t x v t) (map (map_snd (subst_i_i x v)) args).
  Proof.
    induct args; simpl; eauto.
    destruct a as [b i]; simpl.
    rewrite IHargs.
    eauto.
  Qed.
  
  Lemma forall_subst_i_p_intro_imply_2 bs x b_v v p1 p2 :
    imply_ bs (interp_p bs p1) p2 ->
    nth_error bs x = Some b_v ->
    bsorting (my_skipn bs (S x)) v b_v ->
    wfprop1 bs p1 ->
    let bs' := removen x bs in
    imply_ bs' (interp_p bs' (subst_i_p x (shift_i_i x 0 v) p1)) (subst x _ (interp_idx v _ b_v) p2).
  Proof.
    simpl.
    intros H Hx Hv Hp1.
    eapply forall_trans.
    {
      eapply forall_iff_imply.
      eapply forall_subst_i_p_iff_subst; eauto.
      rewrite skipn_my_skipn; eauto.
    }
    simpl.
    rewrite <- subst_lift2.
    eapply forall_subst; eauto.
  Qed.

  Lemma subst_t_t_shift_hit_setoid n x y v :
    x + n <= y ->
    forall b,
      subst_t_t y (shift_t_t y 0 v) (shift_t_t n x b) = shift_t_t n x (subst_t_t (y - n) (shift_t_t (y - n) 0 v) b).
  Proof.
    intros; eapply subst_t_t_shift_hit; eauto.
  Qed.
  
  Lemma subst_t_t_TApps x v args t :
    subst_t_t x v (TApps t args) = TApps (subst_t_t x v t) args.
  Proof.
    induct args; simpl; eauto.
    destruct a as [b i]; simpl.
    rewrite IHargs.
    eauto.
  Qed.
  
  Lemma forall_lift3_lift3_lift5_1_4_2_5 :
    forall bs A1 A2 A3 A4 A5 P1 P2 P3 P4 P5 (f1 : _ -> _ -> _ -> Prop) (f2 : _ -> _ -> _ -> Prop) (f3 : _ -> _ -> _ -> _ -> _ -> Prop),
      (forall (a1 : A1) (a2 : A2) (a3 : A3) (a4 : A4) (a5 : A5), f1 a1 a3 a4 -> f2 a2 a3 a5 -> f3 a1 a2 a3 a4 a5) ->
      forall_ bs (lift3 bs f1 P1 P3 P4) ->
      forall_ bs (lift3 bs f2 P2 P3 P5) ->
      forall_ bs (lift5 bs f3 P1 P2 P3 P4 P5).
  Proof.
    induct bs; simplify; eauto.
    rewrite fuse_lift1_lift3 in *.
    rewrite fuse_lift1_lift5 in *.
    eapply IHbs; eauto.
    simplify.
    eauto.
  Qed.
  
  Lemma forall_lift3_lift3_lift6_1_4_5_3_4_6 :
    forall bs A1 A2 A3 A4 A5 A6 P1 P2 P3 P4 P5 P6 (f1 : _ -> _ -> _ -> Prop) (f2 : _ -> _ -> _ -> Prop) (f3 : _ -> _ -> _ -> _ -> _ -> _ -> Prop),
      (forall (a1 : A1) (a2 : A2) (a3 : A3) (a4 : A4) (a5 : A5) (a6 : A6), f1 a1 a4 a5 -> f2 a3 a4 a6 -> f3 a1 a2 a3 a4 a5 a6) ->
      forall_ bs (lift3 bs f1 P1 P4 P5) ->
      forall_ bs (lift3 bs f2 P3 P4 P6) ->
      forall_ bs (lift6 bs f3 P1 P2 P3 P4 P5 P6).
  Proof.
    induct bs; simplify; eauto.
    rewrite fuse_lift1_lift3 in *.
    rewrite fuse_lift1_lift6 in *.
    eapply IHbs; eauto.
    simplify.
    eauto.
  Qed.
  
  Lemma forall_lift3_lift2_lift3_2_4 :
    forall bs A1 A2 A3 A4 P1 P2 P3 P4 (f1 : A1 -> A2 -> A3 -> Prop) (f2 : A2 -> A4 -> Prop) (f3 : A1 -> A4 -> A3 -> Prop),
      (forall a1 a2 a3 a4, f1 a1 a2 a3 -> f2 a2 a4 -> f3 a1 a4 a3) ->
      forall_ bs (lift3 bs f1 P1 P2 P3) ->
      forall_ bs (lift2 bs f2 P2 P4) ->
      forall_ bs (lift3 bs f3 P1 P4 P3).
  Proof.
    induct bs; simplify; eauto.
    rewrite fuse_lift1_lift3 in *.
    rewrite fuse_lift1_lift2 in *.
    eapply IHbs; eauto.
    simplify.
    eauto.
  Qed.
  
  Lemma forall_lift3_lift4_1_3_4 :
    forall bs A1 A2 A3 A4 P1 P2 P3 P4 (f1 : A1 -> A3 -> A4 -> Prop) (f2 : A1 -> A2 -> A3 -> A4 -> Prop),
      (forall a1 a2 a3 a4, f1 a1 a3 a4 -> f2 a1 a2 a3 a4) ->
      forall_ bs (lift3 bs f1 P1 P3 P4) ->
      forall_ bs (lift4 bs f2 P1 P2 P3 P4).
  Proof.
    induct bs; simplify; eauto.
    rewrite fuse_lift1_lift3 in *.
    rewrite fuse_lift1_lift4 in *.
    eapply IHbs; eauto.
    simplify.
    eauto.
  Qed.
  
  Lemma forall_lift2_lift3_lift4_5_3_2_5_4 :
    forall bs A1 A2 A3 A4 A5 P1 P2 P3 P4 P5 (f1 : A5 -> A3 -> Prop) (f2 : A2 -> A5 -> A4 -> Prop) (f3 : A1 -> A2 -> A3 -> A4 -> Prop),
      (forall a1 a2 a3 a4 a5, f1 a5 a3 -> f2 a2 a5 a4 -> f3 a1 a2 a3 a4) ->
      forall_ bs (lift2 bs f1 P5 P3) ->
      forall_ bs (lift3 bs f2 P2 P5 P4) ->
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
  
  Lemma forall_lift3_lift3_lift4_3_5_1_4_5_2 :
    forall bs A1 A2 A3 A4 A5 P1 P2 P3 P4 P5 (f1 : A3 -> A5 -> A1 -> Prop) (f2 : A4 -> A5 -> A2 -> Prop) (f3 : A1 -> A2 -> A3 -> A4 -> Prop),
      (forall a1 a2 a3 a4 a5, f1 a3 a5 a1 -> f2 a4 a5 a2 -> f3 a1 a2 a3 a4) ->
      forall_ bs (lift3 bs f1 P3 P5 P1) ->
      forall_ bs (lift3 bs f2 P4 P5 P2) ->
      forall_ bs (lift4 bs f3 P1 P2 P3 P4).
  Proof.
    induct bs; simplify; eauto.
    rewrite fuse_lift1_lift3 in *.
    rewrite fuse_lift1_lift4 in *.
    eapply IHbs; eauto.
    simplify.
    eauto.
  Qed.
  
  Lemma par_preserves_TQuanI q k t1 t' :
    par (TQuanI q k t1) t' ->
    exists t1',
      t' = TQuanI q k t1' /\
      par t1 t1'.
  Proof.
    induct 1; simpl; eauto.
  Qed.
  
  Lemma pars_preserves_TQuanI q k t1 t' :
    par^* (TQuanI q k t1) t' ->
    exists t1',
      t' = TQuanI q k t1' /\
      par^* t1 t1'.
  Proof.
    induct 1; simpl; eauto using par_preserves_TQuanI.
    eapply par_preserves_TQuanI in H; eauto.
    openhyp.
    subst.
    edestruct IHtrc; eauto.
    openhyp.
    subst.
    repeat eexists_split; eauto.
  Qed.

  Lemma invert_tyeq1_TQuanI_TArrow L q s t1 t1' i t2' K k :
    let t := TQuanI q s t1 in
    let t' := TArrow t1' i t2' in
    tyeq1 L K t t' k ->
    let bs := map get_bsort L in
    bkinding bs K t k ->
    bkinding bs K t' k ->
    wfsorts1 L ->
    False.
  Proof.
    simpl.
    intros H H1 H2 HL.
    invert H1.
    invert H2.
    eapply tyeq1_par in H; eauto.
    edestruct H as (r1 & r1' & Ht1r1 & Ht1'r1' & Hr1r1' & Hr1 & Hr1'); eauto.
    eapply pars_preserves_TQuanI in Ht1r1.
    openhyp.
    subst.
    eapply pars_preserves_TArrow in Ht1'r1'.
    openhyp.
    subst.
    invert Hr1r1'.
  Qed.

  Lemma invert_tyeq1_TQuanI_TQuan L q s t1 q' k1 t1' K k :
    let t := TQuanI q s t1 in
    let t' := TQuan q' k1 t1' in
    tyeq1 L K t t' k ->
    let bs := map get_bsort L in
    bkinding bs K t k ->
    bkinding bs K t' k ->
    wfsorts1 L ->
    False.
  Proof.
    simpl.
    intros H H1 H2 HL.
    invert H1.
    invert H2.
    eapply tyeq1_par in H; eauto.
    edestruct H as (r1 & r1' & Ht1r1 & Ht1'r1' & Hr1r1' & Hr1 & Hr1'); eauto.
    eapply pars_preserves_TQuanI in Ht1r1.
    openhyp.
    subst.
    eapply pars_preserves_TQuan in Ht1'r1'.
    openhyp.
    subst.
    invert Hr1r1'.
  Qed.

  (* Arguments TExists _ _ / . *)
  (* Arguments TForall _ _ / . *)
  
  Lemma invert_tyeq1_TExists_TForall L k1 t1 k1' t1' K k :
    let t := TExists k1 t1 in
    let t' := TForall k1' t1' in
    tyeq1 L K t t' k ->
    let bs := map get_bsort L in
    bkinding bs K t k ->
    bkinding bs K t' k ->
    wfsorts1 L ->
    False.
  Proof.
    unfold TExists, TForall.
    simpl.
    intros H H1 H2 HL.
    invert H1.
    invert H2.
    eapply tyeq1_par in H; simpl; eauto.
    edestruct H as (r1 & r1' & Ht1r1 & Ht1'r1' & Hr1r1' & Hr1 & Hr1'); eauto.
    eapply pars_preserves_TQuan in Ht1r1.
    openhyp.
    subst.
    eapply pars_preserves_TQuan in Ht1'r1'.
    openhyp.
    subst.
    invert Hr1r1'.
  Qed.

  Lemma invert_tyeq1_TBinOp_TQuan L opr ta tb q k1 t1 K k :
    let t := TBinOp opr ta tb in
    let t' := TQuan q k1 t1 in
    tyeq1 L K t t' k ->
    let bs := map get_bsort L in
    bkinding bs K t k ->
    bkinding bs K t' k ->
    wfsorts1 L ->
    False.
  Proof.
    simpl.
    intros H H1 H2 HL.
    invert H1.
    invert H2.
    eapply tyeq1_par in H; simpl; eauto.
    edestruct H as (r1 & r1' & Ht1r1 & Ht1'r1' & Hr1r1' & Hr1 & Hr1'); eauto.
    eapply pars_preserves_TBinOp in Ht1r1.
    openhyp; subst.
    eapply pars_preserves_TQuan in Ht1'r1'.
    openhyp; subst.
    invert Hr1r1'.
  Qed.

  Lemma invert_tyeq1_TApps_TRec_TQuanI L args k1 t1 q s t1' K k :
    let t := TApps (TRec k1 t1) args in
    let t' := TQuanI q s t1' in
    tyeq1 L K t t' k ->
    let bs := map get_bsort L in
    bkinding bs K t k ->
    bkinding bs K t' k ->
    wfsorts1 L ->
    False.
  Proof.
    simpl.
    intros H H1 H2 HL.
    eapply bkinding_TApps_invert in H1.
    destruct H1 as (H1 & Hargs).
    invert H1.
    invert H2.
    eapply tyeq1_par in H; eauto using bkinding_TApps.
    edestruct H as (r1 & r1' & Ht1r1 & Ht1'r1' & Hr1r1' & Hr1 & Hr1'); eauto.
    eapply pars_preserves_TApps_TRec in Ht1r1.
    openhyp; subst.
    eapply pars_preserves_TQuanI in Ht1'r1'.
    openhyp; subst.
    set (k' := KArrows (map fst args) KType) in *.
    destruct (TApps_TRec_dec args k' x) as [ [ [? ?] [Heq ?] ] | [Heq ?]]; subst; simpl in * ; try rewrite Heq in *; invert Hr1r1'.
  Qed.

  Lemma invert_tyeq1_TBinOp_TQuanI L opr ta tb q s t1 K k :
    let t := TBinOp opr ta tb in
    let t' := TQuanI q s t1 in
    tyeq1 L K t t' k ->
    let bs := map get_bsort L in
    bkinding bs K t k ->
    bkinding bs K t' k ->
    wfsorts1 L ->
    False.
  Proof.
    simpl.
    intros H H1 H2 HL.
    invert H1.
    invert H2.
    eapply tyeq1_par in H; simpl; eauto.
    edestruct H as (r1 & r1' & Ht1r1 & Ht1'r1' & Hr1r1' & Hr1 & Hr1'); eauto.
    eapply pars_preserves_TBinOp in Ht1r1.
    openhyp; subst.
    eapply pars_preserves_TQuanI in Ht1'r1'.
    openhyp; subst.
    invert Hr1r1'.
  Qed.

  Lemma invert_tyeq1_TBinOp_TConst L opr ta tb cn K k :
    let t := TBinOp opr ta tb in
    let t' := TConst cn in
    tyeq1 L K t t' k ->
    let bs := map get_bsort L in
    bkinding bs K t k ->
    bkinding bs K t' k ->
    wfsorts1 L ->
    False.
  Proof.
    simpl.
    intros H H1 H2 HL.
    invert H1.
    invert H2.
    eapply tyeq1_par in H; simpl; eauto.
    edestruct H as (r1 & r1' & Ht1r1 & Ht1'r1' & Hr1r1' & Hr1 & Hr1'); eauto.
    eapply pars_preserves_TBinOp in Ht1r1.
    openhyp; subst.
    eapply pars_preserves_TConst in Ht1'r1'.
    openhyp; subst.
    invert Hr1r1'.
  Qed.

  Lemma invert_tyeq1_TProd_TSum L t1 t2 t1' t2' K k :
    let t := TProd t1 t2 in
    let t' := TSum t1' t2' in
    tyeq1 L K t t' k ->
    let bs := map get_bsort L in
    bkinding bs K t k ->
    bkinding bs K t' k ->
    wfsorts1 L ->
    False.
  Proof.
    unfold TProd, TSum.
    simpl.
    intros H H1 H2 HL.
    invert H1.
    invert H2.
    eapply tyeq1_par in H; simpl; eauto.
    edestruct H as (r1 & r1' & Ht1r1 & Ht1'r1' & Hr1r1' & Hr1 & Hr1'); eauto.
    eapply pars_preserves_TBinOp in Ht1r1.
    openhyp; subst.
    eapply pars_preserves_TBinOp in Ht1'r1'.
    openhyp; subst.
    invert Hr1r1'.
  Qed.

  Lemma invert_tyeq1_TConst_TQuanI L cn q s t1 K k :
    let t := TConst cn in
    let t' := TQuanI q s t1 in
    tyeq1 L K t t' k ->
    let bs := map get_bsort L in
    bkinding bs K t k ->
    bkinding bs K t' k ->
    wfsorts1 L ->
    False.
  Proof.
    simpl.
    intros H H1 H2 HL.
    invert H1.
    invert H2.
    eapply tyeq1_par in H; simpl; eauto.
    edestruct H as (r1 & r1' & Ht1r1 & Ht1'r1' & Hr1r1' & Hr1 & Hr1'); eauto.
    eapply pars_preserves_TConst in Ht1r1.
    openhyp; subst.
    eapply pars_preserves_TQuanI in Ht1'r1'.
    openhyp; subst.
    invert Hr1r1'.
  Qed.

  Definition TForallI := TQuanI QuanForall.
  Definition TExistsI := TQuanI QuanExists.

  Lemma invert_tyeq1_TExistsI_TForallI L s t1 s' t1' K k :
    let t := TExistsI s t1 in
    let t' := TForallI s' t1' in
    tyeq1 L K t t' k ->
    let bs := map get_bsort L in
    bkinding bs K t k ->
    bkinding bs K t' k ->
    wfsorts1 L ->
    False.
  Proof.
    unfold TExistsI, TForallI.
    simpl.
    intros H H1 H2 HL.
    invert H1.
    invert H2.
    eapply tyeq1_par in H; simpl; eauto.
    edestruct H as (r1 & r1' & Ht1r1 & Ht1'r1' & Hr1r1' & Hr1 & Hr1'); eauto.
    eapply pars_preserves_TQuanI in Ht1r1.
    openhyp; subst.
    eapply pars_preserves_TQuanI in Ht1'r1'.
    openhyp; subst.
    invert Hr1r1'.
  Qed.

  Lemma kinding1_TApps_TRec_invert L K args k t k' :
    kinding1 L K (TApps (TRec k t) args) k' ->
    k = KArrows (map fst args) k' /\
    kinding1 L (k :: K) t k /\
    Forall (fun p => sorting1 L (snd p) (SBaseSort (fst p))) args.
  Proof.
    intros H.
    eapply kinding1_TApps_invert in H.
    destruct H as [H1 H2].
    invert H1.
    eauto.
  Qed.

  Lemma tyeq1_TApps L cs cs' :
    Forall2 (fun p p' => fst p = fst p' /\ idxeq L (snd p) (snd p') (fst p)) cs cs' ->
    forall K t t' k',
      let k'' := KArrows (map fst cs) k' in
      tyeq1 L K t t' k'' ->
      tyeq1 L K (TApps t cs) (TApps t' cs') k'.
  Proof.
    simpl.
    induct 1; simpl; intros K t t' k' Htt'; eauto.
    destruct x as [b i]; simpl in *.
    destruct y as [b' i']; simpl in *.
    openhyp; subst.
    eapply IHForall2.
    eapply TyEq1App; eauto.
  Qed.
  
  Lemma forall_lift3_lift3_lift7_6_2_4_7_3_5 :
    forall bs A1 A2 A3 A4 A5 A6 A7 P1 P2 P3 P4 P5 P6 P7 (f1 : A6 -> A2 -> A4 -> Prop) (f2 : A7 -> A3 -> A5 -> Prop) (f3 : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> Prop),
      (forall a1 a2 a3 a4 a5 a6 a7, f1 a6 a2 a4 -> f2 a7 a3 a5 -> f3 a1 a2 a3 a4 a5 a6 a7) ->
      forall_ bs (lift3 bs f1 P6 P2 P4) ->
      forall_ bs (lift3 bs f2 P7 P3 P5) ->
      forall_ bs (lift7 bs f3 P1 P2 P3 P4 P5 P6 P7).
  Proof.
    induct bs; simplify; eauto.
    rewrite fuse_lift1_lift3 in *.
    rewrite fuse_lift1_lift7 in *.
    eapply IHbs; eauto.
    simplify.
    eauto.
  Qed.
  
  Ltac elim_existsT_eq_2 :=
    repeat match goal with
             H : _ |- _ => eapply Eqdep_dec.inj_pair2_eq_dec in H; [|intros; solve [eapply bsort_dec ] ]; subst
           end.

  Lemma invert_tyeq1_TQuanI L q1 s1 t1 q2 s2 t2 K k :
    let t := TQuanI q1 s1 t1 in
    let t' := TQuanI q2 s2 t2 in 
    tyeq1 L K t t' k ->
    let bs := map get_bsort L in
    bkinding bs K t k ->
    bkinding bs K t' k ->
    wfsorts1 L ->
    q1 = q2 /\
    sorteq L s1 s2 /\
    tyeq1 (s1 :: L) K t1 t2 k.
  Proof.
    simpl.
    intros H H1 H2 HL.
    invert H1.
    invert H2.
    eapply tyeq1_par in H; eauto.
    edestruct H as (r1 & r1' & Ht1r1 & Ht1'r1' & Hr1r1' & Hr1 & Hr1'); eauto.
    eapply pars_preserves_TQuanI in Ht1r1.
    openhyp; subst.
    eapply pars_preserves_TQuanI in Ht1'r1'.
    openhyp; subst.
    invert Hr1r1'.
    repeat try_split; eauto.
    {
      eapply TyEq1Trans.
      {
        eapply pars_tyeq1; eauto.
      }
      eapply TyEq1Trans.
      {
        eapply cong_tyeq1; eauto using pars_preserves_bkinding.
      }
      {
        eapply TyEq1Sym.
        eapply pars_tyeq1; [eauto using pars_preserves_bkinding|].
        invert H13; simpl in *; eauto.
      }
      {
        eapply pars_preserves_bkinding; eauto.
        invert H13; simpl in *; eauto.
      }
      {
        eapply pars_preserves_bkinding; eauto.
      }
    }
  Qed.

  Lemma kinding1_bkinding' L K t k bs :
    kinding1 L K t k ->
    bs = map get_bsort L ->
    bkinding bs K t k.
  Proof.
    intros; subst; eapply kinding1_bkinding; eauto.
  Qed.

  Lemma par_preserves_TNat i t' :
    par (TNat i) t' ->
    t' = TNat i.
  Proof.
    induct 1; simpl; eauto.
  Qed.
  
  Lemma pars_preserves_TNat i t' :
    par^* (TNat i) t' ->
    t' = TNat i.
  Proof.
    induct 1; simpl; eauto using par_preserves_TNat.
  Qed.

  Lemma invert_tyeq1_TNat L i i' K k :
    let t := TNat i in
    let t' := TNat i' in
    tyeq1 L K t t' k ->
    let bs := map get_bsort L in
    bkinding bs K t k ->
    bkinding bs K t' k ->
    wfsorts1 L ->
    idxeq L i i' BSNat.
  Proof.
    simpl.
    intros H H1 H2 HL.
    invert H1.
    invert H2.
    eapply tyeq1_par in H; eauto.
    edestruct H as (r1 & r1' & Ht1r1 & Ht1'r1' & Hr1r1' & Hr1 & Hr1'); eauto.
    eapply pars_preserves_TNat in Ht1r1.
    openhyp; subst.
    eapply pars_preserves_TNat in Ht1'r1'.
    openhyp; subst.
    invert Hr1r1'.
    repeat try_split; eauto.
  Qed.

  Lemma invert_tyeq1_TApps_TRec_TNat L args k1 t1 i K k :
    let t := TApps (TRec k1 t1) args in
    let t' := TNat i in 
    tyeq1 L K t t' k ->
    let bs := map get_bsort L in
    bkinding bs K t k ->
    bkinding bs K t' k ->
    wfsorts1 L ->
    False.
  Proof.
    simpl.
    intros H H1 H2 HL.
    eapply bkinding_TApps_invert in H1.
    destruct H1 as (H1 & Hargs).
    invert H1.
    invert H2.
    eapply tyeq1_par in H; eauto using bkinding_TApps.
    edestruct H as (r1 & r1' & Ht1r1 & Ht1'r1' & Hr1r1' & Hr1 & Hr1'); eauto.
    eapply pars_preserves_TApps_TRec in Ht1r1.
    openhyp; subst.
    eapply pars_preserves_TNat in Ht1'r1'.
    openhyp; subst.
    set (k' := KArrows (map fst args) KType) in *.
    destruct (TApps_TRec_dec args k' x) as [ [ [? ?] [Heq ?] ] | [Heq ?]]; subst; simpl in * ; try rewrite Heq in *; invert Hr1r1'.
  Qed.

  Lemma invert_tyeq1_TQuanI_TNat L q s t1 i K k :
    let t := TQuanI q s t1 in
    let t' := TNat i in
    tyeq1 L K t t' k ->
    let bs := map get_bsort L in
    bkinding bs K t k ->
    bkinding bs K t' k ->
    wfsorts1 L ->
    False.
  Proof.
    simpl.
    intros H H1 H2 HL.
    invert H1.
    invert H2.
    eapply tyeq1_par in H; simpl; eauto.
    edestruct H as (r1 & r1' & Ht1r1 & Ht1'r1' & Hr1r1' & Hr1 & Hr1'); eauto.
    eapply pars_preserves_TQuanI in Ht1r1.
    openhyp; subst.
    eapply pars_preserves_TNat in Ht1'r1'.
    openhyp; subst.
    invert Hr1r1'.
  Qed.

  Lemma invert_tyeq1_TQuanI_TArr L q s t1 t1' i K k :
    let t := TQuanI q s t1 in
    let t' := TArr t1' i in
    tyeq1 L K t t' k ->
    let bs := map get_bsort L in
    bkinding bs K t k ->
    bkinding bs K t' k ->
    wfsorts1 L ->
    False.
  Proof.
    simpl.
    intros H H1 H2 HL.
    invert H1.
    invert H2.
    eapply tyeq1_par in H; simpl; eauto.
    edestruct H as (r1 & r1' & Ht1r1 & Ht1'r1' & Hr1r1' & Hr1 & Hr1'); eauto.
    eapply pars_preserves_TQuanI in Ht1r1.
    openhyp; subst.
    eapply pars_preserves_TArr in Ht1'r1'.
    openhyp; subst.
    invert Hr1r1'.
  Qed.

  Lemma invert_tyeq1_TNat_TArrow L i t1 i' t2 K k :
    let t := TNat i in
    let t' := TArrow t1 i' t2 in
    tyeq1 L K t t' k ->
    let bs := map get_bsort L in
    bkinding bs K t k ->
    bkinding bs K t' k ->
    wfsorts1 L ->
    False.
  Proof.
    simpl.
    intros H H1 H2 HL.
    invert H1.
    invert H2.
    eapply tyeq1_par in H; simpl; eauto.
    edestruct H as (r1 & r1' & Ht1r1 & Ht1'r1' & Hr1r1' & Hr1 & Hr1'); eauto.
    eapply pars_preserves_TNat in Ht1r1.
    openhyp; subst.
    eapply pars_preserves_TArrow in Ht1'r1'.
    openhyp; subst.
    invert Hr1r1'.
  Qed.

  Lemma invert_tyeq1_TArr_TArrow L t1 i t1' i' t2' K k :
    let t := TArr t1 i in
    let t' := TArrow t1' i' t2' in
    tyeq1 L K t t' k ->
    let bs := map get_bsort L in
    bkinding bs K t k ->
    bkinding bs K t' k ->
    wfsorts1 L ->
    False.
  Proof.
    simpl.
    intros H H1 H2 HL.
    invert H1.
    invert H2.
    eapply tyeq1_par in H; simpl; eauto.
    edestruct H as (r1 & r1' & Ht1r1 & Ht1'r1' & Hr1r1' & Hr1 & Hr1'); eauto.
    eapply pars_preserves_TArr in Ht1r1.
    openhyp; subst.
    eapply pars_preserves_TArrow in Ht1'r1'.
    openhyp; subst.
    invert Hr1r1'.
  Qed.

  Lemma invert_tyeq1_TQuan_TNat L q s t1 i K k :
    let t := TQuan q s t1 in
    let t' := TNat i in
    tyeq1 L K t t' k ->
    let bs := map get_bsort L in
    bkinding bs K t k ->
    bkinding bs K t' k ->
    wfsorts1 L ->
    False.
  Proof.
    simpl.
    intros H H1 H2 HL.
    invert H1.
    invert H2.
    eapply tyeq1_par in H; simpl; eauto.
    edestruct H as (r1 & r1' & Ht1r1 & Ht1'r1' & Hr1r1' & Hr1 & Hr1'); eauto.
    eapply pars_preserves_TQuan in Ht1r1.
    openhyp; subst.
    eapply pars_preserves_TNat in Ht1'r1'.
    openhyp; subst.
    invert Hr1r1'.
  Qed.

  Lemma invert_tyeq1_TQuan_TArr q s t1 t1' i L K k :
    let t := TQuan q s t1 in
    let t' := TArr t1' i in
    tyeq1 L K t t' k ->
    let bs := map get_bsort L in
    bkinding bs K t k ->
    bkinding bs K t' k ->
    wfsorts1 L ->
    False.
  Proof.
    simpl.
    intros H H1 H2 HL.
    invert H1.
    invert H2.
    eapply tyeq1_par in H; simpl; eauto.
    edestruct H as (r1 & r1' & Ht1r1 & Ht1'r1' & Hr1r1' & Hr1 & Hr1'); eauto.
    eapply pars_preserves_TQuan in Ht1r1.
    openhyp; subst.
    eapply pars_preserves_TArr in Ht1'r1'.
    openhyp; subst.
    invert Hr1r1'.
  Qed.

  Lemma invert_tyeq1_TApps_TRec_TArr k1 t1 args t1' i L K k :
    let t := TApps (TRec k1 t1) args in
    let t' := TArr t1' i in
    tyeq1 L K t t' k ->
    let bs := map get_bsort L in
    bkinding bs K t k ->
    bkinding bs K t' k ->
    wfsorts1 L ->
    False.
  Proof.
    simpl.
    intros H H1 H2 HL.
    eapply bkinding_TApps_invert in H1.
    destruct H1 as (H1 & Hargs).
    invert H1.
    invert H2.
    eapply tyeq1_par in H; eauto using bkinding_TApps.
    edestruct H as (r1 & r1' & Ht1r1 & Ht1'r1' & Hr1r1' & Hr1 & Hr1'); eauto.
    eapply pars_preserves_TApps_TRec in Ht1r1.
    openhyp; subst.
    eapply pars_preserves_TArr in Ht1'r1'.
    openhyp; subst.
    set (k' := KArrows (map fst args) KType) in *.
    destruct (TApps_TRec_dec args k' x) as [ [ [? ?] [Heq ?] ] | [Heq ?]]; subst; simpl in * ; try rewrite Heq in *; invert Hr1r1'.
  Qed.

  Lemma invert_tyeq1_TNat_TBinOp i opr t1 t2 L K k :
    let t := TNat i in
    let t' := TBinOp opr t1 t2 in
    tyeq1 L K t t' k ->
    let bs := map get_bsort L in
    bkinding bs K t k ->
    bkinding bs K t' k ->
    wfsorts1 L ->
    False.
  Proof.
    simpl.
    intros H H1 H2 HL.
    invert H1.
    invert H2.
    eapply tyeq1_par in H; simpl; eauto.
    edestruct H as (r1 & r1' & Ht1r1 & Ht1'r1' & Hr1r1' & Hr1 & Hr1'); eauto.
    eapply pars_preserves_TNat in Ht1r1.
    openhyp; subst.
    eapply pars_preserves_TBinOp in Ht1'r1'.
    openhyp; subst.
    invert Hr1r1'.
  Qed.

  Lemma invert_tyeq1_TArr_TBinOp t1 i opr t1' t2' L K k :
    let t := TArr t1 i in
    let t' := TBinOp opr t1' t2' in
    tyeq1 L K t t' k ->
    let bs := map get_bsort L in
    bkinding bs K t k ->
    bkinding bs K t' k ->
    wfsorts1 L ->
    False.
  Proof.
    simpl.
    intros H H1 H2 HL.
    invert H1.
    invert H2.
    eapply tyeq1_par in H; simpl; eauto.
    edestruct H as (r1 & r1' & Ht1r1 & Ht1'r1' & Hr1r1' & Hr1 & Hr1'); eauto.
    eapply pars_preserves_TArr in Ht1r1.
    openhyp; subst.
    eapply pars_preserves_TBinOp in Ht1'r1'.
    openhyp; subst.
    invert Hr1r1'.
  Qed.

  Lemma invert_tyeq1_TNat_TArr i t1 i' L K k :
    let t := TNat i in
    let t' := TArr t1 i' in
    tyeq1 L K t t' k ->
    let bs := map get_bsort L in
    bkinding bs K t k ->
    bkinding bs K t' k ->
    wfsorts1 L ->
    False.
  Proof.
    simpl.
    intros H H1 H2 HL.
    invert H1.
    invert H2.
    eapply tyeq1_par in H; simpl; eauto.
    edestruct H as (r1 & r1' & Ht1r1 & Ht1'r1' & Hr1r1' & Hr1 & Hr1'); eauto.
    eapply pars_preserves_TNat in Ht1r1.
    openhyp; subst.
    eapply pars_preserves_TArr in Ht1'r1'.
    openhyp; subst.
    invert Hr1r1'.
  Qed.

  Lemma invert_tyeq1_TConst_TArrow cn t1 i t2 L K k :
    let t := TConst cn in
    let t' := TArrow t1 i t2 in
    tyeq1 L K t t' k ->
    let bs := map get_bsort L in
    bkinding bs K t k ->
    bkinding bs K t' k ->
    wfsorts1 L ->
    False.
  Proof.
    simpl.
    intros H H1 H2 HL.
    invert H1.
    invert H2.
    eapply tyeq1_par in H; simpl; eauto.
    edestruct H as (r1 & r1' & Ht1r1 & Ht1'r1' & Hr1r1' & Hr1 & Hr1'); eauto.
    eapply pars_preserves_TConst in Ht1r1.
    openhyp; subst.
    eapply pars_preserves_TArrow in Ht1'r1'.
    openhyp; subst.
    invert Hr1r1'.
  Qed.

  Lemma invert_tyeq1_TConst_TQuan cn q k1 t1 L K k :
    let t := TConst cn in
    let t' := TQuan q k1 t1 in
    tyeq1 L K t t' k ->
    let bs := map get_bsort L in
    bkinding bs K t k ->
    bkinding bs K t' k ->
    wfsorts1 L ->
    False.
  Proof.
    simpl.
    intros H H1 H2 HL.
    invert H1.
    invert H2.
    eapply tyeq1_par in H; simpl; eauto.
    edestruct H as (r1 & r1' & Ht1r1 & Ht1'r1' & Hr1r1' & Hr1 & Hr1'); eauto.
    eapply pars_preserves_TConst in Ht1r1.
    openhyp; subst.
    eapply pars_preserves_TQuan in Ht1'r1'.
    openhyp; subst.
    invert Hr1r1'.
  Qed.

  Lemma invert_tyeq1_TConst cn cn' L K k :
    let t := TConst cn in
    let t' := TConst cn' in
    tyeq1 L K t t' k ->
    let bs := map get_bsort L in
    bkinding bs K t k ->
    bkinding bs K t' k ->
    wfsorts1 L ->
    cn = cn'.
  Proof.
    simpl.
    intros H H1 H2 HL.
    invert H1.
    invert H2.
    eapply tyeq1_par in H; eauto.
    edestruct H as (r1 & r1' & Ht1r1 & Ht1'r1' & Hr1r1' & Hr1 & Hr1'); eauto.
    eapply pars_preserves_TConst in Ht1r1.
    openhyp; subst.
    eapply pars_preserves_TConst in Ht1'r1'.
    openhyp; subst.
    invert Hr1r1'.
    repeat try_split; eauto.
  Qed.

  Lemma invert_tyeq1_TConst_TNat cn i L K k :
    let t := TConst cn in
    let t' := TNat i in
    tyeq1 L K t t' k ->
    let bs := map get_bsort L in
    bkinding bs K t k ->
    bkinding bs K t' k ->
    wfsorts1 L ->
    False.
  Proof.
    simpl.
    intros H H1 H2 HL.
    invert H1.
    invert H2.
    eapply tyeq1_par in H; simpl; eauto.
    edestruct H as (r1 & r1' & Ht1r1 & Ht1'r1' & Hr1r1' & Hr1 & Hr1'); eauto.
    eapply pars_preserves_TConst in Ht1r1.
    openhyp; subst.
    eapply pars_preserves_TNat in Ht1'r1'.
    openhyp; subst.
    invert Hr1r1'.
  Qed.

  Lemma invert_tyeq1_TConst_TArr cn t1 i L K k :
    let t := TConst cn in
    let t' := TArr t1 i in
    tyeq1 L K t t' k ->
    let bs := map get_bsort L in
    bkinding bs K t k ->
    bkinding bs K t' k ->
    wfsorts1 L ->
    False.
  Proof.
    simpl.
    intros H H1 H2 HL.
    invert H1.
    invert H2.
    eapply tyeq1_par in H; simpl; eauto.
    edestruct H as (r1 & r1' & Ht1r1 & Ht1'r1' & Hr1r1' & Hr1 & Hr1'); eauto.
    eapply pars_preserves_TConst in Ht1r1.
    openhyp; subst.
    eapply pars_preserves_TArr in Ht1'r1'.
    openhyp; subst.
    invert Hr1r1'.
  Qed.

  (* ============================================================= *)
  (* The term language *)
  (* ============================================================= *)
  
  
  Inductive expr_const :=
  | ECTT
  | ECInt (i : int)
  | ECNat (n : nat)
  .

  Inductive prim_expr_bin_op :=
  | PEBIntAdd
  | PEBIntMult
  .

  Definition prim_cost opr :=
    match opr with
    | PEBIntAdd => 0%time
    | PEBIntMult => 0%time
    end.

  Definition prim_arg1_type opr :=
    match opr with
    | PEBIntAdd => TInt
    | PEBIntMult => TInt
    end.
    
  Definition prim_arg2_type opr :=
    match opr with
    | PEBIntAdd => TInt
    | PEBIntMult => TInt
    end.
    
  Definition prim_result_type opr :=
    match opr with
    | PEBIntAdd => TInt
    | PEBIntMult => TInt
    end.
    
  Inductive projector :=
  | ProjFst
  | ProjSnd
  .

  Inductive injector :=
  | InjInl
  | InjInr
  .

  Definition loc := nat.

  Definition hctx := fmap loc (ty * idx).
  Definition tctx := list ty.
  Definition ctx := (sctx * kctx * hctx * tctx)%type.
  
  Inductive expr_un_op :=
  | EUProj (p : projector)
  | EUInj (inj : injector)
  | EUFold
  | EUUnfold
  .

  Inductive expr_bin_op :=
  | EBPrim (opr : prim_expr_bin_op)
  | EBApp
  | EBPair
  | EBNew 
  | EBRead 
  | EBNatAdd
  .

  Definition nat_add_cost := 0%time.

  Inductive expr :=
  | EVar (x : var)
  | EConst (cn : expr_const)
  | ELoc (l : loc)
  | EUnOp (opr : expr_un_op) (e : expr)
  | EBinOp (opr : expr_bin_op) (e1 e2 : expr)
  | EWrite (e_arr e_idx e_val : expr)
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
  .

  Definition EProj p e := EUnOp (EUProj p) e.
  Definition EInj c e := EUnOp (EUInj c) e.
  Definition EFold e := EUnOp EUFold e.
  Definition EUnfold e := EUnOp EUUnfold e.
  Definition ENew e1 e2 := EBinOp EBNew e1 e2.
  Definition ERead e1 e2 := EBinOp EBRead e1 e2.

  Definition EApp := EBinOp EBApp.
  Definition EPair := EBinOp EBPair.
  (* Definition EWrite := EBinOp EBWrite. *)
  Definition EPrim opr := EBinOp (EBPrim opr).
  
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

  Definition shift_i_ti n x b := (shift_i_t n x (fst b), shift_i_i n x (snd b)).
  Definition shift0_i_ti := shift_i_ti 1 0.
  
  Definition add_sorting_ctx s (C : ctx) : ctx :=
    match C with
      (L, K, W, G) => (s :: L, K, fmap_map shift0_i_ti W, map shift0_i_t G)
    end
  .

  Definition shift_t_ti n x (b : ty * idx) := (shift_t_t n x (fst b), snd b).
  Definition shift0_t_ti := shift_t_ti 1 0.
  
  Definition add_kinding_ctx k (C : ctx) :=
    match C with
      (L, K, W, G) => (L, k :: K, fmap_map shift0_t_ti W, map shift0_t_t G)
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
    | ECNat n => TNat (IConst (ICNat n))
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

  Definition unroll (k : kind) (t : ty) (args : list (bsort * idx)) : ty :=
    let r := subst0_t_t (TRec k t) t in
    TApps r args.

  Definition ENatAdd := EBinOp EBNatAdd.
  
  Inductive typing1 : ctx -> expr -> ty -> idx -> Prop :=
  | Ty1Var C x t :
      nth_error (get_tctx C) x = Some t ->
      typing1 C (EVar x) t T0
  | Ty1App C e1 e2 t i1 i2 i t2 :
      typing1 C e1 (TArrow t2 i t) i1 ->
      typing1 C e2 t2 i2 ->
      typing1 C (EApp e1 e2) t (i1 + i2 + T1 + i)
  | Ty1Abs C e t1 i t :
      kinding1 (get_sctx C) (get_kctx C) t1 KType ->
      typing1 (add_typing_ctx t1 C) e t i ->
      typing1 C (EAbs e) (TArrow t1 i t) T0
  | Ty1AppT C e t t1 i k :
      typing1 C e (TForall k t1) i ->
      kinding1 (get_sctx C) (get_kctx C) t k -> 
      typing1 C (EAppT e t) (subst0_t_t t t1) i
  | Ty1AbsT C e t k :
      value e ->
      typing1 (add_kinding_ctx k C) e t T0 ->
      typing1 C (EAbsT e) (TForall k t) T0
  | Ty1AppI C e c t i s :
      typing1 C e (TForallI s t) i ->
      sorting1 (get_sctx C) c s -> 
      typing1 C (EAppI e c) (subst0_i_t c t) i
  | Ty1AbsI C e t s :
      value e ->
      wfsort1 (map get_bsort (get_sctx C)) s ->
      typing1 (add_sorting_ctx s C) e t T0 ->
      typing1 C (EAbsI e) (TForallI s t) T0
  | Ty1Rec C tis e1 t :
      let e := EAbsTIs tis (EAbs e1) in
      kinding1 (get_sctx C) (get_kctx C) t KType ->
      typing1 (add_typing_ctx t C) e t T0 ->
      typing1 C (ERec e) t T0
  | Ty1Fold C e k t cs i :
      let t_rec := TApps (TRec k t) cs in
      kinding1 (get_sctx C) (get_kctx C) t_rec KType ->
      typing1 C e (unroll k t cs) i ->
      typing1 C (EFold e) t_rec i
  | Ty1Unfold C e k t cs i :
      typing1 C e (TApps (TRec k t) cs) i ->
      typing1 C (EUnfold e) (unroll k t cs) i
  | Ty1Pack C c e i t1 k :
      kinding1 (get_sctx C) (get_kctx C) (TExists k t1) KType ->
      kinding1 (get_sctx C) (get_kctx C) c k ->
      typing1 C e (subst0_t_t c t1) i ->
      typing1 C (EPack c e) (TExists k t1) i
  | Ty1Unpack C e1 e2 t2 i1 i2 t k :
      typing1 C e1 (TExists k t) i1 ->
      typing1 (add_typing_ctx t (add_kinding_ctx k C)) e2 (shift0_t_t t2) i2 ->
      typing1 C (EUnpack e1 e2) t2 (i1 + i2)
  | Ty1PackI C c e i t1 s :
      kinding1 (get_sctx C) (get_kctx C) (TExistsI s t1) KType ->
      sorting1 (get_sctx C) c s ->
      typing1 C e (subst0_i_t c t1) i ->
      typing1 C (EPackI c e) (TExistsI s t1) i
  | Ty1UnpackI C e1 e2 t2 i1 i2 t s :
      typing1 C e1 (TExistsI s t) i1 ->
      typing1 (add_typing_ctx t (add_sorting_ctx s C)) e2 (shift0_i_t t2) (shift0_i_i i2) ->
      typing1 C (EUnpackI e1 e2) t2 (i1 + i2)
  | Ty1Const C cn :
      typing1 C (EConst cn) (const_type cn) T0
  | Ty1Pair C e1 e2 t1 t2 i1 i2 :
      typing1 C e1 t1 i1 ->
      typing1 C e2 t2 i2 ->
      typing1 C (EPair e1 e2) (TProd t1 t2) (i1 + i2)
  | Ty1Proj C pr e t1 t2 i :
      typing1 C e (TProd t1 t2) i ->
      typing1 C (EProj pr e) (proj (t1, t2) pr) i
  | Ty1Inj C inj e t t' i :
      typing1 C e t i ->
      kinding1 (get_sctx C) (get_kctx C) t' KType ->
      typing1 C (EInj inj e) (choose (TSum t t', TSum t' t) inj) i
  | Ty1Case C e e1 e2 t i i1 i2 t1 t2 :
      typing1 C e (TSum t1 t2) i ->
      typing1 (add_typing_ctx t1 C) e1 t i1 ->
      typing1 (add_typing_ctx t2 C) e2 t i2 ->
      typing1 C (ECase e e1 e2) t (i + Tmax i1 i2)
  | Ty1New C e1 e2 t len i1 i2 :
      typing1 C e1 t i1 ->
      typing1 C e2 (TNat len) i2 ->
      typing1 C (ENew e1 e2) (TArr t len) (i1 + i2)
  | Ty1Read C e1 e2 t i1 i2 len i :
      typing1 C e1 (TArr t len) i1 ->
      typing1 C e2 (TNat i) i2 ->
      interp_prop (get_sctx C) (i < len) ->
      typing1 C (ERead e1 e2) t (i1 + i2)
  | Ty1Write C e1 e2 e3 i1 i2 i3 t len i :
      typing1 C e1 (TArr t len) i1 ->
      typing1 C e2 (TNat i) i2 ->
      interp_prop (get_sctx C) (i < len) ->
      typing1 C e3 t i3 ->
      typing1 C (EWrite e1 e2 e3) TUnit (i1 + i2 + i3)
  | Ty1Loc C l t i :
      get_hctx C $? l = Some (t, i) ->
      typing1 C (ELoc l) (TArr t i) T0
  | Ty1Prim C opr e1 e2 i1 i2 :
      typing1 C e1 (prim_arg1_type opr) i1 ->
      typing1 C e2 (prim_arg2_type opr) i2 ->
      typing1 C (EPrim opr e1 e2) (prim_result_type opr) (i1 + i2 + Tconst (prim_cost opr))
  | Ty1NatAdd C e1 e2 j1 j2 i1 i2 :
      typing1 C e1 (TNat j1) i1 ->
      typing1 C e2 (TNat j2) i2 ->
      typing1 C (ENatAdd e1 e2) (TNat (Nadd j1 j2)) (i1 + i2 + Tconst nat_add_cost)
  | Ty1Ty1eq C e t1 i t2 :
      typing1 C e t1 i ->
      let L := get_sctx C in
      let K := get_kctx C in
      kinding1 L K t2 KType ->
      tyeq1 L K t1 t2 KType ->
      typing1 C e t2 i
  | Ty1Le C e t i1 i2 :
      typing1 C e t i1 ->
      let L := get_sctx C in
      sorting1 L i2 STime ->
      interp_prop L (i1 <= i2) ->
      typing1 C e t i2 
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
      | EWrite e1 e2 e3 => EWrite (shift_i_e x e1) (shift_i_e x e2) (shift_i_e x e3)
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
      | EWrite e1 e2 e3 => EWrite (shift_t_e x e1) (shift_t_e x e2) (shift_t_e x e3)
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
      | EWrite e1 e2 e3 => EWrite (shift_e_e x e1) (shift_e_e x e2) (shift_e_e x e3)
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
    | EWrite e1 e2 e3 => EWrite (subst_i_e x v e1) (subst_i_e x v e2) (subst_i_e x v e3)
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
    | EWrite e1 e2 e3 => EWrite (subst_t_e x v e1) (subst_t_e x v e2) (subst_t_e x v e3)
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
    | EWrite e1 e2 e3 => EWrite (subst_e_e x v e1) (subst_e_e x v e2) (subst_e_e x v e3)
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
  | ECWrite1 (E : ectx) (e2 e3 : expr)
  | ECWrite2 (v1 : expr) (E : ectx) (e3 : expr)
  | ECWrite3 (v1 v2 : expr) (E : ectx)
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
  | PlugWrite1 E e e' e2 e3 :
      plug E e e' ->
      plug (ECWrite1 E e2 e3) e (EWrite e' e2 e3)
  | PlugWrite2 E e e' v1 e3 :
      plug E e e' ->
      value v1 ->
      plug (ECWrite2 v1 E e3) e (EWrite v1 e' e3)
  | PlugWrite3 E e e' v1 v2 :
      plug E e e' ->
      value v1 ->
      value v2 ->
      plug (ECWrite3 v1 v2 E) e (EWrite v1 v2 e')
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

  Definition heap := fmap loc (list expr).

  Definition fuel := time_type.

  Definition config := (heap * expr * fuel)%type.

  (* Require Import Reals. *)

  (* Local Open Scope R_scope. *)

  (* Local Open Scope time_scope. *)

  Import OpenScope.

  Definition ENat n := EConst (ECNat n).
  Arguments ENat _ / .
  Definition EInt n := EConst (ECInt n).
  Arguments EInt _ / .
  
  Definition upd {A} ls n (v : A) := insert [v] n (removen n ls).

  Notation int_add := BinIntDef.Z.add.
  Notation int_mult := BinIntDef.Z.mul.
  
  Definition exec_prim opr a b :=
    match (opr, a, b) with
    | (PEBIntAdd, ECInt a, ECInt b) => Some (ECInt (int_add a b))
    | (PEBIntMult, ECInt a, ECInt b) => Some (ECInt (int_mult a b))
    | _ => None
    end.
  
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
  | ARead h l n t vs v :
      h $? l = Some vs ->
      nth_error vs n = Some v ->
      astep (h, ERead (ELoc l) (ENat n), t) (h, v, t)
  | AWrite h l n v t vs :
      value v ->
      h $? l = Some vs ->
      n < length vs ->
      astep (h, EWrite (ELoc l) (ENat n) v, t) (h $+ (l, upd vs n v), ETT, t)
  | ANew h v n t l :
      value v ->
      h $? l = None ->
      astep (h, ENew v (ENat n), t) (h $+ (l, repeat v n), ELoc l, t)
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
  | ANatAdd h n1 n2 t :
      nat_add_cost <= t ->
      astep (h, ENatAdd (ENat n1) (ENat n2), t) (h, ENat (n1 + n2), t - nat_add_cost)
  | APrim h opr cn1 cn2 t cn :
      prim_cost opr <= t ->
      exec_prim opr cn1 cn2 = Some cn ->
      astep (h, EPrim opr (EConst cn1) (EConst cn2), t) (h, EConst cn, t - prim_cost opr)
  .

  Inductive step : config -> config -> Prop :=
  | StepPlug h e1 t h' e1' t' e e' E :
      astep (h, e, t) (h', e', t') ->
      plug E e e1 ->
      plug E e' e1' ->
      step (h, e1, t) (h', e1', t')
  .

  Definition allocatable (h : heap) := exists l_alloc, forall l, l >= l_alloc -> h $? l = None.
  
  Definition htyping1 (h : heap) (W : hctx) :=
    (forall l t i,
        W $? l = Some (t, i) ->
        exists vs,
          h $? l = Some vs /\
          length vs = interp_idx i [] BSNat /\
          Forall (fun v => value v /\ typing1 ([], [], W, []) v t T0) vs) /\
    allocatable h.

  Definition kinding1_KType L K t := kinding1 L K t KType.
  Arguments kinding1_KType L K t / .

  Definition wfhctx1 L K (W : hctx) := fmap_forall (fun p => kinding1 L K (fst p) KType /\ sorting1 L (snd p) SNat) W.
  
  Definition wfctx1 C :=
    let L := get_sctx C in
    let K := get_kctx C in
    let W := get_hctx C in
    let G := get_tctx C in
    wfsorts1 L /\
    wfhctx1 L K W /\
    Forall (kinding1_KType L K) G.
  
  Definition ctyping1 W (s : config) t i :=
    let '(h, e, f) := s in
    let C := ([], [], W, []) in
    typing1 C e t i /\
    htyping1 h W /\
    interp_time i <= f /\
    wfctx1 C
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

  
  Lemma Ty1ETT C : typing1 C ETT TUnit T0.
  Proof.
    eapply Ty1Const.
  Qed.

  Lemma Ty1IdxEq C e t i1 i2 :
    typing1 C e t i1 ->
    sorting1 (get_sctx C) i2 STime ->
    interp_prop (get_sctx C) (i1 == i2)%idx ->
    typing1 C e t i2.
  Proof.
    intros.
    eapply Ty1Le; eauto.
    eapply interp_prop_eq_interp_prop_le; eauto.
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
  
  Lemma shift0_i_ti_shift n x b :
    shift0_i_ti (shift_i_ti n x b) = shift_i_ti n (1 + x) (shift0_i_ti b).
  Proof.
    unfold shift0_i_ti, shift_i_ti; intros.
    simpl.
    rewrite shift0_i_t_shift.
    rewrite shift0_i_i_shift.
    eauto.
  Qed.

  Lemma fmap_map_shift0_i_ti_shift n x (W : hctx) :
    fmap_map shift0_i_ti (fmap_map (shift_i_ti n x) W) =
    fmap_map (shift_i_ti n (1 + x)) (fmap_map shift0_i_ti W).
  Proof.
    repeat rewrite fmap_map_fmap_map.
    setoid_rewrite shift0_i_ti_shift.
    eauto.
  Qed.

  Lemma shift0_t_ti_shift n x b :
    shift0_t_ti (shift_t_ti n x b) = shift_t_ti n (1 + x) (shift0_t_ti b).
  Proof.
    unfold shift0_t_ti, shift_t_ti; intros.
    simpl.
    rewrite shift0_t_t_shift.
    eauto.
  Qed.

  Lemma fmap_map_shift0_t_ti_shift n x (W : hctx) :
    fmap_map shift0_t_ti (fmap_map (shift_t_ti n x) W) =
    fmap_map (shift_t_ti n (1 + x)) (fmap_map shift0_t_ti W).
  Proof.
    repeat rewrite fmap_map_fmap_map.
    setoid_rewrite shift0_t_ti_shift.
    eauto.
  Qed.

  Definition subst_i_ti x v b := (subst_i_t x v (fst b), subst_i_i x v (snd b)).
  Definition subst0_i_ti := subst_i_ti 0.
  
  Lemma shift0_i_ti_subst x v b :
    shift0_i_ti (subst_i_ti x (shift_i_i x 0 v) b) = subst_i_ti (1 + x) (shift_i_i (1 + x) 0 v) (shift0_i_ti b).
  Proof.
    unfold shift0_i_ti, shift_i_ti, subst_i_ti; intros.
    simpl.
    rewrite shift0_i_t_subst.
    rewrite shift0_i_i_subst.
    eauto.
  Qed.

  Lemma fmap_map_shift0_i_ti_subst n c (W : hctx) :
    fmap_map shift0_i_ti (fmap_map (subst_i_ti n (shift_i_i n 0 c)) W) =
    fmap_map (subst_i_ti (1 + n) (shift_i_i (1 + n) 0 c)) (fmap_map shift0_i_ti W).
  Proof.
    repeat rewrite fmap_map_fmap_map.
    setoid_rewrite shift0_i_ti_subst.
    eauto.
  Qed.
  
  Definition subst_t_ti x v (b : ty * idx) := (subst_t_t x v (fst b), snd b).
  Definition subst0_t_ti := subst_t_ti 0.
    
  Lemma shift0_t_ti_subst x v b :
    shift0_t_ti (subst_t_ti x (shift_t_t x 0 v) b) = subst_t_ti (1 + x) (shift_t_t (1 + x) 0 v) (shift0_t_ti b).
  Proof.
    unfold shift0_t_ti, shift_t_ti, subst_t_ti; intros.
    simpl.
    rewrite shift0_t_t_subst.
    eauto.
  Qed.

  Lemma fmap_map_shift0_t_ti_subst n c (W : hctx) :
    fmap_map shift0_t_ti (fmap_map (subst_t_ti n (shift_t_t n 0 c)) W) =
    fmap_map (subst_t_ti (1 + n) (shift_t_t (1 + n) 0 c)) (fmap_map shift0_t_ti W).
  Proof.
    repeat rewrite fmap_map_fmap_map.
    setoid_rewrite shift0_t_ti_subst.
    eauto.
  Qed.
  
  Lemma subst0_i_ti_shift0 v b :
    subst0_i_ti v (shift0_i_ti b) = b.
  Proof.
    unfold shift0_i_ti, shift_i_ti, subst0_i_ti, subst_i_ti.
    simpl.
    rewrite subst0_i_t_shift0.
    rewrite subst0_i_i_shift0.
    destruct b; eauto.
  Qed.
  
  Lemma fmap_map_subst0_i_ti_shift0 k c W : fmap_map (K := k) (subst0_i_ti c) (fmap_map shift0_i_ti W) = W.
  Proof.
    repeat rewrite fmap_map_fmap_map.
    setoid_rewrite subst0_i_ti_shift0.
    eapply fmap_map_id.
  Qed.
  
  Lemma subst0_t_ti_shift0 v b :
    subst0_t_ti v (shift0_t_ti b) = b.
  Proof.
    unfold shift0_t_ti, shift_t_ti, subst0_t_ti, subst_t_ti.
    simpl.
    rewrite subst0_t_t_shift0.
    destruct b; eauto.
  Qed.
  
  Lemma fmap_map_subst0_t_ti_shift0 k c W : fmap_map (K := k) (subst0_t_ti c) (fmap_map shift0_t_ti W) = W.
  Proof.
    repeat rewrite fmap_map_fmap_map.
    setoid_rewrite subst0_t_ti_shift0.
    eapply fmap_map_id.
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
      rewrite shift_i_t_shift_t_t.
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
  
  Lemma shift_i_e_shift_t_e :
    forall b x2 n2 x1 n1,
      shift_i_e x2 n2 (shift_t_e x1 n1 b) = shift_t_e x1 n1 (shift_i_e x2 n2 b).
  Proof.
    induct b; simplify; try rewrite IHb; try rewrite IHb1; try rewrite IHb2; try rewrite IHb3; try rewrite shift_i_t_shift_t_t by la; eauto.
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
      rewrite shift_i_e_shift_t_e.
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
  
  Lemma value_typing1_T0 C e t i :
    typing1 C e t i ->
    value e ->
    typing1 C e t T0.
  Proof.
    induct 1;
      invert 1;
      try solve [eauto | econstructor; eauto | eapply Ty1Ty1eq; eauto].
    {
      (* Case Ty1Pair *)
      clear H H0.
      eapply Ty1IdxEq ; [econstructor; eauto | econstructor; eauto |  ].
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

  Lemma fmap_forall_fmap_map_intro K V V' (P : V' -> Prop) f (m : fmap K V) :
    fmap_forall (fun x => P (f x)) m ->
    fmap_forall P (fmap_map f m).
  Proof.
    intros H.
    unfold fmap_forall in *.
    intros k v Hk.
    eapply fmap_map_lookup_elim in Hk.
    openhyp.
    subst.
    eauto.
  Qed.

  Lemma fmap_forall_impl K V (P1 P2 : V -> Prop) (m : fmap K V) :
    fmap_forall P1 m ->
    (forall x, P1 x -> P2 x) ->
    fmap_forall P2 m.
  Proof.
    intros H1 H12.
    unfold fmap_forall in *.
    eauto.
  Qed.

  Lemma wellscoped_t_unroll L k t cs :
    wellscoped_t L t ->
    Forall (fun p => wellscoped_i L (snd p)) cs ->
    wellscoped_t L (unroll k t cs).
  Proof.
    unfold unroll.
    intros Ht Hcs.
    eapply wellscoped_t_TApps; eauto.
    eapply wellscoped_subst_t_t_0; eauto.
  Qed.

  Definition wellscoped_ti L p := wellscoped_t L (fst p) /\ wellscoped_i L (snd p).
  Arguments wellscoped_ti _ _ / .
  
  Lemma typing1_wellscoped_t C e t i :
    typing1 C e t i ->
    let L := get_sctx C in
    let W := get_hctx C in
    let G := get_tctx C in
    let nl := length L in
    (* wellscoped_ss L -> *)
    fmap_forall (wellscoped_ti nl) W ->
    Forall (wellscoped_t nl) G ->
    wellscoped_t nl t /\
    wellscoped_i nl i.
  Proof.
    simpl.
    induct 1; unfold_all;
      intros (* HL *) HW HG;
      destruct C as (((L & K) & W) & G);
      simplify; try solve [eauto using kinding1_wellscoped_t | edestruct IHtyping1; eauto using kinding1_wellscoped_t, sorting1_wellscoped_i].
    {
      (* Case Ty1Var *)
      eapply nth_error_Forall in HG; eauto.
    }
    {
      (* Case Ty1App *)
      edestruct IHtyping1_1 as (Ht & ?); eauto.
      edestruct IHtyping1_2; eauto.
      invert Ht.
      split; eauto.
      repeat (econstructor; eauto).
    }
    {
      (* Case Ty1AppT *)
      edestruct IHtyping1 as (Ht & ?); eauto.
      invert Ht.
      split; eauto.
      eapply wellscoped_subst_t_t_0; eauto using kinding1_wellscoped_t.
    }
    {
      (* Case Ty1AbsT *)
      edestruct IHtyping1.
      {
        eapply fmap_forall_fmap_map_intro.
        eapply fmap_forall_impl; eauto.
        intros.
        simpl in *.
        intuition eauto using wellscoped_shift_t_t.
      }
      {
        eapply Forall_map.
        eapply Forall_impl; eauto.
        intros.
        eapply wellscoped_shift_t_t; eauto.
      }
      split; eauto.
      econstructor; eauto using kinding1_wellscoped_t.
    }
    {
      (* Case Ty1AppI *)
      edestruct IHtyping1 as (Ht & ?); eauto.
      invert Ht.
      split; eauto.
      eapply wellscoped_subst_i_t_0; eauto using sorting1_wellscoped_i with db_la.
    }
    {
      (* Case Ty1AbsI *)
      edestruct IHtyping1.
      {
        eapply fmap_forall_fmap_map_intro.
        eapply fmap_forall_impl; eauto.
        intros.
        simpl in *.
        intuition eauto using wellscoped_shift_i_t, wellscoped_shift_i_i.
      }
      {
        eapply Forall_map.
        eapply Forall_impl; eauto.
        intros.
        eapply wellscoped_shift_i_t; eauto.
      }
      split; eauto.
      econstructor; eauto using wfsort1_wellscoped_s'.
      eapply wfsort1_wellscoped_s'; eauto.
      rewrite map_length; eauto.
    }
    {
      (* Case Ty1UnFold *)
      edestruct IHtyping1 as (Ht & ?); eauto.
      eapply wellscoped_t_TApps_invert in Ht.
      destruct Ht as [Ht ?].
      invert Ht.
      split; eauto.
      eapply wellscoped_t_unroll; eauto.
    }
    {
      (* Case Ty1UnPack *)
      edestruct IHtyping1_1 as (Ht & ?); eauto.
      invert Ht.
      edestruct IHtyping1_2 as (Ht2 & ?).
      {
        eapply fmap_forall_fmap_map_intro.
        eapply fmap_forall_impl; eauto.
        intros.
        simpl in *.
        intuition eauto using wellscoped_shift_t_t.
      }
      {
        econstructor; eauto.
        eapply Forall_map.
        eapply Forall_impl; eauto.
        intros.
        eapply wellscoped_shift_t_t; eauto.
      }
      unfold shift0_t_t in *.
      eapply wellscoped_shift_t_t_rev in Ht2; eauto.
      split; eauto.
      econstructor; eauto.
    }
    {
      (* Case Ty1UnPackI *)
      edestruct IHtyping1_1 as (Ht & ?); eauto.
      invert Ht.
      edestruct IHtyping1_2 as (Ht2 & Hi2).
      {
        eapply fmap_forall_fmap_map_intro.
        eapply fmap_forall_impl; eauto.
        intros.
        simpl in *.
        intuition eauto using wellscoped_shift_i_t, wellscoped_shift_i_i.
      }
      {
        econstructor; eauto.
        eapply Forall_map.
        eapply Forall_impl; eauto.
        intros.
        eapply wellscoped_shift_i_t; eauto.
      }
      unfold shift0_i_i, shift0_i_t in *.
      eapply wellscoped_shift_i_i_rev in Hi2; eauto with db_la.
      eapply wellscoped_shift_i_t_rev in Ht2; eauto with db_la.
      simpl in *.
      rewrite Nat.sub_0_r in *.
      split; eauto.
      econstructor; eauto.
    }
    {
      (* Case Ty1Const *)
      destruct cn; simpl; split; econstructor; eauto.
    }
    {
      (* Case Ty1Pair *)
      edestruct IHtyping1_1; eauto.
      edestruct IHtyping1_2; eauto.
      split; econstructor; eauto.
    }
    {
      (* Case Ty1Proj *)
      edestruct IHtyping1 as (Ht & ?); eauto.
      invert Ht.
      destruct pr; split; eauto.
    }
    {
      (* Case Ty1Inj *)
      edestruct IHtyping1; eauto.
      destruct inj; simpl; split; eauto; econstructor; eauto using kinding1_wellscoped_t.
    }
    {
      (* Case Ty1Case *)
      edestruct IHtyping1_1 as (Ht & ?); eauto.
      invert Ht.
      edestruct IHtyping1_2; eauto.
      edestruct IHtyping1_3; eauto.
      split; eauto; repeat (econstructor; eauto).
    }
    {
      (* Case New *)
      edestruct IHtyping1_1; eauto.
      edestruct IHtyping1_2 as (Ht & ?); eauto.
      invert Ht.
      split; eauto; econstructor; eauto.
    }
    {
      (* Case Ty1Read *)
      edestruct IHtyping1_1 as (Ht & ?); eauto.
      invert Ht.
      edestruct IHtyping1_2 as (Ht & ?); eauto.
      invert Ht.
      split; eauto; econstructor; eauto.
    }
    {
      (* Case Ty1Write *)
      edestruct IHtyping1_1 as (Ht & ?); eauto.
      invert Ht.
      edestruct IHtyping1_2 as (Ht & ?); eauto.
      invert Ht.
      edestruct IHtyping1_3; eauto.
      split; eauto; repeat (econstructor; eauto).
    }
    {
      (* Case Loc *)
      eapply HW in H.
      simpl in *.
      openhyp.
      split; eauto; econstructor; eauto.
    }
    {
      (* Case Ty1Prim *)
      edestruct IHtyping1_1; eauto.
      edestruct IHtyping1_2; eauto.
      split; eauto; repeat (econstructor; eauto).
    }
    {
      (* Case Ty1NatAdd *)
      edestruct IHtyping1_1 as (Ht & ?); eauto.
      invert Ht.
      edestruct IHtyping1_2 as (Ht & ?); eauto.
      invert Ht.
      split; eauto; repeat (econstructor; eauto).
    }
  Qed.

  Lemma sorting1_shift_i_i_1_0 L c s s1 s' :
    sorting1 L c s ->
    wellscoped_ss L ->
    wellscoped_s (length L) s ->
    s' = shift_i_s 1 0 s ->
    sorting1 (s1 :: L) (shift_i_i 1 0 c) s'.
  Proof.
    intros; subst.
    eapply sorting1_shift_i_i_0 with (ls := [s1]); eauto.
  Qed.
  
  Lemma kinding1_unroll L K t cs k' :
    let k := KArrows (map fst cs) k' in
    kinding1 L (k :: K) t k ->
    Forall (fun p => sorting1 L (snd p) (SBaseSort (fst p))) cs ->
    wellscoped_ss L ->
    kinding1 L K (unroll k t cs) k'.
  Proof.
    simpl.
    unfold unroll.
    intros Ht Hcs HL.
    eapply kinding1_TApps; eauto.
    eapply kinding1_subst_t_t_0; eauto.
  Qed.
  
  Lemma typing1_kinding1 C e t i :
    typing1 C e t i ->
    let L := get_sctx C in
    let K := get_kctx C in
    let W := get_hctx C in
    let G := get_tctx C in
    wfsorts1 L ->
    wfhctx1 L K W ->
    Forall (kinding1_KType L K) G ->
    kinding1 L K t KType /\
    sorting1 L i STime.
  Proof.
    simpl.
    induct 1; unfold_all;
      intros HL HW HG;
      destruct C as (((L & K) & W) & G);
      simplify; try solve [eauto | edestruct IHtyping1; eauto | edestruct IHtyping1; eauto; split; eauto; econstructor; eauto].
    {
      (* Case Ty1Var *)
      eapply nth_error_Forall in HG; eauto.
      split; eauto; econstructor; eauto.
    }
    {
      (* Case Ty1App *)
      edestruct IHtyping1_1 as (Ht & ?); eauto.
      edestruct IHtyping1_2; eauto.
      invert Ht.
      split; eauto.
      repeat (econstructor; eauto).
    }
    {
      (* Case Ty1AppT *)
      edestruct IHtyping1 as (Ht & ?); eauto.
      invert Ht.
      split; eauto.
      eapply kinding1_subst_t_t_0; eauto using wfsorts1_wellscoped_ss.
    }
    {
      (* Case Ty1AbsT *)
      edestruct IHtyping1; eauto.
      {
        eapply fmap_forall_fmap_map_intro.
        eapply fmap_forall_impl; eauto.
        simpl; intros.
        intuition eauto using kinding1_shift_t_t_1_0.
      }
      {
        eapply Forall_map.
        eapply Forall_impl; eauto.
        intros.
        eapply kinding1_shift_t_t_1_0; eauto.
      }
      split; eauto.
      econstructor; eauto.
    }
    {
      (* Case Ty1AppI *)
      edestruct IHtyping1 as (Ht & ?); eauto.
      invert Ht.
      split; eauto.
      eapply kinding1_subst_i_t_0; eauto with db_la.
    }
    {
      (* Case Ty1AbsI *)
      edestruct IHtyping1; eauto.
      {
        eapply fmap_forall_fmap_map_intro.
        eapply fmap_forall_impl; eauto.
        simpl; intros.
        intuition eauto using kinding1_shift_i_t_1_0, sorting1_shift_i_i_1_0,  wfsorts1_wellscoped_ss.
      }
      {
        eapply Forall_map.
        eapply Forall_impl; eauto.
        intros.
        eapply kinding1_shift_i_t_1_0; eauto using wfsorts1_wellscoped_ss.
      }
      split; econstructor; eauto.
    }
    {
      (* Case Ty1UnFold *)
      edestruct IHtyping1 as (Ht & ?); eauto.
      eapply kinding1_TApps_invert in Ht.
      destruct Ht as [Ht ?].
      invert Ht.
      split; eauto.
      eapply kinding1_unroll; eauto using wfsorts1_wellscoped_ss.
    }
    {
      (* Case Ty1UnPack *)
      edestruct IHtyping1_1 as (Ht & ?); eauto.
      invert Ht.
      edestruct IHtyping1_2 as (Ht2 & ?); eauto.
      {
        eapply fmap_forall_fmap_map_intro.
        eapply fmap_forall_impl; eauto.
        simpl; intros.
        intuition eauto using kinding1_shift_t_t_1_0.
      }
      {
        econstructor; eauto.
        eapply Forall_map.
        eapply Forall_impl; eauto.
        intros.
        eapply kinding1_shift_t_t_1_0; eauto.
      }
      unfold shift0_t_t in *.
      eapply kinding1_shift_t_t_rev_1_0 in Ht2; eauto.
      split; eauto.
      econstructor; eauto.
    }
    {
      (* Case Ty1UnPackI *)
      edestruct IHtyping1_1 as (Ht & ?); eauto.
      invert Ht.
      edestruct IHtyping1_2 as (Ht2 & Hi2); eauto.
      {
        eapply fmap_forall_fmap_map_intro.
        eapply fmap_forall_impl; eauto.
        simpl; intros.
        intuition eauto using kinding1_shift_i_t_1_0, sorting1_shift_i_i_1_0,  wfsorts1_wellscoped_ss.
      }
      {
        econstructor; eauto.
        eapply Forall_map.
        eapply Forall_impl; eauto.
        intros.
        eapply kinding1_shift_i_t_1_0; eauto using wfsorts1_wellscoped_ss.
      }
      unfold shift0_i_i, shift0_i_t in *.
      eapply sorting1_shift_i_i_rev_SBaseSort_1_0 in Hi2; eauto with db_la.
      eapply kinding1_shift_i_t_rev_1_0 in Ht2; eauto with db_la.
      split; eauto.
      econstructor; eauto.
    }
    {
      (* Case Ty1Const *)
      destruct cn; simpl; split; repeat (econstructor; eauto).
    }
    {
      (* Case Ty1Pair *)
      edestruct IHtyping1_1; eauto.
      edestruct IHtyping1_2; eauto.
      split; econstructor; eauto.
    }
    {
      (* Case Ty1Proj *)
      edestruct IHtyping1 as (Ht & ?); eauto.
      invert Ht.
      destruct pr; split; eauto.
    }
    {
      (* Case Ty1Inj *)
      edestruct IHtyping1; eauto.
      destruct inj; simpl; split; eauto; econstructor; eauto.
    }
    {
      (* Case Ty1Case *)
      edestruct IHtyping1_1 as (Ht & ?); eauto.
      invert Ht.
      edestruct IHtyping1_2; eauto.
      edestruct IHtyping1_3; eauto.
      split; eauto; repeat (econstructor; eauto; simpl).
    }
    {
      (* Case Ty1New *)
      edestruct IHtyping1_1; eauto.
      edestruct IHtyping1_2 as (Ht & ?); eauto.
      invert Ht.
      split; eauto; repeat (econstructor; eauto; simpl).
    }
    {
      (* Case Ty1Read *)
      edestruct IHtyping1_1 as (Ht & ?); eauto.
      invert Ht.
      edestruct IHtyping1_2 as (Ht & ?); eauto.
      invert Ht.
      split; eauto; repeat (econstructor; eauto; simpl).
    }
    {
      (* Case Ty1Write *)
      edestruct IHtyping1_1 as (Ht & ?); eauto.
      invert Ht.
      edestruct IHtyping1_2 as (Ht & ?); eauto.
      invert Ht.
      edestruct IHtyping1_3; eauto.
      split; eauto; repeat (econstructor; eauto; simpl).
    }
    {
      (* Case Loc *)
      eapply HW in H.
      openhyp.
      split; eauto; repeat (econstructor; eauto; simpl).
    }
    {
      (* Case Ty1Prim *)
      edestruct IHtyping1_1; eauto.
      edestruct IHtyping1_2; eauto.
      split; eauto; repeat (econstructor; eauto).
    }
    {
      (* Case Ty1NatAdd *)
      edestruct IHtyping1_1 as (Ht & ?); eauto.
      invert Ht.
      edestruct IHtyping1_2 as (Ht & ?); eauto.
      invert Ht.
      split; eauto; repeat (econstructor; eauto).
    }
  Qed.

  Lemma Forall2_Forall_1 A1 A2 (f1 : _ -> _ -> Prop) (f2 : _ -> Prop)ls1 ls2 :
    (forall (a1 : A1) (a2 : A2), f1 a1 a2 -> f2 a1) ->
    Forall2 f1 ls1 ls2 ->
    Forall f2 ls1.
  Proof.
    induct ls1; destruct ls2; simpl; intros Hf H1; invert H1; eauto.
  Qed.

  Lemma tyeq1_shift_t_t_1_0 L K t t' k k1 :
    tyeq1 L K t t' k ->
    tyeq1 L (k1 :: K) (shift_t_t 1 0 t) (shift_t_t 1 0 t') k.
  Proof.
    intros H; eapply tyeq1_shift_t_t with (x := 0) (ls := [k1]) in H; simpl in *; eauto.
  Qed.
  
  Lemma tctx_tyeq' C e t i :
    typing1 C e t i ->
    let L := get_sctx C in
    let K := get_kctx C in
    let W := get_hctx C in
    let G := get_tctx C in
    wfsorts1 L ->
    wfhctx1 L K W ->
    forall G',
      Forall2 (fun t t' => tyeq1 L K t t' KType /\ kinding1 L K t KType /\ kinding1 L K t' KType) G G' ->
      typing1 (L, K, W, G') e t i.
  Proof.
    simpl.
    induct 1; unfold_all;
      intros HL HW G' Htyeq;
      destruct C as (((L & K) & W) & G);
      simpl in *.
      (* try solve [ *)
      (*       econstructor; simpl; eauto 7 using kinding1_bkinding *)
      (*     ]. *)
    (* try solve [econstructor; eauto]. *)
    {
      (* Case Ty1Var *)
      eapply nth_error_Forall2 in Htyeq; eauto.
      openhyp.
      eapply Ty1Ty1eq; simpl; eauto.
      econstructor; simplify; eauto.
    }
    {
      econstructor; eauto.
    }
    {
      econstructor; simpl; eauto 7 using kinding1_bkinding.
    }
    {
      econstructor; simpl; eauto using kinding1_bkinding.
    }
    {
      (* Case AbsT *)
      econstructor; simplify; eauto.
      eapply IHtyping1; eauto.
      {
        eapply fmap_forall_fmap_map_intro.
        eapply fmap_forall_impl; eauto.
        simpl; intros.
        intuition eauto using kinding1_shift_t_t_1_0.
      }
      eapply Forall2_map; eauto.
      simpl.
      intros c c' Htyeq2.
      openhyp.
      repeat try_split; eauto using kinding1_shift_t_t_1_0, tyeq1_shift_t_t_1_0.
    }
    {
      econstructor; simpl; eauto using kinding1_bkinding.
    }
    {
      (* Case AbsI *)
      econstructor; simplify; eauto.
      eapply IHtyping1; eauto.
      {
        eapply fmap_forall_fmap_map_intro.
        eapply fmap_forall_impl; eauto.
        simpl; intros.
        intuition eauto using kinding1_shift_i_t_1_0, sorting1_shift_i_i_1_0,  wfsorts1_wellscoped_ss.
      }
      eapply Forall2_map; eauto.
      simpl.
      intros c c' Htyeq2.
      openhyp.
      unfold shift0_i_t.
      repeat try_split; eauto using kinding1_shift_i_t_1_0, tyeq1_shift0_i_t, kinding1_wellscoped_t, wfsorts1_wellscoped_ss.
    }
    {
      econstructor; simpl; eauto 7 using kinding1_bkinding.
    }
    {
      econstructor; simpl; eauto using kinding1_bkinding.
    }
    {
      econstructor; simpl; eauto using kinding1_bkinding.
    }
    {
      econstructor; simpl; eauto using kinding1_bkinding.
    }
    {
      (* Case Unpack *)
      econstructor; simplify; eauto.
      eapply IHtyping1_2; eauto.
      {
        eapply fmap_forall_fmap_map_intro.
        eapply fmap_forall_impl; eauto.
        simpl; intros.
        intuition eauto using kinding1_shift_t_t_1_0.
      }
      assert (Forall (kinding1_KType L K) G).
      {
        eapply Forall2_Forall_1; eauto.
        simpl; intros.
        propositional.
      }
      econstructor; eauto with db_tyeq1.
      {
        eapply typing1_kinding1 in H; eauto; simpl; eauto.
        destruct H as [Ht ?].
        simpl in *.
        invert Ht.
        repeat try_split; eauto using kinding1_bkinding.
      }
      eapply Forall2_map; eauto.
      simpl.
      intros c c' Htyeq2.
      openhyp.
      repeat try_split; eauto using kinding1_shift_t_t_1_0, tyeq1_shift_t_t_1_0, kinding1_wellscoped_t, wfsorts1_wellscoped_ss.
    }
    {
      econstructor; simpl; eauto using kinding1_bkinding.
    }
    {
      (* Case UnpackI *)
      assert (Forall (kinding1_KType L K) G).
      {
        eapply Forall2_Forall_1; eauto.
        simpl; intros.
        propositional.
      }
      copy H Ht.
      eapply typing1_kinding1 in Ht; eauto; simpl; eauto.
      destruct Ht as [Ht ?].
      simpl in *.
      invert Ht.
      econstructor; simplify; eauto.
      eapply IHtyping1_2; eauto.
      {
        eapply fmap_forall_fmap_map_intro.
        eapply fmap_forall_impl; eauto.
        simpl; intros.
        intuition eauto using kinding1_shift_i_t_1_0, sorting1_shift_i_i_1_0,  wfsorts1_wellscoped_ss.
      }
      econstructor; eauto using kinding1_bkinding with db_tyeq1.
      eapply Forall2_map; eauto.
      simpl.
      intros c c' Htyeq2.
      openhyp.
      repeat try_split; eauto using kinding1_shift_i_t_1_0, tyeq1_shift0_i_t, kinding1_wellscoped_t, wfsorts1_wellscoped_ss.
    }
    {
      econstructor; simpl; eauto using kinding1_bkinding.
    }
    {
      econstructor; simpl; eauto using kinding1_bkinding.
    }
    {
      econstructor; simpl; eauto using kinding1_bkinding.
    }
    {
      econstructor; simpl; eauto using kinding1_bkinding.
    }
    {
      (* Case ECase *)
      assert (Forall (kinding1_KType L K) G).
      {
        eapply Forall2_Forall_1; eauto.
        simpl; intros.
        propositional.
      }
      copy H Ht.
      eapply typing1_kinding1 in Ht; eauto; simpl; eauto.
      destruct Ht as [Ht ?].
      simpl in *.
      invert Ht.
      copy H0 Ht.
      eapply typing1_kinding1 in Ht; eauto; simpl; eauto.
      destruct Ht as [Ht ?].
      simpl in *.
      econstructor; eauto 7 using kinding1_bkinding with db_tyeq1; simpl.
    }
    {
      econstructor; simpl; eauto using kinding1_bkinding.
    }
    {
      econstructor; simpl; eauto using kinding1_bkinding.
    }
    {
      econstructor; simpl; eauto using kinding1_bkinding.
    }
    {
      econstructor; simpl; eauto using kinding1_bkinding.
    }
    {
      econstructor; simpl; eauto using kinding1_bkinding.
    }
    {
      econstructor; simpl; eauto using kinding1_bkinding.
    }
    {
      econstructor; simpl; eauto using kinding1_bkinding.
    }
    {
      eapply Ty1Le; eauto using kinding1_bkinding.
    }
  Qed.

  Lemma Forall1_Forall2_Forall2 A1 A2 (f1 : _ -> Prop) (f2 : _ -> _ -> Prop) (f3 : _ -> _ -> Prop) ls1 ls2 :
    (forall (a1 : A1) (a2 : A2), f1 a1 -> f2 a1 a2 -> f3 a1 a2) ->
    Forall f1 ls1 ->
    Forall2 f2 ls1 ls2 ->
    Forall2 f3 ls1 ls2.
  Proof.
    induct ls1; destruct ls2; simpl; intros Hf H1 H2; invert H1; invert H2; eauto.
  Qed.

  Lemma tctx_tyeq L K W G e t i :
    let C := (L, K, W, G) in
    typing1 C e t i ->
    wfctx1 C ->
    forall G',
      Forall2 (fun t t' => tyeq1 L K t t' KType /\ kinding1 L K t' KType) G G' ->
      typing1 (L, K, W, G') e t i.
  Proof.
    intros C Ht (HL & HW & HG) G' HGG'.
    eapply tctx_tyeq' with (C := C); eauto.
    eapply Forall1_Forall2_Forall2; eauto.
    simpl; intros.
    openhyp; eauto.
  Qed.
  
  Lemma Forall2_refl' A (P : A -> A -> Prop) ls :
    (forall a, P a a) ->
    Forall2 P ls ls.
  Proof.
    induct ls; simplify; eauto.
  Qed.
  
  Lemma Forall2_dedup A1 (p : A1 -> A1 -> Prop) ls1 :
    Forall (fun a1 => p a1 a1) ls1 ->
    Forall2 p ls1 ls1.
  Proof.
    induct ls1; simpl; intros H; invert H; eauto.
  Qed.

  Lemma wfctx1_add_typing1 L K W G t:
    wfctx1 (L, K, W, G) ->
    kinding1 L K t KType ->
    wfctx1 (L, K, W, t :: G).
  Proof.
    intros HC Ht; unfold wfctx1 in *; openhyp; simpl in *; repeat try_split; eauto.
  Qed.
  
  Lemma add_typing_ctx_tyeq1 t1 t2 L K W G e t i :
    let C := (L, K, W, G) in
    typing1 (add_typing_ctx t1 C) e t i ->
    tyeq1 L K t1 t2 KType ->
    kinding1 L K t1 KType ->
    kinding1 L K t2 KType ->
    wfctx1 C ->
    typing1 (add_typing_ctx t2 C) e t i.
  Proof.
    simpl.
    intros Hty Htyeq Ht1 Ht2 HC.
    eapply tctx_tyeq in Hty; eauto using wfctx1_add_typing1; simpl in *.
    econstructor; eauto.
    eapply Forall2_dedup.
    unfold wfctx1 in *; openhyp.
    eapply Forall_impl; eauto.
    simpl; intros; eauto using kinding1_bkinding with db_tyeq1.
  Qed.
  
  Lemma value_shift_e_e e :
    value e ->
    forall n x,
      value (shift_e_e n x e).
  Proof.
    induct 1; simplify; econstructor; eauto.
  Qed.
  
  Lemma value_shift_i_e e :
    value e ->
    forall n x,
      value (shift_i_e n x e).
  Proof.
    induct 1; simplify; econstructor; eauto.
  Qed.
  
  Lemma value_shift_t_e e :
    value e ->
    forall n x,
      value (shift_t_e n x e).
  Proof.
    induct 1; simplify; econstructor; eauto.
  Qed.

  Lemma typing_kinding L K W G e t i :
    let C := (L, K, W, G) in
    typing1 C e t i ->
    wfctx1 C ->
    kinding1 L K t KType /\
    sorting1 L i STime.
  Proof.
    intros C Ht HC.
    unfold wfctx1 in *.
    openhyp.
    eapply typing1_kinding1 with (C := C); eauto.
  Qed.
  
  Lemma shift_i_t_unroll n x k t args :
    shift_i_t n x (unroll k t args) = unroll k (shift_i_t n x t) (map (map_snd (shift_i_i n x)) args).
  Proof.
    unfold unroll; simpl.
    unfold subst0_t_t.
    rewrite shift_i_t_TApps.
    simpl.
    rewrite shift_i_t_subst_t_t.
    eauto.
  Qed.
  
  Lemma fst_map_snd A B C (f : B -> C) (p : A * B) : fst (map_snd f p) = fst p.
  Proof.
    eauto.
  Qed.

  Lemma shift_i_t_proj n x t1 t2 pr : shift_i_t n x (proj (t1, t2) pr) = proj (shift_i_t n x t1, shift_i_t n x t2) pr.
  Proof.
    destruct pr; simpl; eauto.
  Qed.
  
  Lemma shift_i_t_choose n x t1 t2 inj : shift_i_t n x (choose (t1, t2) inj) = choose (shift_i_t n x t1, shift_i_t n x t2) inj.
  Proof.
    destruct inj; simpl; eauto.
  Qed.

  Lemma typing1_shift_i_e C e t i :
    typing1 C e t i ->
    forall x ls,
      let n := length ls in
      let L := get_sctx C in
      let K := get_kctx C in
      let W := get_hctx C in
      let G := get_tctx C in
      x <= length L ->
      wellscoped_ss L ->
      fmap_forall (wellscoped_ti (length L)) W ->
      Forall (wellscoped_t (length L)) G ->
      typing1 (shift_i_ss n (firstn x L) ++ ls ++ my_skipn L x, K, fmap_map (shift_i_ti n x) W, map (shift_i_t n x) G) (shift_i_e n x e) (shift_i_t n x t) (shift_i_i n x i).
  Proof.
    simpl.
    induct 1; simpl; 
      try rename x into x';
      try rename L into L';
      try rename K into K';
      intros x ls Hle HL HW HG;
      destruct C as (((L & K) & W) & G);
      simplify;
      cbn in *.
      (* try solve [econstructor; eauto using kinding1_shift_i_t, sorting1_shift_i_i, kinding1_wellscoped_t]. *)
    {
      (* Case Ty1Var *)
      econstructor.
      eauto using map_nth_error.
    }
    {
      econstructor; eauto using kinding1_shift_i_t, sorting1_shift_i_i, kinding1_wellscoped_t.
    }
    {
      econstructor; eauto using kinding1_shift_i_t, sorting1_shift_i_i, kinding1_wellscoped_t.
    }
    {
      (* Case Ty1AppT *)
      unfold subst0_t_t.
      rewrite shift_i_t_subst_t_t.
      econstructor; eauto using kinding1_shift_i_t.
    }
    Lemma shift_i_ti_shift_t_ti :
      forall b x2 n2 x1 n1,
        shift_i_ti x2 n2 (shift_t_ti x1 n1 b) = shift_t_ti x1 n1 (shift_i_ti x2 n2 b).
    Proof.
      unfold shift_i_ti, shift_t_ti; intros.
      simpl.
      rewrite shift_i_t_shift_t_t.
      eauto.
    Qed.
    
    {
      (* Case AbsT *)
      econstructor; eauto using value_shift_i_e; simpl.
      unfold shift0_t_t in *.
      specialize (IHtyping1 x ls).
      repeat rewrite fmap_map_fmap_map in *.
      repeat rewrite map_map in *.
      setoid_rewrite <- shift_i_t_shift_t_t.
      setoid_rewrite <- shift_i_ti_shift_t_ti.
      eapply IHtyping1; eauto.
      {
        eapply fmap_forall_fmap_map_intro.
        eapply fmap_forall_impl; eauto.
        simpl; intros.
        intuition eauto using wellscoped_shift_t_t.
      }
      {
        eapply Forall_map.
        eapply Forall_impl; eauto.
        intros.
        eapply wellscoped_shift_t_t; eauto.
      }
    }
    {
      (* Case Ty1AppI *)
      unfold subst0_i_t.
      rewrite shift_i_t_subst_out by la.
      econstructor; eauto using kinding1_shift_i_t.
      eapply sorting1_shift_i_i; eauto.
      eapply typing1_wellscoped_t in H; simpl; eauto.
      destruct H as [H ?].
      invert H; eauto.
    }
    {
      (* Case Ty1AbsI *)
      econstructor; eauto using value_shift_i_e, wfsort1_shift_i_s''.
      specialize (IHtyping1 (S x) ls).
      simpl in *.
      unfold shift0_i_t in *.
      repeat rewrite fmap_map_fmap_map in *.
      repeat rewrite map_map in *.
      unfold shift0_i_ti, shift_i_ti, shift0_t_ti, shift_t_ti in *.
      simpl in *.
      setoid_rewrite shift_i_t_shift_cut_2 in IHtyping1; eauto with db_la.
    Lemma shift_i_i_shift_cut_setoid n1 n2 x y :
      x + n1 <= y ->
      forall b,
        shift_i_i n2 y (shift_i_i n1 x b) = shift_i_i n1 x (shift_i_i n2 (y - n1) b).
    Proof.
      intros; eapply shift_i_i_shift_cut; eauto.
    Qed.
    
      setoid_rewrite shift_i_i_shift_cut_setoid in IHtyping1; eauto with db_la.
      simpl in *.
      rewrite Nat.sub_0_r in *.
      rewrite length_firstn_le in * by la.
      eapply IHtyping1; eauto using wfsort1_wellscoped_s' with db_la.
      {
        eapply fmap_forall_fmap_map_intro.
        eapply fmap_forall_impl; eauto.
        simpl; intros.
        intuition eauto using wellscoped_shift_i_t, wellscoped_shift_i_i.
      }
      {
        eapply Forall_map.
        eapply Forall_impl; eauto.
        intros.
        eapply wellscoped_shift_i_t; eauto.
      }
    }
    {
      (* Case Ty1Rec *)
      unfold_all.
      specialize (IHtyping1 x ls).
      rewrite shift_i_e_AbsTIs in *.
      simpl in *.
      econstructor; eauto using kinding1_shift_i_t.
      simpl.
      eapply IHtyping1; eauto using kinding1_wellscoped_t.
    }
    {
      (* Case Ty1Fold *)
      unfold_all.
      specialize (IHtyping1 x ls).
      rewrite shift_i_t_TApps in *.
      rewrite shift_i_t_unroll in *.
      simpl in *.
      econstructor; eauto using kinding1_shift_i_t.
      simpl.
      eapply kinding1_TApps_invert in H.
      destruct H as [Ht ?].
      invert Ht.
      eapply kinding1_TApps; eauto using kinding1_shift_i_t.
      {
        rewrite map_map.
        simpl.
        eauto using kinding1_shift_i_t.
      }
      eapply Forall_map.
      simpl.
      eapply Forall_impl; eauto.
      simpl; intros.
      eauto using sorting1_shift_i_i''.
    }
    {
      (* Case Ty1Unfold *)
      specialize (IHtyping1 x ls).
      rewrite shift_i_t_TApps in *.
      rewrite shift_i_t_unroll in *.
      simpl in *.
      econstructor; eauto using kinding1_shift_i_t.
    }
    {
      (* Case Ty1Pack *)
      invert H.
      econstructor; eauto using kinding1_shift_i_t; simpl.
      {
        econstructor; eauto using kinding1_shift_i_t; simpl.
      }
      unfold subst0_t_t in *.
      rewrite <- shift_i_t_subst_t_t in *.
      eauto.
    }
    {
      (* Case Ty1Unpack *)
      econstructor; eauto.
      simpl.
      unfold shift0_t_t in *.
      specialize (IHtyping1_2 x ls).
      rewrite fmap_map_fmap_map in *.
      rewrite map_map in *.
      unfold shift0_i_ti, shift_i_ti, shift0_t_ti, shift_t_ti in *.
      simpl in *.
      setoid_rewrite <- shift_i_t_shift_t_t.
      eapply typing1_wellscoped_t in H; simpl; eauto.
      destruct H as [Ht ?].
      invert Ht; eauto.
      eapply IHtyping1_2; eauto with db_la.
      {
        eapply fmap_forall_fmap_map_intro.
        eapply fmap_forall_impl; eauto.
        simpl; intros.
        intuition eauto using wellscoped_shift_t_t.
      }
      {
        econstructor; eauto.
        eapply Forall_map.
        eapply Forall_impl; eauto.
        intros.
        eapply wellscoped_shift_t_t; eauto.
      }
    }
    {
      (* Case Ty1PackI *)
      invert H.
      econstructor; eauto using kinding1_shift_i_t, sorting1_shift_i_i, wfsort1_wellscoped_s' with db_la; simpl.
      {
        econstructor; eauto using wfsort1_shift_i_s''; simpl.
        eapply kinding1_shift_i_t with (x := S x) (ls := ls) in H8; simpl; eauto using wfsort1_wellscoped_s' with db_la.
        simpl in *.
        rewrite length_firstn_le in * by la.
        eauto.
      }
      unfold subst0_i_t in *.
      rewrite <- shift_i_t_subst_out by la.
      eauto.
    }
    {
      (* Case Ty1Unpack *)
      econstructor; eauto.
      simpl.
      unfold shift0_i_t, shift0_i_i in *.
      specialize (IHtyping1_2 (S x) ls).
      rewrite fmap_map_fmap_map in *.
      rewrite map_map in *.
      unfold shift0_i_ti, shift_i_ti, shift0_t_ti, shift_t_ti in *.
      simpl in *.
      setoid_rewrite shift_i_t_shift_cut_2 in IHtyping1_2; eauto with db_la.
      setoid_rewrite shift_i_i_shift_cut_setoid in IHtyping1_2; eauto with db_la.
      simpl in *.
      rewrite Nat.sub_0_r in *.
      rewrite length_firstn_le in * by la.
      eapply typing1_wellscoped_t in H; simpl; eauto.
      destruct H as [Ht ?].
      invert Ht; eauto.
      eapply IHtyping1_2;
        eauto using wfsort1_wellscoped_s' with db_la.
      {
        eapply fmap_forall_fmap_map_intro.
        eapply fmap_forall_impl; eauto.
        simpl; intros.
        intuition eauto using wellscoped_shift_i_t, wellscoped_shift_i_i.
      }
      {
        econstructor; eauto.
        eapply Forall_map.
        eapply Forall_impl; eauto.
        intros.
        eapply wellscoped_shift_i_t; eauto.
      }
    }
    {
      (* Case Ty1Const *)
      destruct cn; simpl; econstructor; eauto.
    }
    {
      econstructor; eauto using kinding1_shift_i_t, sorting1_shift_i_i, kinding1_wellscoped_t.
    }
    {
      (* Case Ty1Proj *)
      rewrite shift_i_t_proj.
      econstructor; eauto.
    }
    {
      (* Case Ty1Inj *)
      rewrite shift_i_t_choose.
      simpl.
      econstructor; eauto using kinding1_shift_i_t.
    }
    {
      (* Case Ty1Case *)
      eapply typing1_wellscoped_t in H; simpl; eauto.
      destruct H as [Ht ?].
      invert Ht.
      econstructor; eauto using kinding1_shift_i_t.
    }
    {
      econstructor; eauto using kinding1_shift_i_t, sorting1_shift_i_i, kinding1_wellscoped_t.
    }
    {
      (* Case Read *)
      econstructor; simpl; eauto using kinding1_shift_i_t, sorting1_shift_i_i, kinding1_wellscoped_t, wfprop1_shift_i_p'.
      eapply interp_prop_shift_i_p in H1; simpl in *; eauto.
      eapply typing1_wellscoped_t in H; simpl; eauto.
      destruct H as [Ht ?].
      invert Ht; eauto.
      eapply typing1_wellscoped_t in H0; simpl; eauto.
      destruct H0 as [Ht ?].
      invert Ht; eauto.
      simpl in *.
      econstructor; eauto using sorting1_wellscoped_i.
    }
    {
      (* Case Write *)
      econstructor; simpl; eauto using kinding1_shift_i_t, sorting1_shift_i_i, kinding1_wellscoped_t, wfprop1_shift_i_p'.
      eapply interp_prop_shift_i_p in H1; simpl in *; eauto.
      eapply typing1_wellscoped_t in H; simpl; eauto.
      destruct H as [Ht ?].
      invert Ht; eauto.
      eapply typing1_wellscoped_t in H0; simpl; eauto.
      destruct H0 as [Ht ?].
      invert Ht; eauto.
      simpl in *.
      econstructor; eauto using sorting1_wellscoped_i.
    }
    {
      (* Case Ty1Loc *)
      econstructor; simpl.
      erewrite fmap_map_lookup; eauto.
      eauto.
    }
    {
      Lemma Ty1Prim' C opr e1 e2 i1 i2 t1 t2 t :
        typing1 C e1 t1 i1 ->
        typing1 C e2 t2 i2 ->
        t1 = prim_arg1_type opr ->
        t2 = prim_arg2_type opr ->
        t = prim_result_type opr ->
        typing1 C (EPrim opr e1 e2) t (i1 + i2 + Tconst (prim_cost opr))%idx.
      Proof.
        intros; subst; econstructor; eauto.
      Qed.

      eapply Ty1Prim'; simpl; eauto using kinding1_shift_i_t, sorting1_shift_i_i, kinding1_wellscoped_t;
        destruct opr; simpl; eauto.
    }
    {
      econstructor; eauto using kinding1_shift_i_t, sorting1_shift_i_i, kinding1_wellscoped_t.
    }
    {
      (* Case Ty1Ty1eq *)
      unfold_all.
      eapply Ty1Ty1eq; eauto using kinding1_shift_i_t; simpl.
      eapply tyeq1_shift_i_t; eauto using kinding1_wellscoped_t.
      eapply typing1_wellscoped_t in H; simpl; eauto.
      destruct H as [Ht ?].
      invert Ht; eauto.
    }
    {
      (* Case Ty1Le *)
      unfold_all.
      eapply Ty1Le; eauto using sorting1_shift_i_i''; simpl.
      {
        eapply sorting1_shift_i_i''; eauto.
      }
      eapply interp_prop_shift_i_p in H1; simpl in *; eauto.
      econstructor; eauto using sorting1_wellscoped_i.
      eapply typing1_wellscoped_t in H; simpl; eauto.
      destruct H as [Ht ?].
      invert Ht; eauto.
    }
  Qed.

  Definition wellscoped_ctx C :=
    let L := get_sctx C in
    let K := get_kctx C in
    let W := get_hctx C in
    let G := get_tctx C in
    wellscoped_ss L /\
    fmap_forall (wellscoped_ti (length L)) W /\
    Forall (wellscoped_t (length L)) G.
    
  Lemma typing1_shift_i_e_2 L K W G e t i :
    let C := (L, K, W, G) in
    typing1 C e t i ->
    forall x ls,
      let n := length ls in
      x <= length L ->
      wellscoped_ctx C ->
      typing1 (shift_i_ss n (firstn x L) ++ ls ++ my_skipn L x, K, fmap_map (shift_i_ti n x) W, map (shift_i_t n x) G) (shift_i_e n x e) (shift_i_t n x t) (shift_i_i n x i).
  Proof.
    intros; unfold wellscoped_ctx in *; openhyp; eapply typing1_shift_i_e with (C := C); eauto.
  Qed.
  
  Lemma typing1_shift0_i_e L K W G e t i s :
    let C := (L, K, W, G) in 
    typing1 C e t i ->
    wellscoped_ctx C ->
    typing1 (s :: L, K, fmap_map shift0_i_ti W, map shift0_i_t G) (shift0_i_e e) (shift0_i_t t) (shift0_i_i i).
  Proof.
    intros C Hty HC.
    eapply typing1_shift_i_e_2 with (x := 0) (ls := [s]) in Hty; simplify; eauto with db_la.
    repeat rewrite my_skipn_0 in *.
    eauto.
  Qed.

  Lemma typing1_shift_t_e C e t i :
    typing1 C e t i ->
    forall x ls,
      let n := length ls in
      let L := get_sctx C in
      let K := get_kctx C in
      let W := get_hctx C in
      let G := get_tctx C in
      x <= length K ->
      (* wellscoped_ss L -> *)
      (* fmap_forall (wellscoped_t (length L)) W -> *)
      (* Forall (wellscoped_t (length L)) G -> *)
      typing1 (L, insert ls x K, fmap_map (shift_t_ti n x) W, map (shift_t_t n x) G) (shift_t_e n x e) (shift_t_t n x t) i.
  Proof.
    simpl.
    induct 1; simpl; 
      try rename x into x';
      try rename L into L';
      try rename K into K';
      intros x ls Hle (* HL HW HG *);
      destruct C as (((L & K) & W) & G);
      simpl in *;
      cbn in *.
      (* try solve [econstructor; eauto using kinding1_shift_t_t, kinding1_wellscoped_t]. *)
    {
      (* Case Ty1Var *)
      econstructor.
      eauto using map_nth_error.
    }
    {
      econstructor; eauto using kinding1_shift_t_t, kinding1_wellscoped_t.
    }
    {
      econstructor; eauto using kinding1_shift_t_t, kinding1_wellscoped_t.
    }
    {
      (* Case Ty1AppT *)
      unfold subst0_t_t.
      rewrite shift_t_t_subst_out by la.
      econstructor; eauto using kinding1_shift_t_t.
    }
    {
      (* Case AbsT *)
      econstructor; eauto using value_shift_t_e; simpl.
      unfold shift0_t_t in *.
      specialize (IHtyping1 (S x) ls).
      repeat rewrite fmap_map_fmap_map in *.
      repeat rewrite map_map in *.
      unfold shift0_i_ti, shift_i_ti, shift0_t_ti, shift_t_ti in *.
      simpl in *.
      setoid_rewrite shift_t_t_shift_cut_setoid in IHtyping1; eauto with db_la.
      simpl in *.
      rewrite Nat.sub_0_r in *.
      eapply IHtyping1; eauto with db_la.
    }
    {
      (* Case Ty1AppI *)
      unfold subst0_i_t.
      rewrite shift_t_t_subst_i_t.
      econstructor; eauto using kinding1_shift_t_t.
    }
    {
      (* Case Ty1AbsI *)
      econstructor; eauto using value_shift_t_e.
      specialize (IHtyping1 x ls).
      simpl in *.
      unfold shift0_i_t in *.
      repeat rewrite fmap_map_fmap_map in *.
      repeat rewrite map_map in *.
      unfold shift0_i_ti, shift_i_ti, shift0_t_ti, shift_t_ti in *.
      simpl in *.
      setoid_rewrite shift_i_t_shift_t_t.
      eapply IHtyping1; eauto with db_la.
    }
    {
      (* Case Ty1Rec *)
      unfold_all.
      specialize (IHtyping1 x ls).
      rewrite shift_t_e_AbsTIs in *.
      simpl in *.
      econstructor; eauto using kinding1_shift_t_t.
    }
    {
      (* Case Ty1Fold *)
      unfold_all.
      specialize (IHtyping1 x ls).
  Lemma shift_t_t_unroll n x k t args :
    shift_t_t n x (unroll k t args) = unroll k (shift_t_t n (1 + x) t) args.
  Proof.
    unfold unroll; simpl.
    unfold subst0_t_t.
    rewrite shift_t_t_TApps.
    rewrite shift_t_t_subst_out by la.
    eauto.
  Qed.
  
      rewrite shift_t_t_TApps in *.
      rewrite shift_t_t_unroll in *.
      simpl in *.
      eapply kinding1_TApps_invert in H.
      destruct H as [Ht ?].
      invert Ht.
      econstructor; eauto using kinding1_shift_t_t.
      simpl.
      eapply kinding1_TApps; eauto using kinding1_shift_t_t.
      econstructor.
      eapply kinding1_shift_t_t with (x := S x) (K := _ :: _); simpl; eauto with db_la.
    }
    {
      (* Case Ty1Unfold *)
      specialize (IHtyping1 x ls).
      rewrite shift_t_t_TApps in *.
      rewrite shift_t_t_unroll in *.
      simpl in *.
      econstructor; eauto using kinding1_shift_t_t.
    }
    {
      (* Case Ty1Pack *)
      invert H.
      econstructor; eauto using kinding1_shift_t_t; simpl.
      {
        econstructor; eauto using kinding1_shift_t_t; simpl.
        eapply kinding1_shift_t_t with (x := S x) (K := _ :: _); simpl; eauto with db_la.
      }
      unfold subst0_t_t in *.
      rewrite <- shift_t_t_subst_out by la.
      eauto.
    }
    {
      (* Case Ty1Unpack *)
      econstructor; eauto.
      simpl.
      unfold shift0_t_t in *.
      specialize (IHtyping1_2 (S x) ls).
      rewrite fmap_map_fmap_map in *.
      rewrite map_map in *.
      unfold shift0_i_ti, shift_i_ti, shift0_t_ti, shift_t_ti in *.
      simpl in *.
      setoid_rewrite shift_t_t_shift_cut_setoid in IHtyping1_2; eauto with db_la.
      simpl in *.
      rewrite Nat.sub_0_r in *.
      eapply IHtyping1_2; eauto with db_la.
    }
    {
      (* Case Ty1PackI *)
      invert H.
      econstructor; simpl; eauto using kinding1_shift_t_t; simpl.
      {
        econstructor; eauto using kinding1_shift_t_t.
      }
      unfold subst0_i_t in *.
      specialize (IHtyping1 x ls).
      rewrite shift_t_t_subst_i_t in *.
      eauto.
    }
    {
      (* Case Ty1Unpack *)
      econstructor; eauto.
      simpl.
      unfold shift0_i_t, shift0_i_i in *.
      specialize (IHtyping1_2 x ls).
      rewrite fmap_map_fmap_map in *.
      rewrite map_map in *.
      unfold shift0_i_ti, shift_i_ti, shift0_t_ti, shift_t_ti in *.
      simpl in *.
      setoid_rewrite shift_i_t_shift_t_t.
      eapply IHtyping1_2; eauto with db_la.
    }
    {
      (* Case Ty1Const *)
      destruct cn; simpl; econstructor; eauto.
    }
    {
      econstructor; eauto using kinding1_shift_t_t, kinding1_wellscoped_t.
    }
    {
      (* Case Ty1Proj *)
  Lemma shift_t_t_proj n x t1 t2 pr : shift_t_t n x (proj (t1, t2) pr) = proj (shift_t_t n x t1, shift_t_t n x t2) pr.
  Proof.
    destruct pr; simpl; eauto.
  Qed.
  
  Lemma shift_t_t_choose n x t1 t2 inj : shift_t_t n x (choose (t1, t2) inj) = choose (shift_t_t n x t1, shift_t_t n x t2) inj.
  Proof.
    destruct inj; simpl; eauto.
  Qed.
  
      rewrite shift_t_t_proj.
      econstructor; eauto.
    }
    {
      (* Case Ty1Inj *)
      rewrite shift_t_t_choose.
      simpl.
      econstructor; eauto using kinding1_shift_t_t.
    }
    {
      econstructor; eauto using kinding1_shift_t_t, kinding1_wellscoped_t.
    }
    {
      econstructor; eauto using kinding1_shift_t_t, kinding1_wellscoped_t.
    }
    {
      econstructor; eauto using kinding1_shift_t_t, kinding1_wellscoped_t.
    }
    {
      econstructor; eauto using kinding1_shift_t_t, kinding1_wellscoped_t.
    }
    {
      (* Case Ty1Loc *)
      econstructor; simpl.
      erewrite fmap_map_lookup; simpl; eauto.
      eauto.
    }
    {
      (* Case Ty1Prim *)
      eapply Ty1Prim'; simpl; eauto using kinding1_shift_i_t, sorting1_shift_i_i, kinding1_wellscoped_t;
        destruct opr; simpl; eauto.
    }
    {
      econstructor; eauto using kinding1_shift_t_t, kinding1_wellscoped_t.
    }
    {
      (* Case Ty1Ty1eq *)
      unfold_all.
      eapply Ty1Ty1eq; eauto using kinding1_shift_t_t; simpl.
      eapply tyeq1_shift_t_t; eauto.
    }
    {
      eapply Ty1Le; eauto using kinding1_shift_t_t, kinding1_wellscoped_t.
    }
  Qed.

  Lemma typing1_shift0_t_e L K W G e t i k :
    let C := (L, K, W, G) in 
    typing1 C e t i ->
    typing1 (L, k :: K, fmap_map shift0_t_ti W, map shift0_t_t G) (shift0_t_e e) (shift0_t_t t) i.
  Proof.
    intros C Hty.
    eapply typing1_shift_t_e with (x := 0) (ls := [k]) in Hty; simplify; eauto with db_la.
  Qed.

  Lemma typing1_subst_i_e C e t i :
    typing1 C e t i ->
    let L := get_sctx C in
    let K := get_kctx C in
    let W := get_hctx C in
    let G := get_tctx C in
    forall x v s,
      nth_error L x = Some s ->
      sorting1 (my_skipn L (1 + x)) v s ->
      wfsorts1 L ->
      wfhctx1 L K W ->
      Forall (kinding1_KType L K) G ->
      typing1 (subst_i_ss v (firstn x L) ++ my_skipn L (1 + x), K, fmap_map (subst_i_ti x (shift_i_i x 0 v)) W, map (subst_i_t x (shift_i_i x 0 v)) G) (subst_i_e x (shift_i_i x 0 v) e) (subst_i_t x (shift_i_i x 0 v) t) (subst_i_i x (shift_i_i x 0 v) i).
  Proof.
    simpl.
    induct 1; simpl; 
      try rename x into x';
      try rename L into L';
      try rename K into K';
      try rename s into s';
      destruct C as (((L & K) & W) & G);
      intros x v s Hx Hv HL HW HG;
      simpl in *;
      cbn in *.
      (* try solve [econstructor; simpl; eauto using kinding1_subst_i_t, sorting1_subst_i_i]. *)
    {
      (* Case Ty1Var *)
      econstructor.
      eauto using map_nth_error.
    }
    {
      econstructor; simpl; eauto using kinding1_subst_i_t, sorting1_subst_i_i.
    }
    {
      econstructor; simpl; eauto using kinding1_subst_i_t, sorting1_subst_i_i.
    }
    {
      (* Case Ty1AppT *)
      unfold subst0_t_t.
      rewrite subst_i_t_subst_t_t.
      econstructor; simpl; eauto using kinding1_subst_i_t.
    }
    {
      (* Case Ty1AbsT *)
      econstructor; eauto using value_subst_i_e; simpl.
      unfold shift0_t_t in *.
      specialize (IHtyping1 x v s).
      repeat rewrite fmap_map_fmap_map in *.
      repeat rewrite map_map in *.
      unfold shift0_i_ti, shift_i_ti, shift0_t_ti, shift_t_ti in *.
      simpl in *.
      setoid_rewrite shift_t_t_subst_i_t.
      eapply IHtyping1; eauto.
      {
        eapply fmap_forall_fmap_map_intro.
        eapply fmap_forall_impl; eauto.
        simpl; intros.
        intuition eauto using kinding1_shift_t_t_1_0.
      }
      {
        eapply Forall_map.
        eapply Forall_impl; eauto.
        intros.
        eapply kinding1_shift_t_t_1_0; eauto.
      }
    }
    {
      (* Case Ty1AppI *)
      unfold subst0_i_t.
      rewrite subst_i_t_subst by la.
      econstructor; eauto using kinding1_subst_i_t.
      eapply sorting1_subst_i_i; eauto.
      eapply typing1_kinding1 in H; simpl; eauto.
      destruct H as [H ?].
      invert H.
      eauto.
    }
    {
      (* Case Ty1AbsI *)
      econstructor; simpl; eauto using value_subst_i_e, wfsort1_subst_i_s'.
      specialize (IHtyping1 (S x) v s).
      simpl in *.
      unfold shift0_i_t, shift0_i_i in *.
      repeat rewrite fmap_map_fmap_map in *.
      repeat rewrite map_map in *.
      unfold shift0_i_ti, shift_i_ti, shift0_t_ti, shift_t_ti, subst0_i_ti, subst_i_ti, subst0_t_ti, subst_t_ti in *.
      simpl in *.
      setoid_rewrite subst_i_t_shift_hit_setoid in IHtyping1; eauto with db_la.
    Lemma subst_i_i_shift_hit_setoid v n x y :
      x + n <= y ->
      forall b,
        subst_i_i y (shift_i_i y 0 v) (shift_i_i n x b) = shift_i_i n x (subst_i_i (y - n) (shift_i_i (y - n) 0 v) b).
    Proof.
      intros; eapply subst_i_i_shift_hit; eauto.
    Qed.
    
      setoid_rewrite subst_i_i_shift_hit_setoid in IHtyping1; eauto with db_la.
      simpl in *.
      rewrite Nat.sub_0_r in *.
      copy Hx Hcmp.
      eapply nth_error_Some_lt in Hcmp.
      rewrite length_firstn_le in * by la.
      rewrite shift_i_i_shift_merge by la.
      rewrite plus_comm.
      eapply IHtyping1; eauto with db_la.
      {
        eapply fmap_forall_fmap_map_intro.
        eapply fmap_forall_impl; eauto.
        simpl; intros.
        intuition eauto using kinding1_shift_i_t_1_0, sorting1_shift_i_i_1_0,  wfsorts1_wellscoped_ss.
      }
      {
        eapply Forall_map.
        eapply Forall_impl; eauto.
        intros.
        eapply kinding1_shift_i_t_1_0; eauto using wfsorts1_wellscoped_ss.
      }
    }
    {
      (* Case Ty1Rec *)
      unfold_all.
      specialize (IHtyping1 x v s).
      rewrite subst_i_e_AbsTIs in *.
      simpl in *.
      econstructor; simpl; eauto using kinding1_subst_i_t.
    }
    {
      (* Case Ty1Fold *)
      unfold_all.
      specialize (IHtyping1 x v s).
  Lemma subst_i_t_unroll x v k t args :
    subst_i_t x v (unroll k t args) = unroll k (subst_i_t x v t) (map (map_snd (subst_i_i x v)) args).
  Proof.
    unfold unroll; simpl.
    unfold subst0_t_t.
    rewrite subst_i_t_TApps.
    simpl.
    rewrite subst_i_t_subst_t_t.
    eauto.
  Qed.
  
      rewrite subst_i_t_TApps in *.
      rewrite subst_i_t_unroll in *.
      simpl in *.
      econstructor; simpl; eauto using kinding1_subst_i_t.
      eapply kinding1_TApps_invert in H.
      destruct H as [Ht ?].
      invert Ht.
      eapply kinding1_TApps; eauto using kinding1_subst_i_t.
      {
        rewrite map_map.
        simpl.
        econstructor; simpl; eauto using kinding1_subst_i_t.
      }
      eapply Forall_map.
      simpl.
      eapply Forall_impl; eauto.
      simpl; intros.
      eauto using sorting1_subst_i_i'.
    }
    {
      (* Case Ty1Unfold *)
      specialize (IHtyping1 x v s).
      rewrite subst_i_t_TApps in *.
      rewrite subst_i_t_unroll in *.
      simpl in *.
      econstructor; simpl; eauto using kinding1_subst_i_t.
    }
    {
      (* Case Ty1Pack *)
      invert H.
      econstructor; simpl; eauto using kinding1_subst_i_t; simpl.
      {
        econstructor; eauto using kinding1_subst_i_t; simpl.
      }
      unfold subst0_t_t in *.
      rewrite <- subst_i_t_subst_t_t in *.
      eauto.
    }
    {
      (* Case Ty1Unpack *)
      econstructor; eauto.
      simpl.
      unfold shift0_t_t in *.
      specialize (IHtyping1_2 x v s).
      rewrite fmap_map_fmap_map in *.
      rewrite map_map in *.
      unfold shift0_i_ti, shift_i_ti, shift0_t_ti, shift_t_ti, subst0_i_ti, subst_i_ti, subst0_t_ti, subst_t_ti in *.
      simpl in *.
      setoid_rewrite shift_t_t_subst_i_t.
      eapply typing1_kinding1 in H; simpl; eauto.
      destruct H as [Ht ?].
      invert Ht; eauto.
      eapply IHtyping1_2; eauto with db_la.
      {
        eapply fmap_forall_fmap_map_intro.
        eapply fmap_forall_impl; eauto.
        simpl; intros.
        intuition eauto using kinding1_shift_t_t_1_0.
      }
      {
        econstructor; eauto.
        eapply Forall_map.
        eapply Forall_impl; eauto.
        intros.
        eapply kinding1_shift_t_t_1_0; eauto using wfsorts1_wellscoped_ss.
      }
    }
    {
      (* Case Ty1PackI *)
      invert H.
      econstructor; simpl; eauto using kinding1_subst_i_t, sorting1_subst_i_i.
      {
        econstructor; eauto using wfsort1_subst_i_s'; simpl.
        eapply kinding1_subst_i_t with (x := S x) (L := _ :: _) in H8; simpl; eauto with db_la.
        simpl in *.
        copy Hx Hcmp.
        eapply nth_error_Some_lt in Hcmp.
        rewrite length_firstn_le in * by la.
        unfold shift0_i_i.
        rewrite shift_i_i_shift_merge by la.
        rewrite plus_comm.
        eauto.
      }
      unfold subst0_i_t in *.
      rewrite <- subst_i_t_subst by la.
      eauto.
    }
    {
      (* Case Ty1Unpack *)
      econstructor; eauto.
      simpl.
      unfold shift0_i_t, shift0_i_i in *.
      specialize (IHtyping1_2 (S x) v s).
      rewrite fmap_map_fmap_map in *.
      rewrite map_map in *.
      unfold shift0_i_ti, shift_i_ti, shift0_t_ti, shift_t_ti, subst0_i_ti, subst_i_ti, subst0_t_ti, subst_t_ti in *.
      simpl in *.
      setoid_rewrite subst_i_t_shift_hit_setoid in IHtyping1_2; eauto with db_la.
      setoid_rewrite subst_i_i_shift_hit_setoid in IHtyping1_2; eauto with db_la.
      simpl in *.
      rewrite Nat.sub_0_r in *.
      copy Hx Hcmp.
      eapply nth_error_Some_lt in Hcmp.
      rewrite length_firstn_le in * by la.
      eapply typing1_kinding1 in H; simpl; eauto.
      destruct H as [Ht ?].
      invert Ht; eauto.
      rewrite shift_i_i_shift_merge by la.
      rewrite plus_comm.
      eapply IHtyping1_2; eauto with db_la.
      {
        eapply fmap_forall_fmap_map_intro.
        eapply fmap_forall_impl; eauto.
        simpl; intros.
        intuition eauto using kinding1_shift_i_t_1_0, sorting1_shift_i_i_1_0,  wfsorts1_wellscoped_ss.
      }
      {
        econstructor; eauto.
        eapply Forall_map.
        eapply Forall_impl; eauto.
        intros.
        eapply kinding1_shift_i_t_1_0; eauto using wfsorts1_wellscoped_ss.
      }
    }
    {
      (* Case Ty1Const *)
      destruct cn; simpl; econstructor; eauto.
    }
    {
      econstructor; simpl; eauto using kinding1_subst_i_t, sorting1_subst_i_i.
    }
    {
      (* Case Ty1Proj *)
  Lemma subst_i_t_proj x v t1 t2 pr : subst_i_t x v (proj (t1, t2) pr) = proj (subst_i_t x v t1, subst_i_t x v t2) pr.
  Proof.
    destruct pr; simpl; eauto.
  Qed.
  
  Lemma subst_i_t_choose x v t1 t2 inj : subst_i_t x v (choose (t1, t2) inj) = choose (subst_i_t x v t1, subst_i_t x v t2) inj.
  Proof.
    destruct inj; simpl; eauto.
  Qed.
  
      rewrite subst_i_t_proj.
      econstructor; eauto.
    }
    {
      (* Case Ty1Inj *)
      rewrite subst_i_t_choose.
      simpl.
      econstructor; simpl; eauto using kinding1_subst_i_t.
    }
    {
      (* Case Ty1Case *)
      eapply typing1_kinding1 in H; simpl; eauto.
      destruct H as [Ht ?].
      invert Ht.
      econstructor; simpl; eauto using kinding1_subst_i_t.
    }
    {
      econstructor; simpl; eauto using kinding1_subst_i_t, sorting1_subst_i_i.
    }
    {
      (* Case Read *)
      econstructor; eauto using kinding1_shift_t_t, kinding1_wellscoped_t.
      simpl.
      eapply interp_subst_i_p in H1; simpl in *; eauto.
      eapply typing1_kinding1 in H; simpl in *; eauto.
      destruct H as [Ht ?].
      invert Ht.
      eapply typing1_kinding1 in H0; simpl in *; eauto.
      destruct H0 as [Ht ?].
      invert Ht.
      econstructor; eauto using sorting1_bsorting'.
    }
    {
      (* Case Write *)
      econstructor; eauto using kinding1_shift_t_t, kinding1_wellscoped_t.
      simpl.
      eapply interp_subst_i_p in H1; simpl in *; eauto.
      eapply typing1_kinding1 in H; simpl in *; eauto.
      destruct H as [Ht ?].
      invert Ht.
      eapply typing1_kinding1 in H0; simpl in *; eauto.
      destruct H0 as [Ht ?].
      invert Ht.
      econstructor; eauto using sorting1_bsorting'.
    }
    {
      (* Case Ty1Loc *)
      econstructor; simpl.
      erewrite fmap_map_lookup; eauto.
      eauto.
    }
    {
      (* Case Ty1Prim *)
      eapply Ty1Prim'; simpl; eauto using kinding1_shift_i_t, sorting1_shift_i_i, kinding1_wellscoped_t;
        destruct opr; simpl; eauto.
    }
    {
      econstructor; simpl; eauto using kinding1_subst_i_t, sorting1_subst_i_i.
    }
    {
      (* Case Ty1Ty1eq *)
      unfold_all.
      eapply Ty1Ty1eq; simpl; eauto using kinding1_subst_i_t.
      eapply typing1_kinding1 in H; simpl in *; eauto.
      destruct H as [Ht ?].
      eapply tyeq1_subst_i_t; eauto using kinding1_bkinding.
    }
    {
      (* Case Ty1Le *)
      unfold_all.
      eapply Ty1Le; simpl; eauto using sorting1_subst_i_i'.
      eapply interp_subst_i_p in H1; simpl in *; eauto.
      eapply typing1_kinding1 in H; simpl in *; eauto.
      destruct H as [Ht ?].
      econstructor; eauto using sorting1_bsorting'.
    }
  Qed.
  
  Lemma typing1_subst_i_e_2 L K W G e t i x v s :
    let C := (L, K, W, G) in
    typing1 C e t i ->
    nth_error L x = Some s ->
    sorting1 (my_skipn L (1 + x)) v s ->
    wfctx1 C ->
    typing1 (subst_i_ss v (firstn x L) ++ my_skipn L (1 + x), K, fmap_map (subst_i_ti x (shift_i_i x 0 v)) W, map (subst_i_t x (shift_i_i x 0 v)) G) (subst_i_e x (shift_i_i x 0 v) e) (subst_i_t x (shift_i_i x 0 v) t) (subst_i_i x (shift_i_i x 0 v) i).
  Proof.
    intros C Ht Hx Hv HC; unfold wfctx1 in *; openhyp; eapply typing1_subst_i_e with (C := C); eauto.
  Qed.  

  Lemma typing1_subst0_i_e s L K W G e t i v :
    let C := (s :: L, K, W, G) in
    typing1 C e t i ->
    sorting1 L v s ->
    wfctx1 C ->
    typing1 (L, K, fmap_map (subst0_i_ti v) W, map (subst0_i_t v) G) (subst0_i_e v e) (subst0_i_t v t) (subst0_i_i v i).
  Proof.
    intros C Ht Hv HC.
    eapply typing1_subst_i_e_2 with (x := 0) in Ht; simpl in *;  
      repeat rewrite my_skipn_0 in *;
      repeat rewrite shift_i_i_0 in *;
      eauto.
  Qed.

  (*
  Lemma tyeq1_subst_i_t_2 L t t' k x v1 v2 s :
    tyeq1 L t t' k ->
    nth_error L x = Some s ->
    sorting1 (my_skipn L (1 + x)) v1 s ->
    sorting1 (my_skipn L (1 + x)) v2 s ->
    idxeq (my_skipn L (1 + x)) v1 v2 (get_bsort s) ->
    let bs := map get_bsort L in
    bkinding bs t k ->
    bkinding bs t' k ->
    wfsorts1 L ->
    tyeq1 (subst_i_ss v1 (firstn x L) ++ my_skipn L (1 + x)) (subst_i_t x (shift_i_i x 0 v1) t) (subst_i_t x (shift_i_i x 0 v2) t') k.
  Proof.
    simpl.
    intros Ht1t2 Hx Hv1 Hv2 Hv1v2 Ht Ht' HL.
    rewrite tyeq1_tyeq1' in *.
    unfold tyeq1', idxeq in *.
    eapply interp_prop_shift_i_p with (x := 0) (ls := subst_i_ss v1 (firstn x L)) in Hv1v2; eauto using sorting1_wellscoped_i with db_la.
    Focus 2.
    {
      rewrite <- skipn_my_skipn.
      eapply all_sorts_skipn.
      eapply wfsorts1_wellscoped_ss; eauto.
    }
    Unfocus.
    rewrite my_skipn_0 in *.
    unfold interp_prop in *.
    simpl in *.
    rewrite get_bsort_remove_subst in *.
    copy Hx Hnth'.
    eapply map_nth_error with (f := get_bsort) in Hnth'.
    copy Hv1 Hv1'.
    eapply sorting1_bsorting in Hv1'.
    rewrite map_my_skipn in Hv1'.
    copy Hv2 Hv2'.
    eapply sorting1_bsorting in Hv2'.
    rewrite map_my_skipn in Hv2'.
    eapply forall_subst_i_p_intro_imply_2 with (v := v1) in Ht1t2; eauto using wfsorts1_wfprop1_strip_subsets.
    eapply forall_trans in Ht1t2; [ | eapply subst_strip_subsets_imply with (c := v1) ]; eauto.
    set (bs := map get_bsort L) in *.
    set (ps := interp_p (removen x bs) (and_all (strip_subsets (subst_i_ss v1 (firstn x L) ++ my_skipn L (S x))))) in *.
    copy Hx Hcmp.
    eapply nth_error_Some_lt in Hcmp.
    rewrite length_subst_i_ss in *.
    rewrite length_firstn_le in * by la.
    eapply forall_same_premise_2; [eapply Ht1t2 | eapply Hv1v2 | ].
    rewrite subst_lift2.
  Qed.    
*)

  Lemma Ty1AppI' C e c t i s t' :
    typing1 C e (TForallI s t) i ->
    sorting1 (get_sctx C) c s ->
    t' = subst0_i_t c t ->
    typing1 C (EAppI e c) t' i.
  Proof.
    intros; subst; econstructor; eauto.
  Qed.
  
  Lemma subst_t_t_unroll x v k t args :
    subst_t_t x v (unroll k t args) = unroll k (subst_t_t (1 + x) (shift_t_t 1 0 v) t) args.
  Proof.
    unfold unroll; simpl.
    unfold subst0_t_t.
    rewrite subst_t_t_TApps.
    rewrite subst_t_t_subst by la.
    eauto.
  Qed.
  
  Lemma subst_t_t_proj x v t1 t2 pr : subst_t_t x v (proj (t1, t2) pr) = proj (subst_t_t x v t1, subst_t_t x v t2) pr.
  Proof.
    destruct pr; simpl; eauto.
  Qed.
  
  Lemma subst_t_t_choose x v t1 t2 inj : subst_t_t x v (choose (t1, t2) inj) = choose (subst_t_t x v t1, subst_t_t x v t2) inj.
  Proof.
    destruct inj; simpl; eauto.
  Qed.
  
  Lemma typing1_subst_t_e C e t i :
    typing1 C e t i ->
    let L := get_sctx C in
    let K := get_kctx C in
    let W := get_hctx C in
    let G := get_tctx C in
    forall x v k,
      nth_error K x = Some k ->
      kinding1 L (my_skipn K (1 + x)) v k ->
      wfsorts1 L ->
      wfhctx1 L K W ->
      Forall (kinding1_KType L K) G ->
      typing1 (L, removen x K, fmap_map (subst_t_ti x (shift_t_t x 0 v)) W, map (subst_t_t x (shift_t_t x 0 v)) G) (subst_t_e x (shift_t_t x 0 v) e) (subst_t_t x (shift_t_t x 0 v) t) i.
  Proof.
    simpl.
    induct 1; simpl; 
      try rename x into x';
      try rename L into L';
      try rename K into K';
      try rename k into k';
      intros x v k Hx Hv HL HW HG;
      destruct C as (((L & K) & W) & G);
      simpl in *;
      cbn in *.
      (* try solve [econstructor; simpl; eauto using kinding1_subst_t_t, kinding1_wellscoped_t, wfsorts1_wellscoped_ss]. *)
    {
      (* Case Ty1Var *)
      econstructor.
      eauto using map_nth_error.
    }
    {
      econstructor; simpl; eauto using kinding1_subst_t_t, kinding1_wellscoped_t, wfsorts1_wellscoped_ss. 
    }
    {
      econstructor; simpl; eauto using kinding1_subst_t_t, kinding1_wellscoped_t, wfsorts1_wellscoped_ss. 
    }
    {
      (* Case Ty1AppT *)
      unfold subst0_t_t.
      rewrite subst_t_t_subst by la.
      econstructor; simpl; eauto using kinding1_subst_t_t, wfsorts1_wellscoped_ss.
    }
    {
      (* Case AbsT *)
      econstructor; eauto using value_subst_t_e; simpl.
      unfold shift0_t_t in *.
      specialize (IHtyping1 (S x) v k).
      repeat rewrite fmap_map_fmap_map in *.
      repeat rewrite map_map in *.
      unfold shift0_i_ti, shift_i_ti, shift0_t_ti, shift_t_ti, subst0_i_ti, subst_i_ti, subst0_t_ti, subst_t_ti in *.
      simpl in *.
      setoid_rewrite subst_t_t_shift_hit_setoid in IHtyping1; eauto with db_la.
      simpl in *.
      rewrite Nat.sub_0_r in *.
      rewrite shift_t_t_shift_merge by la.
      rewrite plus_comm.
      eapply IHtyping1; eauto with db_la.
      {
        eapply fmap_forall_fmap_map_intro.
        eapply fmap_forall_impl; eauto.
        simpl; intros.
        intuition eauto using kinding1_shift_t_t_1_0.
      }
      {
        eapply Forall_map.
        eapply Forall_impl; eauto.
        intros.
        eapply kinding1_shift_t_t_1_0; eauto.
      }
    }
    {
      (* Case Ty1AppI *)
      unfold subst0_i_t.
      eapply Ty1AppI'; eauto using kinding1_shift_t_t.
      unfold subst0_i_t, shift0_i_t.
      rewrite subst_i_t_subst_t_t.
      rewrite subst_i_t_shift_avoid by la.
      simpl.
      rewrite shift_i_t_0.
      eauto.
    }
    {
      (* Case Ty1AbsI *)
      econstructor; eauto using value_subst_t_e.
      specialize (IHtyping1 x (shift_i_t 1 0 v) k).
      simpl in *.
      unfold shift0_i_t in *.
      repeat rewrite fmap_map_fmap_map in *.
      repeat rewrite map_map in *.
      unfold shift0_i_ti, shift_i_ti, shift0_t_ti, shift_t_ti, subst0_i_ti, subst_i_ti, subst0_t_ti, subst_t_ti in *.
      simpl in *.
      setoid_rewrite shift_i_t_subst_t_t.
      setoid_rewrite shift_i_t_shift_t_t.
      eapply IHtyping1; simpl; eauto using wfsort1_wellscoped_s', kinding1_shift_i_t_1_0, wfsorts1_wellscoped_ss with db_la.
      {
        eapply fmap_forall_fmap_map_intro.
        eapply fmap_forall_impl; eauto.
        simpl; intros.
        intuition eauto using kinding1_shift_i_t_1_0, sorting1_shift_i_i_1_0,  wfsorts1_wellscoped_ss.
      }
      {
        eapply Forall_map.
        eapply Forall_impl; eauto.
        intros.
        eapply kinding1_shift_i_t_1_0; eauto using wfsorts1_wellscoped_ss.
      }
    }
    {
      (* Case Ty1Rec *)
      unfold_all.
      specialize (IHtyping1 x v k).
      rewrite subst_t_e_AbsTIs in *.
      simpl in *.
      econstructor; simpl; eauto using kinding1_subst_t_t, wfsorts1_wellscoped_ss.
    }
    {
      (* Case Ty1Fold *)
      unfold_all.
      specialize (IHtyping1 x v k).
      rewrite subst_t_t_TApps in *.
      rewrite subst_t_t_unroll in *.
      simpl in *.
      eapply kinding1_TApps_invert in H.
      destruct H as [Ht ?].
      invert Ht.
      econstructor; simpl; eauto using kinding1_subst_t_t.
      eapply kinding1_TApps; eauto using kinding1_subst_t_t.
      econstructor.
      rewrite shift0_t_t_shift_0.
      eapply kinding1_subst_t_t with (x := S x) (K := _ :: _); simpl; eauto using wfsorts1_wellscoped_ss with db_la.
    }
    {
      (* Case Ty1Unfold *)
      specialize (IHtyping1 x v k).
      rewrite subst_t_t_TApps in *.
      rewrite subst_t_t_unroll in *.
      simpl in *.
      econstructor; simpl; eauto using kinding1_subst_t_t.
    }
    {
      (* Case Ty1Pack *)
      invert H.
      econstructor; simpl; eauto using kinding1_subst_t_t, wfsorts1_wellscoped_ss.
      {
        econstructor; simpl; eauto using kinding1_subst_t_t.
        rewrite shift0_t_t_shift_0.
        eapply kinding1_subst_t_t with (x := S x) (K := _ :: _); simpl; eauto using wfsorts1_wellscoped_ss with db_la.
      }
      unfold subst0_t_t in *.
      rewrite <- subst_t_t_subst by la.
      eauto.
    }
    {
      (* Case Ty1Unpack *)
      econstructor; eauto.
      simpl.
      specialize (IHtyping1_2 (S x) v k).
      rewrite fmap_map_fmap_map in *.
      rewrite map_map in *.
      rewrite shift0_t_t_shift_0.
      unfold shift0_t_t in *.
      unfold shift0_i_ti, shift_i_ti, shift0_t_ti, shift_t_ti, subst0_i_ti, subst_i_ti, subst0_t_ti, subst_t_ti in *.
      simpl in *.
      setoid_rewrite subst_t_t_shift_hit_setoid in IHtyping1_2; eauto with db_la.
      simpl in *.
      rewrite Nat.sub_0_r in *.
      eapply typing1_kinding1 in H; simpl; eauto.
      destruct H as [Ht ?].
      invert Ht; eauto.
      eapply IHtyping1_2; eauto with db_la.
      {
        eapply fmap_forall_fmap_map_intro.
        eapply fmap_forall_impl; eauto.
        simpl; intros.
        intuition eauto using kinding1_shift_t_t_1_0.
      }
      {
        econstructor; eauto using kinding1_wellscoped_t.
        eapply Forall_map.
        eapply Forall_impl; eauto.
        intros.
        eapply kinding1_shift_t_t_1_0; eauto.
      }
    }
    {
      (* Case Ty1PackI *)
      invert H.
      econstructor; simpl; eauto using kinding1_subst_t_t; simpl.
      {
        unfold shift0_i_t.
        rewrite shift_i_t_shift_t_t.
        econstructor; simpl; eauto using kinding1_subst_t_t.
        eapply kinding1_subst_t_t; eauto using wfsort1_wellscoped_s', wfsorts1_wellscoped_ss, wellscoped_ss_cons.
        eapply kinding1_shift_i_t_1_0; eauto using wfsorts1_wellscoped_ss.
      }
      unfold subst0_i_t in *.
      specialize (IHtyping1 x v k).
      rewrite subst_i_t_subst_t_t in *.
      unfold shift0_i_t.
      rewrite subst_i_t_shift_avoid by la.
      simpl.
      rewrite shift_i_t_0.
      eauto.
    }
    {
      (* Case Ty1UnpackI *)
      econstructor; eauto.
      simpl.
      unfold shift0_i_t, shift0_i_i in *.
      specialize (IHtyping1_2 x (shift_i_t 1 0 v) k).
      rewrite fmap_map_fmap_map in *.
      rewrite map_map in *.
      unfold shift0_i_ti, shift_i_ti, shift0_t_ti, shift_t_ti, subst0_i_ti, subst_i_ti, subst0_t_ti, subst_t_ti in *.
      simpl in *.
      setoid_rewrite shift_i_t_subst_t_t.
      setoid_rewrite shift_i_t_shift_t_t.
      eapply typing1_kinding1 in H; simpl; eauto.
      destruct H as [Ht ?].
      invert Ht; eauto.
      eapply IHtyping1_2; simpl; eauto using wfsort1_wellscoped_s', kinding1_shift_i_t_1_0, wfsorts1_wellscoped_ss with db_la.
      {
        eapply fmap_forall_fmap_map_intro.
        eapply fmap_forall_impl; eauto.
        simpl; intros.
        intuition eauto using kinding1_shift_i_t_1_0, sorting1_shift_i_i_1_0,  wfsorts1_wellscoped_ss.
      }
      {
        econstructor; eauto.
        eapply Forall_map.
        eapply Forall_impl; eauto.
        intros.
        eapply kinding1_shift_i_t_1_0; eauto using wfsorts1_wellscoped_ss.
      }
    }
    {
      (* Case Ty1Const *)
      destruct cn; simpl; econstructor; eauto.
    }
    {
      econstructor; simpl; eauto using kinding1_subst_t_t, kinding1_wellscoped_t, wfsorts1_wellscoped_ss. 
    }
    {
      (* Case Ty1Proj *)
      rewrite subst_t_t_proj.
      econstructor; eauto.
    }
    {
      (* Case Ty1Inj *)
      rewrite subst_t_t_choose.
      simpl.
      econstructor; simpl; eauto using kinding1_subst_t_t, wfsorts1_wellscoped_ss.
    }
    {
      (* Case Ty1Case *)
      eapply typing1_kinding1 in H; simpl; eauto.
      destruct H as [Ht ?].
      invert Ht.
      econstructor; simpl; eauto using kinding1_subst_t_t, wfsorts1_wellscoped_ss.
    }
    {
      econstructor; simpl; eauto using kinding1_subst_t_t, kinding1_wellscoped_t, wfsorts1_wellscoped_ss. 
    }
    {
      econstructor; simpl; eauto using kinding1_subst_t_t, kinding1_wellscoped_t, wfsorts1_wellscoped_ss. 
    }
    {
      econstructor; simpl; eauto using kinding1_subst_t_t, kinding1_wellscoped_t, wfsorts1_wellscoped_ss. 
    }
    {
      (* Case Ty1Loc *)
      econstructor; simpl.
      erewrite fmap_map_lookup; eauto.
      eauto.
    }
    {
      (* Case Ty1Prim *)
      eapply Ty1Prim'; simpl; eauto using kinding1_shift_i_t, sorting1_shift_i_i, kinding1_wellscoped_t;
        destruct opr; simpl; eauto.
    }
    {
      econstructor; simpl; eauto using kinding1_subst_t_t, kinding1_wellscoped_t, wfsorts1_wellscoped_ss. 
    }
    {
      (* Case Ty1Ty1eq *)
      unfold_all.
      eapply typing1_kinding1 in H; simpl; eauto.
      destruct H as [Ht ?].
      eapply Ty1Ty1eq; simpl; eauto using kinding1_subst_t_t, wfsorts1_wellscoped_ss.
      eapply tyeq1_subst_t_t; eauto using kinding1_wellscoped_t, kinding1_bkinding.
    }
    {
      eapply Ty1Le; simpl; eauto using kinding1_subst_t_t, kinding1_wellscoped_t, wfsorts1_wellscoped_ss. 
    }
  Qed.

  Lemma typing1_subst_t_e_2 L K W G e t i x v k :
    let C := (L, K, W, G) in
    typing1 C e t i ->
    nth_error K x = Some k ->
    kinding1 L (my_skipn K (1 + x)) v k ->
    wfctx1 C ->
    typing1 (L, removen x K, fmap_map (subst_t_ti x (shift_t_t x 0 v)) W, map (subst_t_t x (shift_t_t x 0 v)) G) (subst_t_e x (shift_t_t x 0 v) e) (subst_t_t x (shift_t_t x 0 v) t) i.
  Proof.
    intros C; intros; unfold wfctx1 in *; openhyp; eapply typing1_subst_t_e with (C := C); eauto.
  Qed.
  
  Lemma typing1_subst0_t_e L k K W G e t i v :
    let C := (L, k :: K, W, G) in
    typing1 C e t i ->
    kinding1 L K v k ->
    wfctx1 C ->
    typing1 (L, K, fmap_map (subst0_t_ti v) W, map (subst0_t_t v) G) (subst0_t_e v e) (subst0_t_t v t) i.
  Proof.
    intros C Ht Hv HC.
    eapply typing1_subst_t_e_2 with (x := 0) in Ht; simpl in *;  
      repeat rewrite my_skipn_0 in *;
      repeat rewrite shift_t_t_0 in *;
      eauto.
  Qed.

  Lemma typing_shift_e_e C e t i :
    typing1 C e t i ->
    let L := get_sctx C in
    let K := get_kctx C in
    let W := get_hctx C in
    let G := get_tctx C in
    forall x ls,
      typing1 (L, K, W, firstn x G ++ ls ++ my_skipn G x) (shift_e_e (length ls) x e) t i.
  Proof.
    induct 1;
      try rename x into y;
      try rename L into L';
      try rename K into K';
      intros x ls;
      destruct C as (((L & K) & W) & G);
      simpl in *.
      (* try solve [econstructor; eauto]. *)
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
      econstructor; eauto.
    }
    {
      (* Case Abs *)
      econstructor; simplify; eauto.
      eapply IHtyping1 with (x := S x).
    }
    {
      econstructor; eauto.
    }
    {
      (* Case AbsT *)
      econstructor; simplify; eauto.
      {
        eapply value_shift_e_e; eauto.
      }
      repeat rewrite map_app.
      rewrite map_firstn.
      rewrite map_my_skipn.
      specialize (IHtyping1 x (map shift0_t_t ls)).
      rewrite map_length in *.
      eauto.
    }
    {
      econstructor; eauto.
    }
    {
      (* Case AbsI *)
      econstructor; simplify; eauto.
      {
        eapply value_shift_e_e; eauto.
      }
      repeat rewrite map_app.
      rewrite map_firstn.
      rewrite map_my_skipn.
      specialize (IHtyping1 x (map shift0_i_t ls)).
      rewrite map_length in *.
      eauto.
    }
    {
      (* Case Rec *)
      unfold_all.
      specialize (IHtyping1 (S x) ls); simplify.
      rewrite shift_e_e_AbsTIs in *.
      econstructor; simplify; eauto.
    }
    {
      econstructor; eauto.
    }
    {
      econstructor; eauto.
    }
    {
      econstructor; eauto.
    }
    {
      (* Case Unpack *)
      econstructor; simplify; eauto.
      repeat rewrite map_app.
      rewrite map_firstn.
      rewrite map_my_skipn.
      specialize (IHtyping1_2 (S x) (map shift0_t_t ls)); simplify.
      rewrite map_length in *.
      eauto.
    }
    {
      econstructor; eauto.
    }
    {
      (* Case UnpackI *)
      econstructor; simplify; eauto.
      repeat rewrite map_app.
      rewrite map_firstn.
      rewrite map_my_skipn.
      specialize (IHtyping1_2 (S x) (map shift0_i_t ls)); simplify.
      rewrite map_length in *.
      eauto.
    }
    {
      econstructor; eauto.
    }
    {
      econstructor; eauto.
    }
    {
      econstructor; eauto.
    }
    {
      econstructor; eauto.
    }
    {
      (* Case Case *)
      econstructor; simplify; eauto.
      {
        eapply IHtyping1_2 with (x := S x).
      }
      {
        eapply IHtyping1_3 with (x := S x).
      }
    }
    {
      econstructor; eauto.
    }
    {
      econstructor; eauto.
    }
    {
      econstructor; eauto.
    }
    {
      econstructor; eauto.
    }
    {
      econstructor; eauto.
    }
    {
      econstructor; eauto.
    }
    {
      econstructor; eauto.
    }
    {
      eapply Ty1Le; eauto.
    }
  Qed.
  
  Lemma typing1_shift0_e_e L K W G e t i t' :
    typing1 (L, K, W, G) e t i ->
    typing1 (L, K, W, t' :: G) (shift0_e_e e) t i.
  Proof.
    intros Hty.
    eapply typing_shift_e_e with (C := (L, K, W, G)) (x := 0) (ls := [t']) in Hty.
    simplify.
    repeat rewrite my_skipn_0 in *.
    eauto.
  Qed.
  
  Lemma wellscoped_ctx_add_typing1 L K W G t :
    wellscoped_ctx (L, K, W, G) ->
    wellscoped_t (length L) t ->
    wellscoped_ctx (L, K, W, t :: G).
  Proof.
    unfold wellscoped_ctx; intros HC Ht.
    openhyp.
    simpl in *.
    repeat try_split; eauto.
  Qed.
  
  Lemma wellscoped_ctx_add_kinding1 L K W G k :
    wellscoped_ctx (L, K, W, G) ->
    wellscoped_ctx (L, k :: K, fmap_map shift0_t_ti W, map shift0_t_t G).
  Proof.
    unfold wellscoped_ctx; intros HC.
    openhyp.
    simpl in *.
    repeat try_split; eauto.
    {
      eapply fmap_forall_fmap_map_intro.
      eapply fmap_forall_impl; eauto.
      intros.
      simpl in *.
      intuition eauto using wellscoped_shift_t_t.
    }
    {
      eapply Forall_map.
      eapply Forall_impl; eauto.
      intros.
      eapply wellscoped_shift_t_t; eauto.
    }
  Qed.

  Lemma wellscoped_ctx_add_kinding1_removen L K W G n k :
    wellscoped_ctx (L, K, W, removen n G) ->
    wellscoped_ctx (L, k :: K, fmap_map shift0_t_ti W, removen n (map shift0_t_t G)).
  Proof.
    intros; rewrite <- map_removen.
    eapply wellscoped_ctx_add_kinding1; eauto.
  Qed.
  
  Lemma wellscoped_ctx_add_sorting1 L K W G s :
    wellscoped_ctx (L, K, W, G) ->
    wellscoped_s (length L) s ->
    wellscoped_ctx (s :: L, K, fmap_map shift0_i_ti W, map shift0_i_t G).
  Proof.
    unfold wellscoped_ctx; intros HC Hs.
    openhyp.
    simpl in *.
    repeat try_split; eauto.
    {
      eapply fmap_forall_fmap_map_intro.
      eapply fmap_forall_impl; eauto.
      intros.
      simpl in *.
      intuition eauto using wellscoped_shift_i_t, wellscoped_shift_i_i.
    }
    {
      eapply Forall_map.
      eapply Forall_impl; eauto.
      intros.
      eapply wellscoped_shift_i_t; eauto.
    }
  Qed.

  Lemma wellscoped_ctx_add_sorting1_removen L K W G n s :
    wellscoped_ctx (L, K, W, removen n G) ->
    wellscoped_s (length L) s ->
    wellscoped_ctx (s :: L, K, fmap_map shift0_i_ti W, removen n (map shift0_i_t G)).
  Proof.
    intros; rewrite <- map_removen.
    eapply wellscoped_ctx_add_sorting1; eauto.
  Qed.
  
  Lemma typing1_subst_e_e C e1 t1 i1 :
    typing1 C e1 t1 i1 ->
    let L := get_sctx C in
    let K := get_kctx C in
    let W := get_hctx C in
    let G := get_tctx C in
    forall n t e2 ,
      nth_error G n = Some t ->
      typing1 (L, K, W, removen n G) e2 t T0 ->
      wellscoped_ctx (L, K, W, G) ->
      typing1 (L, K, W, removen n G) (subst_e_e n e2 e1) t1 i1.
      (* typing1 (get_kctx C, get_hctx C, removen n (get_tctx C)) (subst_e_e e2 n 0 e1) t1 i1. *)
  Proof.
    induct 1;
      try rename n into n';
      try rename L into L';
      try rename K into K';
      intros n t'' e2' Hnth Hty HC;
      destruct C as (((L & K) & W) & G);
      simpl in *.
      (* try solve [econstructor; eauto]. *)
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
      econstructor; eauto.
    }
    {
      (* Case Abs *)
      econstructor; simplify; eauto.
      eapply IHtyping1 with (n := 1 + n); simpl; eauto using wellscoped_ctx_add_typing1, kinding1_wellscoped_t.
      simplify.
      eapply typing1_shift0_e_e; eauto.
    }
    {
      econstructor; eauto.
    }
    {
      (* Case EAbsT *)
      econstructor; eauto.
      {
        eapply value_subst_e_e; eauto.
      }
      simplify.
      rewrite map_removen.
      eapply IHtyping1; eauto using wellscoped_ctx_add_kinding1.
      {
        eapply map_nth_error; eauto.
      }
      rewrite <- map_removen.
      eapply typing1_shift0_t_e; eauto.
    }
    {
      econstructor; eauto.
    }
    {
      (* Case EAbsI *)
      econstructor; eauto.
      {
        eapply value_subst_e_e; eauto.
      }
      simplify.
      rewrite map_removen.
      eapply IHtyping1; eauto using wellscoped_ctx_add_sorting1, wfsort1_wellscoped_s' with db_la.
      {
        eapply map_nth_error; eauto.
      }
      rewrite <- map_removen.
      eapply typing1_shift0_i_e with (i := T0); eauto.
      Lemma wellscoped_ctx_removen L K W G n :
        wellscoped_ctx (L, K, W, G) ->
        wellscoped_ctx (L, K, W, removen n G).
      Proof.
        unfold wellscoped_ctx; intros H.
        openhyp.
        simpl in *.
        repeat try_split; eauto.
        eapply Forall_forall.
        intros x Hin.
        Lemma incl_removen A (ls : list A) n : incl (removen n ls) ls.
        Proof.
          unfold incl; induct ls; destruct n; simpl; intuition eauto.
        Qed.

        eapply incl_removen in Hin.
        eapply Forall_forall' in H1; eauto.
      Qed.

      eapply wellscoped_ctx_removen; eauto.
    }
    {
      (* Case Rec *)
      unfold_all.
      rewrite subst_e_e_AbsTIs.
      simpl.
      econstructor; simpl; eauto; simplify.
      specialize (IHtyping1 (S n) t'' (shift0_e_e e2')); simpl in *.
      rewrite subst_e_e_AbsTIs in *.
      simpl in *.
      eapply IHtyping1; eauto using wellscoped_ctx_add_typing1, kinding1_wellscoped_t.
      eapply typing1_shift0_e_e; eauto.
    }
        Lemma typing1_wellscoped_t_2 L K W G e t i :
          let C := (L, K, W, G) in
          typing1 C e t i ->
          let nl := length L in
          wellscoped_ctx C ->
          wellscoped_t nl t /\
          wellscoped_i nl i.
        Proof.
          intros C; intros; unfold wellscoped_ctx in *; openhyp; eapply typing1_wellscoped_t with (C := C); eauto.
        Qed.
        
    {
      econstructor; eauto.
    }
    {
      econstructor; eauto.
    }
    {
      econstructor; eauto.
    }
    {
      (* Case Unpack *)
      eapply Ty1Unpack; eauto.
      simplify.
      rewrite map_removen.
      eapply IHtyping1_2 with (n := S n); eauto using wellscoped_ctx_add_kinding1, wellscoped_ctx_add_typing1, kinding1_wellscoped_t; simplify.
      {
        eapply map_nth_error; eauto.
      }
      {
        rewrite <- map_removen.
        eapply typing1_shift0_e_e; eauto.
        eapply typing1_shift0_t_e; eauto.
      }
      {
        eapply wellscoped_ctx_add_typing1.
        {
          eapply wellscoped_ctx_add_kinding1; eauto.
        }
        eapply typing1_wellscoped_t_2 in H; simpl; eauto.
        destruct H as [Ht ?].
        invert Ht.
        eauto.
      }
    }
    {
      econstructor; eauto.
    }
    {
      (* Case UnpackI *)
      eapply Ty1UnpackI; eauto.
      simplify.
      rewrite map_removen.
      eapply IHtyping1_2 with (n := S n); eauto; simplify.
      {
        eapply map_nth_error; eauto.
      }
      {
        rewrite <- map_removen.
        eapply typing1_shift0_e_e; eauto.
        eapply typing1_shift0_i_e with (i := T0); eauto.
        eapply wellscoped_ctx_removen; eauto.
      }
      {
        eapply typing1_wellscoped_t_2 in H; simpl; eauto.
        destruct H as [Ht ?].
        invert Ht.
        eapply wellscoped_ctx_add_typing1; eauto.
        eapply wellscoped_ctx_add_sorting1; eauto.
      }
    }
    {
      econstructor; eauto.
    }
    {
      econstructor; eauto.
    }
    {
      econstructor; eauto.
    }
    {
      econstructor; eauto.
    }
    {
      (* Case Case *)
      eapply typing1_wellscoped_t_2 in H; simpl; eauto.
      destruct H as [Ht ?].
      invert Ht.
      econstructor; eauto; simplify.
      {
        eapply IHtyping1_2 with (n := S n); eauto using wellscoped_ctx_add_typing1.
        simplify.
        eapply typing1_shift0_e_e; eauto.
      }
      {
        eapply IHtyping1_3 with (n := S n); eauto using wellscoped_ctx_add_typing1.
        simplify.
        eapply typing1_shift0_e_e; eauto.
      }
    }
    {
      econstructor; eauto.
    }
    {
      econstructor; eauto.
    }
    {
      econstructor; eauto.
    }
    {
      econstructor; eauto.
    }
    {
      econstructor; eauto.
    }
    {
      econstructor; eauto.
    }
    {
      econstructor; eauto.
    }
    {
      eapply Ty1Le; eauto.
    }
  Qed.
  
  Lemma typing_subst_e_e L K W t G e1 t1 i1 e2 :
    typing1 (L, K, W, t :: G) e1 t1 i1 ->
    typing1 (L, K, W, G) e2 t T0 ->
    wellscoped_ctx (L, K, W, t :: G) ->
    typing1 (L, K, W, G) (subst0_e_e e2 e1) t1 i1%idx.
  Proof.
    intros Hty1 Hty2 HC.
    eapply typing1_subst_e_e with (C := (L, K, W, t :: G)) (n := 0); simpl; eauto.
  Qed.

  Lemma typing1_subst0_e_e L K W t G e1 t1 i1 e2 i2 :
    typing1 (L, K, W, t :: G) e1 t1 i1 ->
    typing1 (L, K, W, G) e2 t i2 ->
    value e2 ->
    wellscoped_ctx (L, K, W, t :: G) ->
    typing1 (L, K, W, G) (subst0_e_e e2 e1) t1 i1%idx.
  Proof.
    intros Hty1 Hty2 Hval HC.
    eapply typing_subst_e_e; eauto.
    eapply value_typing1_T0; eauto.
  Qed.

  Lemma fmap_map_shift0_i_t_incl (W W' : hctx) :
    W $<= W' ->
    fmap_map shift0_i_ti W $<= fmap_map shift0_i_ti W'.
  Proof.
    intros; eapply incl_fmap_map; eauto.
  Qed.
  
  Lemma weaken_W' C e t i :
    typing1 C e t i ->
    forall W' ,
      get_hctx C $<= W' ->
      typing1 (get_sctx C, get_kctx C, W', get_tctx C) e t i.
  Proof.
    induct 1;
      intros W' Hincl;
      try rename L into L';
      try rename K into K';
      destruct C as (((L & K) & W) & G);
      simpl in *;
      try solve [econstructor; simpl; eauto using incl_fmap_map].
  Qed.
    
  Lemma weaken_W L K W G e t i W' :
    typing1 (L, K, W, G) e t i ->
    W $<= W' ->
    typing1 (L, K, W', G) e t i.
  Proof.
    intros Hty Hincl.
    eapply weaken_W' with (C := (L, K, W, G)); eauto.
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
      
  Lemma htyping1_fresh h W :
    htyping1 h W ->
    exists l, h $? l = None.
  Proof.
    intros Hhty.
    unfold htyping1 in *.
    destruct Hhty as (Hhty & Halloc).
    destruct Halloc as (l_alloc & Halloc).
    exists l_alloc.
    eapply Halloc.
    la.
  Qed.
  
  Lemma htyping1_elim_exists h W l t i :
    htyping1 h W ->
    W $? l = Some (t, i) ->
    exists vs,
      h $? l = Some vs /\
      length vs = interp_idx i [] BSNat /\
      Forall (fun v => value v /\ typing1 ([], [], W, []) v t T0) vs.
  Proof.
    intros Hhty Hl.
    unfold htyping1 in *.
    destruct Hhty as (Hhty & Halloc).
    eauto.
  Qed.    

  Lemma htyping1_elim h W l vs t i :
    htyping1 h W ->
    h $? l = Some vs ->
    W $? l = Some (t, i) ->
    length vs = interp_idx i [] BSNat /\
    Forall (fun v => value v /\ typing1 ([], [], W, []) v t T0) vs.
  Proof.
    intros Hhty Hl HWl.
    unfold htyping1 in *.
    destruct Hhty as (Hhty & Halloc).
    eapply Hhty in HWl.
    destruct HWl as (v' & Hl' & Hval' & Hty').
    rewrite Hl' in Hl.
    invert Hl.
    eauto.
  Qed.
  
  Lemma htyping1_elim_None h W l :
    htyping1 h W ->
    h $? l = None ->
    W $? l = None.
  Proof.
    intros Hhty Hl.
    unfold htyping1 in *.
    destruct Hhty as (Hhty & Halloc).
    cases (W $? l); eauto.
    destruct p.
    eapply Hhty in Heq.
    destruct Heq as (? & Hl2 & ?).
    rewrite Hl2 in Hl.
    invert Hl.
  Qed.
  
  Lemma htyping1_upd h W l t i vs :
    htyping1 h W ->
    W $? l = Some (t, i) ->
    length vs = interp_idx i [] BSNat ->
    Forall (fun v => value v /\ typing1 ([], [], W, []) v t T0) vs ->
    htyping1 (h $+ (l, vs)) W.
  Proof.
    intros Hhty Hl Hlen Hval.
    unfold htyping1 in *.
    destruct Hhty as (Hhty & Halloc).
    split; [ | eapply allocatable_add; eauto].
    intros l' t' i' Hl'.
    cases (l' ==n l); subst; simplify; eauto.
    rewrite Hl' in Hl.
    invert Hl.
    exists vs; repeat eexists_split; eauto.
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
  
  Lemma htyping1_new h W l t i vs :
    htyping1 h W ->
    h $? l = None ->
    length vs = interp_idx i [] BSNat ->
    Forall (fun v => value v /\ typing1 ([], [], W, []) v t T0) vs ->
    htyping1 (h $+ (l, vs)) (W $+ (l, (t, i))).
  Proof.
    intros Hhty Hl Hlen Hval.
    copy Hhty Hhty'.
    unfold htyping1.
    destruct Hhty as (Hhty & Halloc).
    split; [ | eapply allocatable_add; eauto].
    assert (Hincl : W $<= W $+ (l, (t, i))).
    {
      eapply htyping1_elim_None in Hl; eauto.
      eapply includes_add_new; eauto.
      eapply includes_intro; eauto.
    }
    intros l' t' i' Hl'.
    cases (l' ==n l); subst; simplify.
    {
      symmetry in Hl'.
      invert Hl'.
      exists vs; repeat eexists_split; eauto.
      eapply Forall_impl; eauto.
      simpl; intros.
      openhyp.
      split; eauto.
      eapply weaken_W; eauto.
    }
    {
      eapply Hhty in Hl'.
      destruct Hl' as (v' & Hl' & Hval' & Hty').
      exists v'; repeat eexists_split; eauto.
      eapply Forall_impl; eauto.
      simpl; intros.
      openhyp.
      split; eauto.
      eapply weaken_W; eauto.
    }
  Qed.

  Lemma wfctx1_add_kinding1 L K W G k :
    wfctx1 (L, K, W, G) ->
    wfctx1 (L, k :: K, fmap_map shift0_t_ti W, map shift0_t_t G).
  Proof.
    unfold wfctx1; intros HC.
    openhyp.
    simpl in *.
    repeat try_split; eauto.
    {
      eapply fmap_forall_fmap_map_intro.
      eapply fmap_forall_impl; eauto.
      simpl; intros.
      intuition eauto using kinding1_shift_t_t_1_0.
    }
    {
      eapply Forall_map.
      eapply Forall_impl; eauto.
      intros.
      eapply kinding1_shift_t_t_1_0; eauto.
    }
  Qed.

  Lemma wfctx1_add_sorting1 L K W G s :
    wfctx1 (L, K, W, G) ->
    wfsort1 (map get_bsort L) s ->
    wfctx1 (s :: L, K, fmap_map shift0_i_ti W, map shift0_i_t G).
  Proof.
    unfold wfctx1; intros HC Hs.
    openhyp.
    simpl in *.
    repeat try_split; eauto.
    {
      eapply fmap_forall_fmap_map_intro.
      eapply fmap_forall_impl; eauto.
      simpl; intros.
      intuition eauto using kinding1_shift_i_t_1_0, sorting1_shift_i_i_1_0,  wfsorts1_wellscoped_ss.
    }
    {
      eapply Forall_map.
      eapply Forall_impl; eauto.
      intros.
      eapply kinding1_shift_i_t_1_0; eauto using wfsorts1_wellscoped_ss.
    }
  Qed.

  Lemma kctx_elim_kinding1 L K W G l t i :
    let C := (L, K, W, G) in
    W $? l = Some (t, i) ->
    wfctx1 C ->
    kinding1 L K t KType.
  Proof.
    simpl; intros Hl HC.
    copy HC HC'.
    unfold wfctx1 in HC'.
    openhyp.
    simpl in *.
    eapply H0 in Hl.
    openhyp.
    eauto.
  Qed.
  
  Lemma kctx_elim_sorting1 L K W G l t i :
    let C := (L, K, W, G) in
    W $? l = Some (t, i) ->
    wfctx1 C ->
    sorting1 L i SNat.
  Proof.
    simpl; intros Hl HC.
    copy HC HC'.
    unfold wfctx1 in HC'.
    openhyp.
    simpl in *.
    eapply H0 in Hl.
    openhyp.
    eauto.
  Qed.

  Lemma wfctx1_add_htyping1 L K W G l t len:
    wfctx1 (L, K, W, G) ->
    kinding1 L K t KType ->
    sorting1 L len SNat ->
    wfctx1 (L, K, W $+ (l, (t, len)), G).
  Proof.
    intros HC Ht Hlen; unfold wfctx1 in *; openhyp; simpl in *; repeat try_split; eauto.
    unfold wfhctx1 in *.
    unfold fmap_forall in *.
    intros k v Hk.
    eapply lookup_split in Hk.
    destruct Hk; openhyp; subst; eauto.
  Qed.
  
  Ltac tyeq1_false_half H :=
      eapply invert_tyeq1_TQuan_TArrow in H ||
      eapply invert_tyeq1_TQuanI_TArrow in H ||
      eapply invert_tyeq1_TApps_TRec_TArrow in H ||
      eapply invert_tyeq1_TQuan_TArrow in H ||
      eapply invert_tyeq1_TQuanI_TArrow in H ||
      eapply invert_tyeq1_TBinOp_TArrow in H ||
      eapply invert_tyeq1_TQuanI_TQuan in H ||
      eapply invert_tyeq1_TApps_TRec_TQuan in H ||
      eapply invert_tyeq1_TExists_TForall in H ||
      eapply invert_tyeq1_TBinOp_TQuan in H ||
      eapply invert_tyeq1_TApps_TRec_TQuanI in H ||
      eapply invert_tyeq1_TApps_TRec_TBinOp in H ||
      eapply invert_tyeq1_TBinOp_TQuanI in H ||
      eapply invert_tyeq1_TBinOp_TConst in H ||
      eapply invert_tyeq1_TProd_TSum in H ||
      eapply invert_tyeq1_TConst_TQuanI in H || 
      eapply invert_tyeq1_TQuanI_TNat in H ||
      eapply invert_tyeq1_TQuanI_TArr in H ||
      eapply invert_tyeq1_TNat_TArrow in H || 
      eapply invert_tyeq1_TArr_TArrow in H || 
      eapply invert_tyeq1_TQuan_TNat in H ||
      eapply invert_tyeq1_TQuan_TArr in H ||
      eapply invert_tyeq1_TApps_TRec_TNat in H ||
      eapply invert_tyeq1_TApps_TRec_TArr in H ||
      eapply invert_tyeq1_TNat_TBinOp in H || 
      eapply invert_tyeq1_TArr_TBinOp in H || 
      eapply invert_tyeq1_TNat_TArr in H || 
      eapply invert_tyeq1_TConst_TArrow in H ||
      eapply invert_tyeq1_TConst_TQuan in H ||
      eapply invert_tyeq1_TConst_TNat in H ||
      eapply invert_tyeq1_TConst_TArr in H ||
      eapply invert_tyeq1_TApps_TRec_TConst in H ||
      eapply invert_tyeq1_TExistsI_TForallI in H
  .

  Ltac use_typings :=
    repeat match goal with
             H : typing1 _ _ _ _ |- _ => first [eapply typing_kinding in H; openhyp; eauto using wfctx1_add_sorting1, wfctx1_add_kinding1, wfctx1_add_typing1  | clear H ]
           end.
  
  Ltac tyeq1_false H := tyeq1_false_half H || (eapply tyeq1_sym in H; tyeq1_false_half H).

  Ltac tyeq1_dis' :=
    match goal with
      H : tyeq1 _ _ _ _ _ |- _ => tyeq1_false H; simpl; eauto using kinding1_bkinding'; propositional
    end.

  Ltac tyeq1_dis := use_typings; tyeq1_dis'.

  Lemma canon_TArrow' C v t i :
    typing1 C v t i ->
    get_sctx C = [] ->
    get_kctx C = [] ->
    get_tctx C = [] ->
    forall t1 i' t2 ,
      let t' := TArrow t1 i' t2 in
      tyeq1 [] [] t t' KType ->
      value v ->
      kinding1 [] [] t' KType ->
      wfctx1 C ->
      exists e,
        v = EAbs e.
  Proof.
    simpl.
    induct 1; intros Hsnil Hknil Htnil ta i' tb Htyeq Hval Hkd HC;
      try rename L into L';
      try rename K into K';
      destruct C as (((L & K) & W) & G); simpl in *; subst;
      try solve [invert Hval | eexists; eauto]; subst; unfold_all;
      try solve [tyeq1_dis |
                 cases cn; simpl in *; tyeq1_dis |
                 cases inj; simpl in *; tyeq1_dis |
                 eapply IHtyping1; eauto with db_tyeq1
                ].
    {
      cases cn; simpl in *; tyeq1_dis.
      repeat econstructor.
    }
    {
      tyeq1_dis.
      eauto using kctx_elim_kinding1, kctx_elim_sorting1, kinding1_bkinding', sorting1_bsorting''.
    }
    {
      eapply IHtyping1; eauto.
      eapply tyeq1_trans; eauto using kinding1_bkinding'.
    }
  Qed.

  Lemma canon_TArrow W v t1 i t2 i' :
    let C := ([], [], W, []) in 
    typing1 C v (TArrow t1 i t2) i' ->
    value v ->
    wfctx1 C ->
    exists e,
      v = EAbs e.
  Proof.
    intros; eapply canon_TArrow'; eauto using typing_kinding, kinding1_bkinding.
    {
      eapply tyeq1_refl.
      eapply kinding1_bkinding.
      eapply typing_kinding; eauto.
    }
    {
      eapply typing_kinding; eauto.
    }
  Qed.

  Lemma canon_TInt' C v t i :
    typing1 C v t i ->
    get_sctx C = [] ->
    get_kctx C = [] ->
    get_tctx C = [] ->
    tyeq1 [] [] t TInt KType ->
    value v ->
    wfctx1 C ->
    exists n, v = EInt n
  .
  Proof.
    induct 1; intros ? Hknil Htnil Htyeq Hval HC;
      try rename L into L';
      try rename K into K';
      destruct C as (((L & K) & W) & G); simpl in *; subst;
        try solve [invert Hval | eexists; eauto | invert Hval; eexists; eauto | invert Htyeq]; subst; unfold_all;
      try solve [tyeq1_dis |
                 cases inj; simpl in *; tyeq1_dis
                ].
    {
      cases cn; simpl in *; try solve [eapply invert_tyeq1_TConst in Htyeq; eauto; dis].
      tyeq1_dis.
      repeat econstructor.
    }
    {
      tyeq1_dis.
      eauto using kctx_elim_kinding1, kctx_elim_sorting1, kinding1_bkinding', sorting1_bsorting''.
    }
    {
      eapply IHtyping1; eauto.
      eapply tyeq1_trans; eauto using kinding1_bkinding'.
    }
  Qed.
  
  Lemma canon_TInt W v i :
    let C := ([], [], W, []) in 
    typing1 C v TInt i ->
    value v ->
    wfctx1 C ->
    exists n, v = EInt n.
  Proof.
    simpl.
    intros Hty; intros; eapply canon_TInt' in Hty; eauto using typing_kinding, kinding1_bkinding.
    eapply tyeq1_refl.
    repeat econstructor.
  Qed.

  Lemma canon_TForallI' C v t i :
    typing1 C v t i ->
    get_sctx C = [] ->
    get_kctx C = [] ->
    get_tctx C = [] ->
    forall s t1' ,
      let t' := TForallI s t1' in
      tyeq1 [] [] t t' KType ->
      value v ->
      kinding1 [] [] t' KType ->
      wfctx1 C ->
      exists e,
        v = EAbsI e.
  Proof.
    induct 1; intros Hsnil Hknil Htnil k' t'' Htyeq Hval; intros;
      try rename L into L';
      try rename K into K';
      destruct C as (((L & K) & W) & G); simpl in *; subst;
        try solve [invert Hval | eexists; eauto | invert Hval; eexists; eauto | invert Htyeq]; subst; unfold_all;
      try solve [tyeq1_dis |
                 cases inj; simpl in *; tyeq1_dis
                ].
    {
      cases cn; simpl in *; tyeq1_dis.
      repeat econstructor.
    }
    {
      tyeq1_dis.
      eauto using kctx_elim_kinding1, kctx_elim_sorting1, kinding1_bkinding', sorting1_bsorting''.
    }
    {
      eapply IHtyping1; eauto.
      eapply tyeq1_trans; eauto using kinding1_bkinding'.
    }
  Qed.

  Lemma canon_TForallI W v s t i :
    let C := ([], [], W, []) in 
    typing1 C v (TForallI s t) i ->
    value v ->
    wfctx1 C ->
    exists e,
      v = EAbsI e.
  Proof.
    intros; eapply canon_TForallI'; eauto using typing_kinding, kinding1_bkinding.
    {
      eapply tyeq1_refl.
      eapply kinding1_bkinding.
      eapply typing_kinding; eauto.
    }
    {
      eapply typing_kinding; eauto.
    }
  Qed.

  Lemma canon_TExistsI' C v t i :
    typing1 C v t i ->
    get_sctx C = [] ->
    get_kctx C = [] ->
    get_tctx C = [] ->
    forall s t1' ,
      let t' := TExistsI s t1' in
      tyeq1 [] [] t t' KType ->
      value v ->
      kinding1 [] [] t' KType ->
      wfctx1 C ->
      exists c e,
        v = EPackI c e /\
        value e.
  Proof.
    induct 1; intros Hsnil Hknil Htnil k' t'' Htyeq Hval; intros;
      try rename L into L';
      try rename K into K';
      destruct C as (((L & K) & W) & G); simpl in *; subst;
        try solve [invert Hval | eexists; eauto | invert Hval; eexists; eauto | invert Htyeq]; subst; unfold_all;
      try solve [tyeq1_dis |
                 cases inj; simpl in *; tyeq1_dis
                ].
    {
      tyeq1_dis.
      econstructor; eauto using kinding1_bkinding'.
    }
    {
      cases cn; simpl in *; tyeq1_dis.
      repeat econstructor.
    }
    {
      tyeq1_dis.
      eauto using kctx_elim_kinding1, kctx_elim_sorting1, kinding1_bkinding', sorting1_bsorting''.
    }
    {
      eapply IHtyping1; eauto.
      eapply tyeq1_trans; eauto using kinding1_bkinding'.
    }
  Qed.
  
  Lemma canon_TExistsI W v s t i :
    let C := ([], [], W, []) in  
    typing1 C v (TExistsI s t) i ->
    value v ->
    wfctx1 C ->
    exists c e,
      v = EPackI c e /\
      value e.
  Proof.
    intros; eapply canon_TExistsI'; eauto.
    {
      eapply tyeq1_refl.
      eapply kinding1_bkinding.
      eapply typing_kinding; eauto.
    }
    {
      eapply typing_kinding; eauto.
    }
  Qed.

  Lemma canon_TForall' C v t i :
    typing1 C v t i ->
    get_sctx C = [] ->
    get_kctx C = [] ->
    get_tctx C = [] ->
    forall k t1',
      let t' := TForall k t1' in
      tyeq1 [] [] t t' KType ->
      value v ->
      kinding1 [] [] t' KType ->
      wfctx1 C ->
      exists e,
        v = EAbsT e.
  Proof.
    induct 1; intros Hsnil Hknil Htnil k' t'' Htyeq Hval; intros;
      try rename L into L';
      try rename K into K';
      destruct C as (((L & K) & W) & G); simpl in *; subst;
        try solve [invert Hval | eexists; eauto | invert Hval; eexists; eauto | invert Htyeq]; subst; unfold_all;
      try solve [tyeq1_dis |
                 cases inj; simpl in *; tyeq1_dis
                ].
    {
      cases cn; simpl in *; tyeq1_dis.
      repeat econstructor.
    }
    {
      tyeq1_dis.
      eauto using kctx_elim_kinding1, kctx_elim_sorting1, kinding1_bkinding', sorting1_bsorting''.
    }
    {
      eapply IHtyping1; eauto.
      eapply tyeq1_trans; eauto using kinding1_bkinding'.
    }
  Qed.

  Lemma canon_TForall W v k t i :
    let C := ([], [], W, []) in 
    typing1 C v (TForall k t) i ->
    value v ->
    wfctx1 C ->
    exists e,
      v = EAbsT e.
  Proof.
    intros; eapply canon_TForall'; eauto.
    {
      eapply tyeq1_refl.
      eapply kinding1_bkinding.
      eapply typing_kinding; eauto.
    }
    {
      eapply typing_kinding; eauto.
    }
  Qed.

  Lemma canon_TRec' C v t i :
    typing1 C v t i ->
    get_sctx C = [] ->
    get_kctx C = [] ->
    get_tctx C = [] ->
    forall k t1' cs ,
      let t' := TApps (TRec k t1') cs in
      tyeq1 [] [] t t' KType ->
      value v ->
      kinding1 [] [] t' KType ->
      wfctx1 C ->
      exists e,
        v = EFold e /\
        value e.
  Proof.
    induct 1; intros Hsnil Hknil Htnil k' t'' cs' Htyeq Hval; intros;
      try rename L into L';
      try rename K into K';
      destruct C as (((L & K) & W) & G); simpl in *; subst;
        try solve [invert Hval | eexists; eauto | invert Hval; eexists; eauto | invert Htyeq]; subst; unfold_all;
      try solve [tyeq1_dis |
                 cases inj; simpl in *; tyeq1_dis
                ].
    {
      cases cn; simpl in *; tyeq1_dis.
      repeat econstructor.
    }
    {
      tyeq1_dis.
      eauto using kctx_elim_kinding1, kctx_elim_sorting1, kinding1_bkinding', sorting1_bsorting''.
    }
    {
      eapply IHtyping1; eauto.
      eapply tyeq1_trans; eauto using kinding1_bkinding'.
    }
  Qed.

  Lemma canon_TRec W v k t cs i :
    let C := ([], [], W, []) in 
    typing1 C v (TApps (TRec k t) cs) i ->
    value v ->
    wfctx1 C ->
    exists e,
      v = EFold e /\
      value e.
  Proof.
    intros; eapply canon_TRec'; eauto.
    {
      eapply tyeq1_refl.
      eapply kinding1_bkinding.
      eapply typing_kinding; eauto.
    }
    {
      eapply typing_kinding; eauto.
    }
  Qed.

  Lemma canon_TExists' C v t i :
    typing1 C v t i ->
    get_sctx C = [] ->
    get_kctx C = [] ->
    get_tctx C = [] ->
    forall k t1' ,
      let t' := TExists k t1' in
      tyeq1 [] [] t t' KType ->
      value v ->
      kinding1 [] [] t' KType ->
      wfctx1 C ->
      exists c e,
        v = EPack c e /\
        value e.
  Proof.
    induct 1; intros Hsnil Hknil Htnil k' t'' Htyeq Hval; intros;
      try rename L into L';
      try rename K into K';
      destruct C as (((L & K) & W) & G); simpl in *; subst;
        try solve [invert Hval | eexists; eauto | invert Hval; eexists; eauto | invert Htyeq]; subst; unfold_all;
      try solve [tyeq1_dis |
                 cases inj; simpl in *; tyeq1_dis
                ].
    {
      tyeq1_dis.
      econstructor; eauto using kinding1_bkinding'.
    }
    {
      cases cn; simpl in *; tyeq1_dis.
      repeat econstructor.
    }
    {
      tyeq1_dis.
      eauto using kctx_elim_kinding1, kctx_elim_sorting1, kinding1_bkinding', sorting1_bsorting''.
    }
    {
      eapply IHtyping1; eauto.
      eapply tyeq1_trans; eauto using kinding1_bkinding'.
    }
  Qed.
  
  Lemma canon_TExists W v k t i :
    let C := ([], [], W, []) in 
    typing1 C v (TExists k t) i ->
    value v ->
    wfctx1 C ->
    exists c e,
      v = EPack c e /\
      value e.
  Proof.
    intros; eapply canon_TExists'; eauto.
    {
      eapply tyeq1_refl.
      eapply kinding1_bkinding.
      eapply typing_kinding; eauto.
    }
    {
      eapply typing_kinding; eauto.
    }
  Qed.

  Lemma canon_TProd' C v t i :
    typing1 C v t i ->
    get_sctx C = [] ->
    get_kctx C = [] ->
    get_tctx C = [] ->
    forall t1 t2 ,
      let t' := TProd t1 t2 in
      tyeq1 [] [] t t' KType ->
      value v ->
      kinding1 [] [] t' KType ->
      wfctx1 C ->
      exists v1 v2,
        v = EPair v1 v2 /\
        value v1 /\
        value v2.
  Proof.
    induct 1; intros Hsnil Hknil Htnil t1'' t2'' Htyeq Hval; intros;
            try rename L into L';
      try rename K into K';
      destruct C as (((L & K) & W) & G); simpl in *; subst;
        try solve [invert Hval | eexists; eauto | invert Hval; eexists; eauto | invert Htyeq]; subst; unfold_all;
      try solve [tyeq1_dis |
                 cases inj; simpl in *; tyeq1_dis
                ].
    {
      cases cn; simpl in *; tyeq1_dis.
      repeat econstructor.
    }
    {
      cases inj; simpl in *; tyeq1_dis;
      econstructor; eauto using kinding1_bkinding'.
    }
    {
      tyeq1_dis.
      eauto using kctx_elim_kinding1, kctx_elim_sorting1, kinding1_bkinding', sorting1_bsorting''.
    }
    {
      eapply IHtyping1; eauto.
      eapply tyeq1_trans; eauto using kinding1_bkinding'.
    }
  Qed.
  
  Lemma canon_TProd W v t1 t2 i :
    let C := ([], [], W, []) in  
    typing1 C v (TProd t1 t2) i ->
    value v ->
    wfctx1 C ->
    exists v1 v2,
      v = EPair v1 v2 /\
      value v1 /\
      value v2.
  Proof.
    intros; eapply canon_TProd'; eauto.
    {
      eapply tyeq1_refl.
      eapply kinding1_bkinding.
      eapply typing_kinding; eauto.
    }
    {
      eapply typing_kinding; eauto.
    }
  Qed.

  Lemma canon_TSum' C v t i :
    typing1 C v t i ->
    get_sctx C = [] ->
    get_kctx C = [] ->
    get_tctx C = [] ->
    forall t1 t2 ,
      let t' := TSum t1 t2 in
      tyeq1 [] [] t t' KType ->
      value v ->
      kinding1 [] [] t' KType ->
      wfctx1 C ->
      exists inj v',
        v = EInj inj v' /\
        value v'.
  Proof.
    induct 1; intros ? Hknil Htnil t1'' t2'' Htyeq Hval; intros;
      try rename L into L';
      try rename K into K';
      destruct C as (((L & K) & W) & G); simpl in *; subst;
        try solve [invert Hval | eexists; eauto | invert Hval; eexists; eauto | invert Htyeq]; subst; unfold_all;
          try solve [tyeq1_dis |
                     cases inj; simpl in *; tyeq1_dis
                    ].
    {
      cases cn; simpl in *; tyeq1_dis.
      repeat econstructor.
    }
    {
      tyeq1_dis.
      econstructor; eauto using kinding1_bkinding'.
    }
    {
      tyeq1_dis.
      eauto using kctx_elim_kinding1, kctx_elim_sorting1, kinding1_bkinding', sorting1_bsorting''.
    }
    {
      eapply IHtyping1; eauto.
      eapply tyeq1_trans; eauto using kinding1_bkinding'.
    }
  Qed.
  
  Lemma canon_TSum W v t1 t2 i :
    let C := ([], [], W, []) in 
    typing1 C v (TSum t1 t2) i ->
    value v ->
    wfctx1 C ->
    exists inj v',
      v = EInj inj v' /\
      value v'.
  Proof.
    intros; eapply canon_TSum'; eauto.
    {
      eapply tyeq1_refl.
      eapply kinding1_bkinding.
      eapply typing_kinding; eauto.
    }
    {
      eapply typing_kinding; eauto.
    }
  Qed.

  Lemma canon_TNat' C v t i :
    typing1 C v t i ->
    get_sctx C = [] ->
    get_kctx C = [] ->
    get_tctx C = [] ->
    forall i' ,
      let t' := TNat i' in
      tyeq1 [] [] t t' KType ->
      value v ->
      kinding1 [] [] t' KType ->
      wfctx1 C ->
      v = ENat (interp_idx i' [] BSNat).
  Proof.
    induct 1; intros ? Hknil Htnil i' Htyeq Hval; intros;
      try rename L into L';
      try rename K into K';
      destruct C as (((L & K) & W) & G); simpl in *; subst;
        try solve [invert Hval | eexists; eauto | invert Hval; eexists; eauto | invert Htyeq]; subst; unfold_all;
          try solve [tyeq1_dis |
                     cases inj; simpl in *; tyeq1_dis
                    ].
    {
      cases cn; simpl in *; try tyeq1_dis.
      eapply invert_tyeq1_TNat in Htyeq; eauto using kinding1_bkinding'; try solve [repeat econstructor].
      unfold idxeq in *.
      simpl in *.
      rewrite convert_bsort_value_refl_eq in *.
      f_equal.
      f_equal.
      eauto.
    }
    {
      tyeq1_dis.
      eauto using kctx_elim_kinding1, kctx_elim_sorting1, kinding1_bkinding', sorting1_bsorting''.
    }
    {
      eapply IHtyping1; eauto.
      eapply tyeq1_trans; eauto using kinding1_bkinding'.
    }
  Qed.
  
  Lemma canon_TNat W v i1 i :
    let C := ([], [], W, []) in 
    typing1 C v (TNat i1) i ->
    value v ->
    wfctx1 C ->
    v = ENat (interp_idx i1 [] BSNat).
  Proof.
    simpl.
    intros Hty; intros; eapply canon_TNat' in Hty; eauto.
    {
      eapply tyeq1_refl.
      eapply kinding1_bkinding.
      eapply typing_kinding; eauto.
    }
    {
      eapply typing_kinding; eauto.
    }
  Qed.

  Lemma canon_TArr' C v t i :
    typing1 C v t i ->
    get_sctx C = [] ->
    get_kctx C = [] ->
    get_tctx C = [] ->
    forall t1' i' ,
      let t' := TArr t1' i' in
      tyeq1 [] [] t t' KType ->
      value v ->
      kinding1 [] [] t' KType ->
      wfctx1 C ->
      exists l t'' i'',
        v = ELoc l /\
        get_hctx C $? l = Some (t'', i'') /\
        tyeq1 [] [] t'' t1' KType /\
        idxeq [] i'' i' BSNat.
  Proof.
    induct 1; intros ? Hknil Htnil t'' i'' Htyeq Hval; intros;
      try rename L into L';
      try rename K into K';
      destruct C as (((L & K) & W) & G); simpl in *; subst;
        try solve [invert Hval | eexists; eauto | invert Hval; eexists; eauto | invert Htyeq]; subst; unfold_all;
          try solve [tyeq1_dis |
                     cases inj; simpl in *; tyeq1_dis
                    ].
    {
      cases cn; simpl in *; try tyeq1_dis.
      repeat econstructor.
    }
    {
      eapply invert_tyeq1_TArr in Htyeq; eauto using kinding1_bkinding', kctx_elim_kinding1, kctx_elim_sorting1, kinding1_bkinding', sorting1_bsorting''.
      openhyp.
      repeat eexists_split; eauto.
    }
    {
      eapply IHtyping1; eauto.
      eapply tyeq1_trans; eauto using kinding1_bkinding'.
    }
  Qed.
  
  Lemma canon_TArr W v t len i :
    let C := ([], [], W, []) in 
    typing1 C v (TArr t len) i ->
    value v ->
    wfctx1 C ->
    exists l t'' i'',
      v = ELoc l /\
      W $? l = Some (t'', i'') /\
      tyeq1 [] [] t'' t KType /\
      idxeq [] i'' len BSNat.
  Proof.
    simpl; intros Hty; intros; eapply canon_TArr' in Hty; eauto with db_tyeq1.
    {
      eapply tyeq1_refl.
      eapply kinding1_bkinding.
      eapply typing_kinding; eauto.
    }
    {
      eapply typing_kinding; eauto.
    }
  Qed.

  Lemma progress' C e t i :
    typing1 C e t i ->
    get_sctx C = [] ->
    get_kctx C = [] ->
    get_tctx C = [] ->
    forall h f ,
      htyping1 h (get_hctx C) ->
      (interp_time i <= f)%time ->
      wfctx1 C ->
      unstuck (h, e, f).
  Proof.
    induct 1.
    {
      (* Case Var *)
      intros ? ? ? h f Hhty Hle HC.
      destruct C as (((L & K) & W) & G).
      simplify.
      subst.
      rewrite nth_error_nil in H.
      invert H.
    }
    {
      (* Case App *)
      intros ? ? ? h f Hhty Hle HC.
      destruct C as (((L & K) & W) & G).
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
      eapply IHtyping1_1 in Hi1; eauto.
      cases Hi1; simplify.
      {
        eapply canon_TArrow in H1; eauto.
        destruct H1 as (e & ?).
        subst.
        eapply IHtyping1_2 in Hi2; eauto.
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
      (* Case AppT *)
      intros ? ? ? h f Hhty Hle HC.
      destruct C as (((L & K) & W) & G).
      simplify.
      subst.
      eapply IHtyping1 in Hle; eauto.
      cases Hle; simplify.
      {
        eapply canon_TForall in H1; eauto.
        destruct H1 as (e1 & ?).
        subst.
        right.
        exists (h, subst0_t_e t e1, f).
        eapply StepPlug with (E := ECHole); try eapply PlugHole.
        eauto.
      }
      {
        destruct H1 as (((h' & e1') & f') & Hstep).
        invert Hstep.
        rename e' into e0'.
        rename e1' into e'.
        right.
        exists (h', EAppT e' t, f').
        eapply StepPlug with (E := ECAppT E t); repeat econstructor; eauto.
      }
    }
    {
      (* Case AbsT *)
      intros.
      left.
      simplify; eauto.
    }
    {
      (* Case AppI *)
      intros ? ? ? h f Hhty Hle HC.
      destruct C as (((L & K) & W) & G).
      simplify.
      subst.
      eapply IHtyping1 in Hle; eauto.
      cases Hle; simplify.
      {
        eapply canon_TForallI in H1; eauto.
        destruct H1 as (e1 & ?).
        subst.
        right.
        exists (h, subst0_i_e c e1, f).
        eapply StepPlug with (E := ECHole); try eapply PlugHole.
        eauto.
      }
      {
        destruct H1 as (((h' & e1') & f') & Hstep).
        invert Hstep.
        rename e' into e0'.
        rename e1' into e'.
        right.
        exists (h', EAppI e' c, f').
        eapply StepPlug with (E := ECAppI E c); repeat econstructor; eauto.
      }
    }
    {
      (* Case AbsI *)
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
      intros ? ? ? h f Hhty Hle HC.
      destruct C as (((L & K) & W) & G).
      simplify.
      subst.
      eapply IHtyping1 in Hle; eauto.
      cases Hle; simplify.
      {
        left.
        simplify; eauto.
      }
      {
        destruct H1 as (((h' & e1') & f') & Hstep).
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
      intros ? ? ? h f Hhty Hle HC.
      destruct C as (((L & K) & W) & G).
      simplify.
      subst.
      eapply IHtyping1 in Hle; eauto.
      cases Hle; simplify.
      {
        copy H Hty.
        eapply canon_TRec in H; eauto.
        destruct H as (e1 & ? & Hv).
        subst.
        right.
        exists (h, e1, f).
        eapply StepPlug with (E := ECHole); try eapply PlugHole.
        eauto.
      }
      {
        destruct H0 as (((h' & e1') & f') & Hstep).
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
      intros ? ? ? h f Hhty Hle HC.
      destruct C as (((L & K) & W) & G).
      simplify.
      subst.
      eapply IHtyping1 in Hle; eauto.
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
      intros ? ? ? h f Hhty Hle HC.
      destruct C as (((L & K) & W) & G).
      simplify.
      subst.
      assert (Hi1 : (interp_time i1 <= f)%time).
      {
        repeat rewrite interp_time_distr in Hle.
        repeat (eapply Time_add_le_elim in Hle; destruct Hle as (Hle & ?)).
        eauto.
      }
      eapply IHtyping1_1 in Hi1; eauto.
      cases Hi1; simplify.
      {
        rename H into Hty.
        eapply canon_TExists in Hty; eauto.
        destruct Hty as (c & e & ? & Hv).
        subst.
        right.
        exists (h, subst0_e_e e (subst0_t_e c e2), f).
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
      (* Case PackI *)
      intros ? ? ? h f Hhty Hle HC.
      destruct C as (((L & K) & W) & G).
      simplify.
      subst.
      eapply IHtyping1 in Hle; eauto.
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
        exists (h', EPackI c e', f').
        eapply StepPlug with (E := ECPackI c E); repeat econstructor; eauto.
      }
    }
    {
      (* Case UnpackI *)
      intros ? ? ? h f Hhty Hle HC.
      destruct C as (((L & K) & W) & G).
      simplify.
      subst.
      assert (Hi1 : (interp_time i1 <= f)%time).
      {
        repeat rewrite interp_time_distr in Hle.
        repeat (eapply Time_add_le_elim in Hle; destruct Hle as (Hle & ?)).
        eauto.
      }
      eapply IHtyping1_1 in Hi1; eauto.
      cases Hi1; simplify.
      {
        rename H into Hty.
        eapply canon_TExistsI in Hty; eauto.
        destruct Hty as (c & e & ? & Hv).
        subst.
        right.
        exists (h, subst0_e_e e (subst0_i_e c e2), f).
        eapply StepPlug with (E := ECHole); try eapply PlugHole.
        eauto.
      }
      {
        rename H1 into Hstep.
        destruct Hstep as (((h' & e1') & f') & Hstep).
        invert Hstep.
        right.
        exists (h', EUnpackI e1' e2, f').
        eapply StepPlug with (E := ECUnpackI E e2); repeat econstructor; eauto.
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
      intros ? ? ? h f Hhty Hle HC.
      destruct C as (((L & K) & W) & G).
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
      eapply IHtyping1_1 in Hi1; eauto.
      cases Hi1; simplify.
      {
        eapply IHtyping1_2 in Hi2; eauto.
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
      intros ? ? ? h f Hhty Hle HC.
      destruct C as (((L & K) & W) & G).
      simplify.
      subst.
      eapply IHtyping1 in Hle; eauto.
      destruct Hle as [He | He]; simplify.
      {
        eapply canon_TProd in He; eauto.
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
      intros ? ? ? h f Hhty Hle HC.
      destruct C as (((L & K) & W) & G).
      simplify.
      subst.
      eapply IHtyping1 in Hle; eauto.
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
      intros ? ? ? h f Hhty Hle HC.
      destruct C as (((L & K) & W) & G).
      simplify.
      subst.
      assert (Hile : (interp_time i <= f)%time).
      {
        repeat rewrite interp_time_distr in Hle.
        repeat (eapply Time_add_le_elim in Hle; destruct Hle as (Hle & ?)).
        eauto.
      }
      eapply IHtyping1_1 in Hile; eauto.
      destruct Hile as [He | He]; simplify.
      {
        eapply canon_TSum in He; eauto.
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
      intros ? ? ? h f Hhty Hle HC.
      destruct C as (((L & K) & W) & G).
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
      eapply IHtyping1_1 in Hi1; eauto.
      destruct Hi1 as [He1 | He1]; simplify.
      {
        eapply IHtyping1_2 in Hi2; eauto.
        destruct Hi2 as [He2 | He2]; simplify.
        {
          right.
          eapply canon_TNat in He2; eauto.
          subst.
          eapply htyping1_fresh in Hhty.
          destruct Hhty as (l & Hl).
          exists (h $+ (l, repeat e1 (interp_idx len [] BSNat)), ELoc l, f).
          eapply StepPlug with (E := ECHole); try eapply PlugHole.
          eauto.
        }
        {
          destruct He2 as (((h' & e') & f') & Hstep).
          invert Hstep.
          right.
          exists (h', ENew e1 e', f').
          eapply StepPlug with (E := ECBinOp2 _ e1 E); repeat econstructor; eauto.
        }
      }
      {
        destruct He1 as (((h' & e') & f') & Hstep).
        invert Hstep.
        right.
        exists (h', ENew e' e2, f').
        eapply StepPlug with (E := ECBinOp1 _ E e2); repeat econstructor; eauto.
      }
    }
    Lemma nth_error_lt_Some A ls n :
      n < length ls -> exists a : A, nth_error ls n = Some a.
    Proof.
      intros H.
      eapply nth_error_Some in H.
      cases (option_dec (nth_error ls n)); propositional.
      destruct s; eexists; eauto.
    Qed.

    {
      (* Case Read *)
      intros ? ? ? h f Hhty Hle HC.
      destruct C as (((L & K) & W) & G).
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
      eapply IHtyping1_1 in Hi1; eauto.
      destruct Hi1 as [He1 | He1]; simpl in *.
      {
        eapply IHtyping1_2 in Hi2; eauto.
        destruct Hi2 as [He2 | He2]; simpl in *.
        {
          eapply canon_TArr in He1; eauto.
          destruct He1 as (l & t' & i' & ? & Hl & Ht't & Hi'len).
          unfold idxeq, interp_prop in Hi'len.
          simpl in *.
          specialize (Hi'len I).
          subst.
          eapply canon_TNat in He2; eauto.
          subst.
          eapply htyping1_elim_exists in Hl; eauto.
          destruct Hl as (vs & Hl & Hlen & Hvs).
          unfold idxeq, interp_prop in H1.
          simpl in *.
          specialize (H1 I).
          set (n := interp_idx i [] BSNat) in *.
          assert (Hv : exists v, nth_error vs n = Some v).
          {
            eapply nth_error_lt_Some.
            la.
          }
          destruct Hv as (v & Hv).
          right.
          exists (h, v, f).
          eapply StepPlug with (E := ECHole); try eapply PlugHole.
          econstructor; eauto.
        }
        {
          destruct He2 as (((h' & e') & f') & Hstep).
          invert Hstep.
          right.
          exists (h', ERead e1 e', f').
          eapply StepPlug with (E := ECBinOp2 _ e1 E); repeat econstructor; eauto.
        }
      }
      {
        destruct He1 as (((h' & e') & f') & Hstep).
        invert Hstep.
        right.
        exists (h', ERead e' e2, f').
        eapply StepPlug with (E := ECBinOp1 _ E e2); repeat econstructor; eauto.
      }
    }
    {
      (* Case Write *)
      intros ? ? ? h f Hhty Hle HC.
      destruct C as (((L & K) & W) & G).
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
      assert (Hi3 : (interp_time i3 <= f)%time).
      {
        repeat rewrite interp_time_distr in Hle.
        repeat (eapply Time_add_le_elim in Hle; destruct Hle as (Hle & ?)).
        eauto.
      }
      eapply IHtyping1_1 in Hi1; eauto.
      destruct Hi1 as [He1 | He1]; simplify.
      {
        eapply IHtyping1_2 in Hi2; eauto.
        destruct Hi2 as [He2 | He2]; simplify.
        {
          eapply IHtyping1_3 in Hi3; eauto.
          destruct Hi3 as [He3 | He3]; simplify.
          {
            eapply canon_TArr in He1; eauto.
            destruct He1 as (l & t' & i' & ? & Hl & Ht't & Hi'len).
            unfold idxeq, interp_prop in Hi'len.
            simpl in *.
            specialize (Hi'len I).
            subst.
            eapply canon_TNat in He2; eauto.
            subst.
            unfold idxeq, interp_prop in H1.
            simpl in *.
            specialize (H1 I).
            set (n := interp_idx i [] BSNat) in *.
            eapply htyping1_elim_exists in Hl; eauto.
            destruct Hl as (vs & Hl & Hlen & Hvs).
            right.
            exists (h $+ (l, upd vs n e3), ETT, f).
            eapply StepPlug with (E := ECHole); try eapply PlugHole.
            econstructor; eauto with db_la.
          }
          {
            destruct He3 as (((h' & e3') & f') & Hstep).
            invert Hstep.
            right.
            exists (h', EWrite e1 e2 e3', f').
            eapply StepPlug with (E := ECWrite3 e1 e2 E); repeat econstructor; eauto.
          }
        }
        {
          destruct He2 as (((h' & e2') & f') & Hstep).
          invert Hstep.
          right.
          exists (h', EWrite e1 e2' e3, f').
          eapply StepPlug with (E := ECWrite2 e1 E e3); repeat econstructor; eauto.
        }
      }
      {
        destruct He1 as (((h' & e1') & f') & Hstep).
        invert Hstep.
        right.
        exists (h', EWrite e1' e2 e3, f').
        eapply StepPlug with (E := ECWrite1 E e2 e3); repeat econstructor; eauto.
      }
    }
    {
      (* Case Loc *)
      intros.
      left.
      simplify; eauto.
    }
    {
      (* Case Ty1Prim *)
      intros ? ? ? h f Hhty Hle HC.
      destruct C as (((L & K) & W) & G).
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
      eapply IHtyping1_1 in Hi1; eauto.
      destruct Hi1 as [He1 | He1]; simpl in *.
      {
        eapply IHtyping1_2 in Hi2; eauto.
        destruct Hi2 as [He2 | He2]; simpl in *.
        {
          set (f' := (f - prim_cost opr)%time).
          cases opr; simpl in *.
          {
            eapply canon_TInt in He1; eauto.
            destruct He1 as (n1 & ?).
            subst.
            eapply canon_TInt in He2; eauto.
            destruct He2 as (n2 & ?).
            subst.
            right.
            exists (h, EInt (int_add n1 n2), f').
            eapply StepPlug with (E := ECHole); try eapply PlugHole.
            econstructor; eauto.
            repeat rewrite interp_time_distr in Hle.
            repeat (eapply Time_add_le_elim in Hle; destruct Hle as (Hle & ?)).
            eauto.
          }
          {
            eapply canon_TInt in He1; eauto.
            destruct He1 as (n1 & ?).
            subst.
            eapply canon_TInt in He2; eauto.
            destruct He2 as (n2 & ?).
            subst.
            right.
            exists (h, EInt (int_mult n1 n2), f').
            eapply StepPlug with (E := ECHole); try eapply PlugHole.
            econstructor; eauto.
            repeat rewrite interp_time_distr in Hle.
            repeat (eapply Time_add_le_elim in Hle; destruct Hle as (Hle & ?)).
            eauto.
          }
        }
        {
          destruct He2 as (((h' & e') & f') & Hstep).
          invert Hstep.
          right.
          exists (h', EPrim opr e1 e', f').
          eapply StepPlug with (E := ECBinOp2 _ e1 E); repeat econstructor; eauto.
        }
      }
      {
        destruct He1 as (((h' & e') & f') & Hstep).
        invert Hstep.
        right.
        exists (h', EPrim opr e' e2, f').
        eapply StepPlug with (E := ECBinOp1 _ E e2); repeat econstructor; eauto.
      }
    }
    {
      (* Case Ty1NatAdd *)
      intros ? ? ? h f Hhty Hle HC.
      destruct C as (((L & K) & W) & G).
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
      eapply IHtyping1_1 in Hi1; eauto.
      destruct Hi1 as [He1 | He1]; simpl in *.
      {
        eapply IHtyping1_2 in Hi2; eauto.
        destruct Hi2 as [He2 | He2]; simpl in *.
        {
          set (f' := (f - nat_add_cost)%time).
          simpl in *.
          eapply canon_TNat in He1; eauto.
          subst.
          eapply canon_TNat in He2; eauto.
          subst.
          right.
          set (n1 := interp_idx j1 [] BSNat) in *.
          set (n2 := interp_idx j2 [] BSNat) in *.
          exists (h, ENat (n1 + n2), f').
          eapply StepPlug with (E := ECHole); try eapply PlugHole.
          econstructor; eauto.
          repeat rewrite interp_time_distr in Hle.
          repeat (eapply Time_add_le_elim in Hle; destruct Hle as (Hle & ?)).
          eauto.
        }
        {
          destruct He2 as (((h' & e') & f') & Hstep).
          invert Hstep.
          right.
          exists (h', ENatAdd e1 e', f').
          eapply StepPlug with (E := ECBinOp2 _ e1 E); repeat econstructor; eauto.
        }
      }
      {
        destruct He1 as (((h' & e') & f') & Hstep).
        invert Hstep.
        right.
        exists (h', ENatAdd e' e2, f').
        eapply StepPlug with (E := ECBinOp1 _ E e2); repeat econstructor; eauto.
      }
    }
    {
      (* Case Ty1eq *)
      destruct C as (((L' & K') & W) & G).
      simplify.
      subst.
      eapply IHtyping1; eauto.
    }
    {
      (* Case Le *)
      destruct C as (((L' & K) & W) & G).
      simplify.
      subst.
      eapply IHtyping1; eauto.
      eapply interp_prop_le_interp_time in H1.
      eauto with time_order.
    }
  Qed.

  Lemma progress W s t i :
    ctyping1 W s t i ->
    unstuck s.
  Proof.
    unfold ctyping1 in *.
    simplify.
    destruct s as ((h & e) & f).
    propositional.
    eapply progress'; eauto.
  Qed.

  Ltac invert_kindings :=
    repeat match goal with
             H : kinding1 _ _ _ _ |- _ => invert1 H
           end.
  
  Lemma tyeq1_unroll L K k t cs t' cs' k' :
    k = KArrows (map fst cs) k' ->
    tyeq1 L (k :: K) t t' k ->
    Forall2 (fun p p' => fst p = fst p' /\ idxeq L (snd p) (snd p') (fst p)) cs cs' ->
    kinding1 L (k :: K) t k ->
    kinding1 L (k :: K) t' k ->
    wellscoped_ss L ->
    tyeq1 L K (unroll k t cs) (unroll k t' cs') k'.
  Proof.
    intros ? Htt' Hcscs' Ht Ht' HL; subst; unfold unroll in *.
    eapply tyeq1_TApps; eauto.
    eapply tyeq1_subst_t_t_eqv_eqv_0; simpl; eauto using kinding1_bkinding.
  Qed.

  Lemma Ty1Sub C e t1 i1 t2 i2 :
    typing1 C e t1 i1 ->
    let L := get_sctx C in
    tyeq1 L (get_kctx C) t1 t2 KType ->
    interp_prop L (i1 <= i2)%idx ->
    kinding1 L (get_kctx C) t2 KType ->
    sorting1 L i2 STime ->
    typing1 C e t2 i2.
  Proof.
    destruct C as (((L' & K) & W) & G).
    simpl; intros.
    eapply Ty1Ty1eq; eauto.
    eapply Ty1Le; eauto.
  Qed.
  
  Lemma wfctx1_wellscoped_ctx L K W G :
    let C := (L, K, W, G) in
    wfctx1 C -> wellscoped_ctx C.
  Proof.
    simpl; unfold wfctx1, wellscoped_ctx; simpl; intros H; openhyp.
    repeat try_split; eauto using wfsorts1_wellscoped_ss.
    {
      eapply fmap_forall_impl; eauto.
      simpl; intros.
      intuition eauto using kinding1_wellscoped_t, sorting1_wellscoped_i.
    }
    {
      eapply Forall_impl; try eassumption.
      eauto using kinding1_wellscoped_t.
    }
  Qed.

  Hint Resolve wfctx1_wellscoped_ctx.
  
  Lemma preservation_atomic s s' :
    astep s s' ->
    forall W t i,
      ctyping1 W s t i ->
      let df := (get_fuel s - get_fuel s')%time in
      (df <= interp_time i)%time /\
      exists W',
        ctyping1 W' s' t (Tminus i (Tconst df)) /\
        (W $<= W').
  Proof.
    invert 1; simplify.
  Lemma invert_typing1_App C e1 e2 t i :
    typing1 C (EApp e1 e2) t i ->
    wfctx1 C ->
    exists t' t2 i1 i2 i3 ,
      let L := get_sctx C in
      tyeq1 (get_sctx C) (get_kctx C) t t' KType /\
      kinding1 L (get_kctx C) t' KType /\
      typing1 C e1 (TArrow t2 i3 t') i1 /\
      typing1 C e2 t2 i2 /\
      interp_prop (get_sctx C) (i1 + i2 + T1 + i3 <= i)%idx.
  Proof.
    induct 1; intros HC; unfold_all;
      destruct C as (((L & K) & W) & G); simpl in *.
    {
      assert (kinding1 L K t KType).
      {
        use_typings.
        invert_kindings.
        eauto.
      }
      repeat eexists_split; try eassumption; eauto using kinding1_bkinding with db_tyeq1.
    }
    {
      copy HC HC'.
      eapply IHtyping1 in HC'; openhyp; repeat eexists_split; try eassumption.
      eapply tyeq1_trans; eauto.
      use_typings.
      invert_kindings.
      eauto using kinding1_bkinding.
    }
    {
      eapply IHtyping1 in HC; openhyp; repeat eexists_split; eauto; eauto with db_tyeq1.
    }
  Qed.  

  Lemma invert_typing1_Abs C e t i :
    typing1 C (EAbs e) t i ->
    wfctx1 C ->
    exists t1 i' t2 ,
      let L := get_sctx C in
      let K := get_kctx C in
      tyeq1 L K t (TArrow t1 i' t2) KType /\
      kinding1 L K (TArrow t1 i' t2) KType /\
      kinding1 (get_sctx C) (get_kctx C) t1 KType /\
      typing1 (add_typing_ctx t1 C) e t2 i'.
  Proof.
    induct 1; intros HC; unfold_all;
      destruct C as (((L & K) & W) & G); simpl in *.
    {
      assert (kinding1 L K (TArrow t1 i t) KType).
      {
        use_typings.
      }
      repeat eexists_split; eauto; eauto using kinding1_bkinding with db_tyeq1.
    }
    {
      copy HC HC'.
      eapply IHtyping1 in HC'; openhyp; repeat eexists_split; try eassumption.
      eapply tyeq1_trans; eauto.
      use_typings.
      invert_kindings.
      eauto using kinding1_bkinding.
    }
    {
      eapply IHtyping1 in HC; openhyp; repeat eexists_split; eauto; eauto with db_tyeq1.
    }
  Qed.  

    {
      (* Case Beta *)
      destruct H as (Hty & Hhty & Hle & HC).
      rename t into f.
      rename t0 into t.
      copy Hty Hty0.
      eapply invert_typing1_App in Hty; eauto.
      destruct Hty as (t' & t2 & i1 & i2 & i3 & Htyeq & Ht' & Hty1 & Hty2 & Hle2).
      simplify.
      copy Hty1 Hty1'.
      eapply invert_typing1_Abs in Hty1; eauto.
      destruct Hty1 as (t1 & i' & t3 & Htyeq2 & Ht1t3 & Hkd & Hty1).
      simplify.
      eapply typing_kinding in Hty0; eauto.
      destruct Hty0 as [? Hi].
  Lemma typing1_kinding1_t L K W G e t i :
    let C := (L, K, W, G) in
    typing1 C e t i ->
    wfctx1 C ->
    kinding1 L K t KType.
  Proof.
    simpl; intros; eapply typing_kinding; eauto.
  Qed.
  
  Lemma typing1_kinding1_i L K W G e t i :
    let C := (L, K, W, G) in
    typing1 C e t i ->
    wfctx1 C ->
    sorting1 L i STime.
  Proof.
    simpl; intros; eapply typing_kinding; eauto.
  Qed.
  
      eapply invert_tyeq_TArrow in Htyeq2; eauto using kinding1_bkinding, typing1_kinding1_t.
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
      repeat try_split; eauto.
      {
        eapply Ty1Sub; try eassumption; simpl.
        {
          eapply typing1_subst0_e_e with (G := []) in Hty1; eauto.
          {
            eapply Ty1Ty1eq; eauto.
          }
          {
            eapply wellscoped_ctx_add_typing1; eauto using kinding1_wellscoped_t.
          }
        }
        {
          simplify.
          eauto using kinding1_bkinding.
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
        {
          repeat (econstructor; simpl; eauto).
        }
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
  Lemma invert_typing1_Unfold C e t2 i :
    typing1 C (EUnfold e) t2 i ->
    wfctx1 C ->
    exists k t1 cs i',
      let L := get_sctx C in
      let K := get_kctx C in
      tyeq1 L K t2 (unroll k t1 cs) KType /\
      kinding1 L K (unroll k t1 cs) KType /\
      typing1 C e (TApps (TRec k t1) cs) i' /\
      interp_prop (get_sctx C) (i' <= i)%idx.
  Proof.
    induct 1; intros HC; unfold_all;
      destruct C as (((L & K) & W) & G); simpl in *.
    {
      assert (kinding1 L K (unroll k t cs) KType).
      {
        use_typings.
        eapply kinding1_TApps_invert in H.
        openhyp.
        invert_kindings.
        eapply kinding1_unroll; eauto.
        unfold wfctx1 in *.
        openhyp.
        eauto using wfsorts1_wellscoped_ss.
      }
      repeat eexists_split; eauto; eauto using kinding1_bkinding with db_tyeq1.
    }
    {
      copy HC HC'.
      eapply IHtyping1 in HC'; openhyp; repeat eexists_split; try eassumption.
      eapply tyeq1_trans; eauto.
      use_typings.
      invert_kindings.
      eauto using kinding1_bkinding.
    }
    {
      eapply IHtyping1 in HC; openhyp; repeat eexists_split; eauto; eauto with db_tyeq1.
    }
  Qed.  

  Lemma invert_typing1_Fold C e t' i :
    typing1 C (EFold e) t' i ->
    wfctx1 C ->
    exists cs k t2 i',
      let L := get_sctx C in
      let K := get_kctx C in
      let t := TApps (TRec k t2) cs in
      tyeq1 L K t' t KType /\
      kinding1 (get_sctx C) (get_kctx C) t KType /\
      typing1 C e (unroll k t2 cs) i' /\
      interp_prop (get_sctx C) (i' <= i)%idx.
  Proof.
    induct 1; intros HC; unfold_all;
      destruct C as (((L & K) & W) & G); simpl in *.
    {
      repeat eexists_split; eauto; eauto with db_tyeq1.
      eapply tyeq1_refl.
      use_typings.
      eapply kinding1_TApps_invert in H.
      openhyp.
      invert_kindings.
      eapply kinding1_bkinding.
      eapply kinding1_TApps; eauto.
    }
    {
      copy HC HC'.
      eapply IHtyping1 in HC'; openhyp; repeat eexists_split; try eassumption.
      eapply tyeq1_trans; eauto.
      use_typings.
      invert_kindings.
      eauto using kinding1_bkinding.
    }
    {
      eapply IHtyping1 in HC; openhyp; repeat eexists_split; eauto; eauto with db_tyeq1.
    }
  Qed.  

    {
      (* Case Unfold-Fold *)
      destruct H as (Hty & Hhty & Hle & HC).
      rename t into f.
      rename t0 into t.
      copy Hty Hty0.
      eapply invert_typing1_Unfold in Hty; eauto.
      destruct Hty as (k & t2 & cs& i' & Htyeq & ? & Hty & Hle2).
      subst.
      simplify.
      subst.
      copy Hty Hty'.
      eapply invert_typing1_Fold in Hty; eauto.
      simplify.
      destruct Hty as (cs' & k' & t2' & i'' & Htyeq2 & Hkd & Hty & Hle3).
      subst.
      simplify.
      eapply typing_kinding in Hty'; eauto.
      destruct Hty' as [Hkd' Hi'].
      copy Hkd Hkd''.
      eapply kinding1_TApps_TRec_invert in Hkd''.
      destruct Hkd'' as (? & Ht2' & Hcs'); subst.
      copy Hkd' Hkd''.
      eapply kinding1_TApps_TRec_invert in Hkd''.
      destruct Hkd'' as (? & Ht2 & Hcs); subst.
      eapply invert_tyeq1_TApps_TRec in Htyeq2; eauto using kinding1_bkinding.
      destruct Htyeq2 as (Hsorteq & Htyeq2 & Htyeqcs).
      rewrite <- Hsorteq in *.
      set (k := map fst cs) in *.
      split.
      {
        rewrite Time_a_minus_a.
        eapply Time_0_le_x.
      }
      exists W.
      repeat try_split; eauto.
      {
        eapply typing_kinding in Hty0; eauto.
        destruct Hty0 as [Ht Hi].
        
        eapply Ty1Sub; simpl; try eassumption.
        {
          (* tyeq1 *)
          simplify.
          eapply tyeq1_sym.
          eapply tyeq1_trans; [eapply Htyeq | | ]; eauto using kinding1_bkinding.
          eapply tyeq1_unroll; eauto.
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
        {
          simplify.
          econstructor; simpl; eauto.
          econstructor.
        }
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
  Lemma invert_typing1_Rec C e t i :
    typing1 C (ERec e) t i ->
    wfctx1 C ->
    exists n e1 t',
      tyeq1 (get_sctx C) (get_kctx C) t t' KType /\
      e = EAbsTIs n (EAbs e1) /\
      kinding1 (get_sctx C) (get_kctx C) t' KType /\
      typing1 (add_typing_ctx t' C) e t' T0.
  Proof.
    induct 1; intros HC; unfold_all;
      destruct C as (((L & K) & W) & G); simpl in *.
    {
      repeat eexists_split; eauto; eauto with db_tyeq1.
      eapply tyeq1_refl.
      use_typings.
      eauto using kinding1_bkinding.
    }
    {
      copy HC HC'.
      eapply IHtyping1 in HC'; openhyp; repeat eexists_split; try eassumption.
      eapply tyeq1_trans; eauto.
      use_typings.
      invert_kindings.
      eauto using kinding1_bkinding.
    }
    {
      eapply IHtyping1 in HC; openhyp; repeat eexists_split; eauto; eauto with db_tyeq1.
    }
  Qed.  

    {
      (* Case Rec *)
      destruct H as (Hty & Hhty & Hle & HC).
      rename t into f.
      rename t0 into t.
      copy Hty Hty0.
      eapply invert_typing1_Rec in Hty; eauto.
      destruct Hty as (n & e1 & t' & Htt' & ? & Hkd & Hty).
      subst.
      simplify.
      split.
      {
        rewrite Time_a_minus_a.
        eapply Time_0_le_x.
      }
      exists W.
      repeat try_split; eauto.
      {
        eapply typing_kinding in Hty0; eauto.
        destruct Hty0 as [Ht Hi].
        
        eapply typing_subst_e_e with (G := []) in Hty; try eassumption.
        {
          eapply Ty1Sub; simpl; try eassumption.
          {
            eauto with db_tyeq1.
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
          {
            simplify.
            econstructor; simpl; eauto.
            econstructor.
          }
        }
        {
          eapply Ty1Ty1eq; eauto.
          econstructor; simpl; eauto.
          eapply Ty1Ty1eq.
          {
            eapply add_typing_ctx_tyeq1; try eassumption; eauto with db_tyeq1.
          }
          {
            simpl; eauto.
          }
          {
            simpl; eauto with db_tyeq1.
          }
        }
        {
          eapply wellscoped_ctx_add_typing1; eauto using kinding1_wellscoped_t.
        }
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
  Lemma invert_typing1_Unpack C e1 e2 t2'' i :
    typing1 C (EUnpack e1 e2) t2'' i ->
    wfctx1 C ->
    exists t2 t i1 k i2 ,
      let L := get_sctx C in
      let K := get_kctx C in
      tyeq1 L K t2'' t2 KType /\
      kinding1 L K t2 KType /\
      typing1 C e1 (TExists k t) i1 /\
      typing1 (add_typing_ctx t (add_kinding_ctx k C)) e2 (shift0_t_t t2) i2 /\
      interp_prop (get_sctx C) (i1 + i2 <= i)%idx.
  Proof.
    induct 1; intros HC; unfold_all;
      destruct C as (((L & K) & W) & G); simpl in *.
    {
      assert (kinding1 L K t2 KType).
      {
        eapply typing_kinding in H0; eauto.
        {
          openhyp.
          eapply kinding1_shift_t_t_rev_1_0; eauto.
        }
        {
          eapply wfctx1_add_typing1; eauto.
          {
            eapply wfctx1_add_kinding1; eauto.
          }
          eapply typing_kinding in H; eauto.
          openhyp.
          invert_kindings.
          eauto.
        }
      }
      repeat eexists_split; try eassumption; eauto using kinding1_bkinding with db_tyeq1.
    }
    {
      copy HC HC'.
      eapply IHtyping1 in HC'; openhyp; repeat eexists_split; try eassumption.
      eapply tyeq1_trans; eauto.
      clear H5.
      use_typings.
      invert_kindings.
      eauto using kinding1_bkinding.
    }
    {
      eapply IHtyping1 in HC; openhyp; repeat eexists_split; eauto; eauto with db_tyeq1.
    }
  Qed.

  Lemma invert_typing1_Pack C c e t i :
    typing1 C (EPack c e) t i ->
    wfctx1 C ->
    exists t1 k i' ,
      let t' := TExists k t1 in
      tyeq1 (get_sctx C) (get_kctx C) t t' KType /\
      kinding1 (get_sctx C) (get_kctx C) t' KType /\
      kinding1 (get_sctx C) (get_kctx C) c k /\
      typing1 C e (subst0_t_t c t1) i' /\
      interp_prop (get_sctx C) (i' <= i)%idx.
  Proof.
    induct 1; intros HC; unfold_all;
      destruct C as (((L & K) & W) & G); simpl in *.
    {
      repeat eexists_split; eauto; eauto with db_tyeq1.
      eapply tyeq1_refl.
      eauto using kinding1_bkinding.
    }
    {
      copy HC HC'.
      eapply IHtyping1 in HC'; openhyp; repeat eexists_split; try eassumption.
      eapply tyeq1_trans; eauto.
      clear H4.
      use_typings.
      invert_kindings.
      eauto using kinding1_bkinding.
    }
    {
      eapply IHtyping1 in HC; openhyp; repeat eexists_split; eauto; eauto with db_tyeq1.
    }
  Qed.

    {
      (* Case Unpack-Pack *)
      destruct H as (Hty & Hhty & Hle & HC).
      rename t into f.
      rename t0 into t.
      copy Hty Hty0.
      eapply typing_kinding in Hty0; eauto.
      destruct Hty0 as [Ht Hi].
      eapply invert_typing1_Unpack in Hty; eauto.
      destruct Hty as (t2 & t0 & i1 & k & i2 & Htyeq & Ht2 & Hty1 & Hty2 & Hle2).
      subst.
      simplify.
      copy Hty1 Hty0.
      eapply typing_kinding in Hty0; eauto.
      destruct Hty0 as [Ht0 Hi1].
      eapply invert_typing1_Pack in Hty1; eauto.
      destruct Hty1 as (t1 & k' & i' & Htyeq2 & Hkd1 & Hkdc' & Htyv & Hle3).
      subst.
      simplify.
      invert Ht0.
      invert Hkd1.
      eapply invert_tyeq1_TQuan in Htyeq2; eauto using kinding1_bkinding.
      destruct Htyeq2 as (? & ? & Htyeq2).
      subst.
      rename k' into k.
      eapply typing1_subst0_t_e with (L := []) in Hty2; eauto.
      Focus 2.
      {
        eapply wfctx1_add_typing1; eauto.
        eapply wfctx1_add_kinding1 with (G := []); eauto.
      }
      Unfocus.
      simplify.
      rewrite fmap_map_subst0_t_ti_shift0 in Hty2.
      repeat rewrite subst0_t_t_shift0 in Hty2.
      assert (Htyv' : typing1 ([], [], W, []) v (subst0_t_t c t0) i').
      {
        eapply Ty1Ty1eq; simpl; eauto.
        {
          eapply kinding1_subst_t_t_0; eauto.
        }
        eapply tyeq1_subst_t_t_0; eauto using kinding1_wellscoped_t, kinding1_bkinding with db_tyeq1.
      }
      eapply typing1_subst0_e_e with (G := []) in Hty2; eauto.
      Focus 2.
      {
        eapply wellscoped_ctx_add_typing1; eauto.
        eapply wellscoped_subst_t_t_0; eauto using kinding1_wellscoped_t.
      }
      Unfocus.
      split.
      {
        rewrite Time_a_minus_a.
        eapply Time_0_le_x.
      }
      exists W.
      repeat try_split; eauto.
      {
        eapply Ty1Sub; try eassumption; simpl.
        {
          (* tyeq1 *)
          eauto with db_tyeq1.
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
        {
          repeat (econstructor; simpl; eauto).
        }
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
  Lemma invert_typing1_UnpackI C e1 e2 t2'' i :
    typing1 C (EUnpackI e1 e2) t2'' i ->
    wfctx1 C ->
    exists t2 t i1 s i2 ,
      let L := get_sctx C in
      let K := get_kctx C in
      tyeq1 L K t2'' t2 KType /\
      kinding1 L K t2 KType /\
      typing1 C e1 (TExistsI s t) i1 /\
      typing1 (add_typing_ctx t (add_sorting_ctx s C)) e2 (shift0_i_t t2) (shift0_i_i i2) /\
      interp_prop (get_sctx C) (i1 + i2 <= i)%idx.
  Proof.
    induct 1; intros HC; unfold_all;
      destruct C as (((L & K) & W) & G); simpl in *.
    {
      assert (kinding1 L K t2 KType).
      {
        eapply typing_kinding in H0; eauto.
        {
          openhyp.
          eapply kinding1_shift_i_t_rev_1_0; eauto.
          unfold wfctx1 in *; openhyp; eauto.
        }
        {
          clear H0.
          use_typings.
          invert_kindings.
          eapply wfctx1_add_typing1; eauto.
          eapply wfctx1_add_sorting1; eauto.
        }
      }
      repeat eexists_split; try eassumption; eauto using kinding1_bkinding with db_tyeq1.
    }
    {
      copy HC HC'.
      eapply IHtyping1 in HC'; openhyp; repeat eexists_split; try eassumption.
      eapply tyeq1_trans; eauto.
      clear H5.
      use_typings.
      invert_kindings.
      eauto using kinding1_bkinding.
    }
    {
      eapply IHtyping1 in HC; openhyp; repeat eexists_split; eauto; eauto with db_tyeq1.
    }
  Qed.

  Lemma invert_typing1_PackI C c e t i :
    typing1 C (EPackI c e) t i ->
    wfctx1 C ->
    exists t1 s i' ,
      let t' := TExistsI s t1 in
      tyeq1 (get_sctx C) (get_kctx C) t t' KType /\
      kinding1 (get_sctx C) (get_kctx C) t' KType /\
      sorting1 (get_sctx C) c s /\
      typing1 C e (subst0_i_t c t1) i' /\
      interp_prop (get_sctx C) (i' <= i)%idx.
  Proof.
    induct 1; intros HC; unfold_all;
      destruct C as (((L & K) & W) & G); simpl in *.
    {
      repeat eexists_split; eauto; eauto with db_tyeq1.
      eapply tyeq1_refl.
      eauto using kinding1_bkinding.
    }
    {
      copy HC HC'.
      eapply IHtyping1 in HC'; openhyp; repeat eexists_split; try eassumption.
      eapply tyeq1_trans; eauto.
      use_typings.
      invert_kindings.
      eauto using kinding1_bkinding.
    }
    {
      eapply IHtyping1 in HC; openhyp; repeat eexists_split; eauto; eauto with db_tyeq1.
    }
  Qed.

    {
      (* Case UnpackI-PackI *)
      destruct H as (Hty & Hhty & Hle & HC).
      rename t into f.
      rename t0 into t.
      copy Hty Hty0.
      eapply typing_kinding in Hty0; eauto.
      destruct Hty0 as [Ht Hi].
      eapply invert_typing1_UnpackI in Hty; eauto.
      destruct Hty as (t2 & t0 & i1 & s & i2 & Htyeq & Ht2 & Hty1 & Hty2 & Hle2).
      subst.
      simplify.
      copy Hty1 Hty0.
      eapply typing_kinding in Hty0; eauto.
      destruct Hty0 as [Ht0 Hi1].
      eapply invert_typing1_PackI in Hty1; eauto.
      destruct Hty1 as (t1 & s' & i' & Htyeq2 & Hkd1 & Hkdc' & Htyv & Hle3).
      subst.
      simplify.
      invert Ht0.
      invert Hkd1.
      eapply invert_tyeq1_TQuanI in Htyeq2; eauto using kinding1_bkinding.
      destruct Htyeq2 as (? & Hss' & Htyeq2).
      assert (Hkdc : sorting1 [] c s).
      {
        eapply Stg1Eq; simpl; eauto.
      }
      eapply typing1_subst0_i_e with (L := []) in Hty2; eauto.
      Focus 2.
      {
        eapply wfctx1_add_typing1; eauto.
        eapply wfctx1_add_sorting1 with (G := []); eauto.
      }
      Unfocus.
      simplify.
      rewrite fmap_map_subst0_i_ti_shift0 in Hty2.
      repeat rewrite subst0_i_t_shift0 in Hty2.
      repeat rewrite subst0_i_i_shift0 in Hty2.
      assert (Htyv' : typing1 ([], [], W, []) v (subst0_i_t c t0) i').
      {
        eapply Ty1Ty1eq; simpl; eauto.
        {
          eapply kinding1_subst_i_t_0; eauto.
        }
        eapply tyeq1_subst_i_t_0; eauto using kinding1_bkinding with db_tyeq1.
        simpl.
        eapply sorteq_get_bsort in Hss'.
        rewrite <- Hss'.
        eauto using kinding1_bkinding'.
      }
      eapply typing1_subst0_e_e with (G := []) in Hty2; eauto.
      Focus 2.
      {
        eapply wellscoped_ctx_add_typing1; eauto.
        eapply wellscoped_subst_i_t_0; eauto using kinding1_wellscoped_t, sorting1_wellscoped_i.
      }
      Unfocus.
      split.
      {
        rewrite Time_a_minus_a.
        eapply Time_0_le_x.
      }
      exists W.
      repeat try_split; eauto.
      {
        eapply Ty1Sub; try eassumption; simpl.
        {
          (* tyeq1 *)
          eauto with db_tyeq1.
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
        {
          repeat (econstructor; simpl; eauto).
        }
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

  Lemma invert_typing1_Const C cn t i :
    typing1 C (EConst cn) t i ->
    wfctx1 C ->
    exists i',
      let K := get_kctx C in
      tyeq1 (get_sctx C) K t (const_type cn) KType /\
      interp_prop (get_sctx C) (i' <= i)%idx.
  Proof.
    induct 1; intros HC; unfold_all;
      destruct C as (((L & K) & W) & G); simpl in *.
    {
      repeat eexists_split; eauto; eauto with db_tyeq1.
      eapply tyeq1_refl.
      cases cn; simpl; repeat econstructor.
    }
    {
      copy HC HC'.
      eapply IHtyping1 in HC'; openhyp; repeat eexists_split; try eassumption.
      eapply tyeq1_trans; eauto.
      use_typings.
      invert_kindings.
      eauto using kinding1_bkinding.
    }
    {
      eapply IHtyping1 in HC; openhyp; repeat eexists_split; eauto; eauto with db_tyeq1.
    }
  Qed.  

  Lemma invert_typing1_Read C e1 e2 t i :
    typing1 C (ERead e1 e2) t i ->
    wfctx1 C ->
    exists t' len j i1 i2,
      let L := get_sctx C in
      let K := get_kctx C in 
      tyeq1 L K t t' KType /\
      kinding1 L K t' KType /\
      typing1 C e1 (TArr t' len) i1 /\
      typing1 C e2 (TNat j) i2 /\
      interp_prop L (j < len)%idx /\
      interp_prop L (i1 + i2 <= i)%idx.
  Proof.
    induct 1; intros HC; unfold_all;
      destruct C as (((L & K) & W) & G); simpl in *.
    {
      assert (kinding1 L K t KType).
      {
        use_typings.
        invert_kindings.
        eauto.
      }
      repeat eexists_split; try eassumption; eauto using kinding1_bkinding with db_tyeq1.
    }
    {
      copy HC HC'.
      eapply IHtyping1 in HC'; openhyp; repeat eexists_split; try eassumption.
      eapply tyeq1_trans; eauto.
      use_typings.
      invert_kindings.
      eauto using kinding1_bkinding.
    }
    {
      eapply IHtyping1 in HC; openhyp; repeat eexists_split; eauto; eauto with db_tyeq1.
    }
  Qed.

  Lemma invert_typing1_Loc C l t i :
    typing1 C (ELoc l) t i ->
    wfctx1 C ->
    exists t' len,
      let L := get_sctx C in
      let K := get_kctx C in
      tyeq1 L K t (TArr t' len) KType /\
      kinding1 L K (TArr t' len) KType /\
      get_hctx C $? l = Some (t', len).
  Proof.
    induct 1; intros HC; unfold_all;
      destruct C as (((L & K) & W) & G); simpl in *.
    {
      assert (kinding1 L K (TArr t i) KType).
      {
        eauto using kctx_elim_kinding1, kctx_elim_sorting1.
      }
      repeat eexists_split; eauto; eauto using kinding1_bkinding with db_tyeq1.
    }
    {
      copy HC HC'.
      eapply IHtyping1 in HC'; openhyp; repeat eexists_split; try eassumption.
      eapply tyeq1_trans; eauto.
      use_typings.
      invert_kindings.
      eauto using kinding1_bkinding.
    }
    {
      eapply IHtyping1 in HC; openhyp; repeat eexists_split; eauto; eauto with db_tyeq1.
    }
  Qed.

    {
      (* Case Read *)
      destruct H as (Hty & Hhty & Hle & HC).
      rename t into f.
      rename t0 into t.
      copy Hty Hty0.
      eapply typing_kinding in Hty0; eauto.
      destruct Hty0 as [Ht Hi].
      eapply invert_typing1_Read in Hty; eauto.
      destruct Hty as (t'' & len & j & i1 & i2 & Htt'' & Ht' & Hty1 & Hty2 & Hle2).
      simplify.
      copy Hty1 Hty0.
      eapply typing_kinding in Hty0; eauto.
      destruct Hty0 as [Ht'' Hi1].
      invert Ht''.
      eapply invert_typing1_Loc in Hty1; eauto.
      destruct Hty1 as (t' & len' & Htyeq & Ht'len' & Hl).
      simplify.
      copy Hhty Hhty0.
      eapply htyping1_elim in Hhty; eauto.
      destruct Hhty as (Hlen & Htyv).
      eapply invert_tyeq1_TArr in Htyeq; eauto using kinding1_bkinding.
      destruct Htyeq as [Htyeq Hlenlen'].
      copy Hty2 Hty0.
      eapply typing_kinding in Hty0; eauto.
      destruct Hty0 as [Hj Hi2].
      invert Hj.
      eapply invert_typing1_Const in Hty2; eauto.
      destruct Hty2 as (i' & Hjn & Hi').
      simplify.
      eapply invert_tyeq1_TNat in Hjn; eauto using kinding1_bkinding; [| repeat econstructor].
      unfold idxeq, interp_prop in Hjn.
      simpl in *.
      repeat rewrite convert_bsort_value_refl_eq in *.
      specialize (Hjn I).
      subst.
      copy H1 Hcmp.
      eapply nth_error_Some_lt in Hcmp.
      eapply nth_error_Forall in Htyv; eauto.
      destruct Htyv as [Hval Htyv].
      split.
      {
        rewrite Time_a_minus_a.
        eapply Time_0_le_x.
      }
      exists W.
      repeat try_split; eauto.
      {
        eapply Ty1Sub; try eassumption; simpl.
        {
          eauto using kinding1_bkinding with db_tyeq1.
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
        {
          repeat (econstructor; simpl; eauto).
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
      Lemma incl_refl K V (m : fmap K V) : m $<= m.
      Proof.
        eapply includes_intro.
        eauto.
      Qed.
      {
        eapply incl_refl.
      }
    }
  Lemma invert_typing1_Write C e1 e2 e3 t i :
    typing1 C (EWrite e1 e2 e3) t i ->
    wfctx1 C ->
    exists t' len j i1 i2 i3,
      let L := get_sctx C in
      tyeq1 L (get_kctx C) t TUnit KType /\
      typing1 C e1 (TArr t' len) i1 /\
      typing1 C e2 (TNat j) i2 /\
      interp_prop L (j < len)%idx /\
      typing1 C e3 t' i3 /\
      interp_prop L (i1 + i2 + i3 <= i)%idx.
  Proof.
    induct 1; intros HC; unfold_all;
      destruct C as (((L & K) & W) & G); simpl in *.
    {
      repeat eexists_split; eauto; eauto with db_tyeq1.
      eapply tyeq1_refl.
      econstructor.
    }
    {
      copy HC HC'.
      eapply IHtyping1 in HC'; openhyp; repeat eexists_split; try eassumption.
      eapply tyeq1_trans; eauto.
      use_typings.
      invert_kindings.
      eauto using kinding1_bkinding.
    }
    {
      eapply IHtyping1 in HC; openhyp; repeat eexists_split; eauto; eauto with db_tyeq1.
    }
  Qed.

    {
      (* Case Write *)
      destruct H as (Hty & Hhty & Hle & HC).
      rename t into f.
      rename t0 into t.
      copy Hty Hty0.
      eapply typing_kinding in Hty0; eauto.
      destruct Hty0 as [Ht Hi].
      eapply invert_typing1_Write in Hty; eauto.
      destruct Hty as (t' & len & j & i1 & i2 & i3 & Htyeq & Hty1 & Hty2 & Hjlen & Hty3 & Hle2).
      simpl in *.
      copy Hty1 Hty0.
      eapply typing_kinding in Hty0; eauto.
      destruct Hty0 as [Ht' Hi1].
      invert Ht'.
      eapply invert_typing1_Loc in Hty1; eauto.
      destruct Hty1 as (t'' & len' & Htyeq2 & Ht''len' & Hl).
      simplify.
      eapply invert_tyeq1_TArr in Htyeq2; eauto using kinding1_bkinding.
      destruct Htyeq2 as [Htyeq2 Hlenlen'].
      copy Hhty Hhty0.
      eapply htyping1_elim in Hhty; eauto.
      destruct Hhty as (Hlen' & Htyvs).
      copy Hty2 Hty0.
      eapply typing_kinding in Hty0; eauto.
      destruct Hty0 as [Hj Hi2].
      invert Hj.
      eapply invert_typing1_Const in Hty2; eauto.
      destruct Hty2 as (i' & Hjn & Hi').
      simplify.
      eapply invert_tyeq1_TNat in Hjn; eauto using kinding1_bkinding; [| repeat econstructor].
      unfold idxeq, interp_prop in Hjn.
      simpl in *.
      repeat rewrite convert_bsort_value_refl_eq in *.
      specialize (Hjn I).
      subst.
      unfold idxeq, interp_prop in Hlenlen'.
      simpl in *.
      specialize (Hlenlen' I).
      copy H2 Hcmp.
      eapply nth_error_lt_Some in Hcmp.
      destruct Hcmp as (v' & Hv').
      eapply nth_error_Forall in Hv'; eauto.
      simpl in *.
      destruct Hv' as [Hval' Htyv'].
      copy Htyv' Hty0.
      eapply typing_kinding in Hty0; eauto.
      destruct Hty0 as [Ht'' ?].
      split.
      {
        rewrite Time_a_minus_a.
        eauto with time_order.
      }
      exists W.
      repeat try_split; eauto.
      {
        eapply Ty1Sub; try eassumption; simpl.
        {
          eapply Ty1ETT.
        }
        {
          eauto with db_tyeq1.
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
        {
          repeat (econstructor; simpl; eauto).
        }
      }
      {
        eapply htyping1_upd; eauto.
        {
          Lemma length_upd_lt A ls n (a : A) :
            n < length ls ->
            length (upd ls n a) = length ls.
          Proof.
            unfold upd.
            induct ls; destruct n; simpl; eauto with db_la.
          Qed.

          rewrite length_upd_lt by la.
          la.
        }
        {
          Lemma In_upd_elim A ls n (v x : A) :
            In x (upd ls n v) ->
            x = v \/ In x ls.
          Proof.
            unfold upd.
            induct ls; destruct n; simpl; intuition eauto with db_la.
            eapply IHls in H0.
            intuition eauto with db_la.
          Qed.
          
          Lemma Forall_upd A P ls n (v : A) :
            Forall P ls ->
            P v ->
            Forall P (upd ls n v).
          Proof.
            unfold upd.
            induct ls; destruct n; simpl; intros Hls; invert Hls; intuition eauto with db_la.
          Qed.

          eapply Forall_upd; eauto.
          split; eauto.
          eapply value_typing1_T0; eauto.
          eapply Ty1Ty1eq; try eassumption; simpl; eauto with db_tyeq1.
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
  Lemma invert_typing1_New C e1 e2 t i :
    typing1 C (ENew e1 e2) t i ->
    wfctx1 C ->
    exists t' len i1 i2 ,
      let L := get_sctx C in
      let K := get_kctx C in
      tyeq1 L K t (TArr t' len) KType /\
      kinding1 L K (TArr t' len) KType /\
      typing1 C e1 t' i1 /\
      typing1 C e2 (TNat len) i2 /\
      interp_prop (get_sctx C) (i1 + i2 <= i)%idx.
  Proof.
    induct 1; intros HC; unfold_all;
      destruct C as (((L & K) & W) & G); simpl in *.
    {
      assert (kinding1 L K (TArr t len) KType).
      {
        use_typings.
        invert_kindings.
        eauto.
      }
      repeat eexists_split; eauto; eauto using kinding1_bkinding with db_tyeq1.
    }
    {
      copy HC HC'.
      eapply IHtyping1 in HC'; openhyp; repeat eexists_split; try eassumption.
      eapply tyeq1_trans; eauto.
      use_typings.
      invert_kindings.
      eauto using kinding1_bkinding.
    }
    {
      eapply IHtyping1 in HC; openhyp; repeat eexists_split; eauto; eauto with db_tyeq1.
    }
  Qed.

    {
      (* Case New *)
      destruct H as (Hty & Hhty & Hle & HC).
      rename t into f.
      rename t0 into t.
      copy Hty Hty0.
      eapply typing_kinding in Hty0; eauto.
      destruct Hty0 as [Ht Hi].
      eapply invert_typing1_New in Hty; eauto.
      destruct Hty as (t' & len & i1 & i2 & Htyeq & Ht'len & Hty1 & Hty2 & Hle2).
      copy Hty1 Hty0.
      eapply typing_kinding in Hty0; eauto.
      destruct Hty0 as [Ht' Hi1].
      simplify.
      copy Hty2 Hty0.
      eapply typing_kinding in Hty0; eauto.
      destruct Hty0 as [Hlen Hi2].
      invert Hlen.
      simplify.
      eapply invert_typing1_Const in Hty2; eauto.
      destruct Hty2 as (i' & Hjn & Hi').
      simplify.
      eapply invert_tyeq1_TNat in Hjn; eauto using kinding1_bkinding; [| repeat econstructor].
      unfold idxeq, interp_prop in Hjn.
      simpl in *.
      repeat rewrite convert_bsort_value_refl_eq in *.
      specialize (Hjn I).
      subst.
      split.
      {
        rewrite Time_a_minus_a.
        eauto with time_order.
      }
      exists (W $+ (l, (t', len))).
      repeat try_split; eauto.
      {
        eapply Ty1Sub; try eassumption; simpl.
        {
          eapply Ty1Loc.
          simplify.
          eauto.
        }
        {
          eauto with db_tyeq1.
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
        {
          repeat (econstructor; simpl; eauto).
        }
      }
      {
        eapply htyping1_new in Hhty; eauto using repeat_length.
        Lemma Forall_repeat A (P : A -> Prop) n a : P a -> Forall P (repeat a n).
        Proof.
          induct n; simpl; eauto.
        Qed.

        eapply Forall_repeat.
        split; eauto.
        eapply value_typing1_T0; eauto.
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
        eapply wfctx1_add_htyping1; eauto.
      }
      {
        eapply includes_intro.
        intros k v' Hk.
        cases (l ==n k); subst.
        {
          assert (HWk : W $? k = None).
          {
            eapply htyping1_elim_None; eauto.
          }
          simplify.
          eauto.
        }
        simplify.
        eauto.
      }
    }
  Lemma invert_typing1_AppT C e c t i :
    typing1 C (EAppT e c) t i ->
    wfctx1 C ->
    exists t' i' k ,
      let L := get_sctx C in
      let K := get_kctx C in
      tyeq1 L K t (subst0_t_t c t') KType /\
      kinding1 L K (subst0_t_t c t') KType /\
      typing1 C e (TForall k t') i' /\
      kinding1 (get_sctx C) (get_kctx C) c k /\
      interp_prop (get_sctx C) (i' <= i)%idx.
  Proof.
    induct 1; intros HC; unfold_all;
      destruct C as (((L & K) & W) & G); simpl in *.
    {
      assert (kinding1 L K (subst0_t_t c t1) KType).
      {
        use_typings.
        invert_kindings.
        eapply kinding1_subst_t_t_0; eauto.
        unfold wfctx1 in *; openhyp; eauto using wfsorts1_wellscoped_ss.
      }
      repeat eexists_split; eauto; eauto using kinding1_bkinding with db_tyeq1.
    }
    {
      copy HC HC'.
      eapply IHtyping1 in HC'; openhyp; repeat eexists_split; try eassumption.
      eapply tyeq1_trans; eauto.
      use_typings.
      invert_kindings.
      eauto using kinding1_bkinding.
    }
    {
      eapply IHtyping1 in HC; openhyp; repeat eexists_split; eauto; eauto with db_tyeq1.
    }
  Qed.

  Lemma invert_typing1_AbsT C e t i :
    typing1 C (EAbsT e) t i ->
    wfctx1 C ->
    exists t' k ,
      let L := get_sctx C in
      let K := get_kctx C in
      tyeq1 L K t (TForall k t') KType /\
      kinding1 L K (TForall k t') KType /\
      value e /\
      typing1 (add_kinding_ctx k C) e t' T0.
  Proof.
    induct 1; intros HC; unfold_all;
      destruct C as (((L & K) & W) & G); simpl in *.
    {
      assert (kinding1 L K (TForall k t) KType).
      {
        use_typings.
        invert_kindings.
        econstructor; eauto.
      }
      repeat eexists_split; eauto; eauto using kinding1_bkinding with db_tyeq1.
    }
    {
      copy HC HC'.
      eapply IHtyping1 in HC'; openhyp; repeat eexists_split; try eassumption.
      eapply tyeq1_trans; eauto.
      use_typings.
      invert_kindings.
      eauto using kinding1_bkinding.
    }
    {
      eapply IHtyping1 in HC; openhyp; repeat eexists_split; eauto; eauto with db_tyeq1.
    }
  Qed.

  Hint Resolve kinding1_bkinding'.
  
    {
      (* Case AppT *)
      destruct H as (Hty & Hhty & Hle & HC).
      rename t into f.
      rename t0 into t.
      copy Hty Hty0.
      eapply typing_kinding in Hty0; eauto.
      destruct Hty0 as [Ht Hi].
      eapply invert_typing1_AppT in Hty; eauto.
      destruct Hty as (t' & i' & k' & Htyeq & Hct' & Hty & Hkdc & Hle2).
      simplify.
      copy Hty Hty0.
      eapply typing_kinding in Hty0; eauto.
      destruct Hty0 as [Ht' Hi'].
      invert Ht'.
      eapply invert_typing1_AbsT in Hty; eauto.
      destruct Hty as (t'' & k & Htyeq2 & Ht'' & Hval & Hty).
      simplify.
      eapply invert_tyeq1_TQuan in Htyeq2; eauto.
      destruct Htyeq2 as (? & ? & Htyeq2).
      subst.
      split.
      {
        rewrite Time_a_minus_a.
        eauto with time_order.
      }
      exists W.
      repeat try_split; eauto.
      {
        eapply Ty1Sub; try eassumption; simpl.
        {
          eapply typing1_subst0_t_e with (G := []) in Hty; eauto.
          {
            simplify.
            rewrite fmap_map_subst0_t_ti_shift0 in Hty.
            eauto.
          }
          {
            eapply wfctx1_add_kinding1 with (G := []); eauto.
          }
        }
        {
          simplify.
          (* tyeq1 *)
          eapply tyeq1_sym.
          eapply tyeq1_trans; [eapply Htyeq | |]; eauto.
          eapply tyeq1_subst_t_t_0; eauto using kinding1_wellscoped_t with db_tyeq1.
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
        {
          repeat (econstructor; simpl; eauto).
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
  Lemma invert_typing1_AppI C e c t i :
    typing1 C (EAppI e c) t i ->
    wfctx1 C ->
    exists t' i' s,
      let L := get_sctx C in
      let K := get_kctx C in
      tyeq1 L K t (subst0_i_t c t') KType /\
      kinding1 L K (subst0_i_t c t') KType /\
      typing1 C e (TForallI s t') i' /\
      sorting1 (get_sctx C) c s /\
      interp_prop (get_sctx C) (i' <= i)%idx.
  Proof.
    induct 1; intros HC; unfold_all;
      destruct C as (((L & K) & W) & G); simpl in *.
    {
      assert (kinding1 L K (subst0_i_t c t) KType).
      {
        use_typings.
        invert_kindings.
        eapply kinding1_subst_i_t_0; eauto using sorting1_bsorting.
        unfold wfctx1 in *; openhyp; eauto using wfsorts1_wellscoped_ss.
      }
      repeat eexists_split; eauto; eauto with db_tyeq1.
    }
    {
      copy HC HC'.
      eapply IHtyping1 in HC'; openhyp; repeat eexists_split; try eassumption.
      eapply tyeq1_trans; eauto.
      use_typings.
    }
    {
      eapply IHtyping1 in HC; openhyp; repeat eexists_split; eauto; eauto with db_tyeq1.
    }
  Qed.

  Lemma invert_typing1_AbsI C e t i :
    typing1 C (EAbsI e) t i ->
    wfctx1 C ->
    exists t' s,
      tyeq1 (get_sctx C) (get_kctx C) t (TForallI s t') KType /\
      kinding1 (get_sctx C) (get_kctx C) (TForallI s t') KType /\
      value e /\
      wfsort1 (map get_bsort (get_sctx C)) s /\
      typing1 (add_sorting_ctx s C) e t' T0.
  Proof.
    induct 1; intros HC; unfold_all;
      destruct C as (((L & K) & W) & G); simpl in *.
    {
      assert (kinding1 L K (TForallI s t) KType).
      {
        use_typings.
        invert_kindings.
        econstructor; eauto.
      }
      repeat eexists_split; eauto; eauto with db_tyeq1.
    }
    {
      copy HC HC'.
      eapply IHtyping1 in HC'; openhyp; repeat eexists_split; try eassumption.
      eapply tyeq1_trans; eauto.
      use_typings.
    }
    {
      eapply IHtyping1 in HC; openhyp; repeat eexists_split; eauto; eauto with db_tyeq1.
    }
  Qed.

    {
      (* Case AppI *)
      destruct H as (Hty & Hhty & Hle & HC).
      rename t into f.
      rename t0 into t.
      copy Hty Hty0.
      eapply typing_kinding in Hty0; eauto.
      destruct Hty0 as [Ht Hi].
      eapply invert_typing1_AppI in Hty; eauto.
      destruct Hty as (t' & i' & s & Htyeq & Hct' & Hty & Hkdc & Hle2).
      simplify.
      copy Hty Hty0.
      eapply typing_kinding in Hty0; eauto.
      destruct Hty0 as [Ht' Hi'].
      invert Ht'.
      eapply invert_typing1_AbsI in Hty; eauto.
      destruct Hty as (t'' & s' & Htyeq2 & Ht'' & Hval & Hs' & Hty).
      simplify.
      eapply invert_tyeq1_TQuanI in Htyeq2; eauto.
      destruct Htyeq2 as (? & Hss' & Htyeq2).
      assert (Hkdck : sorting1 [] c s').
      {
        eapply Stg1Eq; eauto.
        eapply sorteq_sym; eauto.
      }
      split.
      {
        rewrite Time_a_minus_a.
        eauto with time_order.
      }
      exists W.
      repeat try_split; eauto.
      {
        eapply Ty1Sub; try eassumption; simpl.
        {
          eapply typing1_subst0_i_e with (G := []) in Hty; eauto.
          {
            simplify.
            rewrite fmap_map_subst0_i_ti_shift0 in Hty.
            eauto.
          }
          {
            eapply wfctx1_add_sorting1 with (G := []); eauto.
          }
        }
        {
          simplify.
          (* tyeq1 *)
          eapply tyeq1_sym.
          eapply tyeq1_trans; [eapply Htyeq | | ]; eauto.
          invert_kindings.
          eapply tyeq1_subst_i_t_0; eauto using kinding1_wellscoped_t, kinding1_bkinding' with db_tyeq1.
          invert Hss'; simpl in *; eauto.
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
        {
          repeat (econstructor; simpl; eauto).
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
  Lemma invert_typing1_Proj C pr e t i :
    typing1 C (EProj pr e) t i ->
    wfctx1 C ->
    exists t1 t2 i' ,
      tyeq1 (get_sctx C) (get_kctx C) t (proj (t1, t2) pr) KType /\
      kinding1 (get_sctx C) (get_kctx C) t1 KType /\
      kinding1 (get_sctx C) (get_kctx C) t2 KType /\
      typing1 C e (TProd t1 t2) i' /\
      interp_prop (get_sctx C) (i' <= i)%idx.
  Proof.
    induct 1; intros HC; unfold_all;
      destruct C as (((L & K) & W) & G); simpl in *.
    {
      assert (kinding1 L K t1 KType).
      {
        use_typings.
        invert_kindings.
        eauto.
      }
      assert (kinding1 L K t2 KType).
      {
        use_typings.
        invert_kindings.
        eauto.
      }
      exists t1, t2.
      repeat eexists_split; try eassumption; eauto with db_tyeq1.
      cases pr; eauto using kinding1_bkinding'.
    }
    {
      copy HC HC'.
      eapply IHtyping1 in HC'; openhyp.
      exists x, x0.
      repeat eexists_split; try eassumption.
      eapply tyeq1_trans; eauto.
      use_typings.
    }
    {
      eapply IHtyping1 in HC; openhyp; repeat eexists_split; eauto; eauto with db_tyeq1.
    }
  Qed.

  Lemma invert_typing1_Pair C e1 e2 t i :
    typing1 C (EPair e1 e2) t i ->
    wfctx1 C ->
    exists t1 t2 i1 i2 ,
      tyeq1 (get_sctx C) (get_kctx C) t (TProd t1 t2) KType /\
      kinding1 (get_sctx C) (get_kctx C) (TProd t1 t2) KType /\
      typing1 C e1 t1 i1 /\
      typing1 C e2 t2 i2 /\
      interp_prop (get_sctx C) (i1 + i2 <= i)%idx.
  Proof.
    induct 1; intros HC; unfold_all;
      destruct C as (((L & K) & W) & G); simpl in *.
    {
      assert (kinding1 L K (TProd t1 t2) KType).
      {
        use_typings.
        invert_kindings.
        econstructor;
          eauto using kinding1_bkinding'.
      }
      repeat eexists_split; eauto; eauto with db_tyeq1.
    }
    {
      copy HC HC'.
      eapply IHtyping1 in HC'; openhyp; repeat eexists_split; try eassumption.
      eapply tyeq1_trans; eauto.
      use_typings.
    }
    {
      eapply IHtyping1 in HC; openhyp; repeat eexists_split; eauto; eauto with db_tyeq1.
    }
  Qed.

    {
      (* Case Proj-Pair *)
      destruct H as (Hty & Hhty & Hle & HC).
      rename t into f.
      rename t0 into t.
      copy Hty Hty0.
      eapply typing_kinding in Hty0; eauto.
      destruct Hty0 as [Ht Hi].
      eapply invert_typing1_Proj in Hty; eauto.
      destruct Hty as (t1 & t2 & i' & Htyeq & Ht1 & Ht2 & Hty & Hle2).
      simplify.
      copy Hty Hty0.
      eapply typing_kinding in Hty0; eauto.
      destruct Hty0 as [Ht1t2 Hi'].
      invert Ht1t2.
      eapply invert_typing1_Pair in Hty; eauto.
      destruct Hty as (t1' & t2' & i1 & i2 & Htyeq2 & Ht1't2' & Hty1 & Hty2 & Hle3).
      simplify.
      eapply invert_tyeq1_TBinOp in Htyeq2; eauto.
      destruct Htyeq2 as (? & Htyeq2 & Htyeq3).
      split.
      {
        rewrite Time_a_minus_a.
        eauto with time_order.
      }
      exists W.
      repeat try_split; eauto.
      {
        cases pr; simplify.
        {
          eapply Ty1Sub; eauto; simpl.
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
          {
            repeat (econstructor; simpl; eauto).
          }
        }
        {
          eapply Ty1Sub; eauto; simpl.
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
          {
            repeat (econstructor; simpl; eauto).
          }
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
  Lemma invert_typing1_Case C e e1 e2 t i :
    typing1 C (ECase e e1 e2) t i ->
    wfctx1 C ->
    exists t1 t2 i0 i1 i2 t',
      tyeq1 (get_sctx C) (get_kctx C) t t' KType /\
      kinding1 (get_sctx C) (get_kctx C) t' KType /\
      typing1 C e (TSum t1 t2) i0 /\
      typing1 (add_typing_ctx t1 C) e1 t' i1 /\
      typing1 (add_typing_ctx t2 C) e2 t' i2 /\
      interp_prop (get_sctx C) (i0 + Tmax i1 i2 <= i)%idx.
  Proof.
    induct 1; intros HC; unfold_all;
      destruct C as (((L & K) & W) & G); simpl in *.
    {
      assert (kinding1 L K t KType).
      {
        eapply typing_kinding in H; eauto.
        openhyp.
        invert_kindings.
        use_typings.
      }
      repeat eexists_split; try eassumption; eauto with db_tyeq1.
    }
    {
      copy HC HC'.
      eapply IHtyping1 in HC'; openhyp; repeat eexists_split; try eassumption.
      eapply tyeq1_trans; eauto.
      clear H5 H6.
      use_typings.
    }
    {
      eapply IHtyping1 in HC; openhyp; repeat eexists_split; eauto; eauto with db_tyeq1.
    }
  Qed.

  Lemma invert_typing1_Inj C inj e t i :
    typing1 C (EInj inj e) t i ->
    wfctx1 C ->
    exists t' t'' i' ,
      tyeq1 (get_sctx C) (get_kctx C) t (choose (TSum t' t'', TSum t'' t') inj) KType /\
      kinding1 (get_sctx C) (get_kctx C) t' KType /\
      kinding1 (get_sctx C) (get_kctx C) t'' KType /\
      typing1 C e t' i' /\
      kinding1 (get_sctx C) (get_kctx C) t'' KType /\
      interp_prop (get_sctx C) (i' <= i)%idx.
  Proof.
    induct 1; intros HC; unfold_all;
      destruct C as (((L & K) & W) & G); simpl in *.
    {
      assert (kinding1 L K t KType).
      {
        use_typings.
      }
      exists t, t'.
      repeat eexists_split; eauto; eauto with db_tyeq1.
      cases inj; simpl; econstructor; eauto using kinding1_bkinding'.
    }
    {
      copy HC HC'.
      eapply IHtyping1 in HC'; openhyp.
      exists x, x0.
      repeat eexists_split; try eassumption.
      eapply tyeq1_trans; eauto.
      use_typings.
    }
    {
      eapply IHtyping1 in HC; openhyp; repeat eexists_split; eauto; eauto with db_tyeq1.
    }
  Qed.

    {
      (* Case Case-Inj *)
      destruct H as (Hty & Hhty & Hle & HC).
      rename t into f.
      rename t0 into t.
      copy Hty Hty0.
      eapply typing_kinding in Hty0; eauto.
      destruct Hty0 as [Ht Hi].
      eapply invert_typing1_Case in Hty; eauto.
      destruct Hty as (t1 & t2 & i0 & i1 & i2 & t'2 & Htt'2 & Ht'2 & Hty0 & Hty1 & Hty2 & Hle2).
      simplify.
      copy Hty0 Hty0'.
      eapply typing_kinding in Hty0'; eauto.
      destruct Hty0' as [Ht1t2 Hi0].
      invert Ht1t2.
      eapply invert_typing1_Inj in Hty0; eauto.
      destruct Hty0 as (t' & t'' & i' & Htyeq & Ht' & Ht'' & Hty0 & Hkd & Hle3).
      simplify.
      split.
      {
        rewrite Time_a_minus_a.
        eauto with time_order.
      }
      exists W.
      repeat try_split; eauto.
      {
        cases inj; simplify.
        {
          eapply invert_tyeq1_TBinOp in Htyeq; eauto.
          destruct Htyeq as (? & Htyeq1 & Htyeq).
          eapply Ty1Le; eauto.
          {
            eapply typing1_subst0_e_e with (G := []) in Hty1; eauto.
            {
              eapply Ty1Ty1eq; eauto.
            }
            {
              eapply Ty1Ty1eq; eauto.
            }
            {
              eapply wellscoped_ctx_add_typing1; eauto using kinding1_wellscoped_t.
            }
          }
          {
            repeat (econstructor; simpl; eauto).
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
          eapply invert_tyeq1_TBinOp in Htyeq; eauto.
          destruct Htyeq as (? & Htyeq1 & Htyeq).
          eapply Ty1Le; eauto.
          {
            eapply typing1_subst0_e_e with (G := []) in Hty2; eauto.
            {
              eapply Ty1Ty1eq; eauto.
            }
            {
              eapply Ty1Ty1eq; eauto.
            }
            {
              eapply wellscoped_ctx_add_typing1; eauto using kinding1_wellscoped_t.
            }
          }
          {
            repeat (econstructor; simpl; eauto).
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
  Lemma invert_typing1_NatAdd C e1 e2 t i :
    typing1 C (ENatAdd e1 e2) t i ->
    wfctx1 C ->
    exists j1 j2 i1 i2,
      let L := get_sctx C in
      tyeq1 L (get_kctx C) t (TNat (Nadd j1 j2)) KType /\
      typing1 C e1 (TNat j1) i1 /\
      typing1 C e2 (TNat j2) i2 /\
      interp_prop L (i1 + i2 + Tconst nat_add_cost <= i)%idx.
  Proof.
    induct 1; intros HC; unfold_all;
      destruct C as (((L & K) & W) & G); simpl in *.
    {
      repeat eexists_split; eauto; eauto with db_tyeq1.
      eapply tyeq1_refl.
      use_typings.
      invert_kindings.
      econstructor; eauto using kinding1_bkinding', sorting1_bsorting''.
      econstructor; eauto using sorting1_bsorting''.
    }
    {
      copy HC HC'.
      eapply IHtyping1 in HC'; openhyp; repeat eexists_split; try eassumption.
      eapply tyeq1_trans; eauto.
      use_typings.
    }
    {
      eapply IHtyping1 in HC; openhyp; repeat eexists_split; eauto; eauto with db_tyeq1.
    }
  Qed.

    {
      (* Case NatAdd *)
      destruct H as (Hty & Hhty & Hle & HC).
      rename t into f.
      rename t0 into t.
      copy Hty Hty0.
      eapply typing_kinding in Hty0; eauto.
      destruct Hty0 as [Ht Hi].
      eapply invert_typing1_NatAdd in Hty; eauto.
      destruct Hty as (j1 & j2 & i1 & i2 & Hj1j2 & Hty1 & Hty2 & Hle2).
      simplify.
      copy Hty1 Hty0.
      eapply typing_kinding in Hty0; eauto.
      destruct Hty0 as [Hj1 Hi1].
      invert Hj1.
      copy Hty2 Hty0.
      eapply typing_kinding in Hty0; eauto.
      destruct Hty0 as [Hj2 Hi2].
      invert Hj2.
      eapply invert_typing1_Const in Hty1; eauto.
      destruct Hty1 as (i1' & Hj1n1 & Hi1').
      simpl in *.
      eapply invert_typing1_Const in Hty2; eauto.
      destruct Hty2 as (i2' & Hj2n2 & Hi2').
      simpl in *.
      eapply invert_tyeq1_TNat in Hj1n1; eauto; [| repeat econstructor].
      unfold idxeq, interp_prop in Hj1n1.
      simpl in *.
      repeat rewrite convert_bsort_value_refl_eq in *.
      specialize (Hj1n1 I).
      subst.
      eapply invert_tyeq1_TNat in Hj2n2; eauto; [| repeat econstructor].
      unfold idxeq, interp_prop in Hj2n2.
      simpl in *.
      repeat rewrite convert_bsort_value_refl_eq in *.
      specialize (Hj2n2 I).
      subst.
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
      repeat try_split; eauto.
      {
        eapply Ty1Sub; try eassumption; simpl.
        {
          econstructor.
        }
        {
          simpl in *.
          eapply tyeq1_sym.
          eapply tyeq1_trans; [eapply Hj1j2 | | ]; eauto using sorting1_bsorting''.
          {
            econstructor.
            cbn.
            eauto.
          }
          econstructor.
          econstructor;
          eauto using sorting1_bsorting'' with db_tyeq1.
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
          eapply Time_minus_move_left; eauto.
          eapply Time_le_trans; [| eapply Hle2'].
          cancel.
          repeat rewrite interp_time_0 in *.
          eauto with time_order.
        }
        {
          repeat (econstructor; simpl; eauto).
        }
      }
      {
        rewrite Time_minus_minus_cancel by eauto.
        rewrite interp_time_minus_distr.
        rewrite interp_time_const.
        eapply Time_minus_cancel.
        eauto.
      }
      {
        eapply includes_intro.
        eauto.
      }
    }
  Lemma invert_typing1_BinOpPrim C opr e1 e2 t i :
    typing1 C (EBinOp (EBPrim opr) e1 e2) t i ->
    wfctx1 C ->
    exists i1 i2,
      let L := get_sctx C in
      tyeq1 L (get_kctx C) t (prim_result_type opr) KType /\
      kinding1 L (get_kctx C) (prim_result_type opr) KType /\
      typing1 C e1 (prim_arg1_type opr) i1 /\
      typing1 C e2 (prim_arg2_type opr) i2 /\
      interp_prop L (i1 + i2 + Tconst (prim_cost opr) <= i)%idx.
  Proof.
    induct 1; intros HC; unfold_all;
      destruct C as (((L & K) & W) & G); simpl in *.
    {
      assert (kinding1 L K (prim_result_type opr) KType).
      {
        use_typings.
      }
      repeat eexists_split; eauto; eauto with db_tyeq1.
    }
    {
      copy HC HC'.
      eapply IHtyping1 in HC'; openhyp; repeat eexists_split; try eassumption.
      eapply tyeq1_trans; eauto.
      use_typings.
    }
    {
      eapply IHtyping1 in HC; openhyp; repeat eexists_split; eauto; eauto with db_tyeq1.
    }
  Qed.

    {
      (* Case Prim *)
      destruct H as (Hty & Hhty & Hle & HC).
      rename t into f.
      rename t0 into t.
      copy Hty Hty0.
      eapply typing_kinding in Hty0; eauto.
      destruct Hty0 as [Ht Hi].
      eapply invert_typing1_BinOpPrim in Hty; eauto.
      destruct Hty as (i1 & i2 & Htopr & Hopr & Hty1 & Hty2 & Hle2).
      simplify.
      copy Hty1 Hty0.
      eapply typing_kinding in Hty0; eauto.
      destruct Hty0 as [Hj1 Hi1].
      copy Hty2 Hty0.
      eapply typing_kinding in Hty0; eauto.
      destruct Hty0 as [Hj2 Hi2].
      eapply invert_typing1_Const in Hty1; eauto.
      destruct Hty1 as (i1' & Hcn1 & Hi1').
      simpl in *.
      eapply invert_typing1_Const in Hty2; eauto.
      destruct Hty2 as (i2' & Hcn2 & Hi2').
      simpl in *.
      cases opr; simpl in *.
      Arguments exec_prim _ _ _ / .
      
      Lemma invert_tyeq1_TInt_const_type cn :
        tyeq1 [] [] TInt (const_type cn) KType ->
        exists n, cn = ECInt n.
      Proof.
        intros H.
        cases cn; simpl in *; try solve [eapply invert_tyeq1_TConst in H; eauto; dis].
        tyeq1_dis.
        repeat econstructor.
      Qed.

      {
        eapply invert_tyeq1_TInt_const_type in Hcn1.
        destruct Hcn1 as [n1 ?].
        subst.
        eapply invert_tyeq1_TInt_const_type in Hcn2.
        destruct Hcn2 as [n2 ?].
        subst.
        simpl in *.
        invert H1.
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
        repeat try_split; eauto.
        {
          eapply Ty1Sub; try eassumption; simpl.
          {
            econstructor.
          }
          {
            simpl.
            eauto with db_tyeq1.
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
            eapply Time_minus_move_left; eauto.
            eapply Time_le_trans; [| eapply Hle2'].
            cancel.
            repeat rewrite interp_time_0 in *.
            eauto with time_order.
          }
          {
            repeat (econstructor; simpl; eauto).
          }
        }
        {
          rewrite Time_minus_minus_cancel by eauto.
          rewrite interp_time_minus_distr.
          rewrite interp_time_const.
          eapply Time_minus_cancel.
          eauto.
        }
        {
          eapply includes_intro.
          eauto.
        }
      }
      {
        eapply invert_tyeq1_TInt_const_type in Hcn1.
        destruct Hcn1 as [n1 ?].
        subst.
        eapply invert_tyeq1_TInt_const_type in Hcn2.
        destruct Hcn2 as [n2 ?].
        subst.
        simpl in *.
        invert H1.
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
        repeat try_split; eauto.
        {
          eapply Ty1Sub; try eassumption; simpl.
          {
            econstructor.
          }
          {
            simpl.
            eauto with db_tyeq1.
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
            eapply Time_minus_move_left; eauto.
            eapply Time_le_trans; [| eapply Hle2'].
            cancel.
            repeat rewrite interp_time_0 in *.
            eauto with time_order.
          }
          {
            repeat (econstructor; simpl; eauto).
          }
        }
        {
          rewrite Time_minus_minus_cancel by eauto.
          rewrite interp_time_minus_distr.
          rewrite interp_time_const.
          eapply Time_minus_cancel.
          eauto.
        }
        {
          eapply includes_intro.
          eauto.
        }
      }
    }
  Qed.

  Lemma ectx_typing : forall E e e_all,
      plug E e e_all ->
      forall W t i,
        let C := ([], [], W, []) in  
        typing1 C e_all t i ->
        wfctx1 C ->
        exists t1 i1,
          typing1 C e t1 i1 /\
          interp_prop [] (i1 <= i)%idx /\
          forall e' e_all' W' i1',
            let C' := ([], [], W', []) in  
            plug E e' e_all' ->
            typing1 C' e' t1 i1' ->
            interp_prop [] (i1' <= i1)%idx ->
            W $<= W' ->
            wfctx1 C' ->
            typing1 C' e_all' t (i1' + Tminus i i1)%idx.
  Proof.
    simpl.
    induct 1; try rename t into t'; try rename i into i'; intros W t i Hty HC.
    {
      exists t, i.
      repeat split; eauto.
      {
        eapply interp_time_interp_prop_le.
        eauto with time_order.
      }
      intros.
      invert H.
      eapply Ty1Le; eauto; simpl.
      {
        eapply typing_kinding in Hty; eauto.
        eapply typing_kinding in H0; eauto.
        openhyp.
        repeat (econstructor; simpl; eauto).
      }
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
        copy Hty Hty0.
        eapply typing_kinding in Hty0; eauto.
        destruct Hty0 as [Ht Hi].
        eapply invert_typing1_Proj in Hty; eauto.
        destruct Hty as (t1 & t2 & i' & Htyeq & Ht1 & Ht2 & Hty & Hle).
        simplify.
        copy Hty Hty0.
        eapply typing_kinding in Hty0; eauto.
        destruct Hty0 as [Ht1t2 Hi'].
        invert Ht1t2.
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
        intros e'' e_all' W' i1' Hplug Htye'' Hle3 Hincl HC'.
        invert Hplug.
        rename e'0 into e_all''.
        rename H5 into Hplug.
        eapply HE in Hplug; eauto.
        copy Hplug Hty0.
        eapply typing_kinding in Hty0; eauto.
        destruct Hty0 as [Ht1t2 Hi1'].
        invert Ht1t2.
        eapply sorting1_bsorting in Hi1'.
        invert Hi1'.
        invert H9.
        eapply Ty1Sub; try eassumption; simpl.
        {
          eapply Ty1Proj; eauto.
        }
        {
          eauto with db_tyeq1.
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
        {
          eapply bsorting_sorting1_SBaseSort; eauto.
          repeat (econstructor; simpl; eauto using sorting1_bsorting'').
        }
      }
      {
        (* Case Inj *)
        copy Hty Hty0.
        eapply typing_kinding in Hty0; eauto.
        destruct Hty0 as [Ht Hi].
        eapply invert_typing1_Inj in Hty; eauto.
        destruct Hty as (t1 & t2 & i' & Htyeq & Ht1 & Ht2 & Hty & Hkd & Hle).
        simplify.
        copy Hty Hty0.
        eapply typing_kinding in Hty0; eauto.
        destruct Hty0 as [? Hi'].
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
        intros e'' e_all' W' i1' Hplug Htye'' Hle3 Hincl HC'.
        invert Hplug.
        rename e'0 into e_all''.
        rename H5 into Hplug.
        eapply HE in Hplug; eauto.
        copy Hplug Hty0.
        eapply typing_kinding in Hty0; eauto.
        destruct Hty0 as [? Hi1'].
        eapply sorting1_bsorting in Hi1'.
        invert Hi1'.
  Ltac invert_bsortings :=
    repeat match goal with
             H : bsorting _ _ _ |- _ => invert1 H
           end.
  
        invert_bsortings.
        (* invert H6. *)
        simpl in *.
        cases inj; simplify.
        {
          eapply Ty1Sub; try eassumption; simpl.
          {
            eapply Ty1Inj with (t' := t2); eauto.
          }
          {
            simpl.
            eauto with db_tyeq1.
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
          {
            eapply bsorting_sorting1_SBaseSort; eauto.
            repeat (econstructor; simpl; eauto using sorting1_bsorting'').
          }
        }
        {
          eapply Ty1Sub; try eassumption; simpl.
          {
            eapply Ty1Inj with (t' := t2); eauto.
          }
          {
            simpl.
            eauto with db_tyeq1.
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
          {
            eapply bsorting_sorting1_SBaseSort; eauto.
            repeat (econstructor; simpl; eauto using sorting1_bsorting'').
          }
        }
      }
      {
        (* Case Fold *)
        copy Hty Hty0.
        eapply typing_kinding in Hty0; eauto.
        destruct Hty0 as [Ht Hi].
        eapply invert_typing1_Fold in Hty; eauto.
        simpl in *.
        destruct Hty as (cs & k & t2 & i' & Htyeq & Hkd & Hty & Hle).
        subst.
        simplify.
        copy Hty Hty0.
        eapply typing_kinding in Hty0; eauto.
        destruct Hty0 as [Ht2 Hi'].
        unfold unroll in *.
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
        intros e'' e_all' W' i1' Hplug Htye'' Hle3 Hincl HC'.
        invert Hplug.
        rename e'0 into e_all''.
        rename H4 into Hplug.
        eapply HE in Hplug; eauto.
        copy Hplug Hty0.
        eapply typing_kinding in Hty0; eauto.
        destruct Hty0 as [? Hi1'].
        eapply sorting1_bsorting in Hi1'.
        invert Hi1'.
        invert_bsortings.
        simpl in *.
        eapply Ty1Sub; try eassumption; simpl.
        {
          eapply Ty1Fold; eauto.
        }
        {
          eauto with db_tyeq1.
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
        {
          eapply bsorting_sorting1_SBaseSort; eauto.
          repeat (econstructor; simpl; eauto using sorting1_bsorting'').
        }
      }
      {
        (* Case Unfold *)
        copy Hty Hty0.
        eapply typing_kinding in Hty0; eauto.
        destruct Hty0 as [Ht Hi].
        eapply invert_typing1_Unfold in Hty; eauto.
        destruct Hty as (k & t1 & cs & i' & Htyeq & Ht1cs & Hty & Hle).
        subst.
        simplify.
        copy Hty Hty0.
        eapply typing_kinding in Hty0; eauto.
        destruct Hty0 as [Ht1 Hi'].
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
        intros e'' e_all' W' i1' Hplug Htye'' Hle3 Hincl HC'.
        invert Hplug.
        rename e'0 into e_all''.
        rename H4 into Hplug.
        eapply HE in Hplug; eauto.
        copy Hplug Hty0.
        eapply typing_kinding in Hty0; eauto.
        destruct Hty0 as [? Hi1'].
        eapply sorting1_bsorting in Hi1'.
        invert Hi1'.
        invert_bsortings.
        simpl in *.
        eapply Ty1Sub; try eassumption; simpl.
        {
          eapply Ty1Unfold; eauto.
        }
        {
          eauto with db_tyeq1.
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
        {
          eapply bsorting_sorting1_SBaseSort; eauto.
          repeat (econstructor; simpl; eauto using sorting1_bsorting'').
        }
      }
    }
    {
      cases opr.
      {
        (* Case BinOpPrim *)
        copy Hty Hty0.
        eapply typing_kinding in Hty0; eauto.
        destruct Hty0 as [Ht Hi].
        eapply invert_typing1_BinOpPrim in Hty; eauto.
        destruct Hty as (i1 & i2 & Htopr & Hopr & Hty1 & Hty2 & Hle).
        simplify.
        copy Hty1 Hty0.
        eapply typing_kinding in Hty0; eauto.
        destruct Hty0 as [Ht' Hi1].
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
        intros e'' e_all' W' i1' Hplug Htye'' Hle3 Hincl HC'.
        invert Hplug.
        rename e'0 into e_all''.
        rename H5 into Hplug.
        eapply HE in Hplug; eauto.
        copy Hplug Hty0.
        eapply typing_kinding in Hty0; eauto.
        destruct Hty0 as [? Hi1'].
        eapply sorting1_bsorting in Hi1'.
        invert Hi1'.
        invert_bsortings.
        simpl in *.
        eapply Ty1Sub; try eassumption; simpl.
        {
          eapply Ty1Prim; eauto.
          eapply weaken_W; eauto.
        }
        {
          eauto with db_tyeq1.
        }
        {
          simplify.
          eapply interp_time_interp_prop_le.
          repeat rewrite interp_time_distr.
          rotate_rhs.
          do 3 rotate_lhs.
          cancel.
          do 2 rotate_lhs.
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
        {
          eapply bsorting_sorting1_SBaseSort; eauto.
          repeat (econstructor; simpl; eauto using sorting1_bsorting'').
        }
      }
      {
        (* Case App *)
        copy Hty Hty0.
        eapply typing_kinding in Hty0; eauto.
        destruct Hty0 as [Ht Hi].
        eapply invert_typing1_App in Hty; eauto.
        destruct Hty as (t' & t2 & i1 & i2 & i3 & Htyeq & Ht' & Hty1 & Hty2 & Hle).
        simplify.
        copy Hty1 Hty0.
        eapply typing_kinding in Hty0; eauto.
        destruct Hty0 as [Ht'2 Hi1].
        invert Ht'2.
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
        intros e'' e_all' W' i1' Hplug Htye'' Hle3 Hincl HC'.
        invert Hplug.
        rename e'0 into e_all''.
        rename H8 into Hplug.
        eapply HE in Hplug; eauto.
        copy Hplug Hty0.
        eapply typing_kinding in Hty0; eauto.
        destruct Hty0 as [? Hi1'].
        eapply sorting1_bsorting in Hi1'.
        invert Hi1'.
        invert_bsortings.
        simpl in *.
        eapply Ty1Sub; try eassumption; simpl.
        {
          eapply Ty1App; eauto.
          eapply weaken_W; eauto.
        }
        {
          eauto with db_tyeq1.
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
        {
          eapply bsorting_sorting1_SBaseSort; eauto.
          repeat (econstructor; simpl; eauto using sorting1_bsorting'').
        }
      }
      {
        (* Case Pair *)
        copy Hty Hty0.
        eapply typing_kinding in Hty0; eauto.
        destruct Hty0 as [Ht Hi].
        eapply invert_typing1_Pair in Hty; eauto.
        destruct Hty as (t1 & t2 & i1 & i2 & Htyeq & Ht1t2 & Hty1 & Hty2 & Hle).
        simplify.
        copy Hty1 Hty0.
        eapply typing_kinding in Hty0; eauto.
        destruct Hty0 as [Ht1 Hi1].
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
        intros e'' e_all' W' i1' Hplug Htye'' Hle3 Hincl HC'.
        invert Hplug.
        rename e'0 into e_all''.
        rename H5 into Hplug.
        eapply HE in Hplug; eauto.
        copy Hplug Hty0.
        eapply typing_kinding in Hty0; eauto.
        destruct Hty0 as [? Hi1'].
        eapply sorting1_bsorting in Hi1'.
        invert Hi1'.
        invert_bsortings.
        simpl in *.
        eapply Ty1Sub; try eassumption; simpl.
        {
          eapply Ty1Pair; eauto.
          eapply weaken_W; eauto.
        }
        {
          eauto with db_tyeq1.
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
        {
          eapply bsorting_sorting1_SBaseSort; eauto.
          repeat (econstructor; simpl; eauto using sorting1_bsorting'').
        }
      }
      {
        (* Case New *)
        copy Hty Hty0.
        eapply typing_kinding in Hty0; eauto.
        destruct Hty0 as [Ht Hi].
        eapply invert_typing1_New in Hty; eauto.
        destruct Hty as (t' & len & i1 & i2 & Htyeq & Ht'len & Hty1 & Hty2 & Hle).
        simplify.
        copy Hty1 Hty0.
        eapply typing_kinding in Hty0; eauto.
        destruct Hty0 as [Ht' Hi1].
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
        intros e'' e_all' W' i1' Hplug Htye'' Hle3 Hincl HC'.
        invert Hplug.
        rename e'0 into e_all''.
        rename H5 into Hplug.
        eapply HE in Hplug; eauto.
        copy Hplug Hty0.
        eapply typing_kinding in Hty0; eauto.
        destruct Hty0 as [? Hi1'].
        eapply sorting1_bsorting in Hi1'.
        invert Hi1'.
        invert_bsortings.
        simpl in *.
        eapply Ty1Sub; try eassumption; simpl.
        {
          eapply Ty1New; eauto.
          eapply weaken_W; eauto.
        }
        {
          eauto with db_tyeq1.
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
        {
          eapply bsorting_sorting1_SBaseSort; eauto.
          repeat (econstructor; simpl; eauto using sorting1_bsorting'').
        }
      }
      {
        (* Case Read *)
        copy Hty Hty0.
        eapply typing_kinding in Hty0; eauto.
        destruct Hty0 as [Ht Hi].
        eapply invert_typing1_Read in Hty; eauto.
        destruct Hty as (t'' & len & j & i1 & i2 & Htt'' & Ht'' & Hty1 & Hty2 & Hjlen & Hle).
        simplify.
        copy Hty1 Hty0.
        eapply typing_kinding in Hty0; eauto.
        destruct Hty0 as [Ht' Hi'].
        invert Ht'.
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
        intros e'' e_all' W' i1' Hplug Htye'' Hle3 Hincl HC'.
        invert Hplug.
        rename e'0 into e_all''.
        rename H7 into Hplug.
        eapply HE in Hplug; eauto.
        copy Hplug Hty0.
        eapply typing_kinding in Hty0; eauto.
        destruct Hty0 as [? Hi1'].
        eapply sorting1_bsorting in Hi1'.
        invert Hi1'.
        invert_bsortings.
        simpl in *.
        eapply Ty1Sub; try eassumption; simpl.
        {
          eapply Ty1Read; eauto.
          eapply weaken_W; eauto.
        }
        {
          eauto with db_tyeq1.
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
        {
          eapply bsorting_sorting1_SBaseSort; eauto.
          repeat (econstructor; simpl; eauto using sorting1_bsorting'').
        }
      }
      {
        (* Case NatAdd *)
        copy Hty Hty0.
        eapply typing_kinding in Hty0; eauto.
        destruct Hty0 as [Ht Hi].
        eapply invert_typing1_NatAdd in Hty; eauto.
        destruct Hty as (j1 & j2 & i1 & i2 & Hj1j2 & Hty1 & Hty2 & Hle).
        simplify.
        copy Hty1 Hty0.
        eapply typing_kinding in Hty0; eauto.
        destruct Hty0 as [Ht' Hi1].
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
        intros e'' e_all' W' i1' Hplug Htye'' Hle3 Hincl HC'.
        invert Hplug.
        rename e'0 into e_all''.
        rename H5 into Hplug.
        eapply HE in Hplug; eauto.
        copy Hplug Hty0.
        eapply typing_kinding in Hty0; eauto.
        destruct Hty0 as [? Hi1'].
        eapply sorting1_bsorting in Hi1'.
        invert Hi1'.
        invert_bsortings.
        simpl in *.
        eapply Ty1Sub; try eassumption; simpl.
        {
          eapply Ty1NatAdd; eauto.
          eapply weaken_W; eauto.
        }
        {
          eauto with db_tyeq1.
        }
        {
          simplify.
          eapply interp_time_interp_prop_le.
          repeat rewrite interp_time_distr.
          rotate_rhs.
          do 3 rotate_lhs.
          cancel.
          do 2 rotate_lhs.
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
        {
          eapply bsorting_sorting1_SBaseSort; eauto.
          repeat (econstructor; simpl; eauto using sorting1_bsorting'').
        }
      }
    }
    {
      (* Case BinOp2 *)
      cases opr.
      {
        (* Case BinOpPrim *)
        copy Hty Hty0.
        eapply typing_kinding in Hty0; eauto.
        destruct Hty0 as [Ht Hi].
        eapply invert_typing1_BinOpPrim in Hty; eauto.
        destruct Hty as (i1 & i2 & Htopr & Hopr & Hty1 & Hty2 & Hle).
        simplify.
        copy Hty2 Hty0.
        eapply typing_kinding in Hty0; eauto.
        destruct Hty0 as [Ht2 Hi2].
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
        intros e'' e_all' W' i1' Hplug Htye'' Hle3 Hincl HC'.
        invert Hplug.
        rename e'0 into e_all''.
        rename H6 into Hplug.
        eapply HE in Hplug; eauto.
        copy Hplug Hty0.
        eapply typing_kinding in Hty0; eauto.
        destruct Hty0 as [? Hi1'].
        eapply sorting1_bsorting in Hi1'.
        invert Hi1'.
        invert_bsortings.
        simpl in *.
        eapply Ty1Sub; try eassumption; simpl.
        {
          eapply Ty1Prim'; eauto.
          eapply weaken_W; eauto.
        }
        {
          eauto with db_tyeq1.
        }
        {
          simplify.
          eapply interp_time_interp_prop_le.
          repeat rewrite interp_time_distr.
          repeat rewrite Time_add_assoc.
          rotate_rhs.
          do 2 rotate_lhs.
          cancel.
          do 2 rotate_lhs.
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
        {
          eapply bsorting_sorting1_SBaseSort; eauto.
          repeat (econstructor; simpl; eauto using sorting1_bsorting'').
        }
      }
      {
        (* Case App *)
        copy Hty Hty0.
        eapply typing_kinding in Hty0; eauto.
        destruct Hty0 as [Ht Hi].
        eapply invert_typing1_App in Hty; eauto.
        destruct Hty as (t' & t2 & i1 & i2 & i3 & Htyeq & Ht' & Hty1 & Hty2 & Hle).
        simplify.
        copy Hty2 Hty0.
        eapply typing_kinding in Hty0; eauto.
        destruct Hty0 as [Ht2 Hi2].
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
        intros e'' e_all' W' i1' Hplug Htye'' Hle3 Hincl HC'.
        invert Hplug.
        rename e'0 into e_all''.
        rename H6 into Hplug.
        eapply HE in Hplug; eauto.
        copy Hplug Hty0.
        eapply typing_kinding in Hty0; eauto.
        destruct Hty0 as [? Hi1'].
        eapply sorting1_bsorting in Hi1'.
        invert Hi1'.
        invert_bsortings.
        simpl in *.
        eapply Ty1Sub; try eassumption; simpl.
        {
          eapply Ty1App; eauto.
          eapply weaken_W; eauto.
        }
        {
          eauto with db_tyeq1.
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
        {
          eapply bsorting_sorting1_SBaseSort; eauto.
          repeat (econstructor; simpl; eauto using sorting1_bsorting'').
        }
      }
      {
        (* Case Pair *)
        copy Hty Hty0.
        eapply typing_kinding in Hty0; eauto.
        destruct Hty0 as [Ht Hi].
        eapply invert_typing1_Pair in Hty; eauto.
        destruct Hty as (t1 & t2 & i1 & i2 & Htyeq & Ht1t2 & Hty1 & Hty2 & Hle).
        simplify.
        copy Hty2 Hty0.
        eapply typing_kinding in Hty0; eauto.
        destruct Hty0 as [Ht2 Hi2].
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
        intros e'' e_all' W' i1' Hplug Htye'' Hle3 Hincl HC'.
        invert Hplug.
        rename e'0 into e_all''.
        rename H6 into Hplug.
        eapply HE in Hplug; eauto.
        copy Hplug Hty0.
        eapply typing_kinding in Hty0; eauto.
        destruct Hty0 as [? Hi1'].
        eapply sorting1_bsorting in Hi1'.
        invert Hi1'.
        invert_bsortings.
        simpl in *.
        eapply Ty1Sub; try eassumption; simpl.
        {
          eapply Ty1Pair; eauto.
          eapply weaken_W; eauto.
        }
        {
          eauto with db_tyeq1.
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
        {
          eapply bsorting_sorting1_SBaseSort; eauto.
          repeat (econstructor; simpl; eauto using sorting1_bsorting'').
        }
      }
      {
        (* Case New *)
        copy Hty Hty0.
        eapply typing_kinding in Hty0; eauto.
        destruct Hty0 as [Ht Hi].
        eapply invert_typing1_New in Hty; eauto.
        destruct Hty as (t' & len & i1 & i2 & Htyeq & Ht'len & Hty1 & Hty2 & Hle).
        simplify.
        copy Hty2 Hty0.
        eapply typing_kinding in Hty0; eauto.
        destruct Hty0 as [Ht2 Hi2].
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
        intros e'' e_all' W' i1' Hplug Htye'' Hle3 Hincl HC'.
        invert Hplug.
        rename e'0 into e_all''.
        rename H6 into Hplug.
        eapply HE in Hplug; eauto.
        copy Hplug Hty0.
        eapply typing_kinding in Hty0; eauto.
        destruct Hty0 as [? Hi1'].
        eapply sorting1_bsorting in Hi1'.
        invert Hi1'.
        invert_bsortings.
        simpl in *.
        eapply Ty1Sub; try eassumption; simpl.
        {
          eapply Ty1New; eauto.
          eapply weaken_W; eauto.
        }
        {
          eauto with db_tyeq1.
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
        {
          eapply bsorting_sorting1_SBaseSort; eauto.
          repeat (econstructor; simpl; eauto using sorting1_bsorting'').
        }
      }
      {
        (* Case Read *)
        copy Hty Hty0.
        eapply typing_kinding in Hty0; eauto.
        destruct Hty0 as [Ht Hi].
        eapply invert_typing1_Read in Hty; eauto.
        destruct Hty as (t'' & len & j & i1 & i2 & Htt'' & Ht'' & Hty1 & Hty2 & Hjlen & Hle).
        simplify.
        copy Hty2 Hty0.
        eapply typing_kinding in Hty0; eauto.
        destruct Hty0 as [Ht2 Hi2].
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
        intros e'' e_all' W' i1' Hplug Htye'' Hle3 Hincl HC'.
        invert Hplug.
        rename e'0 into e_all''.
        rename H6 into Hplug.
        eapply HE in Hplug; eauto.
        copy Hplug Hty0.
        eapply typing_kinding in Hty0; eauto.
        destruct Hty0 as [? Hi1'].
        eapply sorting1_bsorting in Hi1'.
        invert Hi1'.
        invert_bsortings.
        simpl in *.
        eapply Ty1Sub; try eassumption; simpl.
        {
          eapply Ty1Read; eauto.
          eapply weaken_W; eauto.
        }
        {
          eauto with db_tyeq1.
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
        {
          eapply bsorting_sorting1_SBaseSort; eauto.
          repeat (econstructor; simpl; eauto using sorting1_bsorting'').
        }
      }
      {
        (* Case NatAdd *)
        copy Hty Hty0.
        eapply typing_kinding in Hty0; eauto.
        destruct Hty0 as [Ht Hi].
        eapply invert_typing1_NatAdd in Hty; eauto.
        destruct Hty as (j1 & j2 & i1 & i2 & Hj1j2 & Hty1 & Hty2 & Hle).
        simplify.
        copy Hty2 Hty0.
        eapply typing_kinding in Hty0; eauto.
        destruct Hty0 as [Ht2 Hi2].
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
        intros e'' e_all' W' i1' Hplug Htye'' Hle3 Hincl HC'.
        invert Hplug.
        rename e'0 into e_all''.
        rename H6 into Hplug.
        eapply HE in Hplug; eauto.
        copy Hplug Hty0.
        eapply typing_kinding in Hty0; eauto.
        destruct Hty0 as [? Hi1'].
        eapply sorting1_bsorting in Hi1'.
        invert Hi1'.
        invert_bsortings.
        simpl in *.
        eapply Ty1Sub; try eassumption; simpl.
        {
          eapply Ty1NatAdd; eauto.
          eapply weaken_W; eauto.
        }
        {
          eauto with db_tyeq1.
        }
        {
          simplify.
          eapply interp_time_interp_prop_le.
          repeat rewrite interp_time_distr.
          repeat rewrite Time_add_assoc.
          rotate_rhs.
          do 2 rotate_lhs.
          cancel.
          do 2 rotate_lhs.
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
        {
          eapply bsorting_sorting1_SBaseSort; eauto.
          repeat (econstructor; simpl; eauto using sorting1_bsorting'').
        }
      }
    }
    {
      (* Case Write1 *)
      copy Hty Hty0.
      eapply typing_kinding in Hty0; eauto.
      destruct Hty0 as [Ht Hi].
      eapply invert_typing1_Write in Hty; eauto.
      destruct Hty as (t' & len & j & i1 & i2 & i3 & Htyeq & Hty1 & Hty2 & Hjlen & Hty3 & Hle).
      simplify.
      copy Hty1 Hty0.
      eapply typing_kinding in Hty0; eauto.
      destruct Hty0 as [Ht' Hi1].
      invert Ht'.
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
      intros e'' e_all' W' i1' Hplug Htye'' Hle3 Hincl HC'.
      invert Hplug.
      rename e'0 into e_all''.
      rename H7 into Hplug.
      eapply HE in Hplug; eauto.
      copy Hplug Hty0.
      eapply typing_kinding in Hty0; eauto.
      destruct Hty0 as [? Hi1'].
      eapply sorting1_bsorting in Hi1'.
      invert Hi1'.
      invert_bsortings.
      simpl in *.
      eapply Ty1Sub; try eassumption; simpl.
      {
        eapply Ty1Write; eauto;
        eapply weaken_W; eauto.
      }
      {
        eauto with db_tyeq1.
      }
      {
        simplify.
        eapply interp_time_interp_prop_le.
        repeat rewrite interp_time_distr.
        repeat rewrite Time_add_assoc.
        rotate_rhs.
        do 3 rotate_lhs.
        cancel.
        do 2 rotate_lhs.
        repeat rewrite interp_time_minus_distr.
        eapply interp_prop_le_interp_time in Hle.
        eapply interp_prop_le_interp_time in Hle2.
        eapply interp_prop_le_interp_time in Hle3.
        rewrite Time_add_minus_assoc by eauto.
        eapply Time_minus_cancel.
        trans_rhs Hle.
        repeat rewrite interp_time_distr.
        do 2 rotate_rhs.
        eauto with time_order.
      }
      {
        eapply bsorting_sorting1_SBaseSort; eauto.
        repeat (econstructor; simpl; eauto using sorting1_bsorting'').
      }
    }
    {
      (* Case Write2 *)
      copy Hty Hty0.
      eapply typing_kinding in Hty0; eauto.
      destruct Hty0 as [Ht Hi].
      eapply invert_typing1_Write in Hty; eauto.
      destruct Hty as (t' & len & j & i1 & i2 & i3 & Htyeq & Hty1 & Hty2 & Hjlen & Hty3 & Hle).
      simplify.
      copy Hty2 Hty0.
      eapply typing_kinding in Hty0; eauto.
      destruct Hty0 as [Ht' Hi2].
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
      intros e'' e_all' W' i1' Hplug Htye'' Hle3 Hincl HC'.
      invert Hplug.
      rename e'0 into e_all''.
      rename H6 into Hplug.
      eapply HE in Hplug; eauto.
      copy Hplug Hty0.
      eapply typing_kinding in Hty0; eauto.
      destruct Hty0 as [? Hi1'].
      eapply sorting1_bsorting in Hi1'.
      invert Hi1'.
      invert_bsortings.
      simpl in *.
      eapply Ty1Sub; try eassumption; simpl.
      {
        eapply Ty1Write; eauto;
        eapply weaken_W; eauto.
      }
      {
        eauto with db_tyeq1.
      }
      {
        simplify.
        eapply interp_time_interp_prop_le.
        repeat rewrite interp_time_distr.
        repeat rewrite Time_add_assoc.
        rotate_rhs.
        do 2 rotate_lhs.
        cancel.
        do 2 rotate_lhs.
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
      {
        eapply bsorting_sorting1_SBaseSort; eauto.
        repeat (econstructor; simpl; eauto using sorting1_bsorting'').
      }
    }
    {
      (* Case Write3 *)
      copy Hty Hty0.
      eapply typing_kinding in Hty0; eauto.
      destruct Hty0 as [Ht Hi].
      eapply invert_typing1_Write in Hty; eauto.
      destruct Hty as (t' & len & j & i1 & i2 & i3 & Htyeq & Hty1 & Hty2 & Hjlen & Hty3 & Hle).
      simplify.
      copy Hty3 Hty0.
      eapply typing_kinding in Hty0; eauto.
      destruct Hty0 as [Ht' Hi3].
      eapply IHplug in Hty3; eauto.
      destruct Hty3 as (t0 & i0 & Hty3 & Hle2 & HE).
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
      intros e'' e_all' W' i1' Hplug Htye'' Hle3 Hincl HC'.
      invert Hplug.
      rename e'0 into e_all''.
      rename H5 into Hplug.
      eapply HE in Hplug; eauto.
      copy Hplug Hty0.
      eapply typing_kinding in Hty0; eauto.
      destruct Hty0 as [? Hi1'].
      eapply sorting1_bsorting in Hi1'.
      invert Hi1'.
      invert_bsortings.
      simpl in *.
      eapply Ty1Sub; try eassumption; simpl.
      {
        eapply Ty1Write; eauto;
        eapply weaken_W; eauto.
      }
      {
        eauto with db_tyeq1.
      }
      {
        simplify.
        eapply interp_time_interp_prop_le.
        repeat rewrite interp_time_distr.
        repeat rewrite Time_add_assoc.
        rotate_rhs.
        do 1 rotate_lhs.
        cancel.
        do 2 rotate_lhs.
        repeat rewrite interp_time_minus_distr.
        eapply interp_prop_le_interp_time in Hle.
        eapply interp_prop_le_interp_time in Hle2.
        eapply interp_prop_le_interp_time in Hle3.
        rewrite Time_add_minus_assoc by eauto.
        eapply Time_minus_cancel.
        trans_rhs Hle.
        repeat rewrite interp_time_distr.
        eauto with time_order.
      }
      {
        eapply bsorting_sorting1_SBaseSort; eauto.
        repeat (econstructor; simpl; eauto using sorting1_bsorting'').
      }
    }
    {
      (* Case Case *)
      copy Hty Hty0.
      eapply typing_kinding in Hty0; eauto.
      destruct Hty0 as [Ht Hi].
      eapply invert_typing1_Case in Hty; eauto.
      destruct Hty as (t1 & t2 & i0' & i1 & i2 & t' & Htt' & Ht' & Hty0 & Hty1 & Hty2 & Hle).
      simplify.
      copy Hty0 Hty0'.
      eapply typing_kinding in Hty0'; eauto.
      destruct Hty0' as [Ht1t2 Hi0'].
      invert Ht1t2.
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
      intros e'' e_all' W' i1' Hplug Htye'' Hle3 Hincl HC'.
      invert Hplug.
      rename e'0 into e_all''.
      rename H7 into Hplug.
      eapply HE in Hplug; eauto.
      copy Hplug Hty0'.
      eapply typing_kinding in Hty0'; eauto.
      destruct Hty0' as [? Hi1'].
      eapply sorting1_bsorting in Hi1'.
      invert Hi1'.
      invert_bsortings.
      simpl in *.
      eapply Ty1Sub; try eassumption; simpl.
      {
        eapply Ty1Case; eauto;
        eapply weaken_W; eauto.
      }
      {
        eauto with db_tyeq1.
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
      {
        eapply bsorting_sorting1_SBaseSort; eauto.
        repeat (econstructor; simpl; eauto using sorting1_bsorting'').
      }
    }
    {
      (* Case AppT *)
      copy Hty Hty0.
      eapply typing_kinding in Hty0; eauto.
      destruct Hty0 as [Ht Hi].
      eapply invert_typing1_AppT in Hty; eauto.
      rename t' into t''.
      destruct Hty as (t' & i' & k & Htyeq & Ht''t' & Hty & Hkd & Hle).
      simplify.
      copy Hty Hty0.
      eapply typing_kinding in Hty0; eauto.
      destruct Hty0 as [Ht' Hi'].
      invert Ht'.
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
      intros e'' e_all' W' i1' Hplug Htye'' Hle3 Hincl HC'.
      invert Hplug.
      rename e'0 into e_all''.
      rename H5 into Hplug.
      eapply HE in Hplug; eauto.
      copy Hplug Hty0'.
      eapply typing_kinding in Hty0'; eauto.
      destruct Hty0' as [? Hi1'].
      eapply sorting1_bsorting in Hi1'.
      invert Hi1'.
      invert_bsortings.
      simpl in *.
      eapply Ty1Sub; try eassumption; simpl.
      {
        eapply Ty1AppT; eauto.
      }
      {
        eauto with db_tyeq1.
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
      {
        eapply bsorting_sorting1_SBaseSort; eauto.
        repeat (econstructor; simpl; eauto using sorting1_bsorting'').
      }
    }
    {
      (* Case AppI *)
      copy Hty Hty0.
      eapply typing_kinding in Hty0; eauto.
      destruct Hty0 as [Ht Hi].
      eapply invert_typing1_AppI in Hty; eauto.
      rename i' into i''.
      destruct Hty as (t' & i' & k & Htyeq & Hi''t' & Hty & Hkd & Hle).
      simplify.
      copy Hty Hty0.
      eapply typing_kinding in Hty0; eauto.
      destruct Hty0 as [Ht' Hi'].
      invert Ht'.
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
      intros e'' e_all' W' i1' Hplug Htye'' Hle3 Hincl HC'.
      invert Hplug.
      rename e'0 into e_all''.
      rename H5 into Hplug.
      eapply HE in Hplug; eauto.
      copy Hplug Hty0'.
      eapply typing_kinding in Hty0'; eauto.
      destruct Hty0' as [? Hi1'].
      eapply sorting1_bsorting in Hi1'.
      invert Hi1'.
      invert_bsortings.
      simpl in *.
      eapply Ty1Sub; try eassumption; simpl.
      {
        eapply Ty1AppI; eauto.
      }
      {
        eauto with db_tyeq1.
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
      {
        eapply bsorting_sorting1_SBaseSort; eauto.
        repeat (econstructor; simpl; eauto using sorting1_bsorting'').
      }
    }
    {
      (* Case Pack *)
      copy Hty Hty0.
      eapply typing_kinding in Hty0; eauto.
      destruct Hty0 as [Ht Hi].
      eapply invert_typing1_Pack in Hty; eauto.
      destruct Hty as (t1 & k & i' & Htyeq & Hkd & Hkdc & Hty & Hle).
      simplify.
      copy Hty Hty0.
      eapply typing_kinding in Hty0; eauto.
      destruct Hty0 as [Ht' Hi'].
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
      intros e'' e_all' W' i1' Hplug Htye'' Hle3 Hincl HC'.
      invert Hplug.
      rename e'0 into e_all''.
      rename H4 into Hplug.
      eapply HE in Hplug; eauto.
      copy Hplug Hty0'.
      eapply typing_kinding in Hty0'; eauto.
      destruct Hty0' as [? Hi1'].
      eapply sorting1_bsorting in Hi1'.
      invert Hi1'.
      invert_bsortings.
      simpl in *.
      eapply Ty1Sub; try eassumption; simpl.
      {
        eapply Ty1Pack; eauto.
      }
      {
        eauto with db_tyeq1.
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
      {
        eapply bsorting_sorting1_SBaseSort; eauto.
        repeat (econstructor; simpl; eauto using sorting1_bsorting'').
      }
    }
    {
      (* Case Unpack *)
      copy Hty Hty0.
      eapply typing_kinding in Hty0; eauto.
      destruct Hty0 as [Ht Hi].
      eapply invert_typing1_Unpack in Hty; eauto.
      destruct Hty as (t2 & t0' & i1 & k & i2 & Htyeq & Ht2 & Hty1 & Hty2 & Hle).
      simplify.
      copy Hty1 Hty0.
      eapply typing_kinding in Hty0; eauto.
      destruct Hty0 as [Ht0' Hi1].
      invert Ht0'.
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
      intros e'' e_all' W' i1' Hplug Htye'' Hle3 Hincl HC'.
      invert Hplug.
      rename e'0 into e_all''.
      rename H5 into Hplug.
      eapply HE in Hplug; eauto.
      copy Hplug Hty0'.
      eapply typing_kinding in Hty0'; eauto.
      destruct Hty0' as [? Hi1'].
      eapply sorting1_bsorting in Hi1'.
      invert Hi1'.
      invert_bsortings.
      simpl in *.
      eapply Ty1Sub with (t1 := t2); try eassumption; simpl.
      {
        eapply Ty1Unpack; eauto.
        simplify.
        assert (Hincl' : fmap_map shift0_t_ti W $<= fmap_map shift0_t_ti W').
        {
          eapply incl_fmap_map; eauto.
        }
        eapply weaken_W; eauto.
      }
      {
        eauto with db_tyeq1.
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
      {
        eapply bsorting_sorting1_SBaseSort; eauto.
        repeat (econstructor; simpl; eauto using sorting1_bsorting'').
      }
    }
    {
      (* Case PackI *)
      copy Hty Hty0.
      eapply typing_kinding in Hty0; eauto.
      destruct Hty0 as [Ht Hi].
      eapply invert_typing1_PackI in Hty; eauto.
      rename i' into i''.
      destruct Hty as (t1 & k & i' & Htyeq & Hkd & Hkdc & Hty & Hle).
      simplify.
      copy Hty Hty0.
      eapply typing_kinding in Hty0; eauto.
      destruct Hty0 as [Ht1 Hi'].
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
      intros e'' e_all' W' i1' Hplug Htye'' Hle3 Hincl HC'.
      invert Hplug.
      rename e'0 into e_all''.
      rename H4 into Hplug.
      eapply HE in Hplug; eauto.
      copy Hplug Hty0'.
      eapply typing_kinding in Hty0'; eauto.
      destruct Hty0' as [? Hi1'].
      eapply sorting1_bsorting in Hi1'.
      invert Hi1'.
      invert_bsortings.
      simpl in *.
      eapply Ty1Sub; try eassumption; simpl.
      {
        eapply Ty1PackI; eauto.
      }
      {
        eauto with db_tyeq1.
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
      {
        eapply bsorting_sorting1_SBaseSort; eauto.
        repeat (econstructor; simpl; eauto using sorting1_bsorting'').
      }
    }
    {
      (* Case UnpackI *)
      copy Hty Hty0.
      eapply typing_kinding in Hty0; eauto.
      destruct Hty0 as [Ht Hi].
      eapply invert_typing1_UnpackI in Hty; eauto.
      destruct Hty as (t2 & t0' & i1 & k & i2 & Htyeq & Ht2 & Hty1 & Hty2 & Hle).
      simplify.
      copy Hty1 Hty0.
      eapply typing_kinding in Hty0; eauto.
      destruct Hty0 as [Ht0' Hi1].
      invert Ht0'.
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
      intros e'' e_all' W' i1' Hplug Htye'' Hle3 Hincl HC'.
      invert Hplug.
      rename e'0 into e_all''.
      rename H5 into Hplug.
      eapply HE in Hplug; eauto.
      copy Hplug Hty0'.
      eapply typing_kinding in Hty0'; eauto.
      destruct Hty0' as [? Hi1'].
      eapply sorting1_bsorting in Hi1'.
      invert Hi1'.
      invert_bsortings.
      simpl in *.
      eapply Ty1Sub with (t1 := t2); try eassumption; simpl.
      {
        eapply Ty1UnpackI; eauto.
        simplify.
        assert (Hincl' : fmap_map shift0_i_ti W $<= fmap_map shift0_i_ti W').
        {
          eapply incl_fmap_map; eauto.
        }
        eapply weaken_W; eauto.
      }
      {
        eauto with db_tyeq1.
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
      {
        eapply bsorting_sorting1_SBaseSort; eauto.
        repeat (econstructor; simpl; eauto using sorting1_bsorting'').
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
      ctyping1 W s t i ->
      exists W' i',
        ctyping1 W' s' t i'.
  Proof.
    invert 1.
    (* induct 1. *)
    (* induction 1. *)
    simplify.
    destruct H as (Hty & Hhty & Hle & HC).
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
    eapply ectx_typing in Hty; eauto.
    destruct Hty as (t1 & i1 & Hty & Hle2 & He').
    rename H0 into Hstep.
    eapply preservation_atomic in Hstep; eauto.
    Focus 2.
    {
      unfold ctyping1; repeat try_split; eauto.
      eapply interp_prop_le_interp_time in Hle2.
      eauto with time_order.
    }
    Unfocus.
    simplify.
    destruct Hstep as (Hle3 & W' & Hty2 & Hincl).
    destruct Hty2 as (Hty2 & Hhty' & Hle4 & HC').
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
    ctyping1 W s t i ->
    invariantFor (trsys_of s) unstuck.
  Proof.
    intros H.
    apply invariant_weaken with (invariant1 := fun s' => exists W' i', ctyping1 W' s' t i'); eauto.
    {
      apply invariant_induction; intros s0 Hs0; simplify; eauto.
      {
        propositional.
        subst; simplify.
        eauto.
      }
      {
        destruct Hs0 as (W' & i' & Hty).
        propositional.
        eapply preservation; eauto.
      }
    }
    {
      simplify.
      destruct H0 as (W' & i' & Hty).
      eauto using progress.
    }
  Qed.

  Theorem soundness1 W s t i : ctyping1 W s t i -> safe s.
  Proof.
    intros H.
    eapply unstuck_invariant in H; eauto.
    unfold invariantFor, safe in *.
    intros s' Hstep.
    simplify.
    eauto.
  Qed.

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
  | StgAbs L i b1 b2 :
      sorting (SBaseSort b1 :: L) i (SBaseSort b2) ->
      sorting L (IAbs i) (SArrow b1 b2)
  | StgApp L c1 c2 b1 b2 :
      sorting L c1 (SArrow b1 b2) ->
      sorting L c2 (SBaseSort b1) ->
      sorting L (IApp b1 c1 c2) (SBaseSort b2)
  | StgSubsetI L c b p :
      sorting L c (SBaseSort b) ->
      interp_prop L (subst0_i_p c p) ->
      sorting L c (SSubset b p)
  | StgSubsetE L c b p :
      sorting L c (SSubset b p) ->
      wfprop (SBaseSort b :: L) p ->
      sorting L c (SBaseSort b)

  with wfprop : list sort -> prop -> Prop :=
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
  
  Hint Constructors sorting wfprop.

  Inductive wfsort : list sort -> sort -> Prop :=
  | WfStBaseSort L b :
      wfsort L (SBaseSort b)
  | WfStSubset L b p :
      wfprop (SBaseSort b :: L) p ->
      wfsort L (SSubset b p)
  .

  Hint Constructors wfsort.

  Scheme sorting_mutind := Minimality for sorting Sort Prop
  with wfprop_mutind := Minimality for wfprop Sort Prop.

  Combined Scheme sorting_wfprop_mutind from sorting_mutind, wfprop_mutind.

  Lemma sorting_wfprop_sorting1_wfprop1 :
    (forall L i s,
        sorting L i s ->
        sorting1 L i s
    ) /\
    (forall L p,
        wfprop L p ->
        wfprop1 (map get_bsort L) p
    ).
  Proof.
    eapply sorting_wfprop_mutind; simpl; eauto using sorting1_bsorting'.
  Qed.

  Lemma sorting_sorting1 L i s : sorting L i s -> sorting1 L i s.
  Proof.
    intros; eapply sorting_wfprop_sorting1_wfprop1; eauto.
  Qed.

  Lemma wfprop_wfprop1 L p : wfprop L p -> wfprop1 (map get_bsort L) p.
  Proof.
    intros; eapply sorting_wfprop_sorting1_wfprop1; eauto.
  Qed.

  Lemma wfsort_wfsort1 L s : wfsort L s -> wfsort1 (map get_bsort L) s.
  Proof.
    induct 1; simpl; eauto using wfprop_wfprop1.
    econstructor.
    eapply wfprop_wfprop1 in H.
    eauto.
  Qed.

  Inductive kinding : sctx -> kctx -> ty -> kind -> Prop :=
  | KdgVar L K x k :
      nth_error K x = Some k ->
      kinding L K (TVar x) k
  | KdgConst L K cn :
      kinding L K (TConst cn) KType
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
  | KdgRec L K k c :
      kinding L (k :: K) c k ->
      kinding L K (TRec k c) k
  | KdgNat L K i :
      sorting L i SNat ->
      kinding L K (TNat i) KType
  | KdgArr L K t i :
      kinding L K t KType ->
      sorting L i SNat ->
      kinding L K (TArr t i) KType
  | KdgAbsT L K t k1 k2 :
      kinding L (k1 :: K) t k2 ->
      kinding L K (TAbsT k1 t) (KArrowT k1 k2)
  | KdgAppT L K t1 t2 k1 k2 :
      kinding L K t1 (KArrowT k1 k2) ->
      kinding L K t2 k1 ->
      kinding L K (TAppT t1 t2) k2
  .

  Hint Constructors kinding.

  Lemma kinding_kinding1 L K t k : kinding L K t k -> kinding1 L K t k.
  Proof.
    induct 1; simpl; eauto using sorting_sorting1, wfsort_wfsort1.
  Qed.

  Local Open Scope idx_scope.

  Inductive tyeq : sctx -> kctx -> ty -> ty -> kind -> Prop :=
  (* congruence rules *)
  | TyEqBinOp L K opr t1 t2 t1' t2' :
      tyeq L K t1 t1' KType ->
      tyeq L K t2 t2' KType ->
      tyeq L K (TBinOp opr t1 t2) (TBinOp opr t1' t2') KType
  | TyEqArrow L K t1 i t2 t1' i' t2':
      tyeq L K t1 t1' KType ->
      idxeq L i i' BSTime ->
      tyeq L K t2 t2' KType ->
      tyeq L K (TArrow t1 i t2) (TArrow t1' i' t2') KType
  | TyEqAbs L K b t t' k :
      tyeq (SBaseSort b :: L) K t t' k ->
      tyeq L K (TAbs b t) (TAbs b t') (KArrow b k)
  | TyEqApp L K t b i t' i' k :
      tyeq L K t t' (KArrow b k) ->
      idxeq L i i' b ->
      tyeq L K (TApp t b i) (TApp t' b i') k
  | TyEqQuan L K quan k t t' :
      tyeq L (k :: K) t t' KType ->
      tyeq L K (TQuan quan k t) (TQuan quan k t') KType
  | TyEqQuanI L K quan s t s' t' :
      sorteq L s s' ->
      tyeq (s :: L) K t t' KType ->
      tyeq L K (TQuanI quan s t) (TQuanI quan s' t') KType
  | TyEqRec L K k c c' :
      tyeq L (k :: K) c c' k ->
      tyeq L K (TRec k c) (TRec k c') k
  | TyEqNat L K i i' :
      idxeq L i i' BSNat ->
      tyeq L K (TNat i) (TNat i') KType
  | TyEqArr L K t i t' i' :
      tyeq L K t t' KType ->
      idxeq L i i' BSNat ->
      tyeq L K (TArr t i) (TArr t' i') KType
  | TyEqAbsT L K k t t' k2 :
      tyeq L (k :: K) t t' k2 ->
      tyeq L K (TAbsT k t) (TAbsT k t') (KArrowT k k2)
  | TyEqAppT L K t1 t2 t1' t2' k1 k2 :
      tyeq L K t1 t1' (KArrowT k1 k2) ->
      tyeq L K t2 t2' k1 ->
      tyeq L K (TAppT t1 t2) (TAppT t1' t2') k2
  | TyEqVar L K x k :
      nth_error K x = Some k ->
      tyeq L K (TVar x) (TVar x) k
  | TyEqConst L K cn :
      tyeq L K (TConst cn) (TConst cn) KType
  (* reduction rules *)
  | TyEqBeta L K s t b i k :
      kinding L K (TApp (TAbs s t) b i) k ->
      tyeq L K (TApp (TAbs s t) b i) (subst0_i_t i t) k
  | TyEqBetaT L K k t1 t2 k2 :
      kinding L K (TAppT (TAbsT k t1) t2) k2 ->
      tyeq L K (TAppT (TAbsT k t1) t2) (subst0_t_t t2 t1) k2
  (* structural rules *)
  | TyEqRefl L K t k :
      kinding L K t k ->
      tyeq L K t t k
  | TyEqSym L K a b k :
      tyeq L K a b k ->
      tyeq L K b a k
  | TyEqTrans L K a b c k :
      tyeq L K a b k ->
      tyeq L K b c k ->
      kinding L K b k ->
      tyeq L K a c k
  .

  Hint Constructors tyeq.

  Lemma tyeq_tyeq1 L K t t' k : tyeq L K t t' k -> tyeq1 L K t t' k.
  Proof.
    induct 1; simpl; eauto using kinding_kinding1, kinding1_bkinding'.
  Qed.
  
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
  | TyRec C tis e1 t :
      let e := EAbsTIs tis (EAbs e1) in
      kinding (get_sctx C) (get_kctx C) t KType ->
      typing (add_typing_ctx t C) e t T0 ->
      typing C (ERec e) t T0
  | TyFold C e k t cs i :
      let t_rec := TApps (TRec k t) cs in
      kinding (get_sctx C) (get_kctx C) t_rec KType ->
      typing C e (unroll k t cs) i ->
      typing C (EFold e) t_rec i
  | TyUnfold C e k t cs i :
      typing C e (TApps (TRec k t) cs) i ->
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
  | TyNew C e1 e2 t len i1 i2 :
      typing C e1 t i1 ->
      typing C e2 (TNat len) i2 ->
      typing C (ENew e1 e2) (TArr t len) (i1 + i2)
  | TyRead C e1 e2 t i1 i2 len i :
      typing C e1 (TArr t len) i1 ->
      typing C e2 (TNat i) i2 ->
      interp_prop (get_sctx C) (i < len) ->
      typing C (ERead e1 e2) t (i1 + i2)
  | TyWrite C e1 e2 e3 i1 i2 i3 t len i :
      typing C e1 (TArr t len) i1 ->
      typing C e2 (TNat i) i2 ->
      interp_prop (get_sctx C) (i < len) ->
      typing C e3 t i3 ->
      typing C (EWrite e1 e2 e3) TUnit (i1 + i2 + i3)
  | TyLoc C l t i :
      get_hctx C $? l = Some (t, i) ->
      typing C (ELoc l) (TArr t i) T0
  | TyPrim C opr e1 e2 i1 i2 :
      typing C e1 (prim_arg1_type opr) i1 ->
      typing C e2 (prim_arg2_type opr) i2 ->
      typing C (EPrim opr e1 e2) (prim_result_type opr) (i1 + i2 + Tconst (prim_cost opr))
  | TyNatAdd C e1 e2 j1 j2 i1 i2 :
      typing C e1 (TNat j1) i1 ->
      typing C e2 (TNat j2) i2 ->
      typing C (ENatAdd e1 e2) (TNat (Nadd j1 j2)) (i1 + i2 + Tconst nat_add_cost)
  | TyTyeq C e t1 i t2 :
      typing C e t1 i ->
      let L := get_sctx C in
      let K := get_kctx C in
      kinding L K t2 KType ->
      tyeq L K t1 t2 KType ->
      typing C e t2 i
  | TyLe C e t i1 i2 :
      typing C e t i1 ->
      let L := get_sctx C in
      sorting L i2 STime ->
      interp_prop L (i1 <= i2) ->
      typing C e t i2 
  .

  Hint Constructors typing.
  
  Local Close Scope idx_scope.

  Hint Constructors typing1.
  
  Lemma typing_typing1 C e t i : typing C e t i -> typing1 C e t i.
  Proof.
    induct 1; destruct C as (((L' & K') & W) & G); simpl; unfold_all; eauto using kinding_kinding1, sorting_sorting1, tyeq_tyeq1, wfsort_wfsort1.
  Qed.

  Definition htyping (h : heap) (W : hctx) :=
    (forall l t i,
        W $? l = Some (t, i) ->
        exists vs,
          h $? l = Some vs /\
          length vs = interp_idx i [] BSNat /\
          Forall (fun v => value v /\ typing ([], [], W, []) v t T0) vs) /\
    allocatable h.

  Lemma htyping_htyping1 h W : htyping h W -> htyping1 h W.
  Proof.
    intros [H1 H2]; unfold htyping, htyping1 in *.
    split; eauto.
    intros l t i Hl.
    eapply H1 in Hl; eauto.
    openhyp; repeat eexists_split; eauto.
    eapply Forall_impl; eauto.
    simpl.
    intuition eauto using typing_typing1.
  Qed.

  Definition wfhctx L K (W : hctx) := fmap_forall (fun p => kinding L K (fst p) KType /\ sorting L (snd p) SNat) W.

  Lemma wfhctx_wfhctx1 L K W : wfhctx L K W -> wfhctx1 L K W.
  Proof.
    intros H; unfold wfhctx, wfhctx1 in *.
    eapply fmap_forall_impl; eauto.
    simpl.
    intuition eauto using kinding_kinding1, sorting_sorting1.
  Qed.
  
  Definition wfsorts := all_sorts (fun L s => wfsort L s).

  Lemma all_sorts_impl (P P' : list sort -> sort -> Prop) :
    (forall L s, P L s -> P' L s) ->
    forall L,
      all_sorts P L ->
      all_sorts P' L.
  Proof.
    induct 2; simpl; eauto.
  Qed.

  Lemma wfsorts_wfsorts1 L : wfsorts L -> wfsorts1 L.
  Proof.
    intros H; eapply all_sorts_impl; eauto.
    simpl.
    intuition eauto using wfsort_wfsort1.
  Qed.

  Definition wfctx C :=
    let L := get_sctx C in
    let K := get_kctx C in
    let W := get_hctx C in
    let G := get_tctx C in
    wfsorts L /\
    wfhctx L K W /\
    Forall (fun t => kinding L K t KType) G.

  Lemma wfctx_wfctx1 C : wfctx C -> wfctx1 C.
  Proof.
    intros H; unfold wfctx, wfctx1 in *.
    destruct C as (((L & K) & W) & G); simpl in *.
    intuition eauto using wfsorts_wfsorts1, wfhctx_wfhctx1.
    eapply Forall_impl; try eassumption.
    simpl.
    intuition eauto using kinding_kinding1.
  Qed.
  
  Definition ctyping W (s : config) t i :=
    let '(h, e, f) := s in
    let C := ([], [], W, []) in
    typing C e t i /\
    htyping h W /\
    (interp_time i <= f)%time /\
    wfctx C
  .

  Lemma ctyping_ctyping1 W s t i : ctyping W s t i -> ctyping1 W s t i.
  Proof.
    intros H; unfold ctyping, ctyping1 in *; simpl in *.
    destruct s; simpl in *.
    destruct p; simpl in *.
    intuition eauto using typing_typing1, htyping_htyping1, wfctx_wfctx1.
  Qed.

  Theorem soundness W s t i : ctyping W s t i -> safe s.
  Proof.
    intros H.
    eapply soundness1; eauto using ctyping_ctyping1.
  Qed.

End TiML.   
