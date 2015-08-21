(* Type soundness *)

Require Import List.
Require Import Program.
Require Import Util.
Require Import Typing EvalCBV.

Import ListNotations.
Open Scope list_scope.

Set Implicit Arguments.

Inductive star A (R : A -> A -> Prop) : A -> A -> Prop :=
| Star0 a : star R a a
| StarS a b c : R a b -> star R b c -> star R a c
.

Notation open_var := var.
Notation open_cexpr := cexpr.
Notation open_size := size.
Notation open_type := type.
Notation open_expr := expr.
Notation cexpr := (open_cexpr []).
Notation size := (open_size []).
Notation type := (open_type []).
Notation expr := (open_expr []).

(* encoding of fix by recursive-type :
     fix f(x).e := \y. (unfold v) v y 
        where v := fold (\z. (\f. \x. e) (\y. (unfold z) z y)) 
                    (for y,z\not\in FV(e))
 *)

Definition step2 ne ne' := step (fst ne) (snd ne) (fst ne') (snd ne').
Infix "~>" := step2 (at level 50).

Definition steps := star step2.

Infix "~>*" := steps (at level 50).

Definition typingsim e τ := exists c s, typing [] e τ c s.
Notation "⊢" := typing.
Notation "|-" := typing.

Definition nat_of_cexpr (c : cexpr) : nat.
  admit.
Defined.

Definition c2n := nat_of_cexpr.

Global Instance Coerce_cexpr_nat : Coerce cexpr nat :=
  {
    coerce := c2n
  }.

Definition typingex n e t c s := typing [] e t c s /\ !c <= n.
Notation "||-" := typingex.

Definition not_stuck n e := IsValue e \/ exists n' e', (n, e) ~> (n', e').
Definition safe n e := forall n' e', (n, e) ~>* (n', e') -> not_stuck n' e'.

Lemma transport_eq_refl A (T : A -> Type) (from : A) (a : T from) : transport a eq_refl = a.
Proof.
  eauto.
Qed.

Open Scope G.

Lemma progress' ctx (T : tcontext ctx) e tau c s :
  |- T e tau c s ->
  forall (Heq : ctx = []) (ee : expr) (cc : cexpr) n, 
    ee = transport e Heq -> 
    cc = transport c Heq ->
    !cc <= n -> 
    not_stuck n ee.
Proof.
  induction 1; intros Heq ee cc n Hee Hcc Hle; subst; rewrite transport_eq_refl in *.
  Focus 2.
  {
    (* Case App *)
    right.
    assert (Hn : exists n', n = 1 + n').
    {
      admit.
    }
    destruct Hn as [n' ?].
    subst.
    assert (IH1 : not_stuck (1 + n') e₀).
    {
      eapply IHtyping1 with (Heq := eq_refl); eauto.
      rewrite transport_eq_refl.
      admit. (* !c0 <= _ *)
    }
    destruct IH1 as [IH1 | IH1].
    {
      Notation ".|-" := typingsim.
      Lemma cf_arrow (e : expr) T t1 c s t2 c0 s0 : 
        IsValue e -> 
        |- T e (Tarrow t1 c s t2) c0 s0 -> 
        exists e',
          e = Eabs t1 e'.
        admit.
      Qed.
      Require Import GeneralTactics4.
      copy_as IH1 IH1'.
      eapply cf_arrow in IH1'; eauto.
      destruct IH1' as [e0' ?].
      subst.
      assert (IH2 : not_stuck (1 + n') e₁).
      {
        eapply IHtyping2 with (Heq := eq_refl); eauto.
        rewrite transport_eq_refl.
        admit. (* !c1 <= _ *)
      }
      destruct IH2 as [IH2 | IH2].
      {
        exists n'.
        eexists.
        unfold step2; simpl.
        econstructor; eauto.
      }
      destruct IH2 as [n'' [e1' IH2]].
      exists n''.
      eexists.
      Lemma step_app2 n e2 n' e2' t e : 
        (n, e2) ~> (n', e2') ->
        (n, Eapp (Eabs t e) e2) ~> (n', Eapp (Eabs t e) e2).
        admit.
      Qed.
      eapply step_app2; eauto.
    }
    destruct IH1 as [n'' [e0' IH1]].
    exists n''.
    eexists.
    Lemma step_app1 n e1 n' e1' e2 :
      (n, e1) ~> (n', e1') ->
      (n, Eapp e1 e2) ~> (n', Eapp e1' e2).
      admit.
    Qed.
    eapply step_app1; eauto.
  }
  Unfocus.
  Focus 2.
  {
    (* Case Abs *)
    left.
    econstructor.
  }
  Unfocus.
  Focus 5.
  {
    (* Case Unfold *)
    right.
    assert (Hn : exists n', n = 1 + n').
    {
      admit.
    }
    destruct Hn as [n' ?].
    subst.
    assert (IH : not_stuck (1 + n') e).
    {
      eapply IHtyping with (Heq := eq_refl); eauto.
      rewrite transport_eq_refl.
      admit. (* !c <= _ *)
    }
    destruct IH as [IH | IH].
    {
      copy_as IH IH'.
      Lemma cf_recur (e : expr) T t c s : 
        IsValue e -> 
        |- T e (Trecur t) c s -> 
        exists v,
          e = Efold (Trecur t) v /\ IsValue v.
        admit.
      Qed.
      eapply cf_recur in IH'; eauto.
      destruct IH' as [v [? Hv]].
      subst.
      exists n'.
      eexists.
      econstructor; eauto.
    }
    destruct IH as [n'' [e' IH]].
    exists n''.
    eexists.
    Lemma step_unfold n e n' e' :
      (n, e) ~> (n', e') ->
      (n, Eunfold e) ~> (n', Eunfold e').
      admit.
    Qed.
    eapply step_unfold; eauto.
  }
  Unfocus.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
Qed.

Lemma progress n e tau c s :
  ||- n e tau c s -> not_stuck n e.
Proof.
  intros [Hwt Hle].
  eapply progress' with (Heq := eq_refl); eauto.
Qed.

Lemma preservation' n e n' e' :
  step n e n' e' ->
  forall tau c s,
    ||- n e tau c s ->
    exists c', ||- (n' - (n - !c)) e' tau c' s.
Proof.
  induction 1; (try rename s into s0); intros tau c s [Hwt Hle].
  Focus 2.
  {
    (* Case Beta *)
    Lemma invert_app e0 e1 tau3 c3 s3 :
      |- [] (Eapp e0 e1) tau3 c3 s3 ->
      exists t1 c s t2 c0 s0 c1 s1,
        |- [] e0 (Tarrow t1 c s t2) c0 s0 /\
        |- [] e1 t1 c1 s1 /\
        tau3 = subst s1 t2 /\
        c0 + c1 + F1 + subst s1 c <= c3 /\
        subst s1 s <= s3.
      admit.
    Qed.
    eapply invert_app in Hwt.
    destruct Hwt as [t1 [c0 [s0 [t2 [c1 [s1 [c2 [s2 Hwt]]]]]]]].
    destruct Hwt as [Hwtf [Hwtarg [? [Hc Hs]]]].
    Lemma invert_abs t1' e t1 c s t2 c0 s0 :
    |- [] (Eabs t1' e) (Tarrow t1 c s t2) c0 s0 ->
    |- (add_typing t1 []) e t2 c s /\ t1' = t1.
      admit.
    Qed.
    eapply invert_abs in Hwtf.
    destruct Hwtf as [Hwtf ?].
    subst.
    exists (subst s2 c0).
    split.
    {
      Lemma subst_wt tau1 e tau c s v c1 s1 :
      |- (add_typing tau1 []) e tau c s ->
      |- [] v tau1 c1 s1 ->
         IsValue v ->
      |- [] (subst v e) (subst s1 tau) (subst s1 c) (subst s1 s).
        admit.
      Qed.
      eapply TPle.
      { eapply subst_wt; eauto. }
      Existing Instance leF_rel_Reflexive.
      Hint Extern 1 (_ <= _) => reflexivity.
      { eauto. }
      { eauto. }
    }
    admit. (* <= *)
  }
  Unfocus.
  {
    (* Case EC *)
    Definition typingec : econtext [] -> type -> open_cexpr [CEexpr] -> open_size [CEexpr] -> open_type [CEexpr] -> Prop.
      admit.
    Defined.
    Lemma invert_ec E e t c s : 
      |- [] (plug E e) t c s ->
      exists t1 c1 s1 c2 s2 t2,
        |- [] e t1 c1 s1 /\
        typingec E t1 c2 s2 t2 /\
        t = subst s1 t2 /\
        c1 + subst s1 c2 <= c /\
        subst s1 s2 <= s.
      admit.
    Qed.
    Lemma constr_ec e t1 c1 s1 E c2 s2 t2 :
      |- [] e t1 c1 s1 ->
      typingec E t1 c2 s2 t2 ->
      |- [] (plug E e) (subst s1 t2) (c1 + subst s1 c2) (subst s1 s2).
      admit.
    Qed.
    eapply invert_ec in Hwt.
    destruct Hwt as [t1 [c1 [s1 [c2 [s2 [t2 Hwt]]]]]].
    destruct Hwt as [Hwte [HwtE [? [Hc Hs]]]].
    subst.
    unfold typingex in IHstep.
    edestruct IHstep as [c1' IH].
    {
      split.
      { eauto. }
      admit. (* le *)
    }
    destruct IH as [IHwt IHle].
    eapply constr_ec in IHwt; eauto.
    exists (c1' + subst s1 c2).
    split.
    {
      eapply TPle; eauto.
    }
    admit. (* le *)
  }
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
Qed.

Lemma preservation n e n' e' :
  (n, e) ~> (n', e') ->
  forall tau c s,
    ||- n e tau c s ->
    exists c', ||- n' e' tau c' s.
Proof.
  intros Hstep tau c s Hwt.
  eapply preservation' in Hwt; [ | eauto ].
  simpl in *.
  destruct Hwt as [c' Hwt].
  exists c'.
  unfold typingex in *.
  destruct Hwt as [Hwt Hle].
  split; eauto.
  etransitivity; eauto.
  omega.
Qed.

Lemma preservation_star' ne ne' :
  ne ~>* ne' ->
  forall n e n' e',
    ne = (n, e) ->
    ne' = (n', e') ->
    forall tau c s,
      ||- n e tau c s ->
      exists c', ||- n' e' tau c' s.
Proof.
  unfold steps.
  induction 1.
  {
    intros n e n' e' ? ? .
    subst.
    intros tau c s Hwt.
    inject H0.
    exists c.
    eauto.
  }
  intros n e n' e' ? ? .
  subst.
  intros tau c s Hwt.
  destruct b as [n2 e2].
  eapply preservation in Hwt; [ | eauto ].
  destruct Hwt as [c' Hwt].
  eapply IHstar; eauto.
Qed.

Lemma preservation_star n e n' e' :
  (n, e) ~>* (n', e') ->
  forall tau c s,
    ||- n e tau c s ->
    exists c', ||- n' e' tau c' s.
Proof.
  intros.
  eapply preservation_star'; eauto.
Qed.

Theorem type_safety n e τ c s :
  ||- n e τ c s -> safe n e.
Proof.
  intros Hwt.
  unfold safe.
  intros n' e' Hsteps.
  eapply preservation_star in Hsteps; eauto.
  destruct Hsteps as [c' Hwt'].
  eapply progress; eauto.
Qed.
