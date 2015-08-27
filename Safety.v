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

Existing Instance leF_rel_Reflexive.
Existing Instance leS_rel_Transitive.
Hint Extern 1 (_ <= _) => reflexivity.

Module ssrewrite.
  Require Import ssreflect.
  Ltac ssrewrite x := rewrite x.
  Ltac ssrewrite_r x := rewrite -x.
End ssrewrite.

Lemma TPsubst ctx (T : tcontext ctx) e t c s : 
  |- T e t c s ->
  forall (x : open_var CEexpr ctx) vt v c' s',
      |- (substx x v T) v vt c' s' ->
      IsValue v ->
      vt = substx x v (!(get_entry x T)) ->
      |- (substx x v T) (substx x v e) (substx x v t) (substx x v c) (substx x v s).
Proof.
  induction 1; try rename x into y; intros x t' v ? ? Hwtv Hval Hvt.
  Focus 3.
  {
    (* Case Abs *)
    Lemma removen_cons ctx xt {x : open_var xt ctx} {var_t} :
      removen (var_t :: ctx) (shift1 (H := Shift_var) var_t x) = var_t :: removen ctx x.
      admit.
    Qed.
    Lemma substx_abs ctx (x : open_var CEexpr ctx) (v : open_expr _) t e :
      let x' := shift1 (H := Shift_var) CEexpr x in
      let ctx' := CEexpr :: ctx in
      let v' := transport (shift1 CEexpr v) (eq_sym removen_cons) in
      substx x v (Eabs t e) = Eabs (substx x v t) (transport (substx x' v' e) removen_cons).
      admit.
    Qed.
    rewrite substx_abs.
    Lemma substx_arrow ctx (x : open_var CEexpr ctx) (v : open_expr _) t1 c s t2 :
      let x' := shift1 (H := Shift_var) CEexpr x in
      let ctx' := CEexpr :: ctx in
      let v' := transport (shift1 CEexpr v) (eq_sym removen_cons) in
      substx x v (Tarrow t1 c s t2) = Tarrow (substx x v t1) (transport (substx x' v' c) removen_cons) (transport (substx x' v' s) removen_cons) (transport (substx x' v' t2) removen_cons).
      admit.
    Qed.
    rewrite substx_arrow.
    Lemma substx_F0 ctx (x : open_var CEexpr ctx) (v : open_expr _) :
      substx x v F0 = F0.
      admit.
    Qed.
    rewrite substx_F0.
    Lemma substx_S0 ctx (x : open_var CEexpr ctx) (v : open_expr _) :
      substx x v S0 = S0.
      admit.
    Qed.
    rewrite substx_S0.
    eapply TPabs.
    Lemma transport_cancel A (T : A -> Type) (from : A) (a : T from) (to : A) (Heq : from = to) : transport (transport a Heq) (eq_sym Heq) = a.
    Proof.
      admit.
    Qed.
    Lemma transport_cancel' A (T : A -> Type) (from : A) (a : T from) (to : A) (Heq : to = from) : transport (transport a (eq_sym Heq)) Heq = a.
    Proof.
      admit.
    Qed.
    rewrite <- (transport_cancel' _ (add_typing _ _) removen_cons).
    Lemma TPtransport ctx (T : tcontext ctx) e t c s ctx' (Heq : ctx = ctx') :
      |- T e t c s -> |- (transport T Heq) (transport e Heq) (transport t Heq) (transport c Heq) (transport s Heq).
      admit.
    Qed.
    Lemma TPtransport_r ctx (T : tcontext ctx) e t c s ctx' (Heq : ctx = ctx') :
      |- (transport T Heq) (transport e Heq) (transport t Heq) (transport c Heq) (transport s Heq) -> |- T e t c s.
      admit.
    Qed.
    eapply TPtransport.
    Lemma substx_add_typing ctx (x : open_var CEexpr ctx) (v : open_expr _) t T :
      let x' := shift1 (H := Shift_var) CEexpr x in
      let ctx' := CEexpr :: ctx in
      let v' := transport (shift1 CEexpr v) (eq_sym removen_cons) in
      substx x' v' (add_typing t T) = transport (add_typing (substx x v t) (substx x v T)) (eq_sym removen_cons).
      admit.
    Qed.
    Import ssrewrite.
    ssrewrite_r (substx_add_typing x v t1 T).
    eapply IHtyping.
    {
      ssrewrite (substx_add_typing x v t1 T).
      eapply TPtransport.
      Lemma TPweaken ctx (T : tcontext ctx) e t c s t1 : 
      |- T e t c s -> 
      |- (add_typing t1 T) (shift1 CEexpr e) (shift1 _ t) (shift1 _ c) (shift1 _ s).
        admit.
      Qed.
      eapply TPweaken.
      eauto.
    }
    {
      Lemma IsValue_transport ctx (v : open_expr ctx) ctx' (Heq : ctx = ctx') :
        IsValue v ->
        IsValue (transport v Heq).
        admit.
      Qed.
      eapply IsValue_transport.
      Lemma IsValue_shift1 vart ctx (v : open_expr ctx) :
        IsValue v ->
        IsValue (shift1 vart v).
        admit.
      Qed.
      eapply IsValue_shift1.
      eauto.
    }
    {
      subst.
      Lemma substx_type_of_te ctx (x : open_var CEexpr ctx) (v : open_expr _) (te : tc_entry CEexpr _) :
        substx x v (!te) = !(substx x v te).
        admit.
      Qed.
      Lemma get_entry_add_typing ctx (x : open_var CEexpr ctx) t T :
        let x' := shift1 (H := Shift_var) CEexpr x in
        get_entry x' (add_typing t T) = shift1 CEexpr (get_entry x T).
        admit.
      Qed.
      ssrewrite get_entry_add_typing.
      Lemma type_of_te_shift1 vart ctx (te : tc_entry CEexpr ctx) :
        !(shift1 vart te) = shift1 vart !te.
        admit.
      Qed.
      ssrewrite type_of_te_shift1.
      Lemma shift1_substx_e_t vart ctx (x : open_var CEexpr ctx) (v : open_expr _) (b : open_type _) :
        let x' := shift1 (H := Shift_var) vart x in
        let ctx' := vart :: ctx in
        let v' := transport (shift1 _ v) (eq_sym removen_cons) in
        shift1 _ (substx x v b) = transport (substx x' v' (shift1 _ b)) removen_cons.
        admit.
      Qed.
      rewrite shift1_substx_e_t.
      rewrite transport_cancel.
      eauto.
    }
  }
  Unfocus.
  Focus 2.
  {
    (* Case App *)
    Lemma substx_app ctx (x : open_var CEexpr ctx) (v : open_expr _) e1 e2 :
      substx x v (Eapp e1 e2) = Eapp (substx x v e1) (substx x v e2).
      admit.
    Qed.
    rewrite substx_app.
    Lemma substx_Fadd ctx (x : open_var CEexpr ctx) (v : open_expr _) c1 c2 :
      substx x v (c1 + c2) = substx x v c1 + substx x v c2.
      admit.
    Qed.
    repeat rewrite substx_Fadd.
    Lemma substx_F1 ctx (x : open_var CEexpr ctx) (v : open_expr _) :
      substx x v F1 = F1.
      admit.
    Qed.
    rewrite substx_F1.
    Lemma substx_subst_s_t ctx (x : open_var CEexpr ctx) (v : open_expr _) (vv : open_size _) (b : open_type _) :
      let x' := shift1 (H := Shift_var) CEexpr x in
      let ctx' := CEexpr :: ctx in
      let v' := transport (shift1 CEexpr v) (eq_sym removen_cons) in
      substx x v (subst vv b) = subst (substx x v vv) (transport (substx x' v' b) removen_cons).
      admit.
    Qed.
    rewrite substx_subst_s_t.
    Lemma substx_subst_s_s ctx (x : open_var CEexpr ctx) (v : open_expr _) (vv : open_size _) (b : open_size _) :
      let x' := shift1 (H := Shift_var) CEexpr x in
      let ctx' := CEexpr :: ctx in
      let v' := transport (shift1 CEexpr v) (eq_sym removen_cons) in
      substx x v (subst vv b) = subst (substx x v vv) (transport (substx x' v' b) removen_cons).
      admit.
    Qed.
    rewrite substx_subst_s_s.
    Lemma substx_subst_s_c ctx (x : open_var CEexpr ctx) (v : open_expr _) (vv : open_size _) (b : open_cexpr _) :
      let x' := shift1 (H := Shift_var) CEexpr x in
      let ctx' := CEexpr :: ctx in
      let v' := transport (shift1 CEexpr v) (eq_sym removen_cons) in
      substx x v (subst vv b) = subst (substx x v vv) (transport (substx x' v' b) removen_cons).
      admit.
    Qed.
    rewrite substx_subst_s_c.
    eapply (TPapp _ _ _ (substx x v τ₁)).
    {
      ssrewrite_r substx_arrow.
      eapply IHtyping1; eauto.
    }
    eapply IHtyping2; eauto.
  }
  Unfocus.
  {
    (* Case Var *)
    Definition var_dec vart ctx (x y : open_var vart ctx) : {x = y} + {x <> y}.
      admit.
    Defined.
    rewrite substx_F0.
    destruct (var_dec x y) as [Heq | Hne].
    {
      symmetry in Heq; subst.
      Lemma substx_Evar_eq ctx (x : open_var CEexpr ctx) (v : open_expr _) :
        substx x v (Evar x) = v.
        admit.
      Qed.
      rewrite substx_Evar_eq.
      Lemma substx_Svar_eq ctx (x : open_var CEexpr ctx) (v : open_expr _) :
        substx x v !x = get_size v.
        admit.
      Qed.
      rewrite substx_Svar_eq.
      Lemma IsValue_TP_F0 ctx (T : tcontext ctx) v t c s : 
        |- T v t c s ->
        IsValue v ->
        |- T v t F0 (get_size v).
        admit.
      Qed.
      eapply IsValue_TP_F0; eauto.
    }
    subst.
    Definition substx_ne vart ctx (x y : open_var vart ctx) (Hne : x <> y) : open_var vart (removen ctx x).
      admit.
    Qed.
    set (y' := substx_ne Hne).
    Lemma substx_Evar_ne ctx (x : open_var CEexpr ctx) y (Hne : x <> y) (v : open_expr _) :
      substx x v (Evar y) = Evar (substx_ne Hne).
      admit.
    Qed.
    rewrite (substx_Evar_ne Hne).
    Lemma substx_Svar_ne ctx (x : open_var CEexpr ctx) y (Hne : x <> y) (v : open_expr _) :
      substx x v !y = !(substx_ne Hne).
      admit.
    Qed.
    rewrite (substx_Svar_ne Hne).
    rewrite substx_type_of_te.
    Lemma substx_get_entry_ne ctx (x : open_var CEexpr ctx) y (Hne : x <> y) (v : open_expr _) T :
      substx x v (get_entry y T) = get_entry (substx_ne Hne) (substx x v T).
      admit.
    Qed.
    rewrite (substx_get_entry_ne Hne).
    eapply TPvar.
  }
  {
    (* Case Tapp *)
    Lemma substx_tapp ctx (x : open_var CEexpr ctx) (v : open_expr _) e t :
      substx x v (Etapp e t) = Etapp (substx x v e) (substx x v t).
      admit.
    Qed.
    rewrite substx_tapp.
    repeat rewrite substx_Fadd.
    rewrite substx_F1.
    Lemma substx_subst_t_t ctx (x : open_var CEexpr ctx) (v : open_expr _) (vv : open_type _) (b : open_type _) :
      let x' := shift1 (H := Shift_var) _ x in
      let ctx' := CEtype :: ctx in
      let v' := transport (shift1 _ v) (eq_sym removen_cons) in
      substx x v (subst vv b) = subst (substx x v vv) (transport (substx x' v' b) removen_cons).
      admit.
    Qed.
    rewrite substx_subst_t_t.
    eapply TPtapp.
    Lemma substx_universal ctx (x : open_var CEexpr ctx) (v : open_expr _) c s t2 :
      let x' := shift1 (H := Shift_var) _ x in
      let ctx' := CEtype :: ctx in
      let v' := transport (shift1 _ v) (eq_sym removen_cons) in
      substx x v (Tuniversal c s t2) = Tuniversal (substx x v c) (substx x v s) (transport (substx x' v' t2) removen_cons).
      admit.
    Qed.
    ssrewrite_r substx_universal.
    eapply IHtyping; eauto.
  }
  {
    (* Case Tabs *)
    Lemma substx_tabs ctx (x : open_var CEexpr ctx) (v : open_expr _) e :
      let x' := shift1 (H := Shift_var) _ x in
      let ctx' := CEtype :: ctx in
      let v' := transport (shift1 _ v) (eq_sym removen_cons) in
      substx x v (Etabs e) = Etabs (transport (substx x' v' e) removen_cons).
      admit.
    Qed.
    rewrite substx_tabs.
    rewrite substx_universal.
    rewrite substx_F0.
    rewrite substx_S0.
    eapply TPtabs.
    rewrite <- (transport_cancel' _ (add_kinding _) removen_cons).
    rewrite <- (transport_cancel' _ (shift1 _ (substx x v c)) removen_cons).
    rewrite <- (transport_cancel' _ (shift1 _ (substx x v s)) removen_cons).
    eapply TPtransport.
    Lemma substx_add_kinding ctx (x : open_var CEexpr ctx) (v : open_expr _) T :
      let x' := shift1 (H := Shift_var) _ x in
      let ctx' := CEtype :: ctx in
      let v' := transport (shift1 _ v) (eq_sym removen_cons) in
      substx x' v' (add_kinding T) = transport (add_kinding (substx x v T)) (eq_sym removen_cons).
      admit.
    Qed.
    ssrewrite_r (substx_add_kinding x v T).
    Lemma shift1_substx_e_c vart ctx (x : open_var CEexpr ctx) (v : open_expr _) (b : open_cexpr _) :
      let x' := shift1 (H := Shift_var) _ x in
      let ctx' := vart :: ctx in
      let v' := transport (shift1 _ v) (eq_sym removen_cons) in
      shift1 vart (substx x v b) = transport (substx x' v' (shift1 vart b)) removen_cons.
      admit.
    Qed.
    rewrite shift1_substx_e_c.
    rewrite transport_cancel.
    Lemma shift1_substx_e_s vart ctx (x : open_var CEexpr ctx) (v : open_expr _) (b : open_size _) :
      let x' := shift1 (H := Shift_var) _ x in
      let ctx' := vart :: ctx in
      let v' := transport (shift1 _ v) (eq_sym removen_cons) in
      shift1 vart (substx x v b) = transport (substx x' v' (shift1 vart b)) removen_cons.
      admit.
    Qed.
    rewrite shift1_substx_e_s.
    rewrite transport_cancel.
    eapply IHtyping.
    {
      ssrewrite (substx_add_kinding x v T).
      eapply TPtransport.
      Lemma TPweaken_t ctx (T : tcontext ctx) e t c s : 
      |- T e t c s -> 
      |- (add_kinding T) (shift1 CEtype e) (shift1 _ t) (shift1 _ c) (shift1 _ s).
        admit.
      Qed.
      eapply TPweaken_t.
      eauto.
    }
    {
      eapply IsValue_transport.
      eapply IsValue_shift1.
      eauto.
    }
    {
      subst.
      Lemma get_entry_add_kinding ctx (x : open_var CEexpr ctx) T :
        let x' := shift1 (H := Shift_var) _ x in
        get_entry x' (add_kinding T) = shift1 _ (get_entry x T).
        admit.
      Qed.
      ssrewrite get_entry_add_kinding.
      ssrewrite type_of_te_shift1.
      rewrite shift1_substx_e_t.
      rewrite transport_cancel.
      eauto.
    }
  }
  {
    (* Case Fold *)
    subst.
    Lemma substx_fold ctx (x : open_var CEexpr ctx) (v : open_expr _) t e :
      substx x v (Efold t e) = Efold (substx x v t) (substx x v e).
      admit.
    Qed.
    rewrite substx_fold.
    Lemma substx_Sfold ctx (x : open_var CEexpr ctx) (v : open_expr _) s :
      substx x v (Sfold s) = Sfold (substx x v s).
      admit.
    Qed.
    rewrite substx_Sfold.
    Lemma substx_recur ctx (x : open_var CEexpr ctx) (v : open_expr _) t :
      let x' := shift1 (H := Shift_var) _ x in
      let ctx' := CEtype :: ctx in
      let v' := transport (shift1 _ v) (eq_sym removen_cons) in
      substx x v (Trecur t) = Trecur (transport (substx x' v' t) removen_cons).
      admit.
    Qed.
    eapply TPfold.
    {
      ssrewrite substx_recur.
      eauto.
    }
    ssrewrite_r substx_subst_t_t.
    eapply IHtyping; eauto.
  }
  {
    (* Case Unfold *)
    subst.
    Lemma substx_unfold ctx (x : open_var CEexpr ctx) (v : open_expr _) e :
      substx x v (Eunfold e) = Eunfold (substx x v e).
      admit.
    Qed.
    rewrite substx_unfold.
    repeat rewrite substx_Fadd.
    rewrite substx_F1.
    rewrite substx_subst_t_t.
    eapply TPunfold.
    {
      eapply IHtyping; eauto.
    }
    {
      Lemma is_fold_substx ctx (x : open_var CEexpr ctx) (v : open_expr _) s s' :
        is_fold s = Some s' ->
        is_fold (substx x v s) = Some (substx x v s').
        admit.
      Qed.
      eapply is_fold_substx; eauto.
    }
    rewrite substx_recur.
    eauto.
  }
  {
    (* Case Hide *)
    subst.
    Lemma substx_hide ctx (x : open_var CEexpr ctx) (v : open_expr _) e :
      substx x v (Ehide e) = Ehide (substx x v e).
      admit.
    Qed.
    rewrite substx_hide.
    Lemma substx_Shide ctx (x : open_var CEexpr ctx) (v : open_expr _) s :
      substx x v (Shide s) = Shide (substx x v s).
      admit.
    Qed.
    rewrite substx_Shide.
    Lemma substx_Thide ctx (x : open_var CEexpr ctx) (v : open_expr _) t :
      substx x v (Thide t) = Thide (substx x v t).
      admit.
    Qed.
    ssrewrite substx_Thide.
    eapply TPhide.
    eapply IHtyping; eauto.
  }
  {
    (* Case Unhide *)
    subst.
    Lemma substx_unhide ctx (x : open_var CEexpr ctx) (v : open_expr _) e :
      substx x v (Eunhide e) = Eunhide (substx x v e).
      admit.
    Qed.
    rewrite substx_unhide.
    repeat rewrite substx_Fadd.
    rewrite substx_F1.
    eapply TPunhide.
    {
      eapply IHtyping; eauto.
    }
    {
      Lemma is_hide_substx ctx (x : open_var CEexpr ctx) (v : open_expr _) s s' :
        is_hide s = Some s' ->
        is_hide (substx x v s) = Some (substx x v s').
        admit.
      Qed.
      eapply is_hide_substx; eauto.
    }
  }
  {
    (* Case Sub *)
    subst.
    eapply TPsub.
    {
      eapply IHtyping; eauto.
    }
    {
      Lemma leF_substx ctx (x : open_var CEexpr ctx) (v : open_expr _) (a b : open_cexpr _) :
        a <= b ->
        substx x v a <= substx x v b.
        admit.
      Qed.
      eapply leF_substx; eauto.
    }
    {
      Lemma leS_substx ctx (x : open_var CEexpr ctx) (v : open_expr _) (a b : open_size _) :
        a <= b ->
        substx x v a <= substx x v b.
        admit.
      Qed.
      eapply leS_substx; eauto.
    }
  }
  {
    (* Case Tt *)
    subst.
    Lemma substx_tt ctx (x : open_var CEexpr ctx) (v : open_expr _) :
      substx x v Ett = Ett.
      admit.
    Qed.
    rewrite substx_tt.
    rewrite substx_F0.
    rewrite substx_S0.
    Lemma substx_unit ctx (x : open_var CEexpr ctx) (v : open_expr _) :
      substx x v Tunit = Tunit.
      admit.
    Qed.
    rewrite substx_unit.
    eapply TPtt.
  }
  {
    (* Case Pair *)
    subst.
    Lemma substx_pair ctx (x : open_var CEexpr ctx) (v : open_expr _) e1 e2 :
      substx x v (Epair e1 e2) = Epair (substx x v e1) (substx x v e2).
      admit.
    Qed.
    rewrite substx_pair.
    Lemma substx_Spair ctx (x : open_var CEexpr ctx) (v : open_expr _) s1 s2 :
      substx x v !(s1, s2) = !(substx x v s1, substx x v s2).
      admit.
    Qed.
    rewrite substx_Spair.
    rewrite substx_Fadd.
    Lemma substx_prod ctx (x : open_var CEexpr ctx) (v : open_expr _) t1 t2 :
      substx x v (Tprod t1 t2) = Tprod (substx x v t1) (substx x v t2).
      admit.
    Qed.
    rewrite substx_prod.
    eapply TPpair.
    { eapply IHtyping1; eauto. }
    { eapply IHtyping2; eauto. }
  }
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

Lemma TPsubst' ctx (x : open_var CEexpr ctx) (T : tcontext ctx) e t c s v : 
  |- T e t c s ->
  forall vt c' s',
      |- (substx x v T) v vt c' s' ->
      IsValue v ->
      |- (substx x v T) (substx x v e) (substx x v t) (substx x v c) (substx x v s).
  admit.
Qed.

Lemma subst_wt' tau1 e tau c s v c1 s1 :
|- (add_typing tau1 []) e tau c s ->
|- [] v tau1 c1 s1 ->
   IsValue v ->
|- [] (subst v e) (subst v tau) (subst v c) (subst v s).
Proof.
  intros Hwt Hwtv Hval.
  Lemma subst_add_typing' ctx (T : tcontext ctx) t (v : open_expr _) :
    substx var0 v (add_typing t T) = T.
    admit.
  Qed.
  Lemma subst_add_typing ctx (T : tcontext ctx) t (v : open_expr _) :
    subst v (add_typing t T) = T.
  Proof.
    unfold subst.
    eapply subst_add_typing'.
  Qed.
  rewrite <- (subst_add_typing [] tau1 v).
  eapply (@TPsubst' [CEexpr] #0); eauto.
  rewrite subst_add_typing'.
  eauto.
Qed.

Lemma subst_wt tau1 e tau c s v c1 s1 :
|- (add_typing tau1 []) e tau c s ->
|- [] v tau1 c1 s1 ->
   IsValue v ->
|- [] (subst v e) (subst s1 tau) (subst s1 c) (subst s1 s).
Proof.
  intros Hwt Hwtv Hval.
  (* use subst_wt' *)
  admit.
Qed.

Lemma subst_t_wt e t c s t1 :
|- (add_kinding []) e t c s ->
|- [] (subst t1 e) (subst t1 t) (subst t1 c) (subst t1 s).
  admit.
Qed.

Lemma progress' ctx (T : tcontext ctx) e tau c s :
  |- T e tau c s ->
  forall (Heq : ctx = []) n, 
    !(transport c Heq) <= n -> 
    not_stuck n (transport e Heq).
Proof.
  induction 1; intros Heq n Hle; subst; rewrite transport_eq_refl in *.
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
  {
    (* Case Var *)
    destruct x as [n' ?].
    destruct n'; simpl in *; discriminate.
  }
  {
    (* Case Tapp *)
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
      admit. (* le *)
    }
    destruct IH as [IH | IH].
    {
      Lemma cf_universal (e : expr) T c s t2 c0 s0 : 
        IsValue e -> 
        |- T e (Tuniversal c s t2) c0 s0 -> 
        exists e',
          e = Etabs e'.
        admit.
      Qed.
      copy_as IH IH'.
      eapply cf_universal in IH'; eauto.
      destruct IH' as [e0' ?].
      subst.
      exists n'.
      eexists.
      unfold step2; simpl.
      econstructor; eauto.
    }
    destruct IH as [n'' [e0' IH]].
    exists n''.
    eexists.
    Lemma step_tapp1 n e n' e' t :
      (n, e) ~> (n', e') ->
      (n, Etapp e t) ~> (n', Etapp e' t).
      admit.
    Qed.
    eapply step_tapp1; eauto.
  }
  {
    (* Case Tabs *)
    left.
    econstructor.
  }
  {
    (* Case Fold *)
    assert (IH : not_stuck n e).
    {
      eapply IHtyping with (Heq := eq_refl); eauto.
    }
    destruct IH as [IH | IH].
    {
      left.
      econstructor.
      eauto.
    }
    right.
    destruct IH as [n' [e' IH]].
    exists n'.
    eexists.
    Lemma step_fold n e n' e' t :
      (n, e) ~> (n', e') ->
      (n, Efold t e) ~> (n', Efold t e').
      admit.
    Qed.
    eapply step_fold; eauto.
  }
  {
    (* Case Hide *)
    assert (IH : not_stuck n e).
    {
      eapply IHtyping with (Heq := eq_refl); eauto.
    }
    destruct IH as [IH | IH].
    {
      left.
      econstructor.
      eauto.
    }
    right.
    destruct IH as [n' [e' IH]].
    exists n'.
    eexists.
    Lemma step_hide n e n' e' :
      (n, e) ~> (n', e') ->
      (n, Ehide e) ~> (n', Ehide e').
      admit.
    Qed.
    eapply step_hide; eauto.
  }
  {
    (* Case Unhide *)
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
      Lemma cf_hide (e : expr) T t c s : 
        IsValue e -> 
        |- T e (Thide t) c s -> 
        exists v,
          e = Ehide v /\ IsValue v.
        admit.
      Qed.
      eapply cf_hide in IH'; eauto.
      destruct IH' as [v [? Hv]].
      subst.
      exists n'.
      eexists.
      econstructor; eauto.
    }
    destruct IH as [n'' [e' IH]].
    exists n''.
    eexists.
    Lemma step_unhide n e n' e' :
      (n, e) ~> (n', e') ->
      (n, Eunhide e) ~> (n', Eunhide e').
      admit.
    Qed.
    eapply step_unhide; eauto.
  }
  {
    (* Case Sub *)
    assert (IH : not_stuck n e).
    {
      eapply IHtyping with (Heq := eq_refl); eauto.
      rewrite transport_eq_refl.
      etransitivity; [ | eauto ].
      admit. (* le *)
    }
    eauto.
  }
  {
    (* Case Tt *)
    left.
    econstructor.
  }
  {
    (* Case Pair *)
    assert (IH1 : not_stuck n e1).
    {
      eapply IHtyping1 with (Heq := eq_refl); eauto.
      rewrite transport_eq_refl.
      admit. (* le *)
    }
    destruct IH1 as [IH1 | IH1].
    {
      assert (IH2 : not_stuck n e2).
      {
        eapply IHtyping2 with (Heq := eq_refl); eauto.
        rewrite transport_eq_refl.
        admit. (* le *)
      }
      destruct IH2 as [IH2 | IH2].
      {
        left.
        econstructor; eauto.
      }
      destruct IH2 as [n' [e2' IH2]].
      right.
      exists n'.
      eexists.
      Lemma step_pair2 n e2 n' e2' e1 : 
        (n, e2) ~> (n', e2') ->
        IsValue e1 ->
        (n, Epair e1 e2) ~> (n', Epair e1 e2).
        admit.
      Qed.
      eapply step_pair2; eauto.
    }
    destruct IH1 as [n' [e1' IH1]].
    right.
    exists n'.
    eexists.
    Lemma step_pair1 n e1 n' e1' e2 :
      (n, e1) ~> (n', e1') ->
      (n, Epair e1 e2) ~> (n', Epair e1' e2).
      admit.
    Qed.
    eapply step_pair1; eauto.
  }
  {
    (* Case Inl *)
    assert (IH : not_stuck n e).
    {
      eapply IHtyping with (Heq := eq_refl); eauto.
    }
    destruct IH as [IH | IH].
    {
      left.
      econstructor.
      eauto.
    }
    right.
    destruct IH as [n' [e' IH]].
    exists n'.
    eexists.
    Lemma step_inl n e n' e' t :
      (n, e) ~> (n', e') ->
      (n, Einl t e) ~> (n', Einl t e').
      admit.
    Qed.
    eapply step_inl; eauto.
  }
  {
    (* Case Inr *)
    assert (IH : not_stuck n e).
    {
      eapply IHtyping with (Heq := eq_refl); eauto.
    }
    destruct IH as [IH | IH].
    {
      left.
      econstructor.
      eauto.
    }
    right.
    destruct IH as [n' [e' IH]].
    exists n'.
    eexists.
    Lemma step_inr n e n' e' t :
      (n, e) ~> (n', e') ->
      (n, Einr t e) ~> (n', Einr t e').
      admit.
    Qed.
    eapply step_inr; eauto.
  }
  {
    (* Case Fst *)
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
      Lemma cf_prod (e : expr) T t1 t2 c s : 
        IsValue e -> 
        |- T e (t1 * t2) c s -> 
        exists v1 v2,
          e = Epair v1 v2 /\ IsValue v1 /\ IsValue v2.
        admit.
      Qed.
      eapply cf_prod in IH'; eauto.
      destruct IH' as [v1 [v2 [? [Hv1 Hv2]]]].
      subst.
      exists n'.
      eexists.
      econstructor; eauto.
    }
    destruct IH as [n'' [e' IH]].
    exists n''.
    eexists.
    Lemma step_fst n e n' e' :
      (n, e) ~> (n', e') ->
      (n, Efst e) ~> (n', Efst e').
      admit.
    Qed.
    eapply step_fst; eauto.
  }
  {
    (* Case Snd *)
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
      eapply cf_prod in IH'; eauto.
      destruct IH' as [v1 [v2 [? [Hv1 Hv2]]]].
      subst.
      exists n'.
      eexists.
      econstructor; eauto.
    }
    destruct IH as [n'' [e' IH]].
    exists n''.
    eexists.
    Lemma step_snd n e n' e' :
      (n, e) ~> (n', e') ->
      (n, Esnd e) ~> (n', Esnd e').
      admit.
    Qed.
    eapply step_snd; eauto.
  }
  {
    (* Case Match *)
    right.
    assert (Hn : exists n', n = 1 + n').
    {
      admit.
    }
    destruct Hn as [n' ?].
    subst.
    assert (IH : not_stuck (1 + n') e).
    {
      eapply IHtyping1 with (Heq := eq_refl); eauto.
      rewrite transport_eq_refl.
      admit. (* !c <= _ *)
    }
    destruct IH as [IH | IH].
    {
      copy_as IH IH'.
      Lemma cf_sum (e : expr) T t1 t2 c s : 
        IsValue e -> 
        |- T e (t1 + t2) c s -> 
        exists v,
          IsValue v /\
          (e = Einl t2 v \/ e = Einr t1 v).
        admit.
      Qed.
      eapply cf_sum in IH'; eauto.
      destruct IH' as [v [Hv [? | ?]]].
      {
        subst.
        exists n'.
        eexists.
        econstructor; eauto.
      }
      {
        subst.
        exists n'.
        eexists.
        econstructor; eauto.
      }
    }
    destruct IH as [n'' [e' IH]].
    exists n''.
    eexists.
    Lemma step_match n e n' e' t s e1 e2 :
      (n, e) ~> (n', e') ->
      (n, Ematch e t s e1 e2) ~> (n', Ematch e' t s e1 e2).
      admit.
    Qed.
    eapply step_match; eauto.
  }
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
      |- (add_typing t1 []) e t2 c s /\
      t1' = t1 /\
      S0 <= s.   
      admit.
    Qed.
    eapply invert_abs in Hwtf.
    destruct Hwtf as [Hwtf ?].
    subst.
    exists (subst s2 c0).
    split.
    {
      eapply TPsub.
      { eapply subst_wt; eauto. }
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
      eapply TPsub; eauto.
    }
    admit. (* le *)
  }
  Focus 6.
  {
    (* Case Unfold-fold *)
    Lemma invert_unfold e t c s :
      |- [] (Eunfold e) t c s ->
      exists t' c' s',
        |- [] e (Trecur t') c' (Sfold s') /\
        t = subst (Trecur t') t' /\
        c' + F1 <= c /\
        s' <= s.
      admit.
    Qed.
    eapply invert_unfold in Hwt.
    destruct Hwt as [t' [c' [s' Hwt]]].
    destruct Hwt as [Hwt [? [Hc Hs]]].
    subst.
    Lemma invert_fold t1 e t c s :
      |- [] (Efold t1 e) t c s ->
      exists t' c' s',
        |- [] e (subst (Trecur t') t') c' s' /\
        t1 = t /\
        t = Trecur t' /\
        c' <= c /\
        Sfold s' <= s.
      admit.
    Qed.
    eapply invert_fold in Hwt.
    destruct Hwt as [t1' [c1 [s1 Hwt]]].
    destruct Hwt as [Hwt [? [Ht1' [Hc' Hs']]]].
    subst.
    symmetry in Ht1'; inject Ht1'.
    exists c'.
    split.
    {
      eapply TPsub.
      { eauto. }
      { eauto. }
      { etransitivity; [ | eauto ].
        Lemma Sfold_le_le (a b : size) :
          Sfold a <= Sfold b ->
          a <= b.
          admit.
        Qed.
        eapply Sfold_le_le; eauto.
      }
    }
    admit. (* le *)
  }
  Unfocus.
  {
    (* Case Fst *)
    Lemma invert_fst e t c s :
      |- [] (Efst e) t c s ->
      exists t' c' s1 s2,
        |- [] e (Tprod t t') c' (Spair s1 s2) /\
        c' + F1 <= c /\
        s1 <= s.
      admit.
    Qed.
    eapply invert_fst in Hwt.
    destruct Hwt as [t' [c' [s1 [s2 Hwt]]]].
    destruct Hwt as [Hwt [Hc Hs]].
    Lemma invert_pair e1 e2 t c s :
      |- [] (Epair e1 e2) t c s ->
      exists t1 c1 s1 t2 c2 s2,
        |- [] e1 t1 c1 s1 /\
        |- [] e2 t2 c2 s2 /\
        t = Tprod t1 t2 /\
        c1 + c2 <= c /\
        Spair s1 s2 <= s.
      admit.
    Qed.
    eapply invert_pair in Hwt.
    destruct Hwt as [t1 [c1 [s1' [t2 [c2 [s2' Hwt]]]]]].
    destruct Hwt as [Htw1 [Htw2 [Ht [Hc' Hss]]]].
    inject Ht.
    exists c'.
    split.
    {
      eapply TPsub.
      { eauto. }
      { admit. (* le *) }
      { etransitivity; [ | eauto ].
        Lemma Spair_le_le (a b a' b' : size) :
          Spair a b <= Spair a' b' ->
          a <= a' /\ b <= b'.
          admit.
        Qed.
        eapply Spair_le_le in Hss.
        eapply Hss.
      }
    }
    admit. (* le *)
  }
  Focus 2.
  {
    (* Case Match-inl *)
    Lemma invert_match e t' s' k1 k2 t c s :
      |- [] (Ematch e t' s' k1 k2) t c s ->
      exists t1 t2 c0 s1 s2 c1 c2,
        |- [] e (Tsum t1 t2) c0 (Sinlinr s1 s2) /\
        |- (add_typing t1 []) k1 (shift1 CEexpr t) c1 (shift1 CEexpr s') /\
        |- (add_typing t2 []) k2 (shift1 CEexpr t) c2 (shift1 CEexpr s') /\
        t' = t /\
        c0 + F1 + max (subst s1 c1) (subst s2 c2) <= c /\
        s' <= s.
      admit.
    Qed.
    eapply invert_match in Hwt.
    destruct Hwt as [t1 [t2 [c0 [s1 [s2 [c1 [c2 Hwt]]]]]]].
    destruct Hwt as [Hwt0 [Hwt1 [Hwt2 [? [Hc Hs]]]]].
    subst.
    Lemma invert_inl t2 e t c s :
      |- [] (Einl t2 e) t c s ->
      exists t1 c1 s1,
        |- [] e t1 c1 s1 /\
        t = Tsum t1 t2 /\
        c1 <= c /\
        Sinlinr s1 S0 <= s.
      admit.
    Qed.
    eapply invert_inl in Hwt0.
    destruct Hwt0 as [t1' [c1' [s1' Hwt0]]].
    destruct Hwt0 as [Htw0 [Ht [Hc0 Hss]]].
    symmetry in Ht; inject Ht.
    exists (subst s1 c1).
    split.
    {
      eapply TPsub.
      { 
        replace tau with (subst s1 (shift1 CEexpr tau)).
        {
          eapply subst_wt; eauto.
          eapply TPsub; eauto.
          Lemma Sinlinr_le_le (a b a' b' : size):
            Sinlinr a b <= Sinlinr a' b' ->
            a <= a' /\ b <= b'.
            admit.
          Qed.
          eapply Sinlinr_le_le in Hss.
          eapply Hss.
        }
        Lemma subst_shift1_s_t ctx (v : open_size ctx) (b : open_type _) : subst v (shift1 CEexpr b) = b.
          admit.
        Qed.
        eapply subst_shift1_s_t.
      }
      { eauto. }
      Lemma subst_shift1_s_s ctx (v : open_size ctx) (b : open_size _) : subst v (shift1 CEexpr b) = b.
        admit.
      Qed.
      rewrite (@subst_shift1_s_s []).
      eauto.
    }
    admit. (* le *)
  }
  Unfocus.
  Focus 3.
  {
    (* Case Tapp *)
    Lemma invert_tapp e t1 t c s: 
      |- [] (Etapp e t1) t c s ->
      exists c0 s0 t0 c' s',
        |- [] e (Tuniversal c0 s0 t0) c' s' /\
        t = subst t1 t0 /\
        c' + F1 + c0 <= c /\
        s0 <= s.
      admit.
    Qed.
    eapply invert_tapp in Hwt.
    destruct Hwt as [c0 [s0 [t0 [c' [s' Hwt]]]]].
    destruct Hwt as [Hwt [? [Hc Hs]]].
    subst.
    Lemma invert_tabs e t c s :
      |- [] (Etabs e) t c s ->
      exists t' c' s',
        |- (add_kinding []) e t' (shift1 CEtype c') (shift1 CEtype s') /\
        t = Tuniversal c' s' t' /\
        S0 <= s.   
      admit.
    Qed.
    eapply invert_tabs in Hwt.
    destruct Hwt as [t' [c'' [s'' Hwt]]].
    destruct Hwt as [Hwt [Ht Hs']].
    symmetry in Ht; inject Ht.
    exists c0.
    split.
    {
      eapply TPsub.
      {
        eapply subst_t_wt.
        eauto.
      }
      {
        Lemma subst_shift1_t_c ctx (v : open_type ctx) (b : open_cexpr _) : subst v (shift1 CEtype b) = b.
          admit.
        Qed.
        rewrite (@subst_shift1_t_c []).
        eauto.
      }
      {
        Lemma subst_shift1_t_s ctx (v : open_type ctx) (b : open_size _) : subst v (shift1 CEtype b) = b.
          admit.
        Qed.
        rewrite (@subst_shift1_t_s []).
        eauto.
      }
    }
    admit. (* le *)
  }
  Unfocus.
  {
    (* Case Snd *)
    Lemma invert_snd e t c s :
      |- [] (Esnd e) t c s ->
      exists t' c' s1 s2,
        |- [] e (Tprod t' t) c' (Spair s1 s2) /\
        c' + F1 <= c /\
        s2 <= s.
      admit.
    Qed.
    eapply invert_snd in Hwt.
    destruct Hwt as [t' [c' [s1 [s2 Hwt]]]].
    destruct Hwt as [Hwt [Hc Hs]].
    eapply invert_pair in Hwt.
    destruct Hwt as [t1 [c1 [s1' [t2 [c2 [s2' Hwt]]]]]].
    destruct Hwt as [Htw1 [Htw2 [Ht [Hc' Hss]]]].
    inject Ht.
    exists c'.
    split.
    {
      eapply TPsub.
      { eauto. }
      { admit. (* le *) }
      { etransitivity; [ | eauto ].
        eapply Spair_le_le in Hss.
        eapply Hss.
      }
    }
    admit. (* le *)
  }
  {
    (* Case Match-inr *)
    eapply invert_match in Hwt.
    destruct Hwt as [t1 [t2 [c0 [s1 [s2 [c1 [c2 Hwt]]]]]]].
    destruct Hwt as [Hwt0 [Hwt1 [Hwt2 [? [Hc Hs]]]]].
    subst.
    Lemma invert_inr t1 e t c s :
      |- [] (Einr t1 e) t c s ->
      exists t2 c2 s2,
        |- [] e t2 c2 s2 /\
        t = Tsum t1 t2 /\
        c2 <= c /\
        Sinlinr S0 s2 <= s.
      admit.
    Qed.
    eapply invert_inr in Hwt0.
    destruct Hwt0 as [t2' [c2' [s2' Hwt0]]].
    destruct Hwt0 as [Htw0 [Ht [Hc0 Hss]]].
    symmetry in Ht; inject Ht.
    exists (subst s2 c2).
    split.
    {
      eapply TPsub.
      { 
        replace tau with (subst s2 (shift1 CEexpr tau)).
        {
          eapply subst_wt; eauto.
          eapply TPsub; eauto.
          eapply Sinlinr_le_le in Hss.
          eapply Hss.
        }
        eapply subst_shift1_s_t.
      }
      { eauto. }
      rewrite (@subst_shift1_s_s []).
      eauto.
    }
    admit. (* le *)
  }
  {
    (* Case Unhide-hide *)
    Lemma invert_unhide e t c s :
      |- [] (Eunhide e) t c s ->
      exists c' s',
        |- [] e (Thide t) c' (Shide s') /\
        c' + F1 <= c /\
        s' <= s.
      admit.
    Qed.
    eapply invert_unhide in Hwt.
    destruct Hwt as [c' [s' Hwt]].
    destruct Hwt as [Hwt [Hc Hs]].
    Lemma invert_hide e t c s :
      |- [] (Ehide e) t c s ->
      exists t' c' s',
        |- [] e t' c' s' /\
        t = Thide t' /\
        c' <= c /\
        Shide s' <= s.
      admit.
    Qed.
    eapply invert_hide in Hwt.
    destruct Hwt as [t1' [c1 [s1 Hwt]]].
    destruct Hwt as [Hwt [Ht1' [Hc' Hs']]].
    symmetry in Ht1'; inject Ht1'.
    exists c'.
    split.
    {
      eapply TPsub.
      { eauto. }
      { eauto. }
      { etransitivity; [ | eauto ].
        Lemma Shide_le_le (a b : size) :
          Shide a <= Shide b ->
          a <= b.
          admit.
        Qed.
        eapply Shide_le_le; eauto.
      }
    }
    admit. (* le *)
  }
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
