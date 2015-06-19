(* Type soundness *)

Require Import List.
Require Import Program.
Require Import Util.
Require Import Typing EvalCBV.
Require Import TypeSoundness1.
Require Import ssreflect.

Import ListNotations.
Local Open Scope list_scope.

Set Implicit Arguments.

Lemma LRbind E (wE : width) (wBE : width) s₁ c₂ s₂ {lctx lctx'} (τ : open_type lctx) (τ' : open_type lctx') ctx (ρ : csubsts lctx ctx) (ρ' : csubsts lctx' ctx) :
  [] |~~ 
     ∀e we c₁ wBe, 
       ⌈IsEC E⌉ /\
       (e, we) ∈ relE τ wBe c₁ s₁ ρ /\ 
       relEC E e we (Wapp wE we) (WappB wBE we) s₁ c₂ s₂ τ τ' ρ ρ' ===> 
       (E $$ e, Wapp wE we) ∈ relE τ' (wBe + WappB wBE we) (c₁ + !c₂) s₂ ρ'.
Proof.
  eapply VLob.
  set (Hlob := 
      openup1 (▹ [])
      ((∀e we c₁ wBe,
          ⌈IsEC E⌉ /\
          (e, we) ∈ relE τ wBe c₁ s₁ ρ /\
          relEC E e we (Wapp wE we) (WappB wBE we) s₁ c₂ s₂ τ τ' ρ ρ' ===>
                (E $$ e, Wapp wE we) ∈ relE τ' (wBe + WappB wBE we) (c₁ + !c₂) s₂ ρ'
       ) : open_rel [] _ _)).
  
  eapply forall1_intro.
  eapply openup1_forall1.
  eapply openup2_forall1.
  eapply openup3_forall1.
  rewrite openup4_imply.
  eapply ORimply_intro.
  rewrite openup4_and.
  eapply destruct_and.
  eapply totop with (n := 1); [ reflexivity | unfold removen ].
  rewrite openup4_and.
  eapply destruct_and.
  set (Ps := _ :: _ :: _ :: _).
  combine_lift.
  eapply openup4_apply.
  {
    intros.
    eapply relE_intro.
  }
  rewrite openup4_and.
  eapply split.
  {
    admit. (* typing *)
  }
  rewrite openup4_and.
  eapply split.
  {
    rewrite openup4_totop2.
    rewrite openup4_shrink.
    subst Ps.
    eapply dup_premise.
    eapply openup4_apply_in.
    {
      intros.
      eapply relE_elim.
    }
    rewrite openup4_and.
    eapply destruct_and.
    eapply totop with (n := 1); [ reflexivity | unfold removen ].
    rewrite openup4_and.
    eapply destruct_and.
    eapply totop with (n := 1); [ reflexivity | unfold removen ].
    rewrite openup4_and.
    eapply destruct_and.
    eapply totop with (n := 1); [ reflexivity | unfold removen ].
    rewrite openup4_and.
    eapply destruct_and.
    eapply totop with (n := 1); [ reflexivity | unfold removen ].
    rewrite openup4_and.
    eapply destruct_and.
    rewrite openup4_totop1.
    rewrite openup4_shrink.
    rewrite openup3_totop1.
    rewrite openup3_shrink.
    rewrite openup2_totop1.
    rewrite openup2_shrink.
    eapply openup1_apply_in.
    {
      intros.
      eapply inj_exists_elim.
    }
    eapply openup1_exists1_elim.
    repeat rewrite liftPs_cons.
    repeat rewrite lift_openup4.
    combine_lift.
    rewrite lift_openup3.
    unfold liftPs, liftPs1, map.
    eapply totop with (n := 1); [ reflexivity | unfold removen ].
    rewrite openup4_shrink.
    rewrite openup3_totop1.
    rewrite openup3_shrink.
    rewrite openup2_totop1.
    rewrite openup2_shrink.
    eapply openup1_apply_in.
    {
      intros.
      eapply inj_exists_elim.
    }
    eapply openup1_exists1_elim.
    repeat rewrite liftPs_cons.
    repeat rewrite lift_openup4.
    combine_lift.
    rewrite lift_openup3.
    unfold liftPs, liftPs1, map.
    totopn 1.
    rewrite lift_openup2.
    eapply dup_premise.
    Lemma runsto_runstoEx e v :
      e ⇓ v -> exists m,⇓*# e m v.
      admit.
    Qed.
    eapply openup2_apply_in.
    {
      intros.
      eapply imply_trans; first last.
      {
        eapply inj_imply.
        eapply runsto_runstoEx.
      }
      eapply inj_exists_elim.
    }
    eapply openup2_exists1_elim.
    repeat rewrite liftPs_cons.
    combine_lift.
    unfold liftPs, liftPs1, map.
    Definition Rlatern n {ctx} (P : rel 0 ctx) : rel 0 ctx := iter n (Rlater []) P.
    Notation "▹#" := Rlatern : rel.
    Notation "|>#" := Rlatern (only parsing) : rel.
    Lemma relE_elim_3_latern e w lctx τ wB c s ctx (ρ : csubsts lctx ctx) :
      [] |~~ (e, w) ∈ relE τ wB c s ρ ===> ∀m v w', ⌈⇓*# e m v /\ wrunsto w w'⌉%type ===> ▹# m ((v, w') ∈ relV τ ρ) /\ ⌈!v ≤ s⌉.
      admit.
    Qed. 
    totopn 7.
    rewrite lift_openup4.
    eapply openup4_apply_in.
    {
      intros.
      eapply relE_elim_3_latern.
    }
    rewrite openup4_totop2.
    rewrite openup4_shrink.
    rewrite openup3_totop2.
    rewrite openup3_shrink.
    rewrite lift_openup2.
    combine_lift.
    eapply openup2_forall1_elim with (x := V0).
    eapply openup3_forall1_elim with (x := V2).
    eapply openup4_forall1_elim with (x := V1).
    rewrite openup5_imply.
    eapply imply_eelim.
    {
      set (Ps := [_;_;_;_;_;_;_;_;_;_]).
      eapply openup5_apply.
      {
        intros.
        eapply inj_and_intro.
      }
      rewrite openup5_and.
      eapply split.
      {
        rewrite openup5_totop1.
        rewrite openup5_shrink.
        rewrite openup4_totop3.
        rewrite openup4_shrink.
        rewrite openup3_totop1.
        rewrite openup3_totop2.
        rewrite openup3_totop2.
        subst Ps.
        eapply ctx_refl.
      }
      rewrite openup5_shrink.
      rewrite openup4_totop1.
      rewrite openup4_shrink.
      rewrite openup3_totop1.
      rewrite openup3_shrink.
      subst Ps.
      totopn 2.
      eapply ctx_refl.
    }
    rewrite openup5_shrink.
    rewrite openup4_shrink.
    rewrite openup3_and.
    eapply destruct_and.
    totopn 9.
    rewrite openup4_totop2.
    rewrite openup4_shrink.
    rewrite openup3_totop2.
    rewrite openup3_shrink.
    eapply dup_premise.
    Lemma relEC_elim_latern (E : econtext) e we (wEe : width) (wBEe : open_width WTnat []) (s₁ : size) (c₂ : cexpr) (s₂ : size) {lctx lctx'} (τ : open_type lctx) (τ' : open_type lctx') ctx (ρ : csubsts lctx ctx) (ρ' : csubsts lctx' ctx) :
      [] |~~ relEC E e we wEe wBEe s₁ c₂ s₂ τ τ' ρ ρ' ===> ∀m v we', ▹# m ((v, we') ∈ relV τ ρ) /\ ⌈e ~>* v /\ !v ≤ s₁ /\ wsteps we we'⌉ ===> ▹# m ((E $ v, wEe) ∈ relE τ' wBEe !c₂ s₂ ρ').
      admit.
    Qed.
    repeat rewrite lift_openup2.
    eapply openup2_apply_in.
    {
      intros.
      eapply relEC_elim_latern.
    }
    combine_lift.
    eapply openup2_forall1_elim with (x := V0).
    eapply openup3_forall1_elim with (x := V2).
    eapply openup4_forall1_elim with (x := V1).
    rewrite openup5_imply.
    eapply imply_eelim.
    {
      rewrite openup5_and.
      eapply split.
      {
        repeat rewrite openup5_shrink.
        repeat rewrite openup4_shrink.
        totopn 1.
        eapply ctx_refl.
      }
      admit. (* ⌈x1 ~>* x3 /\ !x3 ≤ s₁ /\ wsteps x2 x4⌉ *)
    }
    rewrite openup5_shrink.
    rewrite openup4_totop3.
    rewrite openup4_shrink.
    eapply openup3_apply_in.
    {
      intros.
      Lemma latern_mono n ctx (P Q : rel 0 ctx) :
        [] |~~ P ===> Q ->
        [] |~~ ▹# n P ===> ▹# n Q.
        admit.
      Qed.
      eapply latern_mono.
      eapply relE_elim.
    }
    Lemma latern_and_distr n ctx (P Q : rel 0 ctx) :
      [] |~~ |># n (P /\ Q) ===> (|># n P) /\ (|># n Q).
      admit.
    Qed.
    eapply openup3_apply_in.
    {
      intros.
      eapply latern_and_distr.
    }
    rewrite openup3_and.
    eapply destruct_and.
    eapply totop with (n := 1); [ reflexivity | unfold removen ].
    eapply openup3_apply_in.
    {
      intros.
      eapply latern_and_distr.
    }
    rewrite openup3_and.
    eapply destruct_and.
    Lemma latern_inj n ctx P :
      [] |~~ ▹# n [| P |] ===> ([| P |] : rel 0 ctx).
      admit.
    Qed.
    eapply openup3_apply_in.
    {
      intros.
      eapply latern_inj.
    }
    eapply openup3_apply_in.
    {
      intros.
      eapply inj_exists_elim.
    }
    rewrite openup3_totop1.
    rewrite openup3_shrink.
    eapply openup2_exists1_elim.
    repeat rewrite liftPs_cons.
    repeat rewrite lift_openup4.
    combine_lift.
    unfold liftPs, liftPs1, map.
    totopn 11.
    rewrite openup4_totop1.
    rewrite openup4_shrink.
    rewrite openup3_totop1.
    rewrite openup3_shrink.
    eapply openup2_apply_in.
    {
      intros.
      eapply inj_exists_elim.
    }
    eapply openup2_exists1_elim.
    repeat rewrite liftPs_cons.
    repeat rewrite lift_openup4.
    combine_lift.
    unfold liftPs, liftPs1, map.
    repeat erewrite lift_openup3.
    set (Ps := [_;_;_;_;_;_;_;_;_;_;_;_;_;_;_]).
    eapply openup3_apply.
    {
      intros.
      eapply inj_exists_intro.
    }
    eapply openup3_exists1 with (x := openup2 add V0 V1).
    erewrite openup4_comp_openup2.
    subst Ps.
    eapply openup3_apply_in.
    {
      intros.
      eapply inj_and_elim.
    }
    rewrite openup3_and.
    eapply destruct_and.
    rewrite openup3_shrink.
    eapply totop with (n := 2); [ reflexivity | unfold removen ].
    erewrite lift_openup2.
    eapply openup3_apply_in.
    {
      intros.
      eapply inj_and_elim.
    }
    rewrite openup3_and.
    eapply destruct_and.
    rewrite openup3_totop1.
    rewrite openup3_shrink.
    set (Ps := [_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_]).
    eapply openup5_apply.
    {
      intros.
      eapply inj_and_intro.
    }
    rewrite openup5_and.
    eapply split.
    {
      rewrite openup5_totop2.
      rewrite openup5_shrink.
      eapply openup4_apply.
      {
        intros.
        eapply imply_trans.
        {
          eapply inj_imply.
          {
            eapply Wadd_wsteps.
          }
        }
        eapply inj_and_intro.
      }
      rewrite openup4_and.
      eapply split.
      {
        rewrite openup4_totop1.
        rewrite openup4_shrink.
        rewrite openup3_totop1.
        rewrite openup3_shrink.
        subst Ps.
        eapply totop with (n := 2); [ reflexivity | unfold removen ].
        eapply ctx_refl.
      }
      rewrite openup4_shrink.
      rewrite openup3_totop2.
      rewrite openup3_shrink.
      subst Ps.
      eapply ctx_refl.
    }
    rewrite openup5_totop3.
    rewrite openup5_shrink.
    rewrite openup4_totop3.
    rewrite openup4_shrink.
    combine_lift.
    eapply openup3_apply.
    {
      intros.
      eapply imply_trans.
      {
        eapply inj_imply.
        {
          eapply plug_steps_0.
        }
      }
      eapply inj_and_intro.
    }
    rewrite openup3_and.
    eapply split.
    {
      rewrite openup3_totop1.
      rewrite openup3_shrink.
      subst Ps.
      eapply totop with (n := 3); [ reflexivity | unfold removen ].
      rewrite openup3_totop1.
      rewrite openup3_shrink.
      eapply ctx_refl.
    }
    rewrite openup3_shrink.
    eapply openup2_apply.
    {
      intros.
      eapply inj_exists_intro.
    }
    eapply openup2_exists1 with (x := V4).
    eapply openup3_apply.
    {
      intros.
      eapply inj_and_intro.
    }
    rewrite openup3_and.
    eapply split.
    {
      rewrite openup3_totop1.
      rewrite openup3_shrink.
      subst Ps.
      eapply totop with (n := 10); [ reflexivity | unfold removen ].
      erewrite lift_openup2.
      rewrite openup2_totop1.
      eapply ctx_refl.
    }
    rewrite openup3_totop2.
    rewrite openup3_shrink.
    subst Ps.
    eapply totop with (n := 1); [ reflexivity | unfold removen ].
    eapply ctx_refl.
  }
  rewrite openup4_and.
  eapply split.
  {
    rewrite openup4_totop2.
    rewrite openup4_shrink.
    rewrite openup3_totop2.
    rewrite openup3_shrink.
    eapply openup2_forall1.
    eapply openup3_forall1.
    rewrite openup4_imply.
    eapply ORimply_intro.
    subst Ps.
    repeat rewrite liftPs_cons.
    repeat rewrite lift_openup4.
    combine_lift.
    unfold liftPs, liftPs1, map.
    eapply openup4_apply_in.
    {
      intros.
      eapply inj_and_elim.
    }
    rewrite openup4_and.
    eapply destruct_and.
    rewrite openup4_totop1.
    rewrite openup4_shrink.
    rewrite openup3_totop2.
    rewrite openup3_shrink.
    eapply openup2_apply_in.
    {
      intros.
      eapply imply_trans; last first.
      {
        eapply inj_imply.
        {
          eapply plug_runsto_0_elim.
        }
      }
      eapply inj_exists_elim.
    }
    eapply openup2_exists1_elim.
    repeat rewrite liftPs_cons.
    repeat rewrite lift_openup4.
    combine_lift.
    unfold liftPs, liftPs1, map.
    eapply openup3_apply_in.
    {
      intros.
      eapply inj_and_elim.
    }
    rewrite openup3_and.
    eapply destruct_and.
    rewrite openup3_totop1.
    rewrite openup3_shrink.
    eapply totop with (n := 2); [ reflexivity | unfold removen ].
    rewrite openup4_shrink.
    rewrite openup3_totop1.
    rewrite openup3_shrink.
    eapply dup_premise.
    eapply openup2_apply_in.
    {
      intros.
      eapply imply_trans; last first.
      {
        eapply inj_imply.
        {
          eapply app_wrunsto_elim.
        }
      }
      eapply inj_exists_elim.
    }
    eapply openup2_exists1_elim.
    repeat rewrite liftPs_cons.
    repeat rewrite lift_openup4.
    combine_lift.
    unfold liftPs, liftPs1, map.
    eapply openup3_apply_in.
    {
      intros.
      eapply inj_and_elim.
    }
    rewrite openup3_and.
    eapply destruct_and.
    rewrite openup3_totop1.
    rewrite openup3_shrink.
    eapply totop with (n := 5); [ reflexivity | unfold removen ].
    eapply dup_premise.
    eapply openup4_apply_in.
    {
      intros.
      eapply relE_elim.
    }
    rewrite openup4_and.
    eapply destruct_and.
    eapply totop with (n := 1); [ reflexivity | unfold removen ].
    rewrite openup4_and.
    eapply destruct_and.
    eapply totop with (n := 1); [ reflexivity | unfold removen ].
    rewrite openup4_and.
    eapply destruct_and.
    rewrite openup4_totop2.
    rewrite openup4_shrink.
    rewrite openup3_totop2.
    rewrite openup3_shrink.
    rewrite lift_openup2.
    rewrite lift_openup3.
    combine_lift.
    eapply openup2_forall1_elim with (x := V1).
    eapply openup3_forall1_elim with (x := V0).
    rewrite openup4_imply.
    eapply imply_eelim.
    {
      set (Ps := [_;_;_;_;_;_;_;_;_;_;_;_]).
      eapply openup4_apply.
      {
        intros.
        eapply inj_and_intro.
      }
      rewrite openup4_and.
      eapply split.
      {
        rewrite openup4_totop1.
        rewrite openup4_shrink.
        rewrite openup3_totop2.
        rewrite openup3_shrink.
        subst Ps.
        eapply totop with (n := 7); [ reflexivity | unfold removen ].
        eapply ctx_refl.
      }
      rewrite openup4_shrink.
      rewrite openup3_totop1.
      rewrite openup3_shrink.
      subst Ps.
      eapply totop with (n := 4); [ reflexivity | unfold removen ].
      eapply ctx_refl.
    }
    rewrite openup4_shrink.
    rewrite openup3_shrink.
    rewrite openup2_and.
    eapply destruct_and.
    eapply totop with (n := 11); [ reflexivity | unfold removen ].
    eapply dup_premise.
    unfold relEC at 1.
    rewrite openup4_totop2.
    rewrite openup4_shrink.
    rewrite openup3_totop2.
    rewrite openup3_shrink.
    eapply openup2_forall1_elim with (x := V1).
    eapply openup3_forall1_elim with (x := V0).
    rewrite openup4_imply.
    eapply imply_eelim.
    {
      set (Ps := [_;_;_;_;_;_;_;_;_;_;_;_;_;_]).
      rewrite openup4_and.
      eapply split.
      {
        rewrite openup4_shrink.
        rewrite openup3_shrink.
        subst Ps.
        eapply totop with (n := 1); [ reflexivity | unfold removen ].
        eapply ctx_refl.
      }
      eapply openup4_apply.
      {
        intros.
        eapply inj_and_intro.
      }
      rewrite openup4_and.
      eapply split.
      {
        rewrite openup4_totop1.
        rewrite openup4_shrink.
        rewrite openup3_totop2.
        rewrite openup3_shrink.
        subst Ps.
        eapply totop with (n := 10); [ reflexivity | unfold removen ].
        rewrite lift_openup2.
        eapply openup2_apply_in.
        {
          intros.
          eapply inj_imply.
          eapply runstoEx_steps.
        }
        eapply ctx_refl.
      }
      rewrite openup4_shrink.
      eapply openup3_apply.
      {
        intros.
        eapply inj_and_intro.
      }
      rewrite openup3_and.
      eapply split.
      {
        rewrite openup3_shrink.
        rewrite openup2_totop1.
        rewrite openup2_shrink.
        subst Ps.
        eapply totop with (n := 2); [ reflexivity | unfold removen ].
        rewrite openup2_totop1.
        rewrite openup2_shrink.
        eapply ctx_refl.
      }
      rewrite openup3_totop1.
      rewrite openup3_shrink.
      subst Ps.
      eapply totop with (n := 7); [ reflexivity | unfold removen ].
      eapply openup2_apply_in.
      {
        intros.
        eapply inj_imply.
        {
          intros H.
          unfold wrunsto in H.
          destruct H as [H1 H2].
          exact H1.
        }
      }
      eapply ctx_refl.
    }
    rewrite openup4_shrink.
    rewrite openup3_totop2.
    rewrite openup3_shrink.
    eapply openup2_apply_in.
    {
      intros.
      eapply relE_elim.
    }
    rewrite openup2_and.
    eapply destruct_and.
    eapply totop with (n := 1); [ reflexivity | unfold removen ].
    rewrite openup2_and.
    eapply destruct_and.
    eapply totop with (n := 1); [ reflexivity | unfold removen ].
    rewrite openup2_and.
    eapply destruct_and.
    eapply openup2_forall1_elim with (x := V3).
    eapply openup3_forall1_elim with (x := V2).
    rewrite openup4_imply.
    eapply imply_eelim.
    {
      set (Ps := [_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_]).
      eapply openup4_apply.
      {
        intros.
        eapply inj_and_intro.
      }
      rewrite openup4_and.
      eapply split.
      {
        rewrite openup4_shrink.
        rewrite openup3_totop2.
        rewrite openup3_shrink.
        subst Ps.
        eapply totop with (n := 14); [ reflexivity | unfold removen ].
        rewrite openup3_shrink.
        rewrite openup2_totop1.
        eapply ctx_refl.
      }
      rewrite openup4_totop1.
      rewrite openup4_shrink.
      rewrite openup3_totop1.
      rewrite openup3_shrink.
      subst Ps.
      eapply totop with (n := 12); [ reflexivity | unfold removen ].
      eapply ctx_refl.
    }
    rewrite openup4_shrink.
    rewrite openup3_shrink.
    set (Ps := [_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_]).
    rewrite openup4_shrink.
    rewrite openup3_shrink.
    eapply ctx_refl.
  }
  rewrite openup4_and.
  eapply split.
  {
    (* subgoal (4) *)
    eapply openup4_forall1.
    rewrite openup5_imply.
    rewrite openup5_shrink.
    eapply ORimply_intro.
    subst Ps.
    repeat rewrite liftPs_cons.
    repeat rewrite lift_openup4.
    combine_lift.
    unfold liftPs, liftPs1, map.
    rewrite openup5_totop2.
    rewrite openup5_shrink.
    rewrite openup4_totop2.
    rewrite openup4_shrink.
    eapply openup3_apply_in.
    {
      intros.
      eapply inj_and_elim.
    }
    rewrite openup3_and.
    eapply destruct_and.
    eapply openup3_apply_in.
    {
      intros.
      eapply imply_trans; last first.
      {
        eapply inj_imply.
        {
          eapply plug_steps_1_elim.
        }
      }
      eapply inj_or_elim.
    }
    rewrite openup3_or.
    eapply destruct_or.
    {
      rewrite openup3_totop1.
      rewrite openup3_shrink.
      eapply openup2_apply_in.
      {
        intros.
        eapply inj_exists_elim.
      }
      eapply openup2_exists1_elim.
      repeat rewrite liftPs_cons.
      repeat rewrite lift_openup4.
      combine_lift.
      unfold liftPs, liftPs1, map.
      eapply openup3_apply_in.
      {
        intros.
        eapply inj_and_elim.
      }
      rewrite openup3_and.
      eapply destruct_and.
      rewrite openup3_totop1.
      rewrite openup3_shrink.
      eapply totop with (n := 2); [ reflexivity | unfold removen ].
      rewrite lift_openup3.
      rewrite openup3_shrink.
      rewrite openup2_totop1.
      rewrite openup2_shrink.
      eapply openup1_apply_in.
      {
        intros.
        eapply inj_exists_elim.
      }
      eapply openup1_exists1_elim.
      repeat rewrite liftPs_cons.
      repeat rewrite lift_openup4.
      combine_lift.
      unfold liftPs, liftPs1, map.
      eapply dup_premise.
      eapply openup2_apply_in.
      {
        intros.
        eapply imply_trans; last first.
        {
          eapply inj_imply.
          {
            eapply app_wrunsto_elim.
          }
        }
        eapply inj_exists_elim.
      }
      eapply openup2_exists1_elim.
      repeat rewrite liftPs_cons.
      repeat rewrite lift_openup4.
      combine_lift.
      unfold liftPs, liftPs1, map.
      eapply openup3_apply_in.
      {
        intros.
        eapply inj_and_elim.
      }
      rewrite openup3_and.
      eapply destruct_and.
      rewrite openup3_totop1.
      rewrite openup3_shrink.
      eapply totop with (n := 5); [ reflexivity | unfold removen ].
      eapply dup_premise.
      eapply openup4_apply_in.
      {
        intros.
        eapply relE_elim.
      }
      rewrite openup4_and.
      eapply destruct_and.
      eapply totop with (n := 1); [ reflexivity | unfold removen ].
      rewrite openup4_and.
      eapply destruct_and.
      eapply totop with (n := 1); [ reflexivity | unfold removen ].
      rewrite openup4_and.
      eapply destruct_and.
      rewrite openup4_totop2.
      rewrite openup4_shrink.
      rewrite openup3_totop2.
      rewrite openup3_shrink.
      repeat rewrite lift_openup2.
      rewrite lift_openup3.
      combine_lift.
      eapply openup2_forall1_elim with (x := V2).
      eapply openup3_forall1_elim with (x := V0).
      rewrite openup4_imply.
      eapply imply_eelim.
      {
        set (Ps := [_;_;_;_;_;_;_;_;_;_;_;_]).
        eapply openup4_apply.
        {
          intros.
          eapply inj_and_intro.
        }
        rewrite openup4_and.
        eapply split.
        {
          rewrite openup4_totop1.
          rewrite openup4_shrink.
          rewrite openup3_totop2.
          rewrite openup3_shrink.
          subst Ps.
          eapply totop with (n := 7); [ reflexivity | unfold removen ].
          eapply ctx_refl.
        }
        rewrite openup4_shrink.
        rewrite openup3_totop1.
        rewrite openup3_shrink.
        subst Ps.
        eapply totop with (n := 4); [ reflexivity | unfold removen ].
        eapply ctx_refl.
      }
      rewrite openup4_shrink.
      rewrite openup3_shrink.
      rewrite openup2_and.
      eapply destruct_and.
      eapply totop with (n := 11); [ reflexivity | unfold removen ].
      eapply dup_premise.
      unfold relEC at 1.
      rewrite openup4_totop2.
      rewrite openup4_shrink.
      rewrite openup3_totop2.
      rewrite openup3_shrink.
      eapply openup2_forall1_elim with (x := V2).
      eapply openup3_forall1_elim with (x := V0).
      rewrite openup4_imply.
      eapply imply_eelim.
      {
        set (Ps := [_;_;_;_;_;_;_;_;_;_;_;_;_;_]).
        rewrite openup4_and.
        eapply split.
        {
          rewrite openup4_shrink.
          rewrite openup3_shrink.
          subst Ps.
          eapply totop with (n := 1); [ reflexivity | unfold removen ].
          eapply ctx_refl.
        }
        eapply openup4_apply.
        {
          intros.
          eapply inj_and_intro.
        }
        rewrite openup4_and.
        eapply split.
        {
          rewrite openup4_totop1.
          rewrite openup4_shrink.
          rewrite openup3_totop2.
          rewrite openup3_shrink.
          subst Ps.
          eapply totop with (n := 10); [ reflexivity | unfold removen ].
          eapply openup2_apply_in.
          {
            intros.
            eapply inj_imply.
            eapply runstoEx_steps.
          }
          eapply ctx_refl.
        }
        rewrite openup4_shrink.
        eapply openup3_apply.
        {
          intros.
          eapply inj_and_intro.
        }
        rewrite openup3_and.
        eapply split.
        {
          rewrite openup3_shrink.
          rewrite openup2_totop1.
          rewrite openup2_shrink.
          subst Ps.
          eapply totop with (n := 2); [ reflexivity | unfold removen ].
          rewrite openup2_totop1.
          rewrite openup2_shrink.
          eapply ctx_refl.
        }
        rewrite openup3_totop1.
        rewrite openup3_shrink.
        subst Ps.
        eapply totop with (n := 7); [ reflexivity | unfold removen ].
        eapply openup2_apply_in.
        {
          intros.
          eapply inj_imply.
          {
            intros H.
            unfold wrunsto in H.
            destruct H as [H1 H2].
            exact H1.
          }
        }
        eapply ctx_refl.
      }
      rewrite openup4_shrink.
      rewrite openup3_totop2.
      rewrite openup3_shrink.
      eapply openup2_apply_in.
      {
        intros.
        eapply relE_elim.
      }
      rewrite openup2_and.
      eapply destruct_and.
      eapply totop with (n := 1); [ reflexivity | unfold removen ].
      rewrite openup2_and.
      eapply destruct_and.
      eapply totop with (n := 1); [ reflexivity | unfold removen ].
      rewrite openup2_and.
      eapply destruct_and.
      eapply totop with (n := 1); [ reflexivity | unfold removen ].
      rewrite openup2_and.
      eapply destruct_and.
      eapply openup2_forall1_elim with (x := V3).
      rewrite openup3_imply.
      eapply imply_eelim.
      {
        set (Ps := [_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_]).
        eapply openup3_apply.
        {
          intros.
          eapply inj_and_intro.
        }
        rewrite openup3_and.
        eapply split.
        {
          rewrite openup3_shrink.
          subst Ps.
          eapply totop with (n := 15); [ reflexivity | unfold removen ].
          rewrite openup3_shrink.
          rewrite openup2_totop1.
          eapply ctx_refl.
        }
        rewrite openup3_totop1.
        rewrite openup3_shrink.
        rewrite openup2_totop1.
        rewrite openup2_shrink.
        eapply openup1_apply.
        {
          intros.
          eapply inj_exists_intro.
        }
        eapply openup1_exists1 with (x := V1).
        subst Ps.
        eapply totop with (n := 13); [ reflexivity | unfold removen ].
        rewrite openup2_totop1.
        eapply ctx_refl.
      }
      rewrite openup3_totop1.
      rewrite openup3_shrink.
      rewrite openup2_and.
      eapply destruct_and.
      rewrite openup2_shrink.
      rewrite openup1_shrink.
      set (Ps := [_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_]).
      rewrite openup4_and.
      eapply split.
      {
        rewrite openup4_shrink.
        rewrite openup3_totop1.
        rewrite openup3_shrink.
        rewrite openup2_totop1.
        rewrite openup2_shrink.
        eapply openup1_apply.
        {
          intros.
          eapply inj_imply.
          eapply lt_plus_trans_r.
        }
        rewrite openup1_shrink.
        subst Ps.
        eapply ctx_refl.
      }
      rewrite openup4_later.
      eapply later_mono_ctx.
      {
        eapply openup4_apply.
        {
          intros.
          eapply relE_mono_wB_c with (τ := τ') (wB := WappB wBE x1) (c := !c₂ - 1).
        }
        eapply ctx_refl.
      }
      rewrite openup4_and.
      rewrite later_and_distr.
      eapply split.
      {
        rewrite openup4_totop1.
        rewrite openup4_shrink.
        rewrite openup3_totop1.
        rewrite openup3_shrink.
        subst Ps.
        eapply totop with (n := 1); [ reflexivity | unfold removen ].
        eapply ctx_refl.
      }
      eapply VMono.
      rewrite openup4_totop3.
      rewrite openup4_shrink.
      eapply openup3_apply.
      {
        intros.
        eapply inj_imply.
        intros H.
        eapply relE_mono_wB_c_VC.
      }
      instantiate (1 := True).
      rewrite openup3_shrink.
      rewrite openup2_shrink.
      rewrite openup1_shrink.
      eapply inj_true_intro.
    }
    rewrite openup3_totop1.
    rewrite openup3_shrink.
    eapply openup2_apply_in.
    {
      intros.
      eapply inj_exists_elim.
    }
    eapply openup2_exists1_elim.
    repeat rewrite liftPs_cons.
    repeat rewrite lift_openup4.
    combine_lift.
    unfold liftPs, liftPs1, map.
    eapply openup3_apply_in.
    {
      intros.
      eapply inj_and_elim.
    }
    rewrite openup3_and.
    eapply destruct_and.
    rewrite openup3_totop1.
    rewrite openup3_shrink.
    eapply totop with (n := 2); [ reflexivity | unfold removen ].
    rewrite lift_openup3.
    rewrite openup3_shrink.
    rewrite openup2_totop1.
    rewrite openup2_shrink.
    eapply openup1_apply_in.
    {
      intros.
      eapply inj_exists_elim.
    }
    eapply openup1_exists1_elim.
    repeat rewrite liftPs_cons.
    repeat rewrite lift_openup4.
    combine_lift.
    unfold liftPs, liftPs1, map.
    eapply dup_premise.
    eapply openup2_apply_in.
    {
      intros.
      eapply imply_trans; last first.
      {
        eapply inj_imply.
        {
          eapply app_wrunsto_elim.
        }
      }
      eapply inj_exists_elim.
    }
    eapply openup2_exists1_elim.
    repeat rewrite liftPs_cons.
    repeat rewrite lift_openup4.
    combine_lift.
    unfold liftPs, liftPs1, map.
    eapply openup3_apply_in.
    {
      intros.
      eapply inj_and_elim.
    }
    rewrite openup3_and.
    eapply destruct_and.
    rewrite openup3_totop1.
    rewrite openup3_shrink.
    eapply totop with (n := 5); [ reflexivity | unfold removen ].
    eapply dup_premise.
    eapply openup4_apply_in.
    {
      intros.
      eapply relE_elim.
    }
    rewrite openup4_and.
    eapply destruct_and.
    eapply totop with (n := 1); [ reflexivity | unfold removen ].
    rewrite openup4_and.
    eapply destruct_and.
    eapply totop with (n := 1); [ reflexivity | unfold removen ].
    rewrite openup4_and.
    eapply destruct_and.
    eapply totop with (n := 1); [ reflexivity | unfold removen ].
    rewrite openup4_and.
    eapply destruct_and.
    repeat rewrite lift_openup2.
    rewrite lift_openup3.
    combine_lift.
    eapply openup4_forall1_elim with (x := V2).
    rewrite openup5_imply.
    eapply imply_eelim.
    {
      set (Ps := [_;_;_;_;_;_;_;_;_;_;_;_;_]).
      eapply openup5_apply.
      {
        intros.
        eapply inj_and_intro.
      }
      rewrite openup5_and.
      eapply split.
      {
        rewrite openup5_totop1.
        rewrite openup5_shrink.
        rewrite openup4_totop1.
        rewrite openup4_shrink.
        rewrite openup3_totop1.
        rewrite openup3_shrink.
        subst Ps.
        eapply totop with (n := 8); [ reflexivity | unfold removen ].
        eapply ctx_refl.
      }
      rewrite openup5_shrink.
      rewrite openup4_totop1.
      rewrite openup4_shrink.
      rewrite openup3_totop1.
      rewrite openup3_shrink.
      rewrite openup2_totop1.
      rewrite openup2_shrink.
      eapply openup1_apply.
      {
        intros.
        eapply inj_exists_intro.
      }
      eapply openup1_exists1 with (x := V0).
      subst Ps.
      eapply totop with (n := 5); [ reflexivity | unfold removen ].
      rewrite openup2_totop1.
      eapply ctx_refl.
    }
    rewrite openup5_shrink.
    rewrite openup4_and.
    eapply destruct_and.
    rewrite openup4_shrink.
    rewrite openup3_totop1.
    rewrite openup3_shrink.
    rewrite openup2_totop1.
    rewrite openup2_shrink.
    set (Ps := [_;_;_;_;_;_;_;_;_;_;_;_;_;_;_]).
    rewrite openup4_and.
    eapply split.
    {
      rewrite openup4_shrink.
      rewrite openup3_totop1.
      rewrite openup3_shrink.
      rewrite openup2_totop1.
      rewrite openup2_shrink.
      eapply openup1_apply.
      {
        intros.
        eapply inj_imply.
        eapply Plus.lt_plus_trans.
      }
      subst Ps.
      eapply ctx_refl.
    }
    subst Ps.
    eapply totop with (n := 12); [ reflexivity | unfold removen ].
    rewrite openup4_totop2.
    rewrite openup4_shrink.
    rewrite openup3_totop2.
    rewrite openup3_shrink.
    eapply assert with (P := openup2
      (fun (x2 : expr) (x3 : width) =>
       relEC E x2 x3 (Wapp wE x3) (WappB wBE x3) s₁ c₂ s₂ τ τ' ρ ρ') V2 V6).
    {
      eapply openup2_apply.
      {
        intros.
        eapply relEC_red.
      }
      eapply openup2_exists1 with (x := V7).
      rewrite openup3_and.
      eapply split.
      {
        set (Ps := [_;_;_;_;_;_;_;_;_;_;_;_;_;_;_]).
        rewrite openup3_totop2.
        rewrite openup3_shrink.
        eapply openup2_apply.
        {
          intros.
          eapply inj_imply.
          eapply stepsex_steps.
        }
        subst Ps.
        eapply totop with (n := 11); [ reflexivity | unfold removen ].
        eapply ctx_refl.
      }
      set (Ps := [_;_;_;_;_;_;_;_;_;_;_;_;_;_;_]).
      rewrite openup3_totop1.
      rewrite openup3_shrink.
      eapply ctx_refl.
    }
    eapply totop with (n := 15); [ reflexivity | unfold removen ].
    subst Hlob.
    rewrite lift_openup1.
    eapply totop with (n := 4); [ reflexivity | unfold removen ].
    rewrite openup4_later.
    set (Ps := [_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_]).
    rewrite openup4_later.
    eapply later_mono_ctx2; last first.
    {
      eapply split.
      { eapply ctx_refl. }
      subst Ps.
      eapply totop with (n := 1); [ reflexivity | unfold removen ].
      eapply ctx_refl.
    }
    eapply totop with (n := 1); [ reflexivity | unfold removen ].
    rewrite lift_openup0_empty.
    eapply openup0_forall1_elim with (x := V2).
    eapply openup1_forall1_elim with (x := V6).
    eapply openup2_forall1_elim with (x := openup1 (fun x => x - 1) V5).
    eapply openup3_forall1_elim with (x := V4).
    rewrite openup4_totop2.
    rewrite openup4_comp_openup1.
    rewrite openup4_imply.
    eapply imply_eelim.
    {
      subst Ps.
      set (Ps := [_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_]).
      rewrite openup4_and.
      eapply split.
      {
        rewrite openup4_shrink.
        rewrite openup3_shrink.
        rewrite openup2_shrink.
        rewrite openup1_shrink.
        subst Ps.
        eapply totop with (n := 16); [ reflexivity | unfold removen ].
        rewrite openup4_shrink.
        rewrite openup3_shrink.
        rewrite openup2_shrink.
        rewrite openup1_shrink.
        eapply ctx_refl.
      }
      rewrite openup4_and.
      eapply split.
      {
        rewrite openup4_totop1.
        rewrite openup4_totop3.
        rewrite openup4_totop2.
        rewrite openup4_totop3.
        eapply ctx_refl.
      }
      rewrite openup4_shrink.
      rewrite openup3_totop2.
      rewrite openup3_shrink.
      subst Ps.
      eapply totop with (n := 3); [ reflexivity | unfold removen ].
      eapply ctx_refl.
    }
    eapply openup4_apply.
    {
      intros.
      eapply relE_red.
    }
    eapply openup4_exists1 with (x := openup1 (fun x => E $ x) V2).
    rewrite openup5_and.
    subst Ps.
    set (Ps := [_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_]).
    eapply split.
    {
      rewrite openup5_totop1.
      rewrite openup5_shrink.
      rewrite openup4_comp_openup1.
      rewrite openup4_totop1.
      rewrite openup4_shrink.
      rewrite openup3_totop1.
      rewrite openup3_shrink.
      rewrite openup2_totop1.
      subst Ps.
      eapply totop with (n := 16); [ reflexivity | unfold removen ].
      rewrite openup3_shrink.
      eapply ctx_refl.
    }
    rewrite openup5_totop4.
    rewrite openup5_shrink.
    rewrite openup4_comp_openup1.
    eapply openup4_apply.
    {
      intros.
      eapply relE_c_eq.
    }
    rewrite openup4_and.
    eapply split.
    {
      rewrite openup4_totop3.
      rewrite openup4_totop2.
      rewrite openup4_totop2.
      rewrite openup4_totop3.
      eapply ctx_refl.
    }
    rewrite openup4_shrink.
    rewrite openup3_shrink.
    rewrite openup2_totop1.
    rewrite openup2_shrink.
    eapply openup1_apply.
    {
      intros.
      eapply inj_imply.
      eapply swap_minus_plus.
    }
    subst Ps.
    eapply totop with (n := 6); [ reflexivity | unfold removen ].
    eapply ctx_refl.
  }
  rewrite openup4_and.
  eapply split.
  {
    rewrite openup4_totop1.
    rewrite openup4_shrink.
    rewrite openup3_totop1.
    rewrite openup3_shrink.
    rewrite openup2_totop1.
    rewrite openup2_shrink.
    eapply openup1_apply.
    {
      intros.
      eapply imply_trans.
      {
        eapply inj_imply.
        {
          eapply plug_runsto.
        }
      }
      eapply inj_exists_intro.
    }
    subst Ps.
    combine_lift.
    eapply dup_premise.
    eapply openup4_apply_in.
    {
      intros.
      eapply relE_elim.
    }
    rewrite openup4_and.
    eapply destruct_and.
    eapply totop with (n := 1); [ reflexivity | unfold removen ].
    rewrite openup4_and.
    eapply destruct_and.
    eapply totop with (n := 1); [ reflexivity | unfold removen ].
    rewrite openup4_and.
    eapply destruct_and.
    eapply totop with (n := 1); [ reflexivity | unfold removen ].
    rewrite openup4_and.
    eapply destruct_and.
    eapply totop with (n := 1); [ reflexivity | unfold removen ].
    rewrite openup4_and.
    eapply destruct_and.
    rewrite openup4_totop1.
    rewrite openup4_shrink.
    rewrite openup3_totop1.
    rewrite openup3_shrink.
    rewrite openup2_totop1.
    rewrite openup2_shrink.
    eapply openup1_apply_in.
    {
      intros.
      eapply inj_exists_elim.
    }
    eapply openup1_exists1_elim.
    repeat rewrite liftPs_cons.
    repeat rewrite lift_openup4.
    combine_lift.
    unfold liftPs, liftPs1, map.
    eapply totop with (n := 1); [ reflexivity | unfold removen ].
    rewrite openup4_shrink.
    rewrite openup3_totop1.
    rewrite openup3_shrink.
    rewrite openup2_totop1.
    rewrite openup2_shrink.
    eapply openup1_apply_in.
    {
      intros.
      eapply inj_exists_elim.
    }
    eapply openup1_exists1_elim.
    repeat rewrite liftPs_cons.
    repeat rewrite lift_openup4.
    combine_lift.
    unfold liftPs, liftPs1, map.
    totopn 1.
    rewrite lift_openup2.
    eapply dup_premise.
    eapply openup2_apply_in.
    {
      intros.
      eapply imply_trans; first last.
      {
        eapply inj_imply.
        eapply runsto_runstoEx.
      }
      eapply inj_exists_elim.
    }
    eapply openup2_exists1_elim.
    repeat rewrite liftPs_cons.
    combine_lift.
    unfold liftPs, liftPs1, map.
    totopn 7.
    rewrite lift_openup4.
    eapply openup4_apply_in.
    {
      intros.
      eapply relE_elim_3_latern.
    }
    rewrite openup4_totop2.
    rewrite openup4_shrink.
    rewrite openup3_totop2.
    rewrite openup3_shrink.
    rewrite lift_openup2.
    combine_lift.
    eapply openup2_forall1_elim with (x := V0).
    eapply openup3_forall1_elim with (x := V2).
    eapply openup4_forall1_elim with (x := V1).
    rewrite openup5_imply.
    eapply imply_eelim.
    {
      set (Ps := [_;_;_;_;_;_;_;_;_;_]).
      eapply openup5_apply.
      {
        intros.
        eapply inj_and_intro.
      }
      rewrite openup5_and.
      eapply split.
      {
        rewrite openup5_totop1.
        rewrite openup5_shrink.
        rewrite openup4_totop3.
        rewrite openup4_shrink.
        rewrite openup3_totop1.
        rewrite openup3_totop2.
        rewrite openup3_totop2.
        subst Ps.
        eapply ctx_refl.
      }
      rewrite openup5_shrink.
      rewrite openup4_totop1.
      rewrite openup4_shrink.
      rewrite openup3_totop1.
      rewrite openup3_shrink.
      subst Ps.
      totopn 2.
      eapply ctx_refl.
    }
    rewrite openup5_shrink.
    rewrite openup4_shrink.
    rewrite openup3_and.
    eapply destruct_and.
    totopn 9.
    rewrite openup4_totop2.
    rewrite openup4_shrink.
    rewrite openup3_totop2.
    rewrite openup3_shrink.
    eapply dup_premise.
    repeat rewrite lift_openup2.
    eapply openup2_apply_in.
    {
      intros.
      eapply relEC_elim_latern.
    }
    combine_lift.
    eapply openup2_forall1_elim with (x := V0).
    eapply openup3_forall1_elim with (x := V2).
    eapply openup4_forall1_elim with (x := V1).
    rewrite openup5_imply.
    eapply imply_eelim.
    {
      rewrite openup5_and.
      eapply split.
      {
        repeat rewrite openup5_shrink.
        repeat rewrite openup4_shrink.
        totopn 1.
        eapply ctx_refl.
      }
      admit. (* ⌈x1 ~>* x3 /\ !x3 ≤ s₁ /\ wsteps x2 x4⌉ *)
    }
    rewrite openup5_shrink.
    rewrite openup4_totop3.
    rewrite openup4_shrink.
    eapply openup3_apply_in.
    {
      intros.
      eapply latern_mono.
      eapply relE_elim.
    }
    eapply openup3_apply_in.
    {
      intros.
      eapply latern_and_distr.
    }
    rewrite openup3_and.
    eapply destruct_and.
    totopn 1.
    eapply openup3_apply_in.
    {
      intros.
      eapply latern_and_distr.
    }
    rewrite openup3_and.
    eapply destruct_and.
    totopn 1.
    eapply openup3_apply_in.
    {
      intros.
      eapply latern_and_distr.
    }
    rewrite openup3_and.
    eapply destruct_and.
    totopn 1.
    eapply openup3_apply_in.
    {
      intros.
      eapply latern_and_distr.
    }
    rewrite openup3_and.
    eapply destruct_and.
    totopn 1.
    eapply openup3_apply_in.
    {
      intros.
      eapply latern_and_distr.
    }
    rewrite openup3_and.
    eapply destruct_and.
    rewrite openup3_shrink.
    eapply openup2_apply_in.
    {
      intros.
      eapply latern_inj.
    }
    rewrite openup2_shrink.
    set (Ps := [_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_]).
    rewrite lift_openup1.
    eapply openup1_exists1 with (x := V2).
    eapply openup2_apply.
    {
      intros.
      eapply inj_and_intro.
    }
    rewrite openup2_and.
    eapply split.
    {
      subst Ps.
      totopn 10.
      rewrite openup2_totop1.
      eapply ctx_refl.
    }
    rewrite openup2_totop1.
    rewrite openup2_shrink.
    subst Ps.
    eapply ctx_refl.
  }
  (*here*)
  admit.
Qed.

Lemma LRbind'' E (wE : width) (wBE : width) s₁ c₂ s₂ {lctx lctx'} (τ : open_type lctx) (τ' : open_type lctx') ctx (ρ : csubsts lctx ctx) (ρ' : csubsts lctx' ctx) e we c₁ wBe :
  [] |~~ 
     ⌈IsEC E⌉ /\
     (e, we) ∈ relE τ wBe c₁ s₁ ρ /\ 
     relEC E e we (Wapp wE we) (WappB wBE we) s₁ c₂ s₂ τ τ' ρ ρ' ===> 
     (E $$ e, Wapp wE we) ∈ relE τ' (wBe + WappB wBE we) (c₁ + !c₂) s₂ ρ'.
Proof.
  eapply forall1_elim4 with (
    P := fun e we c₁ wBe =>
     ⌈IsEC E⌉ /\
     (e, we) ∈ relE τ wBe c₁ s₁ ρ /\ 
     relEC E e we (Wapp wE we) (WappB wBE we) s₁ c₂ s₂ τ τ' ρ ρ' ===> 
     (E $$ e, Wapp wE we) ∈ relE τ' (wBe + WappB wBE we) (c₁ + !c₂) s₂ ρ'
  ).
  eapply LRbind.
Qed.
