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
  Lemma VLob ctxfo ctx Ps (P : open_rel ctxfo 0 ctx) : openup1 (▹ []) P :: Ps |~ P -> Ps |~ P.
    admit.
  Qed.
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
  Lemma relE_intro lctx ctx e w τ wB c s (ρ : csubsts lctx ctx) :
    [] |~~ 
       ⌈|- e (ρ $ τ) /\ wtyping [] w !(ρ $ τ) ⌉ /\
       ⌈exists B, wsteps wB (Wconst B) /\ forall n e', (~>## e n 0 e') -> n ≤ B⌉%type /\ 
       (∀v w', ⌈e ⇓ v /\ wrunsto w w'⌉%type ===> (v, w') ∈ relV τ ρ /\ ⌈!v ≤ s⌉) /\
       (∀e', ⌈~>*# e 1 e' /\ exists w', wrunsto w w'⌉ ===> ⌈0 < c⌉ /\ ▹ [] ((e', w) ∈ relE τ wB (c - 1) s ρ)) /\
       ⌈exists v, e ⇓ v⌉ /\
       ⌈exists w', wrunsto w w'⌉ ===>
       (e, w) ∈ relE τ wB c s ρ.
    admit.
  Qed.
  Lemma relE_elim lctx ctx e w τ wB c s (ρ : csubsts lctx ctx) :
    [] |~~ 
       (e, w) ∈ relE τ wB c s ρ ===>
       ⌈|- e (ρ $ τ) /\ wtyping [] w !(ρ $ τ) ⌉ /\
       ⌈exists B, wsteps wB (Wconst B) /\ forall n e', (~>## e n 0 e') -> n ≤ B⌉%type /\ 
       (∀v w', ⌈e ⇓ v /\ wrunsto w w'⌉%type ===> (v, w') ∈ relV τ ρ /\ ⌈!v ≤ s⌉) /\
       (∀e', ⌈~>*# e 1 e' /\ exists w', wrunsto w w'⌉ ===> ⌈0 < c⌉ /\ ▹ [] ((e', w) ∈ relE τ wB (c - 1) s ρ)) /\
       ⌈exists v, e ⇓ v⌉ /\
       ⌈exists w', wrunsto w w'⌉.
    admit.
  Qed.
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
    eapply totop with (n := 3); [ reflexivity | unfold removen ].
    rewrite openup4_totop2.
    rewrite openup4_shrink.
    rewrite openup3_totop2.
    rewrite openup3_shrink.
    eapply openup2_forall1_elim with (x := V1).
    eapply openup3_forall1_elim with (x := V0).
    rewrite openup4_imply.
    eapply imply_eelim.
    {
      set (Ps := [_;_;_;_;_;_;_;_]).
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
        eapply totop with (n := 1); [ reflexivity | unfold removen ].
        erewrite lift_openup2.
        eapply ctx_refl.
      }
      rewrite openup4_shrink.
      rewrite openup3_totop1.
      rewrite openup3_shrink.
      subst Ps.
      eapply ctx_refl.
    }
    rewrite openup4_shrink.
    rewrite openup3_shrink.
    rewrite openup2_and.
    eapply destruct_and.
    eapply totop with (n := 7); [ reflexivity | unfold removen ].
    rewrite openup4_totop2.
    rewrite openup4_shrink.
    rewrite openup3_totop2.
    rewrite openup3_shrink.
    eapply dup_premise.
    unfold relEC at 1.
    eapply openup2_forall1_elim with (x := V1).
    eapply openup3_forall1_elim with (x := V0).
    rewrite openup4_imply.
    eapply imply_eelim.
    {
      rewrite openup4_and.
      eapply split.
      {
        repeat rewrite openup4_shrink.
        repeat rewrite openup3_shrink.
        eapply totop with (n := 1); [ reflexivity | unfold removen ].
        eapply ctx_refl.
      }
      admit. (* ⌈x1 ~>* x3 /\ !x3 ≤ s₁ /\ wsteps x2 x4⌉ *)
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
    eapply totop with (n := 9); [ reflexivity | unfold removen ].
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
    set (Ps := [_;_;_;_;_;_;_;_;_;_;_;_;_]).
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
    set (Ps := [_;_;_;_;_;_;_;_;_;_;_;_;_;_;_]).
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
            Lemma Wadd_wsteps w1 w2 n1 n2 : 
              wsteps w1 (Wconst n1) /\ wsteps w2 (Wconst n2) ->
              wsteps (w1 + w2) (Wconst (n1 + n2)).
              admit.
            Qed.
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
    Lemma plug_steps_0 E e n1 n2 : 
      (forall n e', ~>## e n 0 e' -> n <= n1) /\
      (exists v, e ⇓ v /\ forall n e', ~>## (E $ v) n 0 e' -> n <= n2)%type ->
      forall n e', ~>## (E $ e) n 0 e' -> n <= n1 + n2.
      admit.
    Qed.
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
    eapply openup2_exists1 with (x := V3).
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
    Lemma plug_runsto_elim E e v :
      E $$ e ⇓ v ->
      (exists v', e ⇓ v' /\ E $$ v' ⇓ v)%type.
      admit.
    Qed.
    eapply openup2_apply_in.
    {
      intros.
      eapply imply_trans; last first.
      {
        eapply inj_imply.
        {
          eapply plug_runsto_elim.
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
    Lemma app_wrunsto_elim (w1 w2 w : width) :
      wrunsto (Wapp w1 w2) w ->
      (exists w', wrunsto w2 w' /\ wrunsto (Wapp w1 w') w)%type.
      admit.
    Qed.
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
          {
            intros H.
            unfold runsto in H.
            destruct H as [H1 H2].
            exact H1.
          }
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
    Lemma plug_steps_1_elim E e e' :
      ~>*# (E $ e) 1 e' ->
      ((exists v, ⇓*# e 0 v /\ ~>*# (E $ v) 1 e') \/
       (exists e'', ~>*# e 1 e'' /\ ~>*# (E $ e'') 0 e'))%type.
      admit.
    Qed.
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
          eapply openup2_apply_in.
          {
            intros.
            eapply inj_imply.
            {
              Lemma runstoEx_runsto e m v : ⇓*# e m v -> e ⇓ v.
                admit.
              Qed.
              eapply runstoEx_runsto.
            }
          }
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
            {
              intros H.
              eapply runstoEx_runsto in H.
              unfold runsto in H.
              destruct H as [H1 H2].
              exact H1.
            }
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
          Lemma lt_plus_trans_r : forall n m p : nat, n < p -> n < m + p.
            intros; omega.
          Qed.
          eapply lt_plus_trans_r.
        }
        rewrite openup1_shrink.
        subst Ps.
        eapply ctx_refl.
      }
      Definition wle : width_nat -> width_nat -> Prop.
        admit.
      Qed.
      Global Instance Le_width_nat : Le width_nat width_nat :=
        {
          le := wle
        }.
      Lemma relE_mono_wB_c lctx τ c c' s ctx (ρ : csubsts lctx ctx) e w wB wB' : 
        [] |~~ (e, w) ∈ relE τ wB c s ρ /\ [| c <= c' /\ wB <= wB' |] ===> (e, w) ∈ relE τ wB' c' s ρ.
        admit.
      Qed.
      Lemma VMono ctxfo ctx Ps (P : open_rel ctxfo 0 ctx) : Ps |~ P -> Ps |~ (|> [] P)%OR.
        admit.
      Qed.
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
        Lemma relE_mono_wB_c_VC c₁ (c₂ : cexpr) (w w' : width_nat) : !c₂ - 1 ≤ c₁ + !c₂ - 1 /\ w ≤ w' + w.
          admit.
        Qed.
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
    Lemma relEC_red E e' we wEe wBEe s₁ c₂ s₂ lctx lctx' (τ : open_type lctx) (τ' : open_type lctx') ctx (ρ : csubsts lctx ctx) ρ' : 
      [] |~~ (∃e, [|e ~>* e'|] /\ relEC E e we wEe wBEe s₁ c₂ s₂ τ τ' ρ ρ') ===> relEC E e' we wEe wBEe s₁ c₂ s₂ τ τ' ρ ρ'.
      admit.
    Qed.
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
          Lemma stepsex_steps e m e' : ~>*# e m e' -> e ~>* e'.
            admit.
          Qed.
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
    rewrite fold_ORlater.
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
    Lemma relE_red e' w lctx (τ : open_type lctx) wB c s ctx (ρ : csubsts lctx ctx) :
      [] |~~ (∃e, [|~>*# e 0 e'|] /\ (e, w) ∈ relE τ wB c s ρ) ===> (e', w) ∈ relE τ wB c s ρ.
      admit.
    Qed.
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
    Lemma relE_c_eq e w lctx (τ : open_type lctx) wB c c' s ctx (ρ : csubsts lctx ctx) :
      [] |~~ (e, w) ∈ relE τ wB c s ρ /\ [|c = c'|] ===> (e, w) ∈ relE τ wB c' s ρ.
      admit.
    Qed.
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
      Lemma swap_minus_plus (n m : nat) : 0 < n -> n - 1 + m = n + m - 1.
        admit.
      Qed.
      eapply swap_minus_plus.
    }
    subst Ps.
    eapply totop with (n := 6); [ reflexivity | unfold removen ].
    eapply ctx_refl.
  }
  rewrite openup4_and.
  eapply split.
  {
    Lemma split_exists A B P Q :
      ((exists a, P a) /\ (exists b, Q b) ->
      exists (a : A) (b : B), P a /\ Q b)%type.
    Proof.
      intros H.
      destruct H as [[a Ha] [b Hb]].
      exists a b.
      eauto.
    Qed.
    rewrite openup4_totop1.
    rewrite openup4_shrink.
    rewrite openup3_totop1.
    rewrite openup3_shrink.
    rewrite openup2_totop1.
    rewrite openup2_shrink.
    Lemma plug_runsto E e :
      (exists v, e ⇓ v /\ exists v', E $$ v ⇓ v')%type ->
      (exists v, E $$ e ⇓ v).
      admit.
    Qed.
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
    eapply totop with (n := 3); [ reflexivity | unfold removen ].
    rewrite openup4_totop2.
    rewrite openup4_shrink.
    rewrite openup3_totop2.
    rewrite openup3_shrink.
    eapply openup2_forall1_elim with (x := V1).
    eapply openup3_forall1_elim with (x := V0).
    rewrite openup4_imply.
    eapply imply_eelim.
    {
      set (Ps := [_;_;_;_;_;_;_;_]).
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
        eapply totop with (n := 1); [ reflexivity | unfold removen ].
        erewrite lift_openup2.
        eapply ctx_refl.
      }
      rewrite openup4_shrink.
      rewrite openup3_totop1.
      rewrite openup3_shrink.
      subst Ps.
      eapply ctx_refl.
    }
    rewrite openup4_shrink.
    rewrite openup3_shrink.
    rewrite openup2_and.
    eapply destruct_and.
    eapply totop with (n := 7); [ reflexivity | unfold removen ].
    rewrite openup4_totop2.
    rewrite openup4_shrink.
    rewrite openup3_totop2.
    rewrite openup3_shrink.
    eapply dup_premise.
    unfold relEC at 1.
    eapply openup2_forall1_elim with (x := V1).
    eapply openup3_forall1_elim with (x := V0).
    rewrite openup4_imply.
    eapply imply_eelim.
    {
      rewrite openup4_and.
      eapply split.
      {
        repeat rewrite openup4_shrink.
        repeat rewrite openup3_shrink.
        eapply totop with (n := 1); [ reflexivity | unfold removen ].
        eapply ctx_refl.
      }
      admit. (* ⌈x1 ~>* x3 /\ !x3 ≤ s₁ /\ wsteps x2 x4⌉ *)
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
    eapply totop with (n := 1); [ reflexivity | unfold removen ].
    rewrite openup2_and.
    eapply destruct_and.
    set (Ps := [_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_]).
    rewrite lift_openup1.
    eapply openup1_exists1 with (x := V1).
    eapply openup2_apply.
    {
      intros.
      eapply inj_and_intro.
    }
    rewrite openup2_and.
    eapply split.
    {
      subst Ps.
      eapply totop with (n := 10); [ reflexivity | unfold removen ].
      erewrite lift_openup2.
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
