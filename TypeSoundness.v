(* Type soundness *)

Require Import List.
Require Import Program.
Require Import Util.
Require Import Typing EvalCBV.
Require Import TypeSoundness1.
Require Import ssreflect.
Require Import LemmaBind.

Import ListNotations.
Local Open Scope list_scope.

Set Implicit Arguments.

Lemma LRbind'' E (wE : width) (wBE : width) s₁ c₂ s₂ {lctx lctx'} (τ : open_type lctx) (τ' : open_type lctx') ctx (ρ : csubsts lctx ctx) (ρ' : csubsts lctx' ctx) e we c₁ wBe :
  [] |~~ 
     ⌈IsEC E⌉ /\
     (e, we) ∈ relE τ wBe c₁ s₁ ρ /\ 
     relEC E e we (Wapp wE we) (WappB wBE we) s₁ c₂ s₂ τ τ' ρ ρ' ===> 
     (E $$ e, Wapp wE we) ∈ relE τ' (wBe + WappB wBE we) (c₁ + c₂) s₂ ρ'.
Proof.
  eapply forall1_elim4 with (
    P := fun e we c₁ wBe =>
     ⌈IsEC E⌉ /\
     (e, we) ∈ relE τ wBe c₁ s₁ ρ /\ 
     relEC E e we (Wapp wE we) (WappB wBE we) s₁ c₂ s₂ τ τ' ρ ρ' ===> 
     (E $$ e, Wapp wE we) ∈ relE τ' (wBe + WappB wBE we) (c₁ + c₂) s₂ ρ'
  ).
  eapply LRbind.
Qed.

Lemma LRbind''' E s₁ c₂ s₂ {lctx lctx'} (τ : open_type lctx) (τ' : open_type lctx') ctx (ρ : csubsts lctx ctx) (ρ' : csubsts lctx' ctx) e c₁ wBe wEe wBEe :
  [] |~~ 
     (∃we, 
        ⌈IsEC E⌉ /\
        (e, we) ∈ relE τ wBe c₁ s₁ ρ /\ 
        relEC E e we wEe wBEe s₁ c₂ s₂ τ τ' ρ ρ' /\
        (∃wE wBE,
          [| wsteps wEe (Wapp wE we) |] /\
          [| wsteps wBEe (WappB wBE we) |])) ===> 
     (E $$ e, wEe) ∈ relE τ' (wBe + wBEe) (c₁ + c₂) s₂ ρ'.
Proof.
  eapply imply_intro.
  eapply exists1_elim'.
  rewrite openup1_and.
  eapply destruct_and.
  rewrite openup1_shrink.
  totopn 1.
  rewrite openup1_and.
  eapply destruct_and.
  totopn 1.
  rewrite openup1_and.
  eapply destruct_and.
  totopn 1.
  eapply openup1_exists1_elim.
  eapply openup2_exists1_elim.
  rewrite openup3_and.
  eapply destruct_and.
  rewrite openup3_totop2.
  rewrite openup3_shrink.
  totopn 1.
  rewrite openup3_totop1.
  rewrite openup3_shrink.
  repeat rewrite liftPs_cons.
  unfold liftPs, liftPs1, map.
  combine_lift.
  rewrite lift_openup1.
  rewrite lift_openup1.
  set (Ps := [_;_;_;_;_]).
  rewrite lift_openup0_empty.
  eapply openup0_apply.
  {
    eapply relE_replace_w.
  }
  eapply openup0_exists1 with (x := openup2 Wapp V1 V2).
  rewrite openup1_and.
  eapply split.
  {
    eapply openup1_apply.
    {
      intros.
      eapply relE_replace_wB.
    }
    eapply openup1_exists1 with (x := openup2 (fun wBE we => wBe + WappB wBE we) V0 V2).
    rewrite openup2_and.
    eapply split.
    {
      rewrite openup2_comp_openup2.
      rewrite openup3_totop2.
      rewrite openup3_comp_openup2.
      rewrite openup4_totop1.
      rewrite openup4_totop3.
      rewrite openup4_dedup.
      eapply openup3_apply.
      {
        intros.
        eapply LRbind'' with (s₁ := s₁) (τ := τ) (ρ := ρ).
      }
      rewrite openup3_and.
      eapply split.
      {
        rewrite openup3_shrink.
        rewrite openup2_shrink.
        rewrite openup1_shrink.
        subst Ps.
        totopn 4.
        rewrite lift_openup0_empty.
        eapply ctx_refl.
      }
      rewrite openup3_and.
      eapply split.
      {
        rewrite openup3_totop1.
        rewrite openup3_shrink.
        rewrite openup2_totop1.
        rewrite openup2_shrink.
        subst Ps.
        totopn 3.
        eapply ctx_refl.
      }
      eapply openup3_apply.
      {
        intros.
        eapply relEC_replace_wEe_wBEe.
      }
      eapply openup3_exists1 with (x := openup0 wEe).
      rewrite openup4_comp_openup0.
      eapply openup3_exists1 with (x := openup0 wBEe).
      rewrite openup4_comp_openup0.
      rewrite openup3_and.
      eapply split.
      {
        rewrite openup3_totop1.
        rewrite openup3_shrink.
        rewrite openup2_totop1.
        rewrite openup2_shrink.
        subst Ps.
        totopn 2.
        eapply ctx_refl.
      }
      rewrite openup3_and.
      eapply split.
      {
        rewrite openup3_totop2.
        rewrite openup3_shrink.
        subst Ps.
        totopn 1.
        eapply ctx_refl.
      }
      rewrite openup3_totop1.
      rewrite openup3_shrink.
      subst Ps.
      eapply ctx_refl.
    }
    rewrite openup2_totop1.
    rewrite openup2_shrink.
    rewrite openup1_comp_openup2.
    eapply openup2_apply.
    {
      intros.
      eapply inj_imply.
      eapply wsteps_Wadd_b.
    }
    subst Ps.
    rewrite openup2_totop1.
    eapply ctx_refl.
  }
  rewrite openup1_comp_openup2.
  subst Ps.
  totopn 1.
  rewrite openup2_totop1.
  eapply ctx_refl.
Qed.

(*
    Inductive typingEC : econtext -> type -> type -> Prop :=
    | TECempty τ : typingEC ECempty τ τ
    | TECapp1 f arg τ τ₁ c s τ₂ :
        typingEC f τ (Tarrow τ₁ c s τ₂) ->
        (|- arg τ₁) ->
        typingEC (ECapp1 f arg) τ τ₂
    .
 *)

Definition related {lctx} Γ wB w (e : open_expr lctx) τ (c : open_cexpr lctx) (s : open_size lctx) :=
  make_Ps (lctx := lctx) Γ |~ let ρ := make_ρ lctx in openup1 (fun ρ => (ρ $$ e, ρ $$ w) ∈ relE τ (ρ $ wB) !(ρ $ c) (ρ $ s) ρ) ρ.

(* Definition related {lctx} Γ wB w (e : open_expr lctx) τ (c : open_cexpr lctx) (s : open_size lctx) := *)
(*   make_Ps (lctx := lctx) Γ |~ openup1 (fun ρ => (ρ $$ e, ρ $$ w) ∈ relE τ (ρ $ wB) !(ρ $ c) (ρ $ s) ρ)%rel (make_ρ lctx). *)

(*
Definition related {lctx} Γ wB w (e : open_expr lctx) τ (c : open_cexpr lctx) (s : open_size lctx) :=
  make_Ps (lctx := lctx) Γ |~ let ρ := make_ρ lctx in (ρ $$ e, ρ $$ w) ∈ openup1 (fun ρ => relE τ (ρ $ wB) !(ρ $ c) (ρ $ s) ρ) ρ.
*)

Notation "⊩" := related.

Lemma foundamental :
  forall ctx (Γ : tcontext ctx) e τ c s,
    ⊢ Γ e τ c s -> 
    exists wB w, ⊩ Γ wB w e τ c s.
Proof.
  induction 1.
  Focus 2.
  {
    (* case app *)
    unfold related in *.

    destruct IHtyping1 as [wB₀ [w₀ IH₀]].
    destruct IHtyping2 as [wB₁ [w₁ IH₁]].

    exists (wB₀ + (wB₁ + (Wconst 1 + WappB w₀ w₁))).
    exists (Wapp w₀ w₁).

    rename ctx into lctx.
    set (ρ := make_ρ lctx) in *.
    set (ctx := make_ctx lctx) in *.
    set (Ps := make_Ps Γ) in *.

    eapply openup1_apply.
    {
      intros.
      Lemma csubsts_Wadd lctx ctx (ρ : csubsts lctx ctx) (w1 w2 : open_width WTnat lctx) : ρ $$ (w1 + w2) = ρ $$ w1 + ρ $$ w2.
        admit.
      Qed.
      rewrite csubsts_Wadd.
      Lemma csubsts_Eapp lctx ctx (ρ : csubsts lctx ctx) (e1 e2 : open_expr lctx) : ρ $$ (Eapp e1 e2) = Eapp (ρ $$ e1) (ρ $$ e2).
        admit.
      Qed.
      rewrite csubsts_Eapp.
      rewrite <- plug_ECapp1.
      rewrite csubsts_Fadd.
      rewrite coerce_Fadd.
      eapply LRbind'''.
    }
    eapply openup1_exists1 with (x := ρ $ w₀).
    Lemma openup2_comp_openup1 t1 t2 t3 (f : t1 -> t2 -> t3) A1 (g : A1 -> t1) ctxfo x2 y1 : openup2 (ctx := ctxfo) (fun x1 x2 => f x1 x2) (openup1 (fun y1 => g y1) y1) x2 = openup2 (fun y1 x2 => f (g y1) x2) y1 x2.
      admit.
    Qed.
    rewrite openup2_comp_openup1.
    rewrite openup2_dedup.
    rewrite openup1_and.
    eapply split.
    {
      admit. (* IsEC *)
    }
    rewrite openup1_and.
    eapply split.
    {
      eapply IH₀.
    }
    rewrite openup1_and.
    eapply split.
    {
      unfold relEC.
      eapply openup1_forall1.
      eapply openup2_forall1.
      rewrite openup3_imply.
      eapply ORimply_intro.
      eapply openup3_apply.
      {
        intros.
        rewrite csubsts_Wadd.
        unfold apply at 1.
        simpl.
        unfold plug.
        Lemma plug_ECapp2 (e1 e2 : expr) : (ECapp2 e1 ECempty) $$ e2 = Eapp e1 e2.
          admit.
        Qed.
        rewrite <- plug_ECapp2.
        rewrite csubsts_Fadd.
        rewrite coerce_Fadd.
        eapply LRbind''' with (ρ := x1) (s₁ := x1 $ s₁).
      }
      combine_lift.
      set (ρ' := lift ρ) in *.
      eapply openup3_exists1 with (x := ρ' $ w₁).
      rewrite openup4_comp_openup1.
      rewrite openup4_dedup.
      rewrite openup3_and.
      eapply destruct_and.
      rewrite openup3_and.
      eapply split.
      {
        admit. (* IsEC *)
      }
      rewrite openup3_and.
      eapply split.
      {
        instantiate (1 := τ₁).
        subst Ps.
        set (Ps := _ :: _ :: _).
        rewrite openup3_totop1.
        rewrite openup3_shrink.
        rewrite openup2_totop1.
        rewrite openup2_shrink.
        subst Ps.
        Lemma clear ctxfo ctx (P Q : open_rel ctxfo 0 ctx) Ps :
          Ps |~ Q ->
          P :: Ps |~ Q.
          admit.
        Qed.
        eapply clear.
        eapply clear.
        subst ρ'.
        unfold liftPs.
        rewrite -lift_openup1.
        unfold lift.
        Lemma remove_lift ctxfo ctx t (P : open_rel ctxfo 0 ctx) Ps :
          Ps |~ P ->
          liftPs1 t Ps |~ lift1 P.
          admit.
        Qed.
        eapply remove_lift.
        rewrite -lift_openup1.
        unfold lift.
        eapply remove_lift.
        eapply IH₁.
      }
      rewrite openup3_and.
      eapply split.
      {
        unfold relEC.
        subst Ps.
        set (Ps := _ :: _ :: _).
        rewrite openup3_totop2.
        rewrite openup3_shrink.
        eapply openup2_forall1.
        eapply openup3_forall1.
        rewrite openup4_imply.
        eapply ORimply_intro.
        rewrite openup4_totop1.
        rewrite openup4_shrink.
        rewrite openup3_and.
        eapply destruct_and.
        subst Ps.
        repeat rewrite liftPs_cons.
        combine_lift.
        repeat rewrite lift_openup3.
        subst ρ'.
        combine_lift.
        set (ρ' := lift ρ) in *.
        eapply openup4_apply.
        {
          intros.
          rewrite plug_ECapp2.
          rewrite csubsts_Wadd.
          Lemma csubsts_Wapp lctx ctx (ρ : csubsts lctx ctx) (w1 w2 : open_width WTstruct lctx) : ρ $$ (Wapp w1 w2) = Wapp (ρ $ w1) (ρ $ w2).
            admit.
          Qed.
          Lemma csubsts_WappB lctx ctx (ρ : csubsts lctx ctx) (w1 w2 : open_width WTstruct lctx) : ρ $$ (WappB w1 w2) = WappB (ρ $ w1) (ρ $ w2).
            admit.
          Qed.
          rewrite csubsts_Wapp.
          rewrite csubsts_WappB.
          rewrite csubsts_Wconst.
          eapply imply_refl.
        }
        totopn 2.
        set (tmp := relV (Tarrow τ₁ c s τ₂)) at 1.
        simpl in tmp.
        subst tmp.
        eapply openup3_apply_in.
        {
          intros.
          eapply imply_trans; first last.
          {
            eapply beta.
          }
          eapply imply_refl.
        }

        rewrite openup3_and.
        eapply destruct_and.
        totopn 1.
        eapply openup3_exists1_elim.
        repeat rewrite liftPs_cons.
        repeat rewrite lift_openup3.
        rewrite openup4_and.
        eapply destruct_and.
        totopn 1.
        rewrite openup4_totop1.
        rewrite openup4_shrink.
        eapply openup3_exists1_elim.
        repeat rewrite liftPs_cons.
        repeat rewrite lift_openup3.
        eapply openup4_exists1_elim.
        repeat rewrite liftPs_cons.
        repeat rewrite lift_openup3.
        rewrite openup5_and.
        eapply destruct_and.
        totopn 1.
        rewrite openup5_totop1.
        rewrite openup5_shrink.
        rewrite openup4_totop1.

        Lemma openup4_forall1_elim' t1 t2 t3 t4 ctx (f : t1 -> t2 -> t3 -> t4 -> wexpr -> rel 0 ctx) ctxfo x1 x2 x3 x4 e w Ps Q :
          openup6 (ctx := ctxfo) (fun x1 x2 x3 x4 w e => f x1 x2 x3 x4 (e, w)) x1 x2 x3 x4 w e :: Ps |~ Q ->
          openup4 (fun x1 x2 x3 x4 => ∀x, f x1 x2 x3 x4 x) x1 x2 x3 x4 :: Ps |~ Q.
        Proof.
          intros H.
          eapply openup4_forall1_elim with (x := openup2 pair e w).
          rewrite openup5_totop4.
          rewrite openup5_comp_openup2.
          rewrite openup6_totop1.
          do 4 rewrite openup6_totop5.
          eauto.
        Qed.
        combine_lift.
        repeat rewrite lift_openup4.
        combine_lift.
        eapply openup4_forall1_elim' with (e := V4) (w := V3).
        rewrite openup6_imply.
        rewrite openup6_shrink.
        rewrite openup5_totop1.
        rewrite openup5_shrink.
        rewrite openup4_totop1.
        rewrite openup4_shrink.
        totopn 4.
        rewrite openup3_totop1.
        rewrite openup3_totop2.
        rewrite openup3_totop2.
        totopn 1.
        eapply imply_elim.
        subst ρ'.
        set (ρ' := lift ρ) in *.
        set (Ps := _::_::_::_::_::_) at 1.
        rewrite openup4_totop3.
        rewrite openup4_shrink.
        eapply openup3_apply.
        {
          intros.
          rewrite csubsts_subst_s_c.
          rewrite csubsts_subst_s_s.
          eapply relE_mono_tau_c_s with (v := x3).
        }
        rewrite openup3_and.
        eapply split.
        {
          eapply openup3_apply.
          {
            intros.
            eapply imply_trans.
            { eapply relE_rho. }
            eapply relE_app_subst. 
          }
          eapply openup3_exists1 with (x := V2).
          eapply openup4_exists1 with (x := V0).
          eapply openup5_exists1 with (x := V1).
          rewrite openup6_and.
          eapply split.
          {
            eapply openup6_apply.
            {
              intros.
              eapply relE_replace_width.
            }
            eapply openup6_exists1 with (x := V3).
            rewrite openup7_and.
            eapply split.
            {
              rewrite openup7_totop5.
              rewrite openup7_shrink.
              rewrite openup6_totop2.
              rewrite openup6_totop2.
              rewrite openup6_totop4.
              rewrite openup6_totop4.
              eapply openup6_apply_in.
              {
                intros.
                rewrite csubsts_subst_s_c.
                rewrite csubsts_subst_s_s.
                repeat rewrite csubsts_value.
                eapply imply_refl.
              }
              eapply ctx_refl.
            }
            admit. (* wsteps *)
          }
          admit. (* = Eabs /\ = Wabs *)
        }
        admit. (* !v <= rho $ s1 *)
      }
      admit. (* exists wBE *)
    }
    admit. (* exists wBE *)
  }
  Unfocus.
  Focus 7.
  {
    (* case unfold *)
    unfold related in *.
    destruct IHtyping as [wB [w IH]].
    exists (wB + Wconst 1).
    exists (Wunfold w).
    rename ctx into lctx.
    set (ρ := make_ρ lctx) in *.
    set (ctx := make_ctx lctx) in *.
    set (Ps := make_Ps Γ) in *.
    eapply openup1_apply.
    {
      intros.
      rewrite csubsts_Wadd.
      Lemma csubsts_Eunfold lctx ctx (ρ : csubsts lctx ctx) (e : open_expr lctx) : ρ $$ (Eunfold e) = Eunfold (ρ $$ e).
        admit.
      Qed.
      rewrite csubsts_Eunfold.
      Lemma plug_ECunfold (e : expr) : (ECunfold ECempty) $$ e = Eunfold e.
        admit.
      Qed.
      rewrite <- plug_ECunfold.
      rewrite csubsts_Fadd.
      rewrite coerce_Fadd.
      eapply LRbind'''.
    }
    eapply openup1_exists1 with (x := ρ $ w).
    rewrite openup2_comp_openup1.
    rewrite openup2_dedup.
    rewrite openup1_and.
    eapply split.
    {
      admit. (* IsEC *)
    }
    rewrite openup1_and.
    eapply split.
    {
      eapply IH.
    }
    rewrite openup1_and.
    eapply split.
    {
      unfold relEC.
      eapply openup1_forall1.
      eapply openup2_forall1.
      rewrite openup3_imply.
      eapply ORimply_intro.
      rewrite openup3_and.
      eapply destruct_and.
      eapply openup3_apply_in.
      {
        intros.
        eapply relV_type_equal; eauto.
      }
      set (tmp := relV _) at 1.
      simpl in tmp.
      subst tmp.
      eapply openup3_apply_in.
      {
        intros.
        eapply iota.
      }
      eapply openup3_apply_in.
      {
        intros.
        set (v := @@, _) at 1.
        rewrite substr_abs.
        eapply imply_trans; first last.
        {
          eapply beta.
        }
        rewrite substr_and.
        rewrite substr_inj.
        rewrite substr_exists1.
        subst v.
        eapply imply_refl.
      }
      rewrite openup3_and.
      eapply destruct_and.
      totopn 1.
      eapply openup3_exists1_elim.
      repeat rewrite liftPs_cons.
      eapply openup4_apply_in.
      {
        intros.
        rewrite substr_exists1.
        eapply imply_refl.
      }
      eapply openup4_exists1_elim.
      repeat rewrite liftPs_cons.
      eapply openup5_apply_in.
      {
        intros.
        set (v := @@, _) at 1.
        rewrite substr_and.
        rewrite substr_later.
        rewrite substr_app.
        rewrite substr_relV.
        rewrite substr_add_pair.
        rewrite substr_var0.
        rewrite substr_csubsts_shift.
        rewrite substr_inj.
        subst v.
        eapply imply_refl.
      }
      rewrite openup5_and.
      eapply destruct_and.
      rewrite openup5_shrink.
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
        eapply inj_exists_elim.
      }
      eapply openup2_exists1_elim.
      repeat rewrite liftPs_cons.
      combine_lift.
      totopn 2.
      repeat rewrite lift_openup5.
      repeat rewrite lift_openup4.
      repeat rewrite lift_openup3.
      rewrite openup5_totop1.
      rewrite openup5_shrink.
      rewrite openup4_totop1.
      rewrite openup4_shrink.
      combine_lift.
      set (ρ' := lift ρ) in *.
      combine_lift.
      subst Ps.
      set (Ps := _::_::_::_::_::_) at 1.
      rewrite openup3_totop2.
      rewrite openup3_shrink.
      eapply openup2_apply.
      {
        intros.
        unfold plug.
        rewrite csubsts_Wconst.
        rewrite csubsts_F1.
        rewrite csubsts_Wunfold.
        rewrite coerce_F1.
        eapply imply_refl.
      }
      eapply openup2_apply.
      {
        intros.
        eapply relE_e_eq.
      }
      eapply openup2_exists1 with (x := openup2 (fun t v => Eunfold (Efold t v)) V0 V2).
      rewrite openup3_comp_openup2.
      rewrite openup4_and.
      eapply split.
      {
        eapply openup4_apply.
        {
          intros.
          eapply inj_imply.
          intros Hmy.
          rewrite plug_ECunfold.
          f_equal.
          exact Hmy.
        }
        rewrite openup4_totop2.
        rewrite openup4_shrink.
        rewrite openup3_totop1.
        rewrite openup3_totop2.
        subst Ps.
        totopn 1.
        eapply ctx_refl.
      }
      rewrite openup4_totop3.
      rewrite openup4_shrink.
      eapply assert with (P := openup2 (fun v w => [|IsValue v /\ IsWValue w|]) V2 V1).
      {
        eapply openup2_apply.
        {
          intros.
          eapply later_inj.
        }
        rewrite openup2_later.
        subst Ps.
        rewrite openup3_later.
        eapply later_mono_ctx'.
        eapply openup3_apply_in.
        {
          intros.
          eapply relV_value.
        }
        rewrite openup3_shrink.
        eapply ctx_refl.
      }
      eapply openup2_apply_in.
      {
        intros.
        eapply inj_and_elim.
      }
      rewrite openup2_and.
      eapply destruct_and.
      rewrite openup2_totop1.
      repeat rewrite openup2_shrink.
      subst Ps.
      set (Ps := _::_::_::_::_::_::_::_).
      eapply openup3_apply.
      {
        intros.
        eapply relE_intro.
      }
      rewrite openup3_and.
      eapply split.
      {
        admit. (* typing *)
      }
      rewrite openup3_and.
      eapply split.
      {
        rewrite openup3_totop2.
        rewrite openup3_shrink.
        eapply openup2_apply.
        {
          intros.
          eapply inj_imply.
          intros Hevar.
          exists 1.
          split.
          { eapply wsteps_refl. }
          intros n e' Heval.
          eapply unfold_fold_v_0_elim in Heval.
          {
            subst.
            simpl; omega.
          }
          exact Hevar.
        }
        rewrite openup2_shrink.
        subst Ps.
        eapply ctx_refl.
      }
      rewrite openup3_and.
      eapply split.
      {
        eapply openup3_forall1.
        eapply openup4_forall1.
        rewrite openup5_imply.
        rewrite openup5_shrink.
        rewrite openup4_shrink.
        eapply ORimply_intro.
        eapply openup5_apply_in.
        {
          intros.
          eapply inj_and_elim.
        }
        rewrite openup5_and.
        eapply destruct_and.
        rewrite openup5_totop2.
        rewrite openup5_shrink.
        rewrite openup4_totop3.
        rewrite openup4_shrink.
        eapply openup3_apply_in.
        {
          intros.
          eapply inj_imply.
          Lemma unfold_fold_runsto_0_elim t e v :
            ⇓*# (Eunfold (Efold t e)) 0 v -> False.
            admit.
          Qed.
          eapply unfold_fold_runsto_0_elim.
        }
        rewrite openup3_shrink.
        rewrite openup2_shrink.
        rewrite openup1_shrink.
        Lemma inj_false_elim ctx (P : rel 0 ctx) :
          [] |~~ [| False |] ===> P.
          admit.
        Qed.
        eapply openup3_apply.
        {
          intros.
          eapply inj_false_elim.
        }
        rewrite openup3_shrink.
        rewrite openup2_shrink.
        rewrite openup1_shrink.
        eapply ctx_refl.
      }
      eapply assert with (P := openup2 (fun ρ w' => [|wsteps (Wunfold (ρ $ w)) w'|]) ρ' V1).
      {
        subst Ps.
        totopn 6.
        eapply openup3_apply_in.
        {
          intros.
          eapply inj_and_elim.
        }
        rewrite openup3_and.
        eapply destruct_and.
        totopn 1.
        eapply openup3_apply_in.
        {
          intros.
          eapply inj_and_elim.
        }
        rewrite openup3_and.
        eapply destruct_and.
        totopn 1.
        rewrite openup3_totop1.
        rewrite openup3_shrink.
        eapply openup2_apply.
        {
          intros.
          eapply imply_trans.
          {
            eapply inj_imply.
            Lemma wsteps_trans t (a c : open_width t []) : (exists b, wsteps a b /\ wsteps b c)%type -> wsteps a c.
              admit.
            Qed.
            eapply wsteps_trans.
          }
          eapply inj_exists_intro.
        }
        eapply openup2_exists1 with (x := openup1 Wunfold V3).
        rewrite openup3_comp_openup1.
        eapply openup3_apply.
        {
          intros.
          eapply inj_and_intro.
        }
        set (Ps := _::_::_::_::_::_::_::_) at 1.
        rewrite openup3_and.
        eapply split.
        {
          rewrite openup3_totop2.
          rewrite openup3_shrink.
          eapply openup2_apply.
          {
            intros.
            eapply inj_imply.
            Lemma wsteps_unfold a b : wsteps a b -> wsteps (Wunfold a) (Wunfold b).
              admit.
            Qed.
            eapply wsteps_unfold.
          }
          rewrite openup2_totop1.
          eapply ctx_refl.
        }
        rewrite openup3_totop1.
        rewrite openup3_shrink.
        eapply openup2_apply.
        {
          intros.
          eapply imply_trans.
          {
            eapply inj_imply.
            Lemma wsteps_unfold_fold_intro w w' : w = Wfold w' /\ IsWValue w' -> wsteps (Wunfold w) w'.
              admit.
            Qed.
            eapply wsteps_unfold_fold_intro.
          }
          eapply inj_and_intro.
        }
        rewrite openup2_and.
        rewrite openup2_shrink.
        eapply split.
        {
          do 7 eapply clear.
          rewrite openup4_shrink.
          rewrite openup3_totop1.
          rewrite openup3_shrink.
          eapply ctx_refl.
        }
        do 4 eapply clear.
        eapply ctx_refl.
      }
      subst Ps.
      set (Ps := _::_::_::_::_::_::_::_) at 1.
      rewrite openup3_and.
      eapply split.
      {
        eapply openup3_forall1.
        rewrite openup4_imply.
        eapply ORimply_intro.
        rewrite openup4_shrink.
        rewrite openup3_shrink.
        rewrite openup2_and.
        eapply split.
        {
          rewrite openup2_shrink.
          rewrite openup1_shrink.
          eapply openup0_apply.
          {
            eapply inj_tauto.
            omega.
          }
          eapply inj_true_intro.
        }
        eapply openup4_apply_in.
        {
          intros.
          eapply inj_and_elim.
        }
        rewrite openup4_and.
        eapply destruct_and.
        rewrite openup4_totop2.
        rewrite openup4_shrink.
        combine_lift.
        Lemma unfold_fold_steps_1_value_elim t e e' :
          ~>*# (Eunfold (Efold t e)) 1 e' -> IsValue e -> e' = e.
          admit.
        Qed.
        eapply openup3_apply_in.
        {
          intros.
          eapply inj_imply.
          exact (@unfold_fold_steps_1_value_elim _ _ _).
        }
        rewrite openup3_shrink.
        eapply openup2_apply_in.
        {
          intros.
          Lemma inj_imply_elim (P Q : Prop) ctx :
            [] |~~ ([| P -> Q |] : rel 0 ctx) ===> ([| P |] ===> [| Q |]).
            admit.
          Qed.
          eapply inj_imply_elim.
        }
        Lemma openup2_imply {ctx t1 t2} {f g : t1 -> t2 -> rel 0 ctx} {ctxfo x1 x2} : openup2 (ctx := ctxfo) (fun x1 x2 => f x1 x2 ===> g x1 x2) x1 x2 = (openup2 f x1 x2 ===> openup2 g x1 x2)%OR.
          admit.
        Qed.
        rewrite openup2_imply.
        rewrite openup2_totop1.
        rewrite openup2_shrink.
        subst Ps.
        repeat rewrite liftPs_cons.
        combine_lift.
        rewrite lift_openup1.
        totopn 3.
        totopn 1.
        eapply imply_elim.
        totopn 4.
        rewrite lift_openup3.
        rewrite openup3_later.
        rewrite openup2_later.
        eapply later_mono_ctx'.
        combine_lift.
        eapply openup2_apply.
        {
          intros.
          eapply relE_e_eq.
        }
        eapply openup2_exists1 with (x := V3).
        set (Ps := _::_::_::_::_::_::_::_) at 1.
        rewrite openup3_and.
        eapply split.
        {
          rewrite openup3_totop1.
          rewrite openup3_shrink.
          subst Ps.
          totopn 1.
          eapply ctx_refl.
        }
        rewrite openup3_totop2.
        rewrite openup3_shrink.
        eapply openup2_apply.
        {
          intros.
          eapply relE_replace_w.
        }
        eapply openup2_exists1 with (x := V2).
        rewrite openup3_and.
        eapply split; first last.
        {
          rewrite openup3_totop1.
          rewrite openup3_shrink.
          subst Ps.
          totopn 3.
          rewrite lift_openup2.
          subst ρ'.
          combine_lift.
          rewrite openup2_totop1.
          eapply ctx_refl.
        }
        eapply openup3_apply.
        {
          intros.
          Lemma relE_mono_wB_const lctx τ c s ctx (ρ : csubsts lctx ctx) e w n n' : 
            [] |~~ (e, w) ∈ relE τ (Wconst n) c s ρ /\ [| n <= n' |] ===> (e, w) ∈ relE τ (Wconst n') c s ρ.
            admit.
          Qed.
          eapply relE_mono_wB_const with (n := 0).
        }
        rewrite openup3_and.
        eapply split; first last.
        {
          rewrite openup3_shrink.
          rewrite openup2_shrink.
          rewrite openup1_shrink.
          eapply openup0_apply.
          {
            eapply inj_tauto.
            simpl; omega.
          }
          eapply inj_true_intro.
        }
        eapply openup3_apply.
        {
          intros.
          Lemma relV_relE lctx τ s ctx (ρ : csubsts lctx ctx) e w : 
            [] |~~ [|!e <= s|] /\ (e, w) ∈ relV τ ρ ===> (e, w) ∈ relE τ (Wconst 0) 0 s ρ.
            admit.
          Qed.
          eapply relV_relE.
        }
        rewrite openup3_and.
        eapply split.
        {
          rewrite openup3_shrink.
          erewrite <- openup3_shrink.
          instantiate (1 := V5).
          erewrite <- openup4_shrink.
          instantiate (1 := V1).
          subst Ps.
          repeat rewrite lift_openup3.
          subst ρ'.
          combine_lift.
          totopn 8.
          eapply openup3_apply_in.
          {
            intros.
            eapply inj_and_elim.
          }
          rewrite openup3_and.
          eapply destruct_and.
          totopn 1.
          eapply openup3_apply_in.
          {
            intros.
            eapply inj_and_elim.
          }
          rewrite openup3_and.
          eapply destruct_and.
          rewrite openup3_totop2.
          rewrite openup3_shrink.
          totopn 8.
          eapply openup4_apply.
          {
            intros.
            eapply inj_imply.
            intros.
            Lemma is_fold_sle_elim lctx ctx (ρ : csubsts lctx ctx) t (v v' : expr) (s s' : open_size lctx) :
              is_fold s = Some s' /\
              !v <= ρ $$ s /\
              v = Efold t v' ->
              !v' <= ρ $$ s'.
              admit.
            Qed.
            eapply is_fold_sle_elim with (v := x2) (t := x1).
            split.
            { eapply H0. }
            exact H2.
          }
          eapply openup4_apply.
          {
            intros.
            eapply inj_and_intro.
          }
          set (Ps := _::_::_::_::_::_::_::_) at 1.
          rewrite openup4_and.
          eapply split.
          {
            rewrite openup4_shrink.
            rewrite openup3_totop1.
            rewrite openup3_shrink.
            rewrite openup2_totop1.
            subst Ps.
            totopn 1.
            eapply ctx_refl.
          }
          rewrite openup4_totop3.
          rewrite openup4_shrink.
          rewrite openup3_totop2.
          rewrite openup3_totop2.
          eapply ctx_refl.
        }
        eapply openup3_apply.
        {
          intros.
          eapply relV_type_equal.
          {
            Lemma subst_v_equal lctx v v' (b : open_type (CEtype :: lctx)) :
              equal v v' -> equal (subst v b) (subst v' b).
              admit.
            Qed.
            eapply subst_v_equal; symmetry; eauto.
          }
        }
        eapply openup3_apply.
        {
          intros.
          Lemma relV_rho v w lctx τ' τ ctx (ρ : csubsts lctx ctx) :
            [] |~~ (v, w) ∈ relV τ (add (ρ $$ τ', relV τ' ρ) ρ) ===> (v, w) ∈ relV (subst τ' τ) ρ.
            admit.
          Qed.
          eapply relV_rho.
        }
        rewrite openup3_totop1.
        rewrite openup3_totop2.
        subst Ps.
        eapply ctx_refl.
      }
      rewrite openup3_and.
      eapply split.
      {
        rewrite openup3_totop2.
        rewrite openup3_shrink.
        eapply openup2_apply.
        {
          intros.
          eapply inj_imply.
          Lemma runsto_unfold_fold_intro t v :
            IsValue v -> Eunfold (Efold t v) ⇓ v.
            admit.
          Qed.
          intros Hevar.
          exists x2.
          eapply runsto_unfold_fold_intro.
          exact Hevar.
        }
        rewrite openup2_shrink.
        subst Ps.
        totopn 1.
        eapply ctx_refl.
      }
      rewrite openup3_shrink.
      rewrite openup2_shrink.
      eapply openup1_apply.
      {
        intros.
        eapply inj_exists_intro.
      }
      eapply openup1_exists1 with (x := V1).
      rewrite openup2_totop1.
      unfold wrunsto.
      eapply openup2_apply.
      {
        intros.
        eapply inj_and_intro.
      }
      rewrite openup2_and.
      eapply split.
      { eapply ctx_refl. }
      rewrite openup2_shrink.
      subst Ps.
      totopn 2.
      eapply ctx_refl.
    }
    {
      admit. (* exists wE wBE *)
    }
  }
  Unfocus.
  Focus 2.
  {
    (* case abs *)
    unfold related in *.
    destruct IHtyping as [wB [w IH]].
    rename ctx into lctx.
    set (ρ := make_ρ lctx) in *.
    set (ctx := make_ctx lctx) in *.
    set (Ps := make_Ps T) in *.
    exists (Wconst (ctx := lctx) 0).
    exists (Wabs wB w).
    eapply openup1_apply.
    {
      intros.
      rewrite csubsts_Wconst.
      Lemma csubsts_F0 lctx ctx (ρ : csubsts lctx ctx) :
        ρ $$ F0 = F0 (ctx := []).
        admit.
      Qed.
      rewrite csubsts_F0.
      Lemma coerce_F0 : !F0 = 0.
        admit.
      Qed.
      rewrite coerce_F0.
      Global Instance Apply_csubsts_expr_expr' {ctx} lctx' lctx : Apply (csubsts lctx ctx) (open_expr (lctx' :: lctx)) (open_expr [lctx']).
        admit.
      Defined.
      Lemma csubsts_Eabs lctx ctx (ρ : csubsts lctx ctx) t e :
        ρ $$ Eabs t e = Eabs (ρ $ t) (ρ $ e).
        admit.
      Qed.
      rewrite csubsts_Eabs.
      Lemma csubsts_Wabs lctx ctx (ρ : csubsts lctx ctx) wB w :
        ρ $$ Wabs wB w = Wabs (ρ $ wB) (ρ $ w).
        admit.
      Qed.
      rewrite csubsts_Wabs.
      eapply relV_relE.
    }
    rewrite openup1_and.
    eapply split.
    {
      eapply openup1_apply.
      {
        intros.
        Lemma csubsts_S0 lctx ctx (ρ : csubsts lctx ctx) :
          ρ $$ S0 = S0 (ctx := []).
          admit.
        Qed.
        rewrite csubsts_S0.
        eapply inj_tauto.
        Lemma abs_sle_0 (t : type) e :
          !(Eabs t e) <= S0.
          admit.
        Qed.
        eapply abs_sle_0.
      }
      rewrite openup1_shrink.
      eapply inj_true_intro.
    }
    set (tmp := relV _) at 1.
    simpl in tmp.
    subst tmp.
    eapply openup1_apply.
    {
      intros.
      Lemma beta_inv ew ctx g : 
        [] |~~ g ew ===> ew ∈ Rabs (ctx := ctx) g.
        admit.
      Qed.
      eapply imply_trans.
      { eapply beta_inv. }
      eapply imply_refl.
    }
    rewrite openup1_and.
    eapply split.
    {
      admit. (* typing *)
    }
    eapply openup1_exists1 with (x := openup1 (fun ρ => ρ $ e) ρ).
    rewrite openup2_comp_openup1.
    rewrite openup2_dedup.
    rewrite openup1_and.
    eapply split.
    {
      eapply openup1_apply.
      {
        intros.
        eapply inj_tauto.
        eexists.
        eauto.
      }
      rewrite openup1_shrink.
      eapply inj_true_intro.
    }
    eapply openup1_exists1 with (x := openup1 (fun ρ => ρ $ wB) ρ).
    rewrite openup2_comp_openup1.
    rewrite openup2_dedup.
    eapply openup1_exists1 with (x := openup1 (fun ρ => ρ $ w) ρ).
    rewrite openup2_comp_openup1.
    rewrite openup2_dedup.
    rewrite openup1_and.
    eapply split.
    {
      eapply openup1_apply.
      {
        intros.
        eapply inj_tauto.
        eauto.
      }
      rewrite openup1_shrink.
      eapply inj_true_intro.
    }
    eapply openup1_forall1.
    rewrite openup2_imply.
    eapply ORimply_intro.
    Opaque openup1.
    simpl in IH.
    unfold add_Ps_expr in IH.
    unfold add_ρ_expr in IH.
    unfold add_typing in IH.
    unfold compose in IH.
    simpl in IH.
    Transparent openup1.
    subst ctx ρ Ps.
    set (ctx := make_ctx lctx) in *.
    set (ρ := make_ρ lctx) in *.
    set (Ps := make_Ps T) in *.
    unfold liftPs.
    rewrite openup1_comp_openup2 in IH.
    Lemma openup5_comp_openup1 t1 t2 t3 t4 t5 t6 (f : t1 -> t2 -> t3 -> t4 -> t5 -> t6) A1 (g : A1 -> t1) ctxfo x2 x3 x4 x5 y1 : openup5 (ctx := ctxfo) (fun x1 x2 x3 x4 x5 => f x1 x2 x3 x4 x5) (openup1 (fun y1 => g y1) y1) x2 x3 x4 x5 = openup5 (fun y1 x2 x3 x4 x5 => f (g y1) x2 x3 x4 x5) y1 x2 x3 x4 x5.
      admit.
    Qed.
    Lemma openup5_dedup {t0 t2 t3 t4 t5} {f : t0 -> t0 -> t2 -> t3 -> t4 -> t5} {ctxfo x0 x2 x3 x4} : openup5 (ctx := ctxfo) f x0 x0 x2 x3 x4 = openup4 (fun x => f x x) x0 x2 x3 x4.
      admit.
    Qed.
    eapply openup2_apply in IH; first last.
    {
      intros.
      Lemma add_csubsts_expr ew lctx ctx (ρ : csubsts lctx ctx) (e : open_expr _) :
        (add ew ρ) $$ e = subst (fst ew) (ρ $ e).
        admit.
      Qed.
      rewrite add_csubsts_expr.
      Lemma add_csubsts_width ew lctx ctx (ρ : csubsts lctx ctx) t (w : open_width t _) :
        (add ew ρ) $$ w = subst (snd ew) (ρ $ w).
        admit.
      Qed.
      repeat rewrite add_csubsts_width.
      Lemma add_csubsts_cexpr ew lctx ctx (ρ : csubsts lctx ctx) (c : open_cexpr _) :
        (add ew ρ) $$ c = subst (fst ew) (ρ $ c).
        admit.
      Qed.
      rewrite add_csubsts_cexpr.
      Lemma add_csubsts_size ew lctx ctx (ρ : csubsts lctx ctx) (s : open_size _) :
        (add ew ρ) $$ s = subst (fst ew) (ρ $ s).
        admit.
      Qed.
      rewrite add_csubsts_size.
      eapply imply_refl.
    }
    eapply openup2_apply.
    {
      intros.
      Lemma unfold_pair A B (ab : A * B) : ab = (fst ab, snd ab).
        destruct ab; eauto.
      Qed.
      erewrite (unfold_pair x2) at 2.
      rewrite csubsts_subst_s_c.
      rewrite csubsts_subst_s_s.
      repeat rewrite csubsts_value.
      Lemma subst_s_c_subst_e (e : expr) (b : open_cexpr _) :
        subst !(!e) b = subst e b.
        admit.
      Qed.
      rewrite subst_s_c_subst_e.
      Lemma subst_s_s_subst_e (e : expr) (b : open_size _) :
        subst !(!e) b = subst e b.
        admit.
      Qed.
      rewrite subst_s_s_subst_e.
      eapply imply_refl.
    }
    set (Ps' := _ :: _) at 2.
    subst Ps'.
    eapply IH.
  }
  Unfocus.
  Focus 5.
  {
    (* case fold *)
    destruct IHtyping as [wB [w IH]].
    unfold related in *.
    exists wB.
    exists (Wfold w).
    rename ctx into lctx.
    set (ρ := make_ρ lctx) in *.
    set (ctx := make_ctx lctx) in *.
    set (Ps := make_Ps T) in *.

    eapply openup1_apply.
    {
      intros.
      Lemma csubsts_Efold lctx ctx (ρ : csubsts lctx ctx) t (e : open_expr lctx) : ρ $$ (Efold t e) = Efold (ρ $$ t) (ρ $$ e).
        admit.
      Qed.
      rewrite csubsts_Efold.
      Lemma plug_ECfold t (e : expr) : (ECfold t ECempty) $$ e = Efold t e.
        admit.
      Qed.
      rewrite <- plug_ECfold.
      Lemma tmp_add_0 lctx ctx (ρ : csubsts lctx ctx) n : n + !F0 = n.
        admit.
      Qed.
      erewrite <- (tmp_add_0 x1 !(x1 $$ c)).
      Lemma relE_replace_wB_add_0 lctx τ c s ctx (ρ : csubsts lctx ctx) e w wB : 
        [] |~~
           (e, w) ∈ relE τ (wB + Wconst 0) c s ρ ===>
           (e, w) ∈ relE τ wB c s ρ.
        admit.
      Qed.
      eapply imply_trans.
      { eapply relE_replace_wB_add_0. }
      eapply LRbind'''.
    }
    eapply openup1_exists1 with (x := ρ $ w).
    rewrite openup2_comp_openup1.
    rewrite openup2_dedup.
    rewrite openup1_and.
    eapply split.
    {
      admit. (* IsEC *)
    }
    rewrite openup1_and.
    eapply split.
    {
      eapply IH.
    }
    rewrite openup1_and.
    eapply split.
    {
      unfold relEC.
      eapply openup1_forall1.
      eapply openup2_forall1.
      rewrite openup3_imply.
      eapply ORimply_intro.
      rewrite openup3_and.
      eapply destruct_and.
      subst Ps.
      set (Ps := _ :: _ :: _).
      rewrite openup3_totop2.
      rewrite openup3_shrink.
      eapply openup2_apply.
      {
        intros.
        eapply relE_replace_w.
      }
      eapply openup2_exists1 with (x := openup1 Wfold V0).
      rewrite openup3_comp_openup1.
      rewrite openup3_and.
      eapply split; first last.
      {
        admit. (* wsteps *)
      }
      eapply openup3_apply.
      {
        intros.
        unfold apply at 1.
        simpl.
        unfold plug.
        rewrite coerce_F0.
        eapply relV_relE.
      }
      rewrite openup3_and.
      eapply split.
      {
        rewrite openup3_shrink.
        eapply openup2_apply.
        {
          intros.
          eapply inj_imply.
          Lemma csubsts_Sfold lctx ctx (ρ : csubsts lctx ctx) (s : open_size lctx) :
            ρ $$ (Sfold s) = Sfold (ρ $ s).
            admit.
          Qed.
          rewrite csubsts_Sfold.
          Lemma fold_sle_intro t (e : expr) (s : size) :
            !e <= s ->
            !(Efold t e) <= Sfold s.
            admit.
          Qed.
          eapply fold_sle_intro.
        }
        subst Ps.
        totopn 1.
        eapply openup3_apply_in.
        {
          intros.
          eapply inj_and_elim.
        }
        rewrite openup3_and.
        eapply destruct_and.
        totopn 1.
        eapply openup3_apply_in.
        {
          intros.
          eapply inj_and_elim.
        }
        rewrite openup3_and.
        eapply destruct_and.
        rewrite openup3_totop2.
        rewrite openup3_shrink.
        eapply ctx_refl.
      }
      eapply openup3_apply.
      {
        intros.
        eapply imply_trans.
        {
          eapply relV_type_equal.
          symmetry; eauto.
        }
        simpl.
        eapply imply_trans.
        {
          Lemma iota_inv ew ctx R : 
            [] |~~ ew ∈ (substr (ctx := ctx) (Rrecur R) R) ===> ew ∈ (Rrecur R).
            admit.
          Qed.
          eapply iota_inv.
        }
        set (v := @@, _) at 1.
        rewrite substr_abs.
        eapply imply_trans.
        {
          eapply beta_inv.
        }
        rewrite substr_and.
        rewrite substr_inj.
        rewrite substr_exists1.
        subst v.
        eapply imply_refl.
      }
      rewrite openup3_and.
      eapply split.
      {
        admit. (* typing *)
      }
      eapply openup3_exists1 with (x := V1).
      rewrite openup4_totop3.
      rewrite openup4_dedup.
      eapply openup3_apply.
      {
        intros.
        rewrite substr_exists1.
        eapply imply_refl.
      }
      combine_lift.
      set (ρ' := lift ρ).
      eapply openup3_exists1 with (x := V0).
      rewrite openup4_totop2.
      rewrite openup4_dedup.
      eapply openup3_apply.
      {
        intros.
        rewrite substr_and.
        rewrite substr_inj.
        rewrite substr_later.
        rewrite substr_app.
        rewrite substr_relV.
        rewrite substr_add_pair.
        rewrite substr_var0.
        rewrite substr_csubsts_shift.
        eapply imply_refl.
      }
      rewrite openup3_and.
      eapply split.
      {
        admit. (* fold _ = fold _ *)
      }
      rewrite openup3_later.
      eapply VMono.
      eapply openup3_apply.
      {
        intros.
        Lemma relV_rho_inv v w lctx τ' τ ctx (ρ : csubsts lctx ctx) :
          [] |~~ (v, w) ∈ relV (subst τ' τ) ρ ===> (v, w) ∈ relV τ (add (ρ $$ τ', relV τ' ρ) ρ).
          admit.
        Qed.
        eapply relV_rho_inv.
      }
      eapply openup3_apply.
      {
        intros.
        eapply relV_type_equal.
        {
          eapply subst_v_equal; eauto.
        }
      }
      rewrite openup3_totop1.
      rewrite openup3_totop2.
      subst Ps.
      eapply ctx_refl.
    }
    {
      admit. (* exists wE wBE *)
    }
  }
  Unfocus.
  {
    (* case var *)
    unfold related.
    exists (Wconst (ctx := ctx) 0).
    exists (Wvar x).
    rename ctx into lctx.
    set (ρ := make_ρ lctx) in *.
    set (ctx := make_ctx lctx) in *.
    set (Ps := make_Ps Γ) in *.
    eapply openup1_apply.
    {
      intros.
      rewrite csubsts_F0.
      rewrite coerce_F0.
      rewrite csubsts_Wconst.
      eapply relV_relE.
    }
    admit. (* by definition of make_ρ and make_Ps *)
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
  admit.
Qed.

