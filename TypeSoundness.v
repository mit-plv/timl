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
  admit.
Qed.

(*
        Global Instance Apply_open_rel_open_wexpr {ctxfo m ctx} : Apply (open_rel ctxfo (S m) ctx) (open_term ctxfo wexpr) (open_rel ctxfo m ctx) :=
          {
            apply := ORapp
          }.

        Definition ORapp' {ctxfo m ctx} : open_rel ctxfo (S m) ctx -> open_term ctxfo expr * open_term ctxfo width -> open_rel ctxfo m ctx.
          admit.
        Defined.

        Global Instance Apply_open_rel_open_expr_open_width {ctxfo m ctx} : Apply (open_rel ctxfo (S m) ctx) (open_term ctxfo expr * open_term ctxfo width) (open_rel ctxfo m ctx) :=
          {
            apply := ORapp'
          }.

        Lemma VElem ctxfo m ctx (r : wexpr -> open_rel ctxfo m ctx) x : x ∈ (ORabs r) == r x.
          admit.
        Qed.
        Lemma ttt1 ctx (P2 : rel 0 ctx) P x : 
          Forall2 eqv [x ∈ \x, P x; P2] [P x; P2].
          rewrite VElem.
          reflexivity.
        Qed.
        Lemma ttt2 ctx (Q : rel 0 ctx) P P2 x : 
          [P x; P2] |~~ Q ->
          [x ∈ \x, P x; P2] |~~ Q.
          intros H.
          rewrite VElem.
          eauto.
        Qed.



        simpl.

        eapply imply_gen.
        eapply VMorePs.
        eapply VCtxElimEmpty.
        subst ρ.
        intros ρ.
        (* need to change EC to C and IsEC *)
        simpl in ρ.
          Lemma LRappvv lctx ctx (v₀ : expr) (w₀ w₀' : width) (τ₁ : open_type lctx) (c : open_cexpr (CEexpr :: lctx)) (s : open_size (CEexpr :: lctx)) (τ₂ : open_type (CEexpr :: lctx)) (ρ : csubsts lctx ctx) (w₁ : width) (s₁ : open_size lctx) P1 P2 Q :
            [] |~~ 
               (v₀, w₀') ∈ relV (Tarrow τ₁ c s τ₂) ρ /\ ⌈P1 /\ P2 /\ wsteps w₀ w₀'⌉ ===>
               ∀v we', (v, we') ∈ relV τ₁ ρ /\ ⌈Q v /\ !v ≤ ρ $$ s₁ /\ wsteps w₁ we'⌉ ===>
                       (Eapp v₀ v, Wapp w₀ w₁) ∈ relE (subst s₁ τ₂) (Wconst 1 + WappB w₀ w₁) !(ρ $ (subst s₁ c)) (ρ $ (subst s₁ s)) ρ.
          Proof.
            Lemma LRappvv' lctx ctx (v₀ : expr) (w₀ w₀' : width) (τ₁ : open_type lctx) (c : open_cexpr (CEexpr :: lctx)) (s : open_size (CEexpr :: lctx)) (τ₂ : open_type (CEexpr :: lctx)) (ρ : csubsts lctx ctx) (w₁ : width) (s₁ : open_size lctx) :
              [] |~~ 
                 (v₀, w₀') ∈ relV (Tarrow τ₁ c s τ₂) ρ /\ ⌈wsteps w₀ w₀'⌉ ===>
                 ∀v we', (v, we') ∈ relV τ₁ ρ /\ ⌈!v ≤ ρ $$ s₁ /\ wsteps w₁ we'⌉ ===>
                         (Eapp v₀ v, Wapp w₀ w₁) ∈ relE (subst s₁ τ₂) (Wconst 1 + WappB w₀ w₁) !(ρ $ (subst s₁ c)) (ρ $ (subst s₁ s)) ρ.
            Proof.
              Lemma imply_intro ctxfo lctx ctx (ρ : open_csubsts ctxfo lctx ctx) (P Q : csubsts lctx ctx -> rel 0 ctx) Ps :
                openup1 P ρ :: Ps |~ openup1 Q ρ ->
                Ps |~ openup1 (fun ρ => P ρ ===> Q ρ) ρ.
                admit.
              Qed.
              eapply imply_intro_e.
              eapply destruct_and.
              unfold tmp.
              rewrite VElem.
              eapply destruct_and.

              (*here*)

              Definition lift_e {T ctx} (r : rel 0 ctx) : open_rel [T] 0 ctx := fun _ => r.

              Lemma rdestruct_e ctx T (Q : rel 0 ctx) (P : T -> rel 0 ctx) Ps :
                (P : open_rel [T] _ _) :: liftPs1 T Ps |~ lift_e Q ->
                (∃x, P x) :: Ps |~~ Q.
                admit.
              Qed.
              eapply rdestruct_e.

              Lemma rdestruct_1 T1 T2 ctxfo ctx (Q : open_rel ctxfo 0 ctx) (P : T1 -> T2 -> rel 0 ctx) Ps :
                (P : open_rel [T1;T2] _ _) :: liftPs1 T Ps |~ lift_e Q ->
                (fun x1 => ∃x2, P x1 x2) :: Ps |~~ Q.
                admit.
              Qed.  
            Qed.
            admit.
          Qed.

          Definition pair_of_csubsts {lctx ctx} (ρ : csubsts (CEexpr :: lctx) ctx) : wexpr * csubsts lctx ctx.
            admit.
          Qed.

          Definition rhosnd {lctx ctx} (rho : csubsts (CEexpr :: lctx) ctx) := snd (pair_of_csubsts rho).
          assert (Hassert :
                    [] |~~
                       (ρ $$ Evar #0, ρ $$ Wvar #0)
                       ∈ relV (Tarrow τ₁ c s τ₂) (rhosnd ρ) /\
                    ⌈ρ $$ shift1 CEexpr e₀ ~>* ρ $$ Evar #0 /\
                    !(ρ $$ Evar #0) ≤ ρ $$ shift1 CEexpr nouse /\
                    wsteps (rhosnd ρ $ w₀) (ρ $$ Wvar #0) ⌉ ===>
                           (∀(v : expr) (we' : width),
                              (v, we') ∈ relV τ₁ (rhosnd ρ) /\
                              ⌈ρ $$ shift1 CEexpr e₁ ~>* v /\
                              !v ≤ rhosnd ρ $$ s₁ /\ wsteps (rhosnd ρ $ w₁) we' ⌉ ===>
                              (Eapp (ρ $ Evar #0) v, Wapp (rhosnd ρ $ w₀) (rhosnd ρ $ w₁))
                              ∈ relE (subst s₁ τ₂)
                              (Wconst 1 + WappB (rhosnd ρ $ w₀) (rhosnd ρ $ w₁))
                              !(rhosnd ρ $ subst s₁ c)
                              (rhosnd ρ $ subst s₁ s) (rhosnd ρ))).
          {
            eapply LRappvv.
          }
          admit. (* rearrange *)
        }
      }
      Lemma forall1intro ctxfo lctx ctx (ρ : open_csubsts ctxfo lctx ctx) (f : expr -> width -> csubsts lctx ctx -> rel 0 ctx) Ps :
        liftPs1 wexpr Ps |~ openup1 
                (fun ρ => 
                   let pr := pair_of_csubsts ρ in 
                   let vw := fst pr in 
                   let ρ := snd pr in 
                   let v := fst vw in
                   let w := snd vw in
                   f v w ρ) ((fun vw => openup1 (add vw) ρ) : open_csubsts (wexpr :: ctxfo) _ _) ->
        Ps |~ openup1 (fun ρ => ∀v w, f v w ρ) ρ.
        admit.
      Qed.

      eapply forall1intro.
      eapply imply_intro.
      Lemma snd_pair_of_csubsts_cexpr lctx ctx (rho : csubsts (CEexpr :: lctx) ctx) (x : open_cexpr lctx) : snd (pair_of_csubsts rho) $$ x = rho $$ (shift1 CEexpr x).
        admit.
      Qed.
      Lemma snd_pair_of_csubsts_cexpr' lctx ctx (rho : csubsts (CEexpr :: lctx) ctx) (x : open_cexpr lctx) : csubsts_cexpr (snd (pair_of_csubsts rho)) x = csubsts_cexpr rho (shift1 CEexpr x).
        admit.
      Qed.
      simpl.
      (* erewrite snd_pair_of_csubsts_cexpr. *)
      (* erewrite snd_pair_of_csubsts_cexpr'. *)
      admit. (* rearrange *)
    }

    Lemma and_imply_and ctx (P P' Q Q' : rel 0 ctx) Ps :
      Ps |~~ P ===> P' ->
      Ps |~~ Q ===> Q' ->
      Ps |~~ P /\ Q ===> P' /\ Q'.
      admit.
    Qed.

    Lemma imply_refl ctx (P : rel 0 ctx) : [] |~~ P ===> P.
      admit.
    Qed.
*)

(*
Lemma adequacy B e τ c s : ⊩ B [] e τ c s -> forall n e', ~># e n e' -> n ≤ (1 + B) * (1 + !c).
  admit.
Qed.

Theorem sound_wrt_bound_proof : sound_wrt_bounded.
Proof.
  admit.
Qed.

Definition lift_Rel {ctx t2} new : Rel ctx t2 -> Rel (new :: ctx) t2 :=
  fun r var x => r var.

Notation lift_ρ := lift_Rel (only parsing).

(* should compute *)
Definition extend {var t2} ctx new : Funvar var ctx t2 -> Funvar var (ctx ++ new) t2.
  induction ctx.
  {
    simpl.
    intros r.
    exact (openupSingle r).
  }
  {
    simpl.
    intros r x.
    exact (IHctx (r x)).
  }
Defined.

Definition add_Funvar {var} `{H : Add (A var) (B var) (C var)} {ctx} (a : Funvar var ctx A) (b : Funvar var ctx B) : Funvar var ctx C :=
  openup5 (t1 := A) (t2 := B) add a b.

Global Instance Add_Funvar {var} `{Add (A var) (B var) (C var)} {ctx} : Add (Funvar var ctx A) (Funvar var ctx B) (Funvar var ctx C) :=
  {
    add := add_Funvar
  }.

Definition pair_var var := (type * rel var 1)%type.

Global Instance Add_pair_csubsts' {var lctx} : Add (pair_var var) (flip csubsts lctx var) (flip csubsts (CEtype :: lctx) var) :=
  {
    add := add_pair
  }.

Notation RTexpr := (const expr).
Notation RTtype := (const type).

Global Instance Add_expr_csubsts' {var lctx} : Add (RTexpr var) (flip csubsts lctx var) (flip csubsts (CEexpr :: lctx) var) :=
  {
    add := add_expr
  }.

Global Instance Apply_rel_expr' {var n} : Apply (rel var (S n)) (RTexpr var) (rel var n) :=
  {
    apply := Rapp
  }.

Definition c2n' {ctx} (c : Rel ctx (const cexpr)) : Rel ctx (const nat) :=
  fun var => openup1 (t1 := const cexpr) (t2 := const nat) c2n (c var).

Global Instance Coerce_cexpr_nat' : Coerce (Rel ctx (const cexpr)) (Rel ctx (const nat)) :=
  {
    coerce := c2n'
  }.

(*
Definition openE B {lctx} tau c s {var ctx} := openup1 (t1 := flip csubsts lctx) (t2 := 1) (@relE B lctx tau c s var) (ctx := ctx).
Definition goodExpr B {lctx} tau c s {ctx} (ρ : t_ρ ctx lctx) : Rel ctx 1 := fun var => openE B tau c s (ρ var).
Definition openV B {lctx} tau {var ctx} := openup1 (t1 := flip csubsts lctx) (t2 := 1) (@relV B lctx tau var) (ctx := ctx).
Definition goodValue B {lctx} tau {ctx} (ρ : t_ρ ctx lctx) : Rel ctx 1 := fun var => openV B tau (ρ var).
*)

(*
Definition goodECopen {var lctx lctx'} : nat -> expr -> econtext -> csubsts var lctx -> open_type lctx -> open_cexpr [CEexpr] -> open_size [CEexpr] -> csubsts var lctx' -> open_type lctx' -> rel var 0 :=
  fun B e E ρ τ c s ρ' τ' =>
    (∀v, v ∈ relV B τ ρ /\ ⌈e ~>* v⌉ ===> plug E v ∈ relE B τ' !(c $ v) (s $ v) ρ')%rel.

Definition goodEC {lctx lctx'} : nat -> expr -> econtext -> Substs [] lctx -> open_type lctx -> open_cexpr [CEexpr] -> open_size [CEexpr] -> Substs [] lctx' -> open_type lctx' -> Rel [] 0 :=
  fun B e E ρ τ c s ρ' τ' var => 
    goodECopen B e E (ρ var) τ c s (ρ' var) τ'.
*)

Definition subst_Rel `{Subst t A B} {ctx} lctx (x : var t lctx) (v : Rel ctx (const (A (removen lctx x)))) (b : Rel ctx (const (B lctx))) : Rel ctx (const (B (removen lctx x))) :=
  fun var =>
    openup5 (t1 := const (A (removen lctx x))) (t2 := const (B lctx)) (t3 := const (B (removen lctx x))) (substx x) (v var) (b var).

Global Instance Subst_Rel `{Subst t A B} {ctx} : Subst t (fun lctx => Rel ctx (const (A lctx))) (fun lctx => Rel ctx (const (B lctx))) :=
  {
    substx := subst_Rel
  }.

Global Instance Add_Funvar' {var} `{H : Add A B C} {ctx} : Add (Funvar var ctx (const A)) (Funvar var ctx (const B)) (Funvar var ctx (const C)) :=
  {
    add := add_Funvar (A := const A) (B := const B) (C := const C) (H := H)
  }.

Definition add_Rel `{Add A B C} {ctx} (a : Rel ctx (const A)) (b : Rel ctx (const B)) : Rel ctx (const C) :=
  fun var => add (a var) (b var).

Global Instance Add_Rel `{Add A B C} {ctx} : Add (Rel ctx (const A)) (Rel ctx (const B)) (Rel ctx (const C)) :=
  {
    add := add_Rel
  }.


Fixpoint forall_erel {T m} : (T -> erel m) -> erel m :=
  match m with
    | 0 => fun f => forall x, f x
    | S m' => fun f e => forall_erel (flip f e)
  end.

Delimit Scope OR with OR.
Bind Scope OR with open_term.

Section OR.

  Definition interp2varT (t : rtype) : varT :=
    fun var =>
      match t with
        | RTvar m => var m
        | RTcsubsts lctx => csubsts var lctx
        | RTother T => T
      end.

  Fixpoint Funvar2open_term {t var ctx} : Funvar var (map interp2varT ctx) t -> open_term var ctx t :=
    match ctx with
      | nil => id
      | t :: ctx' => fun f x => Funvar2open_term (f x)
    end.

  Global Instance Coerce_Funvar_open_term {t var ctx} : Coerce (Funvar var (map interp2varT ctx) t) (open_term var ctx t) :=
    {
      coerce := Funvar2open_term
    }.

  Fixpoint open_term2Funvar {t var ctx} : open_term var ctx t -> Funvar var (map interp2varT ctx) t :=
    match ctx with
      | nil => id
      | t :: ctx' => fun f x => open_term2Funvar (f x)
    end.

  Global Instance Coerce_open_term_Funvar {t var ctx} : Coerce (open_term var ctx t) (Funvar var (map interp2varT ctx) t) :=
    {
      coerce := open_term2Funvar
    }.

  Context `{var : nat -> Type, ctx : rcontext}.

  (* Notation  := (map interp2varT). *)

  (* Global Instance Coerce_rcontext_varTs : Coerce rcontext (list ((nat -> Type) -> Type)) := *)
  (*   { *)
  (*     coerce := map interp2varT *)
  (*   }. *)

  (* Definition ORvar {n : nat} := openup3 (t := n) (@Rvar var n) (ctx := ctx). *)
  Definition openup3' {var t T} f {ctx} (a : T) : open_term var ctx t :=
    !(openup3 f a).

  Definition ORinj : Prop -> open_term var ctx 0 := 
    openup3' (t := 0) (@Rinj var).

  Definition openup5' {var t1 t2 t3} f {ctx} (a : open_term var ctx t1) (b : open_term var ctx t2) : open_term var ctx t3 :=
    !(openup5 f !a !b).

  Definition ORand : open_term var ctx 0 -> open_term var ctx 0 -> open_term var ctx 0 := 
    openup5' (@Rand var) (t1 := 0) (t2 := 0) (t3 := 0).
  Definition ORor : open_term var ctx 0 -> open_term var ctx 0 -> open_term var ctx 0 := 
    openup5' (@Ror var) (t1 := 0) (t2 := 0) (t3 := 0).
  Definition ORimply : open_term var ctx 0 -> open_term var ctx 0 -> open_term var ctx 0 := 
    openup5' (@Rimply var) (t1 := 0) (t2 := 0) (t3 := 0).

  Definition openup2' {var t1 t2 T} f {ctx} (a : T -> open_term var ctx t1) : open_term var ctx t2 :=
    !(openup2 f (fun x => !(a x))).

  Definition ORforall2 {n} : (var n -> open_term var ctx 0) -> open_term var ctx 0 := 
    openup2' (t1 := 0) (t2 := 0) (@Rforall2 var n).
  Definition ORexists2 {n} : (var n -> open_term var ctx 0) -> open_term var ctx 0 := 
    openup2' (t1 := 0) (t2 := 0) (@Rexists2 var n).
  Definition ORforall1 {T} : (T -> open_term var ctx 0) -> open_term var ctx 0 := 
    openup2' (t1 := 0) (t2 := 0) (@Rforall1 var T).
  Definition ORexists1 {T} : (T -> open_term var ctx 0) -> open_term var ctx 0 := 
    openup2' (t1 := 0) (t2 := 0) (@Rexists1 var T).
  Definition ORabs {n : nat} : (expr -> open_term var ctx n) -> open_term var ctx (S n) := 
    openup2' (t1 := n) (t2 := S n) (@Rabs var n).
  Definition ORapp {n} : open_term var ctx (S n) -> open_term var ctx (const expr) -> open_term var ctx n := 
    openup5' (t1 := S n) (t2 := const expr) (t3 := n) (@Rapp var n).
  Definition ORrecur {n : nat} : (var n -> open_term var ctx n) -> open_term var ctx n := 
    openup2' (t1 := n) (t2 := n) (@Rrecur var n).

  Definition openup1' {var t1 t2} f {ctx} (a : open_term var ctx t1) : open_term var ctx t2 := 
    !(openup1 f !a).

  Definition ORlater : open_term var ctx 0 -> open_term var ctx 0 := 
    openup1' (t1 := 0) (t2 := 0) (@Rlater var).

  Definition ORtrue : open_term var ctx 0 := ORinj True.
  Definition ORfalse : open_term var ctx 0 := ORinj False.

End OR.

Unset Maximal Implicit Insertion.

Notation RTexpr := (const expr).

Global Instance Apply_open_term_RTexpr {var ctx n} : Apply (open_term var ctx (S n)) (open_term var ctx RTexpr) (open_term var ctx n) :=
  {
    apply := ORapp
  }.

Notation "⊤" := ORtrue : OR.
Notation "⊥" := ORtrue : OR.
Notation "⌈ P ⌉" := (ORinj P) : OR.
Notation "\ x .. y , p" := (ORabs (fun x => .. (ORabs (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity) : OR.
Notation "∀ x .. y , p" := (ORforall1 (fun x => .. (ORforall1 (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity) : OR.
Notation "∃ x .. y , p" := (ORexists1 (fun x => .. (ORexists1 (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity) : OR.
Notation "∀₂ x .. y , p" := (ORforall2 (fun x => .. (ORforall2 (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity) : OR.
Notation "∃₂ x .. y , p" := (ORexists2 (fun x => .. (ORexists2 (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity) : OR.
Notation "@@ x .. y , p" := (ORrecur (fun x => .. (ORrecur (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity) : OR.
Infix "/\" := ORand : OR.
Infix "\/" := ORor : OR.
Infix "===>" := ORimply (at level 86) : OR.
Notation "▹" := ORlater : OR.

Delimit Scope OR with OR.

Module test_OR.
  
  Variable var : nat -> Type.
  Variable ctx : rcontext.

  Open Scope OR.
  
  Definition ttt1 : open_term var ctx 1 := \e , ⊤.
  Definition ttt2 : open_term var ctx 1 := \e , ⌈e ↓ Tunit⌉.
  Definition ttt3 : open_term var ctx 0 := ⌈True /\ True⌉.
  Definition ttt4 : open_term var ctx 0 := ∀e, ⌈e = @Ett nil⌉.
  Definition ttt5 : open_term var ctx 0 := ∃e, ⌈e = @Ett nil⌉.

End test_OR.

Delimit Scope OpenTerm with OpenTerm.
Bind Scope OpenTerm with OpenTerm.

Set Maximal Implicit Insertion.
Section OpenTerm.

  Context `{ctx : rcontext}.
  Notation OpenTerm := (OpenTerm ctx).
  
  Definition OTinj P : OpenTerm 0 := fun var => ORinj P.
  Definition OTtrue : OpenTerm 0 := fun var => ORtrue.
  Definition OTfalse : OpenTerm 0 := fun var => ORfalse.
  Definition OTand (a b : OpenTerm 0) : OpenTerm 0 := fun var => ORand (a var) (b var).
  Definition OTor (a b : OpenTerm 0) : OpenTerm 0 := fun var => ORor (a var) (b var).
  Definition OTimply (a b : OpenTerm 0) : OpenTerm 0 := fun var => ORimply (a var) (b var).
  Definition OTforall1 T (F : T -> OpenTerm 0) : OpenTerm 0 := fun var => ORforall1 (fun x => F x var).
  Definition OTexists1 T (F : T -> OpenTerm 0) : OpenTerm 0 := fun var => ORexists1 (fun x => F x var).
  Definition OTabs (n : nat) (F : expr -> OpenTerm n) : OpenTerm (S n) := fun var => ORabs (fun e => F e var).
  Definition OTapp n (r : OpenTerm (S n)) (e : OpenTerm RTexpr) : OpenTerm n := fun var => ORapp (r var) (e var).
  Definition OTlater (P : OpenTerm 0) : OpenTerm 0 := fun var => ORlater (P var).
  
End OpenTerm.
Unset Maximal Implicit Insertion.

Global Instance Apply_OpenTerm_RTexpr {ctx n} : Apply (OpenTerm ctx (S n)) (OpenTerm ctx RTexpr) (OpenTerm ctx n) :=
  {
    apply := OTapp
  }.

Notation "⊤" := OTtrue : OpenTerm.
Notation "⊥" := OTtrue : OpenTerm.
Notation "⌈ P ⌉" := (OTinj P) : OpenTerm.
Notation "\ x .. y , p" := (OTabs (fun x => .. (OTabs (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity) : OpenTerm.
Notation "∀ x .. y , p" := (OTforall1 (fun x => .. (OTforall1 (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity) : OpenTerm.
Notation "∃ x .. y , p" := (OTexists1 (fun x => .. (OTexists1 (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity) : OpenTerm.
Infix "/\" := OTand : OpenTerm.
Infix "\/" := OTor : OpenTerm.
Infix "===>" := OTimply (at level 86) : OpenTerm.
Notation "▹" := OTlater : OpenTerm.

Module test_OpenTerm.
  
  Variable ctx : rcontext.

  Open Scope OpenTerm.

  Definition ttt1 : OpenTerm ctx 1 := \e , ⊤.
  Definition ttt2 : OpenTerm ctx 1 := \e , ⌈e ↓ Tunit⌉.
  Definition ttt3 : OpenTerm ctx 0 := ⌈True /\ True⌉.
  Definition ttt4 : OpenTerm ctx 0 := ∀e, ⌈e = @Ett nil⌉.
  Definition ttt5 : OpenTerm ctx 0 := ∃e, ⌈e = @Ett nil⌉.

End test_OpenTerm.

Definition openupSingle' {var t} f {ctx} : open_term var ctx t := !(openupSingle f).

Definition Relapp' {ctx n} (r : OpenTerm ctx (S n)) (e : expr) : OpenTerm ctx n :=
  fun var =>
    ORapp (r var) (openupSingle' e).

Global Instance Apply_OpenTerm_expr ctx n : Apply (OpenTerm ctx (S n)) expr (OpenTerm ctx n) :=
  {
    apply := Relapp'
  }.

Definition openup7 {var t1 t2} : forall {ctx}, (t1 var -> Funvar var ctx t2) -> Funvar var ctx t1 -> Funvar var ctx t2.
  refine
    (fix F ctx : (t1 var -> Funvar var ctx t2) -> Funvar var ctx t1 -> Funvar var ctx t2 :=
       match ctx return (t1 var -> Funvar var ctx t2) -> Funvar var ctx t1 -> Funvar var ctx t2 with
         | nil => _
         | t :: ctx' => _ 
       end);
  simpl; eauto.
Defined.

Definition openup9 {t1 t2 t3 t4 var} (f : t1 var -> t2 var -> t3 var -> t4 var) : forall {ctx}, Funvar var ctx t1 -> Funvar var ctx t2 -> Funvar var ctx t3 -> Funvar var ctx t4.
  refine
    (fix F ctx : Funvar var ctx t1 -> Funvar var ctx t2 -> Funvar var ctx t3 -> Funvar var ctx t4 :=
       match ctx return Funvar var ctx t1 -> Funvar var ctx t2 -> Funvar var ctx t3 -> Funvar var ctx t4 with
         | nil => _
         | nv :: ctx' => _
       end);
  simpl; eauto.
Defined.

(*
Definition apply_Rel_Rel {n ctx t2} : Rel (n :: ctx) t2 -> Rel ctx n -> Rel ctx t2 :=
  fun f x var => openup7 (f var) (x var).

Global Instance Apply_Rel_Rel n ctx t2 : Apply (Rel (n :: ctx) t2) (Rel ctx n) (Rel ctx t2) :=
  {
    apply := apply_Rel_Rel
  }.
 *)

Reserved Infix "==" (at level 70, no associativity).

Section infer_rules.

  Context `{ctx : rcontext}.

  Open Scope OpenTerm.

  Inductive eqv : forall {n}, OpenTerm ctx n -> OpenTerm ctx n -> Prop :=
  | EVRefl n R : @eqv n R R
  | EVSymm n R1 R2 : @eqv n R1 R2 -> @eqv n R2 R1
  | EVTran n R1 R2 R3 : @eqv n R1 R2 -> @eqv n R2 R3 -> @eqv n R1 R3
  | EVLaterAnd P Q : eqv (▹ (P /\ Q)) (▹P /\ ▹Q)
  | EVLaterOr P Q : eqv (▹ (P \/ Q)) (▹P \/ ▹Q)
  | EVLaterImply P Q : eqv (▹ (P ===> Q)) (▹P ===> ▹Q)
  | EVLaterForall1 T P : eqv (▹ (∀x:T, P x)) (∀x, ▹(P x))
  | EVLaterExists1 T P : eqv (▹ (∃x:T, P x)) (∃x, ▹(P x))
  | EVLaterForallR (n : nat) P : eqv (fun var => ▹ (∀₂ R : var n, P var R))%OR (fun var => ∀₂ R, ▹(P var R))%OR
  | EVLaterExistsR (n : nat) P : eqv (fun var => ▹ (∃₂ R : var n, P var R))%OR (fun var => ∃₂ R, ▹(P var R))%OR
  | VElem n (R : OpenTerm ctx (S n)) (e : OpenTerm ctx RTexpr) : eqv ((\x, R $ x) $ e) (R $ e)
  | VRecur {n : nat} (R : OpenTerm (RTvar n :: ctx) n) : eqv (fun var => @@r, R var r)%OR (fun var => (@@r, R var r))%OR
  .

  Fixpoint Iff {n : nat} : OpenTerm ctx n -> OpenTerm ctx n -> OpenTerm ctx 0 :=
    match n return OpenTerm ctx n -> OpenTerm ctx n -> OpenTerm ctx 0 with
      | 0 => fun P1 P2 => P1 ===> P2 /\ P2 ===> P1
      | S n' => fun R1 R2 => ∀e : expr, Iff (R1 $ e) (R2 $ e)
    end.

  Infix "==" := Iff.

  Implicit Types Ps : list (OpenTerm ctx 0).
  
  Lemma VEqv Ps P1 P2 : eqv P1 P2 -> Ps |~ P1 -> Ps |~ P2.
    admit.
  Qed.


  (* Lemma VReplace2 Ps {n : nat} R1 R2 (P : OpenTerm (RTvar n :: ctx) 0) : Ps |~ R1 == R2 -> Ps |~ P $$ R1 -> Ps |~ P $$ R2. *)

End infer_rules.

Infix "==" := Iff.

Fixpoint squash {var t} (r : rel (rel var) t) : rel var t :=
  match r with
    | Rvar _ v => v
    | Rinj P => Rinj P
    | Rand a b => Rand (squash a) (squash b)
    | Ror a b => Ror (squash a) (squash b)
    | Rimply a b => Rimply (squash a) (squash b)
    | Rforall1 _ g => Rforall1 (fun x => squash (g x))
    | Rexists1 _ g => Rexists1 (fun x => squash (g x))
    | Rforall2 _ g => Rforall2 (fun x => squash (g (Rvar x)))
    | Rexists2 _ g => Rexists2 (fun x => squash (g (Rvar x)))
    | Rabs _ g => Rabs (fun e => squash (g e))
    | Rapp _ a e => Rapp (squash a) e
    | Rrecur _ g => Rrecur (fun x => squash (g (Rvar x)))
    | Rlater P => Rlater (squash P)
  end.

Fixpoint Sub' {t1 t2} (f : forall var, t1 var -> rel var t2) (x : forall var, t1 var) : forall var, rel var t2 :=
  fun var => squash ((f (rel var)) (x (rel var))).

Coercion interp2varT : rtype >-> varT.

Definition Sub {t1 t2} (f : OpenTerm [t1] (flip_rel t2)) (x : OpenTerm [] t1) : OpenTerm [] (flip_rel t2) := Sub' f x.

Fixpoint sub_open' {var t1 t2} {ctx} : open_term (rel var) (t1 :: ctx) (flip_rel t2) -> open_term (rel var) ctx t1 -> open_term var ctx (flip_rel t2) :=
  match ctx return open_term (rel var) (t1 :: ctx) (flip_rel t2) -> open_term (rel var) ctx t1 -> open_term var ctx (flip_rel t2) with
    | nil => fun f x => squash (f x)
    | t :: ctx' => fun f x a => sub_open' (flip f (map_rtype (@Rvar _) a)) (x (map_rtype (@Rvar _) a))
  end.

Definition SubOpen' {t1 t2 ctx} (f : OpenTerm (t1 :: ctx) (flip_rel t2)) (x : OpenTerm ctx t1) : OpenTerm ctx (flip_rel t2) := fun var => sub_open' (f (rel var)) (x (rel var)).

Global Instance Apply_OpenTerm_OpenTerm' {t1 t2 ctx} : Apply (OpenTerm (t1 :: ctx) (flip_rel t2)) (OpenTerm ctx t1) (OpenTerm ctx (flip_rel t2)) := 
  {
    apply := SubOpen'
  }.

Fixpoint sub_open {var t1 t2} (f : t1 (rel var) -> rel (rel var) t2) {ctx} : open_term (rel var) ctx t1 -> open_term var ctx (flip_rel t2) :=
  match ctx return open_term (rel var) ctx t1 -> open_term var ctx (flip_rel t2) with
    | nil => fun x => squash (f x)
    | t :: ctx' => fun x a => sub_open f (x (map_rtype (@Rvar _) a))
  end.

Definition SubOpen {t1 t2 ctx} (f : OpenTerm [t1] (flip_rel t2)) (x : OpenTerm ctx t1) : OpenTerm ctx (flip_rel t2) := fun var => sub_open (f (rel var)) (x (rel var)).

Global Instance Apply_OpenTerm_OpenTerm {t1 t2 ctx} : Apply (OpenTerm [t1] (flip_rel t2)) (OpenTerm ctx t1) (OpenTerm ctx (flip_rel t2)) := 
  {
    apply := SubOpen
  }.

Lemma VCtxElimEmpty' t (P : open_term (rel (rel2 mono_erel)) [t] 0) : 
  (forall n (x : interp_rtype (rel (rel2 mono_erel)) t),
     interp n (unrecur n (squash (P x)))) ->
  forall ctx (x : open_term (rel (rel2 mono_erel)) ctx t) n, 
    forall_ctx [] (interp_open n (unrecur_open n (sub_open P x))).
Proof.
  intros H.
  induction ctx.
  {
    simpl.
    intros x.
    simpl in *.
    intros n Htrue.
    eapply H.
  }
  {
    rename t into t2.
    rename a into t1.
    simpl in *.
    intros x.
    intros n a.
    eapply IHctx.
  }
Qed.

Lemma Forall_In A P ls (x : A) : Forall P ls -> In x ls -> P x.
Proof.
  intros Hf Hin; eapply Forall_forall in Hf; eauto.
Qed.

Fixpoint and_erel {m} : erel m -> erel m -> erel m :=
  match m with
    | 0 => and
    | S m' => fun a b x => and_erel (a x) (b x)
  end.

Fixpoint iff_erel {m} : erel m -> erel m -> Prop :=
  match m with
    | 0 => iff
    | S m' => fun a b => forall x, iff_erel (a x) (b x)
  end.

Instance Equal_erel m : Equal (erel m) :=
  {
    equal := iff_erel
  }.

Local Open Scope G.

Lemma iff_erel_refl {m} (a : erel m) : a == a.
  admit.
Qed.

Lemma iff_erel_symm {m} (a b : erel m) : a == b -> b == a.
  admit.
Qed.

Lemma iff_erel_trans {m} (a b c : erel m) : a == b -> b == c -> a == c.
  admit.
Qed.

Global Add Parametric Relation m : (erel m) (@iff_erel m)
    reflexivity proved by iff_erel_refl
    symmetry proved by iff_erel_symm
    transitivity proved by iff_erel_trans
      as iff_erel_Rel.

Hint Extern 0 (iff_erel _ _) => reflexivity.
Hint Extern 0 (_ <-> _) => reflexivity.

Section wf.

  Variable var1 var2 : nat -> Type.
  
  Record varEntry :=
    {
      Level : nat;
      Arity : nat;
      First : var1 Arity;
      Second : var2 Arity
    }.

  Inductive wf : nat -> list varEntry -> forall t, rel var1 t -> rel var2 t -> Prop :=
  | WFrecur n G m g g' :
      wf n G (Rrecur g) (Rrecur g') ->
      (forall x x', wf (S n) (@Build_varEntry n m x x' :: G) (g x) (g' x')) ->
      wf (S n) G (Rrecur g) (Rrecur g')
  | WFvar n G t x x' : 
      In (@Build_varEntry n t x x') G -> 
      wf n G (Rvar x) (Rvar x')
  | WFlater n G P P' :
      wf n G P P' ->
      wf (S n) G (Rlater P) (Rlater P')
  | WF0 G t r r' : @wf 0 G t r r'
  (* | WFle G n1 t r r' :  *)
  (*     @wf n1 G t r r' -> *)
  (*     forall n2, *)
  (*       n2 <= n1 -> *)
  (*       wf n2 G r r' *)
  | WFinj n G P : wf n G (Rinj P) (Rinj P)
  | WFand n G a b a' b' :
      wf n G a a' ->
      wf n G b b' ->
      wf n G (Rand a b) (Rand a' b')
  | WFor n G a b a' b' :
      wf n G a a' ->
      wf n G b b' ->
      wf n G (Ror a b) (Ror a' b')
  | WFimply n G a b a' b' :
      wf n G a a' ->
      wf n G b b' ->
      wf n G (Rimply a b) (Rimply a' b')
  | WFforall1 n G T g g' :
      (forall x : T, wf n G (g x) (g' x)) ->
      wf n G (Rforall1 g) (Rforall1 g')
  | WFexists1 n G T g g' :
      (forall x : T, wf n G (g x) (g' x)) ->
      wf n G (Rexists1 g) (Rexists1 g')
  | WFforall2 n G m g g' :
      (forall x x', wf n (@Build_varEntry n m x x' :: G) (g x) (g' x')) ->
      wf n G (Rforall2 g) (Rforall2 g')
  | WFexists2 n G m g g' :
      (forall x x', wf n (@Build_varEntry n m x x' :: G) (g x) (g' x')) ->
      wf n G (Rexists2 g) (Rexists2 g')
  | WFabs n G m g g' :
      (forall e, wf n G (g e) (g' e)) ->
      wf n G (Rabs (n := m) g) (Rabs g')
  | WFapp n G m r r' e :
      wf n G r r' ->
      wf n G (Rapp (n := m) r e) (Rapp r' e)
  .

  Record varEntry2 :=
    {
      Arity2 : nat;
      First2 : var1 Arity2;
      Second2 : var2 Arity2
    }.

  Inductive wf2 : list varEntry2 -> forall t, rel var1 t -> rel var2 t -> Prop :=
  | WF2recur G m g g' :
      (forall x x', wf2 (@Build_varEntry2 m x x' :: G) (g x) (g' x')) ->
      wf2 G (Rrecur g) (Rrecur g')
  | WF2var G t x x' : In (@Build_varEntry2 t x x') G -> wf2 G (Rvar x) (Rvar x')
  | WF2later G P P' :
      wf2 G P P' ->
      wf2 G (Rlater P) (Rlater P')
  | WF2inj G P : wf2 G (Rinj P) (Rinj P)
  | WF2and G a b a' b' :
      wf2 G a a' ->
      wf2 G b b' ->
      wf2 G (Rand a b) (Rand a' b')
  | WF2or G a b a' b' :
      wf2 G a a' ->
      wf2 G b b' ->
      wf2 G (Ror a b) (Ror a' b')
  | WF2imply G a b a' b' :
      wf2 G a a' ->
      wf2 G b b' ->
      wf2 G (Rimply a b) (Rimply a' b')
  | WF2forall1 G T g g' :
      (forall x : T, wf2 G (g x) (g' x)) ->
      wf2 G (Rforall1 g) (Rforall1 g')
  | WF2exists1 G T g g' :
      (forall x : T, wf2 G (g x) (g' x)) ->
      wf2 G (Rexists1 g) (Rexists1 g')
  | WF2forall2 G m g g' :
      (forall x x', wf2 (@Build_varEntry2 m x x' :: G) (g x) (g' x')) ->
      wf2 G (Rforall2 g) (Rforall2 g')
  | WF2exists2 G m g g' :
      (forall x x', wf2 (@Build_varEntry2 m x x' :: G) (g x) (g' x')) ->
      wf2 G (Rexists2 g) (Rexists2 g')
  | WF2abs G m g g' :
      (forall e, wf2 G (g e) (g' e)) ->
      wf2 G (Rabs (n := m) g) (Rabs g')
  | WF2app G m r r' e :
      wf2 G r r' ->
      wf2 G (Rapp (n := m) r e) (Rapp r' e)
  .

  (* Lemma wf_mono n1 G t r1 r2 : @wf n1 G t r1 r2 -> forall n2, n2 <= n1 -> wf n2 G r1 r2. *)
  (* Proof. *)
  (*   induction 1; intros n2 Hn2. *)
  (*   { *)
  (*     destruct n2 as [|n2]. *)
  (*     { econstructor. } *)
  (*     econstructor. *)
  (*     { *)
  (*       eapply IHwf. *)
  (*       simpl in *; omega. *)
  (*     } *)
  (*     intros x x'. *)
  (*     eapply H1. *)
  (*   } *)
  (* Qed. *)

  Definition to_varEntry n e := let '(Build_varEntry2 m a b) := e in @Build_varEntry n m a b.

  (* Definition toG n (G : list varEntry2) := *)
  (*   map (to_varEntry n) G. *)

  Fixpoint anyG f (G : list varEntry2) : Prop :=
    match G with
      | nil => f nil
      | e :: G' => forall n, anyG (fun G => f (to_varEntry n e :: G)) G'
    end.

  Lemma wf2_wf : forall G t r1 r2, @wf2 G t r1 r2 -> forall n, anyG (fun G => wf n G r1 r2) G.
  Proof.
    induction 1; simpl in *.
    {
      induction n; simpl in *.
      { 
        Lemma anyG_any G : forall f, (forall G, f G : Prop) -> anyG f G.
        Proof.
          induction G; simpl in *; eauto.
        Qed.
        eapply anyG_any.
        { intros; econstructor. }
      }
      Lemma anyG_imp2 G : forall (f1 f2 f : _ -> Prop), (forall G, f1 G -> f2 G -> f G) -> anyG f1 G -> anyG f2 G -> anyG f G.
      Proof.
        induction G; simpl in *; eauto.
        intros.
        eapply IHG; [ | eapply H0 | eapply H1]; eauto.
        simpl.
        eauto.
      Qed.
      eapply anyG_imp2.
      {
        intros G'; intros.
        econstructor; pattern G'; eauto.
      }
      {
        Lemma anyG_lift G : forall T f, (forall x : T, anyG (f x) G) -> anyG (fun G => forall x, f x G) G.
        Proof.
          induction G; simpl in *; eauto.
        Qed.
        eapply anyG_lift; intros x.
        eapply anyG_lift; intros x'.
        eapply H0.
      }      
      eapply IHn.
    }
    {
     admit. (* var *) 
    }
    {
      induction n; simpl in *.
      { 
        eapply anyG_any.
        { intros; econstructor. }
      }
      Lemma anyG_imp1 G : forall (f1 f : _ -> Prop), (forall G, f1 G -> f G) -> anyG f1 G -> anyG f G.
      Proof.
        induction G; simpl in *; eauto.
        intros.
        eapply IHG; [ | eapply H0 ]; eauto.
        simpl.
        eauto.
      Qed.
      eapply anyG_imp1.
      {
        intros G'; intros.
        econstructor; pattern G'; eauto.
      }
      eauto.
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
  Qed.

  Fixpoint wfOpen {t : nat} n G {ctx} : open_term var1 ctx t -> open_term var2 ctx t -> Type :=
    match ctx return open_term var1 ctx t -> open_term var2 ctx t -> Type with
      | nil => fun r1 r2 => wf n G r1 r2
      | RTvar m :: ctx' => fun r1 r2 => forall x1 x2, wfOpen n (@Build_varEntry n m x1 x2 :: G) (r1 x1) (r2 x2)
      | _ => fun _ _ => False
    end.  

End wf.

Definition WfOpen {t : nat} {ctx} n (R : OpenTerm ctx t) := forall var1 var2, wfOpen n nil (R var1) (R var2).

Lemma wf_OpenTerm m (P : OpenTerm [RTvar m] 0) n : WfOpen n P.
Proof.
  admit.
Qed.

Lemma squash_interp' :
  forall n G m (r1 : rel (rel (rel2 mono_erel)) m) (r2 : rel (rel2 mono_erel) m),
    wf n G r1 r2 ->
    Forall (fun ve => let n := Level ve in interp n (unrecur n (First ve)) == interp n (Second ve)) G ->
    (* forall n', *)
    (*   n' <= n -> *)
      interp n (unrecur n (squash r1)) == interp n (unrecur n r2).
Proof.
  induction 1; intros Hforall(*; intros n' Hn'*).
  {
    (* Require Import Arith. *)
    (* eapply le_lt_eq_dec in Hn'. *)
    (* destruct Hn' as [Hn' | Hn']. *)
    (* { eapply IHwf; eauto; simpl; omega. } *)
    (* subst. *)
    Opaque unrecur interp.
    simpl.
    Lemma interp_recur m n : forall n2 g, interp n2 (unrecur n (Rrecur (n := m) g)) == interp n2 (unrecur n (g (unrecur (pred n) (Rrecur g)))).
    Proof.
      induction n; simpl; intuition. 
    Qed.
    Lemma interp_var m (x : rel2 mono_erel m) n : interp n (unrecur n (Rvar x)) == interp n x.
    Proof.
      destruct n; simpl; eauto.
    Qed.
    repeat rewrite interp_recur.
    simpl.
    eapply H1; simpl; eauto.
    eapply Forall_cons; eauto.
    simpl.
    (* intros k1 k2 Hk1 Hk2. *)
    rewrite interp_var by eauto.
    eapply IHwf; simpl; eauto.
    Transparent unrecur interp.
  }
  {
    simpl in *.
    eapply Forall_In in Hforall; eauto.
    simpl in *.
    rewrite interp_var.
    eauto.
  }
  admit. (* later *)
  {
    (* assert (n' = 0) by (simpl in *; omega); subst. *)
    reflexivity.
  }
  (* { *)
  (*   eapply IHwf; simpl in *; eauto; omega. *)
  (* } *)
  {
    reflexivity.
  }
  {
    simpl.
    Lemma interp_and n : forall (a b : rel (rel2 mono_erel) 0), interp n (unrecur n (a /\ b)) <-> interp n (unrecur n a) /\ interp n (unrecur n b).
    Proof.
      induction n; simpl; intuition.
    Qed.
    repeat rewrite interp_and.
    simpl in *.
    rewrite IHwf1 by eauto.
    rewrite IHwf2 by eauto.
    eauto.
  }
  admit.
  admit.
  {
    simpl in *.
    Lemma interp_forall1 n T : forall (g : T -> rel (rel2 mono_erel) 0), interp n (unrecur n (Rforall1 g)) <-> forall x, interp n (unrecur n (g x)).
    Proof.
      induction n; simpl; intuition.
    Qed.
    repeat rewrite interp_forall1.
    intuition; eapply H0; eauto.
  }
  admit.
  {
    simpl in *.
    Lemma interp_forall2 n m : forall g, interp n (unrecur n (Rforall2 (n := m) g)) <-> forall x, interp n (unrecur n (g (R2var x))).
    Proof.
      induction n; simpl; intuition. 
    Qed.
    repeat rewrite interp_forall2.
    intuition; eapply H0; eauto; eapply Forall_cons; eauto; simpl; repeat rewrite interp_var; eauto.
  }
  admit.
  admit.
  admit.
Qed.

Lemma interp_monotone {m} (r : rel (rel2 mono_erel) m) : monotone (fun n => interp n (unrecur n r)).
  admit.
Qed.

Lemma squash_interp m (P : OpenTerm [RTvar m] 0) n (x : rel (rel2 mono_erel) m) : interp n (unrecur n (squash (P (rel (rel2 mono_erel)) x))) == interp n (unrecur n (P (rel2 mono_erel) (R2var (exist _ _ (interp_monotone x))))).
Proof.
  eapply squash_interp'.
  {
    eapply wf_OpenTerm.
  }
  {
    simpl.
    repeat econstructor; simpl.
    destruct n; eauto.
  }
Qed.

Lemma VCtxElimEmpty t (P : OpenTerm [t] 0) : [] |~ P -> forall ctx (x : OpenTerm ctx t), [] |~ P $ x.
Proof.
  intros H.
  intros ctx x.
  unfold valid in *.
  simpl in *.
  unfold InterpOpen in *.
  simpl in *.
  unfold SubOpen in *.
  simpl in *.
  unfold UnrecurOpen in *.
  simpl in *.
  intros n.
  eapply VCtxElimEmpty'.
  intros n' x'.
  destruct t.
  {
    simpl in *.
    rename n0 into m.
    rewrite squash_interp.
    eapply H.
    eauto.
  }
  admit. (* csubsts *)
  admit. (* other *)
Qed.

(*
Lemma VCtxElim t ctx (P : OpenTerm (t :: ctx) 0) : [] |~ P -> forall (x : OpenTerm ctx t), [] |~ P $ x.
Proof.
  induction ctx.
  {
    simpl.
    intros H x.
    admit.
  }
  {
    simpl in *.
    intros H x.
    admit.
  }
Qed.

Lemma VCtxElimEmpty t (P : OpenTerm [t] 0) : [] |~ P -> forall ctx (x : OpenTerm ctx t), [] |~ fun var => openup1 (P var) (x var).
Proof.
  intros H ctx x.

  Require Import Setoid.
  Require Import Coq.Classes.Morphisms.

  Fixpoint Funvar_pr {var t} (R : t var -> t var -> Prop) {ctx} : Funvar var ctx t -> Funvar var ctx t -> Prop :=
    match ctx return Funvar var ctx t -> Funvar var ctx t -> Prop with
      | nil => R
      | t' :: ctx' => fun a b => forall x, Funvar_pr R (a x) (b x)
    end.

  Definition Funvar_eq {var t ctx} (a b : Funvar var ctx t) := Funvar_pr eq a b.

  Infix "===" := Funvar_eq (at level 70).

  Lemma Funvar_eq_refl var t ctx (a : Funvar var ctx t) : a === a.
    admit.
  Qed.

  Lemma extend_openup1 t (P : OpenTerm [t] 0) ctx var (x : Funvar var ctx t) : openup7 (extend [t] ctx (P var)) x === openup1 (P var) x.
    induction ctx.
    {
      simpl in *.
      eapply Funvar_eq_refl.
    }
    {
      simpl in *.
      unfold Funvar_eq in *; simpl in *.
      intros x1.
      eapply IHctx.
    }
  Qed.
  Lemma VFunvarEq ctx (P Q : OpenTerm ctx 0) Ps : (forall var, P var === Q var) -> Ps |~ P -> Ps |~ Q.
    admit.
  Qed.
  eapply VFunvarEq.
  {
    intros.
    eapply extend_openup1.
  }
  eapply VCtxElim.
  Lemma VExtend ctx (P : OpenTerm ctx 0) : [] |~ P -> forall new, [] |~ (fun var => extend ctx new (P var)).
    admit.
  Qed.
  eapply VExtend with (P := P).
  eauto.
Qed.
 *)

*)