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

Lemma coerce_cexpr (a b : cexpr) : !(a + b) = !a + !b.
  admit.
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
     (E $$ e, wEe) ∈ relE τ' (wBe + wBEe) (c₁ + !c₂) s₂ ρ'.
Proof.
  Lemma exists1_elim' ctx t (Q : open_rel [] 0 ctx) (f : t -> rel 0 ctx) (Ps : list (open_rel [] 0 ctx)) :
    openup1 (ctx := [t]) f V0 :: liftPs (new := [t]) Ps |~ openup0 (ctx := [t]) Q ->
    ((∃x, f x) : open_rel [] 0 ctx) :: Ps |~ Q.
    admit.
  Qed.

  eapply imply_intro.
  Ltac totopn m :=
    eapply totop with (n := m); [ reflexivity | unfold removen ].
  
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
  repeat rewrite liftPs_cons.
  unfold liftPs, liftPs1, map.
  combine_lift.
  set (Ps := [_;_;_;_;_]).
  rewrite lift_openup0_empty.
  Lemma openup0_apply ctx (f g : rel 0 ctx) ctxfo Ps : 
    ([] |~~ f ===> g) ->
    Ps |~ openup0 (ctx := ctxfo) f ->
    Ps |~ openup0 (ctx := ctxfo) g.
    admit.
  Qed.
  eapply openup0_apply.
  {
    Lemma relE_replace_w lctx τ c s ctx (ρ : csubsts lctx ctx) e w wB : 
      [] |~~
         (∃w', (e, w') ∈ relE τ wB c s ρ /\ ⌈wsteps w w'⌉) ===>
         (e, w) ∈ relE τ wB c s ρ.
      admit.
    Qed.
    eapply relE_replace_w.
  }
  Lemma openup0_exists1 ctx t (f : t -> rel 0 ctx) ctxfo x Ps : 
    Ps |~ openup1 f x ->
    Ps |~ openup0 (ctx := ctxfo) (∃x, f x).
    admit.
  Qed.
  eapply openup0_exists1 with (x := openup2 Wapp V1 V2).
  rewrite openup1_and.
  eapply split.
  {
    eapply openup1_apply.
    {
      intros.
      Lemma relE_replace_wB lctx τ c s ctx (ρ : csubsts lctx ctx) e w wB : 
        [] |~~
           (∃wB', (e, w) ∈ relE τ wB' c s ρ /\ ⌈wsteps wB wB'⌉) ===>
           (e, w) ∈ relE τ wB c s ρ.
        admit.
      Qed.
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
      Lemma openup4_dedup {t0 t2 t3 t4} {f : t0 -> t0 -> t2 -> t3 -> t4} {ctxfo x0 x2 x3} : openup4 (ctx := ctxfo) f x0 x0 x2 x3 = openup3 (fun x => f x x) x0 x2 x3.
        admit.
      Qed.
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
      (*here*)
      }
    }
  }
  admit.
Qed.

Lemma LRbind' ctxfo (e : open_term ctxfo expr) (we : open_term ctxfo width) (wBe : open_term ctxfo width_nat) (E : open_term ctxfo econtext) wEe wBEe lctx (c₁ : open_cexpr lctx) (s₁ : open_size lctx) (c₂ : open_cexpr lctx) (s₂ : open_size lctx) (τ : open_type lctx) (τ' : open_type lctx) ctx (ρ : open_csubsts ctxfo lctx ctx) (Ps : list (open_rel ctxfo 0 ctx)) :
  Ps |~ openup1 (fun E => ⌈IsEC E⌉) E ->
  Ps |~ openup4 (fun ρ e we wBe => (e, we) ∈ relE τ wBe !(ρ $ c₁) (ρ $ s₁) ρ) ρ e we wBe ->
  Ps |~ openup6 (fun ρ E e we wEe wBEe => relEC E e we wEe wBEe (ρ $ s₁) (ρ $ c₂) (ρ $ s₂) τ τ' ρ ρ) ρ E e we wEe wBEe ->
  (exists wE, Ps |~ openup2 (fun w w' => [|wsteps w w'|]) wEe (openup2 Wapp wE we)) -> 
  (exists wBE, Ps |~ openup2 (fun w w' => [|wsteps w w'|]) wBEe (openup2 WappB wBE we)) ->
  Ps |~ openup5 (fun ρ E e wEe wBall => (E $$ e, wEe) ∈ relE τ' wBall !(ρ $ (c₁ + c₂)) (ρ $ s₂) ρ) ρ E e wEe (wBe + wBEe).
Proof.
  intros Hty He Hec HwEe HwBEe.
  rewrite openup5_totop4.
  rewrite openup5_comp_openup2.
  eapply openup6_apply.
  {
    intros.
    rewrite csubsts_Fadd.
    rewrite coerce_cexpr.
    eapply LRbind''' with (E := x4) (s₁ := x3 $ s₁) (τ := τ) (ρ := x3).
  }
  eapply openup6_exists1 with (x := we).
  rewrite openup7_and.
  eapply split.
  {
    rewrite openup7_shrink.
    rewrite openup6_shrink.
    rewrite openup5_shrink.
    rewrite openup4_totop1.
    rewrite openup4_totop1.
    rewrite openup4_shrink.
    rewrite openup3_totop1.
    rewrite openup3_shrink.
    rewrite openup2_totop1.
    rewrite openup2_shrink.
    admit. (* IsEC *)
  }
  rewrite openup7_and.
  eapply split.
  {
    rewrite openup7_totop2.
    rewrite openup7_shrink.
    rewrite openup6_totop3.
    rewrite openup6_shrink.
    rewrite openup5_totop4.
    rewrite openup5_shrink.
    rewrite openup4_totop1.
    rewrite openup4_totop1.
    rewrite openup4_totop3.
    rewrite openup4_totop3.
    eauto.
  }      
  rewrite openup7_and.
  eapply split.
  {
    rewrite openup7_totop1.
    rewrite openup7_shrink.
    rewrite openup6_totop1.
    rewrite openup6_totop5.
    rewrite openup6_totop2.
    rewrite openup6_totop5.
    rewrite openup6_totop5.
    rewrite openup6_totop5.
    eauto.
  }
  destruct HwEe as [wE HwEe].
  destruct HwBEe as [wBE HwBEe].
  eapply openup7_exists1 with (x := wE).
  eapply openup8_exists1 with (x := wBE).
  rewrite openup9_and.
  eapply split.
  {
    rewrite openup9_shrink.
    rewrite openup8_totop2.
    rewrite openup8_shrink.
    rewrite openup7_totop2.
    rewrite openup7_shrink.
    rewrite openup6_totop2.
    rewrite openup6_shrink.
    rewrite openup5_totop2.
    rewrite openup5_shrink.
    rewrite openup4_totop2.
    rewrite openup4_shrink.
    rewrite openup2_totop1 in HwEe.
    rewrite openup2_comp_openup2 in HwEe.
    eauto.
  }
  rewrite openup9_totop1.
  rewrite openup9_shrink.
  rewrite openup8_totop2.
  rewrite openup8_shrink.
  rewrite openup7_totop3.
  rewrite openup7_shrink.
  rewrite openup6_totop3.
  rewrite openup6_shrink.
  rewrite openup5_totop3.
  rewrite openup5_shrink.
  rewrite openup4_totop3.
  rewrite openup4_shrink.
  rewrite openup2_totop1 in HwBEe.
  rewrite openup2_comp_openup2 in HwBEe.
  eauto.
(*
    Inductive typingEC : econtext -> type -> type -> Prop :=
    | TECempty τ : typingEC ECempty τ τ
    | TECapp1 f arg τ τ₁ c s τ₂ :
        typingEC f τ (Tarrow τ₁ c s τ₂) ->
        (|- arg τ₁) ->
        typingEC (ECapp1 f arg) τ τ₂
    .

      Lemma imply_elim ctxfo lctx ctx (P Q : csubsts lctx ctx -> rel 0 ctx) (ρ : open_csubsts ctxfo lctx ctx) Ps : 
        Ps |~ openup1 (fun ρ => P ρ ===> Q ρ) ρ ->
        Ps |~ openup1 (fun ρ => P ρ) ρ ->
        Ps |~ openup1 (fun ρ => Q ρ) ρ.
        admit.
      Qed.
      Lemma imply_elim3 ctxfo lctx ctx (P1 P2 P3 Q : csubsts lctx ctx -> rel 0 ctx) (ρ : open_csubsts ctxfo lctx ctx) Ps : 
        Ps |~ openup1 (fun ρ => P1 ρ /\ P2 ρ /\ P3 ρ ===> Q ρ) ρ ->
        Ps |~ openup1 (fun ρ => P1 ρ) ρ ->
        Ps |~ openup1 (fun ρ => P2 ρ) ρ ->
        Ps |~ openup1 (fun ρ => P3 ρ) ρ ->
        Ps |~ openup1 (fun ρ => Q ρ) ρ.
        admit.
      Qed.
      Lemma imply_elim_e ctx (P Q : rel 0 ctx) Ps : 
        Ps |~~ P ===> Q ->
        Ps |~ P ->
        Ps |~ Q.
      Proof.
        admit.
      Qed.
      Lemma imply_gen_e ctx (P Q : rel 0 ctx) Ps :
        Ps |~~ P ===> Q ->
        P :: Ps |~~ Q.
      Proof.
        intros H.
        eapply imply_elim_e.
        {
          Lemma add_Ps ctxfo ctx (P Q : open_rel ctxfo 0 ctx) Ps : Ps |~ Q -> P :: Ps |~ Q.
            admit.
          Qed.
          eapply add_Ps.
          eauto.
 }
        eapply ctx_refl.
      Qed.
      Lemma imply_gen ctxfo lctx ctx (ρ : open_csubsts ctxfo lctx ctx) (P Q : csubsts lctx ctx -> rel 0 ctx) Ps :
        Ps |~ openup1 (fun ρ => P ρ ===> Q ρ) ρ ->
        openup1 P ρ :: Ps |~ openup1 Q ρ.
      Proof.
        intros H.
        eapply imply_elim.
        {
          eapply add_Ps.
          eauto.
        }
        eapply ctx_refl.
      Qed.
      eapply imply_elim3; eauto.
      Lemma VMorePs ctxfo ctx (P : open_rel ctxfo 0 ctx) Ps : [] |~ P -> Ps |~ P.
        admit.
      Qed.
      eapply VMorePs.
      eapply VCtxElimEmpty.
      rename ρ into ρ'.
      intros ρ.
      assert (Hassert :
                []
                  |~~ ⌈IsEC (ρ $$ E) ⌉ /\
                (ρ $$ e, ρ $$ we) ∈ relE τ (ρ $$ wBe) !(ρ $$ c₁) (ρ $$ s₁) ρ /\
                relEC (ρ $$ E) (ρ $$ e) (ρ $$ we) (ρ $$ wEe) 
                      (ρ $$ wBEe) (ρ $$ s₁) (ρ $$ c₂) (ρ $$ s₂) τ τ' ρ ρ ===>
                      ((ρ $ E) $ (ρ $ e), ρ $$ wEe)
                      ∈ relE τ' (ρ $$ wBe + ρ $$ wBEe) !(ρ $$ c₁ + ρ $$ c₂) (ρ $$ s₂) ρ
             ).
      {
        eapply forall1_elim4 with (
          P := fun (e : expr) (we : width) (c₁ : cexpr) (wBe : open_width WTnat []) =>
                 ⌈IsEC (ρ $$ E) ⌉ /\
                 (e, we) ∈ relE τ wBe !c₁ (ρ $$ s₁) ρ /\
                 relEC (ρ $$ E) e we (ρ $$ wEe) 
                       (ρ $$ wBEe) (ρ $$ s₁) (ρ $$ c₂) (ρ $$ s₂) τ τ' ρ ρ ===>
                       (ρ $$ E $$ e, ρ $$ wEe)
                       ∈ relE τ' (wBe + ρ $$ wBEe) !(c₁ + ρ $$ c₂) (ρ $$ s₂) ρ
        ).
        eapply LRbind.
      }
 *)
Qed.

Definition related {lctx} Γ wB w (e : open_expr lctx) τ (c : open_cexpr lctx) (s : open_size lctx) :=
  make_Ps (lctx := lctx) Γ |~ let ρ := make_ρ lctx in openup4 (fun ρ e w wB => (e, w) ∈ relE τ wB !(ρ $ c) (ρ $ s) ρ) ρ (ρ $ e) (ρ $ w) (ρ $ wB).

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
  {
    unfold related.
    exists (Wconst (ctx := ctx) 0).
    simpl.
    admit.
  }
  {
    unfold related in *.

    destruct IHtyping1 as [wB₀ [w₀ IH₀]].
    destruct IHtyping2 as [wB₁ [w₁ IH₁]].

    exists (wB₀ + (wB₁ + (Wconst 1 + WappB w₀ w₁))).
    exists (Wapp w₀ w₁).

    rename ctx into lctx.
    set (ρ := make_ρ lctx) in *.
    set (ctx := make_ctx lctx) in *.
    set (Ps := make_Ps Γ) in *.

    rewrite open_csubsts_Wadd.
    rewrite open_csubsts_Eapp.
    rewrite <- open_ECapp1.
    
    rewrite openup4_totop1.
    rewrite openup4_comp_openup2.
    rewrite openup5_totop2.

    eapply LRbind' with (c₂ := c₁ + subst s₁ c) (s₂ := subst s₁ s) (τ' := subst s₁ τ₂).
    {
      admit. (* IsEC *)
    }
    {
      eapply IH₀.
    }
    {
      unfold relEC.

      eapply relE_relEC.
      rewrite open_csubsts_Wadd.
      rewrite lift_Wadd.
      rewrite lift_openup1.
      rewrite unfold_open_plug.
      rewrite open_ECapp1.
      rewrite <- open_ECapp2.
      rewrite openup4_totop1.
      rewrite openup4_comp_openup2.
      rewrite (openup5_totop2 (x2 := lift ρ)).
      eapply LRbind'.
      {
        admit. (* IsEC *)
      }
      {
        instantiate (1 := lift (ρ $ w₁)).
        instantiate (1 := s₁).
        instantiate (1 := τ₁).
        admit. (* eapply IH₁ *)
      }
      {
        unfold relEC.
        eapply relE_relEC.
        rewrite liftPs_cons.
        rewrite lift_openup5.
        rewrite lift_openup1.
        rewrite liftPs_liftPs.
        combine_lift.
        rewrite unfold_open_plug.
        rewrite open_ECapp2.
        rewrite open_csubsts_Wadd.
        repeat rewrite lift_Wadd.
        repeat rewrite lift_rho_width.
        repeat rewrite lift_rho_expr.
        rewrite openup4_totop1.
        rewrite openup4_comp_openup2.
        erewrite (openup5_totop2 (x2 := lift (new := [width : Type; expr; width : Type; expr]) ρ)).
        rewrite open_csubsts_Wapp.
        rewrite open_csubsts_WappB.
        set (ρ' := lift ρ) in *.
        set (e₀' := ρ' $ e₀) in *.
        set (e₁' := ρ' $ e₁) in *.
        set (w₀' := ρ' $ w₀) in *.
        set (w₁' := ρ' $ w₁) in *.
        rewrite open_csubsts_Wconst.
        eapply totop with (n := 1); [ reflexivity | unfold removen ].
        rewrite openup5_and.
        eapply destruct_and.

        rewrite openup5_totop1.
        rewrite openup5_shrink.
        rewrite openup4_totop1.
        rewrite openup4_shrink.

        set (tmp := relV (Tarrow τ₁ c s τ₂)) at 1.
        simpl in tmp.
        subst tmp.
        rewrite openup3_beta.

        rewrite openup3_and.
        eapply destruct_and.

        eapply totop with (n := 1); [ reflexivity | unfold removen ].

        eapply openup3_exists1_elim.
        repeat rewrite liftPs_cons.
        repeat rewrite lift_openup5.
        rewrite openup4_and.
        eapply destruct_and.
        eapply totop with (n := 1); [ reflexivity | unfold removen ].
        rewrite openup4_totop2.

        rewrite openup4_shrink.
        eapply openup3_exists1_elim.
        repeat rewrite liftPs_cons.
        repeat rewrite lift_openup5.
        eapply openup4_exists1_elim.
        repeat rewrite liftPs_cons.
        repeat rewrite lift_openup5.
        rewrite openup5_and.
        eapply destruct_and.
        eapply totop with (n := 1); [ reflexivity | unfold removen ].
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

        eapply openup4_forall1_elim' with (e := V4) (w := V3).
        rewrite openup6_imply.
        rewrite openup6_shrink.
        rewrite openup5_totop1.
        rewrite openup5_shrink.
        rewrite openup4_totop1.
        rewrite openup4_shrink.
        eapply totop with (n := 5); [ reflexivity | unfold removen ].
        rewrite openup5_and.
        eapply destruct_and.
        rewrite openup5_totop1.
        rewrite openup5_shrink.
        rewrite openup4_totop1.
        rewrite openup4_shrink.
        eapply totop with (n := 2); [ reflexivity | unfold removen ].
        eapply imply_elim.
        subst e₀' e₁' w₀' w₁' ρ'.
        combine_lift.
        repeat rewrite lift_openup4.
        repeat rewrite lift_openup3.
        repeat rewrite lift_openup2.
        repeat rewrite lift_openup0.
        repeat rewrite lift_Wadd.
        repeat rewrite lift_rho_width.
        repeat rewrite lift_rho_expr.
        combine_lift.
        set (ρ' := lift ρ) in *.
        rewrite (openup5_totop3 (x3 := openup2 _ _ _)).
        rewrite openup5_comp_openup2.
        rewrite (openup6_totop5 (x5 := openup2 _ _ _)).

        rewrite openup6_comp_openup2.

        rewrite openup7_comp_openup0.
        rewrite openup6_comp_openup2.

        rewrite openup7_totop2.

        rewrite openup7_dedup.

        rewrite (openup6_totop1 (x1 := ρ' $ w₁ )).
        rewrite (openup6_totop2 (x2 := ρ' $ w₁ )).
        rewrite openup6_dedup.


        erewrite (rewrite_openup5 (x0 := ρ' $ w₁)); last first.
        {
          repeat extensionality'.
          rewrite csubsts_subst_s_c.
          rewrite csubsts_subst_s_s.
          reflexivity.
        }

        eapply openup5_apply.
        {
          intros.
          eapply relE_mono_tau_c_s with (v := x5).
        }
        rewrite openup5_and.
        eapply split.
        {
          eapply openup5_apply.
          {
            intros.
            eapply relE_rho with (w' := x1).
          }
          eapply openup5_apply.
          {
            intros.
            eapply relE_app_subst. 
          }

          eapply openup5_exists1 with (x := V2).
          eapply openup6_exists1 with (x := V0).
          eapply openup7_exists1 with (x := V1).
          rewrite openup8_and.
          eapply split.
          {
            rewrite openup8_totop6.
            rewrite openup8_shrink.
            rewrite openup7_totop4.
            rewrite openup7_shrink.
            eapply openup6_apply.
            {
              intros.
              eapply relE_replace_width.
            }
            eapply openup6_exists1 with (x := V3).
            rewrite openup7_and.
            eapply split.
            {
              rewrite openup7_totop4.
              rewrite openup7_shrink.
              rewrite openup6_totop1.
              rewrite openup6_totop1.
              rewrite openup6_totop3.
              rewrite openup6_totop3.
              rewrite openup6_totop4.
              erewrite rewrite_openup6; last first.
              {
                repeat extensionality'.
                rewrite csubsts_subst_s_c.
                rewrite csubsts_subst_s_s.
                repeat rewrite csubsts_value.
                reflexivity.
              }
              eapply ctx_refl.
            }
            admit. (* wsteps *)
          }
          admit. (* = Eabs /\ = Wabs *)
        }
        admit. (* !v <= rho $ s1 *)
      }
      {
        repeat rewrite lift_rho_width.
        set (ρ' := lift ρ) in *.
        exists (ρ' $ w₀).
        rewrite open_csubsts_Wapp.
        rewrite openup2_dedup.
        eapply openup1_apply.
        {
          intros.
          eapply inj_imply.
          intros.
          Lemma wsteps_refl t (w : open_width t []) : wsteps w w.
            admit.
          Qed.
          eapply wsteps_refl.
        }
        instantiate (1 := True).
        rewrite openup1_shrink.
        eapply inj_true_intro.
      }
      repeat rewrite lift_rho_width.
      set (ρ' := lift ρ) in *.
      Definition var0 {m ctx} : open_var m (m :: ctx).
        admit.
      Defined.
      Notation "#0" := var0 : var.
      Delimit Scope var with var.
      admit. (* exists wBE *)
    }
    {
      admit. (* exists wE *)
      (* exists (openup0 (Wabs (ρ $$ wB₁ + (Wconst 1 + Wapp (Wvar #0%var) (ρ $ w₁))) (Wapp (Wvar #0%var) (ρ $ w₁)))).     *)
    }
    {
      admit. (* exists wBE *)
    }
  }
  {
    (*here*)
    unfold related in *.
    simpl in *.
    unfold add_Ps_expr in *.
    admit.
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
    Instance Max_nat : Max nat :=
      {
        max := Peano.max
      }.
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