Require Import List.
Require Import Bedrock.Platform.Cito.GeneralTactics.
Require Import Bedrock.Platform.Cito.GeneralTactics4.
Require Import Order.
Export Order.

Import ListNotations.
Local Open Scope list_scope.

Local Open Scope F01.
Local Open Scope F.

Lemma leE_addx0 n : (n + 0 == n)%leE.
Proof.
  etransitivity.
  - eapply leE_addC.
  - eapply leE_add0x.
Qed.

Lemma leE_addcncn c n : (c *: n + c *: n == (2 * c)%QN *: n)%leE.
Proof.
  etransitivity.
  { symmetry; eapply leE_scaleDx. }
  eapply leE_scale; try reflexivity.
  eapply QN_addxx.
Qed.

Lemma leE_adda a b a' : (a == a' -> a + b == a' + b)%leE.
Proof.
  intros H; eapply leE_add; try reflexivity; eauto.
Qed.

Lemma leE_addb a b b' : (b == b' -> a + b == a + b')%leE.
Proof.
  intros H; eapply leE_add; try reflexivity; eauto.
Qed.

Lemma leE_addnn n : (n + n == 2%QN *: n)%leE.
Proof.
  etransitivity.
  { eapply leE_adda; symmetry; eapply leE_scale1x. }
  etransitivity.
  { eapply leE_addb; symmetry; eapply leE_scale1x. }
  etransitivity.
  { eapply leE_addcncn. }
  eapply leE_scale; try reflexivity.
  eapply QN_mulx1.
Qed.

Lemma leE_two_halves n : (n / 2%QN + n / 2%QN == n)%leE.
Proof.
  etransitivity.
  eapply leE_addcncn.
  symmetry; etransitivity.
  { symmetry; eapply leE_scale1x. }
  eapply leE_scale; try reflexivity.
  symmetry; eapply QN_2_mul_half.
Qed.

Local Open Scope leC_scope.

Lemma leC_mula a b a' : a <= a' -> a * b <= a' * b.
Proof.
  intros H; eapply leC_mul; eauto; reflexivity.
Qed.

Lemma leC_mulb a b b' : b <= b' -> a * b <= a * b'.
Proof.
  intros H; eapply leC_mul; eauto; reflexivity.
Qed.

Lemma leC_adda a b a' : a <= a' -> a + b <= a' + b.
Proof.
  intros H; eapply leC_add; eauto; reflexivity.
Qed.

Lemma leC_addb a b b' : b <= b' -> a + b <= a + b'.
Proof.
  intros H; eapply leC_add; eauto; reflexivity.
Qed.

Lemma leC_0 n : 0 <= n.
Proof.
  etransitivity.
  { eapply leC_leE; symmetry; eapply leE_mul0x. }
  etransitivity.
  { eapply leC_mula; eapply leC_01. }
  eapply leC_leE; eapply leE_mul1x.
Qed.

Lemma leC_add_b n m : n <= m + n.
Proof.
  etransitivity.
  { eapply leC_leE; symmetry; eapply leE_add0x. }
  eapply leC_adda; eapply leC_0.
Qed.

Lemma leC_add_a n m : n <= n + m.
Proof.
  etransitivity.
  { eapply leC_leE; symmetry; eapply leE_add0x. }
  etransitivity.
  { eapply leC_leE; eapply leE_addC. }
  eapply leC_addb; eapply leC_0.
Qed.

Lemma leC_addta a b a' : a <= a' -> a <= a' + b.
Proof.
  intros H; etransitivity; eauto; eapply leC_add_a.
Qed.

Lemma leC_addtb a b b' : b <= b' -> b <= a + b'.
Proof.
  intros H; etransitivity; eauto; eapply leC_add_b.
Qed.

Lemma leC_max_b a b : b <= Fmax a b.
Proof.
  etransitivity.
  { eapply leC_max_a. }
  eapply leC_leE; eapply leE_maxC.
Qed.

Lemma leC_max a b a' b' : a <= a' -> b <= b' -> Fmax a b <= Fmax a' b'.
Proof.
  intros H1 H2.
  eapply leC_max_c.
  { etransitivity; eauto; eapply leC_max_a. }
  etransitivity; eauto; eapply leC_max_b.
Qed.

Lemma leC_maxa a b a' : a <= a' -> Fmax a b <= Fmax a' b.
Proof.
  intros H; eapply leC_max; eauto; reflexivity.
Qed.

Lemma leC_maxb a b b' : b <= b' -> Fmax a b <= Fmax a b'.
Proof.
  intros H; eapply leC_max; eauto; reflexivity.
Qed.

Lemma leC_maxta a b a' : a <= a' -> a <= Fmax a' b.
Proof.
  intros H; etransitivity; eauto; eapply leC_max_a.
Qed.

Lemma leC_maxtb a b b' : b <= b' -> b <= Fmax a b'.
Proof.
  intros H; etransitivity; eauto; eapply leC_max_b.
Qed.

Lemma leC_max_idem n : Fmax n n <= n.
Proof.
  eapply leC_max_c; reflexivity.
Qed.

Lemma leC_max_lub a b c : a <= c -> b <= c -> Fmax a b <= c.
Proof.
  intros H1 H2.
  etransitivity.
  { eapply leC_maxa; eassumption. }
  etransitivity.
  { eapply leC_maxb; eassumption. }
  eapply leC_max_idem.
Qed.

Lemma leC_two_halves n : n / 2%QN + n / 2%QN <= n.
Proof.
  eapply leC_leE; eapply leE_two_halves.
Qed.

Definition subpath a b := exists c, c ++ a = b /\ Forall (fun a => a <> Punhide) c.

Lemma leC_cons x p i a : a <> Punhide -> Fvar (x, a :: p) i <= Fvar (x, p) i.
Proof.
  intros H.
  destruct a.
  { etransitivity.
    { eapply leC_add_a. }
    eapply leC_leE; eapply leE_pair.
  }
  { etransitivity.
    { eapply leC_add_b. }
    eapply leC_leE; eapply leE_pair.
  }
  { eapply leC_leE; eapply leE_inl. }
  { eapply leC_leE; eapply leE_inr. }
  { etransitivity.
    { eapply leC_add_b. }
    eapply leC_leE; eapply leE_unfold.
  }
  intuition.
Qed.

Lemma leC_path_subpath' x i p2 d : forall p1, d ++ p2 = p1 -> Forall (fun a => a <> Punhide) d -> Fvar (x, p1) i <= Fvar (x, p2) i.
  induction d; intros p1 H Hall; simpl in *.
  {
    subst.
    reflexivity.
  }
  destruct p1 as [ | a' p1].
  { discriminate. }
  inject H.
  inversion Hall; subst.
  etransitivity.
  { eapply leC_cons; eauto. }
  eapply IHd; eauto.
Qed.

Lemma leC_path_subpath x i p1 p2 : subpath p2 p1 -> Fvar (x, p1) i <= Fvar (x, p2) i.
Proof.
  intros H.
  destruct H as [c [H1 H2] ].
  subst.
  eapply leC_path_subpath'; eauto.
Qed.

Lemma leC_c_x (c : QN) x i : c <= Fvar x i.
Proof.
  etransitivity.
  { eapply leC_add_a. }
  eapply leC_addcx.
Qed.

Lemma leC_c_cx (c1 c2 : QN) x i : (c2 != 0)%QN -> c1 <= c2 *: Fvar x i.
Proof.
  intros H.
  eapply QN_exists_inverse in H.
  destruct H as [q' H].
  etransitivity.
  { eapply leC_leE; symmetry; eapply leE_scale1x. }
  etransitivity.
  {eapply leC_leE; symmetry; eapply leE_scale; eauto; reflexivity. }
  etransitivity.
  { eapply leC_leE; symmetry; eapply leE_scaleA. }
  eapply leC_scale; try reflexivity.
  etransitivity.
  { eapply leC_leE; eapply leE_scaleA. }
  eapply leC_c_x.
Qed.

Lemma leC_1_cx c x i : (c != 0)%QN -> F1 <= c *: Fvar x i.
Proof.
  intros H.
  etransitivity.
  { eapply leC_leE; symmetry; eapply leE_scale1x. }
  eapply leC_c_cx; eauto.
Qed.

Lemma leC_add0x' n n' : n <= n' -> F0 + n <= n'.
Proof.
  intros H; etransitivity; eauto; eapply leC_leE; eapply leE_add0x.
Qed.

Lemma leC_addccx (c1 c2 : QN) x i : (c2 != 0)%QN -> c1 + c2 *: Fvar x i <= c2 *: Fvar x i.
Proof.
  intros H.
  eapply QN_exists_inverse in H.
  destruct H as [q' H].
  etransitivity.
  { eapply leC_adda.
    etransitivity.
    { eapply leC_leE; symmetry; eapply leE_scale1x. }
    etransitivity.
    {eapply leC_leE; symmetry; eapply leE_scale; eauto; reflexivity. }
    eapply leC_leE; symmetry; eapply leE_scaleA.
  }
  etransitivity.
  { eapply leC_leE; symmetry; eapply leE_scalexD. }
  eapply leC_scale; try reflexivity.
  etransitivity.
  { eapply leC_adda; eapply leC_leE; eapply leE_scaleA. }
  eapply leC_addcx.
Qed.

Lemma leC_add1cx (c : QN) x i : (c != 0)%QN -> F1 + c *: Fvar x i <= c *: Fvar x i.
Proof.
  intros H.
  etransitivity.
  { eapply leC_adda; eapply leC_leE; symmetry; eapply leE_scale1x. }
  eapply leC_addccx; eauto.
Qed.

Lemma leC_add1x x i : F1 + Fvar x i <= Fvar x i.
Proof.
  etransitivity.
  { eapply leC_addb; eapply leC_leE; symmetry; eapply leE_scale1x. }
  etransitivity.
  { eapply leC_add1cx; eapply QN_1_not_0. }
  eapply leC_leE; eapply leE_scale1x.
Qed.

Lemma leC_addccx' n (c1 c2 : QN) x i : (c2 != 0)%QN -> n <= c2 *: Fvar x i -> c1 + n <= c2 *: Fvar x i.
Proof.
  intros Hc Hn.
  etransitivity.
  { eapply leC_addb; eassumption. }
  eapply leC_addccx; eauto.
Qed.

Lemma leC_add1cx' n c x i : (c != 0)%QN -> n <= c *: Fvar x i -> F1 + n <= c *: Fvar x i.
Proof.
  intros Hc H.
  etransitivity.
  { eapply leC_adda; eapply leC_leE; symmetry; eapply leE_scale1x. }
  eapply leC_addccx'; eauto.
Qed.

Lemma leC_add1x' n x i : n <= Fvar x i -> F1 + n <= Fvar x i.
Proof.
  intros H.
  etransitivity.
  { eapply leC_add1cx'. 
    { eapply QN_1_not_0. } 
    etransitivity; eauto.
    eapply leC_leE; symmetry; eapply leE_scale1x.
  }
  eapply leC_leE; eapply leE_scale1x.
Qed.

Lemma subpath_nil ls : Forall (fun a => a <> Punhide) ls -> subpath [] ls.
Proof.
  intros H.
  exists ls; rewrite app_nil_r; eauto.
Qed.

Definition is_not_Punhide a :=
  match a with
    | Punhide => false
    | _ => true
  end.

Lemma is_not_Punhide_sound a : is_not_Punhide a = true -> a <> Punhide.
Proof.
  intros H; destruct a; simpl in *; try discriminate; eauto.
Qed.

Lemma all_not_Punhide_sound ls : forallb is_not_Punhide ls = true -> Forall (fun a => a <> Punhide) ls.
Proof.
  intros H.
  eapply Forall_forall.
  intros x Hin.
  eapply forallb_forall in H; eauto.
  eapply is_not_Punhide_sound; eauto.
Qed.

Ltac not0_solver := solve [eapply QN_half_not_0 | eapply QN_2_not_0 | eapply QN_1_not_0 ].

Ltac leC_solver :=
  repeat
    match goal with
      | |- ?A <= ?A => reflexivity
      | |- F0 <= _ => eapply leC_0
      | |- Fmax _ _ <= _ => eapply leC_max_lub
      | |- ?S <= ?A + _ =>
        match A with
            context [ S ] => eapply leC_addta
        end
      | |- ?S <= _ + ?B =>
        match B with
            context [ S ] => eapply leC_addtb
        end
      | |- ?S <= Fmax ?A _ =>
        match A with
            context [ S ] => eapply leC_maxta
        end
      | |- ?S <= Fmax _ ?B =>
        match B with
            context [ S ] => eapply leC_maxtb
        end
      | |- F0 + _ <= _ => eapply leC_add0x'
      | |- F1 + _ <= _ *: Fvar _ _ => eapply leC_add1cx'; [not0_solver | .. ]
      | |- F1 + _ <= Fvar _ _ => eapply leC_add1x'
      | |- F1 <= _ *: Fvar _ _ => eapply leC_1_cx; [not0_solver | .. ]
      | |- _ + ?n <= _ + ?n => eapply leC_adda
      | |- ?n + _ <= ?n + _ => eapply leC_addb
      | |- Fvar (?x, _) ?i <= Fvar (?x, nil) ?i => eapply leC_path_subpath; eapply subpath_nil; try solve [ eassumption | eapply all_not_Punhide_sound; simpl; reflexivity ]
    end.

Local Open Scope G.

Lemma leS_var_addr x n0 n1 : Svar x <= Sstats (n0 + Fvar x 0%nat, n1 + Fvar x 1%nat).
Proof.
  simpl; unfold leS; simpl; split; eapply leC_add_b.
Qed.

Lemma leS_var_addl x n0 n1 : Svar x <= Sstats (Fvar x 0%nat + n0, Fvar x 1%nat + n1).
Proof.
  simpl; unfold leS; simpl; split; eapply leC_add_a.
Qed.

Lemma leS_stats s f0 f1 : 
  let ss := summarize s in 
  stats_get 0%nat ss <= f0 -> 
  stats_get 1%nat ss <= f1 -> 
  s <= Sstats (f0, f1).
Proof.
  simpl; intros H1 H2; unfold leS; simpl; eauto.
Qed.

Lemma leS_Spair a a' b b' : a <= a' -> b <= b' -> Spair a b <= Spair a' b'.
Proof.
  intros H1 H2; simpl in *; unfold leS in *; simpl in *; openhyp.
  destruct (summarize a); simpl in *.
  destruct (summarize b); simpl in *.
  destruct (summarize a'); simpl in *.
  destruct (summarize b'); simpl in *.
  split; eapply leC_add; eauto.
Qed.

Local Close Scope G.

Lemma leO_mula a b a' : a <<= a' -> a * b <<= a' * b.
Proof.
  intros H; eapply leO_mul; eauto; reflexivity.
Qed.

Lemma leO_mulb a b b' : b <<= b' -> a * b <<= a * b'.
Proof.
  intros H; eapply leO_mul; eauto; reflexivity.
Qed.

Lemma leO_adda a b a' : a <<= a' -> a + b <<= a' + b.
Proof.
  intros H; eapply leO_add; eauto; reflexivity.
Qed.

Lemma leO_addb a b b' : b <<= b' -> a + b <<= a + b'.
Proof.
  intros H; eapply leO_add; eauto; reflexivity.
Qed.

Lemma leO_0 n : 0 <<= n.
Proof.
  etransitivity.
  { eapply leO_leE; symmetry; eapply leE_mul0x. }
  etransitivity.
  { eapply leO_mula; eapply leO_01. }
  eapply leO_leE; eapply leE_mul1x.
Qed.

Lemma leO_add_b n m : n <<= m + n.
Proof.
  etransitivity.
  { eapply leO_leE; symmetry; eapply leE_add0x. }
  eapply leO_adda; eapply leO_0.
Qed.

Lemma leO_add_a n m : n <<= n + m.
Proof.
  etransitivity.
  { eapply leO_leE; symmetry; eapply leE_add0x. }
  etransitivity.
  { eapply leO_leE; eapply leE_addC. }
  eapply leO_addb; eapply leO_0.
Qed.

Lemma leO_addta a b a' : a <<= a' -> a <<= a' + b.
Proof.
  intros H; etransitivity; eauto; eapply leO_add_a.
Qed.

Lemma leO_addtb a b b' : b <<= b' -> b <<= a + b'.
Proof.
  intros H; etransitivity; eauto; eapply leO_add_b.
Qed.

Lemma leO_add_idem n : n + n <<= n.
Proof.
  etransitivity.
  { eapply leO_leE; eapply leE_addnn. }
  eapply leO_cn_n.
Qed.

Lemma leO_add_lub a b c : a <<= c -> b <<= c -> a + b <<= c.
Proof.
  intros H1 H2.
  etransitivity.
  { eapply leO_adda; eassumption. }
  etransitivity.
  { eapply leO_addb; eassumption. }
  eapply leO_add_idem.
Qed.

Lemma leO_max_b a b : b <<= Fmax a b.
Proof.
  etransitivity.
  { eapply leO_max_a. }
  eapply leO_leE; eapply leE_maxC.
Qed.

Lemma leO_max a b a' b' : a <<= a' -> b <<= b' -> Fmax a b <<= Fmax a' b'.
Proof.
  intros H1 H2.
  eapply leO_max_c.
  { etransitivity; eauto; eapply leO_max_a. }
  etransitivity; eauto; eapply leO_max_b.
Qed.

Lemma leO_maxa a b a' : a <<= a' -> Fmax a b <<= Fmax a' b.
Proof.
  intros H; eapply leO_max; eauto; reflexivity.
Qed.

Lemma leO_maxb a b b' : b <<= b' -> Fmax a b <<= Fmax a b'.
Proof.
  intros H; eapply leO_max; eauto; reflexivity.
Qed.

Lemma leO_maxta a b a' : a <<= a' -> a <<= Fmax a' b.
Proof.
  intros H; etransitivity; eauto; eapply leO_max_a.
Qed.

Lemma leO_maxtb a b b' : b <<= b' -> b <<= Fmax a b'.
Proof.
  intros H; etransitivity; eauto; eapply leO_max_b.
Qed.

Lemma leO_max_idem n : Fmax n n <<= n.
Proof.
  eapply leO_max_c; reflexivity.
Qed.

Lemma leO_max_lub a b c : a <<= c -> b <<= c -> Fmax a b <<= c.
Proof.
  intros H1 H2.
  etransitivity.
  { eapply leO_maxa; eassumption. }
  etransitivity.
  { eapply leO_maxb; eassumption. }
  eapply leO_max_idem.
Qed.

Ltac leO_solver :=
  repeat
    match goal with
      | |- ?A <<= ?A => reflexivity
      | |- F0 <<= _ => eapply leO_0
      | |- _ + _ <<= _ => eapply leO_add_lub
      | |- Fmax _ _ <<= _ => eapply leO_max_lub
      | |- ?S <<= ?A + _ =>
        match A with
            context [ S ] => eapply leO_addta
        end
      | |- ?S <<= _ + ?B =>
        match B with
            context [ S ] => eapply leO_addtb
        end
      | |- ?S <<= Fmax ?A _ =>
        match A with
            context [ S ] => eapply leO_maxta
        end
      | |- ?S <<= Fmax _ ?B =>
        match B with
            context [ S ] => eapply leO_maxtb
        end
    end.

Lemma leO_scaleb c n n' : n <<= n' -> c *: n <<= c *: n'.
Proof.
  intros H.
  eapply leO_scale; try reflexivity; eauto.
Qed.

Lemma leO_n_cn c n : (c != 0)%QN -> n <<= c *: n.
Proof.
  intros H.
  eapply QN_exists_inverse in H.
  destruct H as [c' H].
  etransitivity.
  {eapply leO_leE; symmetry; eapply leE_scale1x. }
  etransitivity.
  {eapply leO_leE; symmetry; eapply leE_scale; eauto; reflexivity. }
  etransitivity.
  {eapply leO_leE; symmetry; eapply leE_scaleA. }
  eapply leO_scaleb.
  eapply leO_cn_n.
Qed.

Lemma leO_1x_div2 x i : F1 <<= Fvar x i / 2%QN.
Proof.
  etransitivity.
  { eapply leO_n_cn; eapply QN_half_not_0. }
  eapply leO_scaleb.
  eapply leO_1x.
Qed.

Lemma leO_c_x (c : QN) x i : c <<= Fvar x i.
Proof.
  etransitivity.
  { unfold Fconst. eapply leO_cn_n. }
  eapply leO_1x.
Qed.

Lemma leO_1_log2x x i : F1 <<= log2 (Fvar x i).
Proof.
  etransitivity.
  { eapply leO_leE; symmetry; eapply leE_logcc; eapply QN_2_not_0. }
  eapply leO_log.
  eapply leO_c_x.
Qed.

Lemma leO_1_xlog2x x i x' i' : F1 <<= Fvar x i * log2 (Fvar x' i').
Proof.
  etransitivity.
  { eapply leO_leE; symmetry; eapply leE_mul1x. }
  eapply leO_mul.
  { eapply leO_1x. }
  eapply leO_1_log2x.
Qed.

Lemma leO_x_xlog2x x i : Fvar x i <<= Fvar x i * log2 (Fvar x i).
Proof.
  etransitivity.
  { eapply leO_leE; symmetry; eapply leE_mul1x. }
  etransitivity.
  { eapply leO_leE; eapply leE_mulC. }
  eapply leO_mul; try reflexivity.
  eapply leO_1_log2x.
Qed.

Lemma leO_cx_xlog2x c x i : c *: Fvar x i <<= Fvar x i * log2 (Fvar x i).
Proof.
  etransitivity.
  { eapply leO_cn_n. }
  eapply leO_x_xlog2x.
Qed.

Lemma leO_cxlog2cx_xlog2x c1 c2 x i : c1 *: Fvar x i * log2 (c2 *: Fvar x i) <<= Fvar x i * log2 (Fvar x i).
Proof.
  etransitivity.
  { eapply leO_leE; symmetry; eapply leE_scaleAl. }
  etransitivity.
  { eapply leO_cn_n. }
  eapply leO_mul; try reflexivity.
  eapply leO_log.
  eapply leO_cn_n.          
Qed.

Lemma leO_cons x p i a : a <> Punhide -> Fvar (x, a :: p) i <<= Fvar (x, p) i.
Proof.
  intros H.
  destruct a.
  { etransitivity.
    { eapply leO_add_a. }
    eapply leO_leE; eapply leE_pair.
  }
  { etransitivity.
    { eapply leO_add_b. }
    eapply leO_leE; eapply leE_pair.
  }
  { eapply leO_leE; eapply leE_inl. }
  { eapply leO_leE; eapply leE_inr. }
  { etransitivity.
    { eapply leO_add_b. }
    eapply leO_leE; eapply leE_unfold.
  }
  intuition.
Qed.

Lemma leO_path_subpath' x i p2 d : forall p1, d ++ p2 = p1 -> Forall (fun a => a <> Punhide) d -> Fvar (x, p1) i <<= Fvar (x, p2) i.
  induction d; intros p1 H Hall; simpl in *.
  {
    subst.
    reflexivity.
  }
  destruct p1 as [ | a' p1].
  { discriminate. }
  inject H.
  inversion Hall; subst.
  etransitivity.
  { eapply leO_cons; eauto. }
  eapply IHd; eauto.
Qed.

Lemma leO_path_subpath x i p1 p2 : subpath p2 p1 -> Fvar (x, p1) i <<= Fvar (x, p2) i.
  intros H.
  destruct H as [c [H1 H2] ].
  subst.
  eapply leO_path_subpath'; eauto.
Qed.

