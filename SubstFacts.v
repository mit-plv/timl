Require Import Omega.
Require Import GeneralTactics4.
Require Import Syntax Util.
Require Import Subst.
Export Subst.

Lemma fold_subst_s_t n v b : visit_t 0 (lower_t_f n, subst_sub n v, subst_sub n v) b = subst_size_type n v b.
Proof.
  eauto.
Qed.
Lemma fold_subst_t_t n v b : visit_t 0 (subst_t_t_f n v, lower_sub n, lower_sub n) b = subst_t_t n v b.
Proof.
  eauto.
Qed.
Lemma fold_shift_from_t n t : visit_t n (shift_t_f, shift_from, shift_from) t = shift_from_t n t.
Proof.
  eauto.
Qed.

Lemma fold_shift_from_f n t : visit_f (shift_f_f n) t = shift_from_f n t.
Proof.
  eauto.
Qed.

Lemma fold_shift_from_s n t : visit_s (shift_s_f n, shift_from_f n) t = shift_from_s n t.
Proof.
  eauto.
Qed.

Lemma fold_iter A n f (a : A) : iter n f (f a) = iter (S n) f a.
Proof.
  eauto.
Qed.

Lemma fold_subst_s_s n v b : visit_s (subst_s_s_f n v, substn n v) b = subst_size_size n v b.
Proof.
  eauto.
Qed.

Lemma fold_subst_s_f n s : visit_f (subst_s_f_f n s) = subst_size_cexpr n s.
Proof.
  eauto.
Qed.

Lemma shiftby_arrow n : forall m a tm s b, iter n (shift_from_t m) (Tarrow a tm s b) = Tarrow (iter n (shift_from m) a) (iter n (shift_from (S m)) tm) (iter n (shift_from (S m)) s) (iter n (shift_from (S m)) b).
Proof.
  induction n; simpl; intros; try rewrite IHn; eauto.
Qed.

Lemma shiftby_unit n : forall m, iter n (shift_from_t m) Tunit = Tunit.
Proof.
  induction n; simpl; intros; try rewrite IHn; eauto.
Qed.

Arguments subst_t_t n v b / .
Arguments subst_t_t_f n v nv nq / .
Arguments shiftby / .
Arguments shift_from_t n t / .

Lemma shiftby_var n : forall m x, iter n (shift_from_t m) (Tvar x) = Tvar (iter n (shift_nat m) x).
Proof.
  induction n; simpl; intros; try rewrite IHn; eauto.
Qed.

Lemma shiftby_universal n : forall m tm s x, iter n (shift_from_t m) (Tuniversal tm s x) = Tuniversal (iter n (shift_from (S m)) tm) (iter n (shift_from (S m)) s) (iter n (shift_from_t (S m)) x).
Proof.
  induction n; simpl; intros; try rewrite IHn; eauto.
Qed.

Lemma shiftby_abs n : forall m x, iter n (shift_from_t m) (Tabs x) = Tabs (iter n (shift_from_t (S m)) x).
Proof.
  induction n; simpl; intros; try rewrite IHn; eauto.
Qed.

Lemma shiftby_app n : forall m a b, iter n (shift_from_t m) (Tapp a b) = Tapp (iter n (shift_from m) a) (iter n (shift_from m) b).
Proof.
  induction n; simpl; intros; try rewrite IHn; eauto.
Qed.

Lemma shiftby_recur n : forall m x, iter n (shift_from_t m) (Trecur x) = Trecur (iter n (shift_from_t (S m)) x).
Proof.
  induction n; simpl; intros; try rewrite IHn; eauto.
Qed.

Lemma shiftby_hide n : forall m x, iter n (shift_from_t m) (Thide x) = Thide (iter n (shift_from_t m) x).
Proof.
  induction n; simpl; intros; try rewrite IHn; eauto.
Qed.

Arguments shift_nat n nv / .

Lemma shiftby_nat n : forall m x, iter n (shift_nat m) x = match nat_cmp x m with
                                                              | LT _ _ _ => x
                                                              | _ => n + x
                                                            end.
Proof.
  induction n; simpl; intros.
  {
    destruct (nat_cmp x m); eauto.
  }
  destruct (nat_cmp x m) as [ m' ? Hc | ? | x' ? Hc]; subst.
  {
    rewrite IHn.
    destruct (nat_cmp _ _); subst; simpl in *; eauto; omega.
  }
  {
    rewrite IHn.
    destruct (nat_cmp _ _); try subst; simpl in *; eauto; omega.
  }
  {
    rewrite IHn.
    destruct (nat_cmp _ _); subst; simpl in *; eauto; omega.
  }
Qed.

Lemma shiftby_0_f n : forall m, iter n (shift_from_f m) F0 = F0.
Proof.
  induction n; simpl; intros; try rewrite IHn; eauto.
Qed.

Lemma shiftby_add_f n : forall m x1 x2, iter n (shift_from_f m) (Fadd x1 x2) = Fadd (iter n (shift_from m) x1) (iter n (shift_from m) x2).
Proof.
  induction n; simpl; intros; try rewrite IHn; eauto.
Qed.

Lemma shiftby_1_f n : forall m, iter n (shift_from_f m) F1 = F1.
Proof.
  induction n; simpl; intros; try rewrite IHn; eauto.
Qed.

Lemma shiftby_mul_f n : forall m x1 x2, iter n (shift_from_f m) (Fmul x1 x2) = Fmul (iter n (shift_from m) x1) (iter n (shift_from m) x2).
Proof.
  induction n; simpl; intros; try rewrite IHn; eauto.
Qed.

Lemma shiftby_scale_f q n : forall m x, iter n (shift_from_f m) (Fscale q x) = Fscale q (iter n (shift_from m) x).
Proof.
  induction n; simpl; intros; try rewrite IHn; eauto.
Qed.

Lemma shiftby_max_f n : forall m x1 x2, iter n (shift_from_f m) (Fmax x1 x2) = Fmax (iter n (shift_from m) x1) (iter n (shift_from m) x2).
Proof.
  induction n; simpl; intros; try rewrite IHn; eauto.
Qed.

Lemma shiftby_log_f q n : forall m x, iter n (shift_from_f m) (Flog q x) = Flog q (iter n (shift_from m) x).
Proof.
  induction n; simpl; intros; try rewrite IHn; eauto.
Qed.

Lemma shiftby_exp_f q n : forall m x, iter n (shift_from_f m) (Fexp q x) = Fexp q (iter n (shift_from m) x).
Proof.
  induction n; simpl; intros; try rewrite IHn; eauto.
Qed.

Lemma shiftby_minus1_f n : forall m x, iter n (shift_from_f m) (Fminus1 x) = Fminus1 (iter n (shift_from m) x).
Proof.
  induction n; simpl; intros; try rewrite IHn; eauto.
Qed.

Lemma shiftby_var_f p i n : forall m x, iter n (shift_from_f m) (Fvar (x, p) i) = Fvar (iter n (shift_nat m) x, p) i.
Proof.
  induction n; simpl; intros; try rewrite IHn; eauto.
Qed.

Arguments shift_from_s n s / .
Arguments shift_from_f n f / .
Arguments map_stats / .
Arguments shift_t_f nv n / .
Arguments shift_f_f n nv path i / .

Arguments subst_size_type n v b / .
Arguments lower_t_f n nv nq / .

Arguments shift_s_f n nv path / .
Arguments subst_size_size n v b / .

Arguments shift_from_e n e / .

Arguments subst_s_f_f n v nv path i / .
Arguments query_idx idx s / .

Arguments subst_s_s_f n v nv path / .

Lemma subst_shift_s_f_n' v (x : cexpr) : forall (n m r : nat), m <= r -> (r <= n + m)%nat -> visit_f (subst_s_f_f r v) (iter (S n) (shift_from_f m) x) = iter n (shift_from_f m) x.
Proof.
  induction x; intros n m r Hle1 Hle2.
  {
    simpl.
    repeat rewrite shiftby_0_f.
    simpl.
    eauto.
  }
  {
    simpl.
    repeat rewrite shiftby_add_f.
    simpl.
    repeat rewrite fold_shift_from_f in *.
    repeat rewrite fold_iter.
    repeat f_equal.
    { rewrite IHx1; simpl in *; eauto; omega. }
    { rewrite IHx2; simpl in *; eauto; omega. }
  }
  {
    simpl.
    repeat rewrite shiftby_1_f.
    simpl.
    eauto.
  }
  {
    simpl.
    repeat rewrite shiftby_mul_f.
    simpl.
    repeat rewrite fold_shift_from_f in *.
    repeat rewrite fold_iter.
    repeat f_equal.
    { rewrite IHx1; simpl in *; eauto; omega. }
    { rewrite IHx2; simpl in *; eauto; omega. }
  }
  {
    simpl.
    repeat rewrite shiftby_scale_f.
    simpl.
    repeat rewrite fold_shift_from_f in *.
    repeat rewrite fold_iter.
    rewrite IHx; simpl in *; eauto; omega.
  }
  {
    simpl.
    repeat rewrite shiftby_max_f.
    simpl.
    repeat rewrite fold_shift_from_f in *.
    repeat rewrite fold_iter.
    repeat f_equal.
    { rewrite IHx1; simpl in *; eauto; omega. }
    { rewrite IHx2; simpl in *; eauto; omega. }
  }
  {
    simpl.
    repeat rewrite shiftby_log_f.
    simpl.
    repeat rewrite fold_shift_from_f in *.
    repeat rewrite fold_iter.
    rewrite IHx; simpl in *; eauto; omega.
  }
  {
    simpl.
    repeat rewrite shiftby_exp_f.
    simpl.
    repeat rewrite fold_shift_from_f in *.
    repeat rewrite fold_iter.
    rewrite IHx; simpl in *; eauto; omega.
  }
  {
    simpl.
    destruct x as [x p].
    repeat rewrite shiftby_var_f.
    repeat rewrite shiftby_nat.
    simpl.
    destruct (nat_cmp x m) as [ m' ? Hc | ? | x' ? Hc]; subst.
    {
      destruct (nat_cmp x (S m')); subst; destruct (nat_cmp _ _); subst; simpl in *; eauto; omega.
    }
    {
      destruct (nat_cmp (S m) m); try subst; destruct (nat_cmp _ _); try subst; simpl in *; eauto; try omega.
      rewrite <- plus_n_Sm in *.
      inject e0.
      eauto.
    }
    {
      destruct (nat_cmp (S (S x')) m); subst; destruct (nat_cmp _ _); subst; simpl in *; eauto; try omega.
      repeat rewrite <- plus_n_Sm in *.
      inject e0.
      eauto.
    }
  }
  {
    simpl.
    repeat rewrite shiftby_minus1_f.
    simpl.
    repeat rewrite fold_shift_from_f in *.
    repeat rewrite fold_iter.
    rewrite IHx; simpl in *; eauto; omega.
  }
Qed.

Lemma subst_shift_s_f v b : subst_size_cexpr 0 v (shift_from_f 0 b) = b.
Proof.
  fold (iter 1 (shift_from_f 0) b).
  eapply subst_shift_s_f_n'; simpl; eauto; try omega.
Qed.

Arguments lower_f n f / .
Arguments lower_f_f n nv path i / .

Lemma lower_iter_shift_f x : forall (n m r : nat), m <= r -> (r <= n + m)%nat -> visit_f (lower_f_f r) (iter (S n) (shift_from_f m) x) = iter n (shift_from_f m) x.
Proof.
  induction x; intros n m r Hle1 Hle2.
  {
    simpl.
    repeat rewrite shiftby_0_f.
    simpl.
    eauto.
  }
  {
    simpl.
    repeat rewrite shiftby_add_f.
    simpl.
    repeat rewrite fold_shift_from_f in *.
    repeat rewrite fold_iter.
    repeat f_equal.
    { rewrite IHx1; simpl in *; eauto; omega. }
    { rewrite IHx2; simpl in *; eauto; omega. }
  }
  {
    simpl.
    repeat rewrite shiftby_1_f.
    simpl.
    eauto.
  }
  {
    simpl.
    repeat rewrite shiftby_mul_f.
    simpl.
    repeat rewrite fold_shift_from_f in *.
    repeat rewrite fold_iter.
    repeat f_equal.
    { rewrite IHx1; simpl in *; eauto; omega. }
    { rewrite IHx2; simpl in *; eauto; omega. }
  }
  {
    simpl.
    repeat rewrite shiftby_scale_f.
    simpl.
    repeat rewrite fold_shift_from_f in *.
    repeat rewrite fold_iter.
    rewrite IHx; simpl in *; eauto; omega.
  }
  {
    simpl.
    repeat rewrite shiftby_max_f.
    simpl.
    repeat rewrite fold_shift_from_f in *.
    repeat rewrite fold_iter.
    repeat f_equal.
    { rewrite IHx1; simpl in *; eauto; omega. }
    { rewrite IHx2; simpl in *; eauto; omega. }
  }
  {
    simpl.
    repeat rewrite shiftby_log_f.
    simpl.
    repeat rewrite fold_shift_from_f in *.
    repeat rewrite fold_iter.
    rewrite IHx; simpl in *; eauto; omega.
  }
  {
    simpl.
    repeat rewrite shiftby_exp_f.
    simpl.
    repeat rewrite fold_shift_from_f in *.
    repeat rewrite fold_iter.
    rewrite IHx; simpl in *; eauto; omega.
  }
  {
    simpl.
    destruct x as [x p].
    repeat rewrite shiftby_var_f.
    repeat rewrite shiftby_nat.
    simpl.
    destruct (nat_cmp x m) as [ m' ? Hc | ? | x' ? Hc]; subst.
    {
      destruct (nat_cmp x (S m')); subst; destruct (nat_cmp _ _); subst; simpl in *; eauto; omega.
    }
    {
      destruct (nat_cmp (S m) m); try subst; destruct (nat_cmp _ _); try subst; simpl in *; eauto; try omega.
      rewrite <- plus_n_Sm in *.
      inject e0.
      eauto.
    }
    {
      destruct (nat_cmp (S (S x')) m); subst; destruct (nat_cmp _ _); subst; simpl in *; eauto; try omega.
      repeat rewrite <- plus_n_Sm in *.
      inject e0.
      eauto.
    }
  }
  {
    simpl.
    repeat rewrite shiftby_minus1_f.
    simpl.
    repeat rewrite fold_shift_from_f in *.
    repeat rewrite fold_iter.
    rewrite IHx; simpl in *; eauto; omega.
  }
Qed.

Lemma shift_summarize v : forall n, summarize (visit_s (shift_s_f n, shift_from_f n) v) = let (a, b) := summarize v in (visit_f (shift_f_f n) a, visit_f (shift_f_f n) b).
Proof.
  induction v; intros n; try solve [ simpl; eauto ].
  { 
    destruct x as [x p].
    simpl.
    eauto.
  }
  {
    simpl.
    unfold stats_max.
    unfold stats_binop.
    rewrite IHv1.
    rewrite IHv2.
    destruct (summarize v1).
    destruct (summarize v2).
    simpl.
    eauto.
  }
  {
    simpl.
    unfold stats_add.
    unfold stats_binop.
    rewrite IHv1.
    rewrite IHv2.
    destruct (summarize v1).
    destruct (summarize v2).
    simpl.
    eauto.
  }
  {
    simpl.
    rewrite IHv.
    destruct (summarize v).
    simpl.
    eauto.
  }
Qed.

Arguments apply_arrow / . 

Lemma shift_query_cmd v : forall n c, query_cmd c (visit_s (shift_s_f n, shift_from_f n) v) = visit_s (shift_s_f n, shift_from_f n) (query_cmd c v).
Proof.
  induction v; destruct c; try solve [simpl; eauto | simpl; destruct x; simpl; eauto].
  destruct s as [w s]; simpl; eauto.
Qed.

Lemma shift_query' p : forall v n i, (let s := query_path' p (visit_s (shift_s_f n, shift_from_f n) v) in query_idx i s) = visit_f (shift_f_f n) (let s := query_path' p v in query_idx i s).
Proof.
  induction p.
  {
    simpl.
    intros v n.
    rewrite shift_summarize.
    destruct (summarize v).
    destruct i; simpl; eauto.
  }
  simpl in *.
  intros v n i.
  rewrite shift_query_cmd.
  simpl; eauto.
Qed.

Lemma shift_query v : forall p i n, query_path_idx p i (visit_s (shift_s_f n, shift_from_f n) v) = visit_f (shift_f_f n) (query_path_idx p i v).
Proof.
  intros; eapply shift_query'.
Qed.

Arguments subst_size_cexpr n v b / .

Lemma subst_shift_from_s_f x : forall v n m, (m <= n)%nat -> subst_size_cexpr m (shift_from_s n v) (shift_from_f (S n) x) = shift_from_f n (subst_size_cexpr m v x).
Proof.
  induction x; intros v n m Hle; try solve [simpl; f_equal; eauto ].
  destruct x as [x p].
  simpl.
  destruct (nat_cmp x (S n)); subst.
  {
    destruct (nat_cmp x m); subst; simpl in *. 
    {
      destruct (nat_cmp x n); subst; simpl in *; eauto; omega.
    }
    {
      eapply shift_query.
    }
    {
      destruct (nat_cmp _ _); subst; simpl in *; eauto; omega.
    }
  }
  {
    destruct (nat_cmp (S (S n)) m); try subst; destruct (nat_cmp _ _); try subst; simpl in *; eauto; try omega.
    inject e0.
    inject e.
    destruct (nat_cmp _ _); subst; simpl in *; eauto; omega.
  }
  {
    destruct (nat_cmp (S (S m')) m); try subst; destruct (nat_cmp _ _); try subst; simpl in *; eauto; try omega.
    inject e0.
    inject e.
    destruct (nat_cmp _ _); subst; simpl in *; eauto; omega.
  }
Qed.

Lemma shiftby_var_s n : forall m x p, iter n (shift_from_s m) (Svar (x, p)) = Svar (iter n (shift_nat m) x, p).
Proof.
  induction n; simpl; intros; try rewrite IHn; eauto.
Qed.

Lemma shiftby_stats_s n : forall m n1 n2, iter n (shift_from_s m) (Sstats (n1, n2)) = Sstats (iter n (shift_from m) n1, iter n (shift_from m) n2).
Proof.
  induction n; simpl; intros; try rewrite IHn; eauto.
Qed.

Lemma shiftby_inlinr_s n : forall m x1 x2, iter n (shift_from_s m) (Sinlinr x1 x2) = Sinlinr (iter n (shift_from m) x1) (iter n (shift_from m) x2).
Proof.
  induction n; simpl; intros; try rewrite IHn; eauto.
Qed.

Lemma shiftby_pair_s n : forall m x1 x2, iter n (shift_from_s m) (Spair x1 x2) = Spair (iter n (shift_from m) x1) (iter n (shift_from m) x2).
Proof.
  induction n; simpl; intros; try rewrite IHn; eauto.
Qed.

Lemma shiftby_fold_s n : forall m x, iter n (shift_from_s m) (Sfold x) = Sfold (iter n (shift_from m) x).
Proof.
  induction n; simpl; intros; try rewrite IHn; eauto.
Qed.

Lemma shiftby_hide_s n : forall m x, iter n (shift_from_s m) (Shide x) = Shide (iter n (shift_from m) x).
Proof.
  induction n; simpl; intros; try rewrite IHn; eauto.
Qed.

Lemma subst_shift_s_s_n' v (x : size) : forall (n m r : nat), m <= r -> (r <= n + m)%nat -> visit_s (subst_s_s_f r v, substn r v) (iter (S n) (shift_from_s m) x) = iter n (shift_from_s m) x.
Proof.
  induction x; intros n m r Hle1 Hle2.
  {
    simpl.
    destruct x as [x p].
    repeat rewrite shiftby_var_s.
    repeat rewrite shiftby_nat.
    simpl.
    destruct (nat_cmp x m) as [ m' ? Hc | ? | x' ? Hc]; subst.
    {
      destruct (nat_cmp x (S m')); subst; destruct (nat_cmp _ _); subst; simpl in *; eauto; omega.
    }
    {
      destruct (nat_cmp (S m) m); try subst; destruct (nat_cmp _ _); try subst; simpl in *; eauto; try omega.
      rewrite <- plus_n_Sm in *.
      inject e0.
      eauto.
    }
    {
      destruct (nat_cmp (S (S x')) m); subst; destruct (nat_cmp _ _); subst; simpl in *; eauto; try omega.
      repeat rewrite <- plus_n_Sm in *.
      inject e0.
      eauto.
    }
  }
  {
    destruct s as [n1 n2].
    simpl.
    repeat rewrite shiftby_stats_s.
    simpl.
    repeat f_equal; repeat rewrite fold_iter; eapply subst_shift_s_f_n'; simpl in *; eauto; omega.
  }
  {
    simpl.
    repeat rewrite shiftby_inlinr_s.
    simpl.
    repeat rewrite fold_shift_from_s in *.
    repeat rewrite fold_iter.
    repeat f_equal.
    { rewrite IHx1; simpl in *; eauto; omega. }
    { rewrite IHx2; simpl in *; eauto; omega. }
  }
  {
    simpl.
    repeat rewrite shiftby_pair_s.
    simpl.
    repeat rewrite fold_shift_from_s in *.
    repeat rewrite fold_iter.
    repeat f_equal.
    { rewrite IHx1; simpl in *; eauto; omega. }
    { rewrite IHx2; simpl in *; eauto; omega. }
  }
  {
    simpl.
    repeat rewrite shiftby_fold_s.
    simpl.
    repeat rewrite fold_shift_from_s in *.
    repeat rewrite fold_iter.
    rewrite IHx; simpl in *; eauto; omega.
  }
  {
    simpl.
    repeat rewrite shiftby_hide_s.
    simpl.
    repeat rewrite fold_shift_from_s in *.
    repeat rewrite fold_iter.
    rewrite IHx; simpl in *; eauto; omega.
  }
Qed.

Lemma subst_shift_s_s_n n v b : subst_size_size n v (iter (S n) (shift_from_s 0) b) = iter n (shift_from_s 0) b.
Proof.
  intros; eapply subst_shift_s_s_n'; simpl in *; eauto; omega.
Qed.

Lemma subst_shift_s_s v b : subst_size_size 0 v (shift_from_s 0 b) = b.
Proof.
  fold (iter 1 (shift_from_s 0) b).
  repeat rewrite subst_shift_s_s_n in *.
  simpl.
  eauto.
Qed.

Arguments lower_s n s / .
Arguments lower_s_f n nv path / .

Lemma lower_iter_shift_s x : forall (n m r : nat), m <= r -> (r <= n + m)%nat -> visit_s (lower_s_f r, lower r) (iter (S n) (shift_from_s m) x) = iter n (shift_from_s m) x.
Proof.
  induction x; intros n m r Hle1 Hle2.
  {
    simpl.
    destruct x as [x p].
    repeat rewrite shiftby_var_s.
    repeat rewrite shiftby_nat.
    simpl.
    destruct (nat_cmp x m) as [ m' ? Hc | ? | x' ? Hc]; subst.
    {
      destruct (nat_cmp x (S m')); subst; destruct (nat_cmp _ _); subst; simpl in *; eauto; omega.
    }
    {
      destruct (nat_cmp (S m) m); try subst; destruct (nat_cmp _ _); try subst; simpl in *; eauto; try omega.
      rewrite <- plus_n_Sm in *.
      inject e0.
      eauto.
    }
    {
      destruct (nat_cmp (S (S x')) m); subst; destruct (nat_cmp _ _); subst; simpl in *; eauto; try omega.
      repeat rewrite <- plus_n_Sm in *.
      inject e0.
      eauto.
    }
  }
  {
    destruct s as [n1 n2].
    simpl.
    repeat rewrite shiftby_stats_s.
    simpl.
    repeat f_equal; repeat rewrite fold_iter; eapply lower_iter_shift_f; simpl in *; eauto; omega.
  }
  {
    simpl.
    repeat rewrite shiftby_inlinr_s.
    simpl.
    repeat rewrite fold_shift_from_s in *.
    repeat rewrite fold_iter.
    repeat f_equal.
    { rewrite IHx1; simpl in *; eauto; omega. }
    { rewrite IHx2; simpl in *; eauto; omega. }
  }
  {
    simpl.
    repeat rewrite shiftby_pair_s.
    simpl.
    repeat rewrite fold_shift_from_s in *.
    repeat rewrite fold_iter.
    repeat f_equal.
    { rewrite IHx1; simpl in *; eauto; omega. }
    { rewrite IHx2; simpl in *; eauto; omega. }
  }
  {
    simpl.
    repeat rewrite shiftby_fold_s.
    simpl.
    repeat rewrite fold_shift_from_s in *.
    repeat rewrite fold_iter.
    rewrite IHx; simpl in *; eauto; omega.
  }
  {
    simpl.
    repeat rewrite shiftby_hide_s.
    simpl.
    repeat rewrite fold_shift_from_s in *.
    repeat rewrite fold_iter.
    rewrite IHx; simpl in *; eauto; omega.
  }
Qed.

Lemma subst_shift_t_t_n_var v (x : var) (n m r : nat) : m <= r -> (r <= n + m)%nat -> visit_t r (subst_t_t_f 0 v, lower_sub 0, lower_sub 0) (iter (S n) (shift_from_t m) x) = iter n (shift_from_t m) x.
Proof.
  intros Hle1 Hle2.
  simpl.
  repeat rewrite shiftby_var.
  repeat rewrite shiftby_nat.
  simpl.
  destruct (nat_cmp x m) as [ m' ? Hc | ? | x' ? Hc]; subst.
  {
    destruct (nat_cmp x (S m')); subst; destruct (nat_cmp _ _); subst; simpl in *; eauto; omega.
  }
  {
    destruct (nat_cmp (S m) m); try subst; destruct (nat_cmp _ _); try subst; simpl in *; eauto; try omega.
    rewrite <- plus_n_Sm in *.
    inject e0.
    eauto.
  }
  {
    destruct (nat_cmp (S (S x')) m); subst; destruct (nat_cmp _ _); subst; simpl in *; eauto; try omega.
    rewrite <- plus_n_Sm in *.
    inject e0.
    eauto.
  }
Qed.

Lemma subst_shift_t_t_n' v (x : type) : forall (n m r : nat), m <= r -> (r <= n + m)%nat -> visit_t r (subst_t_t_f 0 v, lower_sub 0, lower_sub 0) (iter (S n) (shift_from_t m) x) = iter n (shift_from_t m) x.
Proof.
  induction x; intros n m r Hle1 Hle2.
  {
    simpl.
    repeat rewrite shiftby_arrow.
    simpl.
    f_equal.
    {
      repeat rewrite fold_shift_from_t in *.
      rewrite fold_iter.
      rewrite IHx1; eauto.
    }
    {
      repeat rewrite fold_shift_from_f in *.
      rewrite fold_iter.
      eapply lower_iter_shift_f; simpl in *; eauto; omega.
    }
    {
      repeat rewrite fold_shift_from_s in *.
      rewrite fold_iter.
      eapply lower_iter_shift_s; simpl in *; eauto; omega.
    }
    {
      repeat rewrite fold_shift_from_t in *.
      rewrite fold_iter.
      rewrite IHx2; simpl in *; eauto; omega.
    }
  }
  {
    eapply subst_shift_t_t_n_var; eauto.
  }
  {
    simpl.
    repeat rewrite shiftby_universal.
    simpl.
    f_equal.
    {
      repeat rewrite fold_shift_from_f in *.
      rewrite fold_iter.
      eapply lower_iter_shift_f; simpl in *; eauto; omega.
    }
    {
      repeat rewrite fold_shift_from_s in *.
      rewrite fold_iter.
      eapply lower_iter_shift_s; simpl in *; eauto; omega.
    }
    {
      repeat rewrite fold_shift_from_t in *.
      rewrite fold_iter.
      rewrite IHx; simpl in *; eauto; omega.
    }
  }
  {
    simpl.
    repeat rewrite shiftby_abs.
    simpl.
    repeat rewrite fold_shift_from_t in *.
    rewrite fold_iter.
    rewrite IHx; simpl in *; eauto; omega.
  }
  {
    simpl.
    repeat rewrite shiftby_app.
    simpl.
    f_equal.
    {
      repeat rewrite fold_shift_from_t in *.
      rewrite fold_iter.
      rewrite IHx1; eauto.
    }
    {
      repeat rewrite fold_shift_from_t in *.
      rewrite fold_iter.
      rewrite IHx2; simpl in *; eauto; omega.
    }
  }
  {
    simpl.
    repeat rewrite shiftby_recur.
    simpl.
    repeat rewrite fold_shift_from_t in *.
    rewrite fold_iter.
    rewrite IHx; simpl in *; eauto; omega.
  }
  {
    simpl.
    repeat rewrite shiftby_hide.
    simpl.
    repeat rewrite fold_shift_from_t in *.
    rewrite fold_iter.
    rewrite IHx; simpl in *; eauto; omega.
  }
  {
    simpl.
    repeat rewrite shiftby_unit.
    simpl.
    eauto.
  }
  admit. (* prod *)
  admit. (* sum *)
Qed.

Lemma subst_shift_t_t_n (b : type) : forall n v, visit_t n (subst_t_t_f 0 v, lower_sub 0, lower_sub 0) (iter (S n) (shift_from_t 0) b) = iter n (shift_from_t 0) b.
Proof.
  intros.
  eapply subst_shift_t_t_n'; simpl in *; eauto; omega.
Qed.

Lemma subst_shift_t_t v (b : type) : subst_t_t 0 v (shift_from_t 0 b) = b.
Proof.
  simpl.
  repeat rewrite fold_shift_from_t in *.
  fold (iter 1 (shift_from_t 0) b).
  repeat rewrite subst_shift_t_t_n in *.
  simpl.
  eauto.
Qed.

Lemma subst_shift_s_t_n_var v (x : var) (n m r : nat) : m <= r -> (r <= n + m)%nat -> visit_t r (lower_t_f 0, subst_sub 0 v, subst_sub 0 v) (iter (S n) (shift_from_t m) x) = iter n (shift_from_t m) x.
Proof.
  intros Hle1 Hle2.
  simpl.
  repeat rewrite shiftby_var.
  repeat rewrite shiftby_nat.
  simpl.
  destruct (nat_cmp x m) as [ m' ? Hc | ? | x' ? Hc]; subst.
  {
    destruct (nat_cmp x (S m')); subst; destruct (nat_cmp _ _); subst; simpl in *; eauto; omega.
  }
  {
    destruct (nat_cmp (S m) m); try subst; destruct (nat_cmp _ _); try subst; simpl in *; eauto; try omega.
    rewrite <- plus_n_Sm in *.
    inject e0.
    eauto.
  }
  {
    destruct (nat_cmp (S (S x')) m); subst; destruct (nat_cmp _ _); subst; simpl in *; eauto; try omega.
    rewrite <- plus_n_Sm in *.
    inject e0.
    eauto.
  }
Qed.

Lemma subst_shift_s_t_n' v (x : type) : forall (n m r : nat), m <= r -> (r <= n + m)%nat -> visit_t r (lower_t_f 0, subst_sub 0 v, subst_sub 0 v) (iter (S n) (shift_from_t m) x) = iter n (shift_from_t m) x.
Proof.
  induction x; intros n m r Hle1 Hle2.
  {
    simpl.
    repeat rewrite shiftby_arrow.
    simpl.
    f_equal.
    {
      repeat rewrite fold_shift_from_t in *.
      rewrite fold_iter.
      rewrite IHx1; eauto.
    }
    {
      repeat rewrite fold_shift_from_f in *.
      repeat rewrite fold_iter.
      eapply subst_shift_s_f_n'; simpl in *; eauto; omega.
    }
    {
      repeat rewrite fold_shift_from_s in *.
      repeat rewrite fold_iter.
      eapply subst_shift_s_s_n'; simpl in *; eauto; omega.
    }
    {
      repeat rewrite fold_shift_from_t in *.
      rewrite fold_iter.
      rewrite IHx2; simpl in *; eauto; omega.
    }
  }
  {
    eapply subst_shift_s_t_n_var; eauto.
  }
  {
    simpl.
    repeat rewrite shiftby_universal.
    simpl.
    f_equal.
    {
      repeat rewrite fold_shift_from_f in *.
      repeat rewrite fold_iter.
      eapply subst_shift_s_f_n'; simpl in *; eauto; omega.
    }
    {
      repeat rewrite fold_shift_from_s in *.
      repeat rewrite fold_iter.
      eapply subst_shift_s_s_n'; simpl in *; eauto; omega.
    }
    {
      repeat rewrite fold_shift_from_t in *.
      rewrite fold_iter.
      rewrite IHx; simpl in *; eauto; omega.
    }
  }
  {
    simpl.
    repeat rewrite shiftby_abs.
    simpl.
    repeat rewrite fold_shift_from_t in *.
    rewrite fold_iter.
    rewrite IHx; simpl in *; eauto; omega.
  }
  {
    simpl.
    repeat rewrite shiftby_app.
    simpl.
    f_equal.
    {
      repeat rewrite fold_shift_from_t in *.
      rewrite fold_iter.
      rewrite IHx1; eauto.
    }
    {
      repeat rewrite fold_shift_from_t in *.
      rewrite fold_iter.
      rewrite IHx2; simpl in *; eauto; omega.
    }
  }
  {
    simpl.
    repeat rewrite shiftby_recur.
    simpl.
    repeat rewrite fold_shift_from_t in *.
    rewrite fold_iter.
    rewrite IHx; simpl in *; eauto; omega.
  }
  {
    simpl.
    repeat rewrite shiftby_hide.
    simpl.
    repeat rewrite fold_shift_from_t in *.
    rewrite fold_iter.
    rewrite IHx; simpl in *; eauto; omega.
  }
  {
    simpl.
    repeat rewrite shiftby_unit.
    simpl.
    eauto.
  }
  admit. (* prod *)
  admit. (* sum *)
Qed.

Lemma subst_shift_s_t_n v (x : type) : forall n, visit_t n (lower_t_f 0, subst_sub 0 v, subst_sub 0 v) (iter (S n) (shift_from_t 0) x) = iter n (shift_from_t 0) x.
Proof.
  intros.
  eapply subst_shift_s_t_n'; simpl in *; eauto; omega.
Qed.

Lemma iter_comm A f n : forall (a : A), f (iter n f a) = iter n f (f a).
Proof.
  induction n; simpl; intuition.
Qed.

Lemma combine_iter A f n1 : forall n2 (a : A), iter n1 f (iter n2 f a) = iter (n1 + n2) f a.
Proof.
  induction n1; simpl; intuition.
  rewrite <- IHn1.
  simpl.
  f_equal.
  eapply iter_comm.
Qed.

Lemma subst_s_t_equiv' v x : forall n n', visit_t n' (lower_t_f n, subst_sub n (shiftby n v), subst_sub n (shiftby n v)) x = visit_t (n' + n) (lower_t_f 0, subst_sub 0 v, subst_sub 0 v) x.
Proof.
  induction x; intros n n'.
  {
    simpl.
    f_equal.
    { eapply IHx1. }
    { 
      repeat rewrite fold_shift_from_s in *.
      repeat rewrite fold_iter.
      repeat rewrite combine_iter.
      repeat rewrite <- plus_n_Sm in *.
      rewrite (plus_comm n n').
      eauto.
    }
    { 
      repeat rewrite fold_shift_from_s in *.
      repeat rewrite fold_iter.
      repeat rewrite combine_iter.
      repeat rewrite <- plus_n_Sm in *.
      rewrite (plus_comm n n').
      eauto.
    }
    { eapply IHx2. }
  }
  { simpl; rewrite (plus_comm n n'); eauto. }
  { simpl.
    f_equal.
    { 
      repeat rewrite fold_shift_from_s in *.
      repeat rewrite fold_iter.
      repeat rewrite combine_iter.
      repeat rewrite <- plus_n_Sm in *.
      rewrite (plus_comm n n').
      eauto.
    }
    { 
      repeat rewrite fold_shift_from_s in *.
      repeat rewrite fold_iter.
      repeat rewrite combine_iter.
      repeat rewrite <- plus_n_Sm in *.
      rewrite (plus_comm n n').
      eauto.
    }
    { eapply IHx. }
  }
  { simpl.
    f_equal.
    eapply IHx.
  }
  { simpl.
    f_equal.
    { eapply IHx1. }
    { eapply IHx2. }
  }
  { simpl.
    f_equal.
    eapply IHx.
  }
  { simpl.
    f_equal.
    eapply IHx.
  }
  { simpl; eauto. }
  admit. (* prod *)
  admit. (* sum *)
Qed.

Lemma subst_s_t_equiv v x n : visit_t 0 (lower_t_f n, subst_sub n (iter n (shift_from_s 0) v), subst_sub n (iter n (shift_from_s 0) v)) x = visit_t n (lower_t_f 0, subst_sub 0 v, subst_sub 0 v) x.
Proof.
  eapply subst_s_t_equiv'; eauto.
Qed.

Lemma subst_shift_s_t_n2 v (x : type) n : subst_size_type n (iter n (shift_from_s 0) v) (iter (S n) (shift_from_t 0) x) = iter n (shift_from_t 0) x.
Proof.
  unfold subst_size_type.
  simpl.
  rewrite subst_s_t_equiv.
  repeat rewrite fold_shift_from_t in *.
  repeat rewrite fold_iter.
  eapply subst_shift_s_t_n.
Qed.

Lemma subst_shift_s_t v (b : type) : subst_size_type 0 v (shift_from_t 0 b) = b.
Proof.
  simpl.
  repeat rewrite fold_shift_from_t in *.
  fold (iter 1 (shift_from_t 0) b).
  repeat rewrite subst_shift_s_t_n in *.
  simpl.
  eauto.
Qed.

Lemma shift_from_shiftby_f_n x : forall n m m', m' = m + n -> shift_from_f m' (iter n (shift_from_f m) x) = iter (S n) (shift_from_f m) x.
Proof.
  induction x; intros n m ? ?; subst.
  {
    simpl.
    repeat rewrite shiftby_0_f.
    simpl.
    eauto.
  }
  {
    simpl.
    repeat rewrite shiftby_add_f.
    simpl.
    repeat rewrite fold_shift_from_f in *.
    repeat rewrite fold_iter.
    repeat f_equal.
    { rewrite IHx1; simpl in *; eauto; omega. }
    { rewrite IHx2; simpl in *; eauto; omega. }
  }
  {
    simpl.
    repeat rewrite shiftby_1_f.
    simpl.
    eauto.
  }
  {
    simpl.
    repeat rewrite shiftby_mul_f.
    simpl.
    repeat rewrite fold_shift_from_f in *.
    repeat rewrite fold_iter.
    repeat f_equal.
    { rewrite IHx1; simpl in *; eauto; omega. }
    { rewrite IHx2; simpl in *; eauto; omega. }
  }
  {
    simpl.
    repeat rewrite shiftby_scale_f.
    simpl.
    repeat rewrite fold_shift_from_f in *.
    repeat rewrite fold_iter.
    rewrite IHx; simpl in *; eauto; omega.
  }
  {
    simpl.
    repeat rewrite shiftby_max_f.
    simpl.
    repeat rewrite fold_shift_from_f in *.
    repeat rewrite fold_iter.
    repeat f_equal.
    { rewrite IHx1; simpl in *; eauto; omega. }
    { rewrite IHx2; simpl in *; eauto; omega. }
  }
  {
    simpl.
    repeat rewrite shiftby_log_f.
    simpl.
    repeat rewrite fold_shift_from_f in *.
    repeat rewrite fold_iter.
    rewrite IHx; simpl in *; eauto; omega.
  }
  {
    simpl.
    repeat rewrite shiftby_exp_f.
    simpl.
    repeat rewrite fold_shift_from_f in *.
    repeat rewrite fold_iter.
    rewrite IHx; simpl in *; eauto; omega.
  }
  {
    simpl.
    destruct x as [x p].
    repeat rewrite shiftby_var_f.
    repeat rewrite shiftby_nat.
    simpl.
    destruct (nat_cmp x m) as [ m' ? Hc | ? | x' ? Hc]; subst; try omega.
    {
      destruct (nat_cmp _ (_ + _)); subst; destruct (nat_cmp _ _); subst; simpl in *; eauto; omega.
    }
    {
      destruct (nat_cmp _ (_ + _)); try subst; destruct (nat_cmp _ _); try subst; simpl in *; eauto; try omega.
      repeat rewrite <- plus_n_Sm in *.
      eauto.
    }
    {
      destruct (nat_cmp _ (_ + _)); try subst; destruct (nat_cmp _ _); try subst; simpl in *; eauto; try omega.
      repeat rewrite <- plus_n_Sm in *.
      eauto.
    }
  }
  {
    simpl.
    repeat rewrite shiftby_minus1_f.
    simpl.
    repeat rewrite fold_shift_from_f in *.
    repeat rewrite fold_iter.
    rewrite IHx; simpl in *; eauto; omega.
  }
Qed.

Lemma shift_from_shiftby_f n x : shift_from_f n (iter n (shift_from_f 0) x) = iter (S n) (shift_from_f 0) x.
Proof.
  intros; eapply shift_from_shiftby_f_n; simpl; eauto.
Qed.

Lemma shift_from_shiftby_s_n x : forall n m m', m' = m + n -> shift_from_s m' (iter n (shift_from_s m) x) = iter (S n) (shift_from_s m) x.
Proof.
  induction x; intros n m ? ?; subst.
  {
    simpl.
    destruct x as [x p].
    repeat rewrite shiftby_var_s.
    repeat rewrite shiftby_nat.
    simpl.
    destruct (nat_cmp x m) as [ m' ? Hc | ? | x' ? Hc]; subst; try omega.
    {
      destruct (nat_cmp _ (_ + _)); subst; destruct (nat_cmp _ _); subst; simpl in *; eauto; omega.
    }
    {
      destruct (nat_cmp _ (_ + _)); try subst; destruct (nat_cmp _ _); try subst; simpl in *; eauto; try omega.
      repeat rewrite <- plus_n_Sm in *.
      eauto.
    }
    {
      destruct (nat_cmp _ (_ + _)); try subst; destruct (nat_cmp _ _); try subst; simpl in *; eauto; try omega.
      repeat rewrite <- plus_n_Sm in *.
      eauto.
    }
  }
  {
    destruct s as [n1 n2].
    simpl.
    repeat rewrite shiftby_stats_s.
    simpl.
    repeat f_equal; repeat rewrite fold_iter; eapply shift_from_shiftby_f_n; simpl in *; eauto; omega.
  }
  {
    simpl.
    repeat rewrite shiftby_inlinr_s.
    simpl.
    repeat rewrite fold_shift_from_s in *.
    repeat rewrite fold_iter.
    repeat f_equal.
    { rewrite IHx1; simpl in *; eauto; omega. }
    { rewrite IHx2; simpl in *; eauto; omega. }
  }
  {
    simpl.
    repeat rewrite shiftby_pair_s.
    simpl.
    repeat rewrite fold_shift_from_s in *.
    repeat rewrite fold_iter.
    repeat f_equal.
    { rewrite IHx1; simpl in *; eauto; omega. }
    { rewrite IHx2; simpl in *; eauto; omega. }
  }
  {
    simpl.
    repeat rewrite shiftby_fold_s.
    simpl.
    repeat rewrite fold_shift_from_s in *.
    repeat rewrite fold_iter.
    rewrite IHx; simpl in *; eauto; omega.
  }
  {
    simpl.
    repeat rewrite shiftby_hide_s.
    simpl.
    repeat rewrite fold_shift_from_s in *.
    repeat rewrite fold_iter.
    rewrite IHx; simpl in *; eauto; omega.
  }
Qed.

Lemma shift_from_shiftby_s n x : shift_from_s n (iter n (shift_from_s 0) x) = iter (S n) (shift_from_s 0) x.
Proof.
  intros; eapply shift_from_shiftby_s_n; simpl; eauto.
Qed.

Lemma shift_from_shiftby_t_n x : forall n m m', m' = m + n -> shift_from_t m' (iter n (shift_from_t m) x) = iter (S n) (shift_from_t m) x.
Proof.
  induction x; intros n m ? ?; subst.
  {
    simpl.
    repeat rewrite shiftby_arrow.
    simpl.
    f_equal.
    {
      repeat rewrite fold_shift_from_t in *.
      rewrite fold_iter.
      rewrite IHx1; eauto.
    }
    {
      repeat rewrite fold_shift_from_f in *.
      repeat rewrite fold_iter.
      eapply shift_from_shiftby_f_n; simpl in *; eauto; omega.
    }
    {
      repeat rewrite fold_shift_from_s in *.
      repeat rewrite fold_iter.
      eapply shift_from_shiftby_s_n; simpl in *; eauto; omega.
    }
    {
      repeat rewrite fold_shift_from_t in *.
      rewrite fold_iter.
      rewrite IHx2; simpl in *; eauto; omega.
    }
  }
  {
    simpl.
    repeat rewrite shiftby_var.
    repeat rewrite shiftby_nat.
    simpl.
    destruct (nat_cmp x m) as [ m' ? Hc | ? | x' ? Hc]; subst; try omega.
    {
      destruct (nat_cmp _ (_ + _)); subst; destruct (nat_cmp _ _); subst; simpl in *; eauto; omega.
    }
    {
      destruct (nat_cmp _ (_ + _)); try subst; destruct (nat_cmp _ _); try subst; simpl in *; eauto; try omega.
    }
    {
      destruct (nat_cmp _ (_ + _)); try subst; destruct (nat_cmp _ _); try subst; simpl in *; eauto; try omega.
    }
  }
  {
    simpl.
    repeat rewrite shiftby_universal.
    simpl.
    f_equal.
    {
      repeat rewrite fold_shift_from_f in *.
      repeat rewrite fold_iter.
      eapply shift_from_shiftby_f_n; simpl in *; eauto; omega.
    }
    {
      repeat rewrite fold_shift_from_s in *.
      repeat rewrite fold_iter.
      eapply shift_from_shiftby_s_n; simpl in *; eauto; omega.
    }
    {
      repeat rewrite fold_shift_from_t in *.
      rewrite fold_iter.
      rewrite IHx; simpl in *; eauto; omega.
    }
  }
  {
    simpl.
    repeat rewrite shiftby_abs.
    simpl.
    repeat rewrite fold_shift_from_t in *.
    rewrite fold_iter.
    rewrite IHx; simpl in *; eauto; omega.
  }
  {
    simpl.
    repeat rewrite shiftby_app.
    simpl.
    f_equal.
    {
      repeat rewrite fold_shift_from_t in *.
      rewrite fold_iter.
      rewrite IHx1; eauto.
    }
    {
      repeat rewrite fold_shift_from_t in *.
      rewrite fold_iter.
      rewrite IHx2; simpl in *; eauto; omega.
    }
  }
  {
    simpl.
    repeat rewrite shiftby_recur.
    simpl.
    repeat rewrite fold_shift_from_t in *.
    rewrite fold_iter.
    rewrite IHx; simpl in *; eauto; omega.
  }
  {
    simpl.
    repeat rewrite shiftby_hide.
    simpl.
    repeat rewrite fold_shift_from_t in *.
    rewrite fold_iter.
    rewrite IHx; simpl in *; eauto; omega.
  }
  {
    simpl.
    repeat rewrite shiftby_unit.
    simpl.
    eauto.
  }
  admit. (* prod *)
  admit. (* sum *)
Qed.

Lemma shift_from_shiftby_t n x : shift_from_t n (iter n (shift_from_t 0) x) = iter (S n) (shift_from_t 0) x.
Proof.
  intros; eapply shift_from_shiftby_t_n; simpl; eauto.
Qed.

