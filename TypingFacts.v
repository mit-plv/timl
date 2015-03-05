Require Import List.
Require Import Bedrock.Platform.Cito.GeneralTactics3.
Require Import Bedrock.Platform.Cito.GeneralTactics4.
Require Import Bedrock.Expr.
Require Import Bedrock.Structured.
Require Import Bedrock.Platform.Cito.ListFacts4.
Require Import Util.
Require Import Typing.

Export Typing.

Import ListNotations.
Open Scope list_scope.

Lemma Ksum' T a b :
  kinding T a 0 ->
  kinding T b 0 ->
  kinding T (Tsum a b) 0.
Proof.
  intros.
  eapply Kapp.
  {
    eapply Kapp.
    { eapply Ksum. }
    { eauto. }
  }
  { eauto. }
Qed.

Lemma Kprod' T a b :
  kinding T a 0 ->
  kinding T b 0 ->
  kinding T (Tprod a b) 0.
Proof.
  intros.
  eapply Kapp.
  {
    eapply Kapp.
    { eapply Kprod. }
    { eauto. }
  }
  { eauto. }
Qed.

Lemma Qbeta' t1 t2 t' :
  t' = subst t2 t1 ->
  teq (Tapp (Tabs t1) t2) t'.
Proof.
  intros; subst; eapply Qbeta; eauto.
Qed.

Lemma TPapp' T e1 e2 ta tb f g n1 n2 s1 s2 t' : 
  typing T e1 (Tarrow ta f g tb) n1 s1 ->
  typing T e2 ta n2 s2 ->
  t' = subst s2 tb ->
  typing T (Eapp e1 e2) t' (n1 + n2 + F1 + subst s2 f) (subst s2 g).
Proof.
  intros; subst; eapply TPapp; eauto.
Qed.

Lemma TPtapp' T e t2 n s t n' t' :
  typing T e (Tuniversal (shift n) (shift s) t) n' Stt ->
  t' = subst t2 t ->
  typing T (Etapp e t2) t' (n' + F1 + n) s.
Proof.
  intros; subst; eapply TPtapp; eauto.
Qed.

Lemma TPtapp0 T e t2 t n' t' :
  typing T e (Tuniversal F0 Stt t) n' Stt ->
  t' = subst t2 t ->
  typing T (Etapp e t2) t' (n' + F1 + F0) Stt.
Proof.
  intros; subst; eapply TPtapp'; eauto.
Qed.

Lemma TPvar' T n t s t' s' : 
  find n T = Some (TEtyping (t, s)) -> 
  t' = shiftby (S n) t ->
  s' = default (var_to_size #n) (shiftby (S n) s) ->
  typing T #n t' F0 s'.
Proof.
  intros; subst; eapply TPvar; eauto.
Qed.

Lemma TPweaken T T' e t n s T'' :
  typing T e t n s ->
  T'' = T ++ T' ->
  typing T'' e t n s.
Proof.
  admit.
Qed.

Lemma TPweaken_empty T e t n s :
  typing [] e t n s ->
  typing T e t n s.
Proof.
  intros H.
  eapply TPweaken; eauto.
  simpl; eauto.
Qed.

Arguments add_typing / . 
Arguments add_typings / . 
Arguments add_kinding / . 

Arguments Tprod / .

Arguments add_snd {A B} b a / .

Lemma TPunfold' T e t n s s1 t1 t' :
  typing T e t n s ->
  is_fold s = Some s1 ->
  t == Trecur t1 ->
  t' = subst t t1 ->
  typing T (Eunfold t e) t' n s1.
Proof.
  intros; subst; eapply TPunfold; eauto.
Qed.

Lemma TPmatch_pair' T e e' t t1 t2 n s n' s' s1 s2 t'' s'' :
  typing T e (Tprod t1 t2) n s ->
  is_pair s = Some (s1, s2) ->
  let t12 := [(t1, Some s1); (t2, Some s2)] in
  let T' := add_typings t12 T in
  typing T' e' t n' s' ->
  let s12 := [s1; s2] in
  t'' = subst_list s12 t ->
  s'' = subst_list s12 s' ->
  typing T (Ematch_pair e e') t'' (n + F1 + subst_list s12 n') s''.
Proof.
  intros; subst; eapply TPmatch_pair; eauto.
Qed.

Definition Epair := Econstr Cpair.
Definition Einl := Econstr Cinl.
Definition Einr := Econstr Cinr.
Definition Ett := Econstr Ctt.

Lemma TPpair_app T A B a b n1 n2 s1 s2 :
  typing T a A n1 s1 ->
  typing T b B n2 s2 ->
  typing T (Epair $$ A $$ B $$ a $$ b) (Tprod A B) (n1 + n2 + F1) (Spair s1 s2).
Proof.
  intros Ha Hb.
  eapply TPsub.
  {
    eapply TPapp'.
    {
      eapply TPapp'.
      {
        eapply TPtapp0.
        {
          eapply TPtapp0.
          { eapply TPpair. }
          { simpl; eauto. }
        }
        { simpl; eauto. }
      }
      {
        repeat rewrite fold_subst_t_t in *.
        repeat rewrite fold_shift_from_t in *.
        repeat rewrite subst_shift_t_t in *.
        eauto.
      }
      { simpl; eauto. }
    }
    {
      repeat rewrite fold_subst_s_t in *.
      repeat rewrite fold_shift_from_t in *.
      repeat rewrite subst_shift_s_t in *.
      eauto.
    }
    {
      simpl.
      repeat rewrite fold_subst_s_t in *.
      repeat rewrite fold_shift_from_t in *.
      fold (iter 2 (shift_from_t 0) B).
      repeat rewrite subst_shift_s_t_n in *.
      simpl.
      repeat rewrite fold_subst_s_t in *.
      repeat rewrite fold_shift_from_t in *.
      repeat rewrite subst_shift_s_t in *.
      eauto. 

      simpl. 
      repeat rewrite fold_shift_from_t in *.
      repeat rewrite fold_subst_s_t in *.
      fold (iter 3 (shift_from_t 0) A).
      repeat rewrite subst_shift_t_t_n in *.
      simpl.
      repeat rewrite fold_subst_s_t in *.
      repeat rewrite fold_shift_from_t in *.
      fold (iter 2 (shift_from_t 0) A).
      repeat rewrite subst_shift_s_t_n in *.
      simpl.
      repeat rewrite fold_subst_s_t in *.
      repeat rewrite fold_shift_from_t in *.
      repeat rewrite subst_shift_s_t in *.
      eauto. 
    }
  }
  {
    simpl.
    leO_solver.
  }
  {
    simpl.
    repeat rewrite fold_subst_s_s in *.
    repeat rewrite fold_shift_from_s in *.
    repeat rewrite subst_shift_s_s in *.
    reflexivity.
  }
Qed.

Lemma TPtabs0 T e t :
  typing (add_kinding 0 T) e t F0 Stt ->
  typing T (Etabs e) (Tuniversal F0 Stt t) F0 Stt.
Proof.
  intros; eapply TPtabs with (n := F0) (s := Stt); simpl; eauto.
Qed.

Lemma TPsubn T e t n s n' :
  typing T e t n s ->
  n <<= n' ->
  typing T e t n' s.
Proof.
  intros; eapply TPsub; eauto.
  reflexivity.
Qed.

Lemma TPinl_app T A B e n s :
  typing T e A n s ->
  typing T (Einl $$ A $$ B $$ e) (Tsum $$ A $$ B) (n + F1) (Sinl s).
Proof.
  intros H.
  eapply TPsub.
  {
    eapply TPapp'.
    {
      eapply TPtapp0.
      {
        eapply TPtapp0.
        { eapply TPinl. }
        { simpl; eauto. }
      }              
      { simpl; eauto. }
    }
    { 
      simpl.
      repeat rewrite fold_shift_from_t in *.
      repeat rewrite fold_subst_t_t in *.
      repeat rewrite subst_shift_t_t in *.
      eauto.
    }
    { 
      simpl.
      repeat rewrite fold_shift_from_t in *.
      repeat rewrite fold_subst_s_t in *.
      repeat rewrite subst_shift_s_t in *.
      fold (iter 2 (shift_from_t 0) A).
      repeat rewrite subst_shift_t_t_n in *.
      simpl.
      repeat rewrite fold_shift_from_t in *.
      repeat rewrite fold_subst_s_t in *.
      repeat rewrite subst_shift_s_t in *.
      eauto.
    }
  }
  {
    simpl.
    leO_solver.
  }
  {
    simpl.
    reflexivity.
  }
Qed.

Lemma TPinr_app T A B e n s :
  typing T e B n s ->
  typing T (Einr $$ A $$ B $$ e) (Tsum $$ A $$ B) (n + F1) (Sinr s).
Proof.
  intros H.
  eapply TPsub.
  {
    eapply TPapp'.
    {
      eapply TPtapp0.
      {
        eapply TPtapp0.
        { eapply TPinr. }
        { simpl; eauto. }
      }              
      { simpl; eauto. }
    }
    { eauto. }          
    { 
      simpl.
      repeat rewrite fold_shift_from_t in *.
      repeat rewrite fold_subst_s_t in *.
      repeat rewrite subst_shift_s_t in *.
      fold (iter 2 (shift_from_t 0) A).
      repeat rewrite subst_shift_t_t_n in *.
      simpl.
      repeat rewrite fold_shift_from_t in *.
      repeat rewrite fold_subst_s_t in *.
      repeat rewrite subst_shift_s_t in *.
      eauto.
    }
  }
  {
    simpl.
    leO_solver.
  }
  {
    simpl.
    reflexivity.
  }
Qed.

Lemma TPsubs T e t n s s' :
  typing T e t n s ->
  s <= s' ->
  typing T e t n s'.
Proof.
  intros; eapply TPsub; eauto.
  reflexivity.
Qed.

Lemma is_pair_shift sp s1 s2 : is_pair sp = Some (s1, s2) -> is_pair (shift sp) = Some (shift s1, shift s2).
Proof.
  destruct sp; simpl; try discriminate; intros H; inject H; eauto.
  destruct x.
  eauto.
Qed.

Lemma is_hide_shift s s' : is_hide s = Some s' -> is_hide (shift s) = Some (shift s').
Proof.
  destruct s; simpl; try discriminate; intros H; inject H; eauto.
  destruct x.
  eauto.
Qed.

Definition shift_from_TE n te :=
  match te with
    | TEtyping ty => TEtyping $ shift_from n ty
    | TEkinding k => te
  end.

Instance Shift_tc_entry : Shift tc_entry :=
  {
    shift_from := shift_from_TE
  }.

Lemma Kshift a T t k : kinding T t k -> kinding (a :: T) (shift t) k.
  admit.
Qed.

Lemma fold_shift_from_e n x : visit_e n (shift_e_f, shift_from) x = shift_from_e n x.
Proof.
  eauto.
Qed.

Definition uncurry {U V W : Type} (f : U -> V -> W) (p : U*V) : W :=
  f (fst p) (snd p).
Arguments uncurry {U V W} f p / .

Fixpoint rev_range len :=
  match len with
    | 0 => nil
    | S n => n :: rev_range n
  end.

Open Scope F.

Lemma subst_shift_from_s_t x : forall v n m, (m <= n)%nat -> subst_size_type m (shift_from_s n v) (shift_from_t (S n) x) = shift_from_t n (subst_size_type m v x).
  admit.
Qed.
Lemma subst_shift_from_s_s x : forall v n m, (m <= n)%nat -> subst_size_size m (shift_from_s n v) (shift_from_s (S n) x) = shift_from_s n (subst_size_size m v x).
  admit.
Qed.
Lemma subst_shift_from_t_t x : forall v n m, (m <= n)%nat -> subst_t_t m (shift_from_t n v) (shift_from_t (S n) x) = shift_from_t n (subst_t_t m v x).
  admit.
Qed.
Lemma shift_from_shift_from_f x n : shift_from_f (S n) (shift_from_f 0 x) = shift_from_f 0 (shift_from_f n x).
  admit.
Qed.
Lemma shift_from_shift_from_s x n : shift_from_s (S n) (shift_from_s 0 x) = shift_from_s 0 (shift_from_s n x).
  admit.
Qed.
Lemma Kinsert T t k : 
  kinding T t k ->
  forall T1 skipped T2 T' m,
    T = T1 ++ T2 ->
    m = length T1 ->
    T' = map (uncurry shift_from) (combine (rev_range m) T1) ++ skipped :: T2 ->
    kinding T' (shift_from m t) k.
  admit.
Qed.

Lemma TPlet' T t1 e1 e2 t2 n1 n2 s1 s2 t2' :
  typing T e1 t1 n1 s1 ->
  typing (add_typing (t1, Some s1) T) e2 t2 n2 s2 ->
  t2' = subst s1 t2 ->
  typing T (Elet t1 e1 e2) t2' (n1 + subst s1 n2) (subst s1 s2).
Proof.
  intros; subst; eapply TPlet; eauto.
Qed.

Lemma TPinsert T e t c s : 
  typing T e t c s ->
  forall T1 skipped T2 T' m,
    T = T1 ++ T2 ->
    m = length T1 ->
    T' = map (uncurry shift_from) (combine (rev_range m) T1) ++ skipped :: T2 ->
    typing T' (shift_from m e) (shift_from m t) (shift_from m c) (shift_from m s).
Proof.
  induction 1.
  {
    unfold_all; intros T1 skipped T2 T' m ? ? ?; subst.
    rename n into x.
    Arguments shift_e_f nv nq / .
    simpl in *.
    repeat rewrite fold_shift_from_t in *.
    repeat rewrite fold_shift_from_s in *.
    destruct (nat_cmp x (length T1)) as [x' ? Hc | ? | x' ? Hc]; subst.
    {
      eapply TPvar'.
      { simpl.
        rewrite Bedrock.Expr.nth_error_app_L in H by eauto.
        eapply Structured.nth_error_app1.
        etransitivity.
        {
          eapply map_nth_error.
          eapply nth_error_combine.
          {
            Lemma nth_error_rev_range len i : i < len -> nth_error (rev_range len) i = Some (len - (1 + i)).
              admit.
            Qed.
            rewrite nth_error_rev_range by eauto.
            eauto.
          }
          { eauto. }
        }
        { simpl; eauto. }
      }
      { simpl.
        admit.
      }
      admit.
    }
    admit.
    admit.
  }
  {
    unfold_all; intros T1 skipped T2 T' m ? ? ?; subst.
    simpl in *.
    repeat rewrite fold_shift_from_s in *.
    repeat rewrite fold_subst_s_f in *.
    repeat rewrite fold_shift_from_f in *.
    repeat rewrite <- subst_shift_from_s_f by omega.
    repeat rewrite fold_subst_s_s in *.
    repeat rewrite <- subst_shift_from_s_s by omega.
    eapply TPapp'.
    { eapply IHtyping1; eauto. }
    { eapply IHtyping2; eauto. }
    simpl.
    repeat rewrite fold_shift_from_t in *.
    repeat rewrite fold_subst_s_t in *.
    repeat rewrite fold_shift_from_s in *.
    repeat rewrite subst_shift_s_t in *.
    repeat rewrite subst_shift_from_s_t by omega.
    eauto.
  }
  {
    unfold_all; intros T1 skipped T2 T' m ? ? ?; subst.
    simpl in *.
    eapply TPabs.
    { eapply Kinsert; eauto. }
    eapply IHtyping. 
    { rewrite app_comm_cons.
      eauto.
    }
    { eauto. }
    { simpl; eauto. }
  }
  {
    unfold_all; intros T1 skipped T2 T' m ? ? ?; subst.
    simpl in *.
    eapply TPtapp'.
    { simpl. 
      repeat rewrite fold_shift_from_e in *.
      repeat rewrite fold_shift_from_s in *.
      repeat rewrite fold_shift_from_f in *.
      repeat rewrite <- shift_from_shift_from_f in *.
      repeat rewrite <- shift_from_shift_from_s in *.
      { eapply IHtyping; eauto. }
    }
    simpl.
    repeat rewrite fold_shift_from_t in *.
    repeat rewrite fold_subst_t_t in *.
    repeat rewrite subst_shift_from_t_t by omega.
    eauto.
  }
  {
    unfold_all; intros T1 skipped T2 T' m ? ? ?; subst.
    simpl in *.
    eapply TPtabs.
    eapply IHtyping. 
    { rewrite app_comm_cons.
      eauto.
    }
    { eauto. }
    { simpl; eauto. }
  }
  {
    unfold_all; intros T1 skipped T2 T' m ? ? ?; subst.
    simpl in *.
    repeat rewrite fold_shift_from_s in *.
    repeat rewrite fold_subst_s_f in *.
    repeat rewrite fold_shift_from_f in *.
    repeat rewrite <- subst_shift_from_s_f by omega.
    repeat rewrite fold_subst_s_s in *.
    repeat rewrite <- subst_shift_from_s_s by omega.
    eapply TPlet'.
    { eapply IHtyping1; eauto. }
    { eapply IHtyping2.
      { rewrite app_comm_cons.
        eauto.
      }
      { eauto. }
      { simpl; eauto. }
    }
    simpl.
    repeat rewrite fold_shift_from_t in *.
    repeat rewrite fold_subst_s_t in *.
    repeat rewrite fold_shift_from_s in *.
    repeat rewrite subst_shift_s_t in *.
    repeat rewrite subst_shift_from_s_t by omega.
    eauto.
  }
  {
(*
    unfold_all; intros T1 skipped T2 T' m ? ? ?; subst.
    simpl.
    eapply TPletrec.
    {
      intros lhs_t rhs_t e Hin.
      Lemma in_loop A B ls b f : In b ((fix loop (ls : list A) : list B := match ls with [] => [] | x :: xs => f x :: loop xs end) ls) -> exists a, In a ls /\ f a = b.
        admit.
      Qed.
      (*here*)
      eapply (@in_loop (type * type * expr) (type * type * expr)) in Hin.
    }
    repeat rewrite fold_shift_from_s in *.
    repeat rewrite fold_subst_s_f in *.
    repeat rewrite fold_shift_from_f in *.
    repeat rewrite <- subst_shift_from_s_f by omega.
    repeat rewrite fold_subst_s_s in *.
    repeat rewrite <- subst_shift_from_s_s by omega.
    eapply TPlet'.
    { eapply IHtyping1; eauto. }
    { eapply IHtyping2.
      { rewrite app_comm_cons.
        eauto.
      }
      { eauto. }
      { simpl; eauto. }
    }
    simpl.
    repeat rewrite fold_shift_from_t in *.
    repeat rewrite fold_subst_s_t in *.
    repeat rewrite fold_shift_from_s in *.
    repeat rewrite subst_shift_s_t in *.
    repeat rewrite subst_shift_from_s_t by omega.
    eauto.
*)
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
Qed.

Lemma TPinsert2 T e t n s r0 r1 r2 r0' r1' : 
  typing (r0 :: r1 :: T) e t n s ->
  r0' = shift_from 1 r0 ->
  r1' = shift_from 0 r1 ->
  typing (r0' :: r1' :: r2 :: T) (shift_from 2 e) (shift_from 2 t) (shift_from 2 n) (shift_from 2 s).
Proof.
  intros H ? ?; subst.
  eapply TPinsert; eauto.
  {
    instantiate (1 := T).
    instantiate (1 := [r0; r1]).
    eauto.
  }
  { eauto. }
  simpl; eauto.
Qed.

Lemma TPinsert0 T e t n s r : typing T e t n s -> typing (r :: T) (shift e) (shift t) (shift n) (shift s).
Proof.
  intros H.
  eapply TPinsert; eauto.
  {
    instantiate (1 := T).
    instantiate (1 := []).
    eauto.
  }
  { eauto. }
  simpl; eauto.
Qed.

