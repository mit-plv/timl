Require Import List.
Require Import Bedrock.Platform.Cito.GeneralTactics4.
Require Import Util.
Require Import TypingFacts.

Export Typing.

Import ListNotations.
Local Open Scope list_scope.

Local Open Scope prog_scope.

Definition Tlist := Tabs $ Trecur $ Tsum Tunit $ Tprod (Thide #1) #0.

Lemma Klist T (t : type) : kinding T t 0 -> kinding T (Tlist $$ t) 0.
Proof.
  eapply Kapp.
  {
    eapply Kabs.
    {
      simpl.
      eapply Krecur.
      eapply Ksum'.
      { eapply Kunit. }
      {
        eapply Kprod'; try eapply Khide; eapply Kvar; simpl; eauto.
      }
    }
  }
Qed.

Local Open Scope G.

Lemma Qlist (t : type) : (Tlist $$ t) == Trecur (Tsum Tunit $ Tprod (Thide (shift t)) #0).
Proof.
  eapply Qbeta'.
  simpl; eauto.
Qed.

Instance Apply_expr_var_expr : Apply expr var expr :=
  {
    apply a b := Eapp a b
  }.

Instance Apply_type_var_type : Apply type var type :=
  {
    apply a b := Tapp a b
  }.

Definition Eunhide_fst := Etabs $ Etabs $ Eabs (Tprod (Thide #1) #0) $ 
                                     Ematch_pair #0 $
                                     Epair $$ (#4 : type) $$ (#3 : type) $$ (Eunhide #1) $$ #0.

Lemma TPunhide_fst :
  typing [] Eunhide_fst (Tuniversal0 $ Tuniversal0 $ Tarrow (Tprod (Thide #1) #0) F1 (Spair (Svar (#0, [Punhide; Pfst])) (Svar (#0, [Psnd]))) $ Tprod #2 #1) F0 Stt.
Proof.
  eapply TPtabs0.
  eapply TPtabs0.
  eapply TPabs.
  { 
    eapply Kprod'; try eapply Khide; eapply Kvar; simpl; eauto.
  }
  simpl.
  eapply TPsub.
  {
    eapply TPmatch_pair'.
    { eapply TPvar'; simpl; eauto; simpl; eauto. }
    { simpl; eauto. }
    {
      simpl.
      eapply TPpair_app.
      {
        eapply TPunhide.
        { eapply TPvar'; simpl; eauto. }
        { simpl; eauto. }
      }
      { eapply TPvar'; simpl; eauto. }
    }
    { simpl; eauto. }
    { eauto. }
  }
  {
    Arguments subst_list _ _ _ _ values e / .
    simpl.
    leO_solver.
  }
  {
    simpl.
    reflexivity.
  }
Qed.

Lemma TPunhide_fst_app T A B e n s s1 s2 s1' : 
  typing T e (Tprod (Thide A) B) n s ->
  is_pair s = Some (s1', s2) ->
  is_hide s1' = Some s1 ->
  typing T (Eunhide_fst $$ A $$ B $$ e) (Tprod A B) (n + F1) (Spair s1 s2).
Proof.
  intros He Hs Hs1'.
  eapply TPsub.
  {
    eapply TPapp'.
    {
      eapply TPtapp0.
      {
        eapply TPtapp0.
        { 
          eapply TPweaken_empty.
          eapply TPunhide_fst.
        }
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
    { 
      simpl. 
      repeat rewrite fold_shift_from_t in *.
      repeat rewrite fold_subst_s_t in *.
      repeat rewrite subst_shift_s_t in *.
      fold (iter 2 (shift_from_t 0) A).
      repeat rewrite subst_shift_t_t_n in *.
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
    Arguments query_path path s / .
    simpl.
    rewrite Hs.
    simpl.
    rewrite Hs1'.
    simpl.
    reflexivity.
  }
Qed.

Definition Ematch_list (telm : type) e b_nil b_cons := 
  let tlist := Tlist $$ telm in
  Ematch_sum (Eunfold tlist e) (shift b_nil) (Ematch_pair (Eunhide_fst $$ (shift telm) $$ (shift tlist) $$ #0) $ shift_from 2 b_cons).

Definition Enil := Etabs $ Efold (Tlist $ #0) (Einl $$ Tunit $$ Tprod (Thide #0) (Tlist $ #0) $$ Ett).

Definition Econs := 
  Etabs $ Eabs #0 $ Eabs (Tlist $ #1) $ 
        let telm := #2 : type in
        let tlist := Tlist $ telm in
        Efold tlist (Einr $$ Tunit $$ Tprod (Thide telm) tlist $$ (Epair $$ Thide telm $$ tlist $$ Ehide #1 $$ #0)).

Lemma TPnil :
  typing [] Enil (Tuniversal F1 (Sfold (Sinl Stt)) $ Tlist $$ #0) F0 Stt.
Proof.
  eapply TPtabs with (n := F1) (s := Sfold (Sinl Stt)).
  simpl.
  eapply TPfold.
  { eapply Qlist. }
  {
    simpl.
    eapply TPsubn.
    {
      eapply TPinl_app.
      eapply TPtt.
    }
    {
      simpl.
      leO_solver.
    }
  }
Qed.

Lemma TPnil_app T (A : type) :
  typing T (Enil $ A) (Tlist $ A) F1 (Sfold $ Sinl Stt).
Proof.
  eapply TPsubn.
  {
    eapply TPtapp'.  
    {
      simpl.
      instantiate (3 := F1).
      simpl.
      eapply TPweaken_empty.
      eapply TPnil.
    }
    { simpl; eauto. }
  }
  {
    simpl.
    leO_solver.
  }
Qed.

Lemma TPcons : 
  typing [] Econs (Tuniversal0 $ Tarrow #0 F0 Stt $ Tarrow (Tlist $ #1) F1 (Sfold $ Sinr $ Spair (Shide #1) #0) (Tlist $ #2)) F0 Stt.
Proof.
  eapply TPtabs0.
  eapply TPabs.
  { eapply Kvar; eauto. }
  {
    simpl.
    eapply TPabs.
    { eapply Klist; eapply Kvar; eauto. }
    eapply TPfold.
    { eapply Qlist. }
    simpl.
    eapply TPsub.
    {
      eapply TPinr_app.
      eapply TPpair_app.
      {
        eapply TPhide.
        eapply TPvar'; simpl; eauto.
      }
      { eapply TPvar'; simpl; eauto. }
    }
    {
      simpl.
      leO_solver.
    }
    {
      simpl.
      reflexivity.
    }
  }
Qed.

Lemma TPcons_app T telm e ls n1 s1 n2 s2 : 
  let tlist := Tlist $ telm in
  typing T e telm n1 s1 ->
  typing T ls tlist n2 s2 -> 
  typing T (Econs $$ telm $$ e $$ ls) tlist (n1 + n2 + F1) (Sfold $ Sinr $ Spair (Shide s1) s2).
Proof.
  simpl.
  intros Hx Hxs.
  eapply TPsub.
  {
    eapply TPapp'.
    {
      eapply TPapp'.
      {
        eapply TPtapp0.
        { 
          eapply TPweaken_empty.
          eapply TPcons.
        }
        { 
          simpl. 
          eauto. 
        }
      }
      { eauto. }
      { 
        simpl. 
        eauto. 
      }
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
      fold (iter 2 (shift_from_t 0) telm).
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

Definition is_list s :=
  s <- is_fold s ;;
  p <- is_inlinr s ;;
  p <- is_pair (snd p) ;;
  let (s1, s2) := (p : size * size) in
  s1 <- is_hide s1 ;;
  ret (s1, s2).

Lemma is_list_elim s p : is_list s = Some p -> exists s1 s2 s3 s4, is_fold s = Some s1 /\ is_inlinr s1 = Some (s2, s3) /\ is_pair s3 = Some (s4, snd p) /\ is_hide s4 = Some (fst p).
Proof.
  intros H.
  unfold is_list in *.    
  destruct s; simpl in *; try discriminate.
  { inject H.
    repeat eexists.
  }
  destruct s; simpl in *; try discriminate.
  { inject H.
    repeat eexists.
  }
  destruct s2; simpl in *; try discriminate.
  { inject H.
    repeat eexists.
  }
  destruct s2_1; simpl in *; try discriminate.
  { inject H.
    repeat eexists.
  }
  { inject H.
    repeat eexists.
  }
Qed.

Lemma TPmatch_list T e e1 e2 telm n s s1 s2 t' na nb s' :
  let list := Tlist $ telm in
  typing T e list n s ->
  is_list s = Some (s1, s2) ->
  typing T e1 t' na s' ->
  typing (add_typings [(telm, Some s1); (list, Some s2)] T) e2 (shiftby 2 t') nb (shiftby 2 s') ->
  let s12 := [s1; s2] in
  typing T (Ematch_list telm e e1 e2) t' (n + F1 + max na (subst_list s12 nb)) s'.
Proof.
  simpl.
  intros He Hs H1 H2.
  unfold Ematch_list.
  eapply is_list_elim in Hs.
  simpl in Hs.
  destruct Hs as [sf [sl [sr [sfst [Hsf [Hslr [Hsp Hh]]]]]]].
  eapply TPsubn.
  {
    eapply TPmatch_inlinr.
    {
      eapply TPunfold'; eauto.
      { eapply Qlist. }
      {
        simpl.
        rewrite fold_subst_t_t in *.
        rewrite fold_shift_from_t in *.
        rewrite subst_shift_t_t.
        unfold Tsum.
        eauto.
      }
    }
    { simpl; eauto. }
    {
      rewrite fold_shift_from_t in *.
      eapply TPinsert0; eauto.
    }
    {
      eapply TPmatch_pair'.
      { 
        simpl.
        eapply TPunhide_fst_app.
        { eapply TPvar'; simpl; eauto; simpl; eauto. }
        { simpl; eapply is_pair_shift; eauto. }
        { simpl; eapply is_hide_shift; eauto. }
      }
      { simpl; eauto. }
      {
        simpl.
        repeat rewrite fold_shift_from_t in *.
        repeat rewrite fold_shift_from_s in *.
        repeat rewrite fold_shift_from_e in *.
        eapply TPinsert2; simpl; eauto.
        simpl in *.
        repeat rewrite fold_shift_from_t in *.
        repeat rewrite fold_shift_from_s in *.
        repeat rewrite fold_shift_from_e in *.
        fold (iter 1 (shift_from_t 0) telm).
        rewrite shift_from_shiftby_t.
        fold (iter 1 (shift_from_s 0) s2).
        rewrite shift_from_shiftby_s.
        eauto.
      }
      {
        simpl.
        repeat rewrite fold_shift_from_t in *.
        fold (iter 2 (shift_from_t 0) t').
        rewrite shift_from_shiftby_t.
        simpl.
        repeat rewrite fold_shift_from_t in *.
        repeat rewrite fold_shift_from_s in *.
        repeat rewrite fold_subst_s_t in *.
        fold (iter 1 (shift_from_s 0) (shift_from_s 0 s1)).
        fold (iter 2 (shift_from_t 0) (shift_from_t 0 t')).
        rewrite subst_shift_s_t_n2.
        simpl.
        repeat rewrite fold_subst_s_t in *.
        repeat rewrite fold_shift_from_t in *.
        repeat rewrite fold_shift_from_s in *.
        repeat rewrite subst_shift_s_t in *.
        eauto.
      }
      {
        simpl.
        repeat rewrite fold_shift_from_s in *.
        fold (iter 2 (shift_from_s 0) s').
        rewrite (@shift_from_shiftby_s 2).
        simpl.
        repeat rewrite fold_shift_from_s in *.
        repeat rewrite fold_subst_s_s in *.
        fold (iter 1 (shift_from_s 0) (shift_from_s 0 s1)).
        fold (iter 2 (shift_from_s 0) (shift_from_s 0 s')).
        rewrite subst_shift_s_s_n.
        simpl.
        repeat rewrite fold_subst_s_s in *.
        repeat rewrite fold_shift_from_s in *.
        repeat rewrite subst_shift_s_s in *.
        eauto.
      }
    }
  }
  {
    simpl.
    repeat rewrite fold_subst_s_f in *.
    repeat rewrite fold_shift_from_f in *.
    repeat rewrite subst_shift_s_f in *.
    leO_solver.
    eapply leO_addtb.
    eapply leO_maxtb.

    repeat rewrite fold_shift_from_s in *.

    fold (iter 2 (shift_from_s 0) s1).
    erewrite <- shift_from_shiftby_s.

    repeat rewrite subst_shift_from_s_f by omega.
    eauto.
    repeat rewrite subst_shift_s_f in *.
    reflexivity.
  }
Qed.

