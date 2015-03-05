Require Import List.
Require Import Util.
Require Import TypingFacts.
Require Import EList EBool EFix.

Import ListNotations.
Local Open Scope list_scope.
Local Open Scope prog_scope.
Local Open Scope F.

Class Mul t :=
  {
    mul : t -> t -> t
  }.

Infix "*" := mul : G.

Instance Mul_nat : Mul nat :=
  {
    mul := Peano.mult
  }.

Instance Mul_cexpr : Mul cexpr :=
  {
    mul := Fmul
  }.

Notation F2 := (F1 + F1).
Notation Fvar_nil x i := (Fvar (x, []) i).
Notation "x ! i" := (Fvar_nil x i) (at level 4, format "x ! i").
Notation "{{ i | f }}" := (Sstats ((fun i => f) 0, (fun i => f) 1)).
(* Notation "x '!0'" := (Fvar (x, []) false) (at level 3, format "x '!0'"). *)
(* Notation "x '!1'" := (Fvar (x, []) true) (at level 3, format "x '!1'"). *)

(* merge-sort example *)

Definition merge_loop_type (telm : type) := 
  let list := Tlist $ telm in
  Tarrow list F0 Stt $ Tarrow (shift list) (#1!0 + #0!0) ({{ i | #1!i + #0!i }}) (shiftby 2 list).

Definition cmp_type (A : type) := Tarrow A F0 Stt $ Tarrow (shift A) F1 bool_size Tbool.

(* merge is equivalent to :
  fun A cmp =>
    fix merge xs ys =>
      match xs with
        | nil => ys
        | x :: xs' => match ys with
                        | nil => xs
                        | y :: ys' => if cmp x y then
                                        x :: merge xs' ys
                                      else
                                        y :: merge xs ys' end end
*)

Definition merge_loop (telm : type) (cmp merge : expr) := 
  Ematch_list telm #1(*xs*) (*level 0*)
              #0(*ys*)
              (Ematch_list (shiftby 2 telm) #2(*ys*) (*level 2*)
                           #3(*xs*)
                           (Eif (shiftby 4 cmp $$ #3(*x*) $$ #1(*y*)) (*level 4*)
                                (Econs $$ shiftby 4 telm $$ #3(*x*) $$ (shiftby 4 merge $$ #2(*xs'*) $$ #4(*ys*)))
                                (Econs $$ shiftby 4 telm $$ #1(*y*) $$ (shiftby 4 merge $$ #5(*xs*) $$ #0(*ys'*))))).

Definition merge :=
  Etabs $ Eabs (cmp_type #0) $ 
        Efixpoint (merge_loop_type #1) (Tlist $ #2) $ 
        Eabs (Tlist $ #3) $ 
        merge_loop #4 #3 #2.

Definition merge_type := 
  Tuniversal0 $ Tarrow (cmp_type #0) F0 Stt $ merge_loop_type #1.

Lemma Kcmp_type T t : kinding T t 0 -> kinding T (cmp_type t) 0.
Proof.
  intros H.
  eapply Karrow; eauto.
  eapply Karrow; eauto.
  {
    simpl.
    eapply Kshift; eauto.
  }
  eapply Kbool.
Qed.

Lemma TPmerge : typing [] merge merge_type F0 Stt.
Proof.
  eapply TPtabs0.
  eapply TPabs.
  { eapply Kcmp_type; eapply Kvar; eauto. }  
  simpl.
  eapply TPfixpoint.
  simpl.
  eapply TPabs.
  { eapply Klist; eapply Kvar; eauto. }
  {
    simpl.
    eapply TPabs.
    { eapply Klist; eapply Kvar; eauto. }
    {
      unfold merge_loop.
      simpl.
      eapply TPsubn.
      {
        eapply TPmatch_list.
        { eapply TPvar'; simpl; eauto. }
        {
          Arguments is_list s / .
          simpl; eauto.
        }
        { 
          eapply TPsubs.
          { eapply TPvar'; simpl; eauto. }
          {
            simpl.
            eapply leS_var_addr.
          }
        }
        {
          simpl.
          eapply TPmatch_list.
          { eapply TPvar'; simpl; eauto. }
          { simpl; eauto. }
          { 
            eapply TPsubs.
            { eapply TPvar'; simpl; eauto. }
            {
              simpl.
              eapply leS_var_addl.
            }
          }
          {
            simpl.
            eapply TPif.
            {
              eapply TPapp'.
              {
                eapply TPapp'. 
                { eapply TPvar'; simpl; eauto; compute; eauto. }
                { eapply TPvar'; simpl; eauto. }
                {
                  simpl; eauto.
                }
              }
              { eapply TPvar'; simpl; eauto. }
              { simpl; eauto. }
            }
            {
              simpl; eauto.
            }
            {
              simpl.
              eapply TPsubs.
              {
                eapply TPcons_app.
                { eapply TPvar'; simpl; eauto. }
                {
                  simpl.
                  eapply TPapp'.
                  {
                    eapply TPapp'. 
                    { eapply TPvar'; simpl; eauto; compute; eauto. }
                    { eapply TPvar'; simpl; eauto. }
                    { simpl; eauto. }
                  }
                  { eapply TPvar'; simpl; eauto. }
                  { simpl; eauto. }
                }
              }
              {
                Lemma leC_lemma1 x1 p1 x2 p2 i : Forall (fun a => a <> Punhide) p1 -> Forall (fun a => a <> Punhide) p2 -> F1 + (F0 + (Fvar (x1, p1) i + Fvar (x2, p2) i)) <= x1!i + x2!i.
                Proof.
                  intros H1 H2.
                  etransitivity.
                  { eapply leC_leE; eapply leE_addA. }
                  etransitivity.
                  { eapply leC_leE; eapply leE_addA. }
                  eapply leC_add.
                  {
                    etransitivity.
                    { eapply leC_leE; symmetry; eapply leE_addA. }
                    simpl.
                    leC_solver.
                  }
                  leC_solver.
                Qed.

                simpl.
                eapply leS_stats; simpl; eapply leC_lemma1; eapply all_not_Punhide_sound; simpl; reflexivity.
              }
            }
            {
              simpl.
              eapply TPsubs.
              {
                eapply TPcons_app.
                { eapply TPvar'; simpl; eauto. }
                {
                  simpl.
                  eapply TPapp'.
                  {
                    eapply TPapp'. 
                    { eapply TPvar'; simpl; eauto; compute; eauto. }
                    { eapply TPvar'; simpl; eauto. }
                    { simpl; eauto. }
                  }
                  { eapply TPvar'; simpl; eauto. }
                  { simpl; eauto. }
                }
              }
              {
                simpl.
                eapply leS_stats; simpl; eapply leC_lemma1; eapply all_not_Punhide_sound; simpl; reflexivity.
              }
            }
          }
        }
      }
      {
        simpl.
        leO_solver; try solve [eapply leO_addta; eapply leO_1x].
        {
          eapply leO_addta.
          eapply leO_path_subpath.
          eapply subpath_nil; eapply all_not_Punhide_sound; simpl; reflexivity.
        }
        {
          eapply leO_addtb.
          eapply leO_path_subpath.
          eapply subpath_nil; eapply all_not_Punhide_sound; simpl; reflexivity.
        }
      }
    }
  }
Qed.

Definition split_type telm :=
  Tarrow (Tlist $ telm) #0!0 (Spair {{ i | #0!i / 2%QN }} {{ i | #0!i / 2%QN }}) (Tprod (Tlist $ shift telm) (Tlist $ shift telm)).

Lemma Ksplit_type T t : kinding T t 0 -> kinding T (split_type t) 0.
Proof.
  intros H.
  eapply Karrow; eauto.
  { eapply Klist; eauto. }
  eapply Kprod'; eapply Klist; eauto; simpl; eapply Kshift; eauto.
Qed.

(* split is equivalent to : 
  fun A => 
    fix split xs =>  
      match xs with
        | nil => (nil, nil)
        | x :: xs' => match xs' with
                        | nil => (x :: nil, nil)
                        | y :: xs'' => match split xs'' with
                                 | (a, b) => (x :: a, y :: b) end end end
 *)

Definition split :=
  Etabs $ Efixpoint (split_type #0) (Tlist $ #1) $ Ematch_list #2 #0 
        (Epair $$ (Tlist $ #2) $$ (Tlist $ #2) $$ (Enil $ (#2 : type)) $$ (Enil $ (#2 : type)))
        $ Ematch_list #4 #0 
        (Epair $$ (Tlist $ #4) $$ (Tlist $ #4) $$ (Econs $$ (#4 : type) $$ #1 $$ (Enil $ (#4 : type))) $$ (Enil $ (#4 : type)))
        $ Ematch_pair ((#5 : expr) $ #0) $ Epair $$ (Tlist $ #8) $$ (Tlist $8) $$ (Econs $$ (#8 : type) $$ #5 $$ #1) $$ (Econs $$ (#8 : type) $$ #3 $$ #0).

Lemma TPsplit : typing [] split (Tuniversal0 (split_type #0)) F0 Stt.
Proof.
  eapply TPtabs0.
  eapply TPfixpoint.
  simpl.
  eapply TPabs.
  { eapply Klist; eapply Kvar; eauto. }
  simpl.
  eapply TPsubn.
  {
    eapply TPmatch_list.
    { eapply TPvar'; simpl; eauto. }
    { simpl; eauto. }
    {
      eapply TPpair_app.
      {
        eapply TPsubs.
        { eapply TPnil_app. }
        {
          eapply leS_stats; simpl; leC_solver.
        }
      }
      {
        eapply TPsubs.
        { eapply TPnil_app. }
        {
          eapply leS_stats; simpl; leC_solver.
        }
      }
    }
    simpl.
    eapply TPmatch_list.
    { eapply TPvar'; simpl; eauto. }
    { simpl; eauto. }
    {
      eapply TPpair_app.
      {
        eapply TPsubs.
        {
          eapply TPcons_app.
          { eapply TPvar'; simpl; eauto. }
          { eapply TPnil_app. }
        }
        {
          simpl.
          eapply leS_stats; simpl; leC_solver.
        }
      }
      {
        eapply TPsubs.
        { eapply TPnil_app. }
        {
          eapply leS_stats; simpl; leC_solver.
        }
      }
    }
    simpl.
    eapply TPsubs.
    {
      eapply TPmatch_pair'.
      {
        eapply TPapp'.
        { eapply TPvar'; simpl; eauto; compute; eauto. }
        { eapply TPvar'; simpl; eauto. }
        { simpl; eauto. }
      }
      { simpl; eauto. }
      {
        eapply TPpair_app.
        {
          eapply TPcons_app.
          { eapply TPvar'; simpl; eauto. }
          { eapply TPvar'; simpl; eauto. }
        }
        {
          eapply TPcons_app.
          { eapply TPvar'; simpl; eauto. }
          { eapply TPvar'; simpl; eauto. }
        }
      }
      { simpl; eauto. }
      { eauto. }
    }
    {
      compute.
      split; eapply leC_add; leC_solver; eapply leC_scale; try reflexivity; eapply leC_path_subpath; eapply subpath_nil; eapply all_not_Punhide_sound; simpl; reflexivity.
    }
  }
  {
    simpl.
    leO_solver; try solve [eapply leO_1x].
    eapply leO_path_subpath.
    eapply subpath_nil; eapply all_not_Punhide_sound; simpl; reflexivity.
  }
Qed.

Definition msort_loop_type telm :=
  Tarrow (Tlist $ telm) (#0!0 * log2 #0!0) (Sstats (#0!0, #0!1)) (Tlist $ shift telm).

(* msort is equivalent to : 
  fun A cmp => 
    fix msort xs =>  
      match xs with
        | nil => xs
        | _ :: xs' => match xs' with
                        | nil => xs 
                        | _ => match split xs with
                                 | (ys, zs) => merge (msort ys) (msort zs) end end end
 *)

Definition msort :=
  Etabs $ Eabs (cmp_type #0) $ Efixpoint (msort_loop_type #1) (Tlist $ #2)
        (Ematch_list #3 #0 
                     #0
                     (Ematch_list #5 #0
                                  #2
                                  (Ematch_pair (split $$ (#7 : type) $$ #4)
                                               (Etapp merge #9 $$ #8 $$ (Eapp #7 #1) $$ (Eapp #7 #0))))).

Definition msort_type :=
  Tuniversal0 $ Tarrow (cmp_type #0) F0 Stt $ msort_loop_type #1.

Lemma TPmsort : typing [] msort msort_type F0 Stt.
Proof.
  eapply TPtabs0.
  eapply TPabs.
  { eapply Kcmp_type; eapply Kvar; eauto. }  
  simpl.
  eapply TPfixpoint.
  simpl.
  eapply TPabs.
  { eapply Klist; eapply Kvar; eauto. }
  {
    simpl.
    eapply TPsubn.
    {
      eapply TPmatch_list.
      { eapply TPvar'; simpl; eauto. }
      { simpl; eauto. }
      {
        eapply TPsubs.
        { eapply TPvar'; simpl; eauto. }
        {
          simpl.
          eapply leS_stats; simpl; reflexivity.
        }
      }
      {
        simpl.
        eapply TPmatch_list.
        { eapply TPvar'; simpl; eauto. }
        { simpl; eauto. }
        {
          eapply TPsubs.
          { eapply TPvar'; simpl; eauto. }
          {
            simpl.
            eapply leS_stats; simpl; reflexivity.
          }
        }
        {
          simpl.
          eapply TPsubs.
          {
            eapply TPmatch_pair'.
            {
              eapply TPapp'.
              { 
                eapply TPtapp0.
                {
                  eapply TPweaken_empty.
                  eapply TPsplit.
                }
                { simpl; eauto. }
              }
              { eapply TPvar'; simpl; eauto. }
              { simpl; eauto. }
            }
            { simpl; eauto. }
            {
              eapply TPapp'.
              {
                eapply TPapp'.
                {
                  eapply TPapp'.
                  {
                    eapply TPeq.
                    {
                      eapply TPtapp0.
                      {
                        eapply TPweaken_empty.
                        eapply TPmerge.
                      }
                      eauto.
                    }
                    { simpl; reflexivity. }
                  }
                  { eapply TPvar'; simpl; eauto. }
                  { simpl; eauto. }
                }
                {
                  eapply TPapp'.
                  { eapply TPvar'; simpl; eauto; compute; eauto. }
                  { eapply TPvar'; simpl; eauto. }
                  { simpl; eauto. }
                }
                { simpl; eauto. }
              }
              {
                eapply TPapp'.
                { eapply TPvar'; simpl; eauto; compute; eauto. }
                { eapply TPvar'; simpl; eauto. }
                { simpl; eauto. }
              }
              { eauto. }
            }
            { eauto. }
            { eauto. }
          }
          {
            simpl.
            eapply leS_stats; simpl; eapply leC_two_halves.
          }
        }
      }
    }
    {
      simpl.
      leO_solver; try solve [eapply leO_1_xlog2x].
      - eapply leO_x_xlog2x.
      - eapply leO_cxlog2cx_xlog2x.
      - eapply leO_cxlog2cx_xlog2x.
      - eapply leO_cx_xlog2x.
      - eapply leO_cx_xlog2x.
    }
  }
Qed.