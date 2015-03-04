Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 
Generalizable All Variables.

Require Import List.
Require Import Program.
Require Import Bedrock.Platform.Cito.ListFacts4.
Require Import Bedrock.Platform.Cito.GeneralTactics.
Require Import Bedrock.Platform.Cito.GeneralTactics3.
Require Import NonnegRational.
Require Import Syntax.
Require Import Util.
Require Import Subst.
Require Import Order.

Import ListNotations.
Open Scope list_scope.

Close Scope F01.

Fixpoint range begin len :=
  match len with
    | 0 => nil
    | S n => begin :: range (S begin) n
  end.

Definition assoc_list A B := list (A * B).

Class Functor F :=
  {
    map : forall A B, (A -> B) -> F A -> F B
  }.

Instance Functor_list : Functor list :=
  {
    map := List.map
  }.

Instance Functor_option : Functor option :=
  {
    map := option_map
  }.

Definition map_snd {A B C} (f : B -> C) (p : A * B) := (fst p, f (snd p)).

Definition map_assoc_list A B C (f : B -> C) (ls : assoc_list A B) := map (map_snd f) ls.

Instance Functor_assoc_list A : Functor (assoc_list A) :=
  {
    map := @map_assoc_list A
  }.

Infix "<<" := compose (at level 40) : prog_scope.
Infix ">>" := (flip compose) (at level 40) : prog_scope.
Open Scope prog_scope.

Instance Apply_type_type_type : Apply type type type :=
  {
    apply := Tapp
  }.

Definition Tunit := Tconstr TCunit.
Definition Tprod t1 t2 := Tconstr TCprod $$ t1 $$ t2.
Definition Tsum t1 t2 := Tconstr TCsum $$ t1 $$ t2.

Class Find key value container := 
  {
    find : key -> container -> option value
  }.

Instance Find_list A : Find nat A (list A) :=
  {
    find k c := @nth_error A c k
  }.

Instance Apply_expr_expr_expr : Apply expr expr expr :=
  {
    apply := Eapp
  }.

Instance Apply_expr_type_expr : Apply expr type expr :=
  {
    apply := Etapp
  }.

Definition Epair := Econstr Cpair.
Definition Einl := Econstr Cinl.
Definition Einr := Econstr Cinr.
Definition Ett := Econstr Ctt.

(* kinds are restricted to the form (* => * => ... => *). 0 means * *)
Definition kind := nat.

(* Typing context.
   The second field of TEtyping is the optional size constraint
 *)
Inductive tc_entry := 
  | TEtyping (_ : type * option size)
  | TEkinding (_ : kind).

Arguments rev {A} _.

Definition cat_options {A} (ls : list (option A)) := fold_right (fun x acc => match x with Some v => v :: acc | _ => acc end) [] ls.

Definition map_option {A B} (f : A -> option B) := cat_options << map f.

(* Definition tcontext := StringMap.t tc_entry. *)
Definition tcontext := list tc_entry.

Fixpoint repeat A (a : A) n :=
  match n with
    | O => nil
    | S n => a :: repeat a n
  end.

Arguments fst {A B} _.

Instance Shift_option `{Shift A} : Shift (option A) :=
  {
    shift_from n o := option_map (shift_from n) o
  }.

Instance Shift_pair `{Shift A, Shift B} : Shift (A * B) :=
  {
    shift_from n p := (shift_from n (fst p), shift_from n (snd p))
  }.

Definition add_typing t T := TEtyping t :: T.
Definition add_typings ls T := fst $ fold_left (fun (p : tcontext * nat) t => let (T, n) := p in (add_typing (shiftby n t) T, S n)) ls (T, 0%nat).
Definition add_kinding k T := TEkinding k :: T.

Coercion var_to_size (x : var) : size := Svar (x, []).

Inductive kinding : tcontext -> type -> kind -> Prop :=
| Kvar T n k : find n T = Some (TEkinding k) -> kinding T #n k
| Kapp T t1 t2 k :
    kinding T t1 (S k) ->
    kinding T t2 0 ->
    kinding T (Tapp t1 t2) k
| Kabs T t k :
    kinding (add_kinding 0 T) t k ->
    kinding T (Tabs t) (S k)
| Karrow T t1 f g t2 :
    kinding T t1 0 ->
    kinding (add_typing (t1, None) T) t2 0 ->
    kinding T (Tarrow t1 f g t2) 0
| Kuniversal T f g t :
    kinding (add_kinding 0 T) t 0 ->
    kinding T (Tuniversal f g t) 0
| Krecur T t :
    kinding (add_kinding 0 T) t 0 ->
    kinding T (Trecur t) 0
| Khide T t :
    kinding T t 0 ->
    kinding T (Thide t) 0
| Kunit T :
    kinding T (Tconstr TCunit) 0
| Kprod T :
    kinding T (Tconstr TCprod) 2
| Ksum T :
    kinding T (Tconstr TCsum) 2
(* | Kint T : *)
(*     kinding T (Tconstr TCint) 0 *)
.

Inductive teq : type -> type -> Prop :=
| Qrefl t : teq t t
| Qsymm a b : teq a b -> teq b a
| Qtrans a b c : teq a b -> teq b c -> teq a c
| Qabs a b :
    teq a b ->
    teq (Tabs a) (Tabs b)
| Qapp a b a' b' :
    teq a a' ->
    teq b b' ->
    teq (Tapp a b) (Tapp a' b')
| Qbeta t1 t2 :
    teq (Tapp (Tabs t1) t2) (subst t2 t1)
| Qarrow a f g b a' b' : 
    teq a a' ->
    teq b b' ->
    teq (Tarrow a f g b) (Tarrow a' f g b')
| Qrecur a b :
    teq a b ->
    teq (Trecur a) (Trecur b)
.

Global Add Relation type teq
    reflexivity proved by Qrefl
    symmetry proved by Qsymm
    transitivity proved by Qtrans
      as teq_rel.

Class Equal t :=
  {
    equal : t -> t -> Prop
  }.

Infix "==" := equal (at level 70) : G.

Instance Equal_type : Equal type :=
  {
    equal := teq
  }.

Definition add_snd {A B} (b : B) (a : A) := (a, b).

Close Scope F01.
Open Scope F.
Open Scope G.

Notation Tuniversal0 := (Tuniversal F0 Stt).

Inductive typing : tcontext -> expr -> type -> cexpr -> size -> Prop :=
| TPvar T n t s : 
    find n T = Some (TEtyping (t, s)) -> 
    typing T #n (shiftby (S n) t) F0 (default (var_to_size #n) (shiftby (S n) s))
| TPapp T e1 e2 ta tb n s n1 n2 nouse s2 : 
    typing T e1 (Tarrow ta n s tb) n1 nouse ->
    typing T e2 ta n2 s2 ->
    typing T (Eapp e1 e2) (subst s2 tb) (n1 + n2 + F1 + subst s2 n) (subst s2 s)
| TPabs T e t1 t2 n s :
    kinding T t1 0 ->
    typing (add_typing (t1, None) T) e t2 n s ->
    typing T (Eabs t1 e) (Tarrow t1 n s t2) F0 Stt
| TPtapp T e t2 n s t n' :
    typing T e (Tuniversal (shift n) (shift s) t) n' Stt ->
    typing T (Etapp e t2) (subst t2 t) (n' + F1 + n) s
| TPtabs T e n s t :
    typing (add_kinding 0 T) e t n s ->
    typing T (Etabs e) (Tuniversal n s t) F0 Stt
| TPlet T t1 e1 e2 t2 n1 n2 s1 s2:
    typing T e1 t1 n1 s1 ->
    typing (add_typing (t1, Some s1) T) e2 t2 n2 s2 ->
    typing T (Elet t1 e1 e2) (subst s1 t2) (n1 + subst s1 n2) (subst s1 s2)
| TPletrec T (defs : list letrec_entry) main t n s :
    let len := length defs in
    let T' := add_typings (map (fst >> fst >> add_snd (Some Stt)) defs) T in
    (forall lhs_t rhs_t e, 
       In (lhs_t, rhs_t, e) defs -> 
       typing T' (Eabs rhs_t e) (shiftby len lhs_t) F0 Stt) ->
    typing T' main (shiftby len t) (shiftby len n) (shiftby len s) ->
    typing T (Eletrec defs main) t n s
| TPmatch_pair T e e' t t1 t2 n s n' s' s1 s2 :
    typing T e (Tprod t1 t2) n s ->
    is_pair s = Some (s1, s2) ->
    let t12 := [(t1, Some s1); (t2, Some s2)] in
    let T' := add_typings t12 T in
    typing T' e' t n' s' ->
    let s12 := [s1; s2] in
    typing T (Ematch_pair e e') (subst_list s12 t) (n + F1 + subst_list s12 n') (subst_list s12 s')
| TPmatch_inlinr T e e1 e2 t1 t2 n s s1 s2 t n1 n2 s' :
    typing T e (Tsum t1 t2) n s ->
    is_inlinr s = Some (s1, s2) ->
    (* timing constraints are passed forward; size and type constraints are passed backward.
       t' and s' are backward guidance for branches *)
    typing (add_typing (t1, Some s1) T) e1 (shift t) n1 (shift s') -> 
    typing (add_typing (t2, Some s2) T) e2 (shift t) n2 (shift s') -> 
    typing T (Ematch_sum e e1 e2) t (n + F1 + max (subst s1 n1) (subst s2 n2)) s'
| TPmatch_inl T e e1 e2 t1 t2 n s t' n' s' :
    typing T e (Tsum t1 t2) n (Sinl s) ->
    typing (add_typing (t1, Some s) T) e1 t' n' s' ->
    typing T (Ematch_sum e e1 e2) (subst s t') (n + F1 + subst s n') (subst s s')
| TPmatch_inr T e e1 e2 t1 t2 n s t' n' s' :
    typing T e (Tsum t1 t2) n (Sinr s) ->
    typing (add_typing (t2, Some s) T) e2 t' n' s' ->
    typing T (Ematch_sum e e1 e2) (subst s t') (n + F1 + subst s n') (subst s s')
| TPfold T e t n s t1 :
    t == Trecur t1 ->
    typing T e (subst t t1) n s ->
    typing T (Efold t e) t n (Sfold s)
| TPunfold T e t n s s1 t1 :
    typing T e t n s ->
    is_fold s = Some s1 ->
    t == Trecur t1 ->
    typing T (Eunfold t e) (subst t t1) n s1
| TPhide T e t n s :
    typing T e t n s ->
    typing T (Ehide e) (Thide t) n (Shide s)
| TPunhide T e t n s s1 :
    typing T e (Thide t) n s ->
    is_hide s = Some s1 ->
    typing T (Eunhide e) t n s1
| TPeq T e t1 t2 n s :
    typing T e t1 n s ->
    t1 == t2 ->
    typing T e t2 n s
| TPsub T e t n n' s s' :
    typing T e t n s ->
    n <<= n' ->
    s <= s' ->
    typing T e t n' s'
(* built-in constants *)
| TPpair T : 
    typing T Cpair (Tuniversal0 $ Tuniversal0 $ Tarrow #1 F0 Stt $ Tarrow #1 F1 (Spair #1 #0) $ Tprod #3 #2) F0 Stt
| TPinl T :
    typing T Cinl (Tuniversal0 $ Tuniversal0 $ Tarrow #1 F1 (Sinl #0) $ Tsum #2 #1) F0 Stt
| TPinr T :
    typing T Cinr (Tuniversal0 $ Tuniversal0 $ Tarrow #0 F1 (Sinr #0) $ Tsum #2 #1) F0 Stt
| TPtt T :
    typing T Ctt Tunit F0 Stt
.

(* examples *)

Instance Apply_expr_var_expr : Apply expr var expr :=
  {
    apply a b := Eapp a b
  }.

Instance Apply_type_var_type : Apply type var type :=
  {
    apply a b := Tapp a b
  }.

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

Lemma Qbeta' t1 t2 t' :
  t' = subst t2 t1 ->
  teq (Tapp (Tabs t1) t2) t'.
Proof.
  intros; subst; eapply Qbeta; eauto.
Qed.

Lemma Qlist (t : type) : (Tlist $$ t) == Trecur (Tsum Tunit $ Tprod (Thide (shift t)) #0).
Proof.
  eapply Qbeta'.
  simpl; eauto.
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

Arguments compose / . 
Arguments flip / . 
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

Definition Eunhide_fst := Etabs $ Etabs $ Eabs (Tprod (Thide #1) #0) $ 
                                     Ematch_pair #0 $
                                     Epair $$ (#4 : type) $$ (#3 : type) $$ (Eunhide #1) $$ #0.

Lemma TPsubn T e t n s n' :
  typing T e t n s ->
  n <<= n' ->
  typing T e t n' s.
Proof.
  intros; eapply TPsub; eauto.
  reflexivity.
Qed.

Close Scope F01.

Lemma TPtabs0 T e t :
  typing (add_kinding 0 T) e t F0 Stt ->
  typing T (Etabs e) (Tuniversal F0 Stt t) F0 Stt.
Proof.
  intros; eapply TPtabs with (n := F0) (s := Stt); simpl; eauto.
Qed.

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

Definition Tbool := Tsum Tunit Tunit.
Definition Etrue := Einl $$ Tunit $$ Tunit $$ Ett.
Definition Efalse := Einr $$ Tunit $$ Tunit $$ Ett.
Definition Eif e b_true b_false :=
  Ematch_sum e (shift b_true) (shift b_false).

(*  
Definition Tint := Tconstr TCint.
Variable int_lt : expr.
Hypothesis TPint_lt : forall T, typing T int_lt (Tarrow Tint F1 Stt $ Tarrow Tint F1 Stt Tbool) F1 Stt.

Definition list_int := Tlist $$ Tint.
*)

Lemma Kbool T : kinding T Tbool 0.
Proof.
  eapply Ksum'; eapply Kunit.
Qed.

Definition is_list s :=
  s <- is_fold s ;;
  p <- is_inlinr s ;;
  p <- is_pair (snd p) ;;
  let (s1, s2) := (p : size * size) in
  s1 <- is_hide s1 ;;
  ret (s1, s2).

Lemma TPsubs T e t n s s' :
  typing T e t n s ->
  s <= s' ->
  typing T e t n s'.
Proof.
  intros; eapply TPsub; eauto.
  reflexivity.
Qed.

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

Definition removen A n ls := @firstn A n ls ++ skipn (S n) ls.

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
        rewrite Expr.nth_error_app_L in H by eauto.
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

Definition Efixpoint tlhs t0 e := Eletrec [(tlhs, t0, e)] #0.

Lemma TPfixpoint T tlhs t0 e :
  typing (add_typing (tlhs, Some Stt) T) (Eabs t0 e) (shift tlhs) F0 Stt ->
  typing T (Efixpoint tlhs t0 e) tlhs F0 Stt.
Proof.
  intros H.
  eapply TPletrec.
  {
    intros until 0.
    intros Hin.
    eapply in_singleton_iff in Hin.
    inject Hin.
    simpl.
    eauto.
  }
  { eapply TPvar'; simpl; eauto. }
Qed.

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

Definition bool_size := Sinlinr Stt Stt.

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

Lemma TPif T e e1 e2 n s' t n1 n2 s s1 s2 :
  typing T e Tbool n s' ->
  is_inlinr s' = Some (s1, s2) ->
  typing T e1 t n1 s ->
  typing T e2 t n2 s ->
  typing T (Eif e e1 e2) t (n + F1 + max n1 n2) s.
Proof.
  intros He Hs H1 H2.
  {
    eapply TPsubn.
    {
      eapply TPmatch_inlinr.
      { eauto. }
      { eauto. }
      { eapply TPinsert0; eauto. }
      { eapply TPinsert0; eauto. }
    }
    {
      simpl.
      repeat rewrite fold_subst_s_f.
      repeat rewrite fold_shift_from_f.
      repeat rewrite subst_shift_s_f.
      reflexivity.
    }
  }
Qed.

Open Scope F.

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

(* Type soundness *)

(* encoding of fix by recursive-type :
     fix f(x).e := \y. (unfold v) v y 
        where v := fold (\z. (\f. \x. e) (\y. (unfold z) z y)) 
                    (for y,z\not\in FV(e))
 *)

Inductive IsOpaque : expr -> Prop :=
  | OPvar x : IsOpaque (Evar x)
  | OPconstr c : IsOpaque (Econstr c)
.

Inductive general_arg :=
  | Aapp (_ : expr)
  | Atapp (_ : type)
  | Afold (_ : type)
  | Ahide 
.

Definition general_apply (f : expr) (a : general_arg) :=
  match a with
    | Aapp e => Eapp f e
    | Atapp t => Etapp f t
    | Afold t => Efold t f
    | Ahide => Ehide f
  end.

Definition general_apply_many f args := fold_left general_apply args f.

Definition app_many f args := fold_left Eapp args f.

Inductive IsValue : expr -> Prop :=
| Vabs t e : IsValue (Eabs t e)
| Vapp f args : 
    IsOpaque f ->
    (forall a, In (Aapp a) args -> IsValue a) ->
    IsValue (general_apply_many f args)
.

(* evaluation context *)
Inductive econtext :=
  | ECempty
  | ECapp1 (f : econtext) (arg : expr)
  | ECapp2 (f : expr) (arg : econtext) : IsValue f -> econtext
  | EClet (t : type) (def : econtext) (main : expr)
  | ECletrec (defs : list letrec_entry) (main : econtext) (* Only evaluate main. All the definitions are already values, since that are all functions *)
  | ECmatch_pair (target : econtext) (_ : expr)
  | ECmatch_sum (target : econtext) (a b : expr)
  | ECtapp (f : econtext) (t : type)
  | ECfold (t : type) (_ : econtext)
  | ECunfold (t : type) (_ : econtext)
  | EChide (_ : econtext)
  | ECunhide (_ : econtext)
.

Fixpoint plug (c : econtext) (e : expr) : expr :=
  match c with
    | ECempty => e
    | ECapp1 f arg => Eapp (plug f e) arg
    | ECapp2 f arg _ => Eapp f (plug arg e)
    | EClet t def main => Elet t (plug def e) main
    | ECletrec defs main => Eletrec defs (plug main e)
    | ECmatch_pair target k => Ematch_pair (plug target e) k
    | ECmatch_sum target a b => Ematch_sum (plug target e) a b
    | ECtapp f t => Etapp (plug f e) t
    | ECfold t c => Efold t (plug c e)
    | ECunfold t c => Eunfold t (plug c e)
    | EChide c => Ehide (plug c e)
    | ECunhide c => Eunhide (plug c e)
  end.

Inductive step : expr -> expr -> Prop :=
  | STecontext c e1 e2 : step e1 e2 -> step (plug c e1) (plug c e2)
  | STapp t body arg : IsValue arg -> step (Eapp (Eabs t body) arg) (subst arg body)
  | STlet t v main : IsValue v -> step (Elet t v main) (subst v main)
  | STletrec_instantiate defs c (n : nat) t e : 
      find n defs = Some (t, e) -> 
      step (Eletrec defs (plug c (Evar #n))) (Eletrec defs (plug c e))  (* the definitions are only simplified, but not making any recursive or mutual-recursive call. All these calls are made only in the evaluation of 'main' *)
  | STletrec_finish defs v : IsValue v -> step (Eletrec defs v) v (* this is wrong *)
  (* missing some rules for letrec *)
  | STmatch_pair ta tb a b k : 
      IsValue a ->
      IsValue b ->
      step (Ematch_pair (Epair $$ ta $$ tb $$ a $$ b) k) (subst_list [a; b] k)
  | STmatch_inl ta tb v k1 k2 : 
      IsValue v ->
      step (Ematch_sum (Einl $$ ta $$ tb $$ v) k1 k2) (subst v k1)
  | STmatch_inr ta tb v k1 k2 : 
      IsValue v ->
      step (Ematch_sum (Einr $$ ta $$ tb $$ v) k1 k2) (subst v k2)
  | STtapp body t : step (Etapp (Etabs body) t) (subst t body)
  | STunfold_fold v t1 t2 : 
      IsValue v ->
      step (Eunfold t2 (Efold t1 v)) v
  | STunhide_hide v :
      IsValue v ->
      step (Eunhide (Ehide v)) v
.

Inductive nsteps : expr -> nat -> expr -> Prop :=
| Nsteps0 e : nsteps e 0 e
| NstepsS e1 e2 n e3 : step e1 e2 -> nsteps e2 n e3 -> nsteps e1 (S n) e3
.

Inductive steps : expr -> expr -> Prop :=
| Steps0 e : steps e e
| StepsS e1 e2 e3 : step e1 e2 -> steps e2 e3 -> steps e1 e3
.

Definition get_size (e : expr) : size.
  admit.
Defined.

Definition typingsim T e t := exists c s, typing T e t c s.

Open Scope G.

Definition nat_of_cexpr (c : cexpr) : option nat.
  admit.
Defined.

Definition nostuck e := forall e', steps e e' -> IsValue e' \/ exists e'', step e' e''.

Theorem type_soundness : forall t1 c s e t, 
  typing [TEtyping (t1, None)] e t c s -> 
  exists Ct s0, 
    forall v1,
      IsValue v1 ->
      typingsim [] v1 t1 ->
      let s1 := get_size v1 in
      (s0 <= s1) ->
      nostuck (subst v1 e) /\
      forall v n, 
        IsValue v -> 
        nsteps (subst v1 e) n v ->
        (exists c_s1, nat_of_cexpr (subst s1 c) = Some c_s1 /\ n <= Ct * c_s1) /\
        get_size v <= subst s1 s.
Proof.
  admit.
Qed.
