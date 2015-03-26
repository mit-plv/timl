Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 
Generalizable All Variables.

Require Import List.
Require Import Omega.
Require Import Syntax. 
Require Import Util. 

Inductive cmp m n :=
| LT n' (_ : n = S n') (_ : m < n)
| EQ (_ : m = n)
| GT m' (_ : m = S m') (_ : n < m).

Global Arguments LT [m n] n' _ _ .
Global Arguments EQ [m n] _ .
Global Arguments GT [m n] m' _ _ .

Fixpoint nat_cmp m n : cmp m n.
refine (
    match m, n with
      | 0, 0 => EQ _
      | 0, S n' => LT n' _ _
      | S m', 0 => GT m' _ _
      | S m', S n' => 
        match nat_cmp m' n' with
          | LT _ _ _ => LT n' _ _
          | EQ _ => EQ _
          | GT _ _ _ => GT m' _ _
        end
    end); subst; eauto; omega.
Defined.

Definition default A (def : A) x :=
  match x with
    | Some v => v
    | None => def
  end.

Class Monad m := 
  {
    ret : forall a, a -> m a;
    bind : forall a, m a -> forall b, (a -> m b) -> m b
  }.

Notation "x <- a ;; b" := (bind a (fun x => b)) (at level 90, right associativity).
Notation "a ;;; b" := (bind a (fun _ => b)) (at level 90, right associativity).

Global Instance Monad_option : Monad option :=
  {
    ret := fun A (v : A) => Some v;
    bind := fun A (a : option A) B (f : A -> option B) =>
              match a with
                | Some a => f a
                | None => None
              end
  }.

Class Add a b c := 
  {
    add : a -> b -> c
  }.

Infix "+" := add : G.

Global Instance Add_nat : Add nat nat nat :=
  {
    add := Peano.plus
  }.

Section ctx.

  Variable ctx : context.
  
  Global Instance Add_cexpr : Add (cexpr ctx) (cexpr ctx) (cexpr ctx) :=
    {
      add := Fadd
    }.

  Definition append_path (x : var_path ctx) p : var_path ctx := (fst x, p :: snd x).

  Global Arguments Svar {ctx} _ .
  Global Arguments Sstats {ctx} _ .

  Definition is_pair (s : size ctx) :=
    match s with
      | Svar x => Some (Svar (append_path x Pfst), Svar (append_path x Psnd))
      | Spair a b => Some (a, b)
      | _ => None
    end.

  Definition is_inlinr (s : size ctx) :=
    match s with
      | Svar x => Some (Svar (append_path x Pinl), Svar (append_path x Pinr))
      | Sinlinr a b => Some (a, b)
      | _ => None
    end.

  Definition is_fold (s : size ctx) :=
    match s with
      | Svar x => Some (Svar (append_path x Punfold))
      | Sfold t => Some t
      | _ => None
    end.

  Definition is_hide (s : size ctx) :=
    match s with
      | Svar x => Some (Svar (append_path x Punhide))
      | Shide t => Some t
      | _ => None
    end.

  Definition S0 : size ctx := Sstats (F0, F0).

  Definition query_cmd cmd s :=
    match cmd, s with
      | Pfst, Spair a b => a
      | Psnd, Spair a b => b
      | Pinl, Sinlinr a b => a
      | Pinr, Sinlinr a b => b
      | Punfold, Sfold s => s
      | Punhide, Shide s => s
      | _, Svar x => Svar (append_path x cmd)
      | _, Sstats _ => s (* being conservative *)
      | _, _ => S0 (* type mismatch *)
    end.

  Fixpoint query_path' path s :=
    match path with
      | cmd :: path => 
        let s := query_cmd cmd s in
        query_path' path s
      | nil => s
    end.

  Definition query_path path := query_path' (rev path).

  Local Open Scope prog_scope.

  Definition query_idx idx s : cexpr ctx := stats_get idx $ summarize s.

  Definition query_path_idx path idx s :=
    let s := query_path path s in
    query_idx idx s.

End ctx.

Fixpoint visit_f {ctx ctx'} f (fm : cexpr ctx) : cexpr ctx' :=
  match fm with
    | Fvar (nv, path) i => f nv path i
    | F0 => @F0 ctx'
    | Fadd a b => Fadd (visit_f f a) (visit_f f b)
    | F1 => @F1 ctx'
    | Fmul a b => Fmul (visit_f f a) (visit_f f b)
    | Fscale c n => Fscale c (visit_f f n)
    | Fmax a b => Fmax (visit_f f a) (visit_f f b)
    | Flog b n => Flog b (visit_f f n)
    | Fexp b n => Fexp b (visit_f f n)
    | Fminus1 c => Fminus1 (visit_f f c)
  end.

Coercion get_i {ctx t} (x : var ctx t) :=
  match x with
    | Var i _ => i
  end.

Coercion nat_of_ord n (i : 'I_n) := match i with Ordinal m _ => m end.

Fixpoint removen {A} (ls : list A) n :=
  match ls with
    | x :: ls =>
      match n with
        | 0 => ls
        | S n => x :: removen ls n
      end
    | nil => nil
  end.

Require Import Program.

Arguments Var {ctx t} _ _ .

Require Import Coq.Bool.Bool.
Require Import Compare_dec.

Inductive unvar {ctx t} (x : var ctx t) :=
| unVar n H (_ : x = Var n H)
.

Definition un_var {ctx t} (x : var ctx t) : unvar x.
  destruct x.
  econstructor.
  eauto.
Defined.

Unset Implicit Arguments.

Require Import Bedrock.Platform.Cito.GeneralTactics4.
Require Import Bedrock.Platform.Cito.GeneralTactics3.

Notation "# n" := (Var n _) (at level 3).

Lemma remove_after A ls : forall m n (a : A), n < m -> let ls' := removen ls m in nth_error ls n = Some a -> nth_error ls' n = Some a.
Proof.
  simpl.
  induction ls; destruct m; destruct n; simpl in *; intros; try discriminate; try omega; eauto.
  eapply IHls; eauto.
  omega.
Qed.

Lemma remove_before A ls : forall m n (a : A), m < S n -> let ls' := removen ls m in nth_error ls (S n) = Some a -> nth_error ls' n = Some a.
Proof.
  simpl.
  induction ls; destruct m; destruct n; simpl in *; intros; try discriminate; try omega; eauto.
  eapply IHls; eauto.
  omega.
Qed.

Definition subst_s_f_f {ctx} (ni : var ctx CEexpr) (v : size (removen ctx ni)) (niv : var ctx CEexpr) (path : path) (i : stat_idx) : cexpr (removen ctx ni).
  refine
    match un_var ni, un_var niv with
      | unVar n Hn Hni, unVar nv Hnv Hniv =>
        match nat_cmp nv n with 
          | LT p Heq Hlt => Fvar (#nv, path) i
          | EQ Heq => query_path_idx path i v
          | GT p Heq Hlt => Fvar (#p, path) i
        end
    end.
  {
    copy_as Hn Hn'.
    eapply ceb_iff in Hn'.
    copy_as Hnv Hnv'.
    eapply ceb_iff in Hnv'.
    eapply ceb_iff.
    subst.
    simpl in *.
    eapply remove_after; eauto.
  }
  {
    copy_as Hn Hn'.
    eapply ceb_iff in Hn'.
    copy_as Hnv Hnv'.
    eapply ceb_iff in Hnv'.
    eapply ceb_iff.
    subst.
    simpl in *.
    eapply remove_before; eauto.
  }
Defined.
  
Definition subst_size_cexpr {ctx} (n : var ctx CEexpr) (v : size (removen ctx n)) (b : cexpr ctx) : cexpr (removen ctx n) :=
  visit_f (subst_s_f_f n v) b.

Global Arguments fst {A B} _.
Global Arguments snd {A B} _.

(* substitute the outer-most bound variable *)
Class Subst var_t value body :=
  {
    substn : forall ctx (n : var ctx var_t), value (removen ctx n) -> body ctx -> body (removen ctx n)
  }.

Arguments substn {_ _ _ _ _} _ _ _ .

Lemma ceb_iff_c {a b} : a = b -> ceb a b = true.
  admit.
Qed.

Definition subst `{Subst var_t V B} {ctx} (v : V ctx) (b : B (var_t :: ctx)) : B ctx := substn (@Var (var_t :: ctx) var_t 0 (ceb_iff_c eq_refl)) v b.

Global Instance Subst_size_cexpr : Subst CEexpr size cexpr :=
  {
    substn := @subst_size_cexpr
  }.

Definition insert {A} (ls : list A) n new := firstn n ls ++ new ++ skipn n ls.

Lemma insert_after A ls : forall m n new (a : A), n < m -> let ls' := insert ls m new in nth_error ls n = Some a -> nth_error ls' n = Some a.
Proof.
  simpl.
  induction ls; destruct m; destruct n; simpl in *; intros; try discriminate; try omega; eauto.
  eapply IHls; eauto.
  omega.
Qed.

Require Import Bedrock.Platform.Cito.ListFacts4.

Lemma nth_error_prefix A ls1 : forall ls2 n (a : A), nth_error ls2 n = Some a -> nth_error (ls1 ++ ls2) (length ls1 + n) = Some a.
Proof.
  induction ls1; destruct n; simpl in *; intros; try discriminate; try omega; eauto.
Qed.

Lemma nth_error_at A ls1 : forall ls2 (a : A), nth_error (ls1 ++ a :: ls2) (length ls1) = Some a.
Proof.
  intros.
  rewrite <- (plus_0_r (length ls1)).
  eapply nth_error_prefix; eauto.
Qed.

Lemma insert_at A ls : forall n new (a : A), let ls' := insert ls n new in nth_error ls n = Some a -> nth_error ls' (length new + n) = Some a.
Proof.
  Arguments insert {_} _ _ _ / .
  simpl.
  induction ls; destruct n; simpl in *; intros; try discriminate; try omega; eauto.
  {
    simpl.
    inject H.
    rewrite plus_0_r.
    eapply nth_error_at.
  }
  {
    rewrite <- plus_n_Sm.
    simpl.
    eapply IHls; eauto.
  }
Qed.

Lemma insert_before A ls : forall m n new (a : A), m < n -> let ls' := insert ls m new in nth_error ls n = Some a -> nth_error ls' (length new + n) = Some a.
Proof.
  simpl.
  induction ls; destruct m; destruct n; simpl in *; intros; try discriminate; try omega; eauto.
  {
    eapply nth_error_prefix; eauto.
  }
  {
    rewrite <- plus_n_Sm.
    simpl.
    eapply IHls; eauto.
    omega.
  }
Qed.

Definition shift_nat {ctx t} new n (niv : var ctx t) : var (insert ctx n new) t.
  refine
    match un_var niv with
      | unVar nv Hnv Hniv =>
        match nat_cmp nv n with
          | LT _ _ _ => #nv
          | _ => #(length new + nv)
        end
    end.
  {
    copy_as Hnv Hnv'.
    eapply ceb_iff in Hnv'.
    eapply ceb_iff.
    subst.
    eapply insert_after; eauto.
  }
  {
    copy_as Hnv Hnv'.
    eapply ceb_iff in Hnv'.
    eapply ceb_iff.
    subst.
    simpl in *.
    eapply insert_at; eauto.
  }
  {
    copy_as Hnv Hnv'.
    eapply ceb_iff in Hnv'.
    eapply ceb_iff.
    subst.
    eapply insert_before; eauto.
  }
Defined.

Definition shift_f_f {ctx} new n nv path i :=
  Fvar (shift_nat (ctx := ctx) new n nv, path) i.

Definition shiftby_f {ctx} new n f :=
  visit_f (@shift_f_f ctx new n) f.

Class Shift {A} T := 
  {
    shiftby : forall ctx new n, T ctx -> T (@insert A ctx n new)
  }.

Arguments shiftby {_ _ _ _} _ _ _ .

Definition shift_from `{Shift T} {ctx} new n := shiftby (ctx := ctx) [new] n.
Definition shift `{Shift T} {ctx} new := shift_from (ctx := ctx) new 0.

Global Instance Shift_cexpr : Shift cexpr :=
  {
    shiftby := @shiftby_f
  }.

Fixpoint iter {A} n f (x : A) :=
  match n with
    | 0 => x
    | S n' => iter n' f (f x)
  end.

(*
Definition subst_list `{Subst V B} `{Shift V} (values : list V) (e : B) := 
  fst $ fold_left (fun p v => let '(b, n) := p in (substn n (shiftby n v) b, n - 1)) values (e, length values - 1).
*)

Definition map_stats {ctx A} (f : cexpr ctx -> A) (ss : stats ctx) := 
  match ss with
    | (n0, n1) => (f n0, f n1)
  end.

Local Open Scope prog_scope.

Arguments Sinlinr {ctx} _ _ .
Arguments Spair {ctx} _ _ .
Arguments Sfold {ctx} _ .
Arguments Shide {ctx} _ .

Fixpoint visit_s {ctx ctx'} (f : (var ctx CEexpr -> path -> size ctx') * (cexpr ctx -> cexpr ctx')) (s : size ctx) : size ctx' :=
  let (fv, ff) := f in
  match s with
    | Svar (nv, path) => fv nv path
    | Sstats ss => Sstats $ map_stats ff ss
    | Spair a b => Spair (visit_s f a) (visit_s f b)
    | Sinlinr a b => Sinlinr (visit_s f a) (visit_s f b)
    | Sfold s => Sfold (visit_s f s)
    | Shide s => Shide (visit_s f s)
  end.

Definition subst_s_s_f {ctx} (ni : var ctx CEexpr) (v : size (removen ctx ni)) (niv : var ctx CEexpr) (path : path) : size (removen ctx ni).
  refine
    match un_var ni, un_var niv with
      | unVar n Hn Hni, unVar nv Hnv Hniv =>
        match nat_cmp nv n with 
          | LT p Heq Hlt => Svar (#nv, path)
          | EQ Heq => query_path path v
          | GT p Heq Hlt => Svar (#p, path)
        end
    end.
  {
    copy_as Hn Hn'.
    eapply ceb_iff in Hn'.
    copy_as Hnv Hnv'.
    eapply ceb_iff in Hnv'.
    eapply ceb_iff.
    subst.
    simpl in *.
    eapply remove_after; eauto.
  }
  {
    copy_as Hn Hn'.
    eapply ceb_iff in Hn'.
    copy_as Hnv Hnv'.
    eapply ceb_iff in Hnv'.
    eapply ceb_iff.
    subst.
    simpl in *.
    eapply remove_before; eauto.
  }
Defined.

Definition subst_size_size {ctx} n v b :=
  visit_s 
    (@subst_s_s_f ctx n v,
    substn n v) 
    b.

Global Instance Subst_size_size : Subst CEexpr size size :=
  {
    substn := @subst_size_size
  }.

Definition shift_s_f {ctx} new n nv path :=
  Svar (shift_nat (ctx := ctx) new n nv, path).

Definition shift_s {ctx} new n s :=
  visit_s
    (@shift_s_f ctx new n,
    shiftby new n)
    s.

Global Instance Shift_size : Shift size :=
  {
    shiftby := @shift_s
  }.

Fixpoint visit_t {ctx ctx'} nq (f : (forall nq, var (nq ++ ctx) CEtype -> type (nq ++ ctx')) * (forall nq, cexpr (nq ++ ctx) -> cexpr (nq ++ ctx')) * (forall nq, size (nq ++ ctx) -> size (nq ++ ctx'))) (b : type (nq ++ ctx)) : type (nq ++ ctx') :=
  let fv := fst (fst f) in
  let ff := snd (fst f) in
  let fs := snd f in
  match b with
    | Tvar n' => fv _ n'
    | Tarrow a time retsize b => Tarrow (visit_t _ f a) (ff (CEexpr :: _) time) (fs (CEexpr :: _) retsize) (visit_t (CEexpr :: _) f b)
    | Tuniversal time retsize t => Tuniversal (ff _ time) (fs _ retsize) (visit_t (CEtype :: _) f t) 
    | Tabs t => Tabs (visit_t (CEtype :: _) f t) 
    | Tapp a b => Tapp (visit_t _ f a) (visit_t _ f b)
    | Trecur t => Trecur (visit_t (CEtype :: _) f t) 
    | Thide t => Thide (visit_t _ f t)
    | Tunit => Tunit _
    | Tprod a b => Tprod (visit_t _ f a) (visit_t _ f b)
    | Tsum a b => Tsum (visit_t _ f a) (visit_t _ f b)
  end
.

(* transport_xxx : non-computable casting *)

Definition transport_type {ctx} (t : type ctx) {ctx'} (H : ctx = ctx') : type ctx'.
  subst; eauto.
Defined.

(* cast_xxx : computable casting *)

Definition cast_cexpr {from} (t : cexpr from) {to} (H : from = to) : cexpr to.
  admit.
Defined.

Definition cast_size {from} (t : size from) {to} (H : from = to) : size to.
  admit.
Defined.

Program Fixpoint cast_type {from} (t : type from) {to} (H : from = to) : type to :=
  match t with
    | Tvar (Var n Hn) => Tvar (Var n _)
    | Tarrow a c s b => Tarrow (cast_type a H) (cast_cexpr c _) (cast_size s _) (cast_type b _)
    | Tuniversal c s t => Tuniversal (cast_cexpr c H) (cast_size s H) (cast_type t _)
    | Tabs t => Tabs (cast_type t _)
    | Tapp a b => Tapp (cast_type a H) (cast_type b H)
    | Trecur t => Trecur (cast_type t _)
    | Thide t => Thide (cast_type t H)
    | Tunit => Tunit _
    | Tprod a b => Tprod (cast_type a H) (cast_type b H)
    | Tsum a b => Tsum (cast_type a H) (cast_type b H)
  end.

Module test_compute.

  Definition ctx := [CEexpr; CEtype].

  Goal (match Tvar (@Var ctx CEtype 1 (eq_refl true)) with
         | Tvar x => get_i x
         | _ => 100 end) = 1. Proof. eapply eq_refl. Qed.

  Variable ctx' : context.
  Hypothesis ctx_ctx' : ctx = ctx'.

  (* won't compute *)
  (* Eval compute in *)
  (*     (match transport_type (Tvar (@Var ctx CEtype 1 (eq_refl true))) ctx_ctx' with *)
  (*        | Tvar x => get_i x *)
  (*        | _ => 100 end). *)

  Goal (match cast_type (Tvar (@Var ctx CEtype 1 (eq_refl true))) ctx_ctx' with
          | Tvar x => get_i x
          | _ => 100 end) = 1. Proof. eapply eq_refl. Qed.

  Goal (match cast_type (Tvar (@Var ctx CEtype 1 (eq_refl true))) ctx_ctx' with
          | Tvar x => match un_var x with
                        | unVar n _ _ => n
                      end
          | _ => 100 end) = 1. Proof. eapply eq_refl. Qed.

End test_compute.

Class Cast {A} T :=
  {
    cast : forall (from : A), T from -> forall to, from = to -> T to
  }.

Arguments cast {A T _} {from} _ {to} _ .

Instance Cast_cexpr : Cast cexpr :=
  {
    cast := @cast_cexpr
  }.

Instance Cast_size : Cast size :=
  {
    cast := @cast_size
  }.

Instance Cast_type : Cast type :=
  {
    cast := @cast_type
  }.

Lemma insert_prefix A (ls1 : list A) : forall ls2 n new, insert (ls1 ++ ls2) (length ls1 + n) new = ls1 ++ insert ls2 n new.
Proof.
  induction ls1; simpl in *; intros; eauto; f_equal; eauto.
Qed.

Definition shift_t_f {ctx} new n nq (nv : var (nq ++ ctx) CEtype) : type (nq ++ insert ctx n new).
  refine
    (cast_type (Tvar (shift_nat new (length nq + n) nv)) _).
  eapply insert_prefix.
Defined.

Definition shiftby_cast `{Shift A T, Cast _ T} {ctx} new n nq (b : T (nq ++ ctx)) : T (nq ++ insert ctx n new).
  refine
    (cast (from := insert (nq ++ ctx) (length nq + n) new) (shiftby new (length nq + n) b) (to := nq ++ insert ctx n new) _).
  eapply insert_prefix.
Defined.

Definition shift_t {ctx} new n t :=
  visit_t [] (@shift_t_f ctx new n, shiftby_cast new n, shiftby_cast new n) t.

Global Instance Shift_type : Shift type :=
  {
    shiftby := @shift_t
  }.

Lemma remove_prefix A (ls1 : list A) : forall ls2 n, removen (ls1 ++ ls2) (length ls1 + n) = ls1 ++ removen ls2 n.
Proof.
  induction ls1; simpl in *; intros; eauto; f_equal; eauto.
Qed.

Definition lower_t_f {ctx} (ni : var ctx CEexpr) nq (niv : var (nq ++ ctx) CEtype) : type (nq ++ removen ctx ni).
  refine
    match un_var ni, un_var niv with
      | unVar n Hn Hni, unVar nv Hnv Hniv =>
        match nat_cmp nv (length nq + n) with 
          | GT p Heq Hlt => Tvar #p
          | LT p Heq Hlt => Tvar #nv
          | EQ Heq => _
        end
    end.
  {
    copy_as Hn Hn'.
    eapply ceb_iff in Hn'.
    copy_as Hnv Hnv'.
    eapply ceb_iff in Hnv'.
    eapply ceb_iff.
    subst.
    simpl in *.
    rewrite <- remove_prefix.
    eapply remove_after; eauto.
  }
  {
    copy_as Hn Hn'.
    eapply ceb_iff in Hn'.
    copy_as Hnv Hnv'.
    eapply ceb_iff in Hnv'.
    subst.
    simpl in *.
    erewrite nth_error_prefix in Hnv'; eauto.
    discriminate.
  }
  {
    copy_as Hn Hn'.
    eapply ceb_iff in Hn'.
    copy_as Hnv Hnv'.
    eapply ceb_iff in Hnv'.
    eapply ceb_iff.
    subst.
    simpl in *.
    rewrite <- remove_prefix.
    eapply remove_before; eauto.
  }
Defined.

Definition subst_t_t_f {ctx} (ni : var ctx CEtype) (v : type (removen ctx ni)) nq (niv : var (nq ++ ctx) CEtype) : type (nq ++ removen ctx ni).
  refine
    match un_var ni, un_var niv with
      | unVar n Hn Hni, unVar nv Hnv Hniv =>
        match nat_cmp nv (length nq + n) with 
          | LT p Heq Hlt => Tvar #nv
          | EQ Heq => shiftby nq 0 v
          | GT p Heq Hlt => Tvar #p (* variables above (length nq + n) should be lowered *)
        end
    end.
  {
    copy_as Hn Hn'.
    eapply ceb_iff in Hn'.
    copy_as Hnv Hnv'.
    eapply ceb_iff in Hnv'.
    eapply ceb_iff.
    subst.
    simpl in *.
    rewrite <- remove_prefix.
    eapply remove_after; eauto.
  }
  {
    copy_as Hn Hn'.
    eapply ceb_iff in Hn'.
    copy_as Hnv Hnv'.
    eapply ceb_iff in Hnv'.
    eapply ceb_iff.
    subst.
    simpl in *.
    rewrite <- remove_prefix.
    eapply remove_before; eauto.
  }
Defined.

Definition subst_cast `{Subst var_t V B, Shift _ V, Cast _ V, Cast _ B} {ctx} (ni : var ctx var_t) (v : V (removen ctx ni)) nq (b : B (nq ++ ctx)) : B (nq ++ removen ctx ni).
  refine
    match un_var ni with
      | unVar n Hn Hni =>
        cast (substn #(length nq + n) (cast (shiftby nq 0 v) _) b) _
    end.
  {
    subst; simpl in *.
    symmetry; eapply remove_prefix.
  }
  {
    subst; simpl in *.
    eapply remove_prefix.
  }
  Grab Existential Variables.
  {
    copy_as Hn Hn'.
    eapply ceb_iff in Hn'.
    eapply ceb_iff.
    unfold_all.
    subst.
    simpl in *.
    eapply nth_error_prefix; eauto.
  }
Defined.

Definition subst_size_type {ctx} n v b :=
  visit_t
    [] 
    (@lower_t_f ctx n,
     subst_cast n v,
     subst_cast n v)
    b.

Global Instance Subst_size_type : Subst CEexpr size type :=
  {
    substn := @subst_size_type
  }.

Definition lower_f_f {ctx} (ni : var ctx CEtype) (niv : var ctx CEexpr) (path : path) (i : stat_idx) : cexpr (removen ctx ni).
  refine
    match un_var ni, un_var niv with
      | unVar n Hn Hni, unVar nv Hnv Hniv =>
        match nat_cmp nv n with 
          | GT p Heq Hlt => Fvar (#p, path) i
          | LT p Heq Hlt => Fvar (#nv, path) i
          | EQ Heq => _
        end
    end.
  {
    copy_as Hn Hn'.
    eapply ceb_iff in Hn'.
    copy_as Hnv Hnv'.
    eapply ceb_iff in Hnv'.
    eapply ceb_iff.
    subst.
    simpl in *.
    eapply remove_after; eauto.
  }
  {
    copy_as Hn Hn'.
    eapply ceb_iff in Hn'.
    copy_as Hnv Hnv'.
    eapply ceb_iff in Hnv'.
    subst.
    simpl in *.
    erewrite Hn' in Hnv'.
    discriminate.
  }
  {
    copy_as Hn Hn'.
    eapply ceb_iff in Hn'.
    copy_as Hnv Hnv'.
    eapply ceb_iff in Hnv'.
    eapply ceb_iff.
    subst.
    simpl in *.
    eapply remove_before; eauto.
  }
Defined.

Definition lower_f {ctx} n f :=
  visit_f
    (@lower_f_f ctx n) 
    f.

(* 'lower' is a 'dry run' of 'subst', not doing substitution, only lowering bound variables above n *)
Class Lower var_t T := 
  {
    lower : forall ctx (n : var ctx var_t), T ctx -> T (removen ctx n)
  }.

Arguments lower {_ _ _ ctx} _ _ .

Global Instance Lower_cexpr : Lower CEtype cexpr :=
  {
    lower := @lower_f
  }.

Definition lower_s_f {ctx} (ni : var ctx CEtype) (niv : var ctx CEexpr) (path : path) : size (removen ctx ni).
  refine
    match un_var ni, un_var niv with
      | unVar n Hn Hni, unVar nv Hnv Hniv =>
        match nat_cmp nv n with 
          | GT p Heq Hlt => Svar (#p, path)
          | LT p Heq Hlt => Svar (#nv, path)
          | EQ Heq => _
        end
    end.
  {
    copy_as Hn Hn'.
    eapply ceb_iff in Hn'.
    copy_as Hnv Hnv'.
    eapply ceb_iff in Hnv'.
    eapply ceb_iff.
    subst.
    simpl in *.
    eapply remove_after; eauto.
  }
  {
    copy_as Hn Hn'.
    eapply ceb_iff in Hn'.
    copy_as Hnv Hnv'.
    eapply ceb_iff in Hnv'.
    subst.
    simpl in *.
    erewrite Hn' in Hnv'.
    discriminate.
  }
  {
    copy_as Hn Hn'.
    eapply ceb_iff in Hn'.
    copy_as Hnv Hnv'.
    eapply ceb_iff in Hnv'.
    eapply ceb_iff.
    subst.
    simpl in *.
    eapply remove_before; eauto.
  }
Defined.

Definition lower_s {ctx} n s :=
  visit_s
    (@lower_s_f ctx n,
     lower n) 
    s.

Global Instance Lower_size : Lower CEtype size :=
  {
    lower := @lower_s
  }.

Definition lower_cast `{Lower var_t B, Cast _ B} {ctx} (ni : var ctx var_t) nq (b : B (nq ++ ctx)) : B (nq ++ removen ctx ni).
  refine
    match un_var ni with
      | unVar n Hn Hni =>
        cast (lower #(length nq + n) b) _
    end.
  {
    subst; simpl in *.
    eapply remove_prefix.
  }
  Grab Existential Variables.
  {
    copy_as Hn Hn'.
    eapply ceb_iff in Hn'.
    eapply ceb_iff.
    unfold_all.
    subst.
    simpl in *.
    eapply nth_error_prefix; eauto.
  }
Defined.

Definition subst_t_t {ctx} n v b := 
  visit_t [] (@subst_t_t_f ctx n v, lower_cast n, lower_cast n) b.

Global Instance Subst_type_type : Subst CEtype type type :=
  {
    substn := @subst_t_t
  }.

Definition lower_t {ctx} n t :=
  visit_t
    []
    (@lower_t_f ctx n,
     lower_cast n,
     lower_cast n)
    t.

Global Instance Lower_type : Lower type :=
  {
    lower := lower_t
  }.

Fixpoint visit_e n (f : (nat -> nat -> expr) * (nat -> type -> type)) b :=
  let (fv, ft) := f in
  match b with
    | Evar n' => fv n' n
    | Eapp a b => Eapp (visit_e n f a) (visit_e n f b)
    | Eabs t e => Eabs (ft n t) (visit_e (S n) f e)
    | Elet def main => Elet (visit_e n f def) (visit_e (S n) f main)
    | Etapp e t => Etapp (visit_e n f e) (ft n t)
    | Etabs e => Etabs (visit_e (S n) f e)
    | Efold t e => Efold (ft n t) (visit_e n f e)
    | Eunfold e => Eunfold (visit_e n f e)
    | Ehide e =>Ehide (visit_e n f e)
    | Eunhide e =>Eunhide (visit_e n f e)
    | Ett => b
    | Epair a b => Epair (visit_e n f a) (visit_e n f b)
    | Einl t e => Einl (ft n t) (visit_e n f e)
    | Einr t e => Einr (ft n t) (visit_e n f e)
    | Ematch_pair target handler => Ematch_pair (visit_e n f target) (visit_e (2 + n) f handler)
    | Ematch_sum target a b => Ematch_sum (visit_e n f target) (visit_e (S n) f a) (visit_e (S n) f b)
  end.

Definition shift_e_f nv nq :=
  match nat_cmp nv nq with 
    | LT _ _ _ => #nv : expr
    | _ => #(S nv) : expr
  end.

Definition shift_from_e n e := 
  visit_e 
    n
    (shift_e_f, shift_from) 
    e.

Global Instance Shift_expr : Shift expr :=
  {
    shift_from := shift_from_e
  }.

Definition subst_e_e_f n v nv nq : expr :=
  match nat_cmp nv (n + nq) with 
    | LT _ _ _ => #nv
    | EQ _ => shiftby nq v
    | GT p _ _ => #p
  end.

Definition subst_e_e n v b := 
  visit_e 0 (subst_e_e_f n v, lower_cast n) b.

Global Instance Subst_expr_expr : Subst expr expr :=
  {
    substn := subst_e_e
  }.

Definition lower_e_f n nv nq : expr := 
  match nat_cmp nv (n + nq) with 
    | GT p _ _ => #p
    | _ => #nv
  end.

Definition subst_t_e n (v : type) (b : expr) : expr :=
  visit_e
    0
    (lower_e_f n,
     subst_cast n v)
    b.

Global Instance Subst_type_expr : Subst type expr :=
  {
    substn := subst_t_e
  }.

Definition lower_e n e :=
  visit_e 0 (lower_e_f n, lower_cast n) e.

Global Instance Lower_expr : Lower expr :=
  {
    lower := lower_e
  }.
