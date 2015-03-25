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

(* Program Definition subst_s_f_f {ctx} (ni : var ctx CEexpr) (v : size (removen ctx ni)) (niv : var ctx CEexpr) (path : path) (i : stat_idx) : cexpr (removen ctx ni) := *)
Definition subst_s_f_f {ctx} (ni : var ctx CEexpr) (v : size (removen ctx ni)) (niv : var ctx CEexpr) (path : path) (i : stat_idx) : cexpr (removen ctx ni).
  refine
    match un_var ni, un_var niv with
      | unVar n Hn Hni, unVar nv Hnv Hniv =>
        match nat_cmp nv n with 
          | LT p Heq Hlt => Fvar (#nv, path) i
          | EQ Heq => query_path_idx path i v
          | GT p Heq Hlt => Fvar (#p, path) i
        (* | LT p Heq Hlt => Fvar (Var #nv, path) i *)
        (* | EQ Heq => query_path_idx path i v *)
        (* | GT p Heq Hlt => Fvar (Var #p, path) i *)
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
    Lemma remove_after A ls : forall m n (a : A), n < m -> let ls' := removen ls m in nth_error ls n = Some a -> nth_error ls' n = Some a.
    Proof.
      simpl.
      induction ls; destruct m; destruct n; simpl in *; intros; try discriminate; try omega; eauto.
      eapply IHls; eauto.
      omega.
    Qed.
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
    Lemma remove_before A ls : forall m n (a : A), m < S n -> let ls' := removen ls m in nth_error ls (S n) = Some a -> nth_error ls' n = Some a.
    Proof.
      simpl.
      induction ls; destruct m; destruct n; simpl in *; intros; try discriminate; try omega; eauto.
      eapply IHls; eauto.
      omega.
    Qed.
    eapply remove_before; eauto.
  }
Defined.
  
Definition substn_size_cexpr {ctx} (n : var ctx CEexpr) (v : size (removen ctx n)) (b : cexpr ctx) : cexpr (removen ctx n) :=
  visit_f (subst_s_f_f n v) b.

Global Arguments fst {A B} _.
Global Arguments snd {A B} _.

Definition subst_size_cexpr {ctx} (v : size ctx) (b : cexpr (CEexpr :: ctx)) : cexpr ctx :=
  substn_size_cexpr (@Var (CEexpr :: ctx) CEexpr 0 (eq_refl true)) v b.

(* substitute the outer-most bound variable *)
Class Subst value body result :=
  {
    subst : value -> body -> result
  }.

Global Instance Subst_size_cexpr ctx : Subst (size ctx) (cexpr (CEexpr :: ctx)) (cexpr ctx) :=
  {
    subst := subst_size_cexpr
  }.

Definition insert {A} (ls : list A) n new := firstn n ls ++ new ++ skipn n ls.

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
    simpl in *.
    Lemma insert_after A ls : forall m n new (a : A), n < m -> let ls' := insert ls m new in nth_error ls n = Some a -> nth_error ls' n = Some a.
    Proof.
      simpl.
      induction ls; destruct m; destruct n; simpl in *; intros; try discriminate; try omega; eauto.
      eapply IHls; eauto.
      omega.
    Qed.
    eapply insert_after; eauto.
  }
  {
    copy_as Hnv Hnv'.
    eapply ceb_iff in Hnv'.
    eapply ceb_iff.
    subst.
    simpl in *.
    Lemma insert_at A ls : forall n new (a : A), let ls' := insert ls n new in nth_error ls n = Some a -> nth_error ls' (length new + n) = Some a.
    Proof.
      Arguments insert {_} _ _ _ / .
      simpl.
      induction ls; destruct n; simpl in *; intros; try discriminate; try omega; eauto.
      simpl.
      (*here*)
      eapply IHls; eauto.
      omega.
    Qed.
  }

Definition shift_f_f n nv path i :=
  Fvar (#(shift_nat n nv), path) i.

Definition shift_from_f n f :=
  visit_f (shift_f_f n) f.

Global Instance Shift_cexpr : Shift cexpr :=
  {
    shift_from := shift_from_f
  }.

Class Shift t := 
  {
    shift_from : nat -> t -> t
  }.

Definition shift `{Shift t} := shift_from 0.

Fixpoint iter {A} n f (x : A) :=
  match n with
    | 0 => x
    | S n' => iter n' f (f x)
  end.

Definition shiftby `{Shift t} n := iter n shift.

Definition subst_list `{Subst V B} `{Shift V} (values : list V) (e : B) := 
  fst $ fold_left (fun p v => let '(b, n) := p in (substn n (shiftby n v) b, n - 1)) values (e, length values - 1).

(* 'lower' is a 'dry run' of 'subst', not doing substitution, only lowering bound variables above n *)
Class Lower t := 
  {
    lower : nat -> t -> t
  }.

Definition lower_f_f n nv path i :=
  match nat_cmp nv n with 
    | GT p _ _ => Fvar (#p, path) i
    | _ => Fvar (#nv, path) i
  end.

Definition lower_f n f :=
  visit_f
    (lower_f_f n) 
    f.

Global Instance Lower_cexpr : Lower cexpr :=
  {
    lower := lower_f
  }.

Definition map_stats {A} (f : cexpr -> A) (ss : stats) := 
  match ss with
    | (n0, n1) => (f n0, f n1)
  end.

Fixpoint visit_s (f : (nat -> path -> size) * (cexpr -> cexpr)) s :=
  let (fv, ff) := f in
  match s with
    | Svar (nv, path) => fv nv path
    | Sstats ss => Sstats $ map_stats ff ss
    | Spair a b => Spair (visit_s f a) (visit_s f b)
    | Sinlinr a b => Sinlinr (visit_s f a) (visit_s f b)
    | Sfold s => Sfold (visit_s f s)
    | Shide s => Shide (visit_s f s)
  end.

Definition subst_s_s_f n v nv path :=
  match nat_cmp nv n with 
    | LT _ _ _ => Svar (#nv, path)
    | EQ _ => query_path path v
    | GT p _ _ => Svar (#p, path)
  end.

Definition subst_size_size (n : nat) (v b : size) : size :=
  visit_s 
    (subst_s_s_f n v,
    substn n v) 
    b.

Global Instance Subst_size_size : Subst size size :=
  {
    substn := subst_size_size
  }.

Definition shift_s_f n nv path :=
  Svar (#(shift_nat n nv), path).

Definition shift_from_s n s :=
  visit_s
    (shift_s_f n,
    shift_from n)
    s.

Global Instance Shift_size : Shift size :=
  {
    shift_from := shift_from_s
  }.

Definition lower_s_f n nv path :=
  match nat_cmp nv n with 
    | GT p _ _ => Svar (#p, path)
    | _ => Svar (#nv, path)
  end.

Definition lower_s n s :=
  visit_s
    (lower_s_f n,
     lower n) 
    s.

Global Instance Lower_size : Lower size :=
  {
    lower := lower_s
  }.

Fixpoint visit_t n (f : (nat -> nat -> type) * (nat -> cexpr -> cexpr) * (nat -> size -> size)) b :=
  let fv := fst $ fst f in
  let ff := snd $ fst f in
  let fs := snd f in
  match b with
    | Tvar n' => fv n' n
    | Tarrow a time retsize b => Tarrow (visit_t n f a) (ff (S n) time) (fs (S n) retsize) (visit_t (S n) f b)
    | Tuniversal time retsize t => Tuniversal (ff (S n) time) (fs (S n) retsize) (visit_t (S n) f t) 
    | Tabs t => Tabs (visit_t (S n) f t) 
    | Tapp a b => Tapp (visit_t n f a) (visit_t n f b)
    | Trecur t => Trecur (visit_t (S n) f t) 
    | Thide t => Thide (visit_t n f t)
    | Tunit => b
    | Tprod a b => Tprod (visit_t n f a) (visit_t n f b)
    | Tsum a b => Tsum (visit_t n f a) (visit_t n f b)
  end.

(* nv : the number in var
   nq : the number of surrounding quantification layers 
 *)

Definition shift_t_f nv n : type := Tvar $ #(shift_nat n nv).

Definition shift_from_t n t := 
  visit_t n (shift_t_f, shift_from, shift_from) t.

Global Instance Shift_type : Shift type :=
  {
    shift_from := shift_from_t
  }.

Definition subst_t_t_f n v nv nq : type :=
  match nat_cmp nv (n + nq) with 
    | LT _ _ _ => #nv
    | EQ _ => shiftby nq v
    | GT p _ _ => #p (* variables above n+nq should be lowered *)
  end.

Definition lower_sub `{Lower B} n nq b := lower (n + nq) b.

Definition subst_t_t n v b := 
  visit_t 0 (subst_t_t_f n v, lower_sub n, lower_sub n) b.

Global Instance Subst_type_type : Subst type type :=
  {
    substn := subst_t_t
  }.

Definition subst_sub `{Subst V B, Shift V} n v nq b := substn (n + nq) (shiftby nq v) b.

Definition lower_t_f n nv nq : type :=
  match nat_cmp nv (n + nq) with 
    | GT p _ _ => #p
    | _ => #nv
  end.

Definition subst_size_type (n : nat) (v : size) (b : type) : type :=
  visit_t
    0 
    (lower_t_f n,
     subst_sub n v,
     subst_sub n v)
    b.

Global Instance Subst_size_type : Subst size type :=
  {
    substn := subst_size_type
  }.

Definition lower_t n t :=
  visit_t
    0
    (lower_t_f n,
     lower_sub n,
     lower_sub n)
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
  visit_e 0 (subst_e_e_f n v, lower_sub n) b.

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
     subst_sub n v)
    b.

Global Instance Subst_type_expr : Subst type expr :=
  {
    substn := subst_t_e
  }.

Definition lower_e n e :=
  visit_e 0 (lower_e_f n, lower_sub n) e.

Global Instance Lower_expr : Lower expr :=
  {
    lower := lower_e
  }.
