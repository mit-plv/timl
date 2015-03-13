Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 
Generalizable All Variables.

Require Import List.
Require Import Omega.
Require Import Bedrock.Platform.Cito.GeneralTactics4.
Require Import Syntax. 
Require Import Util. 

(* substitute the outer-most bound variable *)
Class Subst value body :=
  {
    substn : nat -> value -> body -> body
  }.

Definition subst `{Subst V B} := substn 0.

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

Local Open Scope prog_scope.

Arguments fst {A B} _.
Arguments snd {A B} _.

Definition subst_list `{Subst V B} `{Shift V} (values : list V) (e : B) := 
  fst $ fold_left (fun p v => let '(b, n) := p in (substn n (shiftby n v) b, n - 1)) values (e, length values - 1).

(* 'lower' is a 'dry run' of 'subst', not doing substitution, only lowering bound variables above n *)
Class Lower t := 
  {
    lower : nat -> t -> t
  }.

Fixpoint visit_f f fm :=
  match fm with
    | Fvar (nv, path) i => f nv path i
    | F0 => fm
    | Fadd a b => Fadd (visit_f f a) (visit_f f b)
    | F1 => fm
    | Fmul a b => Fmul (visit_f f a) (visit_f f b)
    | Fscale c n => Fscale c (visit_f f n)
    | Fmax a b => Fmax (visit_f f a) (visit_f f b)
    | Flog b n => Flog b (visit_f f n)
    | Fexp b n => Fexp b (visit_f f n)
  end.

Inductive cmp m n :=
| LT n' (_ : n = S n') (_ : m < n)
| EQ (_ : m = n)
| GT m' (_ : m = S m') (_ : n < m).

Arguments LT [m n] n' _ _.
Arguments GT [m n] m' _ _.

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

Instance Monad_option : Monad option :=
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

Instance Add_nat : Add nat nat nat :=
  {
    add := Peano.plus
  }.

Instance Add_cexpr : Add cexpr cexpr cexpr :=
  {
    add := Fadd
  }.

Definition append_path (x : var_path) p : var_path := (fst x, p :: snd x).

Definition is_pair (s : size) :=
  match s with
    | Svar x => Some (Svar (append_path x Pfst), Svar (append_path x Psnd))
    | Spair a b => Some (a, b)
    | _ => None
  end.

Definition is_inlinr (s : size) :=
  match s with
    | Svar x => Some (Svar (append_path x Pinl), Svar (append_path x Pinr))
    | Sinlinr a b => Some (a, b)
    | _ => None
  end.

Definition has_inl (s : size) :=
  match s with
    | Svar x => Some (Svar (append_path x Pinl))
    | Sinlinr a b => Some a
    | Sinl s => Some s
    | _ => None
  end.

Definition has_inr (s : size) :=
  match s with
    | Svar x => Some (Svar (append_path x Pinr))
    | Sinlinr a b => Some b
    | Sinr s => Some s
    | _ => None
  end.

Definition is_fold (s : size) :=
  match s with
    | Svar x => Some (Svar (append_path x Punfold))
    | Sfold t => Some t
    | _ => None
  end.

Definition is_hide (s : size) :=
  match s with
    | Svar x => Some (Svar (append_path x Punhide))
    | Shide t => Some t
    | _ => None
  end.

Definition query_cmd cmd s :=
  match cmd with
    | Pfst => 
      p <- is_pair s ;;
      ret (fst p)
    | Psnd =>
      p <- is_pair s ;;
      ret (snd p)
    | Pinl => has_inl s
    | Pinr => has_inr s
    | Punfold => is_fold s
    | Punhide => is_hide s
  end.

Fixpoint query_path' path s :=
  match path with
    | cmd :: path => 
      s <- query_cmd cmd s ;;
      query_path' path s
    | nil => ret s
  end.

Definition query_path path := query_path' (rev path).

Definition query_idx idx s := stats_get idx $ summarize s.

Definition query_path_idx path idx s :=
  s <- query_path path s ;;
  ret (query_idx idx s).

Definition subst_s_f_f n v nv path i :=
  match nat_cmp nv n with 
    | LT _ _ _ => Fvar (#nv, path) i
    | EQ _ => default F0 $ query_path_idx path i v
    | GT p _ _ => Fvar (#p, path) i
  end.

Definition subst_size_cexpr (n : nat) (v : size) (b : cexpr) : cexpr :=
  visit_f (subst_s_f_f n v) b.

Instance Subst_size_cexpr : Subst size cexpr :=
  {
    substn := subst_size_cexpr
  }.

Definition shift_nat n nv :=
  match nat_cmp nv n with
    | LT _ _ _ => nv
    | _ => S nv
  end.

Definition shift_f_f n nv path i :=
  Fvar (#(shift_nat n nv), path) i.

Definition shift_from_f n f :=
  visit_f (shift_f_f n) f.

Instance Shift_cexpr : Shift cexpr :=
  {
    shift_from := shift_from_f
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

Instance Lower_cexpr : Lower cexpr :=
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
    | Stt => Stt
    | Spair a b => Spair (visit_s f a) (visit_s f b)
    | Sinlinr a b => Sinlinr (visit_s f a) (visit_s f b)
    | Sinl s => Sinl (visit_s f s)
    | Sinr s => Sinr (visit_s f s)
    | Sfold s => Sfold (visit_s f s)
    | Shide s => Shide (visit_s f s)
  end.

Definition subst_s_s_f n v nv path :=
  match nat_cmp nv n with 
    | LT _ _ _ => Svar (#nv, path)
    | EQ _ => default Stt $ query_path path v
    | GT p _ _ => Svar (#p, path)
  end.

Definition subst_size_size (n : nat) (v b : size) : size :=
  visit_s 
    (subst_s_s_f n v,
    substn n v) 
    b.

Instance Subst_size_size : Subst size size :=
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

Instance Shift_size : Shift size :=
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

Instance Lower_size : Lower size :=
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

Instance Shift_type : Shift type :=
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

Instance Subst_type_type : Subst type type :=
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

Instance Subst_size_type : Subst size type :=
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

Instance Lower_type : Lower type :=
  {
    lower := lower_t
  }.

Fixpoint visit_e n (f : (nat -> nat -> expr) * (nat -> type -> type)) b :=
  let (fv, ft) := f in
  match b with
    | Evar n' => fv n' n
    | Eapp a b => Eapp (visit_e n f a) (visit_e n f b)
    | Eabs t e => Eabs (ft n t) (visit_e (S n) f e)
    | Elet t def main => Elet (ft n t) (visit_e n f def) (visit_e (S n) f main)
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

Instance Shift_expr : Shift expr :=
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

Instance Subst_expr_expr : Subst expr expr :=
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

Instance Subst_type_expr : Subst type expr :=
  {
    substn := subst_t_e
  }.

Definition lower_e n e :=
  visit_e 0 (lower_e_f n, lower_sub n) e.

Instance Lower_expr : Lower expr :=
  {
    lower := lower_e
  }.

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

Lemma shift_query_cmd v : forall n c, query_cmd c (visit_s (shift_s_f n, shift_from_f n) v) = option_map (visit_s (shift_s_f n, shift_from_f n)) (query_cmd c v).
Proof.
  induction v; destruct c; try solve [simpl; eauto | simpl; destruct x; simpl; eauto].
Qed.

Lemma shift_query' p : forall v n i, default F0 (s <- query_path' p (visit_s (shift_s_f n, shift_from_f n) v);; ret (query_idx i s)) = visit_f (shift_f_f n) (default F0 (s <- query_path' p v;; ret (query_idx i s))).
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
  destruct (query_cmd a v); simpl; eauto.
Qed.

Lemma shift_query v : forall p i n, default F0 (query_path_idx p i (visit_s (shift_s_f n, shift_from_f n) v)) = visit_f (shift_f_f n) (default F0 (query_path_idx p i v)).
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

Lemma shiftby_tt_s n : forall m, iter n (shift_from_s m) Stt = Stt.
Proof.
  induction n; simpl; intros; try rewrite IHn; eauto.
Qed.

Lemma shiftby_inl_s n : forall m x, iter n (shift_from_s m) (Sinl x) = Sinl (iter n (shift_from m) x).
Proof.
  induction n; simpl; intros; try rewrite IHn; eauto.
Qed.

Lemma shiftby_inr_s n : forall m x, iter n (shift_from_s m) (Sinr x) = Sinr (iter n (shift_from m) x).
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

Arguments apply_arrow / . 

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
    repeat rewrite shiftby_tt_s.
    simpl.
    eauto.
  }
  {
    simpl.
    repeat rewrite shiftby_inl_s.
    simpl.
    repeat rewrite fold_shift_from_s in *.
    repeat rewrite fold_iter.
    rewrite IHx; simpl in *; eauto; omega.
  }
  {
    simpl.
    repeat rewrite shiftby_inr_s.
    simpl.
    repeat rewrite fold_shift_from_s in *.
    repeat rewrite fold_iter.
    rewrite IHx; simpl in *; eauto; omega.
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
    repeat rewrite shiftby_tt_s.
    simpl.
    eauto.
  }
  {
    simpl.
    repeat rewrite shiftby_inl_s.
    simpl.
    repeat rewrite fold_shift_from_s in *.
    repeat rewrite fold_iter.
    rewrite IHx; simpl in *; eauto; omega.
  }
  {
    simpl.
    repeat rewrite shiftby_inr_s.
    simpl.
    repeat rewrite fold_shift_from_s in *.
    repeat rewrite fold_iter.
    rewrite IHx; simpl in *; eauto; omega.
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
    repeat rewrite shiftby_tt_s.
    simpl.
    eauto.
  }
  {
    simpl.
    repeat rewrite shiftby_inl_s.
    simpl.
    repeat rewrite fold_shift_from_s in *.
    repeat rewrite fold_iter.
    rewrite IHx; simpl in *; eauto; omega.
  }
  {
    simpl.
    repeat rewrite shiftby_inr_s.
    simpl.
    repeat rewrite fold_shift_from_s in *.
    repeat rewrite fold_iter.
    rewrite IHx; simpl in *; eauto; omega.
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

