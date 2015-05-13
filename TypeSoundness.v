(* Type soundness *)

Require Import List.
Require Import Program.
Require Import Util.
Require Import Typing EvalCBV.

Import ListNotations.
Local Open Scope list_scope.

Set Implicit Arguments.

Inductive star A (R : A -> A -> Prop) : A -> A -> Prop :=
| Star0 e : star R e e
| StarS e1 e2 e3 : R e1 e2 -> star R e2 e3 -> star R e1 e3
.

Module width.

  Inductive wtype := WTstruct | WTnat.
  
  Inductive width : wtype -> context -> Type :=
  | Wvar {ctx} : var CEexpr ctx -> width WTstruct ctx
  | WappB {ctx} : width WTstruct ctx -> width WTstruct ctx -> width WTnat ctx
  | Wapp {ctx} : width WTstruct ctx -> width WTstruct ctx -> width WTstruct ctx
  | Wabs {ctx} : width WTnat (CEexpr :: ctx) -> width WTstruct (CEexpr :: ctx) -> width WTstruct ctx
  | Wtabs {ctx} : width WTnat ctx -> width WTstruct ctx -> width WTstruct ctx
  | Wfold {ctx} : width WTstruct ctx -> width WTstruct ctx
  | Wunfold {ctx} : width WTstruct ctx -> width WTstruct ctx
  | Wtt {ctx} : width WTstruct ctx
  | Wpair {ctx} : width WTstruct ctx -> width WTstruct ctx -> width WTstruct ctx
  | Winl {ctx} : width WTstruct ctx -> width WTstruct ctx
  | Winr {ctx} : width WTstruct ctx -> width WTstruct ctx
  | Wfst {ctx} : width WTstruct ctx -> width WTstruct ctx
  | Wsnd {ctx} : width WTstruct ctx -> width WTstruct ctx
  | Wmatch {ctx} : width WTstruct ctx -> width WTstruct (CEexpr :: ctx) -> width WTstruct (CEexpr :: ctx) -> width WTstruct ctx
  | Wconst {ctx} : nat -> width WTnat ctx
  | Wbinop {ctx} : (nat -> nat -> nat) -> width WTnat ctx -> width WTnat ctx -> width WTnat ctx
  .

  Global Instance Coerce_option A : Coerce A (option A) :=
    {
      coerce := Some
    }.

  Lemma shift_width : forall t (ctx new : list CtxEntry) (n : nat), width t ctx -> width t (insert ctx n new).
    admit.
  Qed.

  Global Instance Shift_width t : Shift (width t) :=
    {
      shift := @shift_width t
    }.

  Local Open Scope ty.
  Local Open Scope G.

  Inductive wtyping {ctx} : tcontext ctx -> forall {t}, width t ctx -> option (type ctx) -> Prop :=
  | WTPvar Γ x : 
      wtyping Γ (Wvar x) !(cast (shiftby (firstn (S x) ctx) !(findtc x Γ)) (firstn_skipn _ ctx))
  | WTPapp Γ e₀ e₁ τ₁ c s τ₂ s₁ : 
      wtyping Γ e₀ !(Tarrow τ₁ c s τ₂) ->
      wtyping Γ e₁ !τ₁ ->
      wtyping Γ (Wapp e₀ e₁) !(subst s₁ τ₂)
  | WTPappB Γ e₀ e₁ τ₁ c s τ₂ : 
      wtyping Γ e₀ !(Tarrow τ₁ c s τ₂) ->
      wtyping Γ e₁ !τ₁ ->
      wtyping Γ (WappB e₀ e₁) None
  | WTPabs T wB w t1 t2 c s :
      kinding T t1 0 ->
      wtyping (ctx := _ ) (add_typing t1 T) wB None ->
      wtyping (ctx := _ ) (add_typing t1 T) w !t2 ->
      wtyping T (Wabs wB w) !(Tarrow t1 c s t2)
  | WTPtabs T wB w c s t :
      wtyping (ctx := _) T wB None ->
      wtyping (ctx := _) (add_kinding T) (shift1 CEtype w) !t ->
      wtyping T (Wtabs wB w) !(Tuniversal c s t)
  | WTPfold T w t t1 :
      t == Trecur t1 ->
      wtyping T w !(subst t t1) ->
      wtyping T (Wfold w) !t
  | WTPunfold T w t t1 :
      wtyping T w !t ->
      t == Trecur t1 ->
      wtyping T (Wunfold w) !(subst t t1)
  | WTPeq T t w t1 t2 :
      wtyping T (t := t) w !t1 ->
      t1 == t2 ->
      wtyping T w !t2
  (* basic types - intro *)
  | WTPtt T :
      wtyping T Wtt !Tunit
  | WTPpair T w1 t1 w2 t2 : 
      wtyping T w1 !t1 ->
      wtyping T w2 !t2 ->
      wtyping T (Wpair w1 w2) !(t1 * t2)
  | WTPinl T t w tw :
      wtyping T w !tw ->
      wtyping T (Winl w) !(tw + t)%ty
  | WTPinr T t w tw :
      wtyping T w !tw ->
      wtyping T (Winr w) !(t + tw)%ty
  (* basic types - elim *)
  | WTPfst T w t1 t2 :
      wtyping T w !(t1 * t2) ->
      wtyping T (Wfst w) !t1
  | WTPsnd T w t1 t2 :
      wtyping T w !(t1 * t2) ->
      wtyping T (Wsnd w) !t2
  | WTPmatch T w w1 w2 t1 t2 t :
      wtyping T w !(t1 + t2)%ty ->
      wtyping (ctx := _) (add_typing t1 T) w1 !(shift1 CEexpr t) -> 
      wtyping (ctx := _) (add_typing t2 T) w2 !(shift1 CEexpr t) -> 
      wtyping T (Wmatch w w1 w2) !t
  | WTPconst T n :
      wtyping T (Wconst n) None
  | WTPbinop T op a b : 
      wtyping T a None ->
      wtyping T b None ->
      wtyping T (Wbinop op a b) None
  .

  Definition subst_width_width {t ctx} (x : var CEexpr ctx) : width WTstruct (removen ctx x) -> width t ctx -> width t (removen ctx x).
    admit.
  Defined.

  Global Instance Subst_width_width {t} : Subst CEexpr (width WTstruct) (width t) :=
    {
      substx := @subst_width_width t
    }.

  Definition consume_width {t ctx} (x : var CEtype ctx) : width t ctx -> width t (removen ctx x).
    admit.
  Defined.

  Global Instance Consume_width {t} : Consume CEtype (width t) :=
    {
      consume := @consume_width t
    }.

  Inductive wstep : forall {t}, width t [] -> width t [] -> Prop :=
  | WSappB B w w' : wstep (WappB (Wabs B w) w') (subst w' B)
  | WSapp B w w' : wstep (Wapp (Wabs B w) w') (subst w' w)
  | WSbinop op a b : wstep (Wbinop op (Wconst a) (Wconst b)) (Wconst (op a b))
  .

  Definition wsteps {t} : width t [] -> width t [] -> Prop := star wstep.

End width.

Local Notation open_var := var.
Local Notation open_cexpr := cexpr.
Local Notation open_size := size.
Local Notation open_type := type.
Local Notation open_expr := expr.
Local Notation cexpr := (open_cexpr []).
Local Notation size := (open_size []).
Local Notation type := (open_type []).
Local Notation expr := (open_expr []).

Import width.

Notation open_width := width.
Notation width := (open_width WTstruct []).
Notation wexpr := (expr * width)%type.

(* encoding of fix by recursive-type :
     fix f(x).e := \y. (unfold v) v y 
        where v := fold (\z. (\f. \x. e) (\y. (unfold z) z y)) 
                    (for y,z\not\in FV(e))
 *)

Infix "~>" := step (at level 50).

Definition steps : expr -> expr -> Prop := star step.

Infix "~>*" := steps (at level 50).

Notation "⊢" := typing.
Definition typingsim e τ := exists c s, ⊢ TCnil e τ c s.
Notation "|-" := typingsim.

Definition nostuck e := forall e', e ~>* e' -> IsValue e' \/ exists e'', e' ~> e''.

Theorem sound_wrt_nostuck :
  forall e τ,
    |- e τ ->
    nostuck e.
Proof.
  admit.
Qed.

Inductive nsteps : expr -> nat -> expr -> Prop :=
| Nsteps0 e : nsteps e 0 e
| NstepsS e1 e2 n e3 : e1 ~> e2 -> nsteps e2 n e3 -> nsteps e1 (S n) e3
.
Notation "~>#" := nsteps.

Local Open Scope G.

(* concrete size *)
Inductive csize :=
| CStt
| CSinl (_ : csize)
| CSinr (_ : csize)
| CSpair (a b: csize)
| CSfold (_ : csize)
| CShide (_ : csize)
.
(*
Definition leCS : csize -> csize -> Prop.
  admit.
Defined.

Global Instance Le_csize : Le csize csize :=
  {
    le := leCS
  }.
*)
Definition get_csize (e : expr) : csize.
  admit.
Defined.

Global Instance Coerce_expr_csize : Coerce expr csize :=
  {
    coerce := get_csize
  }.

Definition nat_of_cexpr (c : cexpr) : nat.
  admit.
Defined.

Definition c2n := nat_of_cexpr.

Global Instance Coerce_cexpr_nat : Coerce cexpr nat :=
  {
    coerce := c2n
  }.

Definition c2s {ctx} (ξ : csize) : open_size ctx.
  admit.
Defined.

Global Instance Coerce_csize_size ctx : Coerce csize (open_size ctx) :=
  {
    coerce := c2s (ctx := ctx)
  }.

Definition le_csize_size : csize -> size -> Prop.
  admit.
Defined.

Global Instance Le_cszie_size : Le csize size :=
  {
    le := le_csize_size
  }.

Infix "≤" := le (at level 70).

Infix "×" := Tprod (at level 40) : ty.
Infix "+" := Tsum : ty.
Definition runsto e τ := IsValue e /\ |- e τ.
Infix "↓" := runsto (at level 51).

Local Open Scope prog_scope.

Definition sound_wrt_bounded :=
  forall f τ₁ c s τ₂, 
    f ↓ Tarrow τ₁ c s τ₂ -> 
    exists C, 
      forall v,
        v ↓ τ₁ ->
        (* any reduction sequence is bounded by C * c(|v|) *)
        forall n e',
          ~># (f $ v) n e' -> n ≤ C * (1 + !(subst v c)).

Inductive stepex : expr -> bool -> expr -> Prop :=
| STecontext E e1 b e2 : 
    stepex e1 b e2 -> 
    stepex (plug E e1) b (plug E e2)
| STapp t body arg : IsValue arg -> stepex (Eapp (Eabs t body) arg) false (subst arg body)
| STlet v main : IsValue v -> stepex (Elet v main) false (subst v main)
| STfst v1 v2 :
    IsValue v1 ->
    IsValue v2 ->
    stepex (Efst (Epair v1 v2)) false v1
| STsnd v1 v2 :
    IsValue v1 ->
    IsValue v2 ->
    stepex (Esnd (Epair v1 v2)) false v2
| STmatch_inl t v k1 k2 : 
    IsValue v ->
    stepex (Ematch (Einl t v) k1 k2) false (subst v k1)
| STmatch_inr t v k1 k2 : 
    IsValue v ->
    stepex (Ematch (Einr t v) k1 k2) false (subst v k2)
| STtapp body t : stepex (Etapp (Etabs body) t) false (subst t body)
| STunfold_fold v t1 : 
    IsValue v ->
    stepex (Eunfold (Efold t1 v)) true v
| STunhide_hide v :
    IsValue v ->
    stepex (Eunhide (Ehide v)) false v
.

Inductive nstepsex : expr -> nat -> nat -> expr -> Prop :=
| NEsteps0 e : nstepsex e 0 0 e
| NEstepsS e1 b e2 n m e3 : stepex e1 b e2 -> nstepsex e2 n m e3 -> nstepsex e1 (S n) ((if b then 1 else 0) + m) e3
.
Notation "~>##" := nstepsex.

Definition stepsex e m e' := exists n, ~>## e n m e'.
Notation "~>*#" := stepsex.

Definition terminatesWith e v := e ~>* v /\ IsValue v.
Infix "⇓" := terminatesWith (at level 51).

Definition terminatesWithEx e m v := ~>*# e m v /\ IsValue v.
Notation "⇓*#" := terminatesWithEx.

Set Maximal Implicit Insertion.

Inductive usab := Usable | Unusable.
Definition relvart := (nat * usab)%type.
Definition nat2relvart n : relvart := (n, Usable).
Coercion nat2relvart : nat >-> relvart.

Require Import Bool.
Definition beq_pair {A B} fa fb (a b : A * B) := fa (fst a) (fst b) && fb (snd a) (snd b).

Definition beq_usab a b :=
  match a, b with
    | Usable, Usable => true
    | Unusable, Unusable => true
    | _, _ => false
  end.

Require Import EqNat.
Definition beq_relvart : relvart -> relvart -> bool := beq_pair beq_nat beq_usab.
Definition beq_orelvart := option_eq_b beq_relvart.

Lemma beq_relvart_refl m : beq_relvart m m = true.
  admit.
Qed.

Definition varR m ctx := {n | beq_orelvart (nth_error ctx n) (Some m) = true}.
Definition make_varR {m ctx} n (P : beq_orelvart (nth_error ctx n) (Some m) = true) : varR m ctx := exist _ n P.
Definition varR0 {m ctx} : varR m (m :: ctx).
  refine ((make_varR (ctx := m%nat :: _) (m := m) 0 _)).
  eapply beq_relvart_refl.
Defined.
Notation "#0" := varR0.

(*
Fixpoint forall2b A B (f : A -> B -> bool) ls1 ls2 :=
  match ls1, ls2 with
    | nil, nil => true
    | a :: ls1', b :: ls2' => f a b && forall2b f ls1' ls2'
    | _, _ => false
  end.
Definition compat_ctx : list relvart -> list relvart -> bool := forall2b (fun m m' => beq_nat (fst m) (fst m')).
Arguments compat_ctx _ _ / .
Lemma compat_ctx_refl {ctx} : compat_ctx ctx ctx = true.
  admit.
Qed.
 *)

Fixpoint change_usab chg (ctx : list relvart) : list relvart :=
  match chg, ctx with
    | new :: chg', old :: ctx' =>
      (fst old, default (snd old) new) :: change_usab chg' ctx'
    | nil, _ => ctx
    | _, _ => nil
  end.

Inductive rel : nat -> list relvart -> Type :=
| Rvar {m ctx} : varR (m, Usable) ctx -> rel m ctx
| Rinj {ctx} : Prop -> rel 0 ctx
| Rand {ctx} (_ _ : rel 0 ctx) : rel 0 ctx
| Ror {ctx} (_ _ : rel 0 ctx) : rel 0 ctx
| Rimply {ctx} (_ _ : rel 0 ctx) : rel 0 ctx
| Rforall1 {ctx T} : (T -> rel 0 ctx) -> rel 0 ctx
| Rexists1 {ctx T} : (T -> rel 0 ctx) -> rel 0 ctx
| Rforall2 {ctx m} : rel 0 (m :: ctx) -> rel 0 ctx
| Rexists2 {ctx m} : rel 0 (m :: ctx) -> rel 0 ctx
| Rabs {ctx m} : (wexpr -> rel m ctx) -> rel (S m) ctx
| Rapp {ctx m} : rel (S m) ctx -> wexpr -> rel m ctx
| Rrecur {ctx m} : rel m ((m, Unusable) :: ctx) -> rel m ctx
| Rlater {ctx} chg : rel 0 (change_usab chg ctx) -> rel 0 ctx
.

Arguments Rinj {ctx} _ .
Definition Rtrue {ctx} := Rinj (ctx := ctx) True.
Definition Rfalse {ctx} := Rinj (ctx := ctx) False.

Unset Maximal Implicit Insertion.

Generalizable All Variables.

Class MemberOf A B C :=
  {
    memberOf : A -> B -> C
  }.

Instance MemberOf_Apply `{Apply A B C} : MemberOf B A C :=
  {
    memberOf := flip apply
  }.

Require Import Bedrock.Platform.Cito.ListFacts4.

Definition uncurry {U V W : Type} (f : U -> V -> W) : U*V -> W :=
  fun p => f (fst p) (snd p).

Infix "∈" := memberOf (at level 70).

Notation "⊤" := Rtrue : rel.
Notation "⊥" := Rtrue : rel.
Notation "\ x .. y , p" := (Rabs (fun x => .. (Rabs (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity) : rel.
Notation "∀ x .. y , p" := (Rforall1 (fun x => .. (Rforall1 (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity) : rel.
Notation "∃ x .. y , p" := (Rexists1 (fun x => .. (Rexists1 (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity) : rel.
Notation "∀₂ , P" := (Rforall2 P) (at level 200, right associativity) : rel.
Notation "∃₂ , P" := (Rexists2 P) (at level 200, right associativity) : rel.
Notation "@@ , P" := (Rrecur P) (at level 200, right associativity) : rel.
Notation "⌈ P ⌉" := (Rinj P) : rel.
Global Instance Apply_rel_wexpr {m ctx} : Apply (rel (S m) ctx) wexpr (rel m ctx) :=
  {
    apply := Rapp
  }.
Infix "/\" := Rand : rel.
Infix "\/" := Ror : rel.
Infix "===>" := Rimply (at level 86) : rel.
Notation "▹" := Rlater : rel.

Delimit Scope rel with rel.
Bind Scope rel with rel.

Definition typingew (ew : wexpr) τ := let (e, w) := ew in e ↓ τ /\ wtyping [] w !τ.
Infix "↓↓" := typingew (at level 51).

Module test_rel.
  
  Variable ctx : list relvart.

  Open Scope rel.

  Definition ttt1 : rel 1 ctx := \e , ⊤.
  Definition ttt2 : rel 1 ctx := \e , ⌈e ↓↓ Tunit⌉.
  Definition ttt3 : rel 1 ctx := \_ , ⌈True /\ True⌉.

End test_rel.

(* An Logical Step-indexed Logical Relation (LSLR) for boundedness *)

Local Open Scope prog_scope.

(* closing substitutions *)

Inductive SubstEntry : CtxEntry -> list relvart -> Type :=
| SEtype {ctx} (_ : type) (_ : varR 1 ctx) : SubstEntry CEtype ctx
| SEexpr {ctx} (_ : wexpr) : SubstEntry CEexpr ctx
.

Inductive csubsts : context -> list relvart -> Type :=
| CSnil {ctx} : csubsts [] ctx
| CScons {ctx t lctx} : SubstEntry t ctx -> csubsts lctx ctx -> csubsts (t :: lctx) ctx
.

Notation "[ ]" := CSnil : CS.
Notation "[ x ; .. ; y ]" := (CScons x .. (CScons y CSnil) ..) : CS.
Infix "::" := CScons (at level 60, right associativity) : CS.
Delimit Scope CS with CS.
Bind Scope CS with csubsts.

Definition pair_of_se {ctx} (e : SubstEntry CEtype ctx) : type * varR 1 ctx :=
  match e with
    | SEtype _ t r => (t, r)
  end.

Definition type_of_se {ctx} := pair_of_se (ctx := ctx) >> fst.
Definition sem_of_se {ctx} := pair_of_se (ctx := ctx) >> snd.

Definition wexpr_of_se {ctx} (e : SubstEntry CEexpr ctx) : wexpr :=
  match e with
    | SEexpr _ s => s
  end.

Definition expr_of_se {ctx} := wexpr_of_se (ctx := ctx) >> fst.
Definition width_of_se {ctx} := wexpr_of_se (ctx := ctx) >> snd.

Definition pair_of_cs {ctx t lctx} (rho : csubsts (t :: lctx) ctx) : SubstEntry t ctx * csubsts lctx ctx :=
  match rho with
    | CScons _ _ _ e rho' => (e, rho')
  end.

Arguments tl {A} _ .

Definition csubsts_sem : forall {lctx ctx}, csubsts lctx ctx -> open_var CEtype lctx -> varR 1 ctx.
  refine
    (fix csubsts_sem {lctx} : forall ctx, csubsts lctx ctx -> open_var CEtype lctx -> varR 1 ctx :=
       match lctx return forall ctx, csubsts lctx ctx -> open_var CEtype lctx -> varR 1 ctx with
         | nil => _
         | t :: lctx' => 
           fun ctx rho =>
             match rho in (csubsts c ctx) return c = t :: lctx' -> open_var CEtype (t :: lctx') -> varR 1 ctx with
               | CSnil _ => _
               | CScons _ t' _ v rho' => _
             end eq_refl
       end).
  {
    intros ? ? x.
    destruct x.
    eapply ceb_iff in e.
    rewrite nth_error_nil in e; discriminate.
  }
  {
    discriminate.
  }
  {
    intros Heq x.
    destruct x.
    eapply ceb_iff in e.
    destruct n as [| n'].
    {
      simpl in *.
      destruct t; try discriminate; destruct t'; try discriminate.
      exact (sem_of_se v).
    }
    {
      simpl in *.
      eapply csubsts_sem with (lctx := lctx').
      - eapply (transport (T := fun lctx => csubsts lctx ctx0) rho' _).
      - eapply (#n').
    }
  }
  Grab Existential Variables.
  { eapply ceb_iff; eauto. }
  { eapply f_equal with (f := tl) in Heq; exact Heq. }
Defined.

Global Instance Apply_csubsts_nat_rel {ctx} lctx : Apply (csubsts lctx ctx) (open_var CEtype lctx) (varR 1 ctx) :=
  {
    apply := csubsts_sem
  }.

Definition csubst_type `{Subst CEtype open_type B} {ctx lctx} (v : SubstEntry CEtype ctx) (b : B (CEtype :: lctx)) : B lctx.
  refine
    (subst (cast (shiftby lctx (type_of_se v)) _) b).
  simpl.
  eapply app_nil_r.
Defined.

Definition csubst_expr `{Subst CEexpr open_expr B} {ctx lctx} (v : SubstEntry CEexpr ctx) (b : B (CEexpr :: lctx)) : B lctx.
  refine
    (subst (cast (shiftby lctx (expr_of_se v)) _) b).
  simpl.
  eapply app_nil_r.
Defined.

Definition subst_close `{Subst CEtype open_type B, Subst CEexpr open_expr B} : forall lctx ctx, csubsts lctx ctx -> B lctx -> B [].
  refine
    (fix subst_close lctx : forall ctx, csubsts lctx ctx -> B lctx -> B [] :=
       match lctx return forall ctx, csubsts lctx ctx -> B lctx -> B [] with
         | nil => fun _ _ b => b
         | t :: lctx' =>
           fun ctx rho =>
             match rho in (csubsts c ctx) return c = t :: lctx' -> B (t :: lctx') -> B [] with
               | CSnil _ => _
               | CScons _ t' _ v rho' => _
             end eq_refl
       end).
  {
    discriminate.
  }
  destruct t; destruct t'; try discriminate.
  {
    intros Heq b.
    eapply subst_close with (lctx := lctx').
    (* can use transport here because we are sure that the proof is generated from eq_refl (hence is concrete) *)
    - eapply (transport (T := fun lctx => csubsts lctx ctx0) rho' _).
    - eapply (csubst_type v b).
  }
  {
    intros Heq b.
    eapply subst_close with (lctx := lctx').
    - eapply (transport (T := fun lctx => csubsts lctx ctx0) rho' _).
    - eapply (csubst_expr v b).
  }
  Grab Existential Variables.
  { eapply f_equal with (f := tl) in Heq; exact Heq. }
  { eapply f_equal with (f := tl) in Heq; exact Heq. }
Defined.

Definition csubsts_cexpr :=
  subst_close (B := open_cexpr).

Global Instance Apply_csubsts_cexpr_cexpr {ctx} lctx : Apply (csubsts lctx ctx) (open_cexpr lctx) cexpr :=
  {
    apply := @csubsts_cexpr _ _
  }.

Definition csubsts_size :=
  subst_close (B := open_size).

Global Instance Apply_csubsts_size_size {ctx} lctx : Apply (csubsts lctx ctx) (open_size lctx) size :=
  {
    apply := @csubsts_size _ _
  }.

Definition csubsts_type :=
  subst_close (B := open_type).

Global Instance Apply_csubsts_type_type {ctx} lctx : Apply (csubsts lctx ctx) (open_type lctx) type :=
  {
    apply := @csubsts_type _ _
  }.

Definition csubsts_expr :=
  subst_close (B := open_expr).

Global Instance Apply_csubsts_expr_expr {ctx} lctx : Apply (csubsts lctx ctx) (open_expr lctx) expr :=
  {
    apply := @csubsts_expr _ _
  }.

Definition add_pair {ctx lctx} p rho :=
  CScons (ctx := ctx) (lctx := lctx) (SEtype (fst p) (snd p)) rho.

Global Instance Add_pair_csubsts {ctx} lctx : Add (type * varR 1 ctx) (csubsts lctx ctx) (csubsts (CEtype :: lctx) ctx) :=
  {
    add := add_pair
  }.

Definition add_wexpr {ctx lctx} e rho :=
  CScons (ctx := ctx) (lctx := lctx) (SEexpr e) rho.

Global Instance Add_wexpr_csubsts {ctx} lctx : Add wexpr (csubsts lctx ctx) (csubsts (CEexpr :: lctx) ctx) :=
  {
    add := add_wexpr
  }.

Definition VWSet {ctx} τ (S : rel 1 ctx) := (∀vw, vw ∈ S ===> ⌈vw ↓↓ τ⌉)%rel.

Definition shift_csubsts {lctx ctx} new n (rho : csubsts lctx ctx) : csubsts lctx (insert ctx n new).
  admit.
Defined.

Instance Shift_csubsts lctx : Shift (csubsts lctx) :=
  {
    shift := @shift_csubsts lctx
  }.

(* A "step-indexed" kriple model *)
(* the logical relation *)
Section LR.
  
  Open Scope rel.

  Open Scope ty.

  Definition pair_to_Epair {ctx} (p : open_expr ctx * open_expr ctx) := Epair (fst p) (snd p).

  Global Instance Coerce_prod_expr ctx : Coerce (open_expr ctx * open_expr ctx) (open_expr ctx) :=
    {
      coerce := pair_to_Epair (ctx := ctx)
    }.

  Existing Instance Apply_rel_wexpr.

  (* Notation "\\ e w , p" := (Rabs (uncurry (fun e w => p))) (at level 200, right associativity) : rel. *)

  Fixpoint relE' {lctx} (relV : forall ctx, csubsts lctx ctx -> rel 1 ctx) (τ : open_type lctx) (wB : open_width WTnat []) (c : nat) (s : size) ctx (ρ : csubsts lctx ctx) : rel 1 ctx :=
    \ew, let (e, w) := ew in
         ⌈|- e (ρ $ τ) /\ wtyping [] w !(ρ $ τ) /\
         exists B, wsteps wB (Wconst B) /\ forall n e', (~>## e n 0 e') -> n ≤ B⌉%type /\ 
         (∀v, ⌈⇓*# e 0 v⌉ ===> (v, w) ∈ relV ctx ρ /\ ⌈!v ≤ s⌉) /\
         (∀e', ⌈~>*# e 1 e'⌉ ===> 
                     match c with
                       | 0 => ⊥
                       | S c' =>
                         ▹ [] ((e', w) ∈ relE' relV τ wB c' s ρ)
                     end).
  
  Definition EWinl {ctx} t vw := (Einl (ctx := ctx) t (fst vw), Winl (ctx := ctx) (snd vw)).
  Definition EWinr {ctx} t vw := (Einr (ctx := ctx) t (fst vw), Winr (ctx := ctx) (snd vw)).
  Definition EWpair {ctx} a b := (Epair (ctx := ctx) (fst a) (fst b), Wpair (ctx := ctx) (snd a) (snd b)).

  Fixpoint relV {lctx} (τ : open_type lctx) ctx (ρ : csubsts lctx ctx) : rel 1 ctx :=
    match τ with
      | Tvar α => Rvar (csubsts_sem ρ α)
      | Tunit => \vw, ⌈vw ↓↓ Tunit⌉
      | τ₁ × τ₂ => \vw, ⌈vw ↓↓ ρ $$ τ⌉ /\ ∃a b, ⌈vw = EWpair a b⌉ /\ a ∈ relV τ₁ ρ /\ b ∈ relV τ₂ ρ
      | τ₁ + τ₂ => \vw, ⌈vw ↓↓ ρ $$ τ⌉ /\ ∃vw', (⌈vw = EWinl (ρ $ τ₂) vw'⌉ /\ vw' ∈ relV τ₁ ρ) \/ (⌈vw = EWinr (ρ $ τ₁) vw'⌉ /\ vw' ∈ relV τ₂ ρ)
      | Tarrow τ₁ c s τ₂ => \vw, ⌈vw ↓↓ ρ $$ τ⌉ /\ let (v, w) := vw in ∃τ₁' e, ⌈v = Eabs τ₁' e⌉ /\ ∃wB w₂, ⌈w = Wabs wB w₂⌉ /\ ∀vw₁ : wexpr, vw₁ ∈ relV τ₁ ρ ===> let (v₁, w₁) := vw₁ in (subst v₁ e, subst w₁ w₂) ∈ relE' (relV τ₂) τ₂ (subst w₁ wB) !(ρ $ subst !(!v₁) c) (ρ $ subst !(!v₁) s) (add vw₁ ρ)
      | Tuniversal c s τ₁ => \vw, ⌈vw ↓↓ ρ $$ τ⌉ /\ let (v, w) := vw in ∃e, ⌈v = Etabs e⌉ /\ ∃wB w₂, ⌈w = Wtabs wB w₂⌉ /\ ∀τ', ∀₂, VWSet τ' (Rvar #0) ===> (v $$ τ', w) ∈ relE' (relV τ₁) τ₁ wB !(ρ $ c) (ρ $ s) (add (τ', #0) (shift1 _ ρ))
      | Trecur τ₁ => @@, \vw, ⌈vw ↓↓ ρ $$ τ⌉ /\ let (v, w) := vw in ∃τ' v' w', ⌈v = Efold τ' v' /\ w = Wfold w'⌉ /\ ▹ [Some Usable] ((v', w') ∈ relV τ₁ (add (ρ $ τ, #0) (shift1 _ ρ)))
      | _ => \_, ⊥
    end.

  Definition relE {lctx} τ := relE' (lctx := lctx) (relV τ) τ.

End LR.

Fixpoint erel m :=
  match m with
    | 0 => Prop
    | S m' => wexpr -> erel m'
  end.

Fixpoint monotone {m} : (nat -> erel m) -> Prop :=
  match m return (nat -> erel m) -> Prop with
    | 0 => fun f => forall n, f n -> forall n', n' < n -> f n'
    | S m' => fun f => forall e, monotone (fun n => f n e)
  end.

Definition mono_erel m := { f : nat -> erel m | monotone f}.

Fixpoint const_erel (P : Prop) (m : nat) : erel m :=
  match m with
    | 0 => P
    | S m' => fun _ => const_erel P m'
  end.

Definition rsubsts : list relvart -> Prop.
  admit.
Defined.

Definition apply_rsubsts_var {m : nat} {ctx} : rsubsts ctx -> varR m ctx -> mono_erel m.
  admit.
Defined.

Instance Apply_rsubsts_var {m : nat} {ctx} : Apply (rsubsts ctx) (varR m ctx) (mono_erel m) :=
  {
    apply := apply_rsubsts_var
  }.

Definition add_rsubsts {m : nat} {u ctx} : mono_erel m -> rsubsts ctx -> rsubsts ((m, u) :: ctx).
  admit.
Defined.

Instance Add_rsubsts {m : nat} {u ctx} : Add (mono_erel m) (rsubsts ctx) (rsubsts ((m, u) :: ctx)) :=
  {
    add := add_rsubsts
  }.

Definition apply_rel_rel {m m' : nat} {u ctx} : rel m' ((m, u) :: ctx) -> rel m ctx -> rel m' ctx.
  admit.
Defined.

Instance Apply_rel_rel {m m' : nat} {u ctx} : Apply (rel m' ((m, u) :: ctx)) (rel m ctx) (rel m' ctx) :=
  {
    apply := apply_rel_rel
  }.

Definition imply (a b : Prop) : Prop := a -> b.
Infix "-->" := imply (at level 95, right associativity).

Require Import Bedrock.Platform.Cito.GeneralTactics4.

Definition shift_varR {m ctx} new n (xv : varR m ctx) : varR m (insert ctx n new).
  admit.
Qed.

Global Instance Shift_varR m : Shift (varR m) :=
  {
    shift := @shift_varR m
  }.

Inductive relsize :=
| RS1 : relsize
| RSadd (_ _ : relsize) : relsize
| RSbind T : (T -> relsize) -> relsize
| RSbinde : (wexpr -> relsize) -> relsize
.

Instance Add_relsize : Add relsize relsize relsize :=
  {
    add := RSadd
  }.

Definition RSadd1 := RSadd RS1.

Fixpoint rel2size {m ctx} (r : rel m ctx) : relsize :=
  match r with
    | Rvar _ _ _ => RS1
    | Rinj _ _ => RS1
    | Rand _ a b => rel2size a + rel2size b
    | Ror _ a b => rel2size a + rel2size b
    | Rimply _ a b => rel2size a + rel2size b
    | Rforall1 _ _ g => RSbind (fun x => rel2size (g x))
    | Rexists1 _ _ g => RSbind (fun x => rel2size (g x))
    | Rforall2 _ _ g => RSadd1 (rel2size g)
    | Rexists2 _ _ g => RSadd1 (rel2size g)
    | Rabs _ _ g => RSbinde (fun e => rel2size (g e))
    | Rapp _ _ a _ => RSadd1 (rel2size a)
    | Rrecur _ _ g => RSadd1 (rel2size g)
    | Rlater _ _ _ => RS1
  end.

Lemma guarded_size {m : nat} {ctx} (g : rel m ((m, Unusable) :: ctx)) : forall r, rel2size g = rel2size (g $ r).
  admit.
Qed.

Definition change_rsubsts chg {ctx} : rsubsts ctx -> rsubsts (change_usab chg ctx).
  admit.
Defined.

Definition interp' : forall (n : nat) {m ctx} (r : rel m ctx), rsubsts ctx -> erel m.
  refine
    (fix interp n {m ctx} (r : rel m ctx) (d : rsubsts ctx) : erel m :=
       match n with
         | 0 => const_erel True m
         | S n' =>
           (fix interp' n (rs : relsize) {ctx m} (r : rel m ctx) {struct rs} : rs = rel2size r -> rsubsts ctx -> erel m :=
              match rs with
                | RS1 => 
                  match r in rel m ctx return RS1 = rel2size r -> rsubsts ctx -> erel m with
                    | Rvar _ _ x => fun Heq d => ` (d $ x) n
                    | Rinj _ P => fun _ _ => P
                    | Rlater _ chg P => fun _ d => interp n' P (change_rsubsts chg d)
                    | _ => _
                  end
                | RSadd sa sb =>
                  match r in rel m ctx return RSadd sa sb = rel2size r -> rsubsts ctx -> erel m with
                    | Rand _ a b => fun Heq d => interp' n sa a _ d /\ interp' n sb b _ d
                    | Ror _ a b => fun Heq d => interp' n sa a _ d \/ interp' n sb b _ d
                    | Rimply _ a b => fun Heq d => (fun f : _ -> Prop => forall k, k <= n -> f k) (fun k => interp' k sa a _ d --> interp' k sb b _ d)
                    | Rforall2 _ (_, _) g => fun Heq d => (fun f : _ -> Prop => forall x, f x) (fun x => interp' n sb g _ (add x d))
                    | Rexists2 _ (_, _) g => fun Heq d => (fun f : _ -> Prop => exists x, f x) (fun x => interp' n sb g _ (add x d))
                    | Rapp _ _ r e => fun Heq d => interp' n sb r _ d e
                    | Rrecur _ m' g => fun Heq d => interp' n sb (g $ Rrecur g) _ d
                    | _ => _
                  end
                | RSbind _ sg =>
                  match r in rel m ctx return RSbind sg = rel2size r -> rsubsts ctx -> erel m with
                    | Rforall1 _ _ g => fun Heq d => (fun f => forall sx x (Heq_x : sx ~= x), (f sx x Heq_x : Prop)) (fun sx x Heq_x => interp' n (sg sx) (g x) _ d)
                    | Rexists1 _ _ g => fun Heq d => (fun f => exists sx x (Heq_x : sx ~= x), (f sx x Heq_x : Prop)) (fun sx x Heq_x => interp' n (sg sx) (g x) _ d)
                    | _ => _
                  end
                | RSbinde sg =>
                  match r in rel m ctx return RSbinde sg = rel2size r -> rsubsts ctx -> erel m with
                    | Rabs _ _ g => fun Heq d => fun e => interp' n (sg e) (g e) _ d
                    | _ => _
                  end
              end) n (rel2size r) _ _ r eq_refl d
       end); simpl in *; try solve [intros; discriminate | intros; inject Heq; eauto]; simpl in *.
  {
    inject Heq.
    eapply guarded_size.
  }
  {
    inject Heq; subst.
    dependent induction H; eauto.
  }
  {
    inject Heq; subst.
    dependent induction H; eauto.
  }
Defined.

Definition interp {ctx m} (r : rel m ctx) (d : rsubsts ctx) (n : nat) : erel m :=
  interp' n r d.

Lemma interp_monotone ctx m (r : rel m ctx) (d : rsubsts ctx) : monotone (interp r d).
  admit.
Qed.

Fixpoint open_term (domains : list Type) (range : Type) : Type :=
  match domains with
    | nil => range
    | domain :: domains' => domain -> open_term domains' range
  end.

Definition open_rel ctxfo m ctx := open_term ctxfo (rel m ctx).

Fixpoint openup1 {t1 t2} (f : t1 -> t2) {ctx} : open_term ctx t1 -> open_term ctx t2 :=
  match ctx return open_term ctx t1 -> open_term ctx t2 with
    | nil => fun r => f r
    | t :: ctx' => fun r x => openup1 f (r x)
  end.

Definition interp_open n {ctx m} d {ctxfo} : open_rel ctxfo m ctx -> open_term ctxfo (erel m) :=
  openup1 (fun r => interp r d n).

Fixpoint All ls :=
  match ls with
    | nil => True
    | P :: ls' => (P /\ All ls')%type
  end.

Fixpoint forall_ctx {ctxfo} : list (open_term ctxfo Prop) -> open_term ctxfo Prop -> Prop :=
  match ctxfo return list (open_term ctxfo Prop) -> open_term ctxfo Prop -> Prop with
    | nil => fun Ps P => All Ps -> P
    | t :: ctxfo' => fun Ps P => forall x, forall_ctx (map (flip apply_arrow x) Ps) (P x)
  end.

Definition valid {ctx ctxfo} : list (open_rel ctxfo 0 ctx) -> open_rel ctxfo 0 ctx -> Prop :=
  fun Ps P => forall n d, forall_ctx (map (interp_open n d) Ps) (interp_open n d P).

Infix "|~" := valid (at level 89, no associativity).

Lemma VCtxElimEmpty lctx ctx (f : csubsts lctx ctx -> open_rel [] 0 ctx) : (forall rho : csubsts lctx ctx, [] |~ f rho) -> forall ctxfo (rho : open_term ctxfo (csubsts lctx ctx)), [] |~ openup1 f rho.
Proof.
  intros H.
  induction ctxfo.
  {
    simpl; eauto.
  }
  {
    simpl.
    intros rho.
    unfold valid in *.
    simpl in *.
    intros n d x.
    eapply IHctxfo.
  }
Qed.

Definition open_csubsts ctxfo lctx ctx := open_term ctxfo (csubsts lctx ctx).
Notation t_ρ := open_csubsts (only parsing).

Definition shift_open_csubsts {ctxfo lctx ctx new} n (rho : open_csubsts ctxfo lctx ctx) : open_csubsts ctxfo lctx (insert ctx n new) := openup1 (shift new n) rho.

Instance Shift_open_csubsts {ctxfo lctx} : Shift (open_csubsts ctxfo lctx) :=
  {
    shift := @shift_open_csubsts ctxfo lctx
  }.

Definition add_pair_open_csubsts {ctxfo lctx ctx} p (rho : open_csubsts ctxfo lctx ctx) : open_csubsts ctxfo (CEtype :: lctx) ctx := openup1 (add_pair p) rho.

Global Instance Add_pair_open_csubsts {ctxfo lctx ctx} : Add (type * varR 1 ctx) (open_csubsts ctxfo lctx ctx) (open_csubsts ctxfo (CEtype :: lctx) ctx) :=
  {
    add := add_pair_open_csubsts
  }.

Definition t_Ps ctxfo ctx := list (open_rel ctxfo 0 ctx).

Definition shift_list `{Shift A T} ctx new n (ls : list (T ctx)) :=
  map (shift new n) ls.

Instance Shift_list `{Shift A T} : Shift (fun ctx => list (T ctx)) :=
  {
    shift := shift_list
  }.

Definition shift_rel {m ctx} new n (r : rel m ctx) : rel m (insert ctx n new).
  admit.
Defined.

Definition shift_open_rel {ctxfo m ctx} new n (r : open_rel ctxfo m ctx) : open_rel ctxfo m (insert ctx n new) := openup1 (shift_rel new n) r.

Instance Shift_open_rel {ctxfo m} : Shift (open_rel ctxfo m) :=
  {
    shift := @shift_open_rel ctxfo m
  }.

Fixpoint openup0 {T} (f : T) {ctx} : open_term ctx T :=
  match ctx return open_term ctx T with
    | nil => f
    | t :: ctx' => fun _ => openup0 f
  end.

Definition lift_Ps {ctxfo ctx} T (ls : t_Ps ctxfo ctx) : t_Ps (T :: ctxfo) ctx :=
  map (fun P => fun _ => P) ls.

Definition add_wexpr_open_csubsts {ctxfo lctx ctx} e (rho : open_csubsts ctxfo lctx ctx) : open_csubsts ctxfo (CEexpr :: lctx) ctx := openup1 (add_wexpr e) rho.

Global Instance Add_wexpr_open_csubsts {ctxfo lctx ctx} : Add wexpr (open_csubsts ctxfo lctx ctx) (open_csubsts ctxfo (CEexpr :: lctx) ctx) :=
  {
    add := add_wexpr_open_csubsts
  }.

Definition add_ρ_type {ctxfo lctx ctx} (ρ : t_ρ ctxfo lctx ctx) : t_ρ (type :: ctxfo) (CEtype :: lctx) ((1 : relvart) :: ctx) :=
  let ρ := shift1 (1 : relvart) ρ in
  let ρ := fun τ => add (τ, #0) ρ in
  ρ
.

Definition add_Ps_type {ctxfo ctx} (Ps : t_Ps ctxfo ctx) : t_Ps (type :: ctxfo) ((1 : relvart) :: ctx) :=
  let Ps := shift1 (1 : relvart) Ps in
  let Ps := lift_Ps type Ps in
  let Ps := (fun τ => openup0 (⌈kinding [] τ 0⌉ /\ VWSet τ (Rvar #0))%rel) :: Ps in
  Ps
.

Definition add_ρ_expr {ctxfo lctx ctx} (ρ : t_ρ ctxfo lctx ctx) : t_ρ (wexpr :: ctxfo) (CEexpr :: lctx) ctx :=
  let ρ := fun vw => add vw ρ in
  ρ
.

Definition add_Ps_expr {ctxfo lctx ctx} τ (Ps : t_Ps ctxfo ctx) (ρ : t_ρ ctxfo lctx ctx) : t_Ps (wexpr :: ctxfo) ctx :=
  let Ps := lift_Ps wexpr Ps in
  let Ps := (fun vw => openup1 (fun ρ => vw ∈ relV τ ρ)%rel ρ) :: Ps in
  Ps
.

Fixpoint make_ctxfo lctx :=
  match lctx with
    | nil => nil
    | e :: Γ' =>
      let ctxfo := make_ctxfo Γ' in
      match e with
        | CEtype =>
          type :: ctxfo
        | CEexpr =>
          wexpr :: ctxfo
      end
  end.

Fixpoint make_ctx lctx : list relvart :=
  match lctx with
    | nil => nil
    | e :: Γ' =>
      let ctx := make_ctx Γ' in
      match e with
        | CEtype =>
          (1 : relvart) :: ctx
        | CEexpr =>
          ctx
      end
  end.

Fixpoint make_ρ lctx : t_ρ (make_ctxfo lctx) lctx (make_ctx lctx) :=
  match lctx return t_ρ (make_ctxfo lctx) lctx (make_ctx lctx) with 
    | nil => []%CS
    | CEtype :: lctx' =>
      let ρ := make_ρ lctx' in
      add_ρ_type ρ
    | CEexpr :: lctx' =>
      let ρ := make_ρ lctx' in
      add_ρ_expr ρ
  end.

Definition pair_of_tc {t lctx} (T : tcontext (t :: lctx)) : tc_entry t lctx * tcontext lctx :=
  match T with
    | TCcons _ _ e T' => (e, T')
  end.

Fixpoint make_Ps {lctx} : tcontext lctx -> t_Ps (make_ctxfo lctx) (make_ctx lctx) :=
  match lctx return tcontext lctx -> t_Ps (make_ctxfo lctx) (make_ctx lctx) with 
    | nil => fun _ => nil
    | CEtype :: lctx' =>
      fun Γ =>
        let Ps := make_Ps (snd (pair_of_tc Γ)) in
        add_Ps_type Ps
    | CEexpr :: lctx' =>
      fun Γ =>
        let Ps := make_Ps (snd (pair_of_tc Γ)) in
        add_Ps_expr ((type_of_te << fst << pair_of_tc) Γ) Ps (make_ρ lctx')
  end.

Definition csubsts_width {t lctx ctx} : csubsts lctx ctx -> open_width t lctx -> open_width t [].
  admit.
Defined.

Global Instance Apply_csubsts_width_width {t ctx lctx} : Apply (csubsts lctx ctx) (open_width t lctx) (open_width t []) :=
  {
    apply := @csubsts_width _ _ _
  }.

Definition related {lctx} Γ wB w (e : open_expr lctx) τ (c : open_cexpr lctx) (s : open_size lctx) :=
  make_Ps (lctx := lctx) Γ |~ openup1 (fun ρ => (ρ $$ e, ρ $$ w) ∈ relE τ (ρ $ wB) !(ρ $ c) (ρ $ s) ρ)%rel (make_ρ lctx).

Notation "⊩" := related.

Local Notation open_econtext := econtext .
Local Notation econtext := (open_econtext []).

Lemma foundamental :
  forall {ctx} (Γ : tcontext ctx) e τ c s,
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
    Instance Apply_econtext_expr {ctx} : Apply (open_econtext ctx) (open_expr ctx) (open_expr ctx):=
      {
        apply := plug
      }.

    Open Scope rel.

    Instance Apply_Subst `{Subst t A B} {ctx} : Apply (B (t :: ctx)) (A ctx) (B ctx) :=
      {
        apply := flip subst
      }.

    Definition relEC (E : econtext) e we (wEe : width) (wBEe : open_width WTnat []) (s₁ : size) (c₂ : cexpr) (s₂ : size) {lctx lctx'} (τ : open_type lctx) (τ' : open_type lctx') ctx (ρ : csubsts lctx ctx) (ρ' : csubsts lctx' ctx) : rel 0 ctx :=
      ∀v we', (v, we') ∈ relV τ ρ /\ ⌈e ~>* v /\ !v ≤ s₁ /\ wsteps we we'⌉ ===> (E $ v, wEe) ∈ relE τ' wBEe !c₂ s₂ ρ'.

(*
    Inductive typingEC : econtext -> type -> type -> Prop :=
    | TECempty τ : typingEC ECempty τ τ
    | TECapp1 f arg τ τ₁ c s τ₂ :
        typingEC f τ (Tarrow τ₁ c s τ₂) ->
        (|- arg τ₁) ->
        typingEC (ECapp1 f arg) τ τ₂
    .
 *)
  
    Global Instance Add_width_width lctx : Add (open_width WTnat lctx) (open_width WTnat lctx)(open_width WTnat lctx) :=
      {
        add := Wbinop add
      }.

    Lemma LRbind E (wEe : width) (wBEe : open_width WTnat []) s₁ c₂ s₂ {lctx lctx'} (τ : open_type lctx) (τ' : open_type lctx') ctx (ρ : csubsts lctx ctx) (ρ' : csubsts lctx' ctx) :
      valid (ctxfo := []) [] 
            (∀e we c₁ wBe, 
               ((e, we) ∈ relE τ wBe c₁ s₁ ρ /\ 
                relEC E e we wEe wBEe s₁ c₂ s₂ τ τ' ρ ρ') ===> 
                (E $$ e, wEe) ∈ relE τ' (wBe + wBEe) (c₁ + !c₂) s₂ ρ').
    Proof.
      Lemma VLob {ctxfo ctx} Ps (P : open_rel ctxfo 0 ctx) : openup1 (▹ []) P :: Ps |~ P -> Ps |~ P.
        admit.
      Qed.
      
      eapply VLob.
      (*
      eapply Vforall1intro; intros e.
      eapply Vforall1intro; intros c₁.
      Lemma VImplyIntro P Q : (|~ P -> |~ Q) -> |~ P ===> Q.
        admit.
      Qed.
      eapply VImplyIntro; intros H.
      Local Open Scope type.
      Lemma VAndElim P Q : |~ P /\ Q -> (|~ P) /\ (|~ Q).
        admit.
      Qed.
      eapply VAndElim in H; destruct H as [He Hec].
      unfold goodEC.

      Definition apply_Substs {lctx} `{H : Apply (flip csubsts lctx (const unit)) (B lctx) B'} (rho : Substs [] lctx) (b : B lctx) : B' :=
        rho (const unit) $ b.

      Global Instance Apply_Substs {lctx} `{H : Apply (csubsts (const unit) lctx) (B lctx) B'} : Apply (Substs [] lctx) (B lctx) B' :=
        {
          apply := apply_Substs (H := H)
        }.

      Lemma goodExprIntro {lctx} e B (τ : open_type lctx) c s (ρ : Substs [] lctx) : 
        (|- e (ρ $ τ)) -> 
        (forall n e', ~>## e n 0 e' -> n <= c) ->
        (forall v, ⇓*# e 0 v -> !v <= s /\ |~ v ∈ goodValue B τ ρ) ->
        (forall e', ~>*# e 1 e' -> 0 < c /\ |~ ▹(e' ∈ goodExpr B τ (c - 1) s ρ)) ->
        |~ e ∈ goodExpr B τ c s ρ.
      Proof.
        admit.
      Qed.
      unfold goodExpr.
      unfold openE.
      simpl.
      unfold relE.
      unfold relE'.
      simpl.
       *)
      admit.
    Qed.

    unfold related in *.

    Global Instance Apply_csubsts_econtext_econtext {ctx} lctx : Apply (csubsts lctx ctx) (open_econtext lctx) econtext.
      admit.
    Defined.

    Global Instance Apply_csubsts_cexpr_cexpr' {ctx} lctx' lctx : Apply (csubsts lctx ctx) (open_cexpr (lctx' :: lctx)) (open_cexpr [lctx']).
      admit.
    Defined.

    Global Instance Apply_csubsts_size_size' {ctx} lctx' lctx : Apply (csubsts lctx ctx) (open_size (lctx' :: lctx)) (open_size [lctx']).
      admit.
    Defined.

    Global Instance Apply_csubsts_width_width' {t ctx lctx' lctx} : Apply (csubsts lctx ctx) (open_width t (lctx' :: lctx)) (open_width t [lctx']).
      admit.
    Defined.

    Lemma LRbind' {lctx} (e : open_expr lctx) (we : open_width WTstruct lctx) (wBe : open_width WTnat lctx) (E : open_econtext lctx) (wEe : open_width WTstruct lctx) (wBEe : open_width WTnat lctx) (c₁ : open_cexpr lctx) (s₁ : open_size lctx) (c₂ : open_cexpr lctx) (s₂ : open_size lctx) (τ : open_type lctx) (τ' : open_type lctx) {ctxfo ctx} (ρ : open_csubsts ctxfo lctx ctx) (Ps : list (open_rel ctxfo 0 ctx)) :
      Ps |~ openup1 (fun ρ => (ρ $ e, ρ $ we) ∈ relE τ (ρ $ wBe) !(ρ $ c₁) (ρ $ s₁) ρ) ρ ->
      Ps |~ openup1 (fun ρ => relEC (ρ $ E) (ρ $ e) (ρ $ we) (ρ $ wEe) (ρ $ wBEe) (ρ $ s₁) (ρ $ c₂) (ρ $ s₂) τ τ' ρ ρ) ρ ->
      Ps |~ openup1 (fun ρ => (ρ $ (E $ e), ρ $ wEe) ∈ relE τ' ((ρ $ (wBe + wBEe))) !(ρ $ (c₁ + c₂)) (ρ $ s₂) ρ) ρ.
    Proof.
      admit.
    Qed.
    
    destruct IHtyping1 as [wB₀ [w₀ IH₀]].
    destruct IHtyping2 as [wB₁ [w₁ IH₁]].

    exists (wB₀ + (wB₁ + (Wconst 1 + WappB w₀ w₁))).
    exists (Wapp w₀ w₁).

    eapply LRbind' with (wEe := Wapp w₀ w₁) (wBEe := wB₁ + (Wconst 1 + WappB w₀ w₁)) (c₂ := c₁ + subst s₁ c) (s₂ := subst s₁ s) (E := ECapp1 ECempty e₁) (τ' := subst s₁ τ₂) in IH₀.
    {
      eapply IH₀.
    }
    {
      unfold relEC.
      Definition make_var {m ctx} n (P : ceb (nth_error ctx n) (Some m) = true) : var m ctx := Var n P.
      Definition var0 {m ctx} : var m (m :: ctx).
        refine ((make_var (ctx := m%nat :: _) (m := m) 0 _)).
        eapply ceb_iff.
        eauto.
      Defined.
      Notation "#0" := var0.

      Lemma rearrange {ctxfo lctx ctx} (ρ : open_csubsts ctxfo lctx ctx) (Ps : list (open_rel ctxfo 0 ctx)) (τ₁ : open_type lctx) (c : open_cexpr (CEexpr :: lctx)) (s : open_size (CEexpr :: lctx)) (τ₂ : open_type (CEexpr :: lctx)) (e₀ e₁ : open_expr lctx) (nouse : open_size lctx) (w₀ w₁: open_width WTstruct lctx) (c₁ : open_cexpr lctx) (s₁ : open_size lctx) (wB₁ : open_width WTnat lctx) :
        openup1
          (fun ρ : csubsts (CEexpr :: lctx) ctx =>
             let v := ρ $ (Evar #0) in
             let we' := ρ $ (Wvar #0) in
             ((v, we') ∈ relV (shift1 _ (Tarrow τ₁ c s τ₂)) ρ /\ ⌈ρ $$ shift1 _ e₀ ~>* v /\ !v ≤ ρ $$ shift1 _ nouse /\ wsteps (ρ $$ shift1 _ w₀) we' ⌉))
          ((fun vw => openup1 (add vw) ρ) : open_csubsts (wexpr :: ctxfo) _ _) :: lift_Ps wexpr Ps
          |~ 
          openup1
          (fun ρ : csubsts (CEexpr :: lctx) ctx =>
             (ρ $$ Eapp (Evar #0) (shift1 _ e₁), ρ $$ shift1 _ (Wapp w₀ w₁))
               ∈ relE (shift1 _ (subst s₁ τ₂)) (ρ $$ (shift1 _ wB₁ + shift1 _ (Wconst 1 + WappB w₀ w₁)))
               !(ρ $$ (shift1 _ c₁ + shift1 _ (subst s₁ c))) (ρ $$ shift1 _ (subst s₁ s)) ρ)
          ((fun vw => openup1 (add vw) ρ) : open_csubsts (wexpr :: ctxfo) _ _) 
        ->
        Ps |~ openup1
           (fun ρ =>
              ∀(v : expr) (we' : width),
                (v, we') ∈ relV (Tarrow τ₁ c s τ₂) ρ /\ ⌈ρ $$ e₀ ~>* v /\ !v ≤ ρ $$ nouse /\ wsteps (ρ $$ w₀) we' ⌉ ===> (ρ $$ ECapp1 ECempty e₁ $$ v, ρ $$ Wapp w₀ w₁)  ∈ relE (subst s₁ τ₂) (ρ $$ (wB₁ + (Wconst 1 + WappB w₀ w₁))) !(ρ $$ (c₁ + subst s₁ c)) (ρ $$ subst s₁ s) ρ) ρ
      .
      Proof.
        Definition pair_of_csubsts {lctx ctx} (ρ : csubsts (CEexpr :: lctx) ctx) : wexpr * csubsts lctx ctx.
          admit.
        Qed.

        Lemma forall1intro {ctxfo lctx ctx} (ρ : open_csubsts ctxfo lctx ctx) (f : expr -> width -> csubsts lctx ctx -> rel 0 ctx) Ps :
          lift_Ps wexpr Ps |~ openup1 
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

        intros H.
        eapply forall1intro.
        Lemma imply_intro {ctxfo lctx ctx} (ρ : open_csubsts ctxfo lctx ctx) (P Q : csubsts lctx ctx -> rel 0 ctx) Ps :
          openup1 P ρ :: Ps |~ openup1 Q ρ ->
          Ps |~ openup1 (fun ρ => P ρ ===> Q ρ) ρ.
          admit.
        Qed.
        eapply imply_intro.
        Lemma snd_pair_of_csubsts_cexpr {lctx ctx} (rho : csubsts (CEexpr :: lctx) ctx) (x : open_cexpr lctx) : snd (pair_of_csubsts rho) $$ x = rho $$ (shift1 CEexpr x).
          admit.
        Qed.
        Lemma snd_pair_of_csubsts_cexpr' {lctx ctx} (rho : csubsts (CEexpr :: lctx) ctx) (x : open_cexpr lctx) : csubsts_cexpr (snd (pair_of_csubsts rho)) x = csubsts_cexpr rho (shift1 CEexpr x).
          admit.
        Qed.
        simpl.
        (* erewrite snd_pair_of_csubsts_cexpr. *)
        (* erewrite snd_pair_of_csubsts_cexpr'. *)
        admit.
      Qed.

      eapply rearrange.

      (*here*)
      simpl.
      (*here*)
      simpl.
      eapply LRbind' in IH₁.
      Focus 2.
    }
    Lemma LRapp {lctx ctx} (ρ : csubsts lctx ctx) : 
      valid (ctxfo := []) [] 
            (∀ (e₀ : expr) (w₀ : width) (τ₁ : open_type lctx) (c : open_cexpr (CEexpr :: lctx)) (s : open_size (CEexpr :: lctx)) (τ₂ : open_type (CEexpr :: lctx)) (B₀ : nat) (c₀ : cexpr) nouse (e₁ : expr) (w₁ : width) (B₁ : nat) (c₁ : cexpr) (s₁ : open_size lctx),
               (e₀, w₀) ∈ relE (Tarrow τ₁ c s τ₂) B₀ !c₀ nouse ρ ===> 
               (e₁, w₁) ∈ relE τ₁ B₁ !c₁ (ρ $ s₁) ρ ===> 
               ∃(w : open_width WTstruct [CEexpr]) (wB : open_width WTnat [CEexpr]) (B : nat), ⌈wsteps w₀ (Wabs wB w) /\ wsteps (wB $ w₁) (Wconst B)⌉ /\ (e₀ $ e₁, w $ w₁) ∈ relE (τ₂ $ s₁) (B₀ + B₁ + 1 + B) (!c₀ + !c₁ + !(ρ $ (c $ s₁))) (ρ $ (s $ s₁)) ρ).
    Proof.
      admit.
    Qed.

    Lemma VMorePs ctxfo ctx (P : open_rel ctxfo 0 ctx) Ps : [] |~ P -> Ps |~ P.
      admit.
    Qed.

    Instance Max_nat : Max nat :=
      {
        max := Peano.max
      }.
    exists (3 * max B0 B1 + 1).

    eapply VMorePs.
    eapply VCtxElimEmpty.
    intros ρ.

    admit.
  }
  {
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

  Lemma VMono Ps P : Ps |~ P -> Ps |~ ▹P.
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

  Fixpoint Funvar_pointwise_relation {var t} (R : t var -> t var -> Prop) {ctx} : Funvar var ctx t -> Funvar var ctx t -> Prop :=
    match ctx return Funvar var ctx t -> Funvar var ctx t -> Prop with
      | nil => R
      | t' :: ctx' => fun a b => forall x, Funvar_pointwise_relation R (a x) (b x)
    end.

  Definition Funvar_eq {var t ctx} (a b : Funvar var ctx t) := Funvar_pointwise_relation eq a b.

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

