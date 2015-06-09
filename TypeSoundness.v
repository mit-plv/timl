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

  (* ToDo: need to change wtyping to require that when τ doesn't contain arrows, w can only be Wtt *)
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
Definition valueOf e τ := IsValue e /\ |- e τ.
Infix "↓" := valueOf (at level 51).

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

Definition runsto e v := e ~>* v /\ IsValue v.
Infix "⇓" := runsto (at level 51).

Definition runstoEx e m v := ~>*# e m v /\ IsValue v.
Notation "⇓*#" := runstoEx.

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
Notation "⌈ P ⌉" := (Rinj P) (format "⌈ P ⌉") : rel.
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

Definition IsWValue : forall t ctx, open_width t ctx -> Prop.
  admit.
Qed.

Definition wrunsto {t} (w w' : open_width t []) := (wsteps w w' /\ IsWValue w')%type.
Definition wvalueOf (w : width) τ := wtyping [] w !τ /\ IsWValue w.
Definition typingew (ew : wexpr) τ := let (e, w) := ew in e ↓ τ /\ wvalueOf w τ.
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
         (∀v w', ⌈e ⇓ v /\ wrunsto w w'⌉%type ===> (v, w') ∈ relV ctx ρ /\ ⌈!v ≤ s⌉) /\
         (∀e', ⌈~>*# e 1 e' /\ exists w', wrunsto w w'⌉ ===> 
                     match c with
                       | 0 => ⊥
                       | S c' =>
                         ▹ [] ((e', w) ∈ relE' relV τ wB c' s ρ)
                     end) /\
         ⌈exists v, e ⇓ v⌉ /\
         ⌈exists w', wrunsto w w'⌉
  .
  
  Definition EWinl {ctx} t vw := (Einl (ctx := ctx) t (fst vw), Winl (ctx := ctx) (snd vw)).
  Definition EWinr {ctx} t vw := (Einr (ctx := ctx) t (fst vw), Winr (ctx := ctx) (snd vw)).
  Definition EWpair {ctx} a b := (Epair (ctx := ctx) (fst a) (fst b), Wpair (ctx := ctx) (snd a) (snd b)).

  Fixpoint relV {lctx} (τ : open_type lctx) ctx (ρ : csubsts lctx ctx) : rel 1 ctx :=
    match τ with
      | Tvar α => Rvar (csubsts_sem ρ α)
      | Tunit => \vw, ⌈vw ↓↓ Tunit⌉
      | τ₁ × τ₂ => \vw, ⌈vw ↓↓ ρ $$ τ⌉ /\ ∃a b, ⌈vw = EWpair a b⌉ /\ a ∈ relV τ₁ ρ /\ b ∈ relV τ₂ ρ
      | τ₁ + τ₂ => \vw, ⌈vw ↓↓ ρ $$ τ⌉ /\ ∃vw', (⌈vw = EWinl (ρ $ τ₂) vw'⌉ /\ vw' ∈ relV τ₁ ρ) \/ (⌈vw = EWinr (ρ $ τ₁) vw'⌉ /\ vw' ∈ relV τ₂ ρ)
      | Tarrow τ₁ c s τ₂ => \vw, ⌈vw ↓↓ ρ $$ τ⌉ /\ let (v, w) := vw in ∃e, ⌈exists τ₁', v = Eabs τ₁' e⌉ /\ ∃wB w₂, ⌈w = Wabs wB w₂⌉ /\ ∀vw₁ : wexpr, vw₁ ∈ relV τ₁ ρ ===> let (v₁, w₁) := vw₁ in (subst v₁ e, subst w₁ w₂) ∈ relE' (relV τ₂) τ₂ (subst w₁ wB) !(ρ $ subst !(!v₁) c) (ρ $ subst !(!v₁) s) (add vw₁ ρ)
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
Infix "--->" := imply (at level 95, right associativity).

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
                    | Rimply _ a b => fun Heq d => (fun f : _ -> Prop => forall k, k <= n -> f k) (fun k => interp' k sa a _ d ---> interp' k sb b _ d)
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

Notation open_csubsts := (fun ctxfo lctx ctx => open_term ctxfo (csubsts lctx ctx)).
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

Definition liftPs1 {ctxfo ctx} T (ls : t_Ps ctxfo ctx) : t_Ps (T :: ctxfo) ctx :=
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
  let Ps := liftPs1 type Ps in
  let Ps := (fun τ => openup0 (⌈kinding [] τ 0⌉ /\ VWSet τ (Rvar #0))%rel) :: Ps in
  Ps
.

Definition add_ρ_expr {ctxfo lctx ctx} (ρ : t_ρ ctxfo lctx ctx) : t_ρ (wexpr :: ctxfo) (CEexpr :: lctx) ctx :=
  let ρ := fun vw => add vw ρ in
  ρ
.

Definition add_Ps_expr {ctxfo lctx ctx} τ (Ps : t_Ps ctxfo ctx) (ρ : t_ρ ctxfo lctx ctx) : t_Ps (wexpr :: ctxfo) ctx :=
  let Ps := liftPs1 wexpr Ps in
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

Notation width_nat := (open_width WTnat []).
Local Notation open_econtext := econtext .
Local Notation econtext := (open_econtext []).

Fixpoint openup2 {t1 t2 t3} {ctx} (f : t1 -> t2 -> t3) : open_term ctx t1 -> open_term ctx t2 -> open_term ctx t3 :=
  match ctx return open_term ctx t1 -> open_term ctx t2 -> open_term ctx t3 with
    | nil => f
    | t :: ctx' => fun r1 r2 x => openup2 f (r1 x) (r2 x)
  end.

Fixpoint openup3 {t1 t2 t3 t4} (f : t1 -> t2 -> t3 -> t4) {ctx} : open_term ctx t1 -> open_term ctx t2 -> open_term ctx t3 -> open_term ctx t4 :=
  match ctx return open_term ctx t1 -> open_term ctx t2 -> open_term ctx t3 -> open_term ctx t4 with
    | nil => f
    | t :: ctx' => fun r1 r2 r3 x => openup3 f (r1 x) (r2 x) (r3 x)
  end.

Fixpoint openup4 {t1 t2 t3 t4 t5} (f : t1 -> t2 -> t3 -> t4 -> t5) {ctx} : open_term ctx t1 -> open_term ctx t2 -> open_term ctx t3 -> open_term ctx t4 -> open_term ctx t5 :=
  match ctx return open_term ctx t1 -> open_term ctx t2 -> open_term ctx t3 -> open_term ctx t4 -> open_term ctx t5 with
    | nil => f
    | t :: ctx' => fun r1 r2 r3 r4 x => openup4 f (r1 x) (r2 x) (r3 x) (r4 x)
  end.

Fixpoint openup5 {t1 t2 t3 t4 t5 t6} {ctx} (f : t1 -> t2 -> t3 -> t4 -> t5 -> t6) : open_term ctx t1 -> open_term ctx t2 -> open_term ctx t3 -> open_term ctx t4 -> open_term ctx t5 -> open_term ctx t6 :=
  match ctx return open_term ctx t1 -> open_term ctx t2 -> open_term ctx t3 -> open_term ctx t4 -> open_term ctx t5 -> open_term ctx t6 with
    | nil => f
    | t :: ctx' => fun r1 r2 r3 r4 r5 x => openup5 f (r1 x) (r2 x) (r3 x) (r4 x) (r5 x)
  end.

Fixpoint openup6 {t1 t2 t3 t4 t5 t6 t7} (f : t1 -> t2 -> t3 -> t4 -> t5 -> t6 -> t7) {ctx} : open_term ctx t1 -> open_term ctx t2 -> open_term ctx t3 -> open_term ctx t4 -> open_term ctx t5 -> open_term ctx t6 -> open_term ctx t7 :=
  match ctx return open_term ctx t1 -> open_term ctx t2 -> open_term ctx t3 -> open_term ctx t4 -> open_term ctx t5 -> open_term ctx t6 -> open_term ctx t7 with
    | nil => f
    | t :: ctx' => fun r1 r2 r3 r4 r5 r6 x => openup6 f (r1 x) (r2 x) (r3 x) (r4 x) (r5 x) (r6 x)
  end.

Fixpoint openup7 {t1 t2 t3 t4 t5 t6 t7 t8} (f : t1 -> t2 -> t3 -> t4 -> t5 -> t6 -> t7 -> t8) {ctx} : open_term ctx t1 -> open_term ctx t2 -> open_term ctx t3 -> open_term ctx t4 -> open_term ctx t5 -> open_term ctx t6 -> open_term ctx t7 -> open_term ctx t8 :=
  match ctx return open_term ctx t1 -> open_term ctx t2 -> open_term ctx t3 -> open_term ctx t4 -> open_term ctx t5 -> open_term ctx t6 -> open_term ctx t7 -> open_term ctx t8 with
    | nil => f
    | t :: ctx' => fun r1 r2 r3 r4 r5 r6 r7 x => openup7 f (r1 x) (r2 x) (r3 x) (r4 x) (r5 x) (r6 x) (r7 x)
  end.

Fixpoint openup8 {t1 t2 t3 t4 t5 t6 t7 t8 t9} (f : t1 -> t2 -> t3 -> t4 -> t5 -> t6 -> t7 -> t8 -> t9) {ctx} : open_term ctx t1 -> open_term ctx t2 -> open_term ctx t3 -> open_term ctx t4 -> open_term ctx t5 -> open_term ctx t6 -> open_term ctx t7 -> open_term ctx t8 -> open_term ctx t9 :=
  match ctx return open_term ctx t1 -> open_term ctx t2 -> open_term ctx t3 -> open_term ctx t4 -> open_term ctx t5 -> open_term ctx t6 -> open_term ctx t7 -> open_term ctx t8 -> open_term ctx t9 with
    | nil => f
    | t :: ctx' => fun r1 r2 r3 r4 r5 r6 r7 r8 x => openup8 f (r1 x) (r2 x) (r3 x) (r4 x) (r5 x) (r6 x) (r7 x) (r8 x)
  end.

Lemma openup2_totop1 {t0 t1 t2} {f : t0 -> t1 -> t2} {ctxfo x0 x1} : openup2 (ctx := ctxfo) f x0 x1 = openup2 (fun x1 x0 => f x0 x1) x1 x0.
  admit.
Qed.
Lemma openup3_totop1 {t0 t1 t2 t3} {f : t0 -> t1 -> t2 -> t3} {ctxfo x0 x1 x2} : openup3 (ctx := ctxfo) f x0 x1 x2 = openup3 (fun x1 x0 x2 => f x0 x1 x2) x1 x0 x2.
  admit.
Qed.
Lemma openup3_totop2 {t0 t1 t2 t3} {f : t0 -> t1 -> t2 -> t3} {ctxfo x0 x1 x2} : openup3 (ctx := ctxfo) f x0 x1 x2 = openup3 (fun x2 x0 x1 => f x0 x1 x2) x2 x0 x1.
  admit.
Qed.
Lemma openup4_totop1 {t0 t1 t2 t3 t4} {f : t0 -> t1 -> t2 -> t3 -> t4} {ctxfo x0 x1 x2 x3} : openup4 (ctx := ctxfo) f x0 x1 x2 x3 = openup4 (fun x1 x0 x2 x3 => f x0 x1 x2 x3) x1 x0 x2 x3.
  admit.
Qed.
Lemma openup4_totop2 {t0 t1 t2 t3 t4} {f : t0 -> t1 -> t2 -> t3 -> t4} {ctxfo x0 x1 x2 x3} : openup4 (ctx := ctxfo) f x0 x1 x2 x3 = openup4 (fun x2 x0 x1 x3 => f x0 x1 x2 x3) x2 x0 x1 x3.
  admit.
Qed.
Lemma openup4_totop3 {t0 t1 t2 t3 t4} {f : t0 -> t1 -> t2 -> t3 -> t4} {ctxfo x0 x1 x2 x3} : openup4 (ctx := ctxfo) f x0 x1 x2 x3 = openup4 (fun x3 x0 x1 x2 => f x0 x1 x2 x3) x3 x0 x1 x2.
  admit.
Qed.

Lemma openup5_totop1 {t0 t1 t2 t3 t4 t5} {f : t0 -> t1 -> t2 -> t3 -> t4 -> t5} {ctxfo x0 x1 x2 x3 x4} : openup5 (ctx := ctxfo) f x0 x1 x2 x3 x4 = openup5 (fun x1 x0 x2 x3 x4 => f x0 x1 x2 x3 x4) x1 x0 x2 x3 x4.
  admit.
Qed.
Lemma openup5_totop2 {t0 t1 t2 t3 t4 t5} {f : t0 -> t1 -> t2 -> t3 -> t4 -> t5} {ctxfo x0 x1 x2 x3 x4} : openup5 (ctx := ctxfo) f x0 x1 x2 x3 x4 = openup5 (fun x2 x0 x1 x3 x4 => f x0 x1 x2 x3 x4) x2 x0 x1 x3 x4.
  admit.
Qed.
Lemma openup5_totop3 {t0 t1 t2 t3 t4 t5} {f : t0 -> t1 -> t2 -> t3 -> t4 -> t5} {ctxfo x0 x1 x2 x3 x4} : openup5 (ctx := ctxfo) f x0 x1 x2 x3 x4 = openup5 (fun x3 x0 x1 x2 x4 => f x0 x1 x2 x3 x4) x3 x0 x1 x2 x4.
  admit.
Qed.
Lemma openup5_totop4 {t0 t1 t2 t3 t4 t5} {f : t0 -> t1 -> t2 -> t3 -> t4 -> t5} {ctxfo x0 x1 x2 x3 x4} : openup5 (ctx := ctxfo) f x0 x1 x2 x3 x4 = openup5 (fun x4 x0 x1 x2 x3 => f x0 x1 x2 x3 x4) x4 x0 x1 x2 x3.
  admit.
Qed.

Lemma openup6_totop1 {t0 t1 t2 t3 t4 t5 t6} {f : t0 -> t1 -> t2 -> t3 -> t4 -> t5 -> t6} {ctxfo x0 x1 x2 x3 x4 x5} : openup6 (ctx := ctxfo) f x0 x1 x2 x3 x4 x5 = openup6 (fun x1 x0 x2 x3 x4 x5 => f x0 x1 x2 x3 x4 x5) x1 x0 x2 x3 x4 x5.
  admit.
Qed.
Lemma openup6_totop2 {t0 t1 t2 t3 t4 t5 t6} {f : t0 -> t1 -> t2 -> t3 -> t4 -> t5 -> t6} {ctxfo x0 x1 x2 x3 x4 x5} : openup6 (ctx := ctxfo) f x0 x1 x2 x3 x4 x5 = openup6 (fun x2 x0 x1 x3 x4 x5 => f x0 x1 x2 x3 x4 x5) x2 x0 x1 x3 x4 x5.
  admit.
Qed.
Lemma openup6_totop3 {t0 t1 t2 t3 t4 t5 t6} {f : t0 -> t1 -> t2 -> t3 -> t4 -> t5 -> t6} {ctxfo x0 x1 x2 x3 x4 x5} : openup6 (ctx := ctxfo) f x0 x1 x2 x3 x4 x5 = openup6 (fun x3 x0 x1 x2 x4 x5 => f x0 x1 x2 x3 x4 x5) x3 x0 x1 x2 x4 x5.
  admit.
Qed.
Lemma openup6_totop4 {t0 t1 t2 t3 t4 t5 t6} {f : t0 -> t1 -> t2 -> t3 -> t4 -> t5 -> t6} {ctxfo x0 x1 x2 x3 x4 x5} : openup6 (ctx := ctxfo) f x0 x1 x2 x3 x4 x5 = openup6 (fun x4 x0 x1 x2 x3 x5 => f x0 x1 x2 x3 x4 x5) x4 x0 x1 x2 x3 x5.
  admit.
Qed.
Lemma openup6_totop5 {t0 t1 t2 t3 t4 t5 t6} {f : t0 -> t1 -> t2 -> t3 -> t4 -> t5 -> t6} {ctxfo x0 x1 x2 x3 x4 x5} : openup6 (ctx := ctxfo) f x0 x1 x2 x3 x4 x5 = openup6 (fun x5 x0 x1 x2 x3 x4 => f x0 x1 x2 x3 x4 x5) x5 x0 x1 x2 x3 x4.
  admit.
Qed.

Lemma openup7_totop1 {t0 t1 t2 t3 t4 t5 t6 t7} {f : t0 -> t1 -> t2 -> t3 -> t4 -> t5 -> t6 -> t7} {ctxfo x0 x1 x2 x3 x4 x5 x6} : openup7 (ctx := ctxfo) f x0 x1 x2 x3 x4 x5 x6 = openup7 (fun x1 x0 x2 x3 x4 x5 x6 => f x0 x1 x2 x3 x4 x5 x6) x1 x0 x2 x3 x4 x5 x6.
  admit.
Qed.
Lemma openup7_totop2 {t0 t1 t2 t3 t4 t5 t6 t7} {f : t0 -> t1 -> t2 -> t3 -> t4 -> t5 -> t6 -> t7} {ctxfo x0 x1 x2 x3 x4 x5 x6} : openup7 (ctx := ctxfo) f x0 x1 x2 x3 x4 x5 x6 = openup7 (fun x2 x0 x1 x3 x4 x5 x6 => f x0 x1 x2 x3 x4 x5 x6) x2 x0 x1 x3 x4 x5 x6.
  admit.
Qed.
Lemma openup7_totop3 {t0 t1 t2 t3 t4 t5 t6 t7} {f : t0 -> t1 -> t2 -> t3 -> t4 -> t5 -> t6 -> t7} {ctxfo x0 x1 x2 x3 x4 x5 x6} : openup7 (ctx := ctxfo) f x0 x1 x2 x3 x4 x5 x6 = openup7 (fun x3 x0 x1 x2 x4 x5 x6 => f x0 x1 x2 x3 x4 x5 x6) x3 x0 x1 x2 x4 x5 x6.
  admit.
Qed.
Lemma openup7_totop4 {t0 t1 t2 t3 t4 t5 t6 t7} {f : t0 -> t1 -> t2 -> t3 -> t4 -> t5 -> t6 -> t7} {ctxfo x0 x1 x2 x3 x4 x5 x6} : openup7 (ctx := ctxfo) f x0 x1 x2 x3 x4 x5 x6 = openup7 (fun x4 x0 x1 x2 x3 x5 x6 => f x0 x1 x2 x3 x4 x5 x6) x4 x0 x1 x2 x3 x5 x6.
  admit.
Qed.

Lemma openup8_totop1 {t0 t1 t2 t3 t4 t5 t6 t7 t8} {f : t0 -> t1 -> t2 -> t3 -> t4 -> t5 -> t6 -> t7 -> t8} {ctxfo x0 x1 x2 x3 x4 x5 x6 x7} : openup8 (ctx := ctxfo) f x0 x1 x2 x3 x4 x5 x6 x7 = openup8 (fun x1 x0 x2 x3 x4 x5 x6 x7 => f x0 x1 x2 x3 x4 x5 x6 x7) x1 x0 x2 x3 x4 x5 x6 x7.
  admit.
Qed.
Lemma openup8_totop2 {t0 t1 t2 t3 t4 t5 t6 t7 t8} {f : t0 -> t1 -> t2 -> t3 -> t4 -> t5 -> t6 -> t7 -> t8} {ctxfo x0 x1 x2 x3 x4 x5 x6 x7} : openup8 (ctx := ctxfo) f x0 x1 x2 x3 x4 x5 x6 x7 = openup8 (fun x2 x0 x1 x3 x4 x5 x6 x7 => f x0 x1 x2 x3 x4 x5 x6 x7) x2 x0 x1 x3 x4 x5 x6 x7.
  admit.
Qed.
Lemma openup8_totop6 {t0 t1 t2 t3 t4 t5 t6 t7 t8} {f : t0 -> t1 -> t2 -> t3 -> t4 -> t5 -> t6 -> t7 -> t8} {ctxfo x0 x1 x2 x3 x4 x5 x6 x7} : openup8 (ctx := ctxfo) f x0 x1 x2 x3 x4 x5 x6 x7 = openup8 (fun x6 x0 x1 x2 x3 x4 x5 x7 => f x0 x1 x2 x3 x4 x5 x6 x7) x6 x0 x1 x2 x3 x4 x5 x7.
  admit.
Qed.

Lemma openup8_shrink t1 t2 t3 t4 t5 t6 t7 t8 t9 (f : t2 -> t3 -> t4 -> t5 -> t6 -> t7 -> t8 -> t9) ctxfo x1 x2 x3 x4 x5 x6 x7 x8 : openup8 (ctx := ctxfo) (fun (_ : t1) x2 x3 x4 x5 x6 x7 x8 => f x2 x3 x4 x5 x6 x7 x8) x1 x2 x3 x4 x5 x6 x7 x8 = openup7 f x2 x3 x4 x5 x6 x7 x8.
  admit.
Qed.
Lemma openup7_shrink t1 t2 t3 t4 t5 t6 t7 t8 (f : t2 -> t3 -> t4 -> t5 -> t6 -> t7 -> t8) ctxfo x1 x2 x3 x4 x5 x6 x7 : openup7 (ctx := ctxfo) (fun (_ : t1) x2 x3 x4 x5 x6 x7 => f x2 x3 x4 x5 x6 x7) x1 x2 x3 x4 x5 x6 x7 = openup6 f x2 x3 x4 x5 x6 x7.
  admit.
Qed.
Lemma openup6_shrink t1 t2 t3 t4 t5 t6 t7 (f : t2 -> t3 -> t4 -> t5 -> t6 -> t7) ctxfo x1 x2 x3 x4 x5 x6 : openup6 (ctx := ctxfo) (fun (_ : t1) x2 x3 x4 x5 x6 => f x2 x3 x4 x5 x6) x1 x2 x3 x4 x5 x6 = openup5 f x2 x3 x4 x5 x6.
  admit.
Qed.
Lemma openup5_shrink t1 t2 t3 t4 t5 t6 (f : t2 -> t3 -> t4 -> t5 -> t6) ctxfo x1 x2 x3 x4 x5 : openup5 (ctx := ctxfo) (fun (_ : t1) x2 x3 x4 x5 => f x2 x3 x4 x5) x1 x2 x3 x4 x5 = openup4 f x2 x3 x4 x5.
  admit.
Qed.
Lemma openup4_shrink t1 t2 t3 t4 t5 (f : t2 -> t3 -> t4 -> t5) ctxfo x1 x2 x3 x4 : openup4 (ctx := ctxfo) (fun (_ : t1) x2 x3 x4 => f x2 x3 x4) x1 x2 x3 x4 = openup3 f x2 x3 x4.
  admit.
Qed.
Lemma openup3_shrink t1 t2 t3 t4 (f : t2 -> t3 -> t4) ctxfo x1 x2 x3 : openup3 (ctx := ctxfo) (fun (_ : t1) x2 x3 => f x2 x3) x1 x2 x3 = openup2 f x2 x3.
  admit.
Qed.
Lemma openup2_shrink t1 t2 t3 (f : t2 -> t3) ctxfo x1 x2 : openup2 (ctx := ctxfo) (fun (_ : t1) x2 => f x2) x1 x2 = openup1 f x2.
  admit.
Qed.
Lemma openup1_shrink {t1 t2} {f : t2} {ctxfo x1} : openup1 (ctx := ctxfo) (fun (_ : t1) => f) x1 = openup0 f.
  admit.
Qed.

Lemma openup6_dedup {t0 t2 t3 t4 t5 t6} {f : t0 -> t0 -> t2 -> t3 -> t4 -> t5 -> t6} {ctxfo x0 x2 x3 x4 x5} : openup6 (ctx := ctxfo) f x0 x0 x2 x3 x4 x5 = openup5 (fun x => f x x) x0 x2 x3 x4 x5.
  admit.
Qed.
Lemma openup7_dedup {t0 t2 t3 t4 t5 t6 t7} {f : t0 -> t0 -> t2 -> t3 -> t4 -> t5 -> t6 -> t7} {ctxfo x0 x2 x3 x4 x5 x6} : openup7 (ctx := ctxfo) f x0 x0 x2 x3 x4 x5 x6 = openup6 (fun x => f x x) x0 x2 x3 x4 x5 x6.
  admit.
Qed.

Lemma openup7_comp_openup0 t1 t2 t3 t4 t5 t6 t7 t8 (f : t1 -> t2 -> t3 -> t4 -> t5 -> t6 -> t7 -> t8) (g : t1) ctxfo x2 x3 x4 x5 x6 x7 : openup7 (ctx := ctxfo) (fun x1 x2 x3 x4 x5 x6 x7 => f x1 x2 x3 x4 x5 x6 x7) (openup0 g) x2 x3 x4 x5 x6 x7 = openup6 (fun x2 x3 x4 x5 x6 x7 => f g x2 x3 x4 x5 x6 x7) x2 x3 x4 x5 x6 x7.
  admit.
Qed.
Lemma openup3_comp_openup2 t1 t2 t3 t4 (f : t1 -> t2 -> t3 -> t4) A1 A2 (g : A1 -> A2 -> t1) ctxfo x2 x3 y1 y2 : openup3 (ctx := ctxfo) (fun x1 x2 x3 => f x1 x2 x3) (openup2 (fun y1 y2 => g y1 y2) y1 y2) x2 x3 = openup4 (fun y1 y2 x2 x3 => f (g y1 y2) x2 x3) y1 y2 x2 x3.
  admit.
Qed.
Lemma openup4_comp_openup2 t1 t2 t3 t4 t5 (f : t1 -> t2 -> t3 -> t4 -> t5) A1 A2 (g : A1 -> A2 -> t1) ctxfo x2 x3 x4 y1 y2 : openup4 (ctx := ctxfo) (fun x1 x2 x3 x4 => f x1 x2 x3 x4) (openup2 (fun y1 y2 => g y1 y2) y1 y2) x2 x3 x4 = openup5 (fun y1 y2 x2 x3 x4 => f (g y1 y2) x2 x3 x4) y1 y2 x2 x3 x4.
  admit.
Qed.
(*
Lemma openup4_comp_openup2' T1 T2 T3 T4 T5 (f : T1 -> T2 -> T3 -> T4 -> T5) A1 A2 (g : A1 -> A2 -> T2) ctxfo x1 x3 x4 y1 y2 : openup4 (ctx := ctxfo) (fun x1 x2 x3 x4 => f x1 x2 x3 x4) x1 (openup2 (fun y1 y2 => g y1 y2) y1 y2) x3 x4 = openup5 (fun x1 y1 y2 x3 x4 => f x1 (g y1 y2) x3 x4) x1 y1 y2 x3 x4.
  admit.
Qed.
*)
Lemma openup5_comp_openup2 t1 t2 t3 t4 t5 t6 (f : t1 -> t2 -> t3 -> t4 -> t5 -> t6) A1 A2 (g : A1 -> A2 -> t1) ctxfo x2 x3 x4 x5 y1 y2 : openup5 (ctx := ctxfo) (fun x1 x2 x3 x4 x5 => f x1 x2 x3 x4 x5) (openup2 (fun y1 y2 => g y1 y2) y1 y2) x2 x3 x4 x5 = openup6 (fun y1 y2 x2 x3 x4 x5 => f (g y1 y2) x2 x3 x4 x5) y1 y2 x2 x3 x4 x5.
  admit.
Qed.
Lemma openup6_comp_openup2 t1 t2 t3 t4 t5 t6 t7 (f : t1 -> t2 -> t3 -> t4 -> t5 -> t6 -> t7) A1 A2 (g : A1 -> A2 -> t1) ctxfo x2 x3 x4 x5 x6 y1 y2 : openup6 (ctx := ctxfo) (fun x1 x2 x3 x4 x5 x6 => f x1 x2 x3 x4 x5 x6) (openup2 (fun y1 y2 => g y1 y2) y1 y2) x2 x3 x4 x5 x6 = openup7 (fun y1 y2 x2 x3 x4 x5 x6 => f (g y1 y2) x2 x3 x4 x5 x6) y1 y2 x2 x3 x4 x5 x6.
  admit.
Qed.

Infix "|~~" := (valid (ctxfo := [])) (at level 89, no associativity, only parsing).
Open Scope rel.

Lemma openup1_apply ctx t1 (f g : t1 -> rel 0 ctx) ctxfo x1 Ps : 
  (forall x1, [] |~~ f x1 ===> g x1) ->
  Ps |~ openup1 (ctx := ctxfo) f x1 ->
  Ps |~ openup1 (ctx := ctxfo) g x1.
  admit.
Qed.
Lemma openup2_apply ctx t1 t2 (f g : t1 -> t2 -> rel 0 ctx) ctxfo x1 x2 Ps : 
  (forall x1 x2, [] |~~ f x1 x2 ===> g x1 x2) ->
  Ps |~ openup2 (ctx := ctxfo) f x1 x2 ->
  Ps |~ openup2 (ctx := ctxfo) g x1 x2.
  admit.
Qed.
Lemma openup3_apply ctx t1 t2 t3 (f g : t1 -> t2 -> t3 -> rel 0 ctx) ctxfo x1 x2 x3 Ps : 
  (forall x1 x2 x3, [] |~~ f x1 x2 x3 ===> g x1 x2 x3) ->
  Ps |~ openup3 (ctx := ctxfo) f x1 x2 x3 ->
  Ps |~ openup3 (ctx := ctxfo) g x1 x2 x3.
  admit.
Qed.
Lemma openup4_apply ctx t1 t2 t3 t4 (f g : t1 -> t2 -> t3 -> t4 -> rel 0 ctx) ctxfo x1 x2 x3 x4 Ps : 
  (forall x1 x2 x3 x4, [] |~~ f x1 x2 x3 x4 ===> g x1 x2 x3 x4) ->
  Ps |~ openup4 (ctx := ctxfo) f x1 x2 x3 x4 ->
  Ps |~ openup4 (ctx := ctxfo) g x1 x2 x3 x4.
  admit.
Qed.
Lemma openup5_apply ctx t1 t2 t3 t4 t5 (f g : t1 -> t2 -> t3 -> t4 -> t5 -> rel 0 ctx) ctxfo x1 x2 x3 x4 x5 Ps : 
  (forall x1 x2 x3 x4 x5, [] |~~ f x1 x2 x3 x4 x5 ===> g x1 x2 x3 x4 x5) ->
  Ps |~ openup5 (ctx := ctxfo) f x1 x2 x3 x4 x5 ->
  Ps |~ openup5 (ctx := ctxfo) g x1 x2 x3 x4 x5.
  admit.
Qed.
Lemma openup6_apply ctx t1 t2 t3 t4 t5 t6 (f g : t1 -> t2 -> t3 -> t4 -> t5 -> t6 -> rel 0 ctx) ctxfo x1 x2 x3 x4 x5 x6 Ps : 
  (forall x1 x2 x3 x4 x5 x6, [] |~~ f x1 x2 x3 x4 x5 x6 ===> g x1 x2 x3 x4 x5 x6) ->
  Ps |~ openup6 (ctx := ctxfo) f x1 x2 x3 x4 x5 x6 ->
  Ps |~ openup6 (ctx := ctxfo) g x1 x2 x3 x4 x5 x6.
  admit.
Qed.

Lemma openup1_apply_in ctx t1 (f g : t1 -> rel 0 ctx) ctxfo x1 Ps P : 
  (forall x1, [] |~~ f x1 ===> g x1) ->
  openup1 (ctx := ctxfo) g x1 :: Ps |~ P ->
  openup1 (ctx := ctxfo) f x1 :: Ps |~ P.
  admit.
Qed.
Lemma openup2_apply_in ctx t1 t2 (f g : t1 -> t2 -> rel 0 ctx) ctxfo x1 x2 Ps P : 
  (forall x1 x2, [] |~~ f x1 x2 ===> g x1 x2) ->
  openup2 (ctx := ctxfo) g x1 x2 :: Ps |~ P ->
  openup2 (ctx := ctxfo) f x1 x2 :: Ps |~ P.
  admit.
Qed.
Lemma openup3_apply_in ctx t1 t2 t3 (f g : t1 -> t2 -> t3 -> rel 0 ctx) ctxfo x1 x2 x3 Ps P : 
  (forall x1 x2 x3, [] |~~ f x1 x2 x3 ===> g x1 x2 x3) ->
  openup3 (ctx := ctxfo) g x1 x2 x3 :: Ps |~ P ->
  openup3 (ctx := ctxfo) f x1 x2 x3 :: Ps |~ P.
  admit.
Qed.
Lemma openup4_apply_in ctx t1 t2 t3 t4 (f g : t1 -> t2 -> t3 -> t4 -> rel 0 ctx) ctxfo x1 x2 x3 x4 Ps P : 
  (forall x1 x2 x3 x4, [] |~~ f x1 x2 x3 x4 ===> g x1 x2 x3 x4) ->
  openup4 (ctx := ctxfo) g x1 x2 x3 x4 :: Ps |~ P ->
  openup4 (ctx := ctxfo) f x1 x2 x3 x4 :: Ps |~ P.
  admit.
Qed.

Definition ORand {ctxfo ctx} : open_rel ctxfo 0 ctx -> open_rel ctxfo 0 ctx -> open_rel ctxfo 0 ctx := openup2 Rand.
Definition ORor {ctxfo ctx} : open_rel ctxfo 0 ctx -> open_rel ctxfo 0 ctx -> open_rel ctxfo 0 ctx := openup2 Ror.
Definition ORimply {ctxfo ctx} : open_rel ctxfo 0 ctx -> open_rel ctxfo 0 ctx -> open_rel ctxfo 0 ctx := openup2 Rimply.

Fixpoint openup_binder1 {t1 t2 t3} (f : (t1 -> t2) -> t3) {ctx} : (t1 -> open_term ctx t2) -> open_term ctx t3 :=
  match ctx return (t1 -> open_term ctx t2) -> open_term ctx t3 with
    | nil => f
    | t :: ctx' => fun r x => openup_binder1 f (fun y => r y x)
  end.

Definition ORforall1 {T ctxfo ctx} : (T -> open_rel ctxfo 0 ctx) -> open_rel ctxfo 0 ctx := openup_binder1 Rforall1.
Definition ORexists1 {T ctxfo ctx} : (T -> open_rel ctxfo 0 ctx) -> open_rel ctxfo 0 ctx := openup_binder1 Rexists1.
Definition ORabs {ctxfo m ctx} : (wexpr -> open_rel ctxfo m ctx) -> open_rel ctxfo (S m) ctx := openup_binder1 Rabs.

Definition ORapp {ctxfo m ctx} : open_rel ctxfo (S m) ctx -> open_term ctxfo wexpr -> open_rel ctxfo m ctx := openup2 Rapp.

Infix "/\" := ORand : OR.
Infix "\/" := ORor : OR.
Infix "===>" := ORimply : OR.
Notation "∀ x .. y , p" := (ORforall1 (fun x => .. (ORforall1 (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity) : OR.
Notation "∃ x .. y , p" := (ORexists1 (fun x => .. (ORexists1 (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity) : OR.
Notation "\ x .. y , p" := (ORabs (fun x => .. (ORabs (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity) : OR.

Delimit Scope OR with OR.
Bind Scope OR with open_term.

Definition eqv {ctxfo m ctx} : open_rel ctxfo m ctx -> open_rel ctxfo m ctx -> Prop.
  admit.
Qed.
Require Import Setoid.
Require Import Morphisms.
Infix "==" := eqv : eqv.
Open Scope eqv.

Lemma eqv_refl {ctxfo m ctx} : Reflexive (@eqv ctxfo m ctx).
  admit.
Qed.
Lemma eqv_symm {ctxfo m ctx} : Symmetric (@eqv ctxfo m ctx).
  admit.
Qed.
Lemma eqv_trans {ctxfo m ctx} : Transitive (@eqv ctxfo m ctx).
  admit.
Qed.
Add Parametric Relation ctxfo m ctx : (open_rel ctxfo m ctx) eqv
    reflexivity proved by eqv_refl
    symmetry proved by eqv_symm
    transitivity proved by eqv_trans
      as eqv_rel.

Definition eqvls {ctxfo ctx} (a b : list (open_rel ctxfo 0 ctx)) := Forall2 eqv a b.
Lemma Forall2_refl A {P : relation A} (H : Reflexive P) : Reflexive (Forall2 P).
  admit.
Qed.
Lemma Forall2_symm A {P : relation A} (H : Symmetric P) : Symmetric (Forall2 P).
  admit.
Qed.
Lemma Forall2_trans A {P : relation A} (H : Transitive P) : Transitive (Forall2 P).
  admit.
Qed.
Add Parametric Relation ctxfo ctx : (list (open_rel ctxfo 0 ctx)) eqvls
    reflexivity proved by (Forall2_refl eqv_refl)
    symmetry proved by (Forall2_symm eqv_symm)
    transitivity proved by (Forall2_trans eqv_trans)
      as eqvls_rel.
Add Parametric Morphism ctxfo ctx : (@cons (open_rel ctxfo 0 ctx)) with
    signature eqv ==> eqvls ==> eqvls as cons_eqvls_mor.
  intros.
  econstructor; eauto.
Qed.
Add Parametric Morphism ctxfo ctx : (valid (ctx := ctx) (ctxfo := ctxfo)) with
    signature (Forall2 eqv) ==> eqv ==> iff as valid_mor.
  admit.
Qed.

Lemma openup1_and ctx t1 (f g : t1 -> rel 0 ctx) ctxfo x1 : openup1 (ctx := ctxfo) (fun x1 => f x1 /\ g x1) x1 = (openup1 f x1 /\ openup1 g x1)%OR.
  admit.
Qed.
Lemma openup2_and ctx t1 t2 (f g : t1 -> t2 -> rel 0 ctx) ctxfo x1 x2 : openup2 (ctx := ctxfo) (fun x1 x2 => f x1 x2 /\ g x1 x2) x1 x2 = (openup2 f x1 x2 /\ openup2 g x1 x2)%OR.
  admit.
Qed.
Lemma openup3_and ctx t1 t2 t3 (f g : t1 -> t2 -> t3 -> rel 0 ctx) ctxfo x1 x2 x3 : openup3 (ctx := ctxfo) (fun x1 x2 x3 => f x1 x2 x3 /\ g x1 x2 x3) x1 x2 x3 = (openup3 f x1 x2 x3 /\ openup3 g x1 x2 x3)%OR.
  admit.
Qed.
Lemma openup4_and ctx t1 t2 t3 t4 (f g : t1 -> t2 -> t3 -> t4 -> rel 0 ctx) ctxfo x1 x2 x3 x4 : openup4 (ctx := ctxfo) (fun x1 x2 x3 x4 => f x1 x2 x3 x4 /\ g x1 x2 x3 x4) x1 x2 x3 x4 = (openup4 f x1 x2 x3 x4 /\ openup4 g x1 x2 x3 x4)%OR.
  admit.
Qed.
Lemma openup5_and ctx t1 t2 t3 t4 t5 (f g : t1 -> t2 -> t3 -> t4 -> t5 -> rel 0 ctx) ctxfo x1 x2 x3 x4 x5 : openup5 (ctx := ctxfo) (fun x1 x2 x3 x4 x5 => f x1 x2 x3 x4 x5 /\ g x1 x2 x3 x4 x5) x1 x2 x3 x4 x5 = (openup5 f x1 x2 x3 x4 x5 /\ openup5 g x1 x2 x3 x4 x5)%OR.
  admit.
Qed.
Lemma openup7_and ctx t1 t2 t3 t4 t5 t6 t7 (f g : t1 -> t2 -> t3 -> t4 -> t5 -> t6 -> t7 -> rel 0 ctx) ctxfo x1 x2 x3 x4 x5 x6 x7 : openup7 (ctx := ctxfo) (fun x1 x2 x3 x4 x5 x6 x7 => f x1 x2 x3 x4 x5 x6 x7 /\ g x1 x2 x3 x4 x5 x6 x7) x1 x2 x3 x4 x5 x6 x7 = (openup7 f x1 x2 x3 x4 x5 x6 x7 /\ openup7 g x1 x2 x3 x4 x5 x6 x7)%OR.
  admit.
Qed.
Lemma openup8_and ctx t1 t2 t3 t4 t5 t6 t7 t8 (f g : t1 -> t2 -> t3 -> t4 -> t5 -> t6 -> t7 -> t8 -> rel 0 ctx) ctxfo x1 x2 x3 x4 x5 x6 x7 x8 : openup8 (ctx := ctxfo) (fun x1 x2 x3 x4 x5 x6 x7 x8 => f x1 x2 x3 x4 x5 x6 x7 x8 /\ g x1 x2 x3 x4 x5 x6 x7 x8) x1 x2 x3 x4 x5 x6 x7 x8 = (openup8 f x1 x2 x3 x4 x5 x6 x7 x8 /\ openup8 g x1 x2 x3 x4 x5 x6 x7 x8)%OR.
  admit.
Qed.

Lemma openup3_imply {ctx t1 t2 t3} {f g : t1 -> t2 -> t3 -> rel 0 ctx} {ctxfo x1 x2 x3} : openup3 (ctx := ctxfo) (fun x1 x2 x3 => f x1 x2 x3 ===> g x1 x2 x3) x1 x2 x3 = (openup3 f x1 x2 x3 ===> openup3 g x1 x2 x3)%OR.
  (* should be eq *)
  admit.
Qed.
Lemma openup4_imply ctx t1 t2 t3 t4 (f g : t1 -> t2 -> t3 -> t4 -> rel 0 ctx) ctxfo x1 x2 x3 x4 : openup4 (ctx := ctxfo) (fun x1 x2 x3 x4 => f x1 x2 x3 x4 ===> g x1 x2 x3 x4) x1 x2 x3 x4 = (openup4 f x1 x2 x3 x4 ===> openup4 g x1 x2 x3 x4)%OR.
  admit.
Qed.
Lemma openup6_imply ctx t1 t2 t3 t4 t5 t6 (f g : t1 -> t2 -> t3 -> t4 -> t5 -> t6 -> rel 0 ctx) ctxfo x1 x2 x3 x4 x5 x6 : openup6 (ctx := ctxfo) (fun x1 x2 x3 x4 x5 x6 => f x1 x2 x3 x4 x5 x6 ===> g x1 x2 x3 x4 x5 x6) x1 x2 x3 x4 x5 x6 = (openup6 f x1 x2 x3 x4 x5 x6 ===> openup6 g x1 x2 x3 x4 x5 x6)%OR.
  admit.
Qed.
Lemma openup8_imply ctx t1 t2 t3 t4 t5 t6 t7 t8 (f g : t1 -> t2 -> t3 -> t4 -> t5 -> t6 -> t7 -> t8 -> rel 0 ctx) ctxfo x1 x2 x3 x4 x5 x6 x7 x8 : openup8 (ctx := ctxfo) (fun x1 x2 x3 x4 x5 x6 x7 x8 => f x1 x2 x3 x4 x5 x6 x7 x8 ===> g x1 x2 x3 x4 x5 x6 x7 x8) x1 x2 x3 x4 x5 x6 x7 x8 = (openup8 f x1 x2 x3 x4 x5 x6 x7 x8 ===> openup8 g x1 x2 x3 x4 x5 x6 x7 x8)%OR.
  admit.
Qed.

Lemma openup2_forall1_elim t1 t2 t ctx (f : t1 -> t2 -> t -> rel 0 ctx) ctxfo x1 x2 x Ps Q :
  openup3 (ctx := ctxfo) f x1 x2 x :: Ps |~ Q ->
  openup2 (fun x1 x2 => ∀x, f x1 x2 x) x1 x2 :: Ps |~ Q.
  admit.
Qed.
Lemma openup3_forall1_elim t1 t2 t3 t ctx (f : t1 -> t2 -> t3 -> t -> rel 0 ctx) ctxfo x1 x2 x3 x Ps Q :
  openup4 (ctx := ctxfo) f x1 x2 x3 x :: Ps |~ Q ->
  openup3 (fun x1 x2 x3 => ∀x, f x1 x2 x3 x) x1 x2 x3 :: Ps |~ Q.
  admit.
Qed.
Lemma openup4_forall1_elim t1 t2 t3 t4 t ctx (f : t1 -> t2 -> t3 -> t4 -> t -> rel 0 ctx) ctxfo x1 x2 x3 x4 x Ps Q :
  openup5 (ctx := ctxfo) f x1 x2 x3 x4 x :: Ps |~ Q ->
  openup4 (fun x1 x2 x3 x4 => ∀x, f x1 x2 x3 x4 x) x1 x2 x3 x4 :: Ps |~ Q.
  admit.
Qed.
Lemma openup5_forall1_elim t1 t2 t3 t4 t5 t ctx (f : t1 -> t2 -> t3 -> t4 -> t5 -> t -> rel 0 ctx) ctxfo x1 x2 x3 x4 x5 x Ps Q :
  openup6 (ctx := ctxfo) f x1 x2 x3 x4 x5 x :: Ps |~ Q ->
  openup5 (fun x1 x2 x3 x4 x5 => ∀x, f x1 x2 x3 x4 x5 x) x1 x2 x3 x4 x5 :: Ps |~ Q.
  admit.
Qed.

Lemma openup1_exists1 ctx t t1 (f : t -> t1 -> rel 0 ctx) ctxfo x x1 Ps : 
  Ps |~ openup2 f x x1 ->
  Ps |~ openup1 (ctx := ctxfo) (fun x1 => ∃x, f x x1) x1.
  admit.
Qed.
Lemma openup2_exists1 ctx t t1 t2 (f : t -> t1 -> t2 -> rel 0 ctx) ctxfo x x1 x2 Ps : 
  Ps |~ openup3 f x x1 x2 ->
  Ps |~ openup2 (ctx := ctxfo) (fun x1 x2 => ∃x, f x x1 x2) x1 x2.
  admit.
Qed.
Lemma openup5_exists1 ctx t t1 t2 t3 t4 t5 (f : t -> t1 -> t2 -> t3 -> t4 -> t5 -> rel 0 ctx) ctxfo x x1 x2 x3 x4 x5 Ps : 
  Ps |~ openup6 f x x1 x2 x3 x4 x5 ->
  Ps |~ openup5 (ctx := ctxfo) (fun x1 x2 x3 x4 x5 => ∃x, f x x1 x2 x3 x4 x5) x1 x2 x3 x4 x5.
Proof.
  intros H.
  Lemma openup5_exists1' ctx t t1 t2 t3 t4 t5 (f : t -> t1 -> t2 -> t3 -> t4 -> t5 -> rel 0 ctx) ctxfo x1 x2 x3 x4 x5 : openup5 (ctx := ctxfo) (fun x1 x2 x3 x4 x5 => ∃x, f x x1 x2 x3 x4 x5) x1 x2 x3 x4 x5 = (∃x, openup5 (f x) x1 x2 x3 x4 x5)%OR.
    admit.
  Qed.
  rewrite openup5_exists1'.
  Fixpoint openup1' {t1 t2} {ctx} : (t1 -> open_term ctx t2) -> open_term ctx t1 -> open_term ctx t2 :=
    match ctx return (t1 -> open_term ctx t2) -> open_term ctx t1 -> open_term ctx t2 with
      | nil => id
      | t :: ctx' => fun f r x => openup1' (fun y => f y x) (r x)
    end.
  Lemma exists1_intro t ctxfo ctx (f : t -> open_rel ctxfo 0 ctx) Ps x :
    Ps |~ openup1' f x ->
    Ps |~ (∃x, f x)%OR.
    admit.
  Qed.
  eapply exists1_intro with (x := x).
  Lemma openup1'_openup5 t t1 t2 t3 t4 t5 t6 (f : t -> t1 -> t2 -> t3 -> t4 -> t5 -> t6) ctxfo x x1 x2 x3 x4 x5 : openup1' (fun x => openup5 (ctx := ctxfo) (f x) x1 x2 x3 x4 x5) x = openup6 f x x1 x2 x3 x4 x5.
    admit.
  Qed.
  rewrite openup1'_openup5.
  eauto.
Qed.
Lemma openup6_exists1 ctx t t1 t2 t3 t4 t5 t6 (f : t -> t1 -> t2 -> t3 -> t4 -> t5 -> t6 -> rel 0 ctx) ctxfo x x1 x2 x3 x4 x5 x6 Ps : 
  Ps |~ openup7 f x x1 x2 x3 x4 x5 x6 ->
  Ps |~ openup6 (ctx := ctxfo) (fun x1 x2 x3 x4 x5 x6 => ∃x, f x x1 x2 x3 x4 x5 x6) x1 x2 x3 x4 x5 x6.
  admit.
Qed.
Lemma openup7_exists1 ctx t t1 t2 t3 t4 t5 t6 t7 (f : t -> t1 -> t2 -> t3 -> t4 -> t5 -> t6 -> t7 -> rel 0 ctx) ctxfo x x1 x2 x3 x4 x5 x6 x7 Ps : 
  Ps |~ openup8 f x x1 x2 x3 x4 x5 x6 x7 ->
  Ps |~ openup7 (ctx := ctxfo) (fun x1 x2 x3 x4 x5 x6 x7 => ∃x, f x x1 x2 x3 x4 x5 x6 x7) x1 x2 x3 x4 x5 x6 x7.
  admit.
Qed.

Fixpoint liftPs {new ctxfo ctx} (Ps : t_Ps ctxfo ctx) : t_Ps (new ++ ctxfo) ctx :=
  match new with
    | nil => Ps
    | T :: new' => liftPs1 T (liftPs Ps)
  end.

Definition lift1 {T ctxfo t} (a : open_term ctxfo t) : open_term (T :: ctxfo) t := fun _ => a.

Fixpoint lift {new ctxfo t} (a : open_term ctxfo t) : open_term (new ++ ctxfo) t :=
  match new return open_term (new ++ ctxfo) t with
    | nil => a
    | T :: new' => lift1 (lift a)
  end.

Lemma fold_lift8 {ctxfo t} (a : open_term ctxfo t) {t1 t2 t3 t4 t5 t6 t7 t8} : lift1 (lift1 (lift1 (lift1 (lift1 (lift1 (lift1 (lift1 a))))))) = lift (new := [t1;t2;t3;t4;t5;t6;t7;t8]) a.
  admit.
Qed.
Lemma fold_lift7 {ctxfo t} (a : open_term ctxfo t) {t1 t2 t3 t4 t5 t6 t7} : lift1 (lift1 (lift1 (lift1 (lift1 (lift1 (lift1 a)))))) = lift (new := [t1;t2;t3;t4;t5;t6;t7]) a.
  admit.
Qed.
Lemma fold_lift6 {ctxfo t} (a : open_term ctxfo t) {t1 t2 t3 t4 t5 t6} : lift1 (lift1 (lift1 (lift1 (lift1 (lift1 a))))) = lift (new := [t1;t2;t3;t4;t5;t6]) a.
  admit.
Qed.
Lemma fold_lift5 {ctxfo t} (a : open_term ctxfo t) {t1 t2 t3 t4 t5} : lift1 (lift1 (lift1 (lift1 (lift1 a)))) = lift (new := [t1;t2;t3;t4;t5]) a.
  admit.
Qed.
Lemma fold_lift4 {ctxfo t} (a : open_term ctxfo t) {t1 t2 t3 t4} : lift1 (lift1 (lift1 (lift1 a))) = lift (new := [t1;t2;t3;t4]) a.
  admit.
Qed.
Lemma fold_lift3 {ctxfo t} (a : open_term ctxfo t) {t1 t2 t3} : lift1 (lift1 (lift1 a)) = lift (new := [t1;t2;t3]) a.
  admit.
Qed.
Lemma fold_lift2 {ctxfo t} (a : open_term ctxfo t) {t1 t2} : lift1 (lift1 a) = lift (new := [t1;t2]) a.
  admit.
Qed.
Lemma fold_lift1 {ctxfo t} (a : open_term ctxfo t) {t1} : lift1 a = lift (new := [t1]) a.
  admit.
Qed.
Require Import ssreflect.
Ltac fold_lift :=
  repeat rewrite fold_lift8;
  repeat rewrite fold_lift7;
  repeat rewrite fold_lift6;
  repeat rewrite fold_lift5;
  repeat rewrite fold_lift4;
  repeat rewrite fold_lift3;
  repeat rewrite fold_lift2;
  repeat rewrite fold_lift1.
Ltac combine_lift :=
  unfold lift; fold_lift.

Lemma liftPs_liftPs ctxfo ctx (a : t_Ps ctxfo ctx) A1 A2 B1 B2 : liftPs (new := [A1;A2]) (liftPs (new := [B1;B2]) a) = liftPs (new := [A1;A2;B1;B2]) a.
  admit.
Qed.

Definition V0 {T0 ctxfo} : open_term (T0 :: ctxfo) T0 := fun x => openup0 x.
Notation V1 := (lift (new := [_]) V0).
Notation V2 := (lift (new := [_;_]) V0).
Notation V3 := (lift (new := [_;_;_]) V0).
Notation V4 := (lift (new := [_;_;_;_]) V0).
Notation V5 := (lift (new := [_;_;_;_;_]) V0).
Notation V6 := (lift (new := [_;_;_;_;_;_]) V0).
Notation V7 := (lift (new := [_;_;_;_;_;_;_]) V0).
Notation V8 := (lift (new := [_;_;_;_;_;_;_;_]) V0).

Lemma lift_openup0 ctxfo t1 (f : t1) new : lift (new := new) (openup0 (ctx := ctxfo) f) = openup0 f.
  admit.
Qed.
Lemma lift_openup1 ctxfo t1 t2 (a : open_term ctxfo t1) (f : t1 -> t2) new : lift (new := new) (openup1 f a) = openup1 f (lift a).
  admit.
Qed.
Lemma lift_openup2 ctxfo t1 t2 t3 (f : t1 -> t2 -> t3) x1 x2 new : lift (new := new) (openup2 (ctx := ctxfo) f x1 x2) = openup2 f (lift x1) (lift x2).
  admit.
Qed.
Lemma lift_openup3 ctxfo t1 t2 t3 t4 (f : t1 -> t2 -> t3 -> t4) x1 x2 x3 new : lift (new := new) (openup3 (ctx := ctxfo) f x1 x2 x3) = openup3 f (lift x1) (lift x2) (lift x3).
  admit.
Qed.
Lemma lift_openup4 ctxfo t1 t2 t3 t4 t5 (f : t1 -> t2 -> t3 -> t4 -> t5) x1 x2 x3 x4 new : lift (new := new) (openup4 (ctx := ctxfo) f x1 x2 x3 x4) = openup4 f (lift x1) (lift x2) (lift x3) (lift x4).
  admit.
Qed.
Lemma lift_openup5 ctxfo t1 t2 t3 t4 t5 t6 (f : t1 -> t2 -> t3 -> t4 -> t5 -> t6) x1 x2 x3 x4 x5 new : lift (new := new) (openup5 (ctx := ctxfo) f x1 x2 x3 x4 x5) = openup5 f (lift x1) (lift x2) (lift x3) (lift x4) (lift x5).
  admit.
Qed.

Lemma openup1_forall1 ctx t1 t (f : t1 -> t -> rel 0 ctx) ctxfo x1 Ps : 
  liftPs (new := [_]) Ps |~ openup2 f (lift (new := [t]) x1) V0 ->
  Ps |~ openup1 (ctx := ctxfo) (fun x1 => ∀x, f x1 x) x1.
  admit.
Qed.
Lemma openup2_forall1 ctx t1 t2 t (f : t1 -> t2 -> t -> rel 0 ctx) ctxfo x1 x2 Ps : 
  liftPs (new := [_]) Ps |~ openup3 f (lift (new := [t]) x1) (lift x2) V0 ->
  Ps |~ openup2 (ctx := ctxfo) (fun x1 x2 => ∀x, f x1 x2 x) x1 x2.
  admit.
Qed.
Lemma openup3_forall1 ctx t1 t2 t3 t (f : t1 -> t2 -> t3 -> t -> rel 0 ctx) ctxfo x1 x2 x3 Ps : 
  liftPs (new := [_]) Ps |~ openup4 f (lift (new := [t]) x1) (lift x2) (lift x3) V0 ->
  Ps |~ openup3 (ctx := ctxfo) (fun x1 x2 x3 => ∀x, f x1 x2 x3 x) x1 x2 x3.
  admit.
Qed.
Lemma openup6_forall1 ctx t1 t2 t3 t4 t5 t6 t (f : t1 -> t2 -> t3 -> t4 -> t5 -> t6 -> t -> rel 0 ctx) ctxfo x1 x2 x3 x4 x5 x6 Ps : 
  liftPs (new := [_]) Ps |~ openup7 f (lift (new := [t]) x1) (lift x2) (lift x3) (lift x4) (lift x5) (lift x6) V0 ->
  Ps |~ openup6 (ctx := ctxfo) (fun x1 x2 x3 x4 x5 x6 => ∀x, f x1 x2 x3 x4 x5 x6 x) x1 x2 x3 x4 x5 x6.
  admit.
Qed.
Lemma openup7_forall1 ctx t1 t2 t3 t4 t5 t6 t7 t (f : t1 -> t2 -> t3 -> t4 -> t5 -> t6 -> t7 -> t -> rel 0 ctx) ctxfo x1 x2 x3 x4 x5 x6 x7 Ps : 
  liftPs (new := [_]) Ps |~ openup8 f (lift (new := [t]) x1) (lift x2) (lift x3) (lift x4) (lift x5) (lift x6) (lift x7) V0 ->
  Ps |~ openup7 (ctx := ctxfo) (fun x1 x2 x3 x4 x5 x6 x7 => ∀x, f x1 x2 x3 x4 x5 x6 x7 x) x1 x2 x3 x4 x5 x6 x7.
  admit.
Qed.

Lemma openup1_exists1_elim ctxfo ctx t1 t (Q : open_rel ctxfo 0 ctx) (f : t1 -> t -> rel 0 ctx) x1 (Ps : list (open_rel ctxfo 0 ctx)) :
  openup2 (fun x1 x => f x1 x) (lift (new := [_]) x1) V0 :: liftPs (new := [_]) Ps |~ lift Q ->
  openup1 (fun x1 => ∃x, f x1 x) x1 :: Ps |~ Q.
  admit.
Qed.
Lemma openup2_exists1_elim ctxfo ctx t1 t2 t (Q : open_rel ctxfo 0 ctx) (f : t1 -> t2 -> t -> rel 0 ctx) x1 x2 (Ps : list (open_rel ctxfo 0 ctx)) :
  openup3 (fun x1 x2 x => f x1 x2 x) (lift (new := [_]) x1) (lift x2) V0 :: liftPs (new := [_]) Ps |~ lift Q ->
  openup2 (fun x1 x2 => ∃x, f x1 x2 x) x1 x2 :: Ps |~ Q.
  admit.
Qed.
Lemma openup3_exists1_elim ctxfo ctx t1 t2 t3 t (Q : open_rel ctxfo 0 ctx) (f : t1 -> t2 -> t3 -> t -> rel 0 ctx) x1 x2 x3 (Ps : list (open_rel ctxfo 0 ctx)) :
  openup4 (fun x1 x2 x3 x => f x1 x2 x3 x) (lift (new := [_]) x1) (lift x2) (lift x3) V0 :: liftPs (new := [_]) Ps |~ lift Q ->
  openup3 (fun x1 x2 x3 => ∃x, f x1 x2 x3 x) x1 x2 x3 :: Ps |~ Q.
  admit.
Qed.
Lemma openup4_exists1_elim ctxfo ctx t1 t2 t3 t4 t (Q : open_rel ctxfo 0 ctx) (f : t1 -> t2 -> t3 -> t4 -> t -> rel 0 ctx) x1 x2 x3 x4 (Ps : list (open_rel ctxfo 0 ctx)) :
  openup5 (fun x1 x2 x3 x4 x => f x1 x2 x3 x4 x) (lift (new := [_]) x1) (lift x2) (lift x3) (lift x4) V0 :: liftPs (new := [_]) Ps |~ lift Q ->
  openup4 (fun x1 x2 x3 x4 => ∃x, f x1 x2 x3 x4 x) x1 x2 x3 x4 :: Ps |~ Q.
  admit.
Qed.

Lemma split ctxfo ctx (P Q : open_rel ctxfo 0 ctx) Ps :
  Ps |~ P ->
  Ps |~ Q ->
  Ps |~ (P /\ Q)%OR.
  admit.
Qed.

Instance Apply_open_econtext_open_expr {ctxfo} : Apply (open_term ctxfo econtext) (open_term ctxfo expr) (open_term ctxfo expr) :=
  {
    apply := openup2 plug
  }.

Global Instance Add_open_width_open_width {ctxfo} : Add (open_term ctxfo width_nat) (open_term ctxfo width_nat)(open_term ctxfo width_nat) :=
  {
    add := openup2 (Wbinop add)
  }.

Global Instance Apply_open_csubsts_expr {ctxfo lctx ctx} : Apply (open_csubsts ctxfo lctx ctx) (open_expr lctx) (open_term ctxfo expr).
  admit.
Defined.

Global Instance Apply_open_csubsts_width {t ctxfo lctx ctx} : Apply (open_csubsts ctxfo lctx ctx) (open_width t lctx) (open_term ctxfo (open_width t [])).
  admit.
Defined.

Instance Apply_econtext_expr {ctx} : Apply (open_econtext ctx) (open_expr ctx) (open_expr ctx):=
  {
    apply := plug
  }.

Instance Apply_Subst `{Subst t A B} {ctx} : Apply (B (t :: ctx)) (A ctx) (B ctx) :=
  {
    apply := flip subst
  }.

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

Global Instance Add_width_width lctx : Add (open_width WTnat lctx) (open_width WTnat lctx)(open_width WTnat lctx) :=
  {
    add := Wbinop add
  }.

Tactic Notation "extensionality'" :=
  match goal with
      [ |- ?X = ?Y ] =>
      (apply (@functional_extensionality _ _ X Y) ||
             apply (@functional_extensionality_dep _ _ X Y)) ; intro
  end.

Lemma rewrite_openup5 {t0 t1 t2 t3 t4 t5 ctxfo} {f g : t0 -> t1 -> t2 -> t3 -> t4 -> t5} {x0 x1 x2 x3 x4} : f = g -> openup5 (ctx := ctxfo) f x0 x1 x2 x3 x4 = openup5 g x0 x1 x2 x3 x4.
  intros H.
  rewrite H.
  reflexivity.
Qed.
Lemma rewrite_openup6 {t0 t1 t2 t3 t4 t5 t6 ctxfo} {f g : t0 -> t1 -> t2 -> t3 -> t4 -> t5 -> t6} {x0 x1 x2 x3 x4 x5} : f = g -> openup6 (ctx := ctxfo) f x0 x1 x2 x3 x4 x5 = openup6 g x0 x1 x2 x3 x4 x5.
  intros H.
  rewrite H.
  reflexivity.
Qed.

Lemma csubsts_Fadd lctx ctx (ρ : csubsts lctx ctx) (a b : open_cexpr lctx) : ρ $$ (a + b) = ρ $$ a + ρ $$ b.
  admit.
Qed.
Lemma open_csubsts_Wadd ctxfo lctx ctx (ρ : open_csubsts ctxfo lctx ctx) (w1 w2 : open_width WTnat lctx) : ρ $$ (w1 + w2) = ρ $$ w1 + ρ $$ w2.
  admit.
Qed.
Lemma open_csubsts_Eapp ctxfo lctx ctx (ρ : open_csubsts ctxfo lctx ctx) (e1 e2 : open_expr lctx) : ρ $$ (Eapp e1 e2) = openup2 (fun e1 e2 => Eapp e1 e2) (ρ $$ e1) (ρ $$ e2).
  admit.
Qed.
Lemma plug_ECapp1 (e1 e2 : expr) : ECapp1 ECempty e2 $$ e1 = Eapp e1 e2.
  eauto.
Qed.
Lemma unfold_open_plug ctxfo E e : E $$ e = openup2 (ctx := ctxfo) plug E e.
  admit.
Qed.
Lemma open_ECapp1 ctxfo (e1 e2 : open_term ctxfo expr) : openup2 (fun E e => E $ e) (openup1 (fun e => ECapp1 ECempty e) e2) e1 = openup2 (fun e1 e2 => Eapp e1 e2) e1 e2.
  admit.
Qed.
Lemma open_ECapp2 ctxfo (e1 e2 : open_term ctxfo expr) : openup2 (fun E e => E $ e) (openup1 (fun e => ECapp2 e ECempty) e1) e2 = openup2 (fun e1 e2 => Eapp e1 e2) e1 e2.
  admit.
Qed.
Lemma lift_Wadd ctxfo (w1 w2 : open_term ctxfo width_nat) new : lift (new := new) (w1 + w2) = lift w1 + lift w2.
  admit.
Qed.
Lemma lift_rho_width ctxfo lctx ctx (ρ : open_csubsts ctxfo lctx ctx) t (w : open_width t lctx) new : lift (new := new) (ρ $ w) = lift ρ $$ w.
  admit.
Qed.
Lemma lift_rho_expr ctxfo lctx ctx (ρ : open_csubsts ctxfo lctx ctx) (e : open_expr lctx) new : lift (new := new) (ρ $ e) = lift ρ $$ e.
  admit.
Qed.
Lemma open_csubsts_Wapp ctxfo lctx ctx (ρ : open_csubsts ctxfo lctx ctx) (w1 w2 : open_width WTstruct lctx) : ρ $$ (Wapp w1 w2) = openup2 Wapp (ρ $ w1) (ρ $ w2).
  admit.
Qed.
Lemma open_csubsts_WappB ctxfo lctx ctx (ρ : open_csubsts ctxfo lctx ctx) (w1 w2 : open_width WTstruct lctx) : ρ $$ (WappB w1 w2) = openup2 WappB (ρ $ w1) (ρ $ w2).
  admit.
Qed.
Lemma open_csubsts_Wconst ctxfo lctx ctx (ρ : open_csubsts ctxfo lctx ctx) n : ρ $$ Wconst n = openup0 (Wconst n).
  admit.
Qed.
Lemma csubsts_subst_s_c lctx ctx (ρ : csubsts lctx ctx) (s : open_size lctx) (c : open_cexpr (CEexpr :: lctx)) : ρ $$ (subst s c) = subst (ρ $ s) (ρ $ c).
  admit.
Qed.
Lemma csubsts_subst_s_s lctx ctx (ρ : csubsts lctx ctx) (s : open_size lctx) (b : open_size (CEexpr :: lctx)) : ρ $$ (subst s b) = subst (ρ $ s) (ρ $ b).
  admit.
Qed.
Lemma csubsts_value lctx ctx (ρ : csubsts lctx ctx) (v : expr) : ρ $$ (!(!v : csize) : open_size lctx) = !(!v).
  admit.
Qed.
Lemma openup0_lift_1 A1 t1 (f : t1) : openup0 (ctx := [A1]) f = lift (new := [A1]) (f : open_term [] _).
  admit.
Qed.
Lemma liftPs_cons ctxfo ctx (a : open_rel ctxfo 0 ctx) ls new : liftPs (new := new) (a :: ls) = lift a :: liftPs ls.
  admit.
Qed.

Lemma imply_intro ctx (P Q : rel 0 ctx) Ps :
  P :: Ps |~~ Q ->
  Ps |~~ P ===> Q.
  admit.
Qed.
Lemma imply_elim ctxfo ctx (P Q : open_rel ctxfo 0 ctx) Ps G : 
  Q :: Ps |~ G ->
  (P ===> Q)%OR :: P :: Ps |~ G.
  admit.
Qed.
Lemma imply_eelim ctxfo ctx (P Q : open_rel ctxfo 0 ctx) Ps G : 
  Ps |~ P ->
  Q :: Ps |~ G ->
  (P ===> Q)%OR :: Ps |~ G.
  admit.
Qed.
Lemma imply_trans ctx (P Q R : rel 0 ctx) : [] |~~ Q ===> R -> [] |~~ P ===> Q -> [] |~~ P ===> R.
  admit.
Qed.
Lemma forall1_intro ctx t (f : t -> rel 0 ctx) Ps : 
  liftPs (new := [_]) Ps |~ openup1 f V0 ->
  Ps |~~ ∀x, f x.
  admit.
Qed.
Lemma forall1_elim4 ctx A B C D (P : A -> B -> C -> D -> rel 0 ctx) e we c₁ wBe :
  [] |~~ (∀e we c₁ wBe, P e we c₁ wBe) ->
  [] |~~ P e we c₁ wBe.
  admit.
Qed.
Lemma exists1_elim ctx t (Q : open_rel [] 0 ctx) (f : t -> rel 0 ctx) (Ps : list (open_rel [] 0 ctx)) :
  openup1 (ctx := [t]) f V0 :: liftPs (new := [t]) Ps |~ lift (new := [t]) Q ->
  ((∃x, f x) : open_rel [] 0 ctx) :: Ps |~ Q.
  admit.
Qed.

Notation "[| P |]" := (Rinj P) (only parsing) : rel.
Lemma inj_exists_intro T (P : T -> Prop) ctx :
  [] |~~ (∃x, [| P x |] : rel 0 ctx) ===> [| exists x, P x |].
  admit.
Qed.
Lemma inj_exists_elim T (P : T -> Prop) ctx :
  [] |~~ [| exists x, P x |] ===> ∃x, [| P x |] : rel 0 ctx.
  admit.
Qed.
Lemma inj_and_intro (P Q : Prop) ctx :
  [] |~~ [| P |] /\ [| Q |] ===> ([| P /\ Q |] : rel 0 ctx).
  admit.
Qed.
Lemma inj_and_elim (P Q : Prop) ctx :
  [] |~~ ([| P /\ Q |] : rel 0 ctx) ===> [| P |] /\ [| Q |].
  admit.
Qed.
Lemma inj_imply (P Q : Prop) ctx :
  (P -> Q) ->
  [] |~~ ([| P |] ===> [| Q |] : rel 0 ctx).
  admit.
Qed.

Lemma ctx_refl ctxfo ctx (P : open_rel ctxfo 0 ctx) Ps : P :: Ps |~ P.
  admit.
Qed.
Lemma totop ctxfo ctx (P Q : open_rel ctxfo 0 ctx) n Ps :
  nth_error Ps n = Some P ->
  P :: removen Ps n |~ Q ->
  Ps |~ Q.
  admit.
Qed.
Lemma eqv_premise ctxfo ctx (P P' Q : open_rel ctxfo 0 ctx) Ps :
  P == P' ->
  P' :: Ps |~ Q ->
  P :: Ps |~ Q.
  admit.
Qed.
Lemma ORimply_intro ctxfo ctx (P Q : open_rel ctxfo 0 ctx) Ps :
  P :: Ps |~ Q ->
  Ps |~ (P ===> Q)%OR.
  admit.
Qed.
Lemma dup_premise ctxfo ctx (P Q : open_rel ctxfo 0 ctx) Ps :
  P :: P :: Ps |~ Q ->
  P :: Ps |~ Q.
  admit.
Qed.
Lemma destruct_and ctxfo ctx (P1 P2 Q : open_rel ctxfo 0 ctx) Ps :
  P1 :: P2 :: Ps |~ Q ->
  (P1 /\ P2)%OR :: Ps |~ Q.
  admit.
Qed.
Lemma openup3_beta ctx t1 t2 t3 (f : t1 -> t2 -> t3 -> wexpr) m g ctxfo x1 x2 x3 : openup3 (ctx := ctxfo) (fun x1 x2 x3 => f x1 x2 x3 ∈ Rabs (m := m) (ctx := ctx) (g x1 x2 x3)) x1 x2 x3 == openup3 (fun x1 x2 x3 => g x1 x2 x3 (f x1 x2 x3)) x1 x2 x3.
  admit.
Qed.

Lemma relE_mono_tau_c_s lctx τ c s s₁ ctx (ρ : csubsts lctx ctx) e w wB (v : expr) : 
  [] |~~ (e, w) ∈ relE (subst !(!v) τ) wB !(subst !(!v) c) (subst !(!v) s) ρ /\ ⌈!v ≤ ρ $$ s₁⌉ ===> (e, w) ∈ relE (subst s₁ τ) wB !(subst (ρ $ s₁) c) (subst (ρ $ s₁) s) ρ.
  admit.
Qed.
Lemma relE_rho lctx τ c s ctx (ρ : csubsts lctx ctx) e w wB (v : expr) w' : 
  [] |~~ (e, w) ∈ relE τ wB c s (add (v, w') ρ) ===> (e, w) ∈ relE (subst !(!v) τ) wB c s ρ.
  admit.
Qed.
Lemma relE_app_subst lctx τ c s ctx (ρ : csubsts lctx ctx) v₀ v₁ w₀ w₁ : 
  [] |~~
     (∃e w wB, (subst v₁ e, subst w₁ w) ∈ relE τ (subst w₁ wB) c s ρ /\ ⌈(exists τ', v₀ = Eabs τ' e) /\ w₀ = Wabs wB w⌉%type) ===>
     (Eapp v₀ v₁, Wapp w₀ w₁) ∈ relE τ (Wconst 1 + WappB w₀ w₁) c s ρ.
  admit.
Qed.
Lemma relE_replace_width lctx τ c s ctx (ρ : csubsts lctx ctx) e v₁ w wB w₁ : 
  [] |~~
     (∃w₁', (subst v₁ e, subst w₁' w) ∈ relE τ (subst w₁' wB) c s (add (v₁, w₁') ρ) /\ ⌈wsteps w₁ w₁'⌉) ===>
     (subst v₁ e, subst w₁ w) ∈ relE τ (subst w₁ wB) c s (add (v₁, w₁) ρ).
  admit.
Qed.

Definition relEC (E : econtext) e we (wEe : width) (wBEe : open_width WTnat []) (s₁ : size) (c₂ : cexpr) (s₂ : size) {lctx lctx'} (τ : open_type lctx) (τ' : open_type lctx') ctx (ρ : csubsts lctx ctx) (ρ' : csubsts lctx' ctx) : rel 0 ctx :=
  ∀v we', (v, we') ∈ relV τ ρ /\ ⌈e ~>* v /\ !v ≤ s₁ /\ wsteps we we'⌉ ===> (E $ v, wEe) ∈ relE τ' wBEe !c₂ s₂ ρ'.

Lemma relE_relEC ctxfo ctx A (ρ : open_term ctxfo A) (E : open_term ctxfo econtext) (e : open_term ctxfo expr) (we : open_term ctxfo width) (wEe : open_term ctxfo width) (wBEe : open_term ctxfo width_nat) Ps P Q :
  openup5 (fun ρ e we we' v => P v we' ρ e we) (lift (new := [_; _]) ρ) (lift e) (lift we) V0 V1 :: liftPs (ctx := ctx) (new := [_; _]) Ps 
          |~ openup4 (fun ρ Ee wEe wBEe => 
                        (Ee, wEe) ∈ Q wBEe ρ) (lift (new := [width : Type; expr])  ρ) (lift E $ V1) (lift wEe) (lift wBEe) ->
  Ps 
    |~ openup6 (fun ρ E e we wEe wBEe => 
                  ∀v we', 
                    P v we' ρ e we ===>
                      (E $$ v, wEe) ∈ Q wBEe ρ) ρ E e we wEe wBEe.
Proof.
  intros H.
  eapply openup6_forall1.
  eapply openup7_forall1.
  rewrite openup8_imply.
  eapply ORimply_intro.
  rewrite openup8_totop1.
  rewrite openup8_shrink.
  rewrite openup7_totop3.
  rewrite openup7_shrink.
  rewrite openup6_totop3.
  rewrite openup6_shrink.
  rewrite openup5_totop3.
  do 4 rewrite openup5_totop4.
  set (tmp := openup5 _ _ _ _ _ _).
  rewrite openup8_totop2.
  rewrite openup8_shrink.
  rewrite openup7_totop2.
  rewrite openup7_shrink.
  rewrite openup6_totop5.
  rewrite openup6_shrink.
  set (tmp2 := lift E $ V1) in H.
  Arguments memberOf : simpl never.
  Arguments apply : simpl never.
  Arguments subst : simpl never.
  Arguments add : simpl never.
  Arguments coerce : simpl never.
  Arguments lift : simpl never.
  Arguments openup2 : simpl never.
  Arguments plug : simpl never.
  unfold apply in tmp2.
  simpl in tmp2.
  subst tmp2.
  rewrite openup4_totop1 in H.
  erewrite openup4_comp_openup2 in H.
  rewrite openup5_totop4.
  rewrite openup5_totop2.
  subst tmp.
  combine_lift.
  unfold liftPs in *.
  eauto.
Qed.

Lemma LRbind E (wE : open_width WTstruct [CEexpr]) (wBE : open_width WTnat [CEexpr]) s₁ c₂ s₂ {lctx lctx'} (τ : open_type lctx) (τ' : open_type lctx') ctx (ρ : csubsts lctx ctx) (ρ' : csubsts lctx' ctx) :
  [] |~~ 
     ∀e we c₁ wBe, 
       ⌈IsEC E⌉ /\
       (e, we) ∈ relE τ wBe !c₁ s₁ ρ /\ 
       relEC E e we (wE $ we) (wBE $ we) s₁ c₂ s₂ τ τ' ρ ρ' ===> 
       (E $$ e, wE $$ we) ∈ relE τ' (wBe + wBE $$ we) !(c₁ + c₂) s₂ ρ'.
Proof.
  Lemma VLob ctxfo ctx Ps (P : open_rel ctxfo 0 ctx) : openup1 (▹ []) P :: Ps |~ P -> Ps |~ P.
    admit.
  Qed.
  eapply VLob.
  set (Hlob := 
      openup1 (▹ [])
      ((∀(e : expr) (we : width) (c₁ : cexpr) (wBe : width_nat),
       ⌈IsEC E⌉ /\
       (e, we) ∈ relE τ wBe !c₁ s₁ ρ /\
       relEC E e we (wE $$ we) (wBE $$ we) s₁ c₂ s₂ τ τ' ρ ρ' ===>
       (E $$ e, wE $$ we) ∈ relE τ' (wBe + wBE $$ we) !(c₁ + c₂) s₂ ρ') : open_rel [] _ _)).
  
  eapply forall1_intro.
  eapply openup1_forall1.
  eapply openup2_forall1.
  eapply openup3_forall1.
  rewrite openup4_imply.
  eapply ORimply_intro.
  rewrite openup4_and.
  eapply destruct_and.
  eapply totop with (n := 1); [ reflexivity | unfold removen ].
  rewrite openup4_and.
  eapply destruct_and.
  set (Ps := _ :: _ :: _ :: _).
  combine_lift.
  Lemma relE_intro lctx ctx e w τ wB c s (ρ : csubsts lctx ctx) :
    [] |~~ 
       ⌈|- e (ρ $ τ) /\ wtyping [] w !(ρ $ τ) ⌉ /\
       ⌈exists B, wsteps wB (Wconst B) /\ forall n e', (~>## e n 0 e') -> n ≤ B⌉%type /\ 
       (∀v w', ⌈e ⇓ v /\ wrunsto w w'⌉%type ===> (v, w') ∈ relV τ ρ /\ ⌈!v ≤ s⌉) /\
       (∀e', ⌈~>*# e 1 e' /\ exists w', wrunsto w w'⌉ ===> ⌈0 < c⌉ /\ ▹ [] ((e', w) ∈ relE τ wB (c - 1) s ρ)) /\
       ⌈exists v, e ⇓ v⌉ /\
       ⌈exists w', wrunsto w w'⌉ ===>
       (e, w) ∈ relE τ wB c s ρ.
    admit.
  Qed.
  Lemma relE_elim lctx ctx e w τ wB c s (ρ : csubsts lctx ctx) :
    [] |~~ 
       (e, w) ∈ relE τ wB c s ρ ===>
       ⌈|- e (ρ $ τ) /\ wtyping [] w !(ρ $ τ) ⌉ /\
       ⌈exists B, wsteps wB (Wconst B) /\ forall n e', (~>## e n 0 e') -> n ≤ B⌉%type /\ 
       (∀v w', ⌈e ⇓ v /\ wrunsto w w'⌉%type ===> (v, w') ∈ relV τ ρ /\ ⌈!v ≤ s⌉) /\
       (∀e', ⌈~>*# e 1 e' /\ exists w', wrunsto w w'⌉ ===> ⌈0 < c⌉ /\ ▹ [] ((e', w) ∈ relE τ wB (c - 1) s ρ)) /\
       ⌈exists v, e ⇓ v⌉ /\
       ⌈exists w', wrunsto w w'⌉.
    admit.
  Qed.
  eapply openup4_apply.
  {
    intros.
    eapply relE_intro.
  }
  rewrite openup4_and.
  eapply split.
  {
    admit. (* typing *)
  }
  rewrite openup4_and.
  eapply split.
  {
    rewrite openup4_totop2.
    rewrite openup4_shrink.
    subst Ps.
    eapply openup4_apply_in.
    {
      intros.
      eapply relE_elim.
    }
    rewrite openup4_and.
    eapply destruct_and.
    eapply totop with (n := 1); [ reflexivity | unfold removen ].
    rewrite openup4_and.
    eapply destruct_and.
    eapply totop with (n := 1); [ reflexivity | unfold removen ].
    rewrite openup4_and.
    eapply destruct_and.
    eapply totop with (n := 1); [ reflexivity | unfold removen ].
    rewrite openup4_and.
    eapply destruct_and.
    eapply totop with (n := 1); [ reflexivity | unfold removen ].
    rewrite openup4_and.
    eapply destruct_and.
    rewrite openup4_totop1.
    rewrite openup4_shrink.
    rewrite openup3_totop1.
    rewrite openup3_shrink.
    rewrite openup2_totop1.
    rewrite openup2_shrink.
    eapply openup1_apply_in.
    {
      intros.
      eapply inj_exists_elim.
    }
    eapply openup1_exists1_elim.
    repeat rewrite liftPs_cons.
    repeat rewrite lift_openup4.
    combine_lift.
    rewrite lift_openup3.
    unfold liftPs, liftPs1, map.
    eapply totop with (n := 1); [ reflexivity | unfold removen ].
    rewrite openup4_shrink.
    rewrite openup3_totop1.
    rewrite openup3_shrink.
    rewrite openup2_totop1.
    rewrite openup2_shrink.
    eapply openup1_apply_in.
    {
      intros.
      eapply inj_exists_elim.
    }
    eapply openup1_exists1_elim.
    repeat rewrite liftPs_cons.
    repeat rewrite lift_openup4.
    combine_lift.
    rewrite lift_openup3.
    unfold liftPs, liftPs1, map.
    eapply totop with (n := 3); [ reflexivity | unfold removen ].
    rewrite openup4_totop2.
    rewrite openup4_shrink.
    rewrite openup3_totop2.
    rewrite openup3_shrink.
    eapply openup2_forall1_elim with (x := V1).
    eapply openup3_forall1_elim with (x := V0).
    rewrite openup4_imply.
    eapply imply_eelim.
    {
      set (Ps := [_;_;_;_;_;_;_;_]).
      eapply openup4_apply.
      {
        intros.
        eapply inj_and_intro.
      }
      rewrite openup4_and.
      eapply split.
      {
        rewrite openup4_totop1.
        rewrite openup4_shrink.
        rewrite openup3_totop2.
        rewrite openup3_shrink.
        subst Ps.
        eapply totop with (n := 1); [ reflexivity | unfold removen ].
        erewrite lift_openup2.
        eapply ctx_refl.
      }
      rewrite openup4_shrink.
      rewrite openup3_totop1.
      rewrite openup3_shrink.
      subst Ps.
      eapply ctx_refl.
    }
    rewrite openup4_shrink.
    rewrite openup3_shrink.
    rewrite openup2_and.
    eapply destruct_and.
    eapply totop with (n := 7); [ reflexivity | unfold removen ].
    rewrite openup4_totop2.
    rewrite openup4_shrink.
    rewrite openup3_totop2.
    rewrite openup3_shrink.
    eapply dup_premise.
    unfold relEC at 1.
    eapply openup2_forall1_elim with (x := V1).
    eapply openup3_forall1_elim with (x := V0).
    rewrite openup4_imply.
    eapply imply_eelim.
    {
      rewrite openup4_and.
      eapply split.
      {
        repeat rewrite openup4_shrink.
        repeat rewrite openup3_shrink.
        eapply totop with (n := 1); [ reflexivity | unfold removen ].
        eapply ctx_refl.
      }
      admit. (* ⌈x1 ~>* x3 /\ !x3 ≤ s₁ /\ wsteps x2 x4⌉ *)
    }
    rewrite openup4_shrink.
    rewrite openup3_totop2.
    rewrite openup3_shrink.
    eapply openup2_apply_in.
    {
      intros.
      eapply relE_elim.
    }
    rewrite openup2_and.
    eapply destruct_and.
    eapply totop with (n := 1); [ reflexivity | unfold removen ].
    rewrite openup2_and.
    eapply destruct_and.
    eapply openup2_apply_in.
    {
      intros.
      eapply inj_exists_elim.
    }
    eapply openup2_exists1_elim.
    repeat rewrite liftPs_cons.
    repeat rewrite lift_openup4.
    combine_lift.
    unfold liftPs, liftPs1, map.
    eapply totop with (n := 9); [ reflexivity | unfold removen ].
    rewrite openup4_totop1.
    rewrite openup4_shrink.
    rewrite openup3_totop1.
    rewrite openup3_shrink.
    eapply openup2_apply_in.
    {
      intros.
      eapply inj_exists_elim.
    }
    eapply openup2_exists1_elim.
    repeat rewrite liftPs_cons.
    repeat rewrite lift_openup4.
    combine_lift.
    unfold liftPs, liftPs1, map.
    repeat erewrite lift_openup3.
    set (Ps := [_;_;_;_;_;_;_;_;_;_;_;_;_]).
    eapply openup3_apply.
    {
      intros.
      eapply inj_exists_intro.
    }
    Lemma openup3_exists1 ctx t t1 t2 t3 (f : t -> t1 -> t2 -> t3 -> rel 0 ctx) ctxfo x x1 x2 x3 Ps : 
      Ps |~ openup4 f x x1 x2 x3 ->
      Ps |~ openup3 (ctx := ctxfo) (fun x1 x2 x3 => ∃x, f x x1 x2 x3) x1 x2 x3.
      admit.
    Qed.
    eapply openup3_exists1 with (x := openup2 add V0 V1).
    erewrite openup4_comp_openup2.
    subst Ps.
    eapply openup3_apply_in.
    {
      intros.
      eapply inj_and_elim.
    }
    rewrite openup3_and.
    eapply destruct_and.
    rewrite openup3_shrink.
    eapply totop with (n := 2); [ reflexivity | unfold removen ].
    erewrite lift_openup2.
    eapply openup3_apply_in.
    {
      intros.
      eapply inj_and_elim.
    }
    rewrite openup3_and.
    eapply destruct_and.
    rewrite openup3_totop1.
    rewrite openup3_shrink.
    set (Ps := [_;_;_;_;_;_;_;_;_;_;_;_;_;_;_]).
    eapply openup5_apply.
    {
      intros.
      eapply inj_and_intro.
    }
    rewrite openup5_and.
    eapply split.
    {
      rewrite openup5_totop2.
      rewrite openup5_shrink.
      eapply openup4_apply.
      {
        intros.
        eapply imply_trans.
        {
          eapply inj_imply.
          {
            Lemma Wadd_wsteps w1 w2 n1 n2 : 
              wsteps w1 (Wconst n1) /\ wsteps w2 (Wconst n2) ->
              wsteps (w1 + w2) (Wconst (n1 + n2)).
              admit.
            Qed.
            eapply Wadd_wsteps.
          }
        }
        eapply inj_and_intro.
      }
      rewrite openup4_and.
      eapply split.
      {
        rewrite openup4_totop1.
        rewrite openup4_shrink.
        rewrite openup3_totop1.
        rewrite openup3_shrink.
        subst Ps.
        eapply totop with (n := 2); [ reflexivity | unfold removen ].
        eapply ctx_refl.
      }
      rewrite openup4_shrink.
      rewrite openup3_totop2.
      rewrite openup3_shrink.
      subst Ps.
      eapply ctx_refl.
    }
    rewrite openup5_totop3.
    rewrite openup5_shrink.
    rewrite openup4_totop3.
    rewrite openup4_shrink.
    combine_lift.
    Lemma plug_steps_0 E e n1 n2 : 
      (forall n e', ~>## e n 0 e' -> n <= n1) /\
      (exists v, e ⇓ v /\ forall n e', ~>## (E $ v) n 0 e' -> n <= n2)%type ->
      forall n e', ~>## (E $ e) n 0 e' -> n <= n1 + n2.
      admit.
    Qed.
    eapply openup3_apply.
    {
      intros.
      eapply imply_trans.
      {
        eapply inj_imply.
        {
          eapply plug_steps_0.
        }
      }
      eapply inj_and_intro.
    }
    rewrite openup3_and.
    eapply split.
    {
      rewrite openup3_totop1.
      rewrite openup3_shrink.
      subst Ps.
      eapply totop with (n := 3); [ reflexivity | unfold removen ].
      rewrite openup3_totop1.
      rewrite openup3_shrink.
      eapply ctx_refl.
    }
    rewrite openup3_shrink.
    eapply openup2_apply.
    {
      intros.
      eapply inj_exists_intro.
    }
    eapply openup2_exists1 with (x := V3).
    eapply openup3_apply.
    {
      intros.
      eapply inj_and_intro.
    }
    rewrite openup3_and.
    eapply split.
    {
      rewrite openup3_totop1.
      rewrite openup3_shrink.
      subst Ps.
      eapply totop with (n := 10); [ reflexivity | unfold removen ].
      erewrite lift_openup2.
      rewrite openup2_totop1.
      eapply ctx_refl.
    }
    rewrite openup3_totop2.
    rewrite openup3_shrink.
    subst Ps.
    eapply totop with (n := 1); [ reflexivity | unfold removen ].
    eapply ctx_refl.
  }
  rewrite openup4_and.
  eapply split.
  {
    rewrite openup4_totop2.
    rewrite openup4_shrink.
    rewrite openup3_totop2.
    rewrite openup3_shrink.
    eapply openup2_forall1.
    eapply openup3_forall1.
    rewrite openup4_imply.
    eapply ORimply_intro.
    subst Ps.
    repeat rewrite liftPs_cons.
    repeat rewrite lift_openup4.
    combine_lift.
    unfold liftPs, liftPs1, map.
    eapply openup4_apply_in.
    {
      intros.
      eapply inj_and_elim.
    }
    rewrite openup4_and.
    eapply destruct_and.
    rewrite openup4_totop1.
    rewrite openup4_shrink.
    rewrite openup3_totop2.
    rewrite openup3_shrink.
    Lemma plug_runsto_elim E e v :
      E $$ e ⇓ v ->
      (exists v', e ⇓ v' /\ E $$ v' ⇓ v)%type.
      admit.
    Qed.
    eapply openup2_apply_in.
    {
      intros.
      eapply imply_trans; last first.
      {
        eapply inj_imply.
        {
          eapply plug_runsto_elim.
        }
      }
      eapply inj_exists_elim.
    }
    eapply openup2_exists1_elim.
    repeat rewrite liftPs_cons.
    repeat rewrite lift_openup4.
    combine_lift.
    unfold liftPs, liftPs1, map.
    eapply openup3_apply_in.
    {
      intros.
      eapply inj_and_elim.
    }
    rewrite openup3_and.
    eapply destruct_and.
    rewrite openup3_totop1.
    rewrite openup3_shrink.
    eapply totop with (n := 2); [ reflexivity | unfold removen ].
    rewrite openup4_shrink.
    rewrite openup3_totop1.
    rewrite openup3_shrink.
    Lemma app_wrunsto_elim (w1 : open_width WTstruct [CEexpr]) (w2 w : width) :
      wrunsto (w1 $ w2) w ->
      (exists w', wrunsto w2 w' /\ wrunsto (w1 $ w') w)%type.
      admit.
    Qed.
    eapply dup_premise.
    eapply openup2_apply_in.
    {
      intros.
      eapply imply_trans; last first.
      {
        eapply inj_imply.
        {
          eapply app_wrunsto_elim.
        }
      }
      eapply inj_exists_elim.
    }
    eapply openup2_exists1_elim.
    repeat rewrite liftPs_cons.
    repeat rewrite lift_openup4.
    combine_lift.
    unfold liftPs, liftPs1, map.
    eapply openup3_apply_in.
    {
      intros.
      eapply inj_and_elim.
    }
    rewrite openup3_and.
    eapply destruct_and.
    rewrite openup3_totop1.
    rewrite openup3_shrink.
    eapply totop with (n := 5); [ reflexivity | unfold removen ].
    eapply dup_premise.
    eapply openup4_apply_in.
    {
      intros.
      eapply relE_elim.
    }
    rewrite openup4_and.
    eapply destruct_and.
    eapply totop with (n := 1); [ reflexivity | unfold removen ].
    rewrite openup4_and.
    eapply destruct_and.
    eapply totop with (n := 1); [ reflexivity | unfold removen ].
    rewrite openup4_and.
    eapply destruct_and.
    rewrite openup4_totop2.
    rewrite openup4_shrink.
    rewrite openup3_totop2.
    rewrite openup3_shrink.
    rewrite lift_openup2.
    rewrite lift_openup3.
    combine_lift.
    eapply openup2_forall1_elim with (x := V1).
    eapply openup3_forall1_elim with (x := V0).
    rewrite openup4_imply.
    eapply imply_eelim.
    {
      set (Ps := [_;_;_;_;_;_;_;_;_;_;_;_]).
      eapply openup4_apply.
      {
        intros.
        eapply inj_and_intro.
      }
      rewrite openup4_and.
      eapply split.
      {
        rewrite openup4_totop1.
        rewrite openup4_shrink.
        rewrite openup3_totop2.
        rewrite openup3_shrink.
        subst Ps.
        eapply totop with (n := 7); [ reflexivity | unfold removen ].
        eapply ctx_refl.
      }
      rewrite openup4_shrink.
      rewrite openup3_totop1.
      rewrite openup3_shrink.
      subst Ps.
      eapply totop with (n := 4); [ reflexivity | unfold removen ].
      eapply ctx_refl.
    }
    rewrite openup4_shrink.
    rewrite openup3_shrink.
    rewrite openup2_and.
    eapply destruct_and.
    eapply totop with (n := 11); [ reflexivity | unfold removen ].
    eapply dup_premise.
    unfold relEC at 1.
    rewrite openup4_totop2.
    rewrite openup4_shrink.
    rewrite openup3_totop2.
    rewrite openup3_shrink.
    eapply openup2_forall1_elim with (x := V1).
    eapply openup3_forall1_elim with (x := V0).
    rewrite openup4_imply.
    eapply imply_eelim.
    {
      set (Ps := [_;_;_;_;_;_;_;_;_;_;_;_;_;_]).
      rewrite openup4_and.
      eapply split.
      {
        rewrite openup4_shrink.
        rewrite openup3_shrink.
        subst Ps.
        eapply totop with (n := 1); [ reflexivity | unfold removen ].
        eapply ctx_refl.
      }
      eapply openup4_apply.
      {
        intros.
        eapply inj_and_intro.
      }
      rewrite openup4_and.
      eapply split.
      {
        rewrite openup4_totop1.
        rewrite openup4_shrink.
        rewrite openup3_totop2.
        rewrite openup3_shrink.
        subst Ps.
        eapply totop with (n := 10); [ reflexivity | unfold removen ].
        rewrite lift_openup2.
        eapply openup2_apply_in.
        {
          intros.
          eapply inj_imply.
          {
            intros H.
            unfold runsto in H.
            destruct H as [H1 H2].
            exact H1.
          }
        }
        eapply ctx_refl.
      }
      rewrite openup4_shrink.
      eapply openup3_apply.
      {
        intros.
        eapply inj_and_intro.
      }
      rewrite openup3_and.
      eapply split.
      {
        rewrite openup3_shrink.
        rewrite openup2_totop1.
        rewrite openup2_shrink.
        subst Ps.
        eapply totop with (n := 2); [ reflexivity | unfold removen ].
        rewrite openup2_totop1.
        rewrite openup2_shrink.
        eapply ctx_refl.
      }
      rewrite openup3_totop1.
      rewrite openup3_shrink.
      subst Ps.
      eapply totop with (n := 7); [ reflexivity | unfold removen ].
      eapply openup2_apply_in.
      {
        intros.
        eapply inj_imply.
        {
          intros H.
          unfold wrunsto in H.
          destruct H as [H1 H2].
          exact H1.
        }
      }
      eapply ctx_refl.
    }
    rewrite openup4_shrink.
    rewrite openup3_totop2.
    rewrite openup3_shrink.
    eapply openup2_apply_in.
    {
      intros.
      eapply relE_elim.
    }
    rewrite openup2_and.
    eapply destruct_and.
    eapply totop with (n := 1); [ reflexivity | unfold removen ].
    rewrite openup2_and.
    eapply destruct_and.
    eapply totop with (n := 1); [ reflexivity | unfold removen ].
    rewrite openup2_and.
    eapply destruct_and.
    eapply openup2_forall1_elim with (x := V3).
    eapply openup3_forall1_elim with (x := V2).
    rewrite openup4_imply.
    eapply imply_eelim.
    {
      set (Ps := [_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_]).
      eapply openup4_apply.
      {
        intros.
        eapply inj_and_intro.
      }
      rewrite openup4_and.
      eapply split.
      {
        rewrite openup4_shrink.
        rewrite openup3_totop2.
        rewrite openup3_shrink.
        subst Ps.
        eapply totop with (n := 14); [ reflexivity | unfold removen ].
        rewrite openup3_shrink.
        rewrite openup2_totop1.
        eapply ctx_refl.
      }
      rewrite openup4_totop1.
      rewrite openup4_shrink.
      rewrite openup3_totop1.
      rewrite openup3_shrink.
      subst Ps.
      eapply totop with (n := 12); [ reflexivity | unfold removen ].
      eapply ctx_refl.
    }
    rewrite openup4_shrink.
    rewrite openup3_shrink.
    set (Ps := [_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_]).
    rewrite openup4_shrink.
    rewrite openup3_shrink.
    eapply ctx_refl.
  }
  rewrite openup4_and.
  eapply split.
  {
    (* subgoal (4) *)
    Lemma openup4_forall1 ctx t1 t2 t3 t4 t (f : t1 -> t2 -> t3 -> t4 -> t -> rel 0 ctx) ctxfo x1 x2 x3 x4 Ps : 
      liftPs (new := [_]) Ps |~ openup5 f (lift (new := [t]) x1) (lift x2) (lift x3) (lift x4) V0 ->
      Ps |~ openup4 (ctx := ctxfo) (fun x1 x2 x3 x4 => ∀x, f x1 x2 x3 x4 x) x1 x2 x3 x4.
      admit.
    Qed.
    eapply openup4_forall1.
    Lemma openup5_forall1 ctx t1 t2 t3 t4 t5 t (f : t1 -> t2 -> t3 -> t4 -> t5 -> t -> rel 0 ctx) ctxfo x1 x2 x3 x4 x5 Ps : 
      liftPs (new := [_]) Ps |~ openup6 f (lift (new := [t]) x1) (lift x2) (lift x3) (lift x4) (lift x5) V0 ->
      Ps |~ openup5 (ctx := ctxfo) (fun x1 x2 x3 x4 x5 => ∀x, f x1 x2 x3 x4 x5 x) x1 x2 x3 x4 x5.
      admit.
    Qed.
    Lemma openup5_imply ctx t1 t2 t3 t4 t5 (f g : t1 -> t2 -> t3 -> t4 -> t5 -> rel 0 ctx) ctxfo x1 x2 x3 x4 x5 : openup5 (ctx := ctxfo) (fun x1 x2 x3 x4 x5 => f x1 x2 x3 x4 x5 ===> g x1 x2 x3 x4 x5) x1 x2 x3 x4 x5 = (openup5 f x1 x2 x3 x4 x5 ===> openup5 g x1 x2 x3 x4 x5)%OR.
      admit.
    Qed.
    rewrite openup5_imply.
    rewrite openup5_shrink.
    eapply ORimply_intro.
    subst Ps.
    repeat rewrite liftPs_cons.
    repeat rewrite lift_openup4.
    combine_lift.
    unfold liftPs, liftPs1, map.
    rewrite openup5_totop2.
    rewrite openup5_shrink.
    rewrite openup4_totop2.
    rewrite openup4_shrink.
    eapply openup3_apply_in.
    {
      intros.
      eapply inj_and_elim.
    }
    rewrite openup3_and.
    eapply destruct_and.
    Lemma plug_steps_1_elim E e e' :
      ~>*# (E $ e) 1 e' ->
      ((exists v, ⇓*# e 0 v /\ ~>*# (E $ v) 1 e') \/
       (exists e'', ~>*# e 1 e' /\ ~>*# (E $ e'') 0 e'))%type.
      admit.
    Qed.
    eapply openup3_apply_in.
    {
      intros.
      eapply imply_trans; last first.
      {
        eapply inj_imply.
        {
          eapply plug_steps_1_elim.
        }
      }
      Lemma inj_or_elim (P Q : Prop) ctx :
        [] |~~ ([| P \/ Q |] : rel 0 ctx) ===> [| P |] \/ [| Q |].
        admit.
      Qed.
      eapply inj_or_elim.
    }
    Lemma openup2_or ctx t1 t2 (f g : t1 -> t2 -> rel 0 ctx) ctxfo x1 x2 : openup2 (ctx := ctxfo) (fun x1 x2 => f x1 x2 \/ g x1 x2) x1 x2 = (openup2 f x1 x2 \/ openup2 g x1 x2)%OR.
      admit.
    Qed.
    Lemma openup3_or ctx t1 t2 t3 (f g : t1 -> t2 -> t3 -> rel 0 ctx) ctxfo x1 x2 x3 : openup3 (ctx := ctxfo) (fun x1 x2 x3 => f x1 x2 x3 \/ g x1 x2 x3) x1 x2 x3 = (openup3 f x1 x2 x3 \/ openup3 g x1 x2 x3)%OR.
      admit.
    Qed.
    rewrite openup3_or.
    Lemma destruct_or ctxfo ctx (P1 P2 Q : open_rel ctxfo 0 ctx) Ps :
      P1 :: Ps |~ Q ->
      P2 :: Ps |~ Q ->
      (P1 \/ P2)%OR :: Ps |~ Q.
      admit.
    Qed.
    eapply destruct_or.
    {
      rewrite openup3_totop1.
      rewrite openup3_shrink.
      eapply openup2_apply_in.
      {
        intros.
        eapply inj_exists_elim.
      }
      eapply openup2_exists1_elim.
      repeat rewrite liftPs_cons.
      repeat rewrite lift_openup4.
      combine_lift.
      unfold liftPs, liftPs1, map.
      eapply openup3_apply_in.
      {
        intros.
        eapply inj_and_elim.
      }
      rewrite openup3_and.
      eapply destruct_and.
      rewrite openup3_totop1.
      rewrite openup3_shrink.
      eapply totop with (n := 2); [ reflexivity | unfold removen ].
      rewrite lift_openup3.
      rewrite openup3_shrink.
      rewrite openup2_totop1.
      rewrite openup2_shrink.
      eapply openup1_apply_in.
      {
        intros.
        eapply inj_exists_elim.
      }
      eapply openup1_exists1_elim.
      repeat rewrite liftPs_cons.
      repeat rewrite lift_openup4.
      combine_lift.
      unfold liftPs, liftPs1, map.
      eapply dup_premise.
      eapply openup2_apply_in.
      {
        intros.
        eapply imply_trans; last first.
        {
          eapply inj_imply.
          {
            eapply app_wrunsto_elim.
          }
        }
        eapply inj_exists_elim.
      }
      eapply openup2_exists1_elim.
      repeat rewrite liftPs_cons.
      repeat rewrite lift_openup4.
      combine_lift.
      unfold liftPs, liftPs1, map.
      eapply openup3_apply_in.
      {
        intros.
        eapply inj_and_elim.
      }
      rewrite openup3_and.
      eapply destruct_and.
      rewrite openup3_totop1.
      rewrite openup3_shrink.
      eapply totop with (n := 5); [ reflexivity | unfold removen ].
      eapply dup_premise.
      eapply openup4_apply_in.
      {
        intros.
        eapply relE_elim.
      }
      rewrite openup4_and.
      eapply destruct_and.
      eapply totop with (n := 1); [ reflexivity | unfold removen ].
      rewrite openup4_and.
      eapply destruct_and.
      eapply totop with (n := 1); [ reflexivity | unfold removen ].
      rewrite openup4_and.
      eapply destruct_and.
      rewrite openup4_totop2.
      rewrite openup4_shrink.
      rewrite openup3_totop2.
      rewrite openup3_shrink.
      repeat rewrite lift_openup2.
      rewrite lift_openup3.
      combine_lift.
      eapply openup2_forall1_elim with (x := V2).
      eapply openup3_forall1_elim with (x := V0).
      rewrite openup4_imply.
      eapply imply_eelim.
      {
        set (Ps := [_;_;_;_;_;_;_;_;_;_;_;_]).
        eapply openup4_apply.
        {
          intros.
          eapply inj_and_intro.
        }
        rewrite openup4_and.
        eapply split.
        {
          rewrite openup4_totop1.
          rewrite openup4_shrink.
          rewrite openup3_totop2.
          rewrite openup3_shrink.
          subst Ps.
          eapply totop with (n := 7); [ reflexivity | unfold removen ].
          eapply openup2_apply_in.
          {
            intros.
            eapply inj_imply.
            {
              Lemma runstoEx_runsto e m v : ⇓*# e m v -> e ⇓ v.
                admit.
              Qed.
              eapply runstoEx_runsto.
            }
          }
          eapply ctx_refl.
        }
        rewrite openup4_shrink.
        rewrite openup3_totop1.
        rewrite openup3_shrink.
        subst Ps.
        eapply totop with (n := 4); [ reflexivity | unfold removen ].
        eapply ctx_refl.
      }
      rewrite openup4_shrink.
      rewrite openup3_shrink.
      rewrite openup2_and.
      eapply destruct_and.
      eapply totop with (n := 11); [ reflexivity | unfold removen ].
      eapply dup_premise.
      unfold relEC at 1.
      rewrite openup4_totop2.
      rewrite openup4_shrink.
      rewrite openup3_totop2.
      rewrite openup3_shrink.
      eapply openup2_forall1_elim with (x := V2).
      eapply openup3_forall1_elim with (x := V0).
      rewrite openup4_imply.
      eapply imply_eelim.
      {
        set (Ps := [_;_;_;_;_;_;_;_;_;_;_;_;_;_]).
        rewrite openup4_and.
        eapply split.
        {
          rewrite openup4_shrink.
          rewrite openup3_shrink.
          subst Ps.
          eapply totop with (n := 1); [ reflexivity | unfold removen ].
          eapply ctx_refl.
        }
        eapply openup4_apply.
        {
          intros.
          eapply inj_and_intro.
        }
        rewrite openup4_and.
        eapply split.
        {
          rewrite openup4_totop1.
          rewrite openup4_shrink.
          rewrite openup3_totop2.
          rewrite openup3_shrink.
          subst Ps.
          eapply totop with (n := 10); [ reflexivity | unfold removen ].
          eapply openup2_apply_in.
          {
            intros.
            eapply inj_imply.
            {
              intros H.
              eapply runstoEx_runsto in H.
              unfold runsto in H.
              destruct H as [H1 H2].
              exact H1.
            }
          }
          eapply ctx_refl.
        }
        rewrite openup4_shrink.
        eapply openup3_apply.
        {
          intros.
          eapply inj_and_intro.
        }
        rewrite openup3_and.
        eapply split.
        {
          rewrite openup3_shrink.
          rewrite openup2_totop1.
          rewrite openup2_shrink.
          subst Ps.
          eapply totop with (n := 2); [ reflexivity | unfold removen ].
          rewrite openup2_totop1.
          rewrite openup2_shrink.
          eapply ctx_refl.
        }
        rewrite openup3_totop1.
        rewrite openup3_shrink.
        subst Ps.
        eapply totop with (n := 7); [ reflexivity | unfold removen ].
        eapply openup2_apply_in.
        {
          intros.
          eapply inj_imply.
          {
            intros H.
            unfold wrunsto in H.
            destruct H as [H1 H2].
            exact H1.
          }
        }
        eapply ctx_refl.
      }
      rewrite openup4_shrink.
      rewrite openup3_totop2.
      rewrite openup3_shrink.
      eapply openup2_apply_in.
      {
        intros.
        eapply relE_elim.
      }
      rewrite openup2_and.
      eapply destruct_and.
      eapply totop with (n := 1); [ reflexivity | unfold removen ].
      rewrite openup2_and.
      eapply destruct_and.
      eapply totop with (n := 1); [ reflexivity | unfold removen ].
      rewrite openup2_and.
      eapply destruct_and.
      eapply totop with (n := 1); [ reflexivity | unfold removen ].
      rewrite openup2_and.
      eapply destruct_and.
      eapply openup2_forall1_elim with (x := V3).
      rewrite openup3_imply.
      eapply imply_eelim.
      {
        set (Ps := [_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_]).
        eapply openup3_apply.
        {
          intros.
          eapply inj_and_intro.
        }
        rewrite openup3_and.
        eapply split.
        {
          rewrite openup3_shrink.
          subst Ps.
          eapply totop with (n := 15); [ reflexivity | unfold removen ].
          rewrite openup3_shrink.
          rewrite openup2_totop1.
          eapply ctx_refl.
        }
        rewrite openup3_totop1.
        rewrite openup3_shrink.
        rewrite openup2_totop1.
        rewrite openup2_shrink.
        eapply openup1_apply.
        {
          intros.
          eapply inj_exists_intro.
        }
        eapply openup1_exists1 with (x := V1).
        subst Ps.
        eapply totop with (n := 13); [ reflexivity | unfold removen ].
        rewrite openup2_totop1.
        eapply ctx_refl.
      }
      rewrite openup3_totop1.
      rewrite openup3_shrink.
      rewrite openup2_and.
      eapply destruct_and.
      rewrite openup2_shrink.
      rewrite openup1_shrink.
      set (Ps := [_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_]).
      rewrite openup4_and.
      eapply split.
      {
        rewrite openup4_shrink.
        rewrite openup3_totop1.
        rewrite openup3_shrink.
        rewrite openup2_totop1.
        rewrite openup2_shrink.
        eapply openup1_apply.
        {
          intros.
          eapply inj_imply.
          Lemma Fadd_gt_0 (a b : cexpr) : 0 < !b -> 0 < !(a + b).
            admit.
          Qed.
          eapply Fadd_gt_0.
        }
        rewrite openup1_shrink.
        subst Ps.
        eapply ctx_refl.
      }
      Definition wle : width_nat -> width_nat -> Prop.
        admit.
      Qed.
      Global Instance Le_width_nat : Le width_nat width_nat :=
        {
          le := wle
        }.
      Lemma relE_mono_wB_c lctx τ c c' s ctx (ρ : csubsts lctx ctx) e w wB wB' : 
        [] |~~ (e, w) ∈ relE τ wB c s ρ /\ [| c <= c' /\ wB <= wB' |] ===> (e, w) ∈ relE τ wB' c' s ρ.
        admit.
      Qed.
      Definition ORlater {ctxfo ctx} chg : open_rel ctxfo 0 (change_usab chg ctx) -> open_rel ctxfo 0 ctx := openup1 (Rlater chg).
      Notation "▹" := ORlater : OR.
      Notation "|>" := Rlater (only parsing) : rel.
      Notation "|>" := ORlater (only parsing) : OR.
      Lemma VMono ctxfo ctx Ps (P : open_rel ctxfo 0 ctx) : Ps |~ P -> Ps |~ (|> [] P)%OR.
        admit.
      Qed.
      Lemma openup4_later ctx t1 t2 t3 t4 (f : t1 -> t2 -> t3 -> t4 -> rel 0 ctx) ctxfo x1 x2 x3 x4 : openup4 (ctx := ctxfo) (fun x1 x2 x3 x4 => ▹ [] (f x1 x2 x3 x4)) x1 x2 x3 x4 = (▹ [] (openup4 f x1 x2 x3 x4))%OR.
        admit.
      Qed.
      rewrite openup4_later.
      Lemma later_mono_ctx ctxfo ctx (P Q : open_rel ctxfo 0 ctx) Ps :
        (P :: Ps |~ Q ->
        Ps |~ |> [] P ->
        Ps |~ |> [] Q)%OR.
        admit.
      Qed.
      eapply later_mono_ctx.
      {
        eapply openup4_apply.
        {
          intros.
          eapply relE_mono_wB_c with (τ := τ') (wB := wBE $$ x1) (c := !c₂ - 1).
        }
        eapply ctx_refl.
      }
      rewrite openup4_and.
      Lemma later_and_distr ctxfo ctx (P Q : open_rel ctxfo 0 ctx) : (|> [] (P /\ Q) == ((|> [] P) /\ (|> [] Q)))%OR.
        admit.
      Qed.
      rewrite later_and_distr.
      eapply split.
      {
        rewrite openup4_totop1.
        rewrite openup4_shrink.
        rewrite openup3_totop1.
        rewrite openup3_shrink.
        subst Ps.
        eapply totop with (n := 1); [ reflexivity | unfold removen ].
        eapply ctx_refl.
      }
      eapply VMono.
      rewrite openup4_totop3.
      rewrite openup4_shrink.
      eapply openup3_apply.
      {
        intros.
        eapply inj_imply.
        intros H.
        Lemma relE_mono_wB_c_VC (c₁ c₂ : cexpr) (wBE : open_width WTnat [CEexpr]) (w : width) (w' : width_nat) : !c₂ - 1 ≤ !(c₁ + c₂) - 1 /\ wBE $$ w ≤ w' + wBE $$ w.
          admit.
        Qed.
        eapply relE_mono_wB_c_VC.
      }
      instantiate (1 := True).
      rewrite openup3_shrink.
      rewrite openup2_shrink.
      rewrite openup1_shrink.
      Lemma inj_true_intro ctxfo ctx (Ps : list (open_rel ctxfo 0 ctx)) : Ps |~ openup0 [| True |].
        admit.
      Qed.
      eapply inj_true_intro.
    }
    (*here*)
      





    admit. 
  }
  rewrite openup3_and.
  eapply split.
  {
    Lemma split_exists A B P Q :
      ((exists a, P a) /\ (exists b, Q b) ->
      exists (a : A) (b : B), P a /\ Q b)%type.
    Proof.
      intros H.
      destruct H as [[a Ha] [b Hb]].
      exists a b.
      eauto.
    Qed.
    rewrite openup3_totop1.
    rewrite openup3_shrink.
    rewrite openup2_totop1.
    rewrite openup2_shrink.
    Lemma plug_runsto E e :
      (exists v, e ⇓ v /\ exists v', E $$ v ⇓ v')%type ->
      (exists v, E $$ e ⇓ v).
      admit.
    Qed.
    eapply openup1_apply.
    {
      intros.
      eapply imply_trans.
      {
        eapply inj_imply.
        {
          eapply plug_runsto.
        }
      }
      eapply inj_exists_intro.
    }
    subst Ps.
    combine_lift.
    eapply openup4_apply_in.
    {
      intros.
      eapply relE_elim.
    }
    rewrite openup4_and.
    eapply destruct_and.
    eapply totop with (n := 1); [ reflexivity | unfold removen ].
    rewrite openup4_and.
    eapply destruct_and.
    eapply totop with (n := 1); [ reflexivity | unfold removen ].
    rewrite openup4_and.
    eapply destruct_and.
    eapply totop with (n := 1); [ reflexivity | unfold removen ].
    rewrite openup4_and.
    eapply destruct_and.
    eapply totop with (n := 1); [ reflexivity | unfold removen ].
    rewrite openup4_and.
    eapply destruct_and.
    rewrite openup4_totop1.
    rewrite openup4_shrink.
    rewrite openup3_totop1.
    rewrite openup3_shrink.
    rewrite openup2_totop1.
    rewrite openup2_shrink.
    eapply openup1_apply_in.
    {
      intros.
      eapply inj_exists_elim.
    }
    eapply openup1_exists1_elim.
    repeat rewrite liftPs_cons.
    repeat rewrite lift_openup4.
    combine_lift.
    unfold liftPs, liftPs1, map.
    eapply totop with (n := 1); [ reflexivity | unfold removen ].
    rewrite openup4_shrink.
    rewrite openup3_totop1.
    rewrite openup3_shrink.
    rewrite openup2_totop1.
    rewrite openup2_shrink.
    eapply openup1_apply_in.
    {
      intros.
      eapply inj_exists_elim.
    }
    eapply openup1_exists1_elim.
    repeat rewrite liftPs_cons.
    repeat rewrite lift_openup4.
    combine_lift.
    unfold liftPs, liftPs1, map.
    eapply totop with (n := 3); [ reflexivity | unfold removen ].
    rewrite openup4_totop2.
    rewrite openup4_shrink.
    rewrite openup3_totop2.
    rewrite openup3_shrink.
    eapply openup2_forall1_elim with (x := V1).
    eapply openup3_forall1_elim with (x := V0).
    eapply eqv_premise.
    {
      eapply openup4_imply.
    }
    eapply imply_eelim.
    {
      set (Ps := [_;_;_;_;_;_;_;_]).
      eapply openup4_apply.
      {
        intros.
        eapply inj_and_intro.
      }
      rewrite openup4_and.
      eapply split.
      {
        rewrite openup4_totop1.
        rewrite openup4_shrink.
        rewrite openup3_totop2.
        rewrite openup3_shrink.
        subst Ps.
        eapply totop with (n := 1); [ reflexivity | unfold removen ].
        erewrite lift_openup2.
        eapply ctx_refl.
      }
      rewrite openup4_shrink.
      rewrite openup3_totop1.
      rewrite openup3_shrink.
      subst Ps.
      eapply ctx_refl.
    }
    rewrite openup4_shrink.
    rewrite openup3_shrink.
    rewrite openup2_and.
    eapply destruct_and.
    eapply totop with (n := 7); [ reflexivity | unfold removen ].
    rewrite openup4_totop2.
    rewrite openup4_shrink.
    rewrite openup3_totop2.
    rewrite openup3_shrink.
    eapply dup_premise.
    unfold relEC at 1.
    eapply openup2_forall1_elim with (x := V1).
    eapply openup3_forall1_elim with (x := V0).
    eapply eqv_premise.
    {
      eapply openup4_imply.
    }
    eapply imply_eelim.
    {
      rewrite openup4_and.
      eapply split.
      {
        repeat rewrite openup4_shrink.
        repeat rewrite openup3_shrink.
        eapply totop with (n := 1); [ reflexivity | unfold removen ].
        eapply ctx_refl.
      }
      admit. (* ⌈x1 ~>* x3 /\ !x3 ≤ s₁ /\ wsteps x2 x4⌉ *)
    }
    rewrite openup4_shrink.
    rewrite openup3_shrink.
    rewrite openup2_totop1.
    rewrite openup2_shrink.
    eapply openup1_apply_in.
    {
      intros.
      eapply relE_elim.
    }
    eapply eqv_premise; [ eapply openup1_and | ].
    eapply destruct_and.
    eapply totop with (n := 1); [ reflexivity | unfold removen ].
    eapply eqv_premise; [ eapply openup1_and | ].
    eapply destruct_and.
    eapply totop with (n := 1); [ reflexivity | unfold removen ].
    eapply eqv_premise; [ eapply openup1_and | ].
    eapply destruct_and.
    eapply totop with (n := 1); [ reflexivity | unfold removen ].
    eapply eqv_premise; [ eapply openup1_and | ].
    eapply destruct_and.
    eapply totop with (n := 1); [ reflexivity | unfold removen ].
    eapply eqv_premise; [ eapply openup1_and | ].
    eapply destruct_and.
    set (Ps := [_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_]).
    rewrite lift_openup1.
    eapply openup1_exists1 with (x := V1).
    eapply openup2_apply.
    {
      intros.
      eapply inj_and_intro.
    }
    rewrite openup2_and.
    eapply split.
    {
      subst Ps.
      eapply totop with (n := 10); [ reflexivity | unfold removen ].
      erewrite lift_openup2.
      rewrite openup2_totop1.
      eapply ctx_refl.
    }
    rewrite openup2_totop1.
    rewrite openup2_shrink.
    subst Ps.
    eapply ctx_refl.
  }
  admit.
Qed.

Lemma LRbind''' E (wEe : width) (wBEe : open_width WTnat []) s₁ c₂ s₂ {lctx lctx'} (τ : open_type lctx) (τ' : open_type lctx') ctx (ρ : csubsts lctx ctx) (ρ' : csubsts lctx' ctx) e we c₁ wBe :
  [] |~~ 
     ⌈IsEC E⌉ /\
  (e, we) ∈ relE τ wBe !c₁ s₁ ρ /\ 
  relEC E e we wEe wBEe s₁ c₂ s₂ τ τ' ρ ρ' ===> 
        (E $$ e, wEe) ∈ relE τ' (wBe + wBEe) !(c₁ + c₂) s₂ ρ'.
Proof.
  eapply forall1_elim4 with (
    P := fun e we c₁ wBe =>
           ⌈IsEC E⌉ /\
           (e, we) ∈ relE τ wBe !c₁ s₁ ρ /\
           relEC E e we wEe wBEe s₁ c₂ s₂ τ τ' ρ ρ' ===>
                 (E $$ e, wEe) ∈ relE τ' (wBe + wBEe) !(c₁ + c₂) s₂ ρ'
  ).
  eapply LRbind.
Qed.

Lemma LRbind'' E (wEe : width) (wBEe : open_width WTnat []) s₁ c₂ s₂ {lctx lctx'} (τ : open_type lctx) (τ' : open_type lctx') ctx (ρ : csubsts lctx ctx) (ρ' : csubsts lctx' ctx) e c₁ wBe :
  [] |~~ 
     (∃we, ⌈IsEC E⌉ /\
           (e, we) ∈ relE τ wBe !c₁ s₁ ρ /\ 
           relEC E e we wEe wBEe s₁ c₂ s₂ τ τ' ρ ρ') ===> 
     (E $$ e, wEe) ∈ relE τ' (wBe + wBEe) !(c₁ + c₂) s₂ ρ'.
Proof.
  eapply imply_intro.
  eapply exists1_elim.
  rewrite <- openup0_lift_1.
  erewrite <- (openup1_shrink (x1 := V0)).
  eapply openup1_apply.
  {
    intros.
    eapply LRbind''' with (we := x1) (s₁ := s₁) (τ := τ) (ρ := ρ).
  }
  eapply ctx_refl.
Qed.

Lemma LRbind' ctxfo (e : open_term ctxfo expr) (we : open_term ctxfo width) (wBe : open_term ctxfo width_nat) (E : open_term ctxfo econtext) (wEe : open_term ctxfo width) (wBEe : open_term ctxfo width_nat) lctx (c₁ : open_cexpr lctx) (s₁ : open_size lctx) (c₂ : open_cexpr lctx) (s₂ : open_size lctx) (τ : open_type lctx) (τ' : open_type lctx) ctx (ρ : open_csubsts ctxfo lctx ctx) (Ps : list (open_rel ctxfo 0 ctx)) :
  Ps |~ openup1 (fun E => ⌈IsEC E⌉) E ->
  Ps |~ openup4 (fun ρ e we wBe => (e, we) ∈ relE τ wBe !(ρ $ c₁) (ρ $ s₁) ρ) ρ e we wBe ->
  Ps |~ openup6 (fun ρ E e we wEe wBEe => relEC E e we wEe wBEe (ρ $ s₁) (ρ $ c₂) (ρ $ s₂) τ τ' ρ ρ) ρ E e we wEe wBEe ->
  Ps |~ openup5 (fun ρ E e wEe wBall => (E $$ e, wEe) ∈ relE τ' wBall !(ρ $ (c₁ + c₂)) (ρ $ s₂) ρ) ρ E e wEe (wBe + wBEe).
Proof.
  intros H1 H2 H3.
  rewrite openup5_totop4.
  set (ttt := wBe + wBEe).
  simpl in ttt.
  subst ttt.
  rewrite openup5_comp_openup2.
  eapply openup6_apply.
  {
    intros.
    rewrite csubsts_Fadd.
    eapply LRbind'' with (E := x4) (s₁ := x3 $ s₁) (τ := τ) (ρ := x3).
  }
  eapply openup6_exists1 with (x := we).
  rewrite openup7_and.
  eapply split.
  {
    rewrite openup7_shrink.
    admit. (* IsEC *)
  }
  rewrite openup7_and.
  eapply split.
  {
    rewrite openup7_totop2.
    rewrite openup7_shrink.
    rewrite openup6_totop3.
    rewrite openup6_shrink.
    rewrite openup5_totop4.
    rewrite openup5_shrink.
    rewrite openup4_totop3.
    rewrite openup4_totop3.
    eauto.
  }      
  rewrite openup7_totop1.
  rewrite openup7_shrink.
  rewrite openup6_totop1.
  rewrite openup6_totop5.
  rewrite openup6_totop2.
  rewrite openup6_totop5.
  rewrite openup6_totop5.
  rewrite openup6_totop5.
  eauto.
(*
    Inductive typingEC : econtext -> type -> type -> Prop :=
    | TECempty τ : typingEC ECempty τ τ
    | TECapp1 f arg τ τ₁ c s τ₂ :
        typingEC f τ (Tarrow τ₁ c s τ₂) ->
        (|- arg τ₁) ->
        typingEC (ECapp1 f arg) τ τ₂
    .

      Lemma imply_elim ctxfo lctx ctx (P Q : csubsts lctx ctx -> rel 0 ctx) (ρ : open_csubsts ctxfo lctx ctx) Ps : 
        Ps |~ openup1 (fun ρ => P ρ ===> Q ρ) ρ ->
        Ps |~ openup1 (fun ρ => P ρ) ρ ->
        Ps |~ openup1 (fun ρ => Q ρ) ρ.
        admit.
      Qed.
      Lemma imply_elim3 ctxfo lctx ctx (P1 P2 P3 Q : csubsts lctx ctx -> rel 0 ctx) (ρ : open_csubsts ctxfo lctx ctx) Ps : 
        Ps |~ openup1 (fun ρ => P1 ρ /\ P2 ρ /\ P3 ρ ===> Q ρ) ρ ->
        Ps |~ openup1 (fun ρ => P1 ρ) ρ ->
        Ps |~ openup1 (fun ρ => P2 ρ) ρ ->
        Ps |~ openup1 (fun ρ => P3 ρ) ρ ->
        Ps |~ openup1 (fun ρ => Q ρ) ρ.
        admit.
      Qed.
      Lemma imply_elim_e ctx (P Q : rel 0 ctx) Ps : 
        Ps |~~ P ===> Q ->
        Ps |~ P ->
        Ps |~ Q.
      Proof.
        admit.
      Qed.
      Lemma imply_gen_e ctx (P Q : rel 0 ctx) Ps :
        Ps |~~ P ===> Q ->
        P :: Ps |~~ Q.
      Proof.
        intros H.
        eapply imply_elim_e.
        {
          Lemma add_Ps ctxfo ctx (P Q : open_rel ctxfo 0 ctx) Ps : Ps |~ Q -> P :: Ps |~ Q.
            admit.
          Qed.
          eapply add_Ps.
          eauto.
 }
        eapply ctx_refl.
      Qed.
      Lemma imply_gen ctxfo lctx ctx (ρ : open_csubsts ctxfo lctx ctx) (P Q : csubsts lctx ctx -> rel 0 ctx) Ps :
        Ps |~ openup1 (fun ρ => P ρ ===> Q ρ) ρ ->
        openup1 P ρ :: Ps |~ openup1 Q ρ.
      Proof.
        intros H.
        eapply imply_elim.
        {
          eapply add_Ps.
          eauto.
        }
        eapply ctx_refl.
      Qed.
      eapply imply_elim3; eauto.
      Lemma VMorePs ctxfo ctx (P : open_rel ctxfo 0 ctx) Ps : [] |~ P -> Ps |~ P.
        admit.
      Qed.
      eapply VMorePs.
      eapply VCtxElimEmpty.
      rename ρ into ρ'.
      intros ρ.
      assert (Hassert :
                []
                  |~~ ⌈IsEC (ρ $$ E) ⌉ /\
                (ρ $$ e, ρ $$ we) ∈ relE τ (ρ $$ wBe) !(ρ $$ c₁) (ρ $$ s₁) ρ /\
                relEC (ρ $$ E) (ρ $$ e) (ρ $$ we) (ρ $$ wEe) 
                      (ρ $$ wBEe) (ρ $$ s₁) (ρ $$ c₂) (ρ $$ s₂) τ τ' ρ ρ ===>
                      ((ρ $ E) $ (ρ $ e), ρ $$ wEe)
                      ∈ relE τ' (ρ $$ wBe + ρ $$ wBEe) !(ρ $$ c₁ + ρ $$ c₂) (ρ $$ s₂) ρ
             ).
      {
        eapply forall1_elim4 with (
          P := fun (e : expr) (we : width) (c₁ : cexpr) (wBe : open_width WTnat []) =>
                 ⌈IsEC (ρ $$ E) ⌉ /\
                 (e, we) ∈ relE τ wBe !c₁ (ρ $$ s₁) ρ /\
                 relEC (ρ $$ E) e we (ρ $$ wEe) 
                       (ρ $$ wBEe) (ρ $$ s₁) (ρ $$ c₂) (ρ $$ s₂) τ τ' ρ ρ ===>
                       (ρ $$ E $$ e, ρ $$ wEe)
                       ∈ relE τ' (wBe + ρ $$ wBEe) !(c₁ + ρ $$ c₂) (ρ $$ s₂) ρ
        ).
        eapply LRbind.
      }
 *)
Qed.

Definition related {lctx} Γ wB w (e : open_expr lctx) τ (c : open_cexpr lctx) (s : open_size lctx) :=
  make_Ps (lctx := lctx) Γ |~ let ρ := make_ρ lctx in openup4 (fun ρ e w wB => (e, w) ∈ relE τ wB !(ρ $ c) (ρ $ s) ρ) ρ (ρ $ e) (ρ $ w) (ρ $ wB).

(* Definition related {lctx} Γ wB w (e : open_expr lctx) τ (c : open_cexpr lctx) (s : open_size lctx) := *)
(*   make_Ps (lctx := lctx) Γ |~ openup1 (fun ρ => (ρ $$ e, ρ $$ w) ∈ relE τ (ρ $ wB) !(ρ $ c) (ρ $ s) ρ)%rel (make_ρ lctx). *)

(*

Definition related {lctx} Γ wB w (e : open_expr lctx) τ (c : open_cexpr lctx) (s : open_size lctx) :=
  make_Ps (lctx := lctx) Γ |~ let ρ := make_ρ lctx in (ρ $$ e, ρ $$ w) ∈ openup1 (fun ρ => relE τ (ρ $ wB) !(ρ $ c) (ρ $ s) ρ) ρ.

*)

Notation "⊩" := related.

Lemma foundamental :
  forall ctx (Γ : tcontext ctx) e τ c s,
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
    unfold related in *.

    destruct IHtyping1 as [wB₀ [w₀ IH₀]].
    destruct IHtyping2 as [wB₁ [w₁ IH₁]].

    exists (wB₀ + (wB₁ + (Wconst 1 + WappB w₀ w₁))).
    exists (Wapp w₀ w₁).

    rename ctx into lctx.
    set (ρ := make_ρ lctx) in *.
    set (ctx := make_ctx lctx) in *.
    set (Ps := make_Ps Γ) in *.

    rewrite open_csubsts_Wadd.
    rewrite open_csubsts_Eapp.
    rewrite <- open_ECapp1.
    
    rewrite openup4_totop1.
    rewrite openup4_comp_openup2.
    rewrite openup5_totop2.

    eapply LRbind' with (c₂ := c₁ + subst s₁ c) (s₂ := subst s₁ s) (τ' := subst s₁ τ₂). 
    {
      admit. (* IsEC *)
    }
    {
      eapply IH₀.
    }
    {
      unfold relEC.

      eapply relE_relEC.
      rewrite open_csubsts_Wadd.
      rewrite lift_Wadd.
      rewrite lift_openup1.
      rewrite unfold_open_plug.
      rewrite open_ECapp1.
      rewrite <- open_ECapp2.
      rewrite openup4_totop1.
      rewrite openup4_comp_openup2.
      rewrite (openup5_totop2 (x2 := lift ρ)).
      eapply LRbind'.
      {
        admit. (* IsEC *)
      }
      {
        instantiate (1 := lift (ρ $ w₁)).
        instantiate (1 := s₁).
        instantiate (1 := τ₁).
        admit. (* eapply IH₁ *)
      }
      {
        unfold relEC.
        eapply relE_relEC.
        rewrite liftPs_cons.
        rewrite lift_openup5.
        rewrite lift_openup1.
        rewrite liftPs_liftPs.
        combine_lift.
        rewrite unfold_open_plug.
        rewrite open_ECapp2.
        rewrite open_csubsts_Wadd.
        repeat rewrite lift_Wadd.
        repeat rewrite lift_rho_width.
        repeat rewrite lift_rho_expr.
        rewrite openup4_totop1.
        rewrite openup4_comp_openup2.
        erewrite (openup5_totop2 (x2 := lift (new := [width : Type; expr; width : Type; expr]) ρ)).
        rewrite open_csubsts_Wapp.
        rewrite open_csubsts_WappB.
        set (ρ' := lift ρ) in *.
        set (e₀' := ρ' $ e₀) in *.
        set (e₁' := ρ' $ e₁) in *.
        set (w₀' := ρ' $ w₀) in *.
        set (w₁' := ρ' $ w₁) in *.
        rewrite open_csubsts_Wconst.
        eapply totop with (n := 1); [ reflexivity | unfold removen ].
        rewrite openup5_and.
        eapply destruct_and.

        rewrite openup5_totop1.
        rewrite openup5_shrink.
        rewrite openup4_totop1.
        rewrite openup4_shrink.

        set (tmp := relV (Tarrow τ₁ c s τ₂)) at 1.
        simpl in tmp.
        subst tmp.
        rewrite openup3_beta.

        rewrite openup3_and.
        eapply destruct_and.

        eapply totop with (n := 1); [ reflexivity | unfold removen ].

        eapply openup3_exists1_elim.
        repeat rewrite liftPs_cons.
        repeat rewrite lift_openup5.
        rewrite openup4_and.
        eapply destruct_and.
        eapply totop with (n := 1); [ reflexivity | unfold removen ].
        rewrite openup4_totop2.

        rewrite openup4_shrink.
        eapply openup3_exists1_elim.
        repeat rewrite liftPs_cons.
        repeat rewrite lift_openup5.
        eapply openup4_exists1_elim.
        repeat rewrite liftPs_cons.
        repeat rewrite lift_openup5.
        rewrite openup5_and.
        eapply destruct_and.
        eapply totop with (n := 1); [ reflexivity | unfold removen ].
        rewrite openup5_totop1.
        rewrite openup5_shrink.
        rewrite openup4_totop1.

        Lemma openup4_forall1_elim' t1 t2 t3 t4 ctx (f : t1 -> t2 -> t3 -> t4 -> wexpr -> rel 0 ctx) ctxfo x1 x2 x3 x4 e w Ps Q :
          openup6 (ctx := ctxfo) (fun x1 x2 x3 x4 w e => f x1 x2 x3 x4 (e, w)) x1 x2 x3 x4 w e :: Ps |~ Q ->
          openup4 (fun x1 x2 x3 x4 => ∀x, f x1 x2 x3 x4 x) x1 x2 x3 x4 :: Ps |~ Q.
        Proof.
          intros H.
          eapply openup4_forall1_elim with (x := openup2 pair e w).
          rewrite openup5_totop4.
          rewrite openup5_comp_openup2.
          rewrite openup6_totop1.
          do 4 rewrite openup6_totop5.
          eauto.
        Qed.

        eapply openup4_forall1_elim' with (e := V4) (w := V3).
        rewrite openup6_imply.
        rewrite openup6_shrink.
        rewrite openup5_totop1.
        rewrite openup5_shrink.
        rewrite openup4_totop1.
        rewrite openup4_shrink.
        eapply totop with (n := 5); [ reflexivity | unfold removen ].
        rewrite openup5_and.
        eapply destruct_and.
        rewrite openup5_totop1.
        rewrite openup5_shrink.
        rewrite openup4_totop1.
        rewrite openup4_shrink.
        eapply totop with (n := 2); [ reflexivity | unfold removen ].
        eapply imply_elim.
        subst e₀' e₁' w₀' w₁' ρ'.
        combine_lift.
        repeat rewrite lift_openup4.
        repeat rewrite lift_openup3.
        repeat rewrite lift_openup2.
        repeat rewrite lift_openup0.
        repeat rewrite lift_Wadd.
        repeat rewrite lift_rho_width.
        repeat rewrite lift_rho_expr.
        combine_lift.
        set (ρ' := lift ρ) in *.
        rewrite (openup5_totop3 (x3 := openup2 _ _ _)).
        rewrite openup5_comp_openup2.
        rewrite (openup6_totop5 (x5 := openup2 _ _ _)).

        rewrite openup6_comp_openup2.

        rewrite openup7_comp_openup0.
        rewrite openup6_comp_openup2.

        rewrite openup7_totop2.

        rewrite openup7_dedup.

        rewrite (openup6_totop1 (x1 := ρ' $ w₁ )).
        rewrite (openup6_totop2 (x2 := ρ' $ w₁ )).
        rewrite openup6_dedup.


        erewrite (rewrite_openup5 (x0 := ρ' $ w₁)); last first.
        {
          repeat extensionality'.
          rewrite csubsts_subst_s_c.
          rewrite csubsts_subst_s_s.
          reflexivity.
        }

        eapply openup5_apply.
        {
          intros.
          eapply relE_mono_tau_c_s with (v := x5).
        }
        rewrite openup5_and.
        eapply split.
        {
          eapply openup5_apply.
          {
            intros.
            eapply relE_rho with (w' := x1).
          }
          eapply openup5_apply.
          {
            intros.
            eapply relE_app_subst. 
          }

          eapply openup5_exists1 with (x := V2).
          eapply openup6_exists1 with (x := V0).
          eapply openup7_exists1 with (x := V1).
          rewrite openup8_and.
          eapply split.
          {
            rewrite openup8_totop6.
            rewrite openup8_shrink.
            rewrite openup7_totop4.
            rewrite openup7_shrink.
            eapply openup6_apply.
            {
              intros.
              eapply relE_replace_width.
            }
            eapply openup6_exists1 with (x := V3).
            rewrite openup7_and.
            eapply split.
            {
              rewrite openup7_totop4.
              rewrite openup7_shrink.
              rewrite openup6_totop1.
              rewrite openup6_totop1.
              rewrite openup6_totop3.
              rewrite openup6_totop3.
              rewrite openup6_totop4.
              erewrite rewrite_openup6; last first.
              {
                repeat extensionality'.
                rewrite csubsts_subst_s_c.
                rewrite csubsts_subst_s_s.
                repeat rewrite csubsts_value.
                reflexivity.
              }
              eapply ctx_refl.
            }
            admit. (* wsteps *)
          }
          admit. (* = Eabs /\ = Wabs *)
        }
        admit. (* !v <= rho $ s1 *)
      }
    }
  }
  {
      (*here*)





































        Global Instance Apply_open_rel_open_wexpr {ctxfo m ctx} : Apply (open_rel ctxfo (S m) ctx) (open_term ctxfo wexpr) (open_rel ctxfo m ctx) :=
          {
            apply := ORapp
          }.

        Definition ORapp' {ctxfo m ctx} : open_rel ctxfo (S m) ctx -> open_term ctxfo expr * open_term ctxfo width -> open_rel ctxfo m ctx.
          admit.
        Defined.

        Global Instance Apply_open_rel_open_expr_open_width {ctxfo m ctx} : Apply (open_rel ctxfo (S m) ctx) (open_term ctxfo expr * open_term ctxfo width) (open_rel ctxfo m ctx) :=
          {
            apply := ORapp'
          }.

        Lemma VElem ctxfo m ctx (r : wexpr -> open_rel ctxfo m ctx) x : x ∈ (ORabs r) == r x.
          admit.
        Qed.
        Lemma ttt1 ctx (P2 : rel 0 ctx) P x : 
          Forall2 eqv [x ∈ \x, P x; P2] [P x; P2].
          rewrite VElem.
          reflexivity.
        Qed.
        Lemma ttt2 ctx (Q : rel 0 ctx) P P2 x : 
          [P x; P2] |~~ Q ->
          [x ∈ \x, P x; P2] |~~ Q.
          intros H.
          rewrite VElem.
          eauto.
        Qed.



        simpl.

        eapply imply_gen.
        eapply VMorePs.
        eapply VCtxElimEmpty.
        subst ρ.
        intros ρ.
        (* need to change EC to C and IsEC *)
        simpl in ρ.
          Lemma LRappvv lctx ctx (v₀ : expr) (w₀ w₀' : width) (τ₁ : open_type lctx) (c : open_cexpr (CEexpr :: lctx)) (s : open_size (CEexpr :: lctx)) (τ₂ : open_type (CEexpr :: lctx)) (ρ : csubsts lctx ctx) (w₁ : width) (s₁ : open_size lctx) P1 P2 Q :
            [] |~~ 
               (v₀, w₀') ∈ relV (Tarrow τ₁ c s τ₂) ρ /\ ⌈P1 /\ P2 /\ wsteps w₀ w₀'⌉ ===>
               ∀v we', (v, we') ∈ relV τ₁ ρ /\ ⌈Q v /\ !v ≤ ρ $$ s₁ /\ wsteps w₁ we'⌉ ===>
                       (Eapp v₀ v, Wapp w₀ w₁) ∈ relE (subst s₁ τ₂) (Wconst 1 + WappB w₀ w₁) !(ρ $ (subst s₁ c)) (ρ $ (subst s₁ s)) ρ.
          Proof.
            Lemma LRappvv' lctx ctx (v₀ : expr) (w₀ w₀' : width) (τ₁ : open_type lctx) (c : open_cexpr (CEexpr :: lctx)) (s : open_size (CEexpr :: lctx)) (τ₂ : open_type (CEexpr :: lctx)) (ρ : csubsts lctx ctx) (w₁ : width) (s₁ : open_size lctx) :
              [] |~~ 
                 (v₀, w₀') ∈ relV (Tarrow τ₁ c s τ₂) ρ /\ ⌈wsteps w₀ w₀'⌉ ===>
                 ∀v we', (v, we') ∈ relV τ₁ ρ /\ ⌈!v ≤ ρ $$ s₁ /\ wsteps w₁ we'⌉ ===>
                         (Eapp v₀ v, Wapp w₀ w₁) ∈ relE (subst s₁ τ₂) (Wconst 1 + WappB w₀ w₁) !(ρ $ (subst s₁ c)) (ρ $ (subst s₁ s)) ρ.
            Proof.
              Lemma imply_intro ctxfo lctx ctx (ρ : open_csubsts ctxfo lctx ctx) (P Q : csubsts lctx ctx -> rel 0 ctx) Ps :
                openup1 P ρ :: Ps |~ openup1 Q ρ ->
                Ps |~ openup1 (fun ρ => P ρ ===> Q ρ) ρ.
                admit.
              Qed.
              eapply imply_intro_e.
              eapply destruct_and.
              unfold tmp.
              rewrite VElem.
              eapply destruct_and.

              (*here*)

              Definition lift_e {T ctx} (r : rel 0 ctx) : open_rel [T] 0 ctx := fun _ => r.

              Lemma rdestruct_e ctx T (Q : rel 0 ctx) (P : T -> rel 0 ctx) Ps :
                (P : open_rel [T] _ _) :: liftPs1 T Ps |~ lift_e Q ->
                (∃x, P x) :: Ps |~~ Q.
                admit.
              Qed.
              eapply rdestruct_e.

              Lemma rdestruct_1 T1 T2 ctxfo ctx (Q : open_rel ctxfo 0 ctx) (P : T1 -> T2 -> rel 0 ctx) Ps :
                (P : open_rel [T1;T2] _ _) :: liftPs1 T Ps |~ lift_e Q ->
                (fun x1 => ∃x2, P x1 x2) :: Ps |~~ Q.
                admit.
              Qed.  
            Qed.
            admit.
          Qed.

          Definition pair_of_csubsts {lctx ctx} (ρ : csubsts (CEexpr :: lctx) ctx) : wexpr * csubsts lctx ctx.
            admit.
          Qed.

          Definition rhosnd {lctx ctx} (rho : csubsts (CEexpr :: lctx) ctx) := snd (pair_of_csubsts rho).
          assert (Hassert :
                    [] |~~
                       (ρ $$ Evar #0, ρ $$ Wvar #0)
                       ∈ relV (Tarrow τ₁ c s τ₂) (rhosnd ρ) /\
                    ⌈ρ $$ shift1 CEexpr e₀ ~>* ρ $$ Evar #0 /\
                    !(ρ $$ Evar #0) ≤ ρ $$ shift1 CEexpr nouse /\
                    wsteps (rhosnd ρ $ w₀) (ρ $$ Wvar #0) ⌉ ===>
                           (∀(v : expr) (we' : width),
                              (v, we') ∈ relV τ₁ (rhosnd ρ) /\
                              ⌈ρ $$ shift1 CEexpr e₁ ~>* v /\
                              !v ≤ rhosnd ρ $$ s₁ /\ wsteps (rhosnd ρ $ w₁) we' ⌉ ===>
                              (Eapp (ρ $ Evar #0) v, Wapp (rhosnd ρ $ w₀) (rhosnd ρ $ w₁))
                              ∈ relE (subst s₁ τ₂)
                              (Wconst 1 + WappB (rhosnd ρ $ w₀) (rhosnd ρ $ w₁))
                              !(rhosnd ρ $ subst s₁ c)
                              (rhosnd ρ $ subst s₁ s) (rhosnd ρ))).
          {
            eapply LRappvv.
          }
          admit. (* rearrange *)
        }
      }
      Lemma forall1intro ctxfo lctx ctx (ρ : open_csubsts ctxfo lctx ctx) (f : expr -> width -> csubsts lctx ctx -> rel 0 ctx) Ps :
        liftPs1 wexpr Ps |~ openup1 
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

      eapply forall1intro.
      eapply imply_intro.
      Lemma snd_pair_of_csubsts_cexpr lctx ctx (rho : csubsts (CEexpr :: lctx) ctx) (x : open_cexpr lctx) : snd (pair_of_csubsts rho) $$ x = rho $$ (shift1 CEexpr x).
        admit.
      Qed.
      Lemma snd_pair_of_csubsts_cexpr' lctx ctx (rho : csubsts (CEexpr :: lctx) ctx) (x : open_cexpr lctx) : csubsts_cexpr (snd (pair_of_csubsts rho)) x = csubsts_cexpr rho (shift1 CEexpr x).
        admit.
      Qed.
      simpl.
      (* erewrite snd_pair_of_csubsts_cexpr. *)
      (* erewrite snd_pair_of_csubsts_cexpr'. *)
      admit. (* rearrange *)
    }

    Lemma and_imply_and ctx (P P' Q Q' : rel 0 ctx) Ps :
      Ps |~~ P ===> P' ->
      Ps |~~ Q ===> Q' ->
      Ps |~~ P /\ Q ===> P' /\ Q'.
      admit.
    Qed.

    Lemma imply_refl ctx (P : rel 0 ctx) : [] |~~ P ===> P.
      admit.
    Qed.
    Instance Max_nat : Max nat :=
      {
        max := Peano.max
      }.
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

  Fixpoint Funvar_pr {var t} (R : t var -> t var -> Prop) {ctx} : Funvar var ctx t -> Funvar var ctx t -> Prop :=
    match ctx return Funvar var ctx t -> Funvar var ctx t -> Prop with
      | nil => R
      | t' :: ctx' => fun a b => forall x, Funvar_pr R (a x) (b x)
    end.

  Definition Funvar_eq {var t ctx} (a b : Funvar var ctx t) := Funvar_pr eq a b.

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

