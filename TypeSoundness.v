(* Type soundness *)

Require Import List.
Require Import Program.
Require Import Util.
Require Import Typing EvalCBV.

Import ListNotations.
Local Open Scope list_scope.

Set Implicit Arguments.

Local Notation open_var := var.
Local Notation open_cexpr := cexpr.
Local Notation open_size := size.
Local Notation open_type := type.
Local Notation open_expr := expr.
Local Notation cexpr := (open_cexpr []).
Local Notation size := (open_size []).
Local Notation type := (open_type []).
Local Notation expr := (open_expr []).

(* encoding of fix by recursive-type :
     fix f(x).e := \y. (unfold v) v y 
        where v := fold (\z. (\f. \x. e) (\y. (unfold z) z y)) 
                    (for y,z\not\in FV(e))
 *)

Infix "~>" := step (at level 50).

Inductive steps : expr -> expr -> Prop :=
| Steps0 e : steps e e
| StepsS e1 e2 e3 : e1 ~> e2 -> steps e2 e3 -> steps e1 e3
.
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
Notation "e ↓ τ" := (IsValue e /\ |- e τ) (at level 51).

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
| STecontext E e1 b e2 e1' e2' : 
    stepex e1 b e2 -> 
    plug E e1 e1' -> 
    plug E e2 e2' -> 
    stepex e1' b e2'
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

Definition onat_eq_b := option_eq_b EqNat.beq_nat.

Definition varR ctx m := {n | onat_eq_b (nth_error ctx n) (Some m) = true}.
Definition make_varR {ctx m} n (P : onat_eq_b (nth_error ctx n) (Some m) = true) : varR ctx m := exist _ n P.

Inductive rel ctx : nat -> Type :=
| Rvar m : varR ctx m -> rel ctx m
| Rinj : Prop -> rel ctx 0
| Rand (_ _ : rel ctx 0) : rel ctx 0
| Ror (_ _ : rel ctx 0) : rel ctx 0
| Rimply (_ _ : rel ctx 0) : rel ctx 0
| Rforall1 T : (T -> rel ctx 0) -> rel ctx 0
| Rexists1 T : (T -> rel ctx 0) -> rel ctx 0
| Rforall2 m : rel (m :: ctx) 0 -> rel ctx 0
| Rexists2 m : rel (m :: ctx) 0 -> rel ctx 0
| Rabs m : (expr -> rel ctx m) -> rel ctx (S m)
| Rapp m : rel ctx (S m) -> expr -> rel ctx m
| Rrecur m : rel (m :: ctx) m -> rel ctx m
| Rlater : rel ctx 0 -> rel ctx 0
.

Definition Rtrue {ctx} := Rinj ctx True.
Definition Rfalse {ctx} := Rinj ctx False.
Arguments Rinj {ctx} _ .

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
Global Instance Apply_rel_expr {var n} : Apply (rel var (S n)) expr (rel var n) :=
  {
    apply := Rapp
  }.
Infix "/\" := Rand : rel.
Infix "\/" := Ror : rel.
Infix "===>" := Rimply (at level 86) : rel.
Notation "▹" := Rlater : rel.

Delimit Scope rel with rel.
Bind Scope rel with rel.

Module test_rel.
  
  Variable ctx : list nat.

  Open Scope rel.

  Definition ttt1 : rel ctx 1 := \e , ⊤.
  Definition ttt2 : rel ctx 1 := \e , ⌈e ↓ Tunit⌉.
  Definition ttt3 : rel ctx 1 := \_ , ⌈True /\ True⌉.

End test_rel.

(* An Logical Step-indexed Logical Relation (LSLR) for boundedness *)

Local Open Scope prog_scope.

(* closing substitutions *)

Inductive SubstEntry : CtxEntry -> list nat -> Type :=
| SEtype {ctx} (_ : type) (_ : varR ctx 1) : SubstEntry CEtype ctx
| SEexpr {ctx} (_ : expr) : SubstEntry CEexpr ctx
.

Inductive csubsts : context -> list nat -> Type :=
| CSnil {ctx} : csubsts [] ctx
| CScons {ctx t lctx} : SubstEntry t ctx -> csubsts lctx ctx -> csubsts (t :: lctx) ctx
.

Notation "[ ]" := CSnil : CS.
Notation "[ x ; .. ; y ]" := (CScons x .. (CScons y CSnil) ..) : CS.
Infix "::" := CScons (at level 60, right associativity) : CS.
Delimit Scope CS with CS.
Bind Scope CS with csubsts.

Definition pair_of_se {ctx} (e : SubstEntry CEtype ctx) : type * varR ctx 1 :=
  match e with
    | SEtype _ t r => (t, r)
  end.

Definition type_of_se {ctx} := pair_of_se (ctx := ctx) >> fst.
Definition sem_of_se {ctx} := pair_of_se (ctx := ctx) >> snd.

Definition expr_of_se {ctx} (e : SubstEntry CEexpr ctx) : expr :=
  match e with
    | SEexpr _ s => s
  end.

Definition pair_of_cs {ctx t lctx} (rho : csubsts (t :: lctx) ctx) : SubstEntry t ctx * csubsts lctx ctx :=
  match rho with
    | CScons _ _ _ e rho' => (e, rho')
  end.

Arguments tl {A} _ .

Require Import Bedrock.Platform.Cito.ListFacts4.

Definition csubsts_sem : forall {lctx ctx}, csubsts lctx ctx -> open_var CEtype lctx -> varR ctx 1.
  refine
    (fix csubsts_sem {lctx} : forall ctx, csubsts lctx ctx -> open_var CEtype lctx -> varR ctx 1 :=
       match lctx return forall ctx, csubsts lctx ctx -> open_var CEtype lctx -> varR ctx 1 with
         | nil => _
         | t :: lctx' => 
           fun ctx rho =>
             match rho in (csubsts c ctx) return c = t :: lctx' -> open_var CEtype (t :: lctx') -> varR ctx 1 with
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

Global Instance Apply_csubsts_nat_rel {ctx} lctx : Apply (csubsts lctx ctx) (open_var CEtype lctx) (varR ctx 1) :=
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

Global Instance Add_pair_csubsts {ctx} lctx : Add (type * varR ctx 1) (csubsts lctx ctx) (csubsts (CEtype :: lctx) ctx) :=
  {
    add := add_pair
  }.

Definition add_expr {ctx lctx} e rho :=
  CScons (ctx := ctx) (lctx := lctx) (SEexpr e) rho.

Global Instance Add_expr_csubsts {ctx} lctx : Add expr (csubsts lctx ctx) (csubsts (CEexpr :: lctx) ctx) :=
  {
    add := add_expr
  }.

Definition VSet {var} τ (S : rel var 1) := (∀v, v ∈ S ===> ⌈v ↓ τ⌉)%rel.

Definition shift_csubsts {lctx ctx new} n (rho : csubsts lctx ctx) : csubsts lctx (insert ctx n new).
  admit.
Defined.

Instance Shift_csubsts lctx : Shift (csubsts lctx) :=
  {
    shift := @shift_csubsts lctx
  }.

Notation "#0" := ((make_varR (ctx := 1 :: _) (m := 1) 0 eq_refl)).

(* A "step-indexed" kriple model *)
(* the logical relation *)
Section LR.
  
  Variable B : nat.

  Open Scope rel.

  Fixpoint relE' {lctx} (relV : forall ctx, csubsts lctx ctx -> rel ctx 1) τ (c : nat) (s : size) ctx (ρ : csubsts lctx ctx) {struct c} : rel ctx 1 :=
    \e, ⌈|- e (ρ $ τ) /\ 
        (forall n e', (~>## e n 0 e') -> n ≤ B)⌉ /\ 
        (∀v, ⌈⇓*# e 0 v⌉ ===> v ∈ relV ctx ρ /\ ⌈!v ≤ s⌉) /\
        (∀e', ⌈~>*# e 1 e'⌉ ===> 
               match c with
                 | 0 => ⊥
                 | S c' =>
                   ▹ (e' ∈ relE' relV τ c' s ρ)
               end).

  Open Scope ty.

  Definition pair_to_Epair {ctx} (p : open_expr ctx * open_expr ctx) := Epair (fst p) (snd p).

  Global Instance Coerce_prod_expr ctx : Coerce (open_expr ctx * open_expr ctx) (open_expr ctx) :=
    {
      coerce := pair_to_Epair (ctx := ctx)
    }.

  Existing Instance Apply_rel_expr.

  Fixpoint relV {lctx} τ ctx (ρ : csubsts lctx ctx) : rel ctx 1 :=
    match τ with
      | Tvar α => Rvar (csubsts_sem ρ α)
      | Tunit => \v, ⌈v ↓ Tunit⌉
      | τ₁ × τ₂ => \v, ⌈v ↓ ρ $$ τ⌉ /\ ∃a b, ⌈v = !(a, b)⌉ /\ a ∈ relV τ₁ ρ /\ b ∈ relV τ₂ ρ
      | τ₁ + τ₂ => \v, ⌈v ↓ ρ $$ τ⌉ /\ ∃v', (⌈v = Einl (ρ $ τ₂) v'⌉ /\ v' ∈ relV τ₁ ρ) \/ (⌈v = Einr (ρ $ τ₁) v'⌉ /\ v' ∈ relV τ₂ ρ)
      | Tarrow τ₁ c s τ₂ => \v, ⌈v ↓ ρ $$ τ⌉ /\ ∃τ₁' e, ⌈v = Eabs τ₁' e⌉ /\ ∀v₁, v₁ ∈ relV τ₁ ρ ===> subst v₁ e ∈ relE' (relV τ₂) τ₂ !(ρ $ subst !(!v₁) c) (ρ $ subst !(!v₁) s) (add v₁ ρ)
      | Tuniversal c s τ₁ => \v, ⌈v ↓ ρ $$ τ⌉ /\ ∀τ', ∀₂, VSet τ' (Rvar #0) ===> v $$ τ' ∈ relE' (relV τ₁) τ₁ !(ρ $ c) (ρ $ s) (add (τ', #0) (shift1 _ ρ))
      | Trecur τ₁ => @@, \v, ⌈v ↓ ρ $$ τ⌉ /\ ∃τ' v', ⌈v = Efold τ' v'⌉ /\ ▹ (v' ∈ relV τ₁ (add (ρ $ τ, #0) (shift1 _ ρ)))
      | _ => \_, ⊥
    end
  .

  Definition relE {lctx} τ := relE' (lctx := lctx) (relV τ) τ.

End LR.

(* Fixpoint const_rel {ctx} P m : rel ctx m := *)
(*   match m with *)
(*     | 0 => Rinj P *)
(*     | S m' => Rabs (fun _ => const_rel P m') *)
(*   end. *)

Fixpoint erel m :=
  match m with
    | 0 => Prop
    | S m' => expr -> erel m'
  end.

Inductive monotone : forall {m}, (nat -> erel m) -> Prop :=
| MN0 (f : nat -> erel 0) : (forall n, f n -> forall n', n' < n -> f n') -> monotone f
| MNS m (f : nat -> erel (S m)) : (forall e, monotone (fun n => f n e)) -> monotone f
.

Definition mono_erel m := { f : nat -> erel m | monotone f}.

Fixpoint const_erel (P : Prop) (m : nat) : erel m :=
  match m with
    | 0 => P
    | S m' => fun _ => const_erel P m'
  end.

Definition rsubsts : list nat -> Prop.
  admit.
Defined.

Definition apply_rsubsts_var {ctx m} : rsubsts ctx -> varR ctx m -> mono_erel m.
  admit.
Defined.

Instance Apply_rsubsts_var {ctx m} : Apply (rsubsts ctx) (varR ctx m) (mono_erel m) :=
  {
    apply := apply_rsubsts_var
  }.

Definition add_rsubsts {ctx m} : mono_erel m -> rsubsts ctx -> rsubsts (m :: ctx).
  admit.
Defined.

Instance Add_rsubsts {ctx m} : Add (mono_erel m) (rsubsts ctx) (rsubsts (m :: ctx)) :=
  {
    add := add_rsubsts
  }.

Definition apply_rel_rel {m ctx m'} : rel (m :: ctx) m' -> rel ctx m -> rel ctx m'.
  admit.
Defined.

Instance Apply_rel_rel {m ctx m'} : Apply (rel (m :: ctx) m') (rel ctx m) (rel ctx m') :=
  {
    apply := apply_rel_rel
  }.

Definition lexical {A B} : (A -> A -> Prop) -> (B -> B -> Prop) -> (A * B) -> A * B -> Prop.
  admit.
Defined.

Inductive relsize :=
| RS1 : relsize
| RSadd (_ _ : relsize) : relsize
| RSbind {T} : (T -> relsize) -> relsize
.

Instance Add_relsize : Add relsize relsize relsize :=
  {
    add := RSadd
  }.

Definition RSadd1 := RSadd RS1.

Fixpoint rel2size {ctx m} (r : rel ctx m) : relsize :=
  match r with
    | Rvar _ _ => RS1
    | Rinj _ => RS1
    | Rand a b => rel2size a + rel2size b
    | Ror a b => rel2size a + rel2size b
    | Rimply a b => rel2size a + rel2size b
    | Rforall1 _ g => RSbind (fun x => rel2size (g x))
    | Rexists1 _ g => RSbind (fun x => rel2size (g x))
    | Rforall2 _ g => RSadd1 (rel2size g)
    | Rexists2 _ g => RSadd1 (rel2size g)
    | Rabs _ g => RSbind (fun e => rel2size (g e))
    | Rapp _ a _ => RSadd1 (rel2size a)
    | Rrecur _ g => RSadd1 (rel2size g)
    | Rlater _ => RS1
  end.

Inductive rlt : relsize -> relsize -> Prop :=
| RLTadd1 a b : rlt a (a + b)
| RLTadd2 a b : rlt b (a + b)
| RLTbind T g x : rlt (g x) (RSbind (T := T) g)
.

Lemma rlt_wf : well_founded rlt.
Proof.
  unfold well_founded.
  induction a.
  {
    econstructor.
    intros y H.
    inversion H.
  }
  {
    econstructor.
    intros y H.
    inversion H; subst; eauto.
  }
  {
    econstructor.
    intros y Hrlt.
    inversion Hrlt.
    Require Import Eqdep.
    eapply inj_pair2 in H3.
    rewrite H3.
    (* or : dependent induction Hrlt. *)
    eauto.
  }
Defined.

Lemma lexical_wf A B Ra Rb : well_founded Ra -> well_founded Rb -> well_founded (@lexical A B Ra Rb).
  admit.
Defined.

Obligation Tactic := try solve [intros; eassumption]; program_simpl.

Program Fixpoint interp {ctx m} (r : rel ctx m) (d : rsubsts ctx) n {measure (n, rel2size r) (lexical lt rlt)} : erel m :=
  match n with
    | 0 => const_erel True m
    | S n' =>
      match r with
        | Rvar _ x => ` (d $ x) n
        | Rinj P => P
        | Rand a b => interp a d n /\ interp b d n
        | Ror a b => interp a d n \/ interp b d n
        | Rimply a b => forall k, k <= n -> interp a d k -> interp b d k
        | Rforall1 _ g => forall x, interp (g x) d n
        | Rexists1 _ g => exists x, interp (g x) d n
        | Rforall2 _ g => forall x, interp g (add x d) n
        | Rexists2 _ g => exists x, interp g (add x d) n
        | Rabs _ g => fun e => interp (g e) d n
        | Rapp _ r e => interp r d n e
        | Rrecur m' g => interp (g $ transport (to := m') r (eq_sym _)) d n
        | Rlater P => interp P d n'
      end
  end.
Next Obligation.
  subst.
  admit.
Defined.
Next Obligation.
  subst.
  admit.
Defined.
Next Obligation.
  subst.
  admit.
Defined.
Next Obligation.
  subst.
  simpl.
  admit.
Defined.
Next Obligation.
  subst.
  simpl.
  admit.
Defined.
Next Obligation.
  rewrite <- Heq_r.
  admit.
Defined.
Next Obligation.
  subst.
  simpl.
  admit.
Defined.
Next Obligation.
  subst.
  admit.
Defined.
Next Obligation.
  subst.
  simpl.
  admit.
Defined.
Next Obligation.
  subst.
  admit.
Defined.
Next Obligation.
  subst.
  admit.
Defined.
Next Obligation.
  subst.
  admit.
Defined.
Next Obligation.
  replace (rel2size r) with (rel2size (Rrecur g)) by (rewrite <- Heq_r; eauto).
  simpl.
  admit.
Defined.
Next Obligation.
  subst.
  simpl.
  admit.
Defined.
Next Obligation.
  eapply measure_wf.
  eapply lexical_wf.
  { eapply Wf_nat.lt_wf. }
  eapply rlt_wf.
Defined.

(*here*)

Set Maximal Implicit Insertion.
Section Funvar.

  Variable var : list nat.

  Definition varT := list nat -> Type.
  Definition varTs := list varT.

  Fixpoint Funvar domains range :=
    match domains with
      | nil => range var
      | domain :: domains' => domain var -> Funvar domains' range
    end.

End Funvar.

Section openup.

  Context `{var : list nat}.
  
  Notation Funvar := (Funvar var).

  Definition openup1 {t1 t2} (f : t1 var -> t2 var) : forall {ctx}, Funvar ctx t1 -> Funvar ctx t2.
    refine
      (fix F ctx : Funvar ctx t1 -> Funvar ctx t2 :=
         match ctx return Funvar ctx t1 -> Funvar ctx t2 with
           | nil => _
           | nv :: ctx' => _
         end);
    simpl; eauto.
  Defined.

  Definition openup2 {t1 t2 T} (f : (T -> t1 var) -> t2 var) : forall {ctx}, (T -> Funvar ctx t1) -> Funvar ctx t2.
    refine
      (fix F ctx : (T -> Funvar ctx t1) -> Funvar ctx t2 :=
         match ctx return (T -> Funvar ctx t1) -> Funvar ctx t2 with
           | nil => _
           | nv :: ctx' => _ 
         end);
    simpl; eauto.
  Defined.

  Definition openup3 {t T} (f : T -> t var) : forall {ctx}, T -> Funvar ctx t.
    refine
      (fix F ctx : T -> Funvar ctx t :=
         match ctx return T -> Funvar ctx t with
           | nil => _
           | nv :: ctx' => _ 
         end);
    simpl; eauto.
  Defined.
  
  Definition openupSingle {t} (f : t var) : forall {ctx}, Funvar ctx t.
    refine
      (fix F ctx : Funvar ctx t :=
         match ctx return Funvar ctx t with
           | nil => _
           | t :: ctx' => _ 
         end);
    simpl; eauto.
  Defined.

  Definition openup5 {t1 t2 t3} (f : t1 var -> t2 var -> t3 var) : forall {ctx}, Funvar ctx t1 -> Funvar ctx t2 -> Funvar ctx t3.
    refine
      (fix F ctx : Funvar ctx t1 -> Funvar ctx t2 -> Funvar ctx t3 :=
         match ctx return Funvar ctx t1 -> Funvar ctx t2 -> Funvar ctx t3 with
           | nil => _
           | nv :: ctx' => _ 
         end);
    simpl; eauto.
  Defined.

  Definition openup8 {t1 t2 T} (f : (T -> t1 var) -> t2 var) : forall {ctx}, (Funvar ctx (const T) -> Funvar ctx t1) -> Funvar ctx t2.
    refine
      (fix F ctx : (Funvar ctx (const T) -> Funvar ctx t1) -> Funvar ctx t2 :=
         match ctx return (Funvar ctx (const T) -> Funvar ctx t1) -> Funvar ctx t2 with
           | nil => _
           | nv :: ctx' => _
         end);
    simpl; eauto.
  Defined.

End openup.

Section open_term.
  
  Inductive rtype :=
  | RTvar (_ : nat)
  | RTcsubsts (_ : context)
  | RTother (_ : Type)
  .

  (* Coercion RTvar : nat >-> rtype. *)

  Definition rcontext := list rtype.

  Variable var : list nat.

  Definition interp_rtype t : Type :=
    match t with
      | RTvar m => varR var m
      | RTcsubsts lctx => csubsts lctx var
      | RTother T => T
    end.

  Fixpoint open_term (domains : rcontext) (range : varT) : Type :=
    match domains with
      | nil => range var
      | domain :: domains' => interp_rtype domain -> open_term domains' range
    end.

End open_term.

Definition flip_rel := flip rel.
Coercion flip_rel : nat >-> Funclass.

Definition OpenTerm ctx t := forall var, open_term var ctx t.

(* Definition Rel ctx t := forall var, Funvar var ctx t. *)
(* Definition Rel1 m := forall var, rel var m. *)
(* Definition Rel2 m := forall var, rel2 var m. *)

Definition Rel1 m := OpenTerm [] (flip_rel m).
Definition Rel2 m := OpenTerm [] (flip rel2 m).

Definition Unrecur n {m} (R : Rel1 m) : Rel2 m := fun var => unrecur n (R (rel2 var)).

Definition Interp {m} (R : Rel1 m) n : erel m := 
  let R' := Unrecur n R in 
  interp n (R' mono_erel).

Lemma Interp_monotone m (R : Rel1 m) : monotone (Interp R).
  admit.
Qed.

Definition map_se {var} {F : (nat -> Type) -> nat -> Type} (f : var 1 -> F var 1) {t} : SubstEntry var t -> SubstEntry (F var) t :=
  match t with
    | CEtype => fun e => let (tau, x) := pair_of_se e in SEtype tau (f x)
    | CEexpr => fun e => SEexpr (expr_of_se e)
  end.

Fixpoint map_csubsts {var} {F : (nat -> Type) -> nat -> Type} (f : forall m, var m -> F var m) {lctx} : csubsts var lctx -> csubsts (F var) lctx :=
  match lctx return csubsts var lctx -> csubsts (F var) lctx with
    | nil => fun _ => []%CS
    | t :: lctx' => 
      fun rho => 
        let (e, rho') := pair_of_cs rho in 
        (map_se (f 1) e :: map_csubsts f rho')%CS
  end.

Definition map_rtype {var F} (f : forall m, var m -> F var m) {t} : interp_rtype var t -> interp_rtype (F var) t :=
  match t return interp_rtype var t -> interp_rtype (F var) t with
    | RTvar _ => fun x => f _ x
    | RTcsubsts _ => fun x => map_csubsts f x
    | RTother _ => fun x => x
  end.

Fixpoint unrecur_open n {m : nat} {var ctx} : open_term (rel2 var) ctx m -> open_term var ctx (flip rel2 m) :=
  match ctx return open_term (rel2 var) ctx (flip rel m) -> open_term var ctx (flip rel2 m) with
    | nil => fun r => unrecur n (m := m) r
    | t :: ctx' => fun r x => unrecur_open n (r (map_rtype (@R2var _) x))
  end.

Definition UnrecurOpen n {ctx} {m : nat} (R : OpenTerm ctx m) : OpenTerm ctx (flip rel2 m) := 
  fun var => unrecur_open n (R (rel2 var)).

Fixpoint interp_open n {m ctx} : open_term mono_erel ctx (flip rel2 m) -> open_term mono_erel ctx (const (erel m)) :=
  match ctx return open_term mono_erel ctx (flip rel2 m) -> open_term mono_erel ctx (const (erel m)) with
    | nil => interp n (m := m)
    | _ :: ctx' => fun r x => interp_open n (r x)
  end.

Definition InterpOpen {ctx} {m : nat} n (R : OpenTerm ctx m) : open_term mono_erel ctx (const (erel m)) :=
  let R' := UnrecurOpen n R in
  interp_open n (R' mono_erel).

Fixpoint forall_erel {T m} : (T -> erel m) -> erel m :=
  match m with
    | 0 => fun f => forall x, f x
    | S m' => fun f e => forall_erel (flip f e)
  end.

Fixpoint All ls :=
  match ls with
    | nil => True
    | P :: ls' => (P /\ All ls')%type
  end.

Fixpoint forall_ctx {ctx} : list (open_term mono_erel ctx (const Prop)) -> open_term mono_erel ctx (const Prop) -> Prop :=
  match ctx return list (open_term mono_erel ctx (const Prop)) -> open_term mono_erel ctx (const Prop) -> Prop with
    | nil => fun Ps P => All Ps -> P
    | t :: ctx' => fun Ps P => forall x, forall_ctx (map (flip apply_arrow x) Ps) (P x)
  end.

Definition DDrev ctx := DDv (rev ctx).

Definition relDDrev ctx m := rel (DDrev ctx) m.

Fixpoint DDlift new {m ctx} : (DDrev ctx m ->  relDDrev ctx m) -> (DDrev (new ++ ctx) m ->  relDDrev (new ++ ctx) m) :=
  match ctx with
    | nil => fun r x => 

Definition toDD {m} : forall ctx, relDDV ctx m -> relDD ctx m.
  refine
    (fix {ctx} (r : rel (DDv (rev ctx)) m) : relDD ctx m :=
       match r with
         | Rforall2 m' g => DDforall2 (toDD (m' :: ctx) (DDlift [m'] g (exist (length ctx) _)))
         | _ => DDinj _ True
       end).

Definition valid {ctx} : list (OpenTerm ctx 0) -> OpenTerm ctx 0 -> Prop :=
  fun Ps P => forall n, forall_ctx (map (InterpOpen n) Ps) (InterpOpen n P).

Infix "|~" := valid (at level 89, no associativity).

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

  Lemma VLob Ps P : ▹P :: Ps |~ P -> Ps |~ P.
    admit.
  Qed.
  
  (* Lemma VReplace2 Ps {n : nat} R1 R2 (P : OpenTerm (RTvar n :: ctx) 0) : Ps |~ R1 == R2 -> Ps |~ P $$ R1 -> Ps |~ P $$ R2. *)

End infer_rules.

Infix "==" := Iff.

Lemma VMorePs ctx (P : OpenTerm ctx 0) Ps : [] |~ P -> Ps |~ P.
  admit.
Qed.

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

Definition lift_Rel {ctx t2} new : Rel ctx t2 -> Rel (new :: ctx) t2 :=
  fun r var x => r var.

Definition t_Ps ctx := list (Rel ctx 0).
Definition Substs ctx lctx := Rel ctx (flip csubsts lctx).
Notation t_ρ := Substs (only parsing).
Notation lift_ρ := lift_Rel (only parsing).

Definition lift_Ps {ctx} t (Ps : t_Ps ctx) : t_Ps (t :: ctx):=
  map (lift_Rel t) Ps.

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

Definition add_ρ_type {ctx lctx} (ρ : t_ρ ctx lctx) : t_ρ (RTrel 1 :: RTtype :: ctx) (CEtype :: lctx) :=
  let ρ := lift_ρ RTtype ρ in
  let ρ := lift_ρ 1 ρ in
  let ρ := fun var => add (extend (t2 := pair_var) [RTrel 1; RTtype] ctx (fun S τ => (τ, S))) (ρ var) in
  ρ
.

Definition add_Ps_type {ctx} (Ps : t_Ps ctx) : t_Ps (RTrel 1 :: RTtype :: ctx) :=
  let Ps := lift_Ps RTtype Ps in
  let Ps := (fun var => extend [RTtype] ctx (fun τ => ⌈kinding TCnil τ 0⌉%rel : Funvar var [] 0)) :: Ps in
  let Ps := lift_Ps 1 Ps in
  let Ps := (fun var => extend [RTrel 1; RTtype] ctx (fun S τ => VSet τ S : Funvar var [] 0)) :: Ps in
  Ps
.

Global Instance Add_expr_csubsts' {var lctx} : Add (RTexpr var) (flip csubsts lctx var) (flip csubsts (CEexpr :: lctx) var) :=
  {
    add := add_expr
  }.

Definition add_ρ_expr {ctx lctx} (ρ : t_ρ ctx lctx) : t_ρ (RTexpr :: ctx) (CEexpr :: lctx) :=
  let ρ := lift_ρ RTexpr ρ in
  let ρ := fun var => add (extend [RTexpr] ctx (fun v => v)) (ρ var) in
  ρ
.

Global Instance Apply_rel_expr' {var n} : Apply (rel var (S n)) (RTexpr var) (rel var n) :=
  {
    apply := Rapp
  }.

Definition add_Ps_expr {ctx lctx} τ B (Ps : t_Ps ctx) (ρ : t_ρ ctx lctx) : t_Ps (RTexpr :: ctx) :=
  let Ps := lift_Ps RTexpr Ps in
  let Ps := (fun var v => openup1 (fun ρ => v ∈ relV B τ ρ) (ρ var)) :: Ps in
  Ps
.

Fixpoint make_ctx lctx :=
  match lctx with
    | nil => nil
    | e :: Γ' =>
      let ctx := make_ctx Γ' in
      match e with
        | CEtype =>
          RTrel 1 :: RTtype :: ctx
        | CEexpr =>
          RTexpr :: ctx
      end
  end.

Fixpoint make_ρ lctx : t_ρ (make_ctx lctx) lctx :=
  match lctx return t_ρ (make_ctx lctx) lctx with 
    | nil => (fun var => [])%CS
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

Section make_Ps.
  Variable B : nat.
  Fixpoint make_Ps {lctx} : tcontext lctx -> t_Ps (make_ctx lctx) :=
    match lctx return tcontext lctx -> t_Ps (make_ctx lctx) with 
      | nil => fun _ => nil
      | CEtype :: lctx' =>
        fun Γ =>
          let Ps := make_Ps (snd (pair_of_tc Γ)) in
          add_Ps_type Ps
      | CEexpr :: lctx' =>
        fun Γ =>
          let Ps := make_Ps (snd (pair_of_tc Γ)) in
          add_Ps_expr ((type_of_te << fst << pair_of_tc) Γ) B Ps (make_ρ lctx')
    end.
End make_Ps.

Definition c2n' {ctx} (c : Rel ctx (const cexpr)) : Rel ctx (const nat) :=
  fun var => openup1 (t1 := const cexpr) (t2 := const nat) c2n (c var).

Global Instance Coerce_cexpr_nat' : Coerce (Rel ctx (const cexpr)) (Rel ctx (const nat)) :=
  {
    coerce := c2n'
  }.

Fixpoint plug (c : econtext) (e : expr) : expr :=
  match c with
    | ECempty => e
    | ECapp1 f arg => Eapp (plug f e) arg
    | ECapp2 f arg _ => Eapp f (plug arg e)
    | EClet def main => Elet (plug def e) main
    | ECtapp f t => Etapp (plug f e) t
    | ECfold t c => Efold t (plug c e)
    | ECunfold c => Eunfold (plug c e)
    | EChide c => Ehide (plug c e)
    | ECunhide c => Eunhide (plug c e)
    | ECpair1 a b => Epair (plug a e) b
    | ECpair2 a b _ => Epair a (plug b e)
    | ECinl t c => Einl t (plug c e)
    | ECinr t c => Einr t (plug c e)
    | ECfst c => Efst (plug c e)
    | ECsnd c => Esnd (plug c e)
    | ECmatch target a b => Ematch (plug target e) a b
  end.

Instance Apply_EC_expr : Apply econtext expr expr :=
  {
    apply := plug
  }.

Instance Apply_Subst `{Subst t A B} {ctx} : Apply (B (t :: ctx)) (A ctx) (B ctx) :=
  {
    apply := flip subst
  }.

(*
Definition openE B {lctx} tau c s {var ctx} := openup1 (t1 := flip csubsts lctx) (t2 := 1) (@relE B lctx tau c s var) (ctx := ctx).
Definition goodExpr B {lctx} tau c s {ctx} (ρ : t_ρ ctx lctx) : Rel ctx 1 := fun var => openE B tau c s (ρ var).
Definition openV B {lctx} tau {var ctx} := openup1 (t1 := flip csubsts lctx) (t2 := 1) (@relV B lctx tau var) (ctx := ctx).
Definition goodValue B {lctx} tau {ctx} (ρ : t_ρ ctx lctx) : Rel ctx 1 := fun var => openV B tau (ρ var).
*)

Definition goodEC {lctx lctx'} : nat -> expr -> econtext -> open_type lctx -> open_cexpr [CEexpr] -> open_size [CEexpr] -> open_type lctx' -> Rel [flip csubsts lctx; flip csubsts lctx'] 0 :=
  fun B e E τ c s τ' var ρ ρ' => 
    (∀v, v ∈ relV B τ ρ /\ ⌈e ~>* v⌉ ===> E $$ v ∈ relE B τ' !(c $ v) (s $ v) ρ')%rel.

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

Definition related {lctx} B Γ (e : open_expr lctx) τ (c : open_cexpr lctx) (s : open_size lctx) :=
  make_Ps (lctx := lctx) B Γ |~ fun var => openup1 (fun ρ : csubsts var lctx => ρ $$ e ∈ relE B τ !(ρ $ c) (ρ $ s) ρ) (var := var) (t1 := flip csubsts lctx) (make_ρ lctx var).

Notation "⊩" := related.

Lemma foundamental :
  forall {ctx} (Γ : tcontext ctx) e τ c s,
    ⊢ Γ e τ c s -> 
    exists B, ⊩ B Γ e τ c s.
Proof.
  induction 1.
  {
    unfold related.
    exists 0.
    simpl.
    admit.
  }
  {
    destruct IHtyping1 as [B0 IH₀].
    destruct IHtyping2 as [B1 IH₁].
    exists (2 * B0 + B1 + 1).
    unfold related in *.
    eapply VMorePs.

    eapply VCtxElimEmpty.

    Open Scope rel.

    Lemma LRbind {lctx lctx'} B (τ : open_type lctx) s₁ E c₂ s₂ (τ' : open_type lctx') : 
      [] |~ fun var => (fun ρ ρ' => ∀ e c₁, e ∈ relE B τ c₁ s₁ ρ /\ goodEC B e E τ c₂ s₂ τ' ρ ρ' ===> E $$ e ∈ relE (2 * B) τ' (c₁ + !(c₂ $ s₁)) (s₂ $ s₁) ρ') : Funvar var [flip csubsts lctx; flip csubsts lctx'] 0.
    Proof.
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
