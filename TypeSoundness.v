(* Type soundness *)

Require Import List.
Require Import Program.
Require Import Util.
Require Import Typing EvalCBV.

Import ListNotations.
Local Open Scope list_scope.

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

Inductive steps : expr -> expr -> Prop :=
| Steps0 e : steps e e
| StepsS e1 e2 e3 : step e1 e2 -> steps e2 e3 -> steps e1 e3
.

Notation "⊢" := typing.
Definition typingsim e τ := exists c s, ⊢ TCnil e τ c s.
Notation "|-" := typingsim.

Definition nostuck e := forall e', steps e e' -> IsValue e' \/ exists e'', step e' e''.

Theorem sound_wrt_nostuck :
  forall e τ,
    |- e τ ->
    nostuck e.
Proof.
  admit.
Qed.

Inductive nsteps : expr -> nat -> expr -> Prop :=
| Nsteps0 e : nsteps e 0 e
| NstepsS e1 e2 n e3 : step e1 e2 -> nsteps e2 n e3 -> nsteps e1 (S n) e3
.

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

Instance Le_csize : Le csize csize :=
  {
    le := leCS
  }.
*)
Definition get_csize (e : expr) : csize.
  admit.
Defined.

Instance Coerce_expr_csize : Coerce expr csize :=
  {
    coerce := get_csize
  }.

Definition nat_of_cexpr (c : cexpr) : nat.
  admit.
Defined.

Definition c2n := nat_of_cexpr.

Instance Coerce_cexpr_nat : Coerce cexpr nat :=
  {
    coerce := c2n
  }.

Definition c2s {ctx} (ξ : csize) : open_size ctx.
  admit.
Defined.

Instance Coerce_csize_size ctx : Coerce csize (open_size ctx) :=
  {
    coerce := c2s (ctx := ctx)
  }.

Definition le_csize_size : csize -> size -> Prop.
  admit.
Defined.

Instance Le_cszie_size : Le csize size :=
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
          nsteps (f $ v) n e' -> n ≤ C * (1 + !(subst !(!v) c)).

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

(* A Parametric Higher-Order Abstract Syntax (PHOAS) encoding for a second-order modal logic (LSLR) *)

Set Maximal Implicit Insertion.
Set Implicit Arguments.
Section rel.

  Variable var : nat -> Type.
  
  Inductive rel : nat -> Type :=
  | Rvar n : var n -> rel n
  | Rinj : Prop -> rel 0
  | Rtrue : rel 0
  | Rfalse : rel 0
  | Rand (_ _ : rel 0) : rel 0
  | Ror (_ _ : rel 0) : rel 0
  | Rimply (_ _ : rel 0) : rel 0
  | Rforall2 n : (var n -> rel 0) -> rel 0
  | Rexists2 n : (var n -> rel 0) -> rel 0
  | Rforall1 T : (T -> rel 0) -> rel 0
  | Rexists1 T : (T -> rel 0) -> rel 0
  | Rabs n : (expr -> rel n) -> rel (S n)
  | Rapp n : rel (S n) -> expr -> rel n
  | Rrecur n : (var n -> rel n) -> rel n
  | Rlater : rel 0 -> rel 0
  .

End rel.
Unset Implicit Arguments.
Unset Maximal Implicit Insertion.

Arguments Rvar {var n} _ .
Arguments Rinj {var} _ .
Arguments Rtrue {var} .
Arguments Rfalse {var} .

Module ClosedPHOAS.

Notation "⊤" := Rtrue.
Notation "⊥" := Rtrue.
(* Notation "\ e , p" := (Rabs (fun e => p)) (at level 200, format "\ e , p"). *)
Notation "\ x .. y , p" := (Rabs (fun x => .. (Rabs (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity).
Notation "∀ x .. y , p" := (Rforall1 (fun x => .. (Rforall1 (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity).
Notation "∃ x .. y , p" := (Rexists1 (fun x => .. (Rexists1 (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity).
Definition Rforall2' {var n} P := (@Rforall2 var n (fun x => P (Rvar x))).
Notation "∀2 x .. y , p" := (Rforall2' (fun x => .. (Rforall2' (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity).
Definition Rexists2' {var n} P := (@Rexists2 var n (fun x => P (Rvar x))).
Notation "∃2 x .. y , p" := (Rexists2' (fun x => .. (Rexists2' (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity).
Definition Rrecur' {var n} P := (@Rrecur var n (fun x => P (Rvar x))).
Notation "@@ x .. y , p" := (Rrecur' (fun x => .. (Rrecur' (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity).
Notation "⌈ P ⌉" := (Rinj P).
Notation "e ∈ P" := (Rapp P e) (at level 70).
Infix "/\" := Rand.
Infix "\/" := Ror.
Infix "⇒" := Rimply (at level 90).
Notation "▹" := Rlater.

Section TestNotations.
  
  Variable var : nat -> Type.

  Definition ttt1 : rel var 1 := \e , ⊤.
  Definition ttt2 : rel var 1 := \e , ⌈e ↓ Tunit⌉.
  Definition ttt3 : rel var 1 := \_ , ⌈True /\ True⌉.

End TestNotations.

End ClosedPHOAS.

Set Implicit Arguments.
Set Maximal Implicit Insertion.

Section relOpen.

  Variable var : nat -> Type.
  
  Inductive termType :=
    | TTrel (arity : nat)
    | TTother (T : Type)
  .

  Coercion TTrel : nat >-> termType.

  Definition interp t :=
    match t with
      | TTrel n => rel var n
      | TTother T => T
    end.

  Definition Ctx := list termType.

  Fixpoint relOpen C range :=
    match C with
      | nil => interp range
      | domain :: C' => interp domain -> relOpen C' range
    end.

End relOpen.
Unset Maximal Implicit Insertion.

Definition Rel ctx t := forall var, relOpen var ctx t.

(* An Logical Step-indexed Logical Relation (LSLR) for boundedness *)

Local Open Scope prog_scope.

(*
Section substs.
  
  Variable ctx : Ctx.

End substs.

Arguments substs_sem {ctx} _ _ _ .
 *)

Notation TTexpr := (TTother expr).
Notation TTtype := (TTother type).
Notation TTcsize := (TTother csize).

(* closing substitutions *)
Section csubsts.
  
  Variable var : nat -> Type.
  Variable ctx : Ctx.

  Inductive SubstEntry : CtxEntry -> Type :=
  | SEtype (_ : relOpen var ctx (TTtype)) (_ : relOpen var ctx 1) : SubstEntry CEtype
  | SEexpr (_ : relOpen var ctx (TTexpr)) : SubstEntry CEexpr
  .

  Inductive csubsts : context -> Type :=
  | CSnil : csubsts []
  | CScons {t lctx} : SubstEntry t -> csubsts lctx -> csubsts (t :: lctx)
  .

End csubsts.

Generalizable All Variables.

Section csubstsClosed.
  
  Variable var : nat -> Type.

  Definition pair_of_se {ctx} (e : SubstEntry var ctx CEtype) : (relOpen var ctx TTtype * relOpen var ctx 1) :=
    match e with
      | SEtype t r => (t, r)
    end.

  Definition type_of_se {ctx} := pair_of_se (ctx := ctx) >> fst.
  Definition sem_of_se {ctx} := pair_of_se (ctx := ctx) >> snd.

  Definition expr_of_se {ctx} (e : SubstEntry var ctx CEexpr) : (relOpen var ctx TTexpr) :=
    match e with
      | SEexpr s => s
    end.

  Arguments tl {A} _ .

  Require Import Bedrock.Platform.Cito.ListFacts4.

  Definition csubsts_sem : forall {lctx}, csubsts var [] lctx -> open_var CEtype lctx -> rel var 1.
    refine
      (fix csubsts_sem {lctx} : csubsts var [] lctx -> open_var CEtype lctx -> rel var 1 :=
         match lctx return csubsts var [] lctx -> open_var CEtype lctx -> rel var 1 with
           | nil => _
           | t :: lctx' => 
             fun rho =>
               match rho in (csubsts _ _ c) return c = t :: lctx' -> open_var CEtype (t :: lctx') -> rel var 1 with
                 | CSnil => _
                 | CScons t' _ v rho' => _
                   (* fun Heq x => *)
                   (*   match x with *)
                   (*     | Var n Hn => (fun (H : x = Var n Hn) => _) (eq_refl (Var n Hn)) *)
                   (*   end *)
               end eq_refl
         end).
    {
      intros ? x.
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
        - eapply (transport rho' _).
        - eapply (#n').
      }
    }
    Grab Existential Variables.
    { eapply ceb_iff; eauto. }
    { eapply f_equal with (f := tl) in Heq; exact Heq. }
  Defined.

  Global Instance Apply_csubsts_nat_rel lctx : Apply (csubsts var [] lctx) (open_var CEtype lctx) (rel var 1) :=
    {
      apply := csubsts_sem
    }.

  Definition csubst_type `{Subst CEtype open_type B} {lctx} (v : SubstEntry var [] CEtype) (b : B (CEtype :: lctx)) : B lctx.
    refine
      (subst (cast (shiftby lctx (type_of_se v)) _) b).
    simpl.
    eapply app_nil_r.
  Defined.
  
  Definition csubst_expr `{Subst CEexpr open_expr B} {lctx} (v : SubstEntry var [] CEexpr) (b : B (CEexpr :: lctx)) : B lctx.
    refine
      (subst (cast (shiftby lctx (expr_of_se v)) _) b).
    simpl.
    eapply app_nil_r.
  Defined.
  
  Definition subst_close `{Subst CEtype open_type B, Subst CEexpr open_expr B} : forall lctx, csubsts var [] lctx -> B lctx -> B [].
    refine
      (fix subst_close lctx : csubsts var [] lctx -> B lctx -> B [] :=
         match lctx return csubsts var [] lctx -> B lctx -> B [] with
           | nil => fun _ b => b
           | t :: lctx' =>
             fun rho =>
               match rho in (csubsts _ _ c) return c = t :: lctx' -> B (t :: lctx') -> B [] with
                 | CSnil => _
                 | CScons t' _ v rho' => _
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
      - eapply (transport rho' _).
      - eapply (csubst_type v b).
    }
    {
      intros Heq b.
      eapply subst_close with (lctx := lctx').
      - eapply (transport rho' _).
      - eapply (csubst_expr v b).
    }
    Grab Existential Variables.
    { eapply f_equal with (f := tl) in Heq; exact Heq. }
    { eapply f_equal with (f := tl) in Heq; exact Heq. }
  Defined.

  Definition csubsts_cexpr :=
   subst_close (B := open_cexpr).

  Global Instance Apply_csubsts_cexpr_cexpr lctx : Apply (csubsts var [] lctx) (open_cexpr lctx) cexpr :=
    {
      apply := @csubsts_cexpr _
    }.

  Definition csubsts_size :=
    subst_close (B := open_size).

  Global Instance Apply_csubsts_size_size lctx : Apply (csubsts var [] lctx) (open_size lctx) size :=
    {
      apply := @csubsts_size _
    }.

  Definition csubsts_type :=
    subst_close (B := open_type).

  Global Instance Apply_csubsts_type_type lctx : Apply (csubsts var [] lctx) (open_type lctx) type :=
    {
      apply := @csubsts_type _
    }.

  Definition csubsts_expr :=
    subst_close (B := open_expr).

  Global Instance Apply_csubsts_expr_expr lctx : Apply (csubsts var [] lctx) (open_expr lctx) expr :=
    {
      apply := @csubsts_expr _
    }.

  Arguments SEtype {var ctx} _ _ .
  Arguments SEexpr {var ctx} _ .

  Definition add_pair {lctx} p rho :=
    CScons (lctx := lctx) (SEtype (var := var) (ctx := []) (fst p) (snd p)) rho.

  Global Instance Add_pair_csubsts lctx : Add (type * rel var 1) (csubsts var [] lctx) (csubsts var [] (CEtype :: lctx)) :=
    {
      add := add_pair
    }.

  Definition add_expr {lctx} e rho :=
    CScons (lctx := lctx) (SEexpr (var := var) (ctx := []) e) rho.
  
  Global Instance Add_expr_csubsts lctx : Add expr (csubsts var [] lctx) (csubsts var [] (CEexpr :: lctx)) :=
    {
      add := add_expr
    }.

End csubstsClosed.

Arguments csubsts_sem {_ lctx} _ _ .

Import ClosedPHOAS.

Definition VSet {var} τ (S : rel var 1) := ∀v, v ∈ S ⇒ ⌈v ↓ τ⌉.

Definition terminatesWith e v := (steps e v /\ IsValue v)%type.
Infix "⇓" := terminatesWith (at level 51).

Definition stepsex e m e' := exists n, nstepsex e n m e'.

(* A "step-indexed" kriple model *)
(* the logical relation *)
Section LR.
  
  Variable Ct : nat.

  (* don't know why this coercion stopped working *)
  Coercion csubsts_type : csubsts >-> Funclass.
  (*
  Context {var lctx} `{ρ : csubsts var [] lctx}.
  Context {τ : open_type lctx}.
  Check (@csubsts_type _ lctx ρ).
  Set Printing All.
  Check (ρ τ).
  Check (@csubsts_type var (@nil termType) lctx ρ).
   *)
  
  Fixpoint E' {lctx} (V : forall var, csubsts var [] lctx -> rel var 1) τ (c : nat) (s : size) var (ρ : csubsts var [] lctx) {struct c} : rel var 1 :=
    \e, ⌈|- e (ρ $ τ) /\ 
        (forall n e', nstepsex e n 0 e' -> n ≤ 1 + Ct)%nat⌉ /\ 
        (∀v, ⌈e ⇓ v⌉ ⇒ v ∈ V var ρ /\ ⌈!v ≤ s⌉) /\
        (∀e', match c with
                | 0 => ⊤
                | S c' =>
                  ⌈stepsex e 1 e'⌉ ⇒ ▹ (e' ∈ E' V τ c' s ρ)
              end).

  Open Scope ty.

  Definition pair_to_Epair {ctx} (p : open_expr ctx * open_expr ctx) := Epair (fst p) (snd p).

  Instance Coerce_prod_expr ctx : Coerce (open_expr ctx * open_expr ctx) (open_expr ctx) :=
    {
      coerce := pair_to_Epair (ctx := ctx)
    }.

  Fixpoint V {lctx} τ var (ρ : csubsts var [] lctx) : rel var 1 :=
    match τ with
      | Tvar α => csubsts_sem ρ α
      | Tunit => \v, ⌈v ↓ Tunit⌉
      | τ₁ × τ₂ => \v, ⌈v ↓ ρ $$ τ⌉ /\ ∃a b, ⌈v = !(a, b)⌉ /\ a ∈ V τ₁ ρ /\ b ∈ V τ₂ ρ
      | τ₁ + τ₂ => \v, ⌈v ↓ ρ $$ τ⌉ /\ ∃v', (⌈v = Einl (ρ $ τ₂) v'⌉ /\ v' ∈ V τ₁ ρ) \/ (⌈v = Einr (ρ $ τ₁) v'⌉ /\ v' ∈ V τ₂ ρ)
      | Tarrow τ₁ c s τ₂ => \v, ⌈v ↓ ρ $$ τ⌉ /\ ∀v₁, v₁ ∈ V τ₁ ρ ⇒ v $$ v₁ ∈ E' (V τ₂) τ₂ !(ρ $ subst !(!v₁) c) (ρ $ subst !(!v₁) s) (add v₁ ρ)
      | Tuniversal c s τ₁ => \v, ⌈v ↓ ρ $$ τ⌉ /\ ∀τ', ∀2 S, VSet τ' S ⇒ v $$ τ' ∈ E' (V τ₁) τ₁ !(ρ $ c) (ρ $ s) (add (τ', S) ρ)
      | Trecur τ₁ => @@S, \v, ⌈v ↓ ρ $$ τ⌉ /\ ∃v', ⌈v = Efold (ρ $ τ) v'⌉ /\ ▹ (v' ∈ V τ₁ (add (ρ $ τ, S) ρ))
      | _ => \_, ⊥
    end
  .

  Definition E {lctx} τ := E' (lctx := lctx) (V τ) τ.

End LR.

Definition lift_se var ctx t : forall new, SubstEntry var ctx t -> SubstEntry var (new :: ctx) t.
  destruct t.
  {
    intros new e.
    destruct (pair_of_se e) as [tau r].
    econstructor.
    {
      simpl in *.
      intros x.
      exact tau.
    }
    {
      simpl in *.
      intros x.
      exact r.
    }
  }
  {
    intros new e.
    eapply expr_of_se in e.
    econstructor.
    simpl in *.
    intros x.
    exact e.
  }
Defined.  

Definition se_close1 {vart} : forall {var t ctx}, SubstEntry var (t :: ctx) vart -> interp var t -> SubstEntry var ctx vart.
  destruct vart.
  {
    intros var t ctx.
    intros e x.
    destruct (pair_of_se e) as [tau r].
    simpl in *.
    econstructor.
    - exact (tau x).
    - exact (r x).
  }
  {
    intros var t ctx.
    intros e x.
    eapply expr_of_se in e.
    simpl in *.
    econstructor.
    exact (e x).
  }
Defined.

Require Import Bedrock.Platform.Cito.GeneralTactics4.

Definition pair_of_cs {var ctx t lctx} (rho : csubsts var ctx (t :: lctx)) : SubstEntry var ctx t * csubsts var ctx lctx :=
  match rho with
    | CScons _ _ e rho' => (e, rho')
  end.

Definition Substs ctx lctx := forall var, csubsts var ctx lctx.

Definition lift_Substs' : forall {var ctx lctx} new, csubsts var ctx lctx -> csubsts var (new :: ctx) lctx.
  refine
    (fix F {var ctx lctx} {struct lctx} : forall new, csubsts var ctx lctx -> csubsts var (new :: ctx) lctx :=
       match lctx return forall new, csubsts var ctx lctx -> csubsts var (new :: ctx) lctx with
         | nil => fun _ _ => CSnil _ _
         | t :: lctx' => fun new rho => _
       end).
  destruct (pair_of_cs rho) as [e rho'].
  econstructor.
  { exact (lift_se _ e). }
  eapply F.
  - exact rho'.
Defined.

Definition lift_Substs {ctx lctx} new : Substs ctx lctx -> Substs (new :: ctx) lctx :=
  fun rho var => lift_Substs' new (rho var).

Class Lift A B :=
  {
    lift : forall (t : termType), A -> B t
  }.

Global Instance Lift_Substs ctx lctx : Lift (Substs ctx lctx) (fun new => Substs (new :: ctx) lctx) :=
  {
    lift := lift_Substs
  }.

Definition csubsts_close1 : forall {lctx var t ctx}, csubsts var (t :: ctx) lctx -> interp var t -> csubsts var ctx lctx.
  refine
    (fix F {lctx} : forall {var t ctx}, csubsts var (t :: ctx) lctx -> interp var t -> csubsts var ctx lctx :=
       match lctx return forall {var t ctx}, csubsts var (t :: ctx) lctx -> interp var t -> csubsts var ctx lctx with
         | nil => fun _ _ _ _ _ => CSnil _ _
         | t :: lctx' => fun var t ctx rho => _
       end).
  destruct (pair_of_cs rho) as [e rho'].
  intros x.
  econstructor.
  {
    eapply se_close1.
    - exact e.
    - exact x.
  }
  eapply F.
  - exact rho'.
  - exact x.
Defined.

Instance Apply_csubsts_interp lctx var t ctx : Apply (csubsts var (t :: ctx) lctx) (interp var t) (csubsts var ctx lctx) :=
  {
    apply := @csubsts_close1 lctx var t ctx
  }.

Definition openup_csubsts {lctx var range} (f : csubsts var [] lctx -> interp var range) : forall ctx, csubsts var ctx lctx -> relOpen var ctx range.
  refine
    (fix F ctx : csubsts var ctx lctx -> relOpen var ctx range :=
       match ctx return csubsts var ctx lctx -> relOpen var ctx range with
         | nil => _
         | nv :: ctx' => _
       end).
  {
    intros a.
    exact (f a).
  }
  {
    simpl in *.
    intros a b.
    exact ((F ctx') (a $ b)).
  }
Defined.

Arguments SEtype {var ctx} _ _ .
Arguments SEexpr {var ctx} _ .

Global Instance Lift_list `{Lift A B} : Lift (list A) (fun t => list (B t)) :=
  {
    lift t a := map (lift t) a
  }.

Definition lift_Rel {ctx range} new : Rel ctx range -> Rel (new :: ctx) range :=
  fun r var x => r var.

Global Instance Lift_Rel ctx range : Lift (Rel ctx range) (fun new => Rel (new :: ctx) range) :=
  {
    lift := lift_Rel
  }.

Definition t_Ps_ρ ctx lctx := (list (Rel ctx 0) * Substs ctx lctx)%type.
Definition t_Ps ctx := list (Rel ctx 0).
Notation t_ρ := Substs.
Notation lift_ρ := lift_Substs.

(*
Definition lift_Ps_ρ {ctx} t (Ps_ρ : t_Ps_ρ ctx) : t_Ps_ρ (t :: ctx):=
  let (Ps, ρ) := Ps_ρ in
  let Ps := map (lift_Rel t) Ps in
  let ρ := lift t ρ in
  (Ps, ρ).

Global Instance Lift_Ps_ρ ctx : Lift (t_Ps_ρ ctx) (fun new => t_Ps_ρ (new :: ctx))%type :=
  {
    lift := lift_Ps_ρ
  }.
 *)

Definition lift_Ps {ctx} t (Ps : t_Ps ctx) : t_Ps (t :: ctx):=
  map (lift_Rel t) Ps.

Global Instance Lift_Ps ctx : Lift (t_Ps ctx) (fun new => t_Ps (new :: ctx))%type :=
  {
    lift := lift_Ps
  }.

Definition openupSingle {var range} : forall {ctx}, interp var range -> relOpen var ctx range.
  refine
    (fix F {ctx} : interp var range -> relOpen var ctx range :=
       match ctx return interp var range -> relOpen var ctx range with
         | nil => _
         | t :: ctx' => _ 
       end).
  {
    simpl.
    exact id.
  }
  {
    simpl.
    intros a x.
    eapply F.
    exact a.
  }
Defined.

(* should compute *)
Definition extend {var range} ctx new : relOpen var ctx range -> relOpen var (ctx ++ new) range.
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

Arguments CScons {var ctx t lctx} _ _ .
Infix ":::" := CScons (at level 60, right associativity).

Definition add_ρ_type {ctx lctx} (ρ : t_ρ ctx lctx) : t_ρ (TTrel 1 :: TTtype :: ctx) (CEtype :: lctx) :=
  let ρ := lift_ρ TTtype ρ in
  let ρ := lift_ρ 1 ρ in
  let ρ := fun var => SEtype (extend [TTrel 1; TTtype] ctx (fun _ τ => τ)) (extend [TTrel 1; TTtype] ctx (fun S _ => S)) ::: ρ var in
  ρ
.

Definition add_Ps_type {ctx} (Ps : t_Ps ctx) : t_Ps (TTrel 1 :: TTtype :: ctx) :=
  let Ps := lift_Ps TTtype Ps in
  let Ps := (fun var => extend [TTtype] ctx (fun τ => ⌈kinding TCnil τ 0⌉ : relOpen var [] 0)) :: Ps in
  let Ps := lift_Ps 1 Ps in
  let Ps := (fun var => extend [TTrel 1; TTtype] ctx (fun S τ => VSet τ S : relOpen var [] 0)) :: Ps in
  Ps
.

Definition add_ρ_expr {ctx lctx} (ρ : t_ρ ctx lctx) : t_ρ (TTexpr :: ctx) (CEexpr :: lctx) :=
  let ρ := lift_ρ TTexpr ρ in
  let ρ := fun var => SEexpr (extend [TTexpr] ctx (fun v => v : relOpen var [] TTexpr)) ::: ρ var in
  ρ
.

Definition add_Ps_expr {ctx lctx} τ Ct (Ps : t_Ps ctx) (ρ : t_ρ ctx lctx) : t_Ps (TTexpr :: ctx) :=
  let Ps := lift_Ps TTexpr Ps in
  let Ps := (fun var v => openup_csubsts (fun ρ => v ∈ V Ct τ ρ : interp _ 0) (ρ var)) :: Ps in
  Ps
.

Fixpoint make_ctx lctx :=
  match lctx with
    | nil => nil
    | e :: Γ' =>
      let ctx := make_ctx Γ' in
      match e with
        | CEtype =>
          TTrel 1 :: TTtype :: ctx
        | CEexpr =>
          TTexpr :: ctx
      end
  end.

Fixpoint make_ρ lctx : t_ρ (make_ctx lctx) lctx :=
  match lctx return t_ρ (make_ctx lctx) lctx with 
    | nil => (fun var => CSnil _ _)
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
  Variable Ct : nat.
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
          add_Ps_expr ((type_of_te << fst << pair_of_tc) Γ) Ct Ps (make_ρ lctx')
    end.
End make_Ps.

Section OR.

  Variable var : nat -> Type.
  Notation relOpen := (relOpen var).

  Definition openup1 {domain range} (f : interp var domain -> interp var range) : forall C, relOpen C domain -> relOpen C range.
    refine
      (fix F C : relOpen C domain -> relOpen C range :=
         match C return relOpen C domain -> relOpen C range with
           | nil => _
           | nv :: C' => _
         end).
    {
      intros a.
      exact (f a).
    }
    {
      simpl in *.
      intros a b.
      eauto.
    }
  Defined.

  Program Fixpoint openup2 C {n1 n2 T} (f : (T -> rel var n1) -> rel var n2) (a : T -> relOpen C n1) : relOpen C n2 :=
    match C with
      | nil => _
      | nv :: C' => _ (@openup2 C' n1 n2)
    end.
  Next Obligation.
    exact (f a).
  Defined.
  Next Obligation.
    exact (x _ f (flip a X)).
  Defined.

  Program Fixpoint openup3 C {n T} (f : T -> rel var n) (a : T) : relOpen C n :=
    match C with
      | nil => _
      | nv :: C' => _ (@openup3 C' n)
    end.

  Program Fixpoint openup4 C {n} (f : rel var n) : relOpen C n :=
    match C with
      | nil => _
      | nv :: C' => _ (@openup4 C' n)
    end.

  Definition openup5 {t1 t2 t3} (f : interp var t1 -> interp var t2 -> interp var t3) : forall C, relOpen C t1 -> relOpen C t2 -> relOpen C t3.
    refine
      (fix F C : relOpen C t1 -> relOpen C t2 -> relOpen C t3 :=
         match C return relOpen C t1 -> relOpen C t2 -> relOpen C t3 with
           | nil => _
           | nv :: C' => _ 
         end).
    {
      intros a b.
      exact (f a b).
    }
    {
      simpl in *.
      intros.
      eauto.
    }
  Defined.

  Definition openup6 {n1 T n2} (f : rel var n1 -> T -> rel var n2) : forall C, relOpen C n1 -> relOpen C (TTother T) -> relOpen C n2.
    refine
      (fix F C : relOpen C n1 -> relOpen C (TTother T) -> relOpen C n2 :=
         match C return relOpen C n1 -> relOpen C (TTother T) -> relOpen C n2 with
           | nil => _
           | nv :: C' => _ 
         end).
    {
      intros a b.
      exact (f a b).
    }
    {
      simpl in *.
      intros a b.
      eauto.
    }
  Defined.

  Definition openup8 {n1 n2 T} (f : (T -> rel var n1) -> rel var n2) : forall C, (relOpen C (TTother T) -> relOpen C n1) -> relOpen C n2.
    refine
      (fix F C : (relOpen C (TTother T) -> relOpen C n1) -> relOpen C n2 :=
         match C return (relOpen C (TTother T) -> relOpen C n1) -> relOpen C n2 with
           | nil => _
           | nv :: C' => _
         end).
    {
      intros a.
      exact (f a).
    }
    {
      simpl in *.
      intros a b.
      eauto.
    }      
  Defined.

  Variable ctx : Ctx.

  Definition ORvar n := openup3 ctx (@Rvar var n).
  Definition ORinj := openup3 ctx (@Rinj var).
  Definition ORtrue := openup4 ctx (@Rtrue var).
  Definition ORfalse := openup4 ctx (@Rfalse var).
  Definition ORand := openup5 (@Rand var) (t1 := 0) (t2 := 0) (t3 := 0) ctx.
  Definition ORor := openup5 (@Ror var) (t1 := 0) (t2 := 0) (t3 := 0) ctx.
  Definition ORimply := openup5 (@Rimply var) (t1 := 0) (t2 := 0) (t3 := 0) ctx.
  Definition ORforall2 n := openup2 ctx (@Rforall2 var n).
  Definition ORexists2 n := openup2 ctx (@Rexists2 var n).
  Definition ORforall1 T := openup2 ctx (@Rforall1 var T).
  Definition ORexists1 T := openup2 ctx (@Rexists1 var T).
  Definition ORabs n := openup2 ctx (@Rabs var n).
  Definition ORapp n := openup6 (@Rapp var n) ctx.
  Definition ORrecur n := openup2 ctx (@Rrecur var n).
  Definition ORlater := openup1 (domain := 0) (range := 0) (@Rlater var) ctx.

End OR.

Arguments ORtrue {var ctx} .
Arguments ORfalse {var ctx} .
Arguments ORinj {var ctx} _ .
Arguments ORabs {var ctx n} _ .
Arguments ORforall1 {var ctx T} _ .
Arguments ORexists1 {var ctx T} _ .
Arguments ORapp {var ctx n} _ _ .
Arguments ORand {var ctx} _ _ .
Arguments ORor {var ctx} _ _ .
Arguments ORimply {var ctx} _ _ .
Arguments ORlater {var ctx} _ .
Arguments ORforall2 {var ctx n} _ .
Arguments ORexists2 {var ctx n} _ .
Arguments ORrecur {var ctx n} _ .

Module OpenPHOAS.
  
Notation "⊤" := ORtrue : OR.
Notation "⊥" := ORtrue : OR.
Notation "⌈ P ⌉" := (ORinj P) : OR.
Notation "\ x .. y , p" := (ORabs (fun x => .. (ORabs (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity) : OR.
Notation "∀ x .. y , p" := (ORforall1 (fun x => .. (ORforall1 (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity) : OR.
Notation "∃ x .. y , p" := (ORexists1 (fun x => .. (ORexists1 (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity) : OR.
Definition ORforall2' {var ctx n} P := (@ORforall2 var ctx n (fun x => P (ORvar var ctx _ x))).
Notation "∀2 x .. y , p" := (ORforall2' (fun x => .. (ORforall2' (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity) : OR.
Definition ORexists2' {var ctx n} P := (@ORexists2 var ctx n (fun x => P (ORvar var ctx _ x))).
Notation "∃2 x .. y , p" := (ORexists2' (fun x => .. (ORexists2' (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity) : OR.
Notation "@@ x .. y , p" := (ORrecur (fun x => .. (ORrecur (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity) : OR.
Definition ORrecur' {var ctx n} P := (@ORrecur var ctx n (fun x => P (ORvar var ctx _ x))).
Notation "@@@ x .. y , p" := (ORrecur' (fun x => .. (ORrecur' (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity) : OR.
Notation "e ∈ P" := (ORapp P e) (at level 70) : OR.
Infix "/\" := ORand : OR.
Infix "\/" := ORor : OR.
Infix "⇒" := ORimply (at level 90) : OR.
Notation "▹" := ORlater : OR.

Delimit Scope OR with OR.

Section TestNotations.
  
  Variable var : nat -> Type.
  Variable ctx : Ctx.

  Open Scope OR.
  
  Definition ttt1 : relOpen var ctx 1 := \e , ⊤.
  Definition ttt2 : relOpen var ctx 1 := \e , ⌈e ↓ Tunit⌉.
  Definition ttt3 : relOpen var ctx 0 := ⌈True /\ True⌉.
  Definition ttt4 : relOpen var ctx 0 := ∀e, ⌈e = @Ett nil⌉.
  Definition ttt5 : relOpen var ctx 0 := ∃e, ⌈e = @Ett nil⌉.

End TestNotations.

End OpenPHOAS.

Set Maximal Implicit Insertion.
Section REL.

  Variable ctx : Ctx.
  Notation Rel := (Rel ctx).
  
  Definition RELinj P : Rel 0 := fun var => ORinj P.
  Definition RELtrue : Rel 0 := fun var => ORtrue.
  Definition RELfalse : Rel 0 := fun var => ORfalse.
  Definition RELand (a b : Rel 0) : Rel 0 := fun var => ORand (a var) (b var).
  Definition RELor (a b : Rel 0) : Rel 0 := fun var => ORor (a var) (b var).
  Definition RELimply (a b : Rel 0) : Rel 0 := fun var => ORimply (a var) (b var).
  Definition RELforall1 T (F : T -> Rel 0) : Rel 0 := fun var => ORforall1 (fun x => F x var).
  Definition RELexists1 T (F : T -> Rel 0) : Rel 0 := fun var => ORexists1 (fun x => F x var).
  Definition RELabs (n : nat) (F : expr -> Rel n) : Rel (S n) := fun var => ORabs (fun e => F e var).
  Definition RELapp n (r : Rel (S n)) (e : Rel TTexpr) : Rel n := fun var => ORapp (r var) (e var).
  Definition RELlater (P : Rel 0) : Rel 0 := fun var => ORlater (P var).
  
End REL.
Unset Maximal Implicit Insertion.

Arguments RELinj {ctx} _ _ .
Arguments RELtrue {ctx} _ .
Arguments RELfalse {ctx} _ .

Module StandalonePHOAS.
  
Notation "⊤" := RELtrue : REL.
Notation "⊥" := RELtrue : REL.
Notation "⌈ P ⌉" := (RELinj P) : REL.
Notation "\ x .. y , p" := (RELabs (fun x => .. (RELabs (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity) : REL.
Notation "∀ x .. y , p" := (RELforall1 (fun x => .. (RELforall1 (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity) : REL.
Notation "∃ x .. y , p" := (RELexists1 (fun x => .. (RELexists1 (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity) : REL.
Notation "e ∈ P" := (RELapp P e) (at level 70) : REL.
Infix "/\" := RELand : REL.
Infix "\/" := RELor : REL.
Infix "⇒" := RELimply (at level 90) : REL.
Notation "▹" := RELlater : REL.

Delimit Scope REL with REL.

Section TestNotations.
  
  Variable ctx : Ctx.

  Open Scope REL.

  Definition ttt1 : Rel ctx 1 := \e , ⊤.
  Definition ttt2 : Rel ctx 1 := \e , ⌈e ↓ Tunit⌉.
  Definition ttt3 : Rel ctx 0 := ⌈True /\ True⌉.
  Definition ttt4 : Rel ctx 0 := ∀e, ⌈e = @Ett nil⌉.
  Definition ttt5 : Rel ctx 0 := ∃e, ⌈e = @Ett nil⌉.

End TestNotations.

End StandalonePHOAS.

Definition openup7 {var domain range} : forall {ctx}, (interp var domain -> relOpen var ctx range) -> relOpen var ctx domain -> relOpen var ctx range.
  refine
    (fix F {ctx} : (interp var domain -> relOpen var ctx range) -> relOpen var ctx domain -> relOpen var ctx range :=
       match ctx return (interp var domain -> relOpen var ctx range) -> relOpen var ctx domain -> relOpen var ctx range with
         | nil => _
         | t :: ctx' => _ 
       end).
  {
    exact id.
  }
  {
    simpl.
    eauto.
  }
Defined.

Definition apply_Rel_Rel {n ctx range} : Rel (n :: ctx) range -> Rel ctx n -> Rel ctx range :=
  fun f x var => openup7 (f var) (x var).

Instance Apply_Rel_Rel n ctx range : Apply (Rel (n :: ctx) range) (Rel ctx n) (Rel ctx range) :=
  {
    apply := apply_Rel_Rel
  }.

Section inferRules.

  Reserved Notation "C |~ P" (at level 90).

  Import OpenPHOAS.
  Import StandalonePHOAS.
  Open Scope REL.

  Variable ctx : Ctx.

  Instance Apply_Rel_TTexpr ctx n : Apply (Rel ctx (S n)) (Rel ctx TTexpr) (Rel ctx n) :=
    {
      apply := RELapp
    }.

  Definition RELapp' {ctx n} (r : Rel ctx (S n)) (e : expr) : Rel ctx n :=
    fun var =>
      ORapp (r var) (openupSingle (ctx := ctx) (e : interp var TTexpr)).

  Instance Apply_Rel_expr ctx n : Apply (Rel ctx (S n)) expr (Rel ctx n) :=
    {
      apply := RELapp'
    }.

  (* Instance Apply_relOpen_expr var ctx n : Apply (relOpen var ctx (S n)) (relOpen var ctx TTexpr) (relOpen var ctx n) := *)
  (*   { *)
  (*     apply := @ORapp var ctx n *)
  (*   }. *)

  Inductive eqv : forall {n}, Rel ctx n -> Rel ctx n -> Prop :=
  | ERuleRefl n R : @eqv n R R
  | ERuleSymm n R1 R2 : @eqv n R1 R2 -> @eqv n R2 R1
  | ERuleTran n R1 R2 R3 : @eqv n R1 R2 -> @eqv n R2 R3 -> @eqv n R1 R3
  | ERuleLaterAnd P Q : eqv (▹ (P /\ Q)) (▹P /\ ▹Q)
  | ERuleLaterOr P Q : eqv (▹ (P \/ Q)) (▹P \/ ▹Q)
  | ERuleLaterImply P Q : eqv (▹ (P ⇒ Q)) (▹P ⇒ ▹Q)
  | ERuleLaterForall1 T P : eqv (▹ (∀x:T, P x)) (∀x, ▹(P x))
  | ERuleLaterExists1 T P : eqv (▹ (∃x:T, P x)) (∃x, ▹(P x))
  | ERuleLaterForallR (n : nat) P : eqv (fun var => ▹ (∀2 (R : relOpen var ctx n), P var R))%OR (fun var => ∀2 R, ▹(P var R))%OR
  | ERuleLaterExistsR (n : nat) P : eqv (fun var => ▹ (∃2 (R : relOpen var ctx n), P var R))%OR (fun var => ∃2 R, ▹(P var R))%OR
  | RuleElem n (R : Rel ctx (S n)) (e : Rel ctx TTexpr) : eqv ((\x, R $ x) $ e) (R $ e)
  | RuleRecur {n : nat} (R : Rel (TTrel n :: ctx) n) : eqv (fun var => @@r, R var (Rvar r))%OR (fun var => (@@r, R var (Rvar r)))%OR
  .

  Fixpoint Iff {n : nat} : Rel ctx n -> Rel ctx n -> Rel ctx 0 :=
    match n return Rel ctx n -> Rel ctx n -> Rel ctx 0 with
      | 0 => fun P1 P2 => P1 ⇒ P2 /\ P2 ⇒ P1
      | S n' => fun R1 R2 => ∀e : expr, Iff (R1 $ e) (R2 $ e)
    end.

  Infix "≡" := Iff (at level 70, no associativity).

  Inductive valid : list (Rel ctx 0) -> Rel ctx 0 -> Prop :=
  | RuleEqv C P1 P2 : eqv P1 P2 -> C |~ P1 -> C |~ P2
  | RuleMono C P : C |~ P -> C |~ ▹P
  | RuleLob C P : ▹P :: C |~ P -> C |~ P
  | RuleReplace2 C {n : nat} R1 R2 (P : Rel (TTrel n :: ctx) 0) : C |~ R1 ≡ R2 -> C |~ P $$ R1 -> C |~ P $$ R2
  where "C |~ P" := (valid C P)
  .

End inferRules.

Notation "Ps |~ P" := (valid Ps P) (at level 90).

Definition apply_Substs {lctx} `{forall var, Apply (csubsts var [] lctx) (B lctx) B'} {ctx} (rho : Substs ctx lctx) (b : B lctx) : Rel ctx (TTother B') :=
  fun var =>
    openup_csubsts (fun rho => rho $ b) (rho var).

Instance Apply_Substs_expr lctx ctx : Apply (Substs ctx lctx) (open_expr lctx) (Rel ctx TTexpr) :=
  {
    apply := apply_Substs
  }.

Instance Apply_Substs_cexpr lctx ctx : Apply (Substs ctx lctx) (open_cexpr lctx) (Rel ctx (TTother cexpr)) :=
  {
    apply := apply_Substs
  }.

Instance Apply_Substs_size lctx ctx : Apply (Substs ctx lctx) (open_size lctx) (Rel ctx (TTother size)) :=
  {
    apply := apply_Substs
  }.

Import StandalonePHOAS.
Local Open Scope REL.

Definition openupE {t1 t2 t3 lctx var} (f : t1 -> t2 -> csubsts var [] lctx -> interp var t3) : forall ctx, (relOpen var ctx (TTother t1) -> relOpen var ctx (TTother t2) -> csubsts var ctx lctx -> relOpen var ctx t3).
  admit.
(*
  refine
    (fix F ctx : csubsts var ctx lctx -> relOpen var ctx range :=
       match ctx return csubsts var ctx lctx -> relOpen var ctx range with
         | nil => _
         | nv :: ctx' => _
       end).
  {
    intros a.
    exact (f a).
  }
  {
    simpl in *.
    intros a b.
    exact ((F ctx') (a $ b)).
  }
*)
Defined.

Definition E'' Ct {lctx} tau {var} n s := @E Ct lctx tau n s var.
Definition openE Ct {lctx} tau {var ctx} := openupE (var := var) (t1 := nat) (t2 := size) (t3 := 1) (ctx := ctx) (lctx := lctx) (@E'' Ct lctx tau var).
Definition goodExpr Ct {lctx} tau {ctx} (n : Rel ctx (TTother nat)) (s : Rel ctx (TTother size)) (ρ : t_ρ ctx lctx) : Rel ctx 1 := fun var => openE Ct tau (n var) (s var) (ρ var).

Definition c2n' {ctx} (c : Rel ctx (TTother cexpr)) : Rel ctx (TTother nat) :=
  fun var => openup1 var (domain := TTother cexpr) (range := TTother nat) c2n ctx (c var).

Instance Coerce_cexpr_nat' : Coerce (Rel ctx (TTother cexpr)) (Rel ctx (TTother nat)) :=
  {
    coerce := c2n'
  }.

Definition related {lctx} Ct Γ (e : open_expr lctx) τ (c : open_cexpr lctx) (s : open_size lctx) :=
  make_Ps Ct Γ |~
          let ρ := (make_ρ lctx) in
          ρ $$ e ∈ goodExpr Ct τ !(ρ $ c) (ρ $ s) ρ.

Notation "⊩" := related.

Lemma adequacy Ct e τ c s : ⊩ Ct [] e τ c s -> forall n e', nsteps e n e' -> n ≤ (1 + Ct) * (1 + !c).
  admit.
Qed.

Definition add_Rel `{Add A B C} {ctx} (a : Rel ctx (TTother A)) (b : Rel ctx (TTother B)) : Rel ctx (TTother C) :=
  fun var => openup5 var (t1 := TTother A) (t2 := TTother B) add ctx (a var) (b var).

Instance Add_Rel `{Add A B C} {ctx} : Add (Rel ctx (TTother A)) (Rel ctx (TTother B)) (Rel ctx (TTother C)) :=
  {
    add := add_Rel
  }.

Definition open_EC : context -> context -> Type.
  admit.
Defined.

Definition EC := open_EC [] [].

Definition plug {ctx} : Rel ctx (TTother EC) -> Rel ctx TTexpr -> Rel ctx TTexpr.
  admit.
Defined.

Definition goodEC {ctx lctx lctx'} : nat -> Rel ctx TTexpr -> Rel ctx (TTother EC) -> Substs ctx lctx -> open_type lctx -> Rel ctx (TTother (open_cexpr [CEexpr])) -> Rel ctx (TTother (open_size [CEexpr])) -> Substs ctx lctx' -> open_type lctx' -> Rel ctx 0.
  admit.
Defined.

Definition subst_Rel `{Subst t A B} {ctx} lctx (x : var t lctx) (v : Rel ctx (TTother (A (removen lctx x)))) (b : Rel ctx (TTother (B lctx))) : Rel ctx (TTother (B (removen lctx x))) :=
  fun var =>
    openup5 var (t1 := TTother (A (removen lctx x))) (t2 := TTother (B lctx)) (t3 := TTother (B (removen lctx x))) (substx x) ctx (v var) (b var).

Instance Subst_Rel `{Subst t A B} {ctx} : Subst t (fun lctx => Rel ctx (TTother (A lctx))) (fun lctx => Rel ctx (TTother (B lctx))) :=
  {
    substx := subst_Rel
  }.

Section DerivedRules.

  Context `{C : list (Rel ctx 0)}.

  (*here*)

  Lemma LRbind {lctx lctx'} Ct e (τ : open_type lctx) (ρ : Substs ctx lctx) c₁ s₁ E c₂ s₂ (τ' : open_type lctx') (ρ' : Substs ctx lctx') : 
    C |~ e ∈ goodExpr Ct τ c₁ s₁ ρ ->
    C |~ goodEC Ct e E ρ τ c₂ s₂ ρ' τ' ->
    C |~ plug E e ∈ goodExpr (1+2*Ct) τ' (c₁ + !(subst s₁ c₂)) (subst s₁ s₂) ρ'.
    admit.
  Qed.

End DerivedRules.

Lemma foundamental :
  forall {ctx} (Γ : tcontext ctx) e τ c s,
    ⊢ Γ e τ c s -> 
    exists Ct, ⊩ Ct Γ e τ c s.
Proof.
  induction 1.
  {
    unfold related.
    exists 0.
    simpl.
    admit.
  }
  {
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

Theorem sound_wrt_bound_proof : sound_wrt_bounded.
Proof.
  admit.
Qed.
