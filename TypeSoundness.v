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

Inductive steps : expr -> expr -> Prop :=
| Steps0 e : steps e e
| StepsS e1 e2 e3 : step e1 e2 -> steps e2 e3 -> steps e1 e3
.

Infix "↝" := step (at level 50).
Infix "↝*" := steps (at level 50).

Notation "⊢" := typing.
Definition typingsim e τ := exists c s, ⊢ TCnil e τ c s.
Notation "|-" := typingsim.

Definition nostuck e := forall e', e ↝* e' -> IsValue e' \/ exists e'', e' ↝ e''.

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
          nsteps (f $ v) n e' -> n ≤ C * (1 + !(subst v c)).

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
Unset Maximal Implicit Insertion.

Arguments Rvar {var n} _ .
Arguments Rinj {var} _ .
Arguments Rtrue {var} .
Arguments Rfalse {var} .

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

Module ClosedPHOAS.

Notation "⊤" := Rtrue : rel.
Notation "⊥" := Rtrue : rel.
Notation "\ x .. y , p" := (Rabs (fun x => .. (Rabs (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity) : rel.
Notation "∀ x .. y , p" := (Rforall1 (fun x => .. (Rforall1 (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity) : rel.
Notation "∃ x .. y , p" := (Rexists1 (fun x => .. (Rexists1 (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity) : rel.
Definition Rforall2' {var n} P := (@Rforall2 var n (fun x => P (Rvar x))).
Notation "∀₂ x .. y , p" := (Rforall2' (fun x => .. (Rforall2' (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity) : rel.
Definition Rexists2' {var n} P := (@Rexists2 var n (fun x => P (Rvar x))).
Notation "∃₂ x .. y , p" := (Rexists2' (fun x => .. (Rexists2' (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity) : rel.
Definition Rrecur' {var n} P := (@Rrecur var n (fun x => P (Rvar x))).
Notation "@@ x .. y , p" := (Rrecur' (fun x => .. (Rrecur' (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity) : rel.
Notation "⌈ P ⌉" := (Rinj P) : rel.
Global Instance Apply_rel_expr {var n} : Apply (rel var (S n)) expr (rel var n) :=
  {
    apply := Rapp
  }.
Infix "/\" := Rand : rel.
Infix "\/" := Ror : rel.
Infix "⇒" := Rimply (at level 90) : rel.
Notation "▹" := Rlater : rel.

Delimit Scope rel with rel.

Section TestNotations.
  
  Variable var : nat -> Type.

  Open Scope rel.

  Definition ttt1 : rel var 1 := \e , ⊤.
  Definition ttt2 : rel var 1 := \e , ⌈e ↓ Tunit⌉.
  Definition ttt3 : rel var 1 := \_ , ⌈True /\ True⌉.

End TestNotations.

End ClosedPHOAS.

(* An Logical Step-indexed Logical Relation (LSLR) for boundedness *)

Local Open Scope prog_scope.

(* closing substitutions *)
Section csubsts.
  
  Context `{var : nat -> Type}.

  Inductive SubstEntry : CtxEntry -> Type :=
  | SEtype (_ : type) (_ : rel var 1) : SubstEntry CEtype
  | SEexpr (_ : expr) : SubstEntry CEexpr
  .

  Inductive csubsts : context -> Type :=
  | CSnil : csubsts []
  | CScons {t lctx} : SubstEntry t -> csubsts lctx -> csubsts (t :: lctx)
  .

  Definition pair_of_se (e : SubstEntry CEtype) : type * rel var 1 :=
    match e with
      | SEtype t r => (t, r)
    end.

  Definition type_of_se := pair_of_se >> fst.
  Definition sem_of_se := pair_of_se >> snd.

  Definition expr_of_se (e : SubstEntry CEexpr) : expr :=
    match e with
      | SEexpr s => s
    end.

  Definition pair_of_cs {t lctx} (rho : csubsts (t :: lctx)) : SubstEntry t * csubsts lctx :=
    match rho with
      | CScons _ _ e rho' => (e, rho')
    end.

  Arguments tl {A} _ .

  Require Import Bedrock.Platform.Cito.ListFacts4.

  Definition csubsts_sem : forall {lctx}, csubsts lctx -> open_var CEtype lctx -> rel var 1.
    refine
      (fix csubsts_sem {lctx} : csubsts lctx -> open_var CEtype lctx -> rel var 1 :=
         match lctx return csubsts lctx -> open_var CEtype lctx -> rel var 1 with
           | nil => _
           | t :: lctx' => 
             fun rho =>
               match rho in (csubsts c) return c = t :: lctx' -> open_var CEtype (t :: lctx') -> rel var 1 with
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

  Global Instance Apply_csubsts_nat_rel lctx : Apply (csubsts lctx) (open_var CEtype lctx) (rel var 1) :=
    {
      apply := csubsts_sem
    }.

  Definition csubst_type `{Subst CEtype open_type B} {lctx} (v : SubstEntry CEtype) (b : B (CEtype :: lctx)) : B lctx.
    refine
      (subst (cast (shiftby lctx (type_of_se v)) _) b).
    simpl.
    eapply app_nil_r.
  Defined.
  
  Definition csubst_expr `{Subst CEexpr open_expr B} {lctx} (v : SubstEntry CEexpr) (b : B (CEexpr :: lctx)) : B lctx.
    refine
      (subst (cast (shiftby lctx (expr_of_se v)) _) b).
    simpl.
    eapply app_nil_r.
  Defined.
  
  Definition subst_close `{Subst CEtype open_type B, Subst CEexpr open_expr B} : forall lctx, csubsts lctx -> B lctx -> B [].
    refine
      (fix subst_close lctx : csubsts lctx -> B lctx -> B [] :=
         match lctx return csubsts lctx -> B lctx -> B [] with
           | nil => fun _ b => b
           | t :: lctx' =>
             fun rho =>
               match rho in (csubsts c) return c = t :: lctx' -> B (t :: lctx') -> B [] with
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

  Global Instance Apply_csubsts_cexpr_cexpr lctx : Apply (csubsts lctx) (open_cexpr lctx) cexpr :=
    {
      apply := @csubsts_cexpr _
    }.

  Definition csubsts_size :=
    subst_close (B := open_size).

  Global Instance Apply_csubsts_size_size lctx : Apply (csubsts lctx) (open_size lctx) size :=
    {
      apply := @csubsts_size _
    }.

  Definition csubsts_type :=
    subst_close (B := open_type).

  Global Instance Apply_csubsts_type_type lctx : Apply (csubsts lctx) (open_type lctx) type :=
    {
      apply := @csubsts_type _
    }.

  Definition csubsts_expr :=
    subst_close (B := open_expr).

  Global Instance Apply_csubsts_expr_expr lctx : Apply (csubsts lctx) (open_expr lctx) expr :=
    {
      apply := @csubsts_expr _
    }.

  Definition add_pair {lctx} p rho :=
    CScons (lctx := lctx) (SEtype (fst p) (snd p)) rho.

  Global Instance Add_pair_csubsts lctx : Add (type * rel var 1) (csubsts lctx) (csubsts (CEtype :: lctx)) :=
    {
      add := add_pair
    }.

  Definition add_expr {lctx} e rho :=
    CScons (lctx := lctx) (SEexpr e) rho.
  
  Global Instance Add_expr_csubsts lctx : Add expr (csubsts lctx) (csubsts (CEexpr :: lctx)) :=
    {
      add := add_expr
    }.

End csubsts.

Arguments SubstEntry : clear implicits.
Arguments csubsts : clear implicits.

Notation "[ ]" := CSnil : CS.
Notation "[ x ; .. ; y ]" := (CScons x .. (CScons y CSnil) ..) : CS.
Infix "::" := CScons (at level 60, right associativity) : CS.
Delimit Scope CS with CS.
Bind Scope CS with csubsts.

Import ClosedPHOAS.

Definition VSet {var} τ (S : rel var 1) := (∀v, v ∈ S ⇒ ⌈v ↓ τ⌉)%rel.

Definition terminatesWith e v := e ↝* v /\ IsValue v.
Infix "⇓" := terminatesWith (at level 51).
Definition stepsex e m e' := exists n, nstepsex e n m e'.
Definition terminatesWithEx e m v := stepsex e m v /\ IsValue v.
Notation "⇓#" := terminatesWithEx.

(* A "step-indexed" kriple model *)
(* the logical relation *)
Section LR.
  
  Variable B : nat.

  Open Scope rel.

  Fixpoint relE' {lctx} (relV : forall var, csubsts var lctx -> rel var 1) τ (c : nat) (s : size) var (ρ : csubsts var lctx) {struct c} : rel var 1 :=
    \e, ⌈|- e (ρ $ τ) /\ 
        (forall n e', nstepsex e n 0 e' -> n ≤ B)⌉ /\ 
        (∀v, ⌈⇓# e 0 v⌉ ⇒ v ∈ relV var ρ /\ ⌈!v ≤ s⌉) /\
        (∀e', ⌈stepsex e 1 e'⌉ ⇒ 
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

  Fixpoint relV {lctx} τ var (ρ : csubsts var lctx) : rel var 1 :=
    match τ with
      | Tvar α => csubsts_sem ρ α
      | Tunit => \v, ⌈v ↓ Tunit⌉
      | τ₁ × τ₂ => \v, ⌈v ↓ ρ $$ τ⌉ /\ ∃a b, ⌈v = !(a, b)⌉ /\ a ∈ relV τ₁ ρ /\ b ∈ relV τ₂ ρ
      | τ₁ + τ₂ => \v, ⌈v ↓ ρ $$ τ⌉ /\ ∃v', (⌈v = Einl (ρ $ τ₂) v'⌉ /\ v' ∈ relV τ₁ ρ) \/ (⌈v = Einr (ρ $ τ₁) v'⌉ /\ v' ∈ relV τ₂ ρ)
      | Tarrow τ₁ c s τ₂ => \v, ⌈v ↓ ρ $$ τ⌉ /\ ∃τ₁' e, ⌈v = Eabs τ₁' e⌉ /\ ∀v₁, v₁ ∈ relV τ₁ ρ ⇒ subst v₁ e ∈ relE' (relV τ₂) τ₂ !(ρ $ subst !(!v₁) c) (ρ $ subst !(!v₁) s) (add v₁ ρ)
      | Tuniversal c s τ₁ => \v, ⌈v ↓ ρ $$ τ⌉ /\ ∀τ', ∀₂ S, VSet τ' S ⇒ v $$ τ' ∈ relE' (relV τ₁) τ₁ !(ρ $ c) (ρ $ s) (add (τ', S) ρ)
      | Trecur τ₁ => @@S, \v, ⌈v ↓ ρ $$ τ⌉ /\ ∃v', ⌈v = Efold (ρ $ τ) v'⌉ /\ ▹ (v' ∈ relV τ₁ (add (ρ $ τ, S) ρ))
      | _ => \_, ⊥
    end
  .

  Definition relE {lctx} τ := relE' (lctx := lctx) (relV τ) τ.

End LR.

Set Maximal Implicit Insertion.
Section Funvar.

  Variable var : nat -> Type.

  Definition Ctx := list ((nat -> Type) -> Type).

  Fixpoint Funvar domains range :=
    match domains with
      | nil => range var
      | domain :: domains' => domain var -> Funvar domains' range
    end.

End Funvar.

Definition TTrel n var := rel var n.
Coercion TTrel : nat >-> Funclass.

Section OR.

  Context `{var : nat -> Type}.
  
  Notation Funvar := (Funvar var).

  Definition openup1 {t1 t2} (f : t1 var -> t2 var) : forall C, Funvar C t1 -> Funvar C t2.
    refine
      (fix F C : Funvar C t1 -> Funvar C t2 :=
         match C return Funvar C t1 -> Funvar C t2 with
           | nil => _
           | nv :: C' => _
         end);
    simpl; eauto.
  Defined.

  Definition openup2 {n1 n2 T} (f : (T -> rel var n1) -> rel var n2) : forall C, (T -> Funvar C n1) -> Funvar C n2.
    refine
      (fix F C : (T -> Funvar C n1) -> Funvar C n2 :=
         match C return (T -> Funvar C n1) -> Funvar C n2 with
           | nil => _
           | nv :: C' => _ 
         end);
    simpl; eauto.
  Defined.

  Definition openup3 {n T} (f : T -> rel var n) : forall C, T -> Funvar C n.
    refine
      (fix F C : T -> Funvar C n :=
         match C return T -> Funvar C n with
           | nil => _
           | nv :: C' => _ 
         end);
    simpl; eauto.
  Defined.
  
  Definition openupSingle {t2} (f : t2 var) : forall ctx, Funvar ctx t2.
    refine
      (fix F ctx : Funvar ctx t2 :=
         match ctx return Funvar ctx t2 with
           | nil => _
           | t :: ctx' => _ 
         end);
    simpl; eauto.
  Defined.

  Definition openup5 {t1 t2 t3} (f : t1 var -> t2 var -> t3 var) : forall C, Funvar C t1 -> Funvar C t2 -> Funvar C t3.
    refine
      (fix F C : Funvar C t1 -> Funvar C t2 -> Funvar C t3 :=
         match C return Funvar C t1 -> Funvar C t2 -> Funvar C t3 with
           | nil => _
           | nv :: C' => _ 
         end);
    simpl; eauto.
  Defined.

  Definition openup6 {n1 T n2} (f : rel var n1 -> T -> rel var n2) : forall C, Funvar C n1 -> Funvar C (const T) -> Funvar C n2.
    refine
      (fix F C : Funvar C n1 -> Funvar C (const T) -> Funvar C n2 :=
         match C return Funvar C n1 -> Funvar C (const T) -> Funvar C n2 with
           | nil => _
           | nv :: C' => _ 
         end);
    simpl; eauto.
  Defined.

  Definition openup8 {n1 n2 T} (f : (T -> rel var n1) -> rel var n2) : forall C, (Funvar C (const T) -> Funvar C n1) -> Funvar C n2.
    refine
      (fix F C : (Funvar C (const T) -> Funvar C n1) -> Funvar C n2 :=
         match C return (Funvar C (const T) -> Funvar C n1) -> Funvar C n2 with
           | nil => _
           | nv :: C' => _
         end);
    simpl; eauto.
  Defined.

  Context `{ctx : Ctx}.

  Definition ORvar {n} := openup3 (@Rvar var n) ctx.
  Definition ORinj := openup3 (@Rinj var) ctx.
  Definition ORtrue := openupSingle (t2 := 0) (@Rtrue var) ctx.
  Definition ORfalse := openupSingle (t2 := 0) (@Rfalse var) ctx.
  Definition ORand := openup5 (@Rand var) (t1 := 0) (t2 := 0) (t3 := 0) ctx.
  Definition ORor := openup5 (@Ror var) (t1 := 0) (t2 := 0) (t3 := 0) ctx.
  Definition ORimply := openup5 (@Rimply var) (t1 := 0) (t2 := 0) (t3 := 0) ctx.
  Definition ORforall2 {n} := openup2 (@Rforall2 var n) ctx.
  Definition ORexists2 {n} := openup2 (@Rexists2 var n) ctx.
  Definition ORforall1 {T} := openup2 (@Rforall1 var T) ctx.
  Definition ORexists1 {T} := openup2 (@Rexists1 var T) ctx.
  Definition ORabs {n} := openup2 (@Rabs var n) ctx.
  Definition ORapp {n} := openup6 (@Rapp var n) ctx.
  Definition ORrecur {n} := openup2 (@Rrecur var n) ctx.
  Definition ORlater := openup1 (t1 := 0) (t2 := 0) (@Rlater var) ctx.

End OR.

Unset Maximal Implicit Insertion.

Definition Rel ctx t := forall var, Funvar var ctx t.

Definition lift_Rel {ctx t2} new : Rel ctx t2 -> Rel (new :: ctx) t2 :=
  fun r var x => r var.

Definition t_Ps ctx := list (Rel ctx 0).
Definition Substs ctx lctx := Rel ctx (flip csubsts lctx).
Notation t_ρ := Substs.
Notation lift_ρ := lift_Rel.

Definition lift_Ps {ctx} t (Ps : t_Ps ctx) : t_Ps (t :: ctx):=
  map (lift_Rel t) Ps.

(* should compute *)
Definition extend {var t2} ctx new : Funvar var ctx t2 -> Funvar var (ctx ++ new) t2.
  induction ctx.
  {
    simpl.
    intros r.
    exact (openupSingle r _).
  }
  {
    simpl.
    intros r x.
    exact (IHctx (r x)).
  }
Defined.

Definition add_Funvar {var} `{H : Add (A var) (B var) (C var)} {ctx} (a : Funvar var ctx A) (b : Funvar var ctx B) : Funvar var ctx C :=
  openup5 (t1 := A) (t2 := B) add ctx a b.

Global Instance Add_Funvar {var} `{Add (A var) (B var) (C var)} {ctx} : Add (Funvar var ctx A) (Funvar var ctx B) (Funvar var ctx C) :=
  {
    add := add_Funvar
  }.

Definition pair_var var := (type * rel var 1)%type.

Global Instance Add_pair_csubsts' {var lctx} : Add (pair_var var) (flip csubsts lctx var) (flip csubsts (CEtype :: lctx) var) :=
  {
    add := add_pair
  }.

Notation TTexpr := (const expr).
Notation TTtype := (const type).

Definition add_ρ_type {ctx lctx} (ρ : t_ρ ctx lctx) : t_ρ (TTrel 1 :: TTtype :: ctx) (CEtype :: lctx) :=
  let ρ := lift_ρ TTtype ρ in
  let ρ := lift_ρ 1 ρ in
  let ρ := fun var => add (extend (t2 := pair_var) [TTrel 1; TTtype] ctx (fun S τ => (τ, S))) (ρ var) in
  ρ
.

Definition add_Ps_type {ctx} (Ps : t_Ps ctx) : t_Ps (TTrel 1 :: TTtype :: ctx) :=
  let Ps := lift_Ps TTtype Ps in
  let Ps := (fun var => extend [TTtype] ctx (fun τ => ⌈kinding TCnil τ 0⌉%rel : Funvar var [] 0)) :: Ps in
  let Ps := lift_Ps 1 Ps in
  let Ps := (fun var => extend [TTrel 1; TTtype] ctx (fun S τ => VSet τ S : Funvar var [] 0)) :: Ps in
  Ps
.

Global Instance Add_expr_csubsts' {var lctx} : Add (TTexpr var) (flip csubsts lctx var) (flip csubsts (CEexpr :: lctx) var) :=
  {
    add := add_expr
  }.

Definition add_ρ_expr {ctx lctx} (ρ : t_ρ ctx lctx) : t_ρ (TTexpr :: ctx) (CEexpr :: lctx) :=
  let ρ := lift_ρ TTexpr ρ in
  let ρ := fun var => add (extend [TTexpr] ctx (fun v => v)) (ρ var) in
  ρ
.

Global Instance Apply_rel_expr' {var n} : Apply (rel var (S n)) (TTexpr var) (rel var n) :=
  {
    apply := Rapp
  }.

Definition add_Ps_expr {ctx lctx} τ B (Ps : t_Ps ctx) (ρ : t_ρ ctx lctx) : t_Ps (TTexpr :: ctx) :=
  let Ps := lift_Ps TTexpr Ps in
  let Ps := (fun var v => openup1 (fun ρ => v ∈ relV B τ ρ) _ (ρ var)) :: Ps in
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

Module OpenPHOAS.
  
Notation "⊤" := ORtrue : OR.
Notation "⊥" := ORtrue : OR.
Notation "⌈ P ⌉" := (ORinj P) : OR.
Notation "\ x .. y , p" := (ORabs (fun x => .. (ORabs (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity) : OR.
Notation "∀ x .. y , p" := (ORforall1 (fun x => .. (ORforall1 (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity) : OR.
Notation "∃ x .. y , p" := (ORexists1 (fun x => .. (ORexists1 (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity) : OR.
Definition ORforall2' {var ctx n} P := (@ORforall2 var ctx n (fun x => P (ORvar (ctx := ctx) x))).
Notation "∀₂ x .. y , p" := (ORforall2' (fun x => .. (ORforall2' (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity) : OR.
Definition ORexists2' {var ctx n} P := (@ORexists2 var ctx n (fun x => P (ORvar (ctx := ctx) x))).
Notation "∃₂ x .. y , p" := (ORexists2' (fun x => .. (ORexists2' (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity) : OR.
Notation "@@ x .. y , p" := (ORrecur (fun x => .. (ORrecur (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity) : OR.
Definition ORrecur' {var ctx n} P := (@ORrecur var ctx n (fun x => P (ORvar (ctx := ctx) x))).
Notation "@@@ x .. y , p" := (ORrecur' (fun x => .. (ORrecur' (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity) : OR.
Global Instance Apply_Funvar_TTexpr {var ctx n} : Apply (Funvar var ctx (S n)) (Funvar var ctx TTexpr) (Funvar var ctx n) :=
  {
    apply := ORapp
  }.
Infix "/\" := ORand : OR.
Infix "\/" := ORor : OR.
Infix "⇒" := ORimply (at level 90) : OR.
Notation "▹" := ORlater : OR.

Delimit Scope OR with OR.

Section TestNotations.
  
  Variable var : nat -> Type.
  Variable ctx : Ctx.

  Open Scope OR.
  
  Definition ttt1 : Funvar var ctx 1 := \e , ⊤.
  Definition ttt2 : Funvar var ctx 1 := \e , ⌈e ↓ Tunit⌉.
  Definition ttt3 : Funvar var ctx 0 := ⌈True /\ True⌉.
  Definition ttt4 : Funvar var ctx 0 := ∀e, ⌈e = @Ett nil⌉.
  Definition ttt5 : Funvar var ctx 0 := ∃e, ⌈e = @Ett nil⌉.

End TestNotations.

End OpenPHOAS.

Set Maximal Implicit Insertion.
Section REL.

  Context `{ctx : Ctx}.
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

Module StandalonePHOAS.
  
Notation "⊤" := RELtrue : REL.
Notation "⊥" := RELtrue : REL.
Notation "⌈ P ⌉" := (RELinj P) : REL.
Notation "\ x .. y , p" := (RELabs (fun x => .. (RELabs (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity) : REL.
Notation "∀ x .. y , p" := (RELforall1 (fun x => .. (RELforall1 (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity) : REL.
Notation "∃ x .. y , p" := (RELexists1 (fun x => .. (RELexists1 (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity) : REL.
Global Instance Apply_Rel_TTexpr {ctx n} : Apply (Rel ctx (S n)) (Rel ctx TTexpr) (Rel ctx n) :=
  {
    apply := RELapp
  }.
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

Definition openup7 {var t1 t2} : forall ctx, (t1 var -> Funvar var ctx t2) -> Funvar var ctx t1 -> Funvar var ctx t2.
  refine
    (fix F ctx : (t1 var -> Funvar var ctx t2) -> Funvar var ctx t1 -> Funvar var ctx t2 :=
       match ctx return (t1 var -> Funvar var ctx t2) -> Funvar var ctx t1 -> Funvar var ctx t2 with
         | nil => _
         | t :: ctx' => _ 
       end);
  simpl; eauto.
Defined.

Definition apply_Rel_Rel {n ctx t2} : Rel (n :: ctx) t2 -> Rel ctx n -> Rel ctx t2 :=
  fun f x var => openup7 _ (f var) (x var).

Global Instance Apply_Rel_Rel n ctx t2 : Apply (Rel (n :: ctx) t2) (Rel ctx n) (Rel ctx t2) :=
  {
    apply := apply_Rel_Rel
  }.

Reserved Notation "C |~ P" (at level 89).

Section inferRules.

  Import OpenPHOAS.
  Import StandalonePHOAS.
  Open Scope REL.

  Variable ctx : Ctx.

  Global Instance Apply_Rel_TTexpr ctx n : Apply (Rel ctx (S n)) (Rel ctx TTexpr) (Rel ctx n) :=
    {
      apply := RELapp
    }.

  Definition RELapp' {ctx n} (r : Rel ctx (S n)) (e : expr) : Rel ctx n :=
    fun var =>
      ORapp (r var) (openupSingle e ctx).

  Global Instance Apply_Rel_expr ctx n : Apply (Rel ctx (S n)) expr (Rel ctx n) :=
    {
      apply := RELapp'
    }.

  Inductive eqv : forall {n}, Rel ctx n -> Rel ctx n -> Prop :=
  | ERuleRefl n R : @eqv n R R
  | ERuleSymm n R1 R2 : @eqv n R1 R2 -> @eqv n R2 R1
  | ERuleTran n R1 R2 R3 : @eqv n R1 R2 -> @eqv n R2 R3 -> @eqv n R1 R3
  | ERuleLaterAnd P Q : eqv (▹ (P /\ Q)) (▹P /\ ▹Q)
  | ERuleLaterOr P Q : eqv (▹ (P \/ Q)) (▹P \/ ▹Q)
  | ERuleLaterImply P Q : eqv (▹ (P ⇒ Q)) (▹P ⇒ ▹Q)
  | ERuleLaterForall1 T P : eqv (▹ (∀x:T, P x)) (∀x, ▹(P x))
  | ERuleLaterExists1 T P : eqv (▹ (∃x:T, P x)) (∃x, ▹(P x))
  | ERuleLaterForallR (n : nat) P : eqv (fun var => ▹ (∀₂ (R : Funvar var ctx n), P var R))%OR (fun var => ∀₂ R, ▹(P var R))%OR
  | ERuleLaterExistsR (n : nat) P : eqv (fun var => ▹ (∃₂ (R : Funvar var ctx n), P var R))%OR (fun var => ∃₂ R, ▹(P var R))%OR
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

Notation "Ps |~ P" := (valid Ps P) (at level 89).

Definition apply_Substs {lctx} `{H : forall var, Apply (flip csubsts lctx var) (B lctx) (B' var)} {ctx} (rho : Substs ctx lctx) (b : B lctx) : Rel ctx B' :=
  fun var =>
    openup1 (fun rho => rho $ b) _ (rho var).

Global Instance Apply_Substs_expr lctx ctx : Apply (Substs ctx lctx) (open_expr lctx) (Rel ctx TTexpr) :=
  {
    apply := apply_Substs (H := fun var => @Apply_csubsts_expr_expr var lctx)
  }.

Global Instance Apply_Substs_cexpr lctx ctx : Apply (Substs ctx lctx) (open_cexpr lctx) (Rel ctx (const cexpr)) :=
  {
    apply := apply_Substs (H := fun var => @Apply_csubsts_cexpr_cexpr var lctx)
  }.

Global Instance Apply_Substs_size lctx ctx : Apply (Substs ctx lctx) (open_size lctx) (Rel ctx (const size)) :=
  {
    apply := apply_Substs (H := fun var => @Apply_csubsts_size_size var lctx)
  }.

Import StandalonePHOAS.
Local Open Scope REL.

Definition openup9 {t1 t2 t3 t4 var} (f : t1 var -> t2 var -> t3 var -> t4 var) : forall ctx, Funvar var ctx t1 -> Funvar var ctx t2 -> Funvar var ctx t3 -> Funvar var ctx t4.
  refine
    (fix F ctx : Funvar var ctx t1 -> Funvar var ctx t2 -> Funvar var ctx t3 -> Funvar var ctx t4 :=
       match ctx return Funvar var ctx t1 -> Funvar var ctx t2 -> Funvar var ctx t3 -> Funvar var ctx t4 with
         | nil => _
         | nv :: ctx' => _
       end);
  simpl; eauto.
Defined.

Definition relE'' B {lctx} tau {var} n s := @relE B lctx tau n s var.
Definition openE B {lctx} tau {var ctx} := openup9 (t1 := const nat) (t2 := const size) (t3 := flip csubsts lctx) (t4 := 1) (@relE'' B lctx tau var) ctx.
Definition goodExpr B {lctx} tau {ctx} (n : Rel ctx (const nat)) (s : Rel ctx (const size)) (ρ : t_ρ ctx lctx) : Rel ctx 1 := fun var => openE B tau (n var) (s var) (ρ var).
Definition openE2 B {lctx} tau c s {var ctx} := openup1 (t1 := flip csubsts lctx) (t2 := 1) (@relE B lctx tau c s var) ctx.
Definition goodExpr2 B {lctx} tau c s {ctx} (ρ : t_ρ ctx lctx) : Rel ctx 1 := fun var => openE2 B tau c s (ρ var).
Definition openV2 B {lctx} tau {var ctx} := openup1 (t1 := flip csubsts lctx) (t2 := 1) (@relV B lctx tau var) ctx.
Definition goodValue2 B {lctx} tau {ctx} (ρ : t_ρ ctx lctx) : Rel ctx 1 := fun var => openV2 B tau (ρ var).

Definition c2n' {ctx} (c : Rel ctx (const cexpr)) : Rel ctx (const nat) :=
  fun var => openup1 (t1 := const cexpr) (t2 := const nat) c2n ctx (c var).

Global Instance Coerce_cexpr_nat' : Coerce (Rel ctx (const cexpr)) (Rel ctx (const nat)) :=
  {
    coerce := c2n'
  }.

Definition related {lctx} B Γ (e : open_expr lctx) τ (c : open_cexpr lctx) (s : open_size lctx) :=
  make_Ps B Γ |~
          let ρ := (make_ρ lctx) in
          ρ $$ e ∈ goodExpr B τ !(ρ $ c) (ρ $ s) ρ.

Notation "⊩" := related.

Lemma adequacy B e τ c s : ⊩ B [] e τ c s -> forall n e', nsteps e n e' -> n ≤ (1 + B) * (1 + !c).
  admit.
Qed.

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

Definition goodEC {lctx lctx'} : nat -> expr -> econtext -> Substs [] lctx -> open_type lctx -> open_cexpr [CEexpr] -> open_size [CEexpr] -> Substs [] lctx' -> open_type lctx' -> Rel [] 0 :=
  fun B e E ρ τ c s ρ' τ' => 
    (∀v, v ∈ goodValue2 B τ ρ /\ ⌈e ↝* v⌉ ⇒ E $$ v ∈ goodExpr2 B τ' !(c $ v) (s $ v) ρ')%REL.

(*
Definition goodECopen {var lctx lctx'} : nat -> expr -> econtext -> csubsts var lctx -> open_type lctx -> open_cexpr [CEexpr] -> open_size [CEexpr] -> csubsts var lctx' -> open_type lctx' -> rel var 0 :=
  fun B e E ρ τ c s ρ' τ' =>
    (∀v, v ∈ relV B τ ρ /\ ⌈e ↝* v⌉ ⇒ plug E v ∈ relE B τ' !(c $ v) (s $ v) ρ')%rel.

Definition goodEC {lctx lctx'} : nat -> expr -> econtext -> Substs [] lctx -> open_type lctx -> open_cexpr [CEexpr] -> open_size [CEexpr] -> Substs [] lctx' -> open_type lctx' -> Rel [] 0 :=
  fun B e E ρ τ c s ρ' τ' var => 
    goodECopen B e E (ρ var) τ c s (ρ' var) τ'.
*)

Definition subst_Rel `{Subst t A B} {ctx} lctx (x : var t lctx) (v : Rel ctx (const (A (removen lctx x)))) (b : Rel ctx (const (B lctx))) : Rel ctx (const (B (removen lctx x))) :=
  fun var =>
    openup5 (t1 := const (A (removen lctx x))) (t2 := const (B lctx)) (t3 := const (B (removen lctx x))) (substx x) ctx (v var) (b var).

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


Definition openup_t {ctx} A (lctx : context) := Rel ctx (const (A lctx)).
Definition open_cexpr' {ctx} := openup_t (ctx := ctx) open_cexpr.
Definition open_size' {ctx} := openup_t (ctx := ctx) open_size.

Section DerivedRules.

  Lemma LRbind {lctx lctx'} B (τ : open_type lctx) (ρ : Substs [] lctx) s₁ E c₂ s₂ (τ' : open_type lctx') (ρ' : Substs [] lctx') : 
    [] |~ ∀ e c₁, e ∈ goodExpr2 B τ c₁ s₁ ρ /\ goodEC B e E ρ τ c₂ s₂ ρ' τ' ⇒ E $$ e ∈ goodExpr2 (2 * B) τ' (c₁ + !(c₂ $ s₁)) (s₂ $ s₁) ρ'.
  Proof.
    eapply RuleLob.
    unfold goodEC.
    unfold goodExpr2 at 4.
    unfold openE2.
    unfold relE.
    unfold relE'.
    simpl.
    admit.
  Qed.

End DerivedRules.

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
    destruct IHtyping1 as [C₀ IH₀].
    destruct IHtyping2 as [C₁ IH₁].
    Global Instance Max_nat : Max nat := 
      {
        max := Peano.max
      }.
    exists (3 + 3 * max C₀ C₁).
    unfold related in *.
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

Theorem sound_wrt_bound_proof : sound_wrt_bounded.
Proof.
  admit.
Qed.
