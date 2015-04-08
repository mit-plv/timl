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

(* A Parametric Higher-Order Abstract Syntax (PHOAS) encoding for a second-order modal logic (LSLR) *)

Set Maximal Implicit Insertion.
Section rel.

  Context `{var : nat -> Type}.
  
  Inductive rel : nat -> Type :=
  | Rvar {n} : var n -> rel n
  | Rinj : Prop -> rel 0
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

  Definition Rtrue := Rinj True.
  Definition Rfalse := Rinj False.

End rel.
Unset Maximal Implicit Insertion.

Arguments rel : clear implicits.

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
Infix "===>" := Rimply (at level 86) : rel.
Notation "▹" := Rlater : rel.

Delimit Scope rel with rel.
Bind Scope rel with rel.

Module test_rel.
  
  Variable var : nat -> Type.

  Open Scope rel.

  Definition ttt1 : rel var 1 := \e , ⊤.
  Definition ttt2 : rel var 1 := \e , ⌈e ↓ Tunit⌉.
  Definition ttt3 : rel var 1 := \_ , ⌈True /\ True⌉.

End test_rel.

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

Definition VSet {var} τ (S : rel var 1) := (∀v, v ∈ S ===> ⌈v ↓ τ⌉)%rel.

(* A "step-indexed" kriple model *)
(* the logical relation *)
Section LR.
  
  Variable B : nat.

  Open Scope rel.

  Fixpoint relE' {lctx} (relV : forall var, csubsts var lctx -> rel var 1) τ (c : nat) (s : size) var (ρ : csubsts var lctx) {struct c} : rel var 1 :=
    \e, ⌈|- e (ρ $ τ) /\ 
        (forall n e', (~>## e n 0 e') -> n ≤ B)⌉ /\ 
        (∀v, ⌈⇓*# e 0 v⌉ ===> v ∈ relV var ρ /\ ⌈!v ≤ s⌉) /\
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

  Fixpoint relV {lctx} τ var (ρ : csubsts var lctx) : rel var 1 :=
    match τ with
      | Tvar α => csubsts_sem ρ α
      | Tunit => \v, ⌈v ↓ Tunit⌉
      | τ₁ × τ₂ => \v, ⌈v ↓ ρ $$ τ⌉ /\ ∃a b, ⌈v = !(a, b)⌉ /\ a ∈ relV τ₁ ρ /\ b ∈ relV τ₂ ρ
      | τ₁ + τ₂ => \v, ⌈v ↓ ρ $$ τ⌉ /\ ∃v', (⌈v = Einl (ρ $ τ₂) v'⌉ /\ v' ∈ relV τ₁ ρ) \/ (⌈v = Einr (ρ $ τ₁) v'⌉ /\ v' ∈ relV τ₂ ρ)
      | Tarrow τ₁ c s τ₂ => \v, ⌈v ↓ ρ $$ τ⌉ /\ ∃τ₁' e, ⌈v = Eabs τ₁' e⌉ /\ ∀v₁, v₁ ∈ relV τ₁ ρ ===> subst v₁ e ∈ relE' (relV τ₂) τ₂ !(ρ $ subst !(!v₁) c) (ρ $ subst !(!v₁) s) (add v₁ ρ)
      | Tuniversal c s τ₁ => \v, ⌈v ↓ ρ $$ τ⌉ /\ ∀τ', ∀₂ S, VSet τ' S ===> v $$ τ' ∈ relE' (relV τ₁) τ₁ !(ρ $ c) (ρ $ s) (add (τ', S) ρ)
      | Trecur τ₁ => @@S, \v, ⌈v ↓ ρ $$ τ⌉ /\ ∃τ' v', ⌈v = Efold τ' v'⌉ /\ ▹ (v' ∈ relV τ₁ (add (ρ $ τ, S) ρ))
      | _ => \_, ⊥
    end
  .

  Definition relE {lctx} τ := relE' (lctx := lctx) (relV τ) τ.

End LR.

Set Maximal Implicit Insertion.
Section Funvar.

  Variable var : nat -> Type.

  Definition varTs := list ((nat -> Type) -> Type).

  Fixpoint Funvar domains range :=
    match domains with
      | nil => range var
      | domain :: domains' => domain var -> Funvar domains' range
    end.

End Funvar.

Section openup.

  Context `{var : nat -> Type}.
  
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

  Definition openup6 {t1 T t2} (f : t1 var -> T -> t2 var) : forall {ctx}, Funvar ctx t1 -> Funvar ctx (const T) -> Funvar ctx t2.
    refine
      (fix F ctx : Funvar ctx t1 -> Funvar ctx (const T) -> Funvar ctx t2 :=
         match ctx return Funvar ctx t1 -> Funvar ctx (const T) -> Funvar ctx t2 with
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

Section OR.

  Context `{var : nat -> Type, ctx : varTs}.

  Definition TTrel n var := rel var n.
  Coercion TTrel : nat >-> Funclass.

  Definition ORvar {n : nat} := openup3 (t := n) (@Rvar var n) (ctx := ctx).
  Definition ORinj := openup3 (t := 0) (@Rinj var) (ctx := ctx).
  Definition ORtrue := openupSingle (t := 0) (@Rtrue var) (ctx := ctx).
  Definition ORfalse := openupSingle (t := 0) (@Rfalse var) (ctx := ctx).
  Definition ORand := openup5 (@Rand var) (t1 := 0) (t2 := 0) (t3 := 0) (ctx := ctx).
  Definition ORor := openup5 (@Ror var) (t1 := 0) (t2 := 0) (t3 := 0) (ctx := ctx).
  Definition ORimply := openup5 (@Rimply var) (t1 := 0) (t2 := 0) (t3 := 0) (ctx := ctx).
  Definition ORforall2 {n} := openup2 (t1 := 0) (t2 := 0) (@Rforall2 var n) (ctx := ctx).
  Definition ORexists2 {n} := openup2 (t1 := 0) (t2 := 0) (@Rexists2 var n) (ctx := ctx).
  Definition ORforall1 {T} := openup2 (t1 := 0) (t2 := 0) (@Rforall1 var T) (ctx := ctx).
  Definition ORexists1 {T} := openup2 (t1 := 0) (t2 := 0) (@Rexists1 var T) (ctx := ctx).
  Definition ORabs {n : nat} := openup2 (t1 := n) (t2 := S n) (@Rabs var n) (ctx := ctx).
  Definition ORapp {n} := openup6 (t1 := S n) (t2 := n) (@Rapp var n) (ctx := ctx).
  Definition ORrecur {n : nat} := openup2 (t1 := n) (t2 := n) (@Rrecur var n) (ctx := ctx).
  Definition ORlater := openup1 (t1 := 0) (t2 := 0) (@Rlater var) (ctx := ctx).

End OR.

Unset Maximal Implicit Insertion.

Definition Rel ctx t := forall var, Funvar var ctx t.

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
Infix "===>" := ORimply (at level 86) : OR.
Notation "▹" := ORlater : OR.

Delimit Scope OR with OR.

Module test_OR.
  
  Variable var : nat -> Type.
  Variable ctx : varTs.

  Open Scope OR.
  
  Definition ttt1 : Funvar var ctx 1 := \e , ⊤.
  Definition ttt2 : Funvar var ctx 1 := \e , ⌈e ↓ Tunit⌉.
  Definition ttt3 : Funvar var ctx 0 := ⌈True /\ True⌉.
  Definition ttt4 : Funvar var ctx 0 := ∀e, ⌈e = @Ett nil⌉.
  Definition ttt5 : Funvar var ctx 0 := ∃e, ⌈e = @Ett nil⌉.

End test_OR.

Delimit Scope Rel with Rel.
Bind Scope Rel with Rel.

Set Maximal Implicit Insertion.
Section Rel.

  Context `{ctx : varTs}.
  Notation Rel := (Rel ctx).
  
  Definition Relinj P : Rel 0 := fun var => ORinj P.
  Definition Reltrue : Rel 0 := fun var => ORtrue.
  Definition Relfalse : Rel 0 := fun var => ORfalse.
  Definition Reland (a b : Rel 0) : Rel 0 := fun var => ORand (a var) (b var).
  Definition Relor (a b : Rel 0) : Rel 0 := fun var => ORor (a var) (b var).
  Definition Relimply (a b : Rel 0) : Rel 0 := fun var => ORimply (a var) (b var).
  Definition Relforall1 T (F : T -> Rel 0) : Rel 0 := fun var => ORforall1 (fun x => F x var).
  Definition Relexists1 T (F : T -> Rel 0) : Rel 0 := fun var => ORexists1 (fun x => F x var).
  Definition Relabs (n : nat) (F : expr -> Rel n) : Rel (S n) := fun var => ORabs (fun e => F e var).
  Definition Relapp n (r : Rel (S n)) (e : Rel TTexpr) : Rel n := fun var => ORapp (r var) (e var).
  Definition Rellater (P : Rel 0) : Rel 0 := fun var => ORlater (P var).
  
End Rel.
Unset Maximal Implicit Insertion.

Notation "⊤" := Reltrue : Rel.
Notation "⊥" := Reltrue : Rel.
Notation "⌈ P ⌉" := (Relinj P) : Rel.
Notation "\ x .. y , p" := (Relabs (fun x => .. (Relabs (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity) : Rel.
Notation "∀ x .. y , p" := (Relforall1 (fun x => .. (Relforall1 (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity) : Rel.
Notation "∃ x .. y , p" := (Relexists1 (fun x => .. (Relexists1 (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity) : Rel.
Global Instance Apply_Rel_TTexpr {ctx n} : Apply (Rel ctx (S n)) (Rel ctx TTexpr) (Rel ctx n) :=
  {
    apply := Relapp
  }.
Infix "/\" := Reland : Rel.
Infix "\/" := Relor : Rel.
Infix "===>" := Relimply (at level 86) : Rel.
Notation "▹" := Rellater : Rel.

Module test_Rel.
  
  Variable ctx : varTs.

  Open Scope Rel.

  Definition ttt1 : Rel ctx 1 := \e , ⊤.
  Definition ttt2 : Rel ctx 1 := \e , ⌈e ↓ Tunit⌉.
  Definition ttt3 : Rel ctx 0 := ⌈True /\ True⌉.
  Definition ttt4 : Rel ctx 0 := ∀e, ⌈e = @Ett nil⌉.
  Definition ttt5 : Rel ctx 0 := ∃e, ⌈e = @Ett nil⌉.

End test_Rel.

Definition openup7 {var t1 t2} : forall {ctx}, (t1 var -> Funvar var ctx t2) -> Funvar var ctx t1 -> Funvar var ctx t2.
  refine
    (fix F ctx : (t1 var -> Funvar var ctx t2) -> Funvar var ctx t1 -> Funvar var ctx t2 :=
       match ctx return (t1 var -> Funvar var ctx t2) -> Funvar var ctx t1 -> Funvar var ctx t2 with
         | nil => _
         | t :: ctx' => _ 
       end);
  simpl; eauto.
Defined.

Definition apply_Rel_Rel {n ctx t2} : Rel (n :: ctx) t2 -> Rel ctx n -> Rel ctx t2 :=
  fun f x var => openup7 (f var) (x var).

Global Instance Apply_Rel_Rel n ctx t2 : Apply (Rel (n :: ctx) t2) (Rel ctx n) (Rel ctx t2) :=
  {
    apply := apply_Rel_Rel
  }.

Definition Relapp' {ctx n} (r : Rel ctx (S n)) (e : expr) : Rel ctx n :=
  fun var =>
    ORapp (r var) (openupSingle e).

Global Instance Apply_Rel_expr ctx n : Apply (Rel ctx (S n)) expr (Rel ctx n) :=
  {
    apply := Relapp'
  }.

Fixpoint interp m (r : rel interp_arity m) : interp_arity m :=
  match r with
    | Rvar _ f => f
    | Rinj P => const_model P
    | Rand a b => fun n => interp a n /\ interp b n
    | Ror a b => fun n => interp a n \/ interp b n
    | Rimply a b => fun n => forall k, k <= n -> interp a k ->interp b k
    | Rforall1 _ g => fun n => forall x, interp (g x) n
    | Rexists1 _ g => fun n => exists x, interp (g x) n
    | Rforall2 _ g => fun n => forall r, interp (g r) n
    | Rexists2 _ g => fun n => exists r, interp (g r) n
    | Rabs _ g => fun e => interp (g e)
    | Rapp _ r e => interp r e
    | Rrecur _ g => _
  end.

Reserved Infix "==" (at level 70, no associativity).
Reserved Infix "|~" (at level 89, no associativity).

Section infer_rules.

  Open Scope Rel.

  Context `{ctx : varTs}.

  Inductive eqv : forall {n}, Rel ctx n -> Rel ctx n -> Prop :=
  | EVRefl n R : @eqv n R R
  | EVSymm n R1 R2 : @eqv n R1 R2 -> @eqv n R2 R1
  | EVTran n R1 R2 R3 : @eqv n R1 R2 -> @eqv n R2 R3 -> @eqv n R1 R3
  | EVLaterAnd P Q : eqv (▹ (P /\ Q)) (▹P /\ ▹Q)
  | EVLaterOr P Q : eqv (▹ (P \/ Q)) (▹P \/ ▹Q)
  | EVLaterImply P Q : eqv (▹ (P ===> Q)) (▹P ===> ▹Q)
  | EVLaterForall1 T P : eqv (▹ (∀x:T, P x)) (∀x, ▹(P x))
  | EVLaterExists1 T P : eqv (▹ (∃x:T, P x)) (∃x, ▹(P x))
  | EVLaterForallR (n : nat) P : eqv (fun var => ▹ (∀₂ (R : Funvar var ctx n), P var R))%OR (fun var => ∀₂ R, ▹(P var R))%OR
  | EVLaterExistsR (n : nat) P : eqv (fun var => ▹ (∃₂ (R : Funvar var ctx n), P var R))%OR (fun var => ∃₂ R, ▹(P var R))%OR
  | VElem n (R : Rel ctx (S n)) (e : Rel ctx TTexpr) : eqv ((\x, R $ x) $ e) (R $ e)
  | VRecur {n : nat} (R : Rel (TTrel n :: ctx) n) : eqv (fun var => @@r, R var (Rvar r))%OR (fun var => (@@r, R var (Rvar r)))%OR
  .

  Fixpoint Iff {n : nat} : Rel ctx n -> Rel ctx n -> Rel ctx 0 :=
    match n return Rel ctx n -> Rel ctx n -> Rel ctx 0 with
      | 0 => fun P1 P2 => P1 ===> P2 /\ P2 ===> P1
      | S n' => fun R1 R2 => ∀e : expr, Iff (R1 $ e) (R2 $ e)
    end.

  Infix "==" := Iff.

  Inductive valid : list (Rel ctx 0) -> Rel ctx 0 -> Prop :=
  | VEqv Ps P1 P2 : eqv P1 P2 -> Ps |~ P1 -> Ps |~ P2
  | VMono Ps P : Ps |~ P -> Ps |~ ▹P
  | VLob Ps P : ▹P :: Ps |~ P -> Ps |~ P
  | VReplace2 Ps {n : nat} R1 R2 (P : Rel (TTrel n :: ctx) 0) : Ps |~ R1 == R2 -> Ps |~ P $$ R1 -> Ps |~ P $$ R2
  where "Ps |~ P" := (valid Ps P)
  .

End infer_rules.

Infix "==" := Iff.
Infix "|~" := valid.

Definition openup9 {t1 t2 t3 t4 var} (f : t1 var -> t2 var -> t3 var -> t4 var) : forall {ctx}, Funvar var ctx t1 -> Funvar var ctx t2 -> Funvar var ctx t3 -> Funvar var ctx t4.
  refine
    (fix F ctx : Funvar var ctx t1 -> Funvar var ctx t2 -> Funvar var ctx t3 -> Funvar var ctx t4 :=
       match ctx return Funvar var ctx t1 -> Funvar var ctx t2 -> Funvar var ctx t3 -> Funvar var ctx t4 with
         | nil => _
         | nv :: ctx' => _
       end);
  simpl; eauto.
Defined.

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
    Lemma VMorePs ctx (P : Rel ctx 0) Ps : [] |~ P -> Ps |~ P.
      admit.
    Qed.
    eapply VMorePs.

    Lemma VCtxElimEmpty' t (P : Rel [t] 0) : [] |~ P -> forall ctx (x : Rel ctx t), [] |~ fun var => openup1 (P var) (x var).
    Proof.
      intros H.
      induction ctx.
      {
        simpl.
        intros x.
        admit.
      }
      {
        simpl in *.
        intros x.
        admit.
      }
    Qed.
    
    Lemma VCtxElim t ctx (P : Rel (t :: ctx) 0) : [] |~ P -> forall (x : Rel ctx t), [] |~ fun var => openup7 (P var) (x var).
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

    Lemma VCtxElimEmpty t (P : Rel [t] 0) : [] |~ P -> forall ctx (x : Rel ctx t), [] |~ fun var => openup1 (P var) (x var).
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

      Lemma extend_openup1 t (P : Rel [t] 0) ctx var (x : Funvar var ctx t) : openup7 (extend [t] ctx (P var)) x === openup1 (P var) x.
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
      Lemma VFunvarEq ctx (P Q : Rel ctx 0) Ps : (forall var, P var === Q var) -> Ps |~ P -> Ps |~ Q.
        admit.
      Qed.
      eapply VFunvarEq.
      {
        intros.
        eapply extend_openup1.
      }
      eapply VCtxElim.
      Lemma VExtend ctx (P : Rel ctx 0) : [] |~ P -> forall new, [] |~ (fun var => extend ctx new (P var)).
        admit.
      Qed.
      eapply VExtend with (P := P).
      eauto.
    Qed.
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
