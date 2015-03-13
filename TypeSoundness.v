(* Type soundness *)

Set Implicit Arguments.

Require Import List.
Require Import Typing EvalCBV.

Import ListNotations.
Local Open Scope list_scope.

(* encoding of fix by recursive-type :
     fix f(x).e := \y. (unfold v) v y 
        where v := fold (\z. (\f. \x. e) (\y. (unfold z) z y)) 
                    (for y,z\not\in FV(e))
 *)

Inductive steps : expr -> expr -> Prop :=
| Steps0 e : steps e e
| StepsS e1 e2 e3 : step e1 e2 -> steps e2 e3 -> steps e1 e3
.

Definition typingsim T e τ := exists c s, typing T e τ c s.

Definition nostuck e := forall e', steps e e' -> IsValue e' \/ exists e'', step e' e''.

Theorem sound_wrt_nostuck :
  forall e τ,
    typingsim [] e τ ->
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

Definition leCS : csize -> csize -> Prop.
  admit.
Defined.

Instance Le_csize : Le csize csize :=
  {
    le := leCS
  }.

Definition get_size (e : expr) : csize.
  admit.
Defined.

Definition nat_of_cexpr (c : cexpr) : option nat.
  admit.
Defined.

Definition csize_to_size (ξ : csize) : size.
  admit.
Defined.

Coercion csize_to_size : csize >-> size.

Instance Subst_csize_cexpr : Subst csize cexpr :=
  {
    substn n v b := substn n (v : size) b
  }.

Instance Subst_csize_size : Subst csize size :=
  {
    substn n v b := substn n (v : size) b
  }.

Definition le_csize_size : csize -> size -> Prop.
  admit.
Defined.

Instance Le_cszie_size : Le csize size :=
  {
    le := le_csize_size
  }.

Notation "| v |" := (get_size v) (at level 10).
Infix "≤" := le (at level 70).

Definition terminatesWith e n v := (nsteps e n v /\ IsValue v)%type.
Notation "⇓" := terminatesWith.

Definition asNat P c :=
  (exists nc, nat_of_cexpr c = Some nc /\ P nc)%type.
Notation "⌊ n | P ⌋" := (asNat (fun n => P)).

(* An Logical Step-indexed Logical Relation (LSLR) for boundedness *)

(* A Parametric Higher-Order Abstract Syntax encoding *)

Section propR.

  Variable var : nat -> Type.
  
  Inductive propR : nat -> Type :=
  | PRvar t : var t -> propR t
  | PRlift : Prop -> propR 0
  | PRtrue : propR 0
  | PRfalse : propR 0
  | PRand (_ _ : propR 0) : propR 0
  | PRor (_ _ : propR 0) : propR 0
  | PRimply (_ _ : propR 0) : propR 0
  | PRforalle : (expr -> propR 0) -> propR 0
  | PRexistse : (expr -> propR 0) -> propR 0
  | PRforallR n : (var n -> propR 0) -> propR 0
  | PRexistsR n : (var n -> propR 0) -> propR 0
  | PRforall1 T : (T -> propR 0) -> propR 0
  | PRexists1 T : (T -> propR 0) -> propR 0
  | PRabs n : (expr -> propR n) -> propR (S n)
  | PRapp n : propR (S n) -> expr -> propR n
  | PRrecur n : (var n -> propR n) -> propR n
  | PRlater : propR 0 -> propR 0
  .

End propR.

Definition PropR n := forall var, propR var n.

Infix "×" := Tprod (at level 40).
Infix "+" := Tsum.
Notation "⊢" := typingsim.

Notation "⊤" := (PRtrue _).
Notation "⊥" := (PRtrue _).
(* Notation "\ e , p" := (PRabs (fun e => p)) (at level 200, format "\ e , p"). *)
Notation "\ x .. y , p" := (PRabs (fun x => .. (PRabs (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity).
Notation "∀ x .. y , p" := (PRforalle (fun x => .. (PRforalle (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity).
Notation "∃ x .. y , p" := (PRexistse (fun x => .. (PRexistse (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity).
Notation "∀1 x .. y , p" := (PRforall1 (fun x => .. (PRforall1 (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity).
Notation "∃1 x .. y , p" := (PRexists1 (fun x => .. (PRexists1 (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity).
Definition PRforallR' var n P := (@PRforallR var n (fun x => P (PRvar _ _ x))).
Notation "∀2 x .. y , p" := (PRforallR' (fun x => .. (PRforallR' (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity).
Definition PRexistsR' var n P := (@PRexistsR var n (fun x => P (PRvar _ _ x))).
Notation "∃2 x .. y , p" := (PRexistsR' (fun x => .. (PRexistsR' (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity).
Definition PRrecur' var n P := (@PRrecur var n (fun x => P (PRvar _ _ x))).
Notation "@ x .. y , p" := (PRrecur' (fun x => .. (PRrecur' (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity).
Notation "⌈ P ⌉" := (PRlift _ P).
Notation "e ↓ τ" := (IsValue e /\ ⊢ [] e τ) (at level 51).
Notation "e ∈ P" := (PRapp P e) (at level 70).
Infix "/\" := PRand.
Infix "\/" := PRor.
Infix "⇒" := PRimply (at level 90).
Notation "▹" := PRlater.
Definition VSet var τ (S : propR var 1) := ∀ v, v ∈ S ⇒ ⌈v ↓ τ⌉.

Section TestNotations.
  
  Variable var : nat -> Type.

  Definition ttt1 : propR var 1 := \e , ⊤.
  Definition ttt2 : propR var 1 := \e , ⌈e ↓ Tunit⌉.
  Definition ttt3 : propR var 1 := \_ , ⌈True /\ True⌉.

End TestNotations.

Inductive thresholds :=
| THleaf
| THarrow : thresholds -> csize -> thresholds -> thresholds
.

Require Import Util.
Local Open Scope prog_scope.

(* A "step-indexed" kriple model *)

(* the logical relation *)
Section LR.
  
  Variable var : nat -> Type.

  Definition substs : Type.
    admit.
  Defined.

  Definition substs_type : substs -> type -> type.
    admit.
  Defined.

  Coercion substs_type : substs >-> Funclass.

  Definition substs_sem : substs -> nat -> propR var 1.
    admit.
  Defined.

  Instance Apply_substs_nat_propR : Apply substs nat (propR var 1) :=
    {
      apply := substs_sem
    }.

  Definition substs_cexpr : substs -> cexpr -> cexpr.
    admit.
  Defined.

  Instance Apply_substs_cexpr_cexpr : Apply substs cexpr cexpr :=
    {
      apply := substs_cexpr
    }.

  Definition substs_size : substs -> size -> size.
    admit.
  Defined.

  Instance Apply_substs_size_size : Apply substs size size :=
    {
      apply := substs_size
    }.

  Definition add_csize : csize -> substs -> substs.
    admit.
  Defined.

  Instance Add_csize_substs : Add csize substs substs :=
    {
      add := add_csize
    }.

  Definition add_pair : (type * propR var 1) -> substs -> substs.
    admit.
  Defined.

  Instance Add_pair_substs : Add (type * propR var 1) substs substs :=
    {
      add := add_pair
    }.

  Definition E' V τ (c : cexpr) (s : size) (ρ : substs) C (θ : thresholds) : propR var 1 :=
    \e, ∀ v, ∀1 n, ⌈⊢ [] e (ρ τ) /\ ⇓ e n v⌉ ⇒ ⌈ ⌊ ñ | n ≤ C * ñ ⌋ (ρ $ c) ⌉ /\ ∃1 ξ : csize, ⌈ξ ≤ ρ $$ s⌉ /\ v ∈ V τ ξ ρ C θ.

  Fixpoint V τ (ξ : csize) (ρ : substs) (C : nat) (θ : thresholds) {struct τ} : propR var 1 :=
    match τ, ξ, θ with
      | Tvar α, _, _ => ρ $ α
      | Tunit, _, _ => \v, ⌈v ↓ τ⌉
      | τ₁ × τ₂, CSpair ξ₁ ξ₂, _ => \v, ⌈v ↓ ρ τ⌉ /\ ∃ a b, ⌈v = Epair a b⌉ /\ a ∈ V τ₁ ξ₁ ρ C θ /\ b ∈ V τ₂ ξ₂ ρ C θ
      | τ₁ + τ₂, CSinl ξ, _ => \v, ⌈v ↓ ρ τ⌉ /\ ∃ v', ⌈v = Einl τ₂ v'⌉ /\ v' ∈ V τ₁ ξ ρ C θ
      | τ₁ + τ₂, CSinr ξ, _ => \v, ⌈v ↓ ρ τ⌉ /\ ∃ v', ⌈v = Einr τ₁ v'⌉ /\ v' ∈ V τ₂ ξ ρ C θ
      | Tarrow τ₁ c s τ₂, _, THarrow θ₁ ξ₀ θ₂ => \v, ⌈v ↓ ρ τ⌉ /\ ∀1 ξ₁, ∀ v₁, v₁ ∈ V τ₁ ξ₁ ρ C θ /\ ⌈ξ₀ ≤ |v₁|⌉ ⇒ Eapp v v₁ ∈ E' V τ₂ c s (add ξ₁ ρ) C θ₂
      | Tuniversal c s τ, _, _ => \v, ⌈v ↓ ρ τ⌉ /\ ∀1 τ', ∀2 S, VSet τ' S ⇒ Etapp v τ' ∈ E' V τ c s (add (τ', S) ρ) C θ
      | Trecur τ, CSfold ξ, _ => @S, \v, ⌈v ↓ ρ τ⌉ /\ ∃ v', ⌈v = Efold τ v'⌉ /\ ▹ (v' ∈ V τ ξ (add (ρ τ, S) ρ) C θ)
      | _, _, _ => \_, ⊥
    end
  .

  Definition E := E' V.

End LR.

Definition relV τ ξ ρ C θ : PropR 1 := fun var => V var τ ξ ρ C θ.
Definition relE τ c s ρ C θ : PropR 1 := fun var => E var τ c s ρ C θ.

Theorem sound_wrt_bounded :
  forall f τ₁ c s τ₂, 
    ⊢ [] f (Tarrow τ₁ c s τ₂) -> 
    exists (C : nat) (ξ₀ : csize), 
      (* ξ₀ is the threshold of input size in asymptotics *)
      forall v,
        v ↓ τ₁ ->
        let ξ := |v| in
        ξ₀ <= ξ ->
        forall v' n, 
          (* n is the actual running time *)
          ⇓ (Eapp f v) n v' ->
          (* n is bounded by c(ξ) w.r.t. constant factor C *)
          ⌊ ñ | n <= C * ñ ⌋ (subst ξ c).
Proof.
  admit.
Qed.
