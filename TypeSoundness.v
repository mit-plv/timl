(* Type soundness *)

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

Lemma sound_wrt_nostuck :
  forall e τ,
    typingsim [] e τ ->
    nostuck e.
Proof.
  admit.
Qed.

Definition value_of v τ := IsValue v /\ typingsim [] v τ.

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

Instance Le_csize : Le csize :=
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

Notation "| v |" := (get_size v) (at level 10).

(* An Logical Step-indexed Logical Relation (LSLR) for boundedness *)

(* A Parametric Higher-Order Abstract Syntax encoding *)

Inductive typeR :=
| TRexpr
| TRrel (arity : nat)
| TRother (T : Type)
.

Coercion TRrel : nat >-> typeR.

Section var.

  Variable var : typeR -> Type.
  
  Inductive PropR : typeR -> Type :=
  | Var t : var t -> PropR t
  | ConstExpr : expr -> 
  .

End var.

Fixpoint V τ ξ ρ C θ {struct τ} : PropR 1 :=
  match τ, ξ, θ with
    | Tvar α, _, _ => ρ α
    | Tunit, _, _ => λ v ↓ τ, ⊤
    | τ₁ × τ₂, Spair ξ₁ ξ₂, _ => λ v ↓ ρ τ, ∃ a b, v = Epair a b /\ a ∈ V τ₁ ξ₁ ρ /\ b ∈ V τ₂ ξ₂ ρ
    | τ' + _, Sinl ξ, _ => λ v ↓ ρ τ, ∃ v', v = Einl v' /\ v' ∈ V τ' ξ ρ
    | _ + τ', Sinr ξ, _ => λ v ↓ ρ τ, ∃ v', v = Einr v' /\ v' ∈ V τ' ξ ρ
    | Tarrow τ₁ c s τ₂, _, THarrow θ₁ ξ₀ θ₂ => λ v ↓ ρ τ, ∀ ξ₁ (v₁ ∈ V τ₁ ξ₁ ρ C θ), ξ₀ ≤ |v₁| ⇒ Eapp v v' ∈ E τ₂ c s (add ξ₁ ρ) C θ₂
    | Tuniversal c s τ, _, _ => λ v ↓ ρ τ, ∀ τ', ∀2 S : VSet τ', Etapp v τ' ∈ E τ c s (add (τ', S) ρ) C θ
    | Trecur τ, Sfold ξ, _ => μ S, λ v ↓ ρ τ, ∃ v', v = Efold τ v' /\ ▹ (v' ∈ V τ ξ (add (ρ τ, S) ρ) C θ)
    | _ _ _ => ⊥
  end
with 
E τ c s ρ C θ :=
  λ e : ρ τ, ∀ (v ∈ Val), ∀1 n, nsteps e n v ⇒ ⌈ natP (fun nc => n ≤ C * nc) (ρ c) ⌉ /\ ∃1 ξ, ξ ≤ ρ s /\ v ∈ V τ ξ ρ C θ
.

Definition bounded τ₁ e c (s : size) :=
  exists (C : nat) (ξ₀ : csize), 
    forall v₁,
      value_of v₁ τ₁ ->
      let ξ₁ := |v₁| in
      ξ₀ <= ξ₁ ->
      forall v n, 
        IsValue v -> 
        (* n is the actual running time *)
        nsteps (subst v₁ e) n v ->
        (* n is bounded *)
        (exists nc, nat_of_cexpr (subst ξ₁ c) = Some nc /\ n <= C * nc) 
.

Lemma sound_wrt_bounded :
  forall τ₁ e τ c s, 
    typing [TEtyping (τ₁, None)] e τ c s -> 
    bounded τ₁ e c s.
Proof.
  admit.
Qed.
