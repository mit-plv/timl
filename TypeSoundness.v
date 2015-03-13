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

Notation typeR := nat (only parsing).
(*
Inductive typeR :=
| TRexpr
| TRrel (arity : nat)
.

Coercion TRrel : nat >-> typeR.
*)
Section propR.

  Variable var : typeR -> Type.
  
  Inductive propR : typeR -> Type :=
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
  | PRabs (n : nat) : (expr -> propR n) -> propR (S n)
  | PRapp (n : nat) : propR (S n) -> expr -> propR n
  | PRrecur (n : nat) : (var n -> propR n) -> propR n
  | PRlater : propR 0 -> propR 0
  .

End propR.

Notation "\ e , p" := (PRabs (fun e => p)) (at level 200, format "\ e , p").
Notation "⊤" := (PRtrue _).
Notation "⊥" := (PRtrue _).
Notation "⌈ P ⌉" := (PRlift _ P).
Notation "e ↓ τ" := (⌈ IsValue e /\ typingsim [] e τ ⌉) (at level 51).
Section TestNotations.
  
  Variable var : typeR -> Type.

  Definition ttt1 : propR var 1 := \e , ⊤.
  Definition ttt2 : propR var 1 := \e , e ↓ Tunit.

End TestNotations.

Inductive thresholds :=
| THleaf
| THarrow : thresholds -> csize -> thresholds
.

(* A "step-indexed" kriple model *)

Section LR.
  
  Variable var : typeR -> Type.

  Notation Tunit := (Tconstr TCunit).
  Notation "a × b" := 
    
  (* the logical relation *)
  Fixpoint V τ (ξ : csize) ρ (C : nat) (θ : thresholds) {struct τ} : propR var 1 :=
    match τ, ξ, θ with
      | Tvar α, _, _ => ρ α
      | Tunit, _, _ => \v, v ↓ τ
      | τ₁ × τ₂, Spair ξ₁ ξ₂, _ => \v, v ↓ ρ τ /\ ∃ a b, v = Epair a b /\ a ∈ V τ₁ ξ₁ ρ /\ b ∈ V τ₂ ξ₂ ρ
      (* | τ' + _, Sinl ξ, _ => \v, v ↓ ρ τ /\ ∃ v', v = Einl v' /\ v' ∈ V τ' ξ ρ *)
      (* | _ + τ', Sinr ξ, _ => \v, v ↓ ρ τ /\ ∃ v', v = Einr v' /\ v' ∈ V τ' ξ ρ *)
      (* | Tarrow τ₁ c s τ₂, _, THarrow θ₁ ξ₀ θ₂ => \v, v ↓ ρ τ /\ ∀ ξ₁ (v₁ ∈ V τ₁ ξ₁ ρ C θ), ξ₀ ≤ |v₁| ⇒ Eapp v v' ∈ E τ₂ c s (add ξ₁ ρ) C θ₂ *)
      (* | Tuniversal c s τ, _, _ => \v, v ↓ ρ τ /\ ∀ τ', ∀ S : VSet τ', Etapp v τ' ∈ E τ c s (add (τ', S) ρ) C θ *)
      (* | Trecur τ, Sfold ξ, _ => \μ S, \v, v ↓ ρ τ /\ ∃ v', v = Efold τ v' /\ ▹ (v' ∈ V τ ξ (add (ρ τ, S) ρ) C θ) *)
      | _, _, _ => \_, ⊥
    end
  (* with  *)
  (* E τ c s ρ C θ := *)
  (*   λ e : ρ τ, ∀ (v ∈ Val), ∀1 n, nsteps e n v ⇒ ⌈ natP (fun nc => n ≤ C * nc) (ρ c) ⌉ /\ ∃1 ξ, ξ ≤ ρ s /\ v ∈ V τ ξ ρ C θ *)
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
