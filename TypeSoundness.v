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

Notation "⊢" := typing.
Definition typingsim T e τ := exists c s, ⊢ T e τ c s.
Notation "|-" := typingsim.

Definition nostuck e := forall e', steps e e' -> IsValue e' \/ exists e'', step e' e''.

Theorem sound_wrt_nostuck :
  forall e τ,
    |- [] e τ ->
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

Infix "×" := Tprod (at level 40).
Infix "+" := Tsum.
Notation "e ↓ τ" := (IsValue e /\ |- [] e τ) (at level 51).

(* A Parametric Higher-Order Abstract Syntax (PHOAS) encoding for a second-order modal logic (LSLR) *)

Section rel.

  Variable var : nat -> Type.
  
  Inductive rel : nat -> Type :=
  | Rvar n : var n -> rel n
  | Rlift : Prop -> rel 0
  | Rtrue : rel 0
  | Rfalse : rel 0
  | Rand (_ _ : rel 0) : rel 0
  | Ror (_ _ : rel 0) : rel 0
  | Rimply (_ _ : rel 0) : rel 0
  | Rforalle : (expr -> rel 0) -> rel 0
  | Rexistse : (expr -> rel 0) -> rel 0
  | RforallR n : (var n -> rel 0) -> rel 0
  | RexistsR n : (var n -> rel 0) -> rel 0
  | Rforall1 T : (T -> rel 0) -> rel 0
  | Rexists1 T : (T -> rel 0) -> rel 0
  | Rabs n : (expr -> rel n) -> rel (S n)
  | Rapp n : rel (S n) -> expr -> rel n
  | Rrecur n : (var n -> rel n) -> rel n
  | Rlater : rel 0 -> rel 0
  .

End rel.

Section relOpen.

  Variable var : nat -> Type.
  
  Fixpoint relOpen R n :=
    match R with
      | nil => rel var n 
      | nv :: R' => var nv -> relOpen R' n
    end.

  Program Fixpoint liftToOpen R n1 n2 (f : rel var n1 -> rel var n2) (a : relOpen R n1) : relOpen R n2 :=
    match R with
      | nil => _
      | nv :: R' => _ (@liftToOpen R' n1 n2)
    end.
  Next Obligation.
    exact (f a).
  Defined.
  Next Obligation.
    exact (x f (a X)).
  Defined.

  Require Import Program.

  Program Fixpoint liftToOpen2 R n1 n2 T (f : (T -> rel var n1) -> rel var n2) (a : T -> relOpen R n1) : relOpen R n2 :=
    match R with
      | nil => _
      | nv :: R' => _ (@liftToOpen2 R' n1 n2)
    end.
  Next Obligation.
    exact (f a).
  Defined.
  Next Obligation.
    exact (x _ f (flip a X)).
  Defined.

  Program Fixpoint liftToOpen3 R n T (f : T -> rel var n) (a : T) : relOpen R n :=
    match R with
      | nil => _
      | nv :: R' => _ (@liftToOpen3 R' n)
    end.

  Program Fixpoint liftToOpen4 R n (f : rel var n) : relOpen R n :=
    match R with
      | nil => _
      | nv :: R' => _ (@liftToOpen4 R' n)
    end.

  Program Fixpoint liftToOpen5 R n1 n2 n3 (f : rel var n1 -> rel var n2 -> rel var n3) (a : relOpen R n1) (b : relOpen R n2) : relOpen R n3 :=
    match R with
      | nil => _
      | nv :: R' => _ (@liftToOpen5 R' n1 n2 n3)
    end.
  Next Obligation.
    exact (f a b).
  Defined.
  Next Obligation.
    exact (x f (a X) (b X)).
  Defined.

  Program Fixpoint liftToOpen6 R n1 T n2 (f : rel var n1 -> T -> rel var n2) (a : relOpen R n1) (b : T) : relOpen R n2 :=
    match R with
      | nil => _
      | nv :: R' => _ (@liftToOpen6 R' n1 T n2)
    end.
  Next Obligation.
    exact (f a b).
  Defined.
  Next Obligation.
    exact (x f (a X) b).
  Defined.

  Variable R : list nat.

  Definition ORvar n := liftToOpen3 R (@Rvar var n).
  Definition ORlift := liftToOpen3 R (@Rlift var).
  Definition ORtrue := liftToOpen4 R (@Rtrue var).
  Definition ORfalse := liftToOpen4 R (@Rfalse var).
  Definition ORand := liftToOpen5 R (@Rand var).
  Definition ORor := liftToOpen5 R (@Ror var).
  Definition ORimply := liftToOpen5 R (@Rimply var).
  Definition ORforalle := liftToOpen2 R (@Rforalle var).
  Definition ORexistse := liftToOpen2 R (@Rexistse var).
  Definition ORforallR n := liftToOpen2 R (@RforallR var n).
  Definition ORexistsR n := liftToOpen2 R (@RexistsR var n).
  Definition ORforall1 T := liftToOpen2 R (@Rforall1 var T).
  Definition ORexists1 T := liftToOpen2 R (@Rexists1 var T).
  Definition ORabs n := liftToOpen2 R (@Rabs var n).
  Definition ORapp n := liftToOpen6 R (@Rapp var n).
  Definition ORrecur n := liftToOpen2 R (@Rrecur var n).
  Definition ORlater := liftToOpen R (@Rlater var).

End relOpen.
    
Notation "⊤" := (ORtrue _ _).
Notation "⊥" := (ORtrue _ _).
Notation "⌈ P ⌉" := (ORlift _ _ P).
Arguments ORabs {var R n} _ .
Notation "\ x .. y , p" := (ORabs (fun x => .. (ORabs (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity).
Arguments ORforalle {var R} _ .
Notation "∀ x .. y , p" := (ORforalle (fun x => .. (ORforalle (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity).
Arguments ORexistse {var R} _ .
Notation "∃ x .. y , p" := (ORexistse (fun x => .. (ORexistse (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity).
Section TestNotations.
  
  Variable var : nat -> Type.
  Variable R : list nat.

  Definition ttt1 : relOpen var R 1 := \e , ⊤.
  Definition ttt2 : relOpen var R 1 := \e , ⌈e ↓ Tunit⌉.
  Definition ttt3 : relOpen var R 1 := \_ , ⌈True /\ True⌉.
  Definition ttt4 : relOpen var R 1 := \_ , ∀ e, ⌈e = Ett⌉.
  Definition ttt5 : relOpen var R 1 := \_ , ∃ e, ⌈e = Ett⌉.

End TestNotations.

Arguments ORforall1 {var R T} _ .
Notation "∀1 x .. y , p" := (ORforall1 (fun x => .. (ORforall1 (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity).
Arguments ORexists1 {var R T} _ .
Notation "∃1 x .. y , p" := (ORexists1 (fun x => .. (ORexists1 (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity).
Definition ORforallR' {var R n} P := (@ORforallR var R n (fun x => P (ORvar var R _ x))).
Notation "∀2 x .. y , p" := (ORforallR' (fun x => .. (ORforallR' (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity).
Definition ORexistsR' {var R n} P := (@ORexistsR var R n (fun x => P (ORvar var R _ x))).
Notation "∃2 x .. y , p" := (ORexistsR' (fun x => .. (ORexistsR' (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity).
Definition ORrecur' {var R n} P := (@ORrecur var R n (fun x => P (ORvar var R _ x))).
Notation "@ x .. y , p" := (ORrecur' (fun x => .. (ORrecur' (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity).
Arguments ORapp {var R n} _ _ .
Notation "e ∈ P" := (ORapp P e) (at level 70).
Arguments ORand {var R} _ _ .
Infix "/\" := ORand.
Arguments ORor {var R} _ _ .
Infix "\/" := ORor.
Arguments ORimply {var R} _ _ .
Infix "⇒" := ORimply (at level 90).
Arguments ORlater {var R} _ .
Notation "▹" := ORlater.
Definition VSet {var R} τ (S : relOpen var R 1) := ∀ v, v ∈ S ⇒ ⌈v ↓ τ⌉.

(*
Section inferRules.

  Variable var : nat -> Type.

  Variable R : list nat.

  Definition prop := openRel R 0.

  Fixpoint 

  Inductive valid : list prop -> prop -> Prop :=
  | Vmono C P : 
*)


(* An Logical Step-indexed Logical Relation (LSLR) for boundedness *)

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
  Variable R : list nat.

  Definition substs : Type.
    admit.
  Defined.

  Definition substs_type : substs -> type -> type.
    admit.
  Defined.

  Coercion substs_type : substs >-> Funclass.

  Definition substs_sem : substs -> nat -> relOpen var R 1.
    admit.
  Defined.

  Instance Apply_substs_nat_rel : Apply substs nat (relOpen var R 1) :=
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

  Definition add_pair : (type * relOpen var R 1) -> substs -> substs.
    admit.
  Defined.

  Instance Add_pair_substs : Add (type * relOpen var R 1) substs substs :=
    {
      add := add_pair
    }.

  Definition E' V τ (c : cexpr) (s : size) (ρ : substs) C (θ : thresholds) : relOpen var R 1 :=
    \e, ∀ v, ∀1 n, ⌈|- [] e (ρ τ) /\ ⇓ e n v⌉ ⇒ ⌈ ⌊ ñ | n ≤ C * ñ ⌋ (ρ $ c) ⌉ /\ ∃1 ξ : csize, ⌈ξ ≤ ρ $$ s⌉ /\ v ∈ V τ ξ ρ C θ.

  Fixpoint V τ (ξ : csize) (ρ : substs) (C : nat) (θ : thresholds) {struct τ} : relOpen var R 1 :=
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

Definition Rel n := forall var R, relOpen var R n.

Definition relV τ ξ ρ C θ : Rel 1 := fun var R => V var R τ ξ ρ C θ.
Definition relE τ c s ρ C θ : Rel 1 := fun var R => E var R τ c s ρ C θ.

Definition sound_wrt_bounded :=
  forall f τ₁ c s τ₂, 
    |- [] f (Tarrow τ₁ c s τ₂) -> 
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

Definition related Γ e τ c s :=
  (* ⊢ Γ e τ c s /\ *)
  exists X,
    wfVarCtx Γ X ->
    exists R,
      wfRelCtx Γ R ->
      
Lemma foundamental :
  forall Γ e τ c s,
    ⊢ Γ e τ c s -> 
    ⊩ Γ e τ c s.
Proof.
  admit.
Qed.

Theorem sound_wrt_bound_proof : sound_wrt_bounded.
Proof.
  admit.
Qed.

