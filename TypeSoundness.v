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
Notation "|~" := typingsim.

Definition nostuck e := forall e', steps e e' -> IsValue e' \/ exists e'', step e' e''.

Theorem sound_wrt_nostuck :
  forall e τ,
    |~ [] e τ ->
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
Notation "e ↓ τ" := (IsValue e /\ |~ [] e τ) (at level 51).

Definition sound_wrt_bounded :=
  forall f τ₁ c s τ₂, 
    f ↓ Tarrow τ₁ c s τ₂ -> 
    (* ξ₀ is the threshold of input size in asymptotics *)
    exists (C : nat) (ξ₀ : csize), 
      forall v,
        v ↓ τ₁ ->
        let ξ := |v| in
        ξ₀ <= ξ ->
        exists n', 
          nat_of_cexpr (subst ξ c) = Some n' /\
          (* actual runing time is bounded by c(ξ) w.r.t. constant factor C *)
          ~ exists n e',
              nsteps (Eapp f v) n e' /\ n > C * n'.

(* A Parametric Higher-Order Abstract Syntax (PHOAS) encoding for a second-order modal logic (LSLR) *)

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

Module ClosedPHOAS.

Notation "⊤" := (Rtrue _).
Notation "⊥" := (Rtrue _).
(* Notation "\ e , p" := (Rabs (fun e => p)) (at level 200, format "\ e , p"). *)
Notation "\ x .. y , p" := (Rabs (fun x => .. (Rabs (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity).
Notation "∀ x .. y , p" := (Rforalle (fun x => .. (Rforalle (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity).
Notation "∃ x .. y , p" := (Rexistse (fun x => .. (Rexistse (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity).
Notation "∀1 x .. y , p" := (Rforall1 (fun x => .. (Rforall1 (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity).
Notation "∃1 x .. y , p" := (Rexists1 (fun x => .. (Rexists1 (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity).
Definition RforallR' var n P := (@RforallR var n (fun x => P (Rvar _ _ x))).
Notation "∀2 x .. y , p" := (RforallR' (fun x => .. (RforallR' (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity).
Definition RexistsR' var n P := (@RexistsR var n (fun x => P (Rvar _ _ x))).
Notation "∃2 x .. y , p" := (RexistsR' (fun x => .. (RexistsR' (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity).
Definition Rrecur' var n P := (@Rrecur var n (fun x => P (Rvar _ _ x))).
Notation "@ x .. y , p" := (Rrecur' (fun x => .. (Rrecur' (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity).
Notation "⌈ P ⌉" := (Rinj _ P).
Notation "e ∈ P" := (Rapp P e) (at level 70).
Infix "/\" := Rand.
Infix "\/" := Ror.
Infix "⇒" := Rimply (at level 90).
Notation "▹" := Rlater.
Definition VSet var τ (S : rel var 1) := ∀ v, v ∈ S ⇒ ⌈v ↓ τ⌉.

Section TestNotations.
  
  Variable var : nat -> Type.

  Definition ttt1 : rel var 1 := \e , ⊤.
  Definition ttt2 : rel var 1 := \e , ⌈e ↓ Tunit⌉.
  Definition ttt3 : rel var 1 := \_ , ⌈True /\ True⌉.

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

  Definition substs_sem : substs -> nat -> rel var 1.
    admit.
  Defined.

  Instance Apply_substs_nat_rel : Apply substs nat (rel var 1) :=
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

  Definition add_pair : (type * rel var 1) -> substs -> substs.
    admit.
  Defined.

  Instance Add_pair_substs : Add (type * rel var 1) substs substs :=
    {
      add := add_pair
    }.

  Inductive stepex : expr -> bool -> expr -> Prop :=
  | STecontext c e1 b e2 : stepex e1 b e2 -> stepex (plug c e1) b (plug c e2)
  | STapp t body arg : IsValue arg -> stepex (Eapp (Eabs t body) arg) false (subst arg body)
  | STlet t v main : IsValue v -> stepex (Elet t v main) false (subst v main)
  | STmatch_pair ta tb a b k : 
      IsValue a ->
      IsValue b ->
      stepex (Ematch_pair (Epair $$ ta $$ tb $$ a $$ b) k) false (subst_list [a; b] k)
  | STmatch_inl ta tb v k1 k2 : 
      IsValue v ->
      stepex (Ematch_sum (Einl $$ ta $$ tb $$ v) k1 k2) false (subst v k1)
  | STmatch_inr ta tb v k1 k2 : 
      IsValue v ->
      stepex (Ematch_sum (Einr $$ ta $$ tb $$ v) k1 k2) false (subst v k2)
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

  Program Fixpoint E' V τ (n : nat) (s : size) (ρ : substs) (C : nat) (θ : thresholds) {measure n} : rel var 1 :=
    \e, ⌈|~ [] e (ρ τ)⌉ /\ 
        ∀1 n', ∀ e', 
          (⌈nstepsex e n' 0 e'⌉ ⇒ ⌈n' ≤ n⌉ /\ (⌈IsValue e'⌉ ⇒ e' ∈ V τ ρ C θ /\ ⌈|e'| ≤ s⌉)) /\
          match n with
            | 0 => ⊤
            | S _ =>
              (⌈nstepsex e (S n') 1 e'⌉ ⇒ ⌈(S n') ≤ n⌉ /\ ▹ (e' ∈ E' V τ (n - S n') s ρ C θ))
          end.
  Next Obligation.
    omega.
  Defined.

  Fixpoint V τ (ρ : substs) (C : nat) (θ : thresholds) {struct τ} : rel var 1 :=
    match τ, θ with
      | Tvar α, _ => ρ $ α
      | Tunit, _ => \v, ⌈v ↓ τ⌉
      | τ₁ × τ₂, _ => \v, ⌈v ↓ ρ τ⌉ /\ ∃ a b, ⌈v = Epair a b⌉ /\ a ∈ V τ₁ ρ C θ /\ b ∈ V τ₂ ρ C θ
      | τ₁ + τ₂, _ => \v, ⌈v ↓ ρ τ⌉ /\ ∃ v', (⌈v = Einl τ₂ v'⌉ /\ v' ∈ V τ₁ ρ C θ) ‌\/ ⌈v = Einr τ₁ v'⌉ /\ v' ∈ V τ₂ ρ C θ
      | Tarrow τ₁ c s τ₂, _, THarrow θ₁ ξ₀ θ₂ => \v, ⌈v ↓ ρ τ⌉ /\ ∀ v₁, v₁ ∈ V τ₁ ρ C θ /\ ⌈ξ₀ ≤ |v₁|⌉ ⇒ Eapp v v₁ ∈ E' V τ₂ c s (add ξ₁ ρ) C θ₂
      | Tuniversal c s τ, _ => \v, ⌈v ↓ ρ τ⌉ /\ ∀1 τ', ∀2 S, VSet τ' S ⇒ Etapp v τ' ∈ E' V τ c s (add (τ', S) ρ) C θ
      | Trecur τ, _ => @S, \v, ⌈v ↓ ρ τ⌉ /\ ∃ v', ⌈v = Efold τ v'⌉ /\ ▹ (v' ∈ V τ (add (ρ τ, S) ρ) C θ)
      | _, _, _ => \_, ⊥
    end
  .

  Definition E := E' V.

End LR.

End ClosedPHOAS.

Module OpenPHOAS.

Section relOpen.

  Variable var : nat -> Type.
  
  Inductive termType :=
    | TTrel (arity : nat)
    | TTexpr
    | TTother (T : Type)
  .

  Coercion TTrel : nat >-> termType.

  Definition interp t :=
    match t with
      | TTrel n => rel var n
      | TTexpr => expr
      | TTother T => T
    end.

  Definition Ctx := list termType.

  Fixpoint relOpen C range :=
    match C with
      | nil => interp range
      | domain :: C' => interp domain -> relOpen C' range
    end.

  Program Fixpoint liftToOpen C n1 n2 (f : rel var n1 -> rel var n2) (a : relOpen C n1) : relOpen C n2 :=
    match C with
      | nil => _
      | nv :: C' => _ (@liftToOpen C' n1 n2)
    end.
  Next Obligation.
    exact (f a).
  Defined.
  Next Obligation.
    exact (x f (a X)).
  Defined.

  Require Import Program.

  Program Fixpoint liftToOpen2 C n1 n2 T (f : (T -> rel var n1) -> rel var n2) (a : T -> relOpen C n1) : relOpen C n2 :=
    match C with
      | nil => _
      | nv :: C' => _ (@liftToOpen2 C' n1 n2)
    end.
  Next Obligation.
    exact (f a).
  Defined.
  Next Obligation.
    exact (x _ f (flip a X)).
  Defined.

  Program Fixpoint liftToOpen3 C n T (f : T -> rel var n) (a : T) : relOpen C n :=
    match C with
      | nil => _
      | nv :: C' => _ (@liftToOpen3 C' n)
    end.

  Program Fixpoint liftToOpen4 C n (f : rel var n) : relOpen C n :=
    match C with
      | nil => _
      | nv :: C' => _ (@liftToOpen4 C' n)
    end.

  Program Fixpoint liftToOpen5 C n1 n2 n3 (f : rel var n1 -> rel var n2 -> rel var n3) (a : relOpen C n1) (b : relOpen C n2) : relOpen C n3 :=
    match C with
      | nil => _
      | nv :: C' => _ (@liftToOpen5 C' n1 n2 n3)
    end.
  Next Obligation.
    exact (f a b).
  Defined.
  Next Obligation.
    exact (x f (a X) (b X)).
  Defined.

  Program Fixpoint liftToOpen6 C n1 T n2 (f : rel var n1 -> T -> rel var n2) (a : relOpen C n1) (b : T) : relOpen C n2 :=
    match C with
      | nil => _
      | nv :: C' => _ (@liftToOpen6 C' n1 T n2)
    end.
  Next Obligation.
    exact (f a b).
  Defined.
  Next Obligation.
    exact (x f (a X) b).
  Defined.

  Variable C : Ctx.

  Definition ORvar n := liftToOpen3 C (@Rvar var n).
  Definition ORinj := liftToOpen3 C (@Rinj var).
  Definition ORtrue := liftToOpen4 C (@Rtrue var).
  Definition ORfalse := liftToOpen4 C (@Rfalse var).
  Definition ORand := liftToOpen5 C (@Rand var).
  Definition ORor := liftToOpen5 C (@Ror var).
  Definition ORimply := liftToOpen5 C (@Rimply var).
  Definition ORforalle := liftToOpen2 C (@Rforalle var).
  Definition ORexistse := liftToOpen2 C (@Rexistse var).
  Definition ORforallR n := liftToOpen2 C (@RforallR var n).
  Definition ORexistsR n := liftToOpen2 C (@RexistsR var n).
  Definition ORforall1 T := liftToOpen2 C (@Rforall1 var T).
  Definition ORexists1 T := liftToOpen2 C (@Rexists1 var T).
  Definition ORabs n := liftToOpen2 C (@Rabs var n).
  Definition ORapp n := liftToOpen6 C (@Rapp var n).
  Definition ORrecur n := liftToOpen2 C (@Rrecur var n).
  Definition ORlater := liftToOpen C (@Rlater var).

End relOpen.
    
Notation "⊤" := (ORtrue _ _).
Notation "⊥" := (ORtrue _ _).
Notation "⌈ P ⌉" := (ORinj _ _ P).
Arguments ORabs {var C n} _ .
Notation "\ x .. y , p" := (ORabs (fun x => .. (ORabs (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity).
Arguments ORforalle {var C} _ .
Notation "∀ x .. y , p" := (ORforalle (fun x => .. (ORforalle (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity).
Arguments ORexistse {var C} _ .
Notation "∃ x .. y , p" := (ORexistse (fun x => .. (ORexistse (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity).
Arguments ORforall1 {var C T} _ .
Notation "∀1 x .. y , p" := (ORforall1 (fun x => .. (ORforall1 (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity).
Arguments ORexists1 {var C T} _ .
Notation "∃1 x .. y , p" := (ORexists1 (fun x => .. (ORexists1 (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity).
Definition ORforallR' {var C n} P := (@ORforallR var C n (fun x => P (ORvar var C _ x))).
Notation "∀2 x .. y , p" := (ORforallR' (fun x => .. (ORforallR' (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity).
Definition ORexistsR' {var C n} P := (@ORexistsR var C n (fun x => P (ORvar var C _ x))).
Notation "∃2 x .. y , p" := (ORexistsR' (fun x => .. (ORexistsR' (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity).
Definition ORrecur' {var C n} P := (@ORrecur var C n (fun x => P (ORvar var C _ x))).
Notation "@ x .. y , p" := (ORrecur' (fun x => .. (ORrecur' (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity).
Arguments ORapp {var C n} _ _ .
Notation "e ∈ P" := (ORapp P e) (at level 70).
Arguments ORand {var C} _ _ .
Infix "/\" := ORand.
Arguments ORor {var C} _ _ .
Infix "\/" := ORor.
Arguments ORimply {var C} _ _ .
Infix "⇒" := ORimply (at level 90).
Arguments ORlater {var C} _ .
Notation "▹" := ORlater.
Definition VSet {var C} τ (S : relOpen var C 1) := ∀ v, v ∈ S ⇒ ⌈v ↓ τ⌉.

Section TestNotations.
  
  Variable var : nat -> Type.
  Variable C : Ctx.

  Definition ttt1 : relOpen var C 1 := \e , ⊤.
  Definition ttt2 : relOpen var C 1 := \e , ⌈e ↓ Tunit⌉.
  Definition ttt3 : relOpen var C 1 := \_ , ⌈True /\ True⌉.
  Definition ttt4 : relOpen var C 1 := \_ , ∀ e, ⌈e = Ett⌉.
  Definition ttt5 : relOpen var C 1 := \_ , ∃ e, ⌈e = Ett⌉.

End TestNotations.

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
  Variable C : Ctx.

  Inductive SubstEntry :=
  | SEtype (_ : relOpen var C (TTother type)) (_ : option (relOpen var C 1))
  | SEexpr (_ : relOpen var C TTexpr) (_ : relOpen var C (TTother csize))
  .

  Definition substs : Type := list SubstEntry.

  Definition substs_type : substs -> type -> type.
    admit.
  Defined.

  Coercion substs_type : substs >-> Funclass.

  Definition substs_sem : substs -> nat -> relOpen var C 1.
    admit.
  Defined.

  Instance Apply_substs_nat_rel : Apply substs nat (relOpen var C 1) :=
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

  Definition add_pair : (type * relOpen var C 1) -> substs -> substs.
    admit.
  Defined.

  Instance Add_pair_substs : Add (type * relOpen var C 1) substs substs :=
    {
      add := add_pair
    }.

  Definition E' V τ (c : cexpr) (s : size) (ρ : substs) Ct (θ : thresholds) : relOpen var C 1 :=
    \e, ∀ v, ∀1 n, ⌈|~ [] e (ρ τ) /\ ⇓ e n v⌉ ⇒ ⌈ ⌊ ñ | n ≤ Ct * ñ ⌋ (ρ $ c) ⌉ /\ ∃1 ξ : csize, ⌈ξ ≤ ρ $$ s⌉ /\ v ∈ V τ ξ ρ Ct θ.

  Fixpoint V τ (ξ : csize) (ρ : substs) (Ct : nat) (θ : thresholds) {struct τ} : relOpen var C 1 :=
    match τ, ξ, θ with
      | Tvar α, _, _ => ρ $ α
      | Tunit, _, _ => \v, ⌈v ↓ τ⌉
      | τ₁ × τ₂, CSpair ξ₁ ξ₂, _ => \v, ⌈v ↓ ρ τ⌉ /\ ∃ a b, ⌈v = Epair a b⌉ /\ a ∈ V τ₁ ξ₁ ρ Ct θ /\ b ∈ V τ₂ ξ₂ ρ Ct θ
      | τ₁ + τ₂, CSinl ξ, _ => \v, ⌈v ↓ ρ τ⌉ /\ ∃ v', ⌈v = Einl τ₂ v'⌉ /\ v' ∈ V τ₁ ξ ρ Ct θ
      | τ₁ + τ₂, CSinr ξ, _ => \v, ⌈v ↓ ρ τ⌉ /\ ∃ v', ⌈v = Einr τ₁ v'⌉ /\ v' ∈ V τ₂ ξ ρ Ct θ
      | Tarrow τ₁ c s τ₂, _, THarrow θ₁ ξ₀ θ₂ => \v, ⌈v ↓ ρ τ⌉ /\ ∀1 ξ₁, ∀ v₁, v₁ ∈ V τ₁ ξ₁ ρ Ct θ /\ ⌈ξ₀ ≤ |v₁|⌉ ⇒ Eapp v v₁ ∈ E' V τ₂ c s (add ξ₁ ρ) Ct θ₂
      | Tuniversal c s τ, _, _ => \v, ⌈v ↓ ρ τ⌉ /\ ∀1 τ', ∀2 S, VSet τ' S ⇒ Etapp v τ' ∈ E' V τ c s (add (τ', S) ρ) Ct θ
      | Trecur τ, CSfold ξ, _ => @S, \v, ⌈v ↓ ρ τ⌉ /\ ∃ v', ⌈v = Efold τ v'⌉ /\ ▹ (v' ∈ V τ ξ (add (ρ τ, S) ρ) Ct θ)
      | _, _, _ => \_, ⊥
    end
  .

  Definition E := E' V.

End LR.

End OpenPHOAS.

Import OpenPHOAS.

Definition valid (X : list bool) {var} C (ctxP : list (relOpen var C 0)) (P : relOpen var C 0) : Prop.
  admit.
Defined.
Notation "|- X C ctxP P" := (valid X C ctxP P) (at level 90).

Definition add_var t ctx Ps ρ :=
  let ctx := t :: ctx in 
  let Ps := lift t Ps in
  let ρ := lift t ρ in
  (ctx, Ps, ρ).

Definition add_type k :=
  let Pack ctx0 Ps ρ := C in
  let (ctx, Ps, ρ) := add_var TTtype ctx0 Ps ρ in
  let Ps := extend ctx0 (fun τ => kinding [] τ k) :: Ps in
  match k with
    | KDstar => 
      let (ctx, Ps, ρ) := add_var (TTrel 1) ctx Ps ρ in
      let Ps := extend ctx0 (fun τ S => VSet τ S) :: Ps in
      let ρ := SEtype #1 (Some #0) :: ρ in
      Pack ctx Ps ρ
    | _ =>
      let ρ := SEtype #1 None :: ρ in
      Pack ctx Ps ρ
  end.

Definition add_expr τ θ os :=
  let Pack ctx0 Ps ρ := C in
  let (ctx, Ps, ρ) := add_var TTexpr ctx0 Ps ρ in
  let Ps := #0 ∈ V τ ρ Ct θ :: Ps in
  let (ctx, Ps, ρ) := add_var (TTother csize) ctx0 Ps ρ in
  let ρ := SEexpr #1 #0 :: ρ in
  match os with
    | inl ξ₀ =>
      let Ps := extend ctx0 (fun v ξ => ξ₀ ≤ |v| ? ξ = |v| : ξ = ξ₀) C :: Ps in
      Pack ctx Ps ρ
    | inr s =>
      let Ps := extend (TTexpr :: ctx0) (fun ξ => asCsize (fun ξs => ξ = ξs) (ρ $$ s)) in
      Pack ctx Ps ρ
  end.

Fixpoint makeC Γ :=
  match Γ with
    | nil => (nil, nil)
    | e : Γ =>
      let C := makeC Γ in
      match e with
        | TEkinging k =>
          add_type k C
        | TEtyping (τ, θ, os) =>
          add_expr τ θ os C
      end
  end.

Definition related Γ e τ c s :=
  exists C ξs θs θ Γ',
    extendΓ Γ ξs θs = Some Γ' /\
    let (C, ρ) := makeC Γ' in
    C |- (ρ $ e) ∈ E τ (C * c) s ρ C θ
    (* ⊢ Γ e τ c s /\ *)
    let X := map () Γ in
    let C := map () Γ in
    let ρ := map () Γ in
    let ctxP := map () Γ in
    |- X C ctxP (e ∈ E c s ρ C θ)
      
(*
Section inferRules.

  Variable var : nat -> Type.

  Variable C : list nat.

  Reserved Notation "C |- P" (at level 90).
  
  Inductive valid : list (relOpen var C 0) -> relOpen var C 0 -> Prop :=
  | RuleMono C P : C |- P -> C |- ▹P
  | RuleLob C P : ▹P :: C |- P -> C |- P
  | RuleLaterAnd1 C P Q : C |- ▹ (P /\ Q) -> C |- ▹P /\ ▹Q
  | RuleLaterAnd2 C P Q : C |- ▹P /\ ▹Q -> C |- ▹ (P /\ Q)
  | RuleElem1 C P e : C |- e ∈ ORabs P -> C |- P e
  | RuleElem2 C P e : C |- P e -> C |- e ∈ ORabs P
  where "C |- P" := (valid C P)
  .

End inferRules.
*)

Definition Rel n := forall var C, relOpen var C n.

Definition relV τ ξ ρ C θ : Rel 1 := fun var C => V var C τ ξ ρ C θ.
Definition relE τ c s ρ C θ : Rel 1 := fun var C => E var C τ c s ρ C θ.

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

