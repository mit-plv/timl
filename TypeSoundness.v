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

Require Import Util.
Local Open Scope prog_scope.

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

Class Leb A B :=
  {
    leb : A -> B -> bool
  }.

Infix "<=?" := leb (at level 70).

Definition lebCS : csize -> csize -> bool.
  admit.
Defined.

Instance Leb_csize_csize : Leb csize csize :=
  {
    leb := lebCS
  }.

Definition cexpr_to_nat (c : cexpr) := default 0 (nat_of_cexpr c).

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

  Program Fixpoint liftToOpen C {n1 n2} (f : rel var n1 -> rel var n2) (a : relOpen C n1) : relOpen C n2 :=
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

  Program Fixpoint liftToOpen2 C {n1 n2 T} (f : (T -> rel var n1) -> rel var n2) (a : T -> relOpen C n1) : relOpen C n2 :=
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

  Program Fixpoint liftToOpen3 C {n T} (f : T -> rel var n) (a : T) : relOpen C n :=
    match C with
      | nil => _
      | nv :: C' => _ (@liftToOpen3 C' n)
    end.

  Program Fixpoint liftToOpen4 C {n} (f : rel var n) : relOpen C n :=
    match C with
      | nil => _
      | nv :: C' => _ (@liftToOpen4 C' n)
    end.

  Program Fixpoint liftToOpen5 C {n1 n2 n3} (f : rel var n1 -> rel var n2 -> rel var n3) (a : relOpen C n1) (b : relOpen C n2) : relOpen C n3 :=
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

  Program Fixpoint liftToOpen6 C {n1 T n2} (f : rel var n1 -> T -> rel var n2) (a : relOpen C n1) (b : T) : relOpen C n2 :=
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
  Variable ctx : Ctx.

  Inductive SubstEntry :=
  | SEtype (_ : relOpen var ctx (TTother type)) (_ : option (relOpen var ctx 1))
  | SEexpr (_ : relOpen var ctx TTexpr) (_ : relOpen var ctx (TTother csize))
  .

  Definition substs : Type := list SubstEntry.

  Definition substs_type : substs -> type -> type.
    admit.
  Defined.

  Coercion substs_type : substs >-> Funclass.

  Definition substs_sem : substs -> nat -> relOpen var ctx 1.
    admit.
  Defined.

  Instance Apply_substs_nat_rel : Apply substs nat (relOpen var ctx 1) :=
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

  Definition substs_expr : substs -> expr -> expr.
    admit.
  Defined.

  Instance Apply_substs_expr_expr : Apply substs expr expr :=
    {
      apply := substs_expr
    }.

  Definition add_csize : csize -> substs -> substs.
    admit.
  Defined.

  Instance Add_csize_substs : Add csize substs substs :=
    {
      add := add_csize
    }.

  Definition add_pair : (type * relOpen var ctx 1) -> substs -> substs.
    admit.
  Defined.

  Instance Add_pair_substs : Add (type * relOpen var ctx 1) substs substs :=
    {
      add := add_pair
    }.

  Program Fixpoint E' V τ (n : nat) (s : size) (ρ : substs) (Ct : nat) (θ : thresholds) {measure n} : relOpen var ctx 1 :=
    \e, ⌈|~ [] e (ρ τ)⌉ /\ 
        ∀1 n', ∀ e', 
          (⌈nstepsex e n' 0 e'⌉ ⇒ ⌈n' ≤ n⌉ /\ (⌈IsValue e'⌉ ⇒ e' ∈ V ρ Ct θ /\ ⌈|e'| ≤ s⌉)) /\
          match n with
            | 0 => ⊤
            | S _ =>
              (⌈nstepsex e (S n') 1 e'⌉ ⇒ ⌈(S n') ≤ n⌉ /\ ▹ (e' ∈ E' V τ (n - S n') s ρ Ct θ))
          end.
  Next Obligation.
    omega.
  Defined.

  Fixpoint V τ (ρ : substs) (Ct : nat) (θ : thresholds) {struct τ} : relOpen var ctx 1 :=
    match τ, θ with
      | Tvar α, _ => ρ $ α
      | Tunit, _ => \v, ⌈v ↓ τ⌉
      | τ₁ × τ₂, _ => \v, ⌈v ↓ ρ τ⌉ /\ ∃ a b, ⌈v = Epair a b⌉ /\ a ∈ V τ₁ ρ Ct θ /\ b ∈ V τ₂ ρ Ct θ
      | τ₁ + τ₂, _ => \v, ⌈v ↓ ρ τ⌉ /\ ∃ v', (⌈v = Einl τ₂ v'⌉ /\ v' ∈ V τ₁ ρ Ct θ) /\ ⌈v = Einr τ₁ v'⌉ /\ v' ∈ V τ₂ ρ Ct θ
      | Tarrow τ₁ c s τ₂, THarrow θ₁ ξ₀ θ₂ => \v, ⌈v ↓ ρ τ⌉ /\ ∀ v₁, v₁ ∈ V τ₁ ρ Ct θ ⇒ Eapp v v₁ ∈ E' (V τ₂) τ₂ (cexpr_to_nat c) s (add (if ξ₀ <=? |v₁| then |v₁| else ξ₀) ρ) Ct θ₂
      | Tuniversal c s τ, _ => \v, ⌈v ↓ ρ τ⌉ /\ ∀1 τ', ∀2 S, VSet τ' S ⇒ Etapp v τ' ∈ E' (V τ) τ (cexpr_to_nat c) s (add (τ', S) ρ) Ct θ
      | Trecur τ, _ => @S, \v, ⌈v ↓ ρ τ⌉ /\ ∃ v', ⌈v = Efold τ v'⌉ /\ ▹ (v' ∈ V τ (add (ρ τ, S) ρ) Ct θ)
      | _, _ => \_, ⊥
    end
  .

  Definition E τ := E' (V τ) τ.

End LR.

End OpenPHOAS.

Import OpenPHOAS.

Unset Strict Implicit.
Unset Printing Implicit Defensive. 
Generalizable All Variables.

Section related.

  Variable var : nat -> Type.

  Class Lift A B :=
    {
      lift : forall (t : termType), A -> B t
    }.

  Instance Lift_list `{Lift A B} : Lift (list A) (fun t => list (B t)) :=
    {
      lift t a := map (lift t) a
    }.

  Definition lift_relOpen {ctx range} new : relOpen var ctx range -> relOpen var (new :: ctx) range.
    admit.
  Defined.

  Instance Lift_relOpen ctx range : Lift (relOpen var ctx range) (fun new => relOpen var (new :: ctx) range) :=
    {
      lift := lift_relOpen
    }.

  Definition lift_SubstEntry {ctx} new : SubstEntry var ctx -> SubstEntry var (new :: ctx).
    admit.
  Defined.

  Instance Lift_SubstEntry ctx : Lift (SubstEntry var ctx) (fun new => SubstEntry var (new :: ctx)) :=
    {
      lift := lift_SubstEntry
    }.

  Definition t_Ps_ρ ctx := (list (relOpen var ctx 0) * substs var ctx)%type.

  Definition lift_Ps_ρ {ctx} t (Ps_ρ : t_Ps_ρ ctx) : t_Ps_ρ (t :: ctx):=
    let (Ps, ρ) := Ps_ρ in
    let Ps := map (lift_relOpen t) Ps in
    let ρ := map (lift t) ρ in
    (Ps, ρ).

  Instance Lift_Ps_ρ ctx : Lift (t_Ps_ρ ctx) (fun new => t_Ps_ρ (new :: ctx))%type :=
    {
      lift := lift_Ps_ρ
    }.

  Definition extend {range} ctx new : relOpen var ctx range -> relOpen var (ctx ++ new) range.
    admit.
  Defined.

  Notation TTtype := (TTother type).
  Notation TTcsize := (TTother csize).

  Arguments SEtype {var ctx} _ _ .
  Arguments SEexpr {var ctx} _ _ .

  Definition add_type {ctx} k (Ps_ρ : t_Ps_ρ ctx) : t_Ps_ρ (TTrel 1 :: TTtype :: ctx) :=
    let (Ps, ρ) := lift_Ps_ρ TTtype Ps_ρ in
    let Ps := extend [TTtype] ctx (fun τ => ⌈kinding [] τ k⌉ : relOpen var [] 0) :: Ps in
    let (Ps, ρ) := lift_Ps_ρ 1 (Ps, ρ) in
    match k with
      | 0 => 
        let Ps := extend [TTrel 1; TTtype] ctx (fun S τ => VSet τ (S : relOpen var [] 1)) :: Ps in
        let ρ := SEtype (extend [TTrel 1; TTtype] ctx (fun _ τ => τ)) (Some (extend [TTrel 1; TTtype] ctx (fun S _ => S))) :: ρ in
        (Ps, ρ)
      | _ =>
        let ρ := SEtype (extend [TTrel 1; TTtype] ctx (fun _ τ => τ)) None :: ρ in
        (Ps, ρ)
    end.

  Arguments V {var ctx} _ _ _ _ .
  Arguments E {var ctx} _ _ _ _ _ _ .

  Definition csize_of_size : size -> option csize.
    admit.
  Defined.

  Definition asCsize P s :=
    (exists x, csize_of_size s = Some x /\ P x)%type.

  Existing Instance Apply_substs_size_size.
  Existing Instance Apply_substs_cexpr_cexpr.
  Existing Instance Apply_substs_expr_expr.

  Definition add_expr {ctx} τ θ (os : csize + size) Ct (Ps_ρ : t_Ps_ρ ctx) : t_Ps_ρ (TTcsize :: TTexpr :: ctx) :=
    let (Ps, ρ) := Ps_ρ in
    let ρ0 := ρ in
    let (Ps, ρ) := lift_Ps_ρ TTexpr (Ps, ρ) in
    let Ps := ((fun e => e ∈ V τ ρ0 Ct θ) : relOpen var (TTexpr :: ctx) 0) :: Ps in
    let (Ps, ρ) := lift_Ps_ρ TTcsize (Ps, ρ) in
    let ρ := SEexpr (extend [TTcsize; TTexpr] ctx (fun _ e => e)) (extend [TTcsize; TTexpr] ctx (fun ξ _ => ξ)) :: ρ in
    match os with
      | inl ξ₀ =>
        let Ps := extend [TTcsize; TTexpr] ctx (fun ξ v => ⌈ξ = if ξ₀ <=? |v| then |v| else ξ₀⌉ : relOpen var [] 0) :: Ps in
        (Ps, ρ)
      | inr s =>
        let Ps := extend [TTcsize; TTexpr] ctx (fun ξ _ => ⌈asCsize (fun ξ' => ξ = ξ') (ρ $$ s)⌉ : relOpen var [] 0) :: Ps in
        (Ps, ρ)
    end.

  Inductive tc_entryex :=
  | TEkindingex (_ : kind)
  | TEtypingex (_ : type * thresholds * (csize + size))
  .

  Definition tcontextex := list tc_entryex.

  Fixpoint make_ctx Γ :=
    match Γ with
      | nil => nil
      | TEkindingex _ :: Γ' =>
        TTrel 1 :: TTtype :: make_ctx Γ'
      | TEtypingex _ :: Γ' =>
        TTcsize :: TTexpr :: make_ctx Γ'
    end.

  Fixpoint make_Ps_ρ Γ Ct : t_Ps_ρ (make_ctx Γ) :=
    match Γ return t_Ps_ρ (make_ctx Γ) with 
      | nil => (nil, nil)
      | TEkindingex k :: Γ' =>
        let Ps_ρ := make_Ps_ρ Γ' Ct in
        add_type k Ps_ρ
      | TEtypingex (τ, θ, os) :: Γ' =>
        let Ps_ρ := make_Ps_ρ Γ' Ct in
        add_expr τ θ os Ct Ps_ρ
    end.

  Definition extendΓ : tcontext -> list csize -> list thresholds -> option tcontextex.
    admit.
  Defined.

  Definition valid {ctx} (Ps : list (relOpen var ctx 0)) (P : relOpen var ctx 0) : Prop.
    admit.
  Defined.
  Notation "Ps |- P" := (valid Ps P) (at level 90).

  Definition related Γ (e : expr) τ (c : cexpr) (s : size) :=
    (exists Ct ξs θs θ Γ',
       extendΓ Γ ξs θs = Some Γ' /\
       let (Ps, ρ) := make_Ps_ρ Γ' Ct in
       Ps |- (ρ $ e) ∈ E τ (Ct * cexpr_to_nat (ρ $ c))%nat (ρ $ s) ρ Ct θ)%type.

  Notation "⊩" := related.

  Lemma foundamental :
    forall Γ e τ c s,
      ⊢ Γ e τ c s -> 
      ⊩ Γ e τ c s.
  Proof.
    (* induction 1. *)
    admit.
  Qed.

End related.
      
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

Theorem sound_wrt_bound_proof : sound_wrt_bounded.
Proof.
  admit.
Qed.

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

  Program Fixpoint E' V τ (n : nat) (s : size) (ρ : substs) (C : nat) (θ : thresholds) {measure n} : rel var 1 :=
    \e, ⌈|~ [] e (ρ τ)⌉ /\ 
        ∀1 n', ∀ e', 
          (⌈nstepsex e n' 0 e'⌉ ⇒ ⌈n' ≤ n⌉ /\ (⌈IsValue e'⌉ ⇒ e' ∈ V ρ C θ /\ ⌈|e'| ≤ s⌉)) /\
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
      | τ₁ + τ₂, _ => \v, ⌈v ↓ ρ τ⌉ /\ ∃ v', (⌈v = Einl τ₂ v'⌉ /\ v' ∈ V τ₁ ρ C θ) /\ ⌈v = Einr τ₁ v'⌉ /\ v' ∈ V τ₂ ρ C θ
      | Tarrow τ₁ c s τ₂, THarrow θ₁ ξ₀ θ₂ => \v, ⌈v ↓ ρ τ⌉ /\ ∀ v₁, v₁ ∈ V τ₁ ρ C θ ⇒ Eapp v v₁ ∈ E' (V τ₂) τ₂ (cexpr_to_nat c) s (add (if ξ₀ <=? |v₁| then |v₁| else ξ₀) ρ) C θ₂
      | Tuniversal c s τ, _ => \v, ⌈v ↓ ρ τ⌉ /\ ∀1 τ', ∀2 S, VSet τ' S ⇒ Etapp v τ' ∈ E' (V τ) τ (cexpr_to_nat c) s (add (τ', S) ρ) C θ
      | Trecur τ, _ => @S, \v, ⌈v ↓ ρ τ⌉ /\ ∃ v', ⌈v = Efold τ v'⌉ /\ ▹ (v' ∈ V τ (add (ρ τ, S) ρ) C θ)
      | _, _ => \_, ⊥
    end
  .

  Definition E τ := E' (V τ).

End LR.

End ClosedPHOAS.

