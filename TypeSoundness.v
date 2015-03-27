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
Notation "|~" := typingsim.

Definition nostuck e := forall e', steps e e' -> IsValue e' \/ exists e'', step e' e''.

Theorem sound_wrt_nostuck :
  forall e τ,
    |~ e τ ->
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

Definition nat_of_cexpr (c : cexpr) : nat.
  admit.
Defined.

Coercion c2s (ξ : csize) {ctx} : open_size ctx.
  admit.
Defined.

(*
Instance Subst_csize_cexpr : Subst CEexpr (fun _ => csize) open_cexpr :=
  {
    substx ctx n v b := substx n (c2s v) b
  }.

Instance Subst_csize_size : Subst CEexpr (fun _ => csize) open_size :=
  {
    substx ctx n v b := substx n (c2s v) b
  }.
*)

Definition le_csize_size : csize -> size -> Prop.
  admit.
Defined.

Instance Le_cszie_size : Le csize size :=
  {
    le := le_csize_size
  }.

Notation "| v |" := (get_csize v) (at level 10).
Infix "≤" := le (at level 70).

Definition terminatesWith e n v := (nsteps e n v /\ IsValue v)%type.
Notation "⇓" := terminatesWith.

(*
Definition asNat P c :=
  (exists nc, nat_of_cexpr c = Some nc /\ P nc)%type.
Notation "⌊ n | P ⌋" := (asNat (fun n => P)).
*)

Infix "×" := Tprod (at level 40).
Infix "+" := Tsum.
Notation "e ↓ τ" := (IsValue e /\ |~ e τ) (at level 51).

Notation "! n" := (c2s n) (at level 3).

Definition sound_wrt_bounded :=
  forall f τ₁ c s τ₂, 
    f ↓ Tarrow τ₁ c s τ₂ -> 
    exists (C : nat), 
      forall v,
        v ↓ τ₁ ->
        let ξ := |v| in
        (* any reduction sequence is bounded by C * c(ξ) *)
        forall n e',
          nsteps (Eapp f v) n e' -> n ≤ C * (nat_of_cexpr (subst !ξ c)).

Local Open Scope prog_scope.

Inductive stepex : expr -> bool -> expr -> Prop :=
| STecontext E e1 b e2 e1' e2' : 
    stepex e1 b e2 -> 
    plug E e1 e1' -> 
    plug E e2 e2' -> 
    stepex e1' b e2'
| STapp t body arg : IsValue arg -> stepex (Eapp (Eabs t body) arg) false (subst arg body)
| STlet v main : IsValue v -> stepex (Elet v main) false (subst v main)
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
    
Definition Rel ctx t := forall var, relOpen var ctx t.

Section REL.

  Variable ctx : Ctx.
  Notation Rel := (Rel ctx).
  
  Definition RELinj P : Rel 0 := fun var => ORinj var ctx P.
  Definition RELtrue : Rel 0 := fun var => ORtrue var ctx.
  Definition RELfalse : Rel 0 := fun var => ORfalse var ctx.
  Definition RELand (a b : Rel 0) : Rel 0 := fun var => ORand var ctx (a var) (b var).
  Definition RELor (a b : Rel 0) : Rel 0 := fun var => ORor var ctx (a var) (b var).
  Definition RELimply (a b : Rel 0) : Rel 0 := fun var => ORimply var ctx (a var) (b var).
  Definition RELforalle (F : expr -> Rel 0) : Rel 0 := fun var => ORforalle var ctx (fun e => F e var).
  Definition RELexistse (F : expr -> Rel 0) : Rel 0 := fun var => ORexistse var ctx (fun e => F e var).
  Definition RELforall1 T (F : T -> Rel 0) : Rel 0 := fun var => ORforall1 var ctx T (fun x => F x var).
  Definition RELexists1 T (F : T -> Rel 0) : Rel 0 := fun var => ORexists1 var ctx T (fun x => F x var).
  Definition RELabs (n : nat) (F : expr -> Rel n) : Rel (S n) := fun var => ORabs var ctx n (fun e => F e var).
  Definition RELapp n (r : Rel (S n)) (e : expr) : Rel n := fun var => ORapp var ctx n (r var) e.
  Definition RELlater (P : Rel 0) : Rel 0 := fun var => ORlater var ctx (P var).
  
End REL.

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

Local Open Scope prog_scope.

(*
Section substs.
  
  Variable ctx : Ctx.

End substs.

Arguments substs_sem {ctx} _ _ _ .
 *)

(* closing substitutions *)
Section csubsts.
  
  Variable var : nat -> Type.
  Variable ctx : Ctx.

  Inductive SubstEntry :=
  | SEtype (_ : relOpen var ctx (TTother type)) (_ : relOpen var ctx 1)
  | SEexpr (_ : relOpen var ctx (TTother csize))
  .

  Definition csubsts (lctx : context) : Type := list SubstEntry.

  Definition csubsts_type {lctx} : csubsts lctx -> open_type lctx -> type.
    admit.
  Defined.

  Coercion csubsts_type : csubsts >-> Funclass.

  Definition csubsts_sem {lctx} : csubsts lctx -> open_var CEtype lctx -> relOpen var ctx 1.
    admit.
  Defined.

  Global Instance Apply_csubsts_nat_rel lctx : Apply (csubsts lctx) (open_var CEtype lctx) (relOpen var ctx 1) :=
    {
      apply := csubsts_sem
    }.

  Definition csubsts_cexpr {lctx} : csubsts lctx -> open_cexpr lctx -> cexpr.
    admit.
  Defined.

  Global Instance Apply_csubsts_cexpr_cexpr lctx : Apply (csubsts lctx) (open_cexpr lctx) cexpr :=
    {
      apply := csubsts_cexpr
    }.

  Definition csubsts_size {lctx} : csubsts lctx -> open_size lctx -> size.
    admit.
  Defined.

  Global Instance Apply_csubsts_size_size lctx : Apply (csubsts lctx) (open_size lctx) size :=
    {
      apply := csubsts_size
    }.

  Definition csubsts_expr {lctx} : csubsts lctx -> (open_expr lctx) -> expr.
    admit.
  Defined.

  Global Instance Apply_csubsts_expr_expr lctx : Apply (csubsts lctx) (open_expr lctx) expr :=
    {
      apply := csubsts_expr
    }.

  Definition add_csize {lctx} : csize -> csubsts lctx -> csubsts (CEexpr :: lctx).
    admit.
  Defined.

  Global Instance Add_csize_csubsts lctx : Add csize (csubsts lctx) (csubsts (CEexpr :: lctx)) :=
    {
      add := add_csize
    }.

  Definition add_pair {lctx} : (type * relOpen var ctx 1) -> csubsts lctx -> csubsts (CEtype :: lctx).
    admit.
  Defined.

  Global Instance Add_pair_csubsts lctx : Add (type * relOpen var ctx 1) (csubsts lctx) (csubsts (CEtype :: lctx)) :=
    {
      add := add_pair
    }.

End csubsts.

Arguments csubsts_sem {_ ctx lctx} _ _ .

(* A "step-indexed" kriple model *)
(* the logical relation *)
Section LR.
  
  Variable ctx : Ctx.

  Program Fixpoint E' {lctx} (V : nat -> forall var, csubsts var ctx lctx -> relOpen var ctx 1) τ (n : nat) (s : size) (Ct : nat) {var} (ρ : csubsts var ctx lctx) {measure n} : relOpen var ctx 1 :=
    \e, ⌈|~ e (ρ τ)⌉ /\ 
        ∀1 n', ∀ e', 
          (⌈nstepsex e n' 0 e'⌉ ⇒ ⌈n' ≤ n⌉ /\ (⌈IsValue e'⌉ ⇒ e' ∈ V Ct var ρ /\ ⌈|e'| ≤ s⌉)) /\
          match n with
            | 0 => ⊤
            | S _ =>
              (⌈nstepsex e (S n') 1 e'⌉ ⇒ ⌈(S n') ≤ n⌉ /\ ▹ (e' ∈ E' V τ (n - S n') s Ct ρ))
          end.
  Next Obligation.
    omega.
  Defined.

  Unset Maximal Implicit Insertion.
  Unset Implicit Arguments.
  (*here*)

  Fixpoint relvii {lctx} (τ : open_type lctx) (Ct : nat) {var} (ρ : csubsts var ctx lctx) {struct τ} : relOpen var ctx 1 :=
    match τ with
      | Tvar α => csubsts_sem ρ α
      | Tunit => \v, ⌈v ↓ τ⌉
      | τ₁ × τ₂ => \v, ⌈v ↓ ρ τ⌉ /\ ∃ a b, ⌈v = Epair a b⌉ /\ a ∈ relvii τ₁ Ct ρ /\ b ∈ relvii τ₂ Ct ρ
      | τ₁ + τ₂ => \v, ⌈v ↓ ρ τ⌉ /\ ∃ v', (⌈v = Einl τ₂ v'⌉ /\ v' ∈ relvii τ₁ Ct ρ) /\ ⌈v = Einr τ₁ v'⌉ /\ v' ∈ relvii τ₂ Ct ρ
      | Tarrow τ₁ c s τ₂ => \v, ⌈v ↓ ρ τ⌉ /\ ∀ v₁, v₁ ∈ relvii τ₁ Ct ρ ⇒ Eapp v v₁ ∈ E' (relvii τ₂) τ₂ (nat_of_cexpr (subst (|v₁|) c)) (subst (|v₁|) s) Ct (add (|v₁|) ρ)
      | Tuniversal c s τ₁ => \v, ⌈v ↓ ρ τ⌉ /\ ∀1 τ', ∀2 S, VSet τ' S ⇒ Etapp v τ' ∈ E' (relvii τ₁) τ₁ (nat_of_cexpr c) s Ct (add (τ', S) ρ)
      | Trecur τ₁ => @S, \v, ⌈v ↓ ρ τ⌉ /\ ∃ v', ⌈v = Efold (ρ τ) v'⌉ /\ ▹ (v' ∈ relvii τ₁ Ct (add (ρ τ, S) ρ))
      | _ => \_, ⊥
    end
  .

  Definition E τ := E' (V τ) τ.

End LR.

Unset Strict Implicit.
Unset Printing Implicit Defensive. 
Generalizable All Variables.

Definition csize_of_size : size -> option csize.
  admit.
Defined.

Definition asCsize P s :=
  (exists x, csize_of_size s = Some x /\ P x)%type.

Notation TTtype := (TTother type).
Notation TTcsize := (TTother csize).

Arguments SEtype {var ctx} _ _ .
Arguments SEexpr {var ctx} _ _ .

Arguments V {ctx} _ _ {var} _ .
Arguments E {ctx} _ _ _ _ {var} _ .

Class Lift A B :=
  {
    lift : forall (t : termType), A -> B t
  }.

Global Instance Lift_list `{Lift A B} : Lift (list A) (fun t => list (B t)) :=
  {
    lift t a := map (lift t) a
  }.

Definition lift_Rel {ctx range} new : Rel ctx range -> Rel (new :: ctx) range.
  admit.
Defined.

Global Instance Lift_Rel ctx range : Lift (Rel ctx range) (fun new => Rel (new :: ctx) range) :=
  {
    lift := lift_Rel
  }.

Definition Substs ctx := forall var, csubsts var ctx.

Definition lift_Substs {ctx} new : Substs ctx -> Substs (new :: ctx).
  admit.
Defined.

Global Instance Lift_Substs ctx : Lift (Substs ctx) (fun new => Substs (new :: ctx)) :=
  {
    lift := lift_Substs
  }.

Definition t_Ps_ρ ctx := (list (Rel ctx 0) * Substs ctx)%type.
Definition t_Ps ctx := list (Rel ctx 0).
Notation t_ρ := Substs.
Notation lift_ρ := lift_Substs.

Definition lift_Ps_ρ {ctx} t (Ps_ρ : t_Ps_ρ ctx) : t_Ps_ρ (t :: ctx):=
  let (Ps, ρ) := Ps_ρ in
  let Ps := map (lift_Rel t) Ps in
  let ρ := lift t ρ in
  (Ps, ρ).

Global Instance Lift_Ps_ρ ctx : Lift (t_Ps_ρ ctx) (fun new => t_Ps_ρ (new :: ctx))%type :=
  {
    lift := lift_Ps_ρ
  }.

Definition lift_Ps {ctx} t (Ps : t_Ps ctx) : t_Ps (t :: ctx):=
  map (lift_Rel t) Ps.

Global Instance Lift_Ps ctx : Lift (t_Ps ctx) (fun new => t_Ps (new :: ctx))%type :=
  {
    lift := lift_Ps
  }.

Definition extend {var range} ctx new : relOpen var ctx range -> relOpen var (ctx ++ new) range.
  admit.
Defined.

Definition add_type {ctx} (Ps_ρ : t_Ps_ρ ctx) : t_Ps_ρ (TTrel 1 :: TTtype :: ctx) :=
  let (Ps, ρ) := lift_Ps_ρ TTtype Ps_ρ in
  let Ps := (fun var => extend [TTtype] ctx (fun τ => ⌈kinding [] τ 0⌉ : relOpen var [] 0)) :: Ps in
  let (Ps, ρ) := lift_Ps_ρ 1 (Ps, ρ) in
  let Ps := (fun var => extend [TTrel 1; TTtype] ctx (fun S τ => VSet τ (S : relOpen var [] 1))) :: Ps in
  let ρ := fun var => SEtype (extend [TTrel 1; TTtype] ctx (fun _ τ => τ)) (extend [TTrel 1; TTtype] ctx (fun S _ => S)) :: ρ var in
  (Ps, ρ)
.

Definition add_Ps_type {ctx} (Ps : t_Ps ctx) : t_Ps (TTrel 1 :: TTtype :: ctx) :=
  let Ps := lift_Ps TTtype Ps in
  let Ps := (fun var => extend [TTtype] ctx (fun τ => ⌈kinding [] τ 0⌉ : relOpen var [] 0)) :: Ps in
  let Ps := lift_Ps 1 Ps in
  let Ps := (fun var => extend [TTrel 1; TTtype] ctx (fun S τ => VSet τ (S : relOpen var [] 1))) :: Ps in
  Ps
.

Definition add_ρ_type {ctx} (ρ : t_ρ ctx) : t_ρ (TTrel 1 :: TTtype :: ctx) :=
  let ρ := lift_ρ TTtype ρ in
  let ρ := lift_ρ 1 ρ in
  let ρ := fun var => SEtype (extend [TTrel 1; TTtype] ctx (fun _ τ => τ)) (extend [TTrel 1; TTtype] ctx (fun S _ => S)) :: ρ var in
  ρ
.

Definition add_expr {ctx} τ Ct (Ps_ρ : t_Ps_ρ ctx) : t_Ps_ρ (TTexpr :: ctx) :=
  let (Ps, ρ) := Ps_ρ in
  let ρ0 := ρ in
  let (Ps, ρ) := lift_Ps_ρ TTexpr (Ps, ρ) in
  let Ps := ((fun var v => v ∈ V τ Ct (ρ0 var)) : Rel (TTexpr :: ctx) 0) :: Ps in
  let ρ := fun var => SEexpr (extend [TTexpr] ctx (fun v => v)) (extend [TTexpr] ctx (fun v => |v| : relOpen var [] TTcsize)) :: ρ var in
  (Ps, ρ)
.

Definition add_ρ_expr {ctx} (ρ : t_ρ ctx) : t_ρ (TTexpr :: ctx) :=
  let ρ := lift_ρ TTexpr ρ in
  let ρ := fun var => SEexpr (extend [TTexpr] ctx (fun v => v)) (extend [TTexpr] ctx (fun v => |v| : relOpen var [] TTcsize)) :: ρ var in
  ρ
.

Definition add_Ps_expr {ctx} τ Ct (Ps : t_Ps ctx) ρ : t_Ps (TTexpr :: ctx) :=
  let Ps := lift_Ps TTexpr Ps in
  let Ps := ((fun var v => v ∈ V τ Ct (ρ var)) : Rel (TTexpr :: ctx) 0) :: Ps in
  Ps
.

Fixpoint make_ctx Γ :=
  match Γ with
    | nil => nil
    | TEkinding :: Γ' =>
      TTrel 1 :: TTtype :: make_ctx Γ'
    | TEtyping _ :: Γ' =>
      TTexpr :: make_ctx Γ'
  end.

Fixpoint make_Ps_ρ Γ Ct : t_Ps_ρ (make_ctx Γ) :=
  match Γ return t_Ps_ρ (make_ctx Γ) with 
    | nil => (nil, (fun var => nil))
    | TEkinding :: Γ' =>
      let Ps_ρ := make_Ps_ρ Γ' Ct in
      add_type Ps_ρ
    | TEtyping τ :: Γ' =>
      let Ps_ρ := make_Ps_ρ Γ' Ct in
      add_expr τ Ct Ps_ρ
  end.

Fixpoint make_ρ Γ : t_ρ (make_ctx Γ) :=
  match Γ return t_ρ (make_ctx Γ) with 
    | nil => (fun var => nil)
    | TEkinding :: Γ' =>
      let ρ := make_ρ Γ' in
      add_ρ_type ρ
    | TEtyping _ :: Γ' =>
      let ρ := make_ρ Γ' in
      add_ρ_expr ρ
  end.

Fixpoint make_Ps Γ Ct : t_Ps (make_ctx Γ) :=
  match Γ return t_Ps (make_ctx Γ) with 
    | nil => nil
    | TEkinding :: Γ' =>
      let Ps := make_Ps Γ' Ct in
      add_Ps_type Ps
    | TEtyping τ :: Γ' =>
      let Ps := make_Ps Γ' Ct in
      add_Ps_expr τ Ct Ps (make_ρ Γ')
  end.

Definition valid {ctx} (Ps : list (Rel ctx 0)) (P : Rel ctx 0) : Prop.
  admit.
Defined.
Notation "Ps |- P" := (valid Ps P) (at level 90).

Definition related Γ (e : expr) τ (c : cexpr) (s : size) :=
  (exists Ct,
     make_Ps Γ Ct |-
     fun var => 
       let ρ := make_ρ Γ var in
       (ρ $ e) ∈ E τ (Ct * cexpr_to_nat (ρ $ c))%nat (ρ $ s) Ct ρ)%type.

Notation "⊩" := related.

Lemma foundamental :
  forall Γ e τ c s,
    ⊢ Γ e τ c s -> 
    ⊩ Γ e τ c s.
Proof.
  induction 1.
  {
    unfold related.
    exists 1.
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

Theorem sound_wrt_bound_proof : sound_wrt_bounded.
Proof.
  admit.
Qed.
