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

Definition c2s {ctx} (ξ : csize) : open_size ctx.
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

(* Notation "| v |" := (get_csize v) (at level 10). *)
Notation "& v" := (get_csize v) (at level 3, format "& v").
Notation "! n" := (c2s n) (at level 3, format "! n").
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

(*
Coercion c2s : csize >-> open_size.
Coercion get_csize : open_expr >-> csize.
Coercion nat_of_cexpr : open_cexpr >-> nat.
 *)

Definition sound_wrt_bounded :=
  forall f τ₁ c s τ₂, 
    f ↓ Tarrow τ₁ c s τ₂ -> 
    exists (C : nat), 
      forall v,
        v ↓ τ₁ ->
        (* any reduction sequence is bounded by C * c(|v|) *)
        forall n e',
          nsteps (Eapp f v) n e' -> n ≤ C * (nat_of_cexpr (subst !(&v) c)).

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
Unset Implicit Arguments.

Module ClosedPHOAS.

Notation "⊤" := (Rtrue _).
Notation "⊥" := (Rtrue _).
(* Notation "\ e , p" := (Rabs (fun e => p)) (at level 200, format "\ e , p"). *)
Notation "\ x .. y , p" := (Rabs (fun x => .. (Rabs (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity).
Notation "∀ x .. y , p" := (Rforalle (fun x => .. (Rforalle (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity).
Notation "∃ x .. y , p" := (Rexistse (fun x => .. (Rexistse (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity).
Notation "∀1 x .. y , p" := (Rforall1 (fun x => .. (Rforall1 (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity).
Notation "∃1 x .. y , p" := (Rexists1 (fun x => .. (Rexists1 (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity).
Definition RforallR' {var n} P := (@RforallR var n (fun x => P (Rvar _ _ x))).
Notation "∀2 x .. y , p" := (RforallR' (fun x => .. (RforallR' (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity).
Definition RexistsR' {var n} P := (@RexistsR var n (fun x => P (Rvar _ _ x))).
Notation "∃2 x .. y , p" := (RexistsR' (fun x => .. (RexistsR' (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity).
Definition Rrecur' {var n} P := (@Rrecur var n (fun x => P (Rvar _ _ x))).
Notation "@@ x .. y , p" := (Rrecur' (fun x => .. (Rrecur' (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity).
Notation "⌈ P ⌉" := (Rinj _ P).
Notation "e ∈ P" := (Rapp P e) (at level 70).
Infix "/\" := Rand.
Infix "\/" := Ror.
Infix "⇒" := Rimply (at level 90).
Notation "▹" := Rlater.
Definition VSet {var} τ (S : rel var 1) := ∀ v, v ∈ S ⇒ ⌈v ↓ τ⌉.

Section TestNotations.
  
  Variable var : nat -> Type.

  Definition ttt1 : rel var 1 := \e , ⊤.
  Definition ttt2 : rel var 1 := \e , ⌈e ↓ Tunit⌉.
  Definition ttt3 : rel var 1 := \_ , ⌈True /\ True⌉.

End TestNotations.

End ClosedPHOAS.

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

  Definition liftToOpen : forall C {n1 n2} (f : rel var n1 -> rel var n2) (a : relOpen C n1), relOpen C n2.
    refine
      (fix liftToOpen C : forall {n1 n2} (f : rel var n1 -> rel var n2) (a : relOpen C n1), relOpen C n2 :=
         match C return forall {n1 n2} (f : rel var n1 -> rel var n2) (a : relOpen C n1), relOpen C n2 with
           | nil => fun n1 n2 f a => _
           | nv :: C' => fun n1 n2 f a => _ (*@liftToOpen C' n1 n2*)
         end).
    {
      exact (f a).
    }
    {
      simpl in *.
      intros X.
      exact ((liftToOpen C' _ _) f (a X)).
    }
  Defined.

  (* should also compute *)
  Program Fixpoint liftToOpen' C {n1 n2} (f : rel var n1 -> rel var n2) (a : relOpen C n1) : relOpen C n2 :=
    match C with
      | nil => _
      | nv :: C' => _ (@liftToOpen' C' n1 n2)
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

Module OpenPHOAS.
  
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
Notation "@@ x .. y , p" := (ORrecur' (fun x => .. (ORrecur' (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity).
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

End OpenPHOAS.

(* An Logical Step-indexed Logical Relation (LSLR) for boundedness *)

Local Open Scope prog_scope.

(*
Section substs.
  
  Variable ctx : Ctx.

End substs.

Arguments substs_sem {ctx} _ _ _ .
 *)

Set Implicit Arguments.

(* closing substitutions *)
Section csubsts.
  
  Variable var : nat -> Type.
  Variable ctx : Ctx.

  Inductive SubstEntry : CtxEntry -> Type :=
  | SEtype (_ : relOpen var ctx (TTother type)) (_ : relOpen var ctx 1) : SubstEntry CEtype
  | SEexpr (_ : relOpen var ctx (TTother csize)) : SubstEntry CEexpr
  .

  Inductive csubsts : context -> Type :=
  | CSnil : csubsts []
  | CScons {t lctx} : SubstEntry t -> csubsts lctx -> csubsts (t :: lctx)
  .

End csubsts.

Section csubstsClosed.
  
  Variable var : nat -> Type.

  Generalizable All Variables.

  Definition pair_of_se (e : SubstEntry var [] CEtype) : (type * rel var 1) :=
    match e with
      | SEtype t r => (t, r)
    end.

  Definition type_of_se := pair_of_se >> fst.
  Definition sem_of_se := pair_of_se >> snd.

  Definition csize_of_se (e : SubstEntry var [] CEexpr) : csize :=
    match e with
      | SEexpr s => s
    end.

  Definition csubst_type `{Subst CEtype open_type B} {lctx} (v : SubstEntry var [] CEtype) (b : B (CEtype :: lctx)) : B lctx.
    refine
      (subst (cast (shiftby lctx (type_of_se v)) _) b).
    simpl.
    eapply app_nil_r.
  Defined.
  
  Definition csubst_csize `{Subst CEexpr open_size B} {lctx} (v : SubstEntry var [] CEexpr) (b : B (CEexpr :: lctx)) : B lctx :=
    subst !(csize_of_se v) b.
  
  Arguments tl {A} _ .

  Definition subst_close `{Subst CEtype open_type B, Subst CEexpr open_size B} : forall lctx, csubsts var [] lctx -> B lctx -> B [].
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
      - eapply (csubst_csize v b).
    }
    Grab Existential Variables.
    { eapply f_equal with (f := tl) in Heq; exact Heq. }
    { eapply f_equal with (f := tl) in Heq; exact Heq. }
  Defined.

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

  Definition csubsts_type :=
    subst_close (B := open_type).

  Global Instance Apply_csubsts_type_type lctx : Apply (csubsts var [] lctx) (open_type lctx) type :=
    {
      apply := @csubsts_type _
    }.

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

  Arguments SEtype {var ctx} _ _ .
  Arguments SEexpr {var ctx} _ .

  Definition add_csize {lctx} s rho :=
    CScons (lctx := lctx) (SEexpr (var := var) (ctx := []) s) rho.
  
  Global Instance Add_csize_csubsts lctx : Add csize (csubsts var [] lctx) (csubsts var [] (CEexpr :: lctx)) :=
    {
      add := add_csize
    }.

  Definition add_pair {lctx} p rho :=
    CScons (lctx := lctx) (SEtype (var := var) (ctx := []) (fst p) (snd p)) rho.

  Global Instance Add_pair_csubsts lctx : Add (type * rel var 1) (csubsts var [] lctx) (csubsts var [] (CEtype :: lctx)) :=
    {
      add := add_pair
    }.

End csubstsClosed.

Arguments csubsts_sem {_ lctx} _ _ .

Import ClosedPHOAS.

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
  
  Program Fixpoint E' {lctx} (V : forall var, csubsts var [] lctx -> rel var 1) τ (n : nat) (s : size) var (ρ : csubsts var [] lctx) {measure n} : rel var 1 :=
    \e, ⌈|~ e (ρ $ τ)⌉ /\ 
        ∀1 n', ∀ e', 
          (⌈nstepsex e n' 0 e'⌉ ⇒ ⌈n' ≤ n⌉ /\ (⌈IsValue e'⌉ ⇒ e' ∈ V var ρ /\ ⌈&e' ≤ s⌉)) /\
          match n with
            | 0 => ⊤
            | S _ =>
              (⌈nstepsex e (S n') 1 e'⌉ ⇒ ⌈(S n') ≤ n⌉ /\ ▹ (e' ∈ E' V τ (n - S n') s ρ))
          end.
  Next Obligation.
    omega.
  Defined.

  Fixpoint V {lctx} τ var (ρ : csubsts var [] lctx) : rel var 1 :=
    match τ with
      | Tvar α => csubsts_sem ρ α
      | Tunit => \v, ⌈v ↓ Tunit⌉
      | τ₁ × τ₂ => \v, ⌈v ↓ ρ $$ τ⌉ /\ ∃ a b, ⌈v = Epair a b⌉ /\ a ∈ V τ₁ ρ /\ b ∈ V τ₂ ρ
      | τ₁ + τ₂ => \v, ⌈v ↓ ρ $$ τ⌉ /\ ∃ v', (⌈v = Einl (ρ $ τ₂) v'⌉ /\ v' ∈ V τ₁ ρ) \/ (⌈v = Einr (ρ $ τ₁) v'⌉ /\ v' ∈ V τ₂ ρ)
      | Tarrow τ₁ c s τ₂ => \v, ⌈v ↓ ρ $$ τ⌉ /\ ∀ v₁, v₁ ∈ V τ₁ ρ ⇒ Eapp v v₁ ∈ E' (V τ₂) τ₂ (Ct * nat_of_cexpr (ρ $ subst !(&v₁) c)) (ρ $ subst !(&v₁) s) (add &v₁ ρ)
      | Tuniversal c s τ₁ => \v, ⌈v ↓ ρ $$ τ⌉ /\ ∀1 τ', ∀2 S, VSet τ' S ⇒ Etapp v τ' ∈ E' (V τ₁) τ₁ (Ct * nat_of_cexpr (ρ $ c)) (ρ $ s) (add (τ', S) ρ)
      | Trecur τ₁ => @@S, \v, ⌈v ↓ ρ $$ τ⌉ /\ ∃ v', ⌈v = Efold (ρ $ τ) v'⌉ /\ ▹ (v' ∈ V τ₁ (add (ρ $ τ, S) ρ))
      | _ => \_, ⊥
    end
  .

  Definition E {lctx} τ := E' (lctx := lctx) (V τ) τ.

End LR.

Definition csubsts_close1 {lctx var t ctx} : csubsts var (t :: ctx) lctx -> interp var t -> csubsts var ctx lctx.
  admit.
Defined.

Instance Apply_csubsts_interp lctx var t ctx : Apply (csubsts var (t :: ctx) lctx) (interp var t) (csubsts var ctx lctx) :=
  {
    apply := @csubsts_close1 lctx var t ctx
  }.

Definition liftLR {lctx var} : forall ctx (f : csubsts var [] lctx -> rel var 1) (a : csubsts var ctx lctx), relOpen var ctx 1.
  refine
    (fix F ctx : forall (f : csubsts var [] lctx -> rel var 1) (a : csubsts var ctx lctx), relOpen var ctx 1 :=
       match ctx return forall (f : csubsts var [] lctx -> rel var 1) (a : csubsts var ctx lctx), relOpen var ctx 1 with
         | nil => fun f a => _
         | nv :: ctx' => fun f a => _ 
       end).
  {
    exact (f a).
  }
  {
    simpl in *.
    intros X.
    exact ((F ctx') f (a $ X)).
  }
Defined.

Definition openE Ct {lctx} tau n s {var ctx} := liftLR (ctx := ctx) (@E Ct lctx tau n s var).
Definition openV Ct {lctx} tau {var ctx} := liftLR (ctx := ctx) (@V Ct lctx tau var).

(*
Definition csize_of_size : size -> option csize.
  admit.
Defined.

Definition asCsize P s :=
  (exists x, csize_of_size s = Some x /\ P x)%type.
 *)

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
