Require Import Arith.
Require Import List.
Require Import Util.
Require Import NonnegRational.

Export NonnegRational.

(* 
  There are two statistics (or 'sizes', 'size measures') for each value :
  s0 (work) : number of invocations of 'fold' 
       (for algebraic data types, this correspond to the number of constructor invocations to construct this value);
  s1 (span) : parallel version of s0, where the fields of a pair are max'ed instead of sum'ed;
  For example, for lists, s0 correspond to its length; for trees, s0 corresponds to its number of nodes; s1 corresponds to its depth.
*)

Definition stat_idx := nat. (* An index indication the statistics you want. *)
Inductive path_command :=
| Pfst
| Psnd
| Pinl
| Pinr
| Punfold
| Punhide
.

Notation path := (list path_command). (* The query path into a inner-component *)

Inductive CtxEntry :=
| CEtype
| CEexpr
.

Definition context := list CtxEntry.

Class Leb A B :=
  {
    leb : A -> B -> bool
  }.

Infix "<=?" := leb (at level 70).
Notation "a <? b" := (negb (b <=? a)) (at level 70).

Global Instance Leb_nat : Leb nat nat :=
  {
    leb := Compare_dec.leb
  }.

Definition boolProp b := b = true.
Coercion boolProp : bool >-> Sortclass.

Inductive ordinal n :=
| Ordinal m (_ : m <? n)
.

Notation "''I_' n" := (ordinal n) (at level 8, n at level 2, format "''I_' n").
Notation "# n" := (Ordinal _ n (eq_refl true)) (at level 3).

Program Fixpoint nthI {A} (ls : list A) (i : 'I_(length ls)) :=
  match ls with
    | x :: xs =>
      match i with
        | Ordinal 0 _ => x
        | Ordinal (S n) _ => nthI xs #n
      end
    | nil => _
  end.
Next Obligation.
  destruct i; simpl in *; intuition.
Defined.

Goal nthI (1 :: 2 :: nil) (Ordinal 2 1 eq_refl) = 2. eauto. Qed.

Section ctx.

  Variable ctx : context.
  
  Inductive var : CtxEntry -> Type :=
  | Var (i : 'I_(length ctx)) : var (nthI ctx i)
  .

  Definition var_path := (var CEexpr * path)%type.

  (* complexity expression *)
  Inductive cexpr :=
  (* it is a ring *)
  | F0
  | Fadd (a b : cexpr)
  | F1
  | Fmul (a b : cexpr)
  (* it is a module, so also an algebra*)
  | Fscale (_ : QN) (_ : cexpr)
  (* some special operations *)
  | Fmax (a b : cexpr)
  | Flog (base : QN) (n : cexpr)
  | Fexp (base : QN) (n : cexpr)
  (* variables *)
  | Fvar (x : var_path) (stat : stat_idx)
  (* minus 1 (lower-capped by 0) *)
  | Fminus1 (_ : cexpr)
  .

  Global Instance Max_cexpr : Max cexpr :=
    {
      max := Fmax
    }.

  (* Definition Fconst c := Fscale c F1. *)
  (* Coercion Fconst : QN >-> cexpr. *)

  Definition stats := (cexpr * cexpr)%type.

  Definition stats_get (idx : stat_idx) (ss : stats) := 
    match ss with
      | (n0, n1) =>
        match idx with
          | O => n0
          | _ => n1
        end
    end.

  Inductive size :=
  | Svar (x : var_path)
  | Sstats (_ : stats)
  | Sinlinr (a b: size)
  | Spair (a b: size)
  | Sfold (_ : size)
  | Shide (_ : size)
  .

  Definition stats_binop {A} (f : cexpr -> cexpr -> A) (a b : stats) :=
    match a, b with
      | (a0, a1), (b0, b1) => (f a0 b0, f a1 b1)
    end.

  Definition stats_add := stats_binop Fadd.
  Infix "+" := stats_add : stats_scope.
  Delimit Scope stats_scope with stats.
  Definition stats_max := stats_binop Fmax.
  Global Instance Max_stats : Max stats :=
    {
      max := stats_max
    }.

  Definition zeros : stats := (F0, F0).

  Fixpoint summarize (s : size) : stats :=
    match s with
      | Svar x => (Fvar x 0%nat, Fvar x 1%nat)
      | Sstats ss => ss
      | Spair a b => 
        (summarize a + summarize b)%stats
      | Sinlinr a b => 
        max (summarize a) (summarize b)
      | Sfold s =>
        ((F1, F1) + summarize s)%stats
      | Shide s => zeros
    end.

End ctx.

Global Arguments Fscale {ctx} _ _ .
Global Arguments Fadd {ctx} _ _ .
Global Arguments Fmul {ctx} _ _ .
Global Arguments F0 {ctx} .
Global Arguments F1 {ctx} .
Global Arguments Flog {ctx} _ _.
Global Arguments Fmax {ctx} _ _ .
Global Arguments Fexp {ctx} _ _ .
Global Arguments Fvar {ctx} _ _ .
Global Arguments Fminus1 {ctx} _ .
Global Arguments stats_get {ctx} _ _ .
Global Arguments summarize {ctx} _ .

