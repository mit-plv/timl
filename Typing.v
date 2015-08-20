Set Maximal Implicit Insertion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 
Generalizable All Variables.

Require Import List.
Require Import Program.
Require Import Util.
Require Import Syntax.
Require Import Subst.
Require Import Order.

Export Syntax Subst Order.

Import ListNotations.
Local Open Scope list_scope.

Global Instance Shift_option `{Shift A T} : Shift (fun ctx => option (T ctx)) :=
  {
    shift ctx new n b := option_map (shift (ctx := ctx) new n) b
  }.

Global Instance Shift_pair `{Shift A T1, Shift A T2} : Shift (fun ctx => T1 ctx * T2 ctx)%type :=
  {
    shift ctx new n b := (shift (ctx := ctx) new n (fst b), shift new n (snd b))
  }.

(* kinds are restricted to the form (* => * => ... => *). 0 means * *)
Definition kind := nat.

(* Typing context.
   The second field of TEtyping is the optional size constraint
 *)
Inductive tc_entry : CtxEntry -> list CtxEntry -> Type := 
  | TEtyping ctx : type ctx -> tc_entry CEexpr ctx
  | TEkinding ctx : tc_entry CEtype ctx
.

Arguments TEkinding {ctx} .

Inductive tcontext : context -> Type :=
| TCnil : tcontext []
| TCcons t ctx : tc_entry t ctx -> tcontext ctx -> tcontext (t :: ctx)
.

Notation "[ ]" := TCnil : TC.
Notation "[ x ; .. ; y ]" := (TCcons x .. (TCcons y TCnil) ..) : TC.
Infix "::" := TCcons (at level 60, right associativity) : TC.
Delimit Scope TC with TC.
Bind Scope TC with tcontext.

Local Open Scope prog_scope.

Definition add_typing {ctx} t T := (TEtyping (ctx := ctx) t :: T)%TC.
Definition add_kinding {ctx} T := (TEkinding (ctx := ctx) :: T)%TC.

Fixpoint add_typings {ctx} ls T :=
  match ls return tcontext (repeat CEexpr (length ls) ++ ctx) with
    | nil => T
    | t :: ls =>
      let T := add_typings ls T in
      add_typing (shift (repeat CEexpr (length ls)) 0 t) T
  end.

Unset Maximal Implicit Insertion.
Unset Implicit Arguments.

Class Equal t :=
  {
    equal : t -> t -> Prop
  }.

Infix "==" := equal (at level 70) : G.

Local Open Scope F.
Local Open Scope G.

Local Open Scope prog_scope.

Notation Tuniversal0 := (Tuniversal F0 S0).

(* Set Maximal Implicit Insertion. *)
(* Set Implicit Arguments. *)

Definition shiftby `{Shift A T} {ctx} new b := shift (ctx := ctx) new 0 b.

Definition type_of_te {ctx} (e : tc_entry CEexpr ctx) : type ctx :=
  match e with
    | TEtyping _ t => t
  end.

Definition TCtl {t ctx} (T : tcontext (t :: ctx)) : tcontext ctx :=
  match T with
    | TCcons _ _ _ T' => T'
  end.

Definition TChd {t ctx} (T : tcontext (t :: ctx)) : tc_entry t ctx :=
  match T with
    | TCcons _ _ e _ => e
  end.

Definition findtc : forall {vart ctx} (x : var vart ctx) (T : tcontext ctx), tc_entry vart (skipn (S x) ctx).
  refine 
    (fix findtc {vart ctx} {struct ctx} : forall (x : var vart ctx) (T : tcontext ctx), tc_entry vart (skipn (S x) ctx) :=
       match ctx return forall (x : var vart ctx) (T : tcontext ctx), tc_entry vart (skipn (S x) ctx) with
         | nil => _
         | t :: ctx' =>
           fun x T => 
             match x return tc_entry vart (skipn x ctx') with
               | Var n Hn => 
                 match n return forall Hn, tc_entry vart (skipn (Var n Hn) ctx') with
                   | 0 => _
                   | S n' => _
                 end Hn
             end
       end).
  {
    intros.
    destruct x; destruct n; simpl in *; discriminate.
  }
  {
    intros Hn'.
    simpl in *.
    eapply ce_eq_b_iff in Hn'.
    destruct t; destruct vart; try discriminate; exact (TChd T).
  }
  {
    intros Hn'.
    simpl in *.
    exact (findtc _ _ (Var n' Hn') (TCtl T)).
  }
Defined.

Goal (findtc (Var (t := CEtype) (ctx := [CEtype; CEtype]) 1 (eq_refl true)) [TEkinding; TEkinding]%TC) = TEkinding. Proof. exact eq_refl. Qed.

Class Coerce A B :=
  {
    coerce : A -> B
  }.

Notation "! a" := (coerce a) (at level 3, format "! a").

Definition var_to_size {ctx} (x : var CEexpr ctx) : size ctx := Svar (x, []).

Global Instance Coerce_var_size ctx : Coerce (var CEexpr ctx) (size ctx) :=
  {
    coerce := var_to_size (ctx := ctx)
  }.

Global Instance Coerce_tc_entry_type ctx : Coerce (tc_entry CEexpr ctx) (type ctx) :=
  {
    coerce := type_of_te (ctx := ctx)
  }.

Definition pair_to_Spair {ctx} (p : size ctx * size ctx) := Spair (fst p) (snd p).

Global Instance Coerce_prod_size ctx : Coerce (size ctx * size ctx) (size ctx) :=
  {
    coerce := pair_to_Spair (ctx := ctx)
  }.

Inductive typing {ctx} : tcontext ctx -> expr ctx -> type ctx -> cexpr ctx -> size ctx -> Prop :=
| TPvar Γ x : 
    typing Γ (Evar x) (cast (shiftby (firstn (S x) ctx) !(findtc x Γ)) (firstn_skipn _ ctx)) F0 !x
| TPapp Γ e₀ e₁ τ₁ c s τ₂ c₀ nouse c₁ s₁ : 
    typing Γ e₀ (Tarrow τ₁ c s τ₂) c₀ nouse ->
    typing Γ e₁ τ₁ c₁ s₁ ->
    typing Γ (Eapp e₀ e₁) (subst s₁ τ₂) (c₀ + c₁ + F1 + subst s₁ c) (subst s₁ s)
| TPabs T e t1 t2 c s :
    typing (ctx := _ ) (add_typing t1 T) e t2 c s ->
    typing T (Eabs t1 e) (Tarrow t1 c s t2) F0 S0
| TPtapp T e t2 c s t c' :
    typing T e (Tuniversal c s t) c' S0 ->
    typing T (Etapp e t2) (subst t2 t) (c' + F1 + c) s
| TPtabs T e c s t :
    typing (ctx := _) (add_kinding T) e t (shift1 CEtype c) (shift1 CEtype s) ->
    typing T (Etabs e) (Tuniversal c s t) F0 S0
| TPfold T e t c s t1 :
    t = Trecur t1 ->
    typing T e (subst t t1) c s ->
    typing T (Efold t e) t c (Sfold s)
| TPunfold Γ e τ c s s₁ τ₁ :
    typing Γ e τ c s ->
    is_fold s = Some s₁ ->
    τ = Trecur τ₁ ->
    typing Γ (Eunfold e) (subst τ τ₁) (c + F1) s₁
| TPhide T e t c s :
    typing T e t c s ->
    typing T (Ehide e) (Thide t) c (Shide s)
| TPunhide T e t c s s1 :
    typing T e (Thide t) c s ->
    is_hide s = Some s1 ->
    typing T (Eunhide e) t (c + F1) s1
| TPle T e t c c' s s' :
    typing T e t c s ->
    c <= c' ->
    s <= s' ->
    typing T e t c' s'
(* basic types - intro *)
| TPtt T :
    typing T Ett Tunit F0 S0
| TPpair T e1 t1 c1 s1 e2 t2 c2 s2 : 
    typing T e1 t1 c1 s1 ->
    typing T e2 t2 c2 s2 ->
    typing T (Epair e1 e2) (t1 * t2) (c1 + c2) !(s1, s2)
| TPinl T t e te c s:
    typing T e te c s ->
    typing T (Einl t e) (te + t) c (Sinlinr s S0)
| TPinr T t e te c s:
    typing T e te c s ->
    typing T (Einr t e) (t + te) c (Sinlinr S0 s)
(* basic types - elim *)
| TPfst T e t1 t2 c s s1 s2 :
    typing T e (t1 * t2) c s ->
    is_pair s = Some (s1, s2) ->
    typing T (Efst e) t1 (c + F1) s1
| TPsnd T e t1 t2 c s s1 s2 :
    typing T e (t1 * t2) c s ->
    is_pair s = Some (s1, s2) ->
    typing T (Esnd e) t2 (c + F1) s2
| TPmatch T e e1 e2 t1 t2 c s12 s1 s2 t c1 c2 s :
    typing T e (t1 + t2) c s12 ->
    typing (ctx := _) (add_typing t1 T) e1 (shift1 CEexpr t) c1 (shift1 CEexpr s) -> 
    typing (ctx := _) (add_typing t2 T) e2 (shift1 CEexpr t) c2 (shift1 CEexpr s) -> 
    is_inlinr s12 = Some (s1, s2) ->
    typing T (Ematch e t s e1 e2) t (c + F1 + max (subst s1 c1) (subst s2 c2)) s
.

