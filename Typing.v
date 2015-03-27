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

Instance Shift_option `{Shift A T} : Shift (fun ctx => option (T ctx)) :=
  {
    shift ctx new n b := option_map (shift (ctx := ctx) new n) b
  }.

Instance Shift_pair `{Shift A T1, Shift A T2} : Shift (fun ctx => T1 ctx * T2 ctx)%type :=
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

Infix ":::" := TCcons (at level 60, right associativity).

Local Open Scope prog_scope.

Definition add_typing {ctx} t T := TEtyping (ctx := ctx) t ::: T.
Definition add_kinding {ctx} T := TEkinding (ctx := ctx) ::: T.

Fixpoint add_typings {ctx} ls T :=
  match ls return tcontext (repeat CEexpr (length ls) ++ ctx) with
    | nil => T
    | t :: ls =>
      let T := add_typings ls T in
      add_typing (shift (repeat CEexpr (length ls)) 0 t) T
  end.

Unset Maximal Implicit Insertion.
Unset Implicit Arguments.

Inductive kinding {ctx} : tcontext ctx -> type ctx -> kind -> Prop :=
| Kvar T x : kinding T x 0
| Kapp T t1 t2 k :
    kinding T t1 (S k) ->
    kinding T t2 0 ->
    kinding T (Tapp t1 t2) k
| Kabs T t k :
    kinding (ctx := _) (add_kinding T) t k ->
    kinding T (Tabs t) (S k)
| Karrow T t1 c s t2 :
    kinding T t1 0 ->
    kinding (ctx := _) (add_typing t1 T) t2 0 ->
    kinding T (Tarrow t1 c s t2) 0
| Kuniversal T c s t :
    kinding (ctx := _) (add_kinding T) t 0 ->
    kinding T (Tuniversal c s t) 0
| Krecur T t :
    kinding (ctx := _) (add_kinding T) t 0 ->
    kinding T (Trecur t) 0
| Khide T t :
    kinding T t 0 ->
    kinding T (Thide t) 0
| Kunit T :
    kinding T Tunit 0
| Kprod T a b :
    kinding T a 0 ->
    kinding T b 0 ->
    kinding T (Tprod a b) 0
| Ksum T a b :
    kinding T a 0 ->
    kinding T b 0 ->
    kinding T (Tsum a b) 0
.

Inductive teq {ctx} : type ctx -> type ctx -> Prop :=
| Qrefl t : teq t t
| Qsymm a b : teq a b -> teq b a
| Qtrans a b c : teq a b -> teq b c -> teq a c
| Qabs a b :
    teq (ctx := _) a b ->
    teq (Tabs a) (Tabs b)
| Qapp a b a' b' :
    teq a a' ->
    teq b b' ->
    teq (Tapp a b) (Tapp a' b')
| Qbeta t1 t2 :
    teq (Tapp (Tabs t1) t2) (subst t2 t1)
| Qarrow a c s b a' b' : 
    teq a a' ->
    teq (ctx := _) b b' ->
    teq (Tarrow a c s b) (Tarrow a' c s b')
| Qrecur a b :
    teq (ctx := _) a b ->
    teq (Trecur a) (Trecur b)
| Qprod a b a' b' :
    teq a a' ->
    teq b b' ->
    teq (Tprod a b) (Tprod a' b')
| Qsum a b a' b' :
    teq a a' ->
    teq b b' ->
    teq (Tsum a b) (Tsum a' b')
.

Global Add Parametric Relation ctx : (type ctx) (@teq ctx)
    reflexivity proved by Qrefl
    symmetry proved by Qsymm
    transitivity proved by Qtrans
      as teq_rel.

Class Equal t :=
  {
    equal : t -> t -> Prop
  }.

Infix "==" := equal (at level 70) : G.

Instance Equal_type ctx : Equal (type ctx) :=
  {
    equal := @teq ctx
  }.

Local Open Scope F.
Local Open Scope G.

Local Open Scope prog_scope.

Notation Tuniversal0 := (Tuniversal F0 S0).

(* Set Maximal Implicit Insertion. *)
(* Set Implicit Arguments. *)

Definition shiftby `{Shift A T} {ctx} new b := shift (ctx := ctx) new 0 b.

Coercion type_of_te {ctx} (e : tc_entry CEexpr ctx) : type ctx :=
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

Goal (findtc (Var (t := CEtype) (ctx := [CEtype; CEtype]) 1 (eq_refl true)) (TEkinding ::: TEkinding ::: TCnil)) = TEkinding. Proof. exact eq_refl. Qed.

Coercion var_to_size {ctx} (x : var CEexpr ctx) : size ctx := Svar (x, []).

Inductive typing {ctx} : tcontext ctx -> expr ctx -> type ctx -> cexpr ctx -> size ctx -> Prop :=
| TPvar Γ x : 
    typing Γ (Evar x) (cast (shiftby (firstn (S x) ctx) (type_of_te (findtc x Γ))) (firstn_skipn _ ctx)) F0 (Svar' [] x)
| TPapp Γ e₀ e₁ τ₁ c s τ₂ c₀ nouse c₁ s₁ : 
    typing Γ e₀ (Tarrow τ₁ c s τ₂) c₀ nouse ->
    typing Γ e₁ τ₁ c₁ s₁ ->
    typing Γ (Eapp e₀ e₁) (subst s₁ τ₂) (c₀ + c₁ + subst s₁ c) (subst s₁ s)
| TPabs T e t1 t2 c s :
    kinding T t1 0 ->
    typing (ctx := _ ) (add_typing t1 T) e t2 c s ->
    typing T (Eabs t1 e) (Tarrow t1 c s t2) F0 S0
| TPtapp T e t2 c s t c' :
    typing T e (Tuniversal c s t) c' S0 ->
    typing T (Etapp e t2) (subst t2 t) (c' + c) s
| TPtabs T e c s t :
    typing (ctx := _) (add_kinding T) e t (shift1 CEtype c) (shift1 CEtype s) ->
    typing T (Etabs e) (Tuniversal c s t) F0 S0
| TPlet T t1 e1 e2 t2 c1 c2 s1 s2:
    typing T e1 t1 c1 s1 ->
    typing (ctx := _) (add_typing t1 T) e2 t2 c2 s2 ->
    typing T (Elet e1 e2) (subst s1 t2) (c1 + subst s1 c2) (subst s1 s2)
| TPfold T e t c s t1 :
    t == Trecur t1 ->
    typing T e (subst t t1) c s ->
    typing T (Efold t e) t c (Sfold s)
| TPunfold T e t c s s1 t1 :
    typing T e t c s ->
    is_fold s = Some s1 ->
    t == Trecur t1 ->
    typing T (Eunfold e) (subst t t1) (F1 + c) s1
| TPhide T e t c s :
    typing T e t c s ->
    typing T (Ehide e) (Thide t) c (Shide s)
| TPunhide T e t c s s1 :
    typing T e (Thide t) c s ->
    is_hide s = Some s1 ->
    typing T (Eunhide e) t c s1
| TPeq T e t1 t2 c s :
    typing T e t1 c s ->
    t1 == t2 ->
    typing T e t2 c s
| TPsub T e t c c' s s' :
    typing T e t c s ->
    c <<= c' ->
    s <= s' ->
    typing T e t c' s'
(* basic types - intro *)
| TPtt T :
    typing T Ett Tunit F0 S0
| TPpair T e1 t1 c1 s1 e2 t2 c2 s2 : 
    typing T e1 t1 c1 s1 ->
    typing T e2 t2 c2 s2 ->
    typing T (Epair e1 e2) (Tprod t1 t2) (c1 + c2) (Spair s1 s2)
| TPinl T t e te c s:
    typing T e te c s ->
    typing T (Einl t e) (Tsum te t) c (Sinlinr s S0)
| TPinr T t e te c s:
    typing T e te c s ->
    typing T (Einr t e) (Tsum t te) c (Sinlinr S0 s)
(* basic types - elim *)
| TPmatch_pair T e (e' : expr (CEexpr :: CEexpr :: ctx)) (t : type (CEexpr :: CEexpr :: ctx)) t1 t2 c s c' s' s1 s2 :
    typing T e (Tprod t1 t2) c s ->
    let T' := add_typings [t2; t1] T in
    typing (ctx := _) T' e' t c' s' ->
    is_pair s = Some (s1, s2) ->
    let sizes := [s2; s1] in
    typing T (Ematch_pair e e') (subst_list sizes t) (c + subst_list sizes c') (subst_list sizes s')
| TPmatch_sum T e e1 e2 t1 t2 c s s1 s2 t c1 c2 s' s1' s2' :
    typing T e (Tsum t1 t2) c s ->
    typing (ctx := _) (add_typing t1 T) e1 (shift1 CEexpr t) c1 s1' -> 
    typing (ctx := _) (add_typing t2 T) e2 (shift1 CEexpr t) c2 s2' -> 
    is_inlinr s = Some (s1, s2) ->
    subst s1 s1' <= s' ->
    subst s2 s2' <= s' ->
    typing T (Ematch_sum e e1 e2) t (c + max (subst s1 c1) (subst s2 c2)) s'
.

