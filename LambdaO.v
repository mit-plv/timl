Set Implicit Arguments.

Inductive constr :=
| Ctt
| Cpair
| Cinl
| Cinr
| Cnil
| Ccons.

Fixpoint arity c :=
  match c with
    | Ctt => 0
    | Cpair => 2
    | Cinl => 1
    | Cinr => 1
    | Cnil => 0
    | Ccons => 2
  end.

Require Import String List.
Require Import OrderedType.
Require FMapAVL.
Module Map := FMapAVL.
Require Import OrderedTypeEx.
Module NatMap := Map.Make Nat_as_OT.

Module Constr_as_MOT <: MiniOrderedType.

  Definition t := constr.

  Definition eq := @eq t.

  Definition lt (x y : t) : Prop.
    admit.
  Defined.

  Lemma eq_refl : forall x : t, eq x x.
    admit.
  Qed.

  Lemma eq_sym : forall x y : t, eq x y -> eq y x.
    admit.
  Qed.

  Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
    admit.
  Qed.

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
    admit.
  Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
    admit.
  Qed.

  Definition compare : forall x y : t, Compare lt eq x y.
    admit.
  Defined.

End Constr_as_MOT.

Module Constr_as_OT := MOT_to_OT Constr_as_MOT.
Require Import OrdersAlt.
Module Constr_as_OT_new := Update_OT Constr_as_OT.
Require Import Equalities.
Module Constr_as_UDT := Make_UDT Constr_as_OT.

Module ConstrMap := Map.Make Constr_as_OT.

Module String_as_MOT <: MiniOrderedType.

  Definition t := string.

  Definition eq := @eq t.

  Definition lt (x y : t) : Prop.
    admit.
  Defined.

  Lemma eq_refl : forall x : t, eq x x.
    admit.
  Qed.

  Lemma eq_sym : forall x y : t, eq x y -> eq y x.
    admit.
  Qed.

  Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
    admit.
  Qed.

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
    admit.
  Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
    admit.
  Qed.

  Definition compare : forall x y : t, Compare lt eq x y.
    admit.
  Defined.

End String_as_MOT.

Module String_as_OT := MOT_to_OT String_as_MOT.
Require Import OrdersAlt.
Module String_as_OT_new := Update_OT String_as_OT.
Require Import Equalities.
Module String_as_UDT := Make_UDT String_as_OT.

Module StringMap := Map.Make String_as_OT.

Section LambdaO.

  Inductive var :=
    | VBound : nat -> var
    | VFree : string -> var
  .

  Coercion VBound : nat >-> var.
  Coercion VFree : string >-> var.

  Inductive metric :=
  | Mvar (x : var) (field : nat)
  | M0 
  | M1
  | Mplus (n1 n2 : metric)
  | Mminus (n1 n2 : metric)
  | Mmult (n1 n2 : metric)
  | Mdiv (n1 n2 : metric)
  | Mlog (n : metric)
  | Mexp (n : metric)
  .

  Infix "+" := Mplus : metric_scope.
  Delimit Scope metric_scope with M.
  Infix "-" := Mminus : M.
  Infix "*" := Mmult : M.
  Infix "/" := Mdiv : M.
  Open Scope M.

  Inductive type :=
  | Tunit
  | Tprod (t1 t2 : type)
  | Tsum (t1 t2 : type)
  | Tlist (elm : type)
  | Tarrow (t1 t2 : type) (cost result_size : metric).

  Inductive expr :=
    | Evar (x : var)
    | Econstr (c : constr)
    | Eapp (f : expr) (arg : expr)
    | Eabs (t : type) (body : expr)
    | Elet (t : type) (def : expr) (main : expr)
    | Eletrec (defs : list (type * expr)) (main : expr)
    | Ematch (target : expr) (branches : list (constr * expr))
    | Etapp (e : expr) (t : type)
    | Etabs (body : expr)
  .

  Coercion Evar : var >-> expr.
  Coercion Econstr : constr >-> expr.

  Inductive IsOpaque : expr -> Prop :=
    | OPvar x : IsOpaque (Evar x)
    | OPconstr c : IsOpaque (Econstr c)
  .

  Definition apply_many f args := fold_left Eapp args f.

  Inductive IsValue : expr -> Prop :=
  | Vabs t e : IsValue (Eabs t e)
  | Vapp f args : 
      IsOpaque f ->
      (forall a, In a args -> IsValue a) ->
      IsValue (apply_many f args)
  .
  
  Inductive context :=
    | CTempty
    | CTapp1 (f : context) (arg : expr)
    | CTapp2 (f : expr) (arg : context) : IsValue f -> context
    | CTlet (t : type) (def : context) (main : expr)
    | CTletrec (defs : list (type * expr)) (main : context)
    | CTmatch (target : context) (branches : list (constr * expr))
  .

  Fixpoint plug (c : context) (e : expr) : expr :=
    match c with
      | CTempty => e
      | CTapp1 f arg => Eapp (plug f e) arg
      | CTapp2 f arg _ => Eapp f (plug arg e)
      | CTlet t def main => Elet t (plug def e) main
      | CTletrec defs main => Eletrec defs (plug main e)
      | CTmatch target branches => Ematch (plug target e) branches
    end.

  Definition subst (e : expr) (v : expr) : expr.
    admit.
  Defined.

  Class Find key value container := 
    {
      find : key -> container -> option value
    }.

  Unset Strict Implicit.
  Unset Printing Implicit Defensive. 
  Generalizable All Variables.

  Instance Find_list A : Find nat A (list A) :=
    {
      find k c := @nth_error A c k
    }.
      
  Definition of_list A (ls : list (constr * A)) : ConstrMap.t A.
    admit.
  Defined.

  Instance Find_list_constr A : Find constr A (list (constr * A)) :=
    {
      find k c := ConstrMap.find k (of_list c)
    }.
      
  Definition Pair e1 e2 := Eapp (Eapp Cpair e1) e2.

  Definition subst_many e values := fold_left subst values e.

  Inductive step : expr -> expr -> Prop :=
    | STcontext c e1 e2 : step e1 e2 -> step (plug c e1) (plug c e2)
    | STbeta t body arg : IsValue arg -> step (Eapp (Eabs t body) arg) (subst body arg)
    | STlet t v main : IsValue v -> step (Elet t v main) (subst main v)
    | STletrec_instantiate defs c (n : nat) t e : 
        find n defs = Some (t, e) -> 
        step (Eletrec defs (plug c (Evar n))) (Eletrec defs (plug c e)) 
    | STletrec_finish defs v : IsValue v -> step (Eletrec defs v) v
    | STmatch_pair (c : constr) values branches e : 
        let n := arity c in
        find c branches = Some e -> 
        length values = n ->
        Forall IsValue values ->
        step (Ematch (apply_many c values) branches) (subst_many e values)
  .

  (* typing context *)
  Inductive tc_entry := 
    | TEtype (t : type)
    | TEtype_var.

  Definition tcontext := StringMap.t tc_entry.

  Instance Find_StringMap A : Find string A (StringMap.t A) :=
    {
      find k c := StringMap.find k c
    }.
      
  Inductive typing : tcontext -> expr -> type -> metric -> metric -> Prop :=
  | TPvar T (x : string) t : find x T = Some t -> typing T x t M0 x.
  | TPapp : 
      typing T e1 (Tarrow t1 t2 f g) n1 s1 ->
      typing T e2 t2 n2 s2 ->
      typing T (Eapp e1 e2) t2 (n1 + n2 + subst_m f s2) (subst_m g s2)
  | TPabs :
      typing T (Eabs 
  | TPpair : typing T Cpair () M0 M1
      