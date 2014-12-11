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
    | Vbound : nat -> var
    | Vfree : string -> var
  .

  Coercion Vbound : nat >-> var.
  Coercion Vfree : string >-> var.

  (* conventional System F types, which will only be part of a type *)
  Inductive typesig :=
  | Tunit
  | Tprod (t1 t2 : typesig)
  | Tsum (t1 t2 : typesig)
  | Tlist (elm : typesig)
  | Tarrow (t1 t2 : typesig)
  | Tvar (x : var)
  | Tabs (t : typesig)
  .

  Coercion Tvar : var >-> typesig.

  Inductive formula :=
  | Fvar (x : var) (field : nat)
  | F0 
  | F1
  | Fplus (n1 n2 : formula)
  | Fminus (n1 n2 : formula)
  | Fmult (n1 n2 : formula)
  | Fdiv (n1 n2 : formula)
  | Flog (n : formula)
  | Fexp (n : formula)
  .

  Coercion var_to_formula (x : var) := Fvar x 0.

  Infix "+" := Fplus : formula_scope.
  Delimit Scope formula_scope with F.
  Infix "-" := Fminus : F.
  Infix "*" := Fmult : F.
  Infix "/" := Fdiv : F.
  Open Scope F.

  (* the second part is the information of time-cost and result-size on each 'arrow' in the type signature *)
  Definition type := (typesig * list (formula * formula))%type.

  Inductive expr :=
    | Evar (x : var)
    | Econstr (c : constr)
    | Eapp (f : expr) (arg : expr)
    | Eabs (t : type) (body : expr)
    | Elet (t : type) (def : expr) (main : expr)
    (* 'Definition' means the RHS of := in letrec.
       Each definition must be a function, so there is an implicit quantifier on the RHS of :=. The LHS of := are also implicitly quantified. For example:
       letrec x := \a. a * x (a - 1) with
              y := \b. b * y (b - 1) in
              x 10 + y 20
       is written as 
       letrec #0 * #2 (#0 - 1) with   (#2, #1, #0 -> x, y, a)
              #0 * #1 (#0 - 1) in     (#2, #1, #0 -> x, y, b)
              #1 10 + #0 10           (#1, #0 -> x, y)  
       This must-be-function restriction is necessary for the type system to work 
    *)
    | Eletrec (defs : list (type * type * expr)) (main : expr)
    | Ematch (target : expr) (branches : list (constr * expr))
    | Etapp (e : expr) (t : type)
    | Etabs (body : expr)
  .

  Definition letrec_entry := (type * type * expr)%type.

  Coercion Evar : var >-> expr.
  Coercion Econstr : constr >-> expr.

  Inductive IsOpaque : expr -> Prop :=
    | OPvar x : IsOpaque (Evar x)
    | OPconstr c : IsOpaque (Econstr c)
  .

  Definition apply_many f args := fold_left (fun f x => match x with inl e => Eapp f e | inr t => Etapp f t end) args f.

  Definition app_many f args := fold_left Eapp args f.

  Inductive IsValue : expr -> Prop :=
  | Vabs t e : IsValue (Eabs t e)
  | Vapp f args : 
      IsOpaque f ->
      (forall a, In (inl a) args -> IsValue a) ->
      IsValue (apply_many f args)
  .
  
  Infix "<<" := compose (at level 40) : prog_scope.
  Infix ">>" := (flip compose) (at level 40) : prog_scope.
  Definition apply {A B} (f : A -> B) x := f x.
  Infix "$" := apply (at level 85, right associativity) : prog_scope.
  Open Scope prog_scope.
  
  Arguments snd {A B} _.

  Inductive context :=
    | CTempty
    | CTapp1 (f : context) (arg : expr)
    | CTapp2 (f : expr) (arg : context) : IsValue f -> context
    | CTlet (t : type) (def : context) (main : expr)
    | CTletrec (defs : list letrec_entry) (main : context) (* Only evaluate main. All the definitions are already values, since that are all functions *)
    | CTmatch (target : context) (branches : list (constr * expr))
    | CTtapp (f : context) (t : type)
  .

  Import ListNotations.
  Open Scope list_scope.

  Fixpoint plug (c : context) (e : expr) : expr :=
    match c with
      | CTempty => e
      | CTapp1 f arg => Eapp (plug f e) arg
      | CTapp2 f arg _ => Eapp f (plug arg e)
      | CTlet t def main => Elet t (plug def e) main
      | CTletrec defs main => Eletrec defs (plug main e)
      | CTmatch target branches => Ematch (plug target e) branches
      | CTtapp f t => Etapp (plug f e) t
    end.

  Definition subst (v : expr) (e : expr) : expr.
    admit.
  Defined.

  Definition subst_t_t (t2 : type) (t : type) : type.
    admit.
  Defined.

  Definition subst_t (t : type) (e : expr) : expr.
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

  Definition subst_many e values := fold_left (flip subst) values e.

  Inductive step : expr -> expr -> Prop :=
    | STcontext c e1 e2 : step e1 e2 -> step (plug c e1) (plug c e2)
    | STapp t body arg : IsValue arg -> step (Eapp (Eabs t body) arg) (subst arg body)
    | STlet t v main : IsValue v -> step (Elet t v main) (subst v main)
    | STletrec_instantiate defs c (n : nat) t e : 
        find n defs = Some (t, e) -> 
        step (Eletrec defs (plug c (Evar n))) (Eletrec defs (plug c e))  (* the definitions are only simplified, but not making any recursive or mutual-recursive call. All these calls are made only in the evaluation of 'main' *)
    | STletrec_finish defs v : IsValue v -> step (Eletrec defs v) v
    | STmatch_pair (c : constr) values branches e : 
        let n := arity c in
        find c branches = Some e -> 
        length values = n ->
        Forall IsValue values ->
        step (Ematch (app_many c values) branches) (subst_many e values)
    | STtapp body t : step (Etapp (Etabs body) t) (subst_t t body)
  .

  (* typing context *)
  Inductive tc_entry := 
    | TEtyping (t : type)
    | TEtypevar.

  Definition tcontext := StringMap.t tc_entry.

  Instance Find_StringMap A : Find string A (StringMap.t A) :=
    {
      find k c := StringMap.find k c
    }.

  Fixpoint range begin len :=
    match len with
      | 0 => nil
      | S n => begin :: range (S begin) n
    end.

  Definition subst_f (s : list formula) (f : formula) : formula.
    admit.
  Defined.

  Definition subst_f_t (s : list formula) (t : type) : type.
    admit.
  Defined.

  Definition substx_f (x : string) (s : list formula) (f : formula) : formula.
    admit.
  Defined.

  Definition abs (x : string) (e : expr) : expr.
    admit.
  Defined.

  Definition abs_f (x : string) (f : formula) : formula.
    admit.
  Defined.

  Definition abs_t (x : string) (t : type) : type.
    admit.
  Defined.

  Notation "# n" := (Vbound n) (at level 0).
  Infix "@" := Fvar (at level 10).

  Fixpoint repeat A (a : A) n :=
    match n with
      | 0 => nil
      | S n => a :: repeat a n
    end.

  Definition ones := repeat F1.

  Definition add_many A ls m := fold_left (fun m p => @StringMap.add A (fst p) (snd p) m) ls m.

  Arguments fst {A B} _.

  Inductive size :=
  | Size (s1 s2 s3 s4 : formula) (children : list size)
  .

  Inductive typing : tcontext -> expr -> type -> formula -> list formula -> Prop :=
  | TPvar T (x : string) t : find x T = Some (TEtyping t) -> typing T x t F1 (size_vars x t)
  | TPpair T : typing T Cpair (Tabs $ Tabs $ Tarrow #1 F1 [] $ Tarrow #1 F1 [#1@0; #0@0] $ Tprod #3 #2) F0 []
  | TPapp T e1 e2 t1 t2 f g n1 n2 s1 s2 : 
      typing T e1 (Tarrow t1 f g t2) n1 s1 ->
      typing T e2 t2 n2 s2 ->
      typing T (Eapp e1 e2) (subst_f_t s2 t2) (n1 + n2 + subst_f s2 f)%F (map (subst_f s2) g)
  | TPabs T x t1 e t2 n s:
      ~ StringMap.In x T -> 
      typing (StringMap.add x (TEtyping t1) T) e t2 n s ->
      typing T (Eabs t1 (abs x e)) (Tarrow t1 (abs_f x n) (map (abs_f x) s) (abs_t x t2)) F1 []
  | TPtapp T e t2 t n:
      typing T e (Tabs t) n [] ->
      let t' := subst_t_t t2 t in
      typing T (Etapp e t2) t' n (ones $ dim t')
  | TPtabs T X e t s:
      ~ StringMap.In X T ->
      typing (StringMap.add X TEtypevar T) e t F1 s ->
      typing T (Etabs (abs X e)) (Tabs (abs_t X t)) F1 []
  | TPlet T t1 e1 e2 t2 n1 n2 s1 s2 x:
      typing T e1 t1 n1 s1 ->
      ~ StringMap.In x T ->
      typing (StringMap.add x (TEtyping t1) T) e2 t2 n2 s2 ->
      typing T (Elet t1 e1 (abs x e2)) t2 (n1 + substx_f x s1 n2)%F (map (substx_f x s1) s2)
  | TPletrec T (defs : list letrec_entry) main t n s xs :
      length xs = length defs ->
      NoDup xs ->
      (forall x, In x xs -> ~ StringMap.In x T) ->
      let T' := add_many (combine xs $ map (fst >> fst >> TEtyping) defs) T in
      (forall lhs_ti rhs_ti ei, In (lhs_ti, rhs_ti, ei) defs -> typing T' (Eabs rhs_ti ei) lhs_ti F1 []) ->
      typing T' main t n s ->
      typing T (Eletrec defs main) t n s.
      