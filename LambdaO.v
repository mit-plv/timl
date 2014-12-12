Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 
Generalizable All Variables.

Require Import String List.
Require Import OrderedType.
Require FMapAVL.
Module Map := FMapAVL.
Require Import OrderedTypeEx.
Module NatMap := Map.Make Nat_as_OT.

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

Fixpoint range begin len :=
  match len with
    | 0 => nil
    | S n => begin :: range (S begin) n
  end.

Import ListNotations.
Open Scope list_scope.

Definition assoc_list A B := list (A * B).

Class Functor F :=
  {
    map : forall A B, (A -> B) -> F A -> F B
  }.

Instance Functor_list : Functor list :=
  {
    map := List.map
  }.

Instance Functor_option : Functor option :=
  {
    map := option_map
  }.

Definition map_snd {A B C} (f : B -> C) (p : A * B) := (fst p, f (snd p)).

Definition map_assoc_list A B C (f : B -> C) (ls : assoc_list A B) := map (map_snd f) ls.

Instance Functor_assoc_list A : Functor (assoc_list A) :=
  {
    map := @map_assoc_list A
  }.

Section LambdaO.

  Inductive var :=
    | Vbound : nat -> var
    | Vfree : string -> var
  .

  Coercion Vbound : nat >-> var.
  Coercion Vfree : string >-> var.

  (* kinds are restricted to the form (* => * => ... => *). 0 means * *)
  Definition kind := nat.

  (* conventional System F types, which will only be part of a type *)
  Inductive typesig :=
  | Tarrow (t1 t2 : typesig)
  (* basic types *)
  | Tunit
  | Tprod (t1 t2 : typesig)
  | Tsum (t1 t2 : typesig)
  (* polymorphism *)           
  | Tvar (x : var)
  | Tuniversal (t : typesig)
  (* higher-order operators *)
  | Tabs (t : typesig)
  | Tapp (a b : typesig)
  (* recursive types *)         
  | Trecur (t : typesig)
  .

  Coercion Tvar : var >-> typesig.

  (* 
    There are four statistics (or 'sizes') for each value and its children:
    s1 : number of constructor invocations to construct this value (only this type's constructors)
    s2 : depth of constructor invocations to construct this value (only this type's constructors)
    s3 : number of constructor invocations to construct this value (all types' constructors)
    s4 : depth of constructor invocations to construct this value (all types' constructors)
    For example,
      for lists, s1 correspond to its length; s2 is the same as s1;
      for trees, s1 corresponds to its number of nodes; s2 corresponds to its depth.
    s3 corresponds to the amount of memory a value needs.
  *)

  Definition stat_idx := nat. (* An index indication the statistics you want. Should be 'I_4 *)
  Definition path := list nat. (* The query path into a descendent *)
  Definition var_path := (var * path)%type.

  Inductive formula :=
  | Fvar (x : var_path) (stat : stat_idx)
  | F0 
  | F1
  | Fplus (n1 n2 : formula)
  | Fminus (n1 n2 : formula)
  | Fmult (n1 n2 : formula)
  | Fdiv (n1 n2 : formula)
  | Flog (n : formula)
  | Fexp (n : formula)
  .

  Definition tuple4 A := (A * A * A * A)%type.

  Definition map_tuple4 A B (f : A -> B) (x : tuple4 A) := 
    match x with (x0, x1, x2, x3) => (f x0, f x1, f x2, f x3) end.

  Instance Functor_tuple4 : Functor tuple4 := 
    {
      map := map_tuple4
    }.

  Definition stats := tuple4 formula.

  Inductive size :=
  | Svar (x : var_path)
  | Sconst (_ : stats)
  | Sinl (_ : stats) (_ : size)
  | Sinr (_ : stats) (_ : size)
  | Sinlinr (_ : stats) (a b: size)
  | Spair (_ : stats) (a b: size)
  .

  Fixpoint map_size (f : var -> var) (g : formula -> formula) (s : size) {struct s} : size :=
    match s with
      | Svar (x, path) => Svar ((f x), path)
      | Sconst stats => Sconst (map g stats)
      | Sinl stats s => Sinl (map g stats) (map_size f g s)
      | Sinr stats s => Sinr (map g stats) (map_size f g s)
      | Sinlinr stats a b => Sinlinr (map g stats) (map_size f g a) (map_size f g b)
      | Spair stats a b => Sinlinr (map g stats) (map_size f g a) (map_size f g b)
    end.

  (* the second part is the information of time-cost and result-size on each 'arrow' in the type signature, which we call 'profile' *)
  Inductive profile :=
  | Parrow (a : profile) (time_cost : formula) (result_size : size) (b : profile)
  | Pleaf.

  Definition type := (typesig * profile)%type.

  Definition append_path (x : var_path) p : var_path := (fst x, snd x ++ [p]).

  Definition tuple4indices : tuple4 nat := (0, 1, 2, 3).

  (* derive a size structure from a variable (with path) x *)
  Definition destruct_var (x : var_path) (t : typesig) :=
    let stats := map (Fvar x) tuple4indices in
    match t with
      | Tprod _ _ =>
        Spair stats (Svar (append_path x 0)) (Svar (append_path x 0))
      | Tsum _ _ =>
        Sinlinr stats (Svar (append_path x 0)) (Svar (append_path x 0))
      | _ => 
        (* all the other types (Tarrow, Tvar, Tuniversal) don't have interesting size information *)
        Sconst stats
    end.

  Definition destruct_size s t := 
    match s with
      | Svar x => destruct_var x t
      | _ => s
    end.
 
  Infix "+" := Fplus : formula_scope.
  Delimit Scope formula_scope with F.
  Infix "-" := Fminus : F.
  Infix "*" := Fmult : F.
  Infix "/" := Fdiv : F.
  Open Scope F.

  Inductive constr :=
  | Ctt
  | Cpair
  | Cinl
  | Cinr
  .

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
    | Ematch_pair (target : expr) (_ : expr)
    | Ematch_sum (target : expr) (left right : expr)
    | Etapp (e : expr) (t : type)
    | Etabs (body : expr)
    | Efold (_ : expr) (_ : type)
    | Eunfold (_ : expr) (_ : type)
  .

  Definition letrec_entry := (type * type * expr)%type.

  Coercion Evar : var >-> expr.
  Coercion Econstr : constr >-> expr.

  Inductive IsOpaque : expr -> Prop :=
    | OPvar x : IsOpaque (Evar x)
    | OPconstr c : IsOpaque (Econstr c)
  .

  Inductive general_arg :=
    | Aapp (_ : expr)
    | Atapp (_ : type)
    | Afold (_ : type)
    | Aunfold (_ : type)
  .

  Definition general_apply (f : expr) (a : general_arg) :=
    match a with
      | Aapp e => Eapp f e
      | Atapp t => Etapp f t
      | Afold t => Efold f t
      | Aunfold t => Eunfold f t
    end.

  Definition general_apply_many f args := fold_left general_apply args f.

  Definition app_many f args := fold_left Eapp args f.

  Inductive IsValue : expr -> Prop :=
  | Vabs t e : IsValue (Eabs t e)
  | Vapp f args : 
      IsOpaque f ->
      (forall a, In (Aapp a) args -> IsValue a) ->
      IsValue (general_apply_many f args)
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
    | CTmatch_pair (target : context) (_ : expr)
    | CTmatch_sum (target : context) (a b : expr)
    | CTtapp (f : context) (t : type)
    | CTfold (_ : context) (t : type)
    | CTunfold (_ : context) (t : type)
  .

  Fixpoint plug (c : context) (e : expr) : expr :=
    match c with
      | CTempty => e
      | CTapp1 f arg => Eapp (plug f e) arg
      | CTapp2 f arg _ => Eapp f (plug arg e)
      | CTlet t def main => Elet t (plug def e) main
      | CTletrec defs main => Eletrec defs (plug main e)
      | CTmatch_pair target k => Ematch_pair (plug target e) k
      | CTmatch_sum target a b => Ematch_sum (plug target e) a b
      | CTtapp f t => Etapp (plug f e) t
      | CTfold f t => Efold (plug f e) t
      | CTunfold f t => Eunfold (plug f e) t
    end.

  Class Subst value body :=
    {
      subst : value -> body -> body
    }.

  Definition subst_var_var (v b : var) : var.
    admit.
  Defined.

  Instance Subst_var_var : Subst var var :=
    {
      subst := subst_var_var
    }.

  Definition subst_e_e (v : expr) (e : expr) : expr.
    admit.
  Defined.

  Instance Subst_expr_expr : Subst expr expr :=
    {
      subst := subst_e_e
    }.

  Definition subst_t_e (t : type) (e : expr) : expr.
    admit.
  Defined.

  Instance Subst_type_expr : Subst type expr :=
    {
      subst := subst_t_e
    }.
    
  Class Find key value container := 
    {
      find : key -> container -> option value
    }.

  Instance Find_list A : Find nat A (list A) :=
    {
      find k c := @nth_error A c k
    }.
      
  Definition subst_many `{Subst V B} values e := fold_left (flip subst) values e.

  Definition e_pair (a b : expr) := Eapp (Eapp (Econstr Cpair) a) b.
  Definition e_inl (a : expr) := Eapp (Econstr Cinl) a.
  Definition e_inr (a : expr) := Eapp (Econstr Cinr) a.

  Inductive step : expr -> expr -> Prop :=
    | STcontext c e1 e2 : step e1 e2 -> step (plug c e1) (plug c e2)
    | STapp t body arg : IsValue arg -> step (Eapp (Eabs t body) arg) (subst arg body)
    | STlet t v main : IsValue v -> step (Elet t v main) (subst v main)
    | STletrec_instantiate defs c (n : nat) t e : 
        find n defs = Some (t, e) -> 
        step (Eletrec defs (plug c (Evar n))) (Eletrec defs (plug c e))  (* the definitions are only simplified, but not making any recursive or mutual-recursive call. All these calls are made only in the evaluation of 'main' *)
    | STletrec_finish defs v : IsValue v -> step (Eletrec defs v) v
    | STmatch_pair a b k : 
        IsValue a ->
        IsValue b ->
        step (Ematch_pair (e_pair a b) k) (subst_many [a; b] k)
    | STmatch_inl v k1 k2 : 
        IsValue v ->
        step (Ematch_sum (e_inl v) k1 k2) (subst v k1)
    | STmatch_inr v k1 k2 : 
        IsValue v ->
        step (Ematch_sum (e_inr v) k1 k2) (subst v k2)
    | STtapp body t : step (Etapp (Etabs body) t) (subst t body)
    | STunfold_fold v t1 t2 : 
        IsValue v ->
        step (Eunfold (Efold v t1) t2) v
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

  Definition subst_t_t (t2 : type) (t : type) : type.
    admit.
  Defined.

  Definition subst_size_formula (s : size) (f : formula) : formula.
    admit.
  Defined.

  Instance Subst_size_formula : Subst size formula :=
    {
      subst := subst_size_formula
    }.

  Definition subst_size_profile (s : size) (p : profile) : profile.
    admit.
  Defined.

  Instance Subst_size_profile : Subst size profile :=
    {
      subst := subst_size_profile
    }.

  Definition subst_size_size (v b : size) : size.
    admit.
  Defined.

  Instance Subst_size_size : Subst size size :=
    {
      subst := subst_size_size
    }.

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

  Fixpoint repeat A (a : A) n :=
    match n with
      | 0 => nil
      | S n => a :: repeat a n
    end.

  Definition ones := repeat F1.

  Definition add_many A ls m := fold_left (fun m p => @StringMap.add A (fst p) (snd p) m) ls m.

  Arguments fst {A B} _.

  Inductive typing : tcontext -> expr -> type -> formula -> size -> Prop :=
  | TPvar T (x : string) t : find x T = Some (TEtyping t) -> typing T x t F1 (Svar (x : var, []))
  | TPapp T e1 e2 ta tb pa f g pb n1 n2 s1 s2 : 
      typing T e1 (Tarrow ta tb, Parrow pa f g pb) n1 s1 ->
      typing T e2 (ta, pa) n2 s2 ->
      typing T (Eapp e1 e2) (tb, subst s2 pb) (n1 + n2 + subst s2 f)%F (subst s2 g).
(*here*)
  | TPabs T x t1 e t2 n s:
      ~ StringMap.In x T -> 
      typing (StringMap.add x (TEtyping t1) T) e t2 n s ->
      typing T (Eabs t1 (abs x e)) (Tarrow t1 (abs_f x n) (map (abs_f x) s) (abs_t x t2)) F1 []
  | TPtapp T e t2 t n:
      typing T e (Tuniversal t) n [] ->
      let t' := subst_t_t t2 t in
      typing T (Etapp e t2) t' n (ones $ dim t')
  | TPtabs T X e t s:
      ~ StringMap.In X T ->
      typing (StringMap.add X TEtypevar T) e t F1 s ->
      typing T (Etabs (abs X e)) (Tuniversal (abs_t X t)) F1 []
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
      
End LambdaO.

  Variable constr : Type.
  Variable arity : constr -> nat.
  Variable place : constr -> nat.



Definition arity c :=
  match c with
    | Ctt => 0
    | Cpair => 2
    | Cinl => 1
    | Cinr => 1
    | Cnil => 0
    | Ccons => 2
  end.

Definition place c :=
  match c with
    | Ctt => 0
    | Cpair => 0
    | Cinl => 0
    | Cinr => 1
    | Cnil => 0
    | Ccons => 1
  end.

Coercion var_to_formula (x : var) := Fvar x 0.

Notation "# n" := (Vbound n) (at level 0).
Infix "@" := Fvar (at level 10).

Axiom TPpair : forall T, typing T Cpair (Tuniversal $ Tuniversal $ Tarrow #1 F1 [] $ Tarrow #1 F1 [#1@0; #0@0] $ Tprod #3 #2) F0 []

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

