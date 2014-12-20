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

  Infix "<<" := compose (at level 40) : prog_scope.
  Infix ">>" := (flip compose) (at level 40) : prog_scope.
  Definition apply {A B} (f : A -> B) x := f x.
  Infix "$" := apply (at level 85, right associativity) : prog_scope.
  Open Scope prog_scope.
  
  Inductive var :=
    | Vbound : nat -> var
    | Vfree : string -> var
  .

  Coercion Vbound : nat >-> var.
  Coercion Vfree : string >-> var.

  (* kinds are restricted to the form (* => * => ... => *). 0 means * *)
  Definition kind := nat.

  (* 
    There are four statistics (or 'sizes') for each value :
    s0 : number of invocations of 'fold' 
         (for parametric algebraic data types, this correspond to the number of constructor invocations to construct this value, not counting those from the parameter types);
    s1 : parallel version of s0, where the fields of a pair are max'ed instead of sum'ed;
    s2 : number of invocations of basic constrctors (tt, pair, inl, inr, lambda)
         (for parametric algebraic data types, this correspond to the number of constructor invocations to construct this value, counting those from the parameter types);
    s3 : parallel version of s2.

    For example, for lists, s0 correspond to its length; s1 is the same as s0;
      for trees, s0 corresponds to its number of nodes; s1 corresponds to its depth.
    s2 corresponds to the amount of memory a value occupies, and the cost of a computation that needs to, for example, look into each element of a list.
  *)

  Definition stat_idx := nat. (* An index indication the statistics you want. Should be 'I_4 *)
  Inductive path_command :=
  | Pfst
  | Psnd
  | Pinl
  | Pinr
  | Punfold
  .
  Definition path := list path_command. (* The query path into a inner-component *)
  Definition var_path := (var * path)%type.

  Variable formula : Type.
  Variable F1 : formula.
  Variable Fvar : var_path -> stat_idx -> formula.
  Variable Fplus Fmax : formula -> formula -> formula.
  Infix "+" := Fplus : formula_scope.
  Delimit Scope formula_scope with F.
  Open Scope F.

  Class Max t := 
    {
      max : t -> t -> t
    }.

  Instance Max_formula : Max formula :=
    {
      max := Fmax
    }.

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
  | Sstats (_ : stats)
  | Stt
  | Sinl (_ : size)
  | Sinr (_ : size)
  | Sinlinr (a b: size)
  | Spair (a b: size)
  | Sfold (_ : size)
  .

  Inductive tconstr :=
  | TCunit
  | TCprod
  | TCsum
  .

  Inductive type :=
  | Tarrow (t1 : type) (time_cost : formula) (result_size : size) (t2 : type)
  (* basic types *)
  | Tconstr (_ : tconstr)
  (* polymorphism *)           
  | Tvar (x : var)
  | Tuniversal (t : type)
  (* higher-order operators *)
  | Tabs (t : type)
  | Tapp (a b : type)
  (* recursive types *)         
  | Trecur (t : type)
  .

  Infix "$$$" := Tapp (at level 85, right associativity).

  Definition Tunit := Tconstr TCunit.
  Definition Tprod t1 t2 := Tconstr TCprod $$$ t1 $$$ t2.
  Definition Tsum t1 t2 := Tconstr TCsum $$$ t1 $$$ t2.

  Coercion Tvar : var >-> type.

  Definition append_path (x : var_path) p : var_path := (fst x, snd x ++ [p]).

(*
  Definition tuple4indices : tuple4 nat := (0, 1, 2, 3). 

  Definition get_stats (s : size) :=
    match s with
      | Svar x => map (Fvar x) tuple4indices
      | Sstruct stats _ => stats
    end.
*)

  Definition is_pair (s : size) :=
    match s with
      | Svar x => Some (Svar (append_path x Pfst), Svar (append_path x Psnd))
      | Spair a b => Some (a, b)
      | _ => None
    end.

  Definition is_inlinr (s : size) :=
    match s with
      | Svar x => Some (Svar (append_path x Pinl), Svar (append_path x Pinr))
      | Sinlinr a b => Some (a, b)
      | _ => None
    end.

  Definition is_fold (s : size) :=
    match s with
      | Svar x => Some (Svar (append_path x Punfold))
      | Sfold t => Some t
      | _ => None
    end.

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
    (* The handler can access #1 and #0 representing the components of the pair
     *)              
    | Ematch_pair (target : expr) (handler : expr)
    (* left and right can access #0 representing the corresponding payload *)
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
  .

  Definition general_apply (f : expr) (a : general_arg) :=
    match a with
      | Aapp e => Eapp f e
      | Atapp t => Etapp f t
      | Afold t => Efold f t
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

  (* substitute the outer-most bound variable *)
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
      
  Definition subst_list `{Subst V B} values e := fold_left (flip subst) values e.

  Instance Subst_list `{Subst V B} : Subst (list V) B := 
    {
      subst := subst_list
    }.

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
        step (Ematch_pair (e_pair a b) k) (subst [a; b] k)
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
    | TEtypevar
    | TEkinding (k : kind).

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

  Definition subst_size_type (s : size) (_ : type) : type.
    admit.
  Defined.

  Instance Subst_size_type : Subst size type :=
    {
      subst := subst_size_type
    }.

  Definition subst_size_size (v b : size) : size.
    admit.
  Defined.

  Instance Subst_size_size : Subst size size :=
    {
      subst := subst_size_size
    }.

  Definition subst_type_type (v b : type) : type.
    admit.
  Defined.

  Instance Subst_type_type : Subst type type :=
    {
      subst := subst_type_type
    }.

  (* substitute a free variable *)
  Class Substx value body :=
    {
      substx : string -> value -> body -> body
    }.

  Definition substx_size_formula (x : string) (v : size) (b : formula) : formula.
    admit.
  Defined.

  Instance Substx_size_formula : Substx size formula :=
    {
      substx := substx_size_formula
    }.

  Definition substx_size_size (x : string) (v : size) (b : size) : size.
    admit.
  Defined.

  Instance Substx_size_size : Substx size size :=
    {
      substx := substx_size_size
    }.

  Definition substx_size_type (x : string) (v : size) (b : type) : type.
    admit.
  Defined.

  Instance Substx_size_type : Substx size type :=
    {
      substx := substx_size_type
    }.

  Class Abs t := 
    {
      abs : string -> t -> t
    }.

  Definition abs_e (x : string) (e : expr) : expr.
    admit.
  Defined.

  Instance Abs_expr : Abs expr :=
    {
      abs := abs_e
    }.

  Definition subst_list_substx `{Substx V B} pairs body := fold_left (fun b p => substx (fst p) (snd p) b) pairs body.

  Instance Subst_list_substx `{Substx V B} : Subst (list (string * V)) B := 
    {
      subst := subst_list_substx
    }.

  Definition abs_f (x : string) (f : formula) : formula.
    admit.
  Defined.

  Instance Abs_formula : Abs formula :=
    {
      abs := abs_f
    }.

  Definition abs_p (x : string) (_ : type) : type.
    admit.
  Defined.

  Instance Abs_type : Abs type :=
    {
      abs := abs_p
    }.

  Definition abs_s (x : string) (s : size) : size.
    admit.
  Defined.

  Instance Abs_size : Abs size :=
    {
      abs := abs_s
    }.

  Definition abs_many `{Abs t} xs t := fold_left (flip abs) xs t.

  Fixpoint repeat A (a : A) n :=
    match n with
      | 0 => nil
      | S n => a :: repeat a n
    end.

  Definition ones := repeat F1.

  Definition add_many A ls m := fold_left (fun m p => @StringMap.add A (fst p) (snd p) m) ls m.

  Arguments fst {A B} _.

  Definition size1 := Stt.

  Inductive typesig :=
  | TSarrow (t1 t2 : typesig)
  | TSconstr (_ : tconstr)
  | TSvar (x : var)
  | TSuniversal (t : typesig)
  | TSabs (t : typesig)
  | TSapp (a b : typesig)
  | TSrecur (t : typesig)
  .

  Fixpoint sig (t : type) : typesig :=
    match t with
      | Tarrow a _ _ b => TSarrow (sig a ) (sig b)
      | Tconstr c => TSconstr c
      | Tvar x => TSvar x
      | Tuniversal t => TSuniversal (sig t)
      | Tabs t => TSabs (sig t)
      | Tapp a b => TSapp (sig a) (sig b)
      | Trecur t => TSrecur (sig t)
    end.

  Definition AllNotIn elt xs T := forall x, In x xs -> ~ @StringMap.In elt x T.

  Definition add_typing x t T := StringMap.add x (TEtyping t) T.

  Definition add_typings (ls : list (string * type)) T := add_many (map (map_snd TEtyping) ls) T.

  Definition add_kinding x k T := StringMap.add x (TEkinding k) T.

  Definition max_type (a b : type) : type.
    admit.
  Defined.

  Instance Max_type : Max type :=
    {
      max := max_type
    }.

  Definition max_size (a b : size) : size.
    admit.
  Defined.

  Instance Max_size : Max size :=
    {
      max := max_size
    }.

  Notation "# n" := (Vbound n) (at level 0).
  Coercion var_to_size (x : var) : size := Svar (x, []).

  Inductive kinding : tcontext -> type -> kind -> Prop :=
  | Kvar T (x : string) k : find x T = Some (TEkinding k) -> kinding T x k
  | Kapp T t1 t2 k :
      kinding T t1 (S k) ->
      kinding T t2 0 ->
      kinding T (Tapp t1 t2) k
  | Kabs T x t k :
      ~ StringMap.In x T ->
      kinding (add_kinding x 0 T) t k ->
      kinding T (Tabs (abs x t)) (S k)
  | Karrow T t1 f g t2 :
      kinding T t1 0 ->
      kinding T t2 0 ->
      kinding T (Tarrow t1 f g t2) 0
  | Kunit T :
      kinding T (Tconstr TCunit) 0
  | Kprod T :
      kinding T (Tconstr TCprod) 2
  | Ksum T :
      kinding T (Tconstr TCsum) 2
  | Krecur T x t :
      ~ StringMap.In x T ->
      kinding (add_kinding x 0 T) t 0 ->
      kinding T (Trecur (abs x t)) 0
  .

  Inductive teq : type -> type -> Prop :=
  | Qrefl t : teq t t
  | Qsymm a b : teq a b -> teq b a
  | Qtrans a b c : teq a b -> teq b c -> teq a c
  | Qabs a b :
      teq a b ->
      teq (Tabs a) (Tabs b)
  | Qapp a b a' b' :
      teq a a' ->
      teq b b' ->
      teq (Tapp a b) (Tapp a' b')
  | Qbeta t1 t2 :
      teq (Tapp (Tabs t1) t2) (subst t2 t1)
  | Qarrow a f g b a' b' : 
      teq a a' ->
      teq b b' ->
      teq (Tarrow a f g b) (Tarrow a' f g b')
  | Qrecur a b :
      teq a b ->
      teq (Trecur a) (Trecur b)
  .

  Inductive typing : tcontext -> expr -> type -> formula -> size -> Prop :=
  | TPvar T (x : string) t : find x T = Some (TEtyping t) -> typing T x t F1 (Svar (x : var, []))
  | TPapp T e1 e2 ta tb f g n1 n2 s1 s2 : 
      typing T e1 (Tarrow ta f g tb) n1 s1 ->
      typing T e2 ta n2 s2 ->
      typing T (Eapp e1 e2) (subst s2 tb) (n1 + n2 + subst s2 f)%F (subst s2 g)
  | TPabs T x e t1 t2 n s:
      kinding T t1 0 ->
      ~ StringMap.In x T -> 
      typing (add_typing x t1 T) e t2 n s ->
      typing T (Eabs t1 (abs x e)) (Tarrow t1 (abs x n) (abs x s) (abs x t2)) F1 size1
  | TPtapp T e t2 t n s:
      typing T e (Tuniversal t) n s ->
      let t' := subst t2 t in
      typing T (Etapp e t2) t' n s
  | TPtabs T X e t s:
      ~ StringMap.In X T ->
      typing (StringMap.add X TEtypevar T) e t F1 s ->
      typing T (Etabs (abs X e)) (Tuniversal (abs X t)) F1 s
  | TPlet T t1 e1 e2 t2 n1 n2 s1 s2 x:
      typing T e1 t1 n1 s1 ->
      ~ StringMap.In x T ->
      typing (add_typing x t1 T) e2 t2 n2 s2 ->
      typing T (Elet t1 e1 (abs x e2)) t2 (n1 + substx x s1 n2)%F (substx x s1 s2)
  | TPletrec T (defs : list letrec_entry) main t n s xs :
      length xs = length defs ->
      NoDup xs ->
      AllNotIn xs T ->
      let T' := add_typings (combine xs $ map (fst >> fst) defs) T in
      (forall lhs_ti rhs_ti ei, In (lhs_ti, rhs_ti, ei) defs -> typing T' (Eabs rhs_ti ei) lhs_ti F1 size1) ->
      typing T' main t n s ->
      typing T (Eletrec defs main) t n s
  | TPmatch_pair T e x1 x2 e' t t1 t2 n s n' s' s1 s2 :
      typing T e (Tprod t1 t2) n s ->
      is_pair s = Some (s1, s2) ->
      let x12 := [x1; x2] in
      AllNotIn x12 T ->
      let t12 := [t1; t2] in
      let T' := add_typings (combine x12 t12) T in
      typing T' e' t n' s' ->
      let xs12 := combine x12 [s1; s2] in
      typing T (Ematch_pair e (abs_many x12 e')) (subst xs12 t) (n + subst xs12 n') (subst xs12 s')
  | TPmatch_inlinr T e x e1 e2 t1 t2 n s s1 s2 ta na sa tb nb sb :
      typing T e (Tsum t1 t2) n s ->
      is_inlinr s = Some (s1, s2) ->
      ~ StringMap.In x T ->
      typing (add_typing x t1 T) e1 ta na sa ->
      typing (add_typing x t2 T) e2 tb nb sb ->
      sig ta = sig tb ->
      typing T (Ematch_sum e (abs x e1) (abs x e2)) (max (substx x s1 ta) (substx x s2 tb)) (n + max (substx x s1 na) (substx x s2 nb)) (max (substx x s1 sa) (substx x s2 sb))
  | TPmatch_inl T e x e1 e2 t1 t2 n s s' t' n' sa :
      typing T e (Tsum t1 t2) n s ->
      s = Sinl s' ->
      ~ StringMap.In x T ->
      typing (add_typing x t1 T) e1 t' n' sa ->
      typing T (Ematch_sum e (abs x e1) e2) (substx x s' t') (n + substx x s' n') (substx x s' sa)
  | TPmatch_inr T e x e1 e2 t1 t2 n s s' t' n' sa :
      typing T e (Tsum t1 t2) n s ->
      s = Sinr s' ->
      ~ StringMap.In x T ->
      typing (add_typing x t2 T) e2 t' n' sa ->
      typing T (Ematch_sum e e1 (abs x e2)) (substx x s' t') (n + substx x s' n') (substx x s' sa)
  | TPfold T e t1 n s :
      let t := Trecur t1 in
      typing T e (subst t t1) n s ->
      typing T (Efold e t) t n (Sfold s)
  | TPunfold T e t1 n s s1 :
      let t := Trecur t1 in
      is_fold s = Some s1 ->
      typing T e t n s ->
      typing T (Eunfold e t) (subst t t1) n s1
  (* bounded variables in profiles and those in type signatures are in different binding-space *)
  | TPpair T : 
      typing T Cpair (Tuniversal $ Tuniversal $ Tarrow #1 F1 size1 $ Tarrow #0 F1 (Spair #1 #0) $ Tprod #1 #0) F1 size1
  | TPinl T :
      typing T Cinl (Tuniversal $ Tuniversal $ Tarrow #1 F1 (Sinl #0) $ Tsum #1 #0) F1 size1
  | TPinr T :
      typing T Cinl (Tuniversal $ Tuniversal $ Tarrow #0 F1 (Sinr #0) $ Tsum #1 #0) F1 size1
  | TPtt T :
      typing T Ctt Tunit F1 size1
  | TPeq T e t1 t2 n s :
      typing T e t1 n s ->
      teq t1 t2 ->
      typing T e t2 n s
  .

  (* examples *)

  Definition Tlist := Tabs $ Trecur $ Tsum Tunit $ Tprod #1 #0.

  Variable Tint : type.

  Infix "$$" := Eapp (at level 85, right associativity).
  Definition list_int := Tlist $$$ Tint.

  Definition Fvar_empty_path (x : var) i := Fvar (x, []) i.
  Infix "@" := Fvar_empty_path (at level 10).

  Open Scope string_scope.

  Definition Ematch_list t e b_nil b_cons := Ematch_sum (Eunfold e t) b_nil (Ematch_pair #0 b_cons).


  Definition Ccons t a b := Efold (Econstr Cpair $$ a $$ b) t.

  Variable int_lt : expr.

  Definition merge_body merge := 
    abs_many ["xs"; "ys"]
             $ Ematch_list list_int  "xs"
             "ys" 
             $ abs_many ["x"; "xs'"]
             $ Ematch_list list_int  "ys"
             "xs"
             $ abs_many ["y"; "ys'"]
             $ Ematch_sum (int_lt $$ "x" $$ "y")
             (Ccons list_int  "x" (merge $$ "xs'" $$ "ys"))
             (Ccons list_int  "y" (merge $$ "xs" $$ "ys'")).

  Definition merge_type := Tarrow list_int F1 size1 $ Tarrow list_int (#1@0 + #0@0) (Sstats (#1@0 + #0@0, #1@1 + #0@1, #1@2 + #0@2, #1@3 + #0@3)) list_int.

  Definition merge :=
    Eletrec [(merge_type, list_int, Eabs list_int (merge_body #2))] #0.

  Arguments StringMap.empty {elt}.

  Lemma merge_typing : typing StringMap.empty merge merge_type F1 size1.
  Proof.
    eapply TPletrec.
    {
      instantiate (1 := ["merge"]).
      simpl.
      eauto.
    }
    {
      repeat econstructor; intuition.
    }
    {
      intros k Hin1 Hin2.
      admit.
    }
    {
      intros.
    }
  Qed.
      
End LambdaO.

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