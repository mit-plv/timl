Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 
Generalizable All Variables.

Require Import String List.
Open Scope string_scope.
Import ListNotations.
Open Scope list_scope.

Fixpoint range begin len :=
  match len with
    | 0 => nil
    | S n => begin :: range (S begin) n
  end.

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

  Require Import Program.

  Infix "<<" := compose (at level 40) : prog_scope.
  Infix ">>" := (flip compose) (at level 40) : prog_scope.
  Class Apply a b c := 
    {
      apply : a -> b -> c
    }.

  Infix "$" := apply (at level 85, right associativity) : prog_scope.
  Infix "$$" := apply (at level 105, left associativity) : prog_scope.
  Open Scope prog_scope.

  Definition apply_arrow {A B} (f : A -> B) x := f x.
  
  Instance Apply_arrow A B : Apply (A -> B) A B :=
    {
      apply := apply_arrow
    }.
  
  Inductive var :=
    | Vbound : nat -> var
    (* | Vfree : string -> var *)
  .

  (* Coercion Vbound : nat >-> var. *)
  (* Coercion Vfree : string >-> var. *)

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

  Instance Apply_type_type_type : Apply type type type :=
    {
      apply := Tapp
    }.
  
  Definition Tunit := Tconstr TCunit.
  Definition Tprod t1 t2 := Tconstr TCprod $$ t1 $$ t2.
  Definition Tsum t1 t2 := Tconstr TCsum $$ t1 $$ t2.

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
      
  Definition subst_list `{Subst V B} (values : list V) (e : B) := fold_left (flip subst) values e.

  Instance Subst_list `{Subst V B} : Subst (list V) B := 
    {
      subst := subst_list
    }.

  Definition Fvar_empty_path (x : var) i := Fvar (x, []) i.
  Infix "!" := Fvar_empty_path (at level 10).
 
  Instance Apply_expr_expr_expr : Apply expr expr expr :=
    {
      apply := Eapp
    }.
  
  Instance Apply_expr_type_expr : Apply expr type expr :=
    {
      apply := Etapp
    }.
  
  Definition Epair (ta tb : type) := Econstr Cpair $$ ta $$ tb.
  Definition Einl (ta tb : type) := Econstr Cinl $$ ta $$ tb.
  Definition Einr (ta tb : type) := Econstr Cinr $$ ta $$ tb.
  Definition Ett := Econstr Ctt.

  Notation "# n" := (Vbound n) (at level 3).

  Inductive step : expr -> expr -> Prop :=
    | STcontext c e1 e2 : step e1 e2 -> step (plug c e1) (plug c e2)
    | STapp t body arg : IsValue arg -> step (Eapp (Eabs t body) arg) (subst arg body)
    | STlet t v main : IsValue v -> step (Elet t v main) (subst v main)
    | STletrec_instantiate defs c (n : nat) t e : 
        find n defs = Some (t, e) -> 
        step (Eletrec defs (plug c (Evar #n))) (Eletrec defs (plug c e))  (* the definitions are only simplified, but not making any recursive or mutual-recursive call. All these calls are made only in the evaluation of 'main' *)
    | STletrec_finish defs v : IsValue v -> step (Eletrec defs v) v
    | STmatch_pair ta tb a b k : 
        IsValue a ->
        IsValue b ->
        step (Ematch_pair (Epair ta tb $$ a $$ b) k) (subst [a; b] k)
    | STmatch_inl ta tb v k1 k2 : 
        IsValue v ->
        step (Ematch_sum (Einl ta tb $$ v) k1 k2) (subst v k1)
    | STmatch_inr ta tb v k1 k2 : 
        IsValue v ->
        step (Ematch_sum (Einr ta tb $$ v) k1 k2) (subst v k2)
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

  (* Definition tcontext := StringMap.t tc_entry. *)
  Definition tcontext := list tc_entry.

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

  Fixpoint repeat A (a : A) n :=
    match n with
      | 0 => nil
      | S n => a :: repeat a n
    end.

  Definition ones := repeat F1.

  Arguments fst {A B} _.

  Definition size1 := Stt.

  Definition add_typing t T := TEtyping t :: T.
  Definition add_typings ls T := map TEtyping (rev ls) ++ T.
  Definition add_kinding k T := TEkinding k :: T.

  Definition max_size (a b : size) : size.
    admit.
  Defined.

  Instance Max_size : Max size :=
    {
      max := max_size
    }.

  Coercion var_to_size (x : var) : size := Svar (x, []).

  Inductive kinding : tcontext -> type -> kind -> Prop :=
  | Kvar T n k : find n T = Some (TEkinding k) -> kinding T #n k
  | Kapp T t1 t2 k :
      kinding T t1 (S k) ->
      kinding T t2 0 ->
      kinding T (Tapp t1 t2) k
  | Kabs T t k :
      kinding (add_kinding 0 T) t k ->
      kinding T (Tabs t) (S k)
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
  | Krecur T t :
      kinding (add_kinding 0 T) t 0 ->
      kinding T (Trecur t) 0
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

  Definition var_to_Svar x := Svar (x, []).

  Class Le t :=
    {
      le : t -> t -> Prop
    }.

  Infix "<=" := le.

  Variable le_formula : formula -> formula -> Prop.
  Instance Le_formula : Le formula :=
    {
      le := le_formula
    }.

  Variable le_size : size -> size -> Prop.
  Instance Le_size : Le size :=
    {
      le := le_size
    }.

  Class Equal t :=
    {
      equal : t -> t -> Prop
    }.

  Infix "==" := equal (at level 70).

  Instance Equal_type : Equal type :=
    {
      equal := teq
    }.

  Inductive typing : tcontext -> expr -> type -> formula -> size -> Prop :=
  | TPvar T n t : find n T = Some (TEtyping t) -> typing T #n t F1 (var_to_Svar #n)
  | TPapp T e1 e2 ta tb f g n1 n2 s1 s2 : 
      typing T e1 (Tarrow ta f g tb) n1 s1 ->
      typing T e2 ta n2 s2 ->
      typing T (Eapp e1 e2) (subst s2 tb) (n1 + n2 + subst s2 f)%F (subst s2 g)
  | TPabs T e t1 t2 n s:
      kinding T t1 0 ->
      typing (add_typing t1 T) e t2 n s ->
      typing T (Eabs t1 e) (Tarrow t1 n s t2) F1 size1
  | TPtapp T e t2 t n s:
      typing T e (Tuniversal t) n s ->
      let t' := subst t2 t in
      typing T (Etapp e t2) t' n s
  | TPtabs T e t s:
      typing (TEtypevar :: T) e t F1 s ->
      typing T (Etabs e) (Tuniversal t) F1 s
  | TPlet T t1 e1 e2 t2 n1 n2 s1 s2:
      typing T e1 t1 n1 s1 ->
      typing (add_typing t1 T) e2 t2 n2 s2 ->
      typing T (Elet t1 e1 e2) (subst s1 t2) (n1 + subst s1 n2)%F (subst s1 s2)
  | TPletrec T (defs : list letrec_entry) main t n s :
      let T' := add_typings (map (fst >> fst) defs) T in
      (forall lhs_t rhs_t e, 
         In (lhs_t, rhs_t, e) defs -> 
         typing T' (Eabs rhs_t e) lhs_t F1 size1) ->
      typing T' main t n s ->
      typing T (Eletrec defs main) t n s
  | TPmatch_pair T e e' t t1 t2 n s n' s' s1 s2 :
      typing T e (Tprod t1 t2) n s ->
      is_pair s = Some (s1, s2) ->
      let t12 := [t1; t2] in
      let T' := add_typings t12 T in
      typing T' e' t n' s' ->
      let s12 := [s1; s2] in
      typing T (Ematch_pair e e') (subst s12 t) (n + subst s12 n') (subst s12 s')
  | TPmatch_inlinr T e e1 e2 t1 t2 n s s1 s2 t na sa nb sb :
      typing T e (Tsum t1 t2) n s ->
      is_inlinr s = Some (s1, s2) ->
      typing (add_typing t1 T) e1 t na sa ->
      typing (add_typing t2 T) e2 t nb sb ->
      typing T (Ematch_sum e e1 e2) t (n + max (subst s1 na) (subst s2 nb)) (max (subst s1 sa) (subst s2 sb))
  | TPmatch_inl T e e1 e2 t1 t2 n s s' t' n' sa :
      typing T e (Tsum t1 t2) n s ->
      s = Sinl s' ->
      typing (add_typing t1 T) e1 t' n' sa ->
      typing T (Ematch_sum e e1 e2) (subst s' t') (n + subst s' n') (subst s' sa)
  | TPmatch_inr T e e1 e2 t1 t2 n s s' t' n' sa :
      typing T e (Tsum t1 t2) n s ->
      s = Sinr s' ->
      typing (add_typing t2 T) e2 t' n' sa ->
      typing T (Ematch_sum e e1 e2) (subst s' t') (n + subst s' n') (subst s' sa)
  | TPfold T e t n s t1 :
      t == Trecur t1 ->
      typing T e (subst t t1) n s ->
      typing T (Efold e t) t n (Sfold s)
  | TPunfold T e t n s s1 t1 :
      t == Trecur t1 ->
      is_fold s = Some s1 ->
      typing T e t n s ->
      typing T (Eunfold e t) (subst t t1) n s1
  | TPeq T e t1 t2 n s :
      typing T e t1 n s ->
      t1 == t2 ->
      typing T e t2 n s
  | TPsub T e t n n' s s' :
      typing T e t n s ->
      n <= n' ->
      s <= s' ->
      typing T e t n' s'
  | TPpair T : 
      typing T Cpair (Tuniversal $ Tuniversal $ Tarrow #1 F1 size1 $ Tarrow #1 F1 (Spair #1 #0) $ Tprod #3 #2) F1 size1
  | TPinl T :
      typing T Cinl (Tuniversal $ Tuniversal $ Tarrow #1 F1 (Sinl #0) $ Tsum #2 #1) F1 size1
  | TPinr T :
      typing T Cinl (Tuniversal $ Tuniversal $ Tarrow #0 F1 (Sinr #0) $ Tsum #2 #1) F1 size1
  | TPtt T :
      typing T Ctt Tunit F1 size1
  .

  (* examples *)

  Definition Tlist := Tabs $ Trecur $ Tsum Tunit $ Tprod #1 #0.
  Definition Ematch_list (telm : type) e b_nil b_cons := 
    let tlist := Tlist $$ telm in
    Ematch_sum (Eunfold e tlist) b_nil (Ematch_pair #0 b_cons).
  Definition Econs (telm : type) (a b : expr) := 
    let tlist := Tlist $$ telm in
    Efold (Epair telm tlist $$ a $$ b) tlist.

  Definition Tbool := Tsum Tunit Tunit.
  Definition Etrue := Einl Tunit Tunit $$ Ett.
  Definition Efalse := Einr Tunit Tunit $$ Ett.
  Definition Ematch_bool e b_true b_false :=
    Ematch_sum e b_true b_false.
  
  Variable Tint : type.
  Hypothesis Kint : forall T, kinding T Tint 0.
  Variable int_lt : expr.
  Hypothesis TPint_lt : forall T, typing T int_lt (Tarrow Tint F1 size1 $ Tarrow Tint F1 size1 Tbool) F1 size1.

  Definition list_int := Tlist $$ Tint.

  Instance Apply_expr_var_expr : Apply expr var expr :=
    {
      apply a b := Eapp a b
    }.
  
  Definition merge_body (merge : expr) := 
    Ematch_list Tint #1(*xs*)
                #1(*ys*)
                (Ematch_list list_int #3(*ys*)
                             #5(*xs*)
                             (Ematch_bool (int_lt $$ #4(*x*) $$ #1(*y*))
                                          (Econs Tint #5(*x*) (merge $$ #4(*xs'*) $$ #7(*ys*)))
                                          (Econs Tint #2(*y*) (merge $$ #8(*xs*) $$ #1(*ys'*))))).

  Definition merge_type := Tarrow list_int F1 size1 $ Tarrow list_int (#1!0 + #0!0) (Sstats (#1!0 + #0!0, #1!1 + #0!1, #1!2 + #0!2, #1!3 + #0!3)) list_int.

  Definition merge :=
    Eletrec [(merge_type, list_int, Eabs list_int (merge_body #2))] #0.

  Require Import ListFacts4.

  Arguments compose /. 
            Arguments flip /. 
            Arguments apply_arrow /. 
            Arguments add_typing /. 
            Arguments add_typings /. 
            Arguments add_kinding /. 

  Lemma Kprod' T a b :
    kinding T a 0 ->
    kinding T b 0 ->
    kinding T (Tprod a b) 0.
  Proof.
    intros.
    eapply Kapp.
    {
      eapply Kapp.
      { eapply Kprod. }
      { eauto. }
    }
    { eauto. }
  Qed.

  Lemma Ksum' T a b :
    kinding T a 0 ->
    kinding T b 0 ->
    kinding T (Tsum a b) 0.
  Proof.
    intros.
    eapply Kapp.
    {
      eapply Kapp.
      { eapply Ksum. }
      { eauto. }
    }
    { eauto. }
  Qed.

  Lemma Klist T (t : type) : kinding T t 0 -> kinding T (Tlist $$ t) 0.
  Proof.
    eapply Kapp.
    {
      eapply Kabs.
      {
        simpl.
        eapply Krecur.
        eapply Ksum'.
        { eapply Kunit. }
        {
          eapply Kprod'; eapply Kvar; compute; eauto.
        }
      }
    }
  Qed.

  Lemma merge_typing : typing [] merge merge_type F1 size1.
  Proof.
    eapply TPletrec.
    {
      intros until 0.
      intros H.
      eapply in_singleton_iff in H.
      inject H.
      eapply TPabs.
      { eapply Klist; eapply Kint. }
      {
        simpl.
        eapply TPabs.
        { eapply Klist; eapply Kint. }
        {
          unfold merge_body.
          unfold Ematch_list.
          eapply TPsub.
          {
            simpl.
            eapply TPmatch_inlinr.
            {
              Lemma TPunfold' T e t n s s1 t1 t' :
                t == Trecur t1 ->
                is_fold s = Some s1 ->
                typing T e t n s ->
                t' = subst t t1 ->
                typing T (Eunfold e t) t' n s1.
              Proof.
                intros; subst; eapply TPunfold; eauto.
              Qed.
              eapply TPunfold'.
              {
                (*here*)
              }
            }
          }
          {
          }
          {
          }
        }
      }        
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