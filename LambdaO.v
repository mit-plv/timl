Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 
Generalizable All Variables.

Require Import ListFacts4.

Require Import List.
Import ListNotations.
Open Scope list_scope.

Fixpoint range begin len :=
  match len with
    | 0 => nil
    | S n => begin :: range (S begin) n
  end.

Fixpoint iter {A} n f (x : A) :=
  match n with
    | 0 => x
    | S n' => iter n' f (f x)
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

Inductive cmp A :=
| LT (_ : A)
| EQ
| GT (_ : A).

Arguments EQ {A}.

Definition map_cmp A B (f : A -> B) c :=
  match c with
    | LT a => LT (f a)
    | EQ => EQ
    | GT a => GT (f a)
  end.

Fixpoint nat_cmp n m :=
  match n, m with
    | O, O => EQ
    | O, S p => LT p
    | S p, O => GT p
    | S n', S m' => map_cmp S (nat_cmp n' m')
  end.

Class Monad m := 
  {
    ret : forall a, a -> m a;
    bind : forall a, m a -> forall b, (a -> m b) -> m b
  }.

Notation "x <- a ;; b" := (bind a (fun x => b)) (at level 90, right associativity).
Notation "a ;;; b" := (bind a (fun _ => b)) (at level 90, right associativity).

Instance Monad_option : Monad option :=
  {
    ret := fun A (v : A) => Some v;
    bind := fun A (a : option A) B (f : A -> option B) =>
              match a with
                | Some a => f a
                | None => None
              end
  }.

Definition default A (def : A) x :=
  match x with
    | Some v => v
    | None => def
  end.

Section LambdaO.

  Require Import Program.

  Infix "<<" := compose (at level 40) : prog_scope.
  Infix ">>" := (flip compose) (at level 40) : prog_scope.
  Class Apply a b c := 
    {
      apply : a -> b -> c
    }.

  Infix "$" := apply (at level 85, right associativity) : prog_scope.
  Infix "$$" := apply (at level 15, left associativity) : prog_scope.
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

  Notation "# n" := (Vbound n) (at level 3).

  (* Coercion Vbound : nat >-> var. *)
  (* Coercion Vfree : string >-> var. *)

  (* kinds are restricted to the form (* => * => ... => *). 0 means * *)
  Definition kind := nat.

  (* 
    There are two statistics (or 'sizes') for each value :
    s0 : number of invocations of 'fold' 
         (for algebraic data types, this correspond to the number of constructor invocations to construct this value);
    s1 : parallel version of s0, where the fields of a pair are max'ed instead of sum'ed;
    For example, for lists, s0 correspond to its length; for trees, s0 corresponds to its number of nodes; s1 corresponds to its depth.
  *)

  Definition stat_idx := bool. (* An index indication the statistics you want. *)
  Inductive path_command :=
  | Pfst
  | Psnd
  | Pinl
  | Pinr
  | Punfold
  .
  Definition path := list path_command. (* The query path into a inner-component *)
  Definition var_path := (var * path)%type.

(*
  Variable formula : Type.
  Variable Fvar : var_path -> stat_idx -> formula.
  Variable F1 : formula.
  Variable Fplus Fmax : formula -> formula -> formula.
*)

  Inductive fbinop :=
  | FBplus
  | FBmax
  | FBminus
  | FBmult
  | FBdiv
  .

  Inductive funop :=
  | FUlog
  | FUexp
  .

  Inductive fconst :=
  | FC0
  | FC1
  .

  Inductive formula :=
  | Fvar (x : var_path) (stat : stat_idx)
  | Fconst (_ : fconst)
  | Fbinop (_ : fbinop) (a b : formula)
  | Funop (_ : funop) (_ : formula)
  .

  Notation F1 := (Fconst FC1).
  Notation F0 := (Fconst FC0).
  Notation Fplus := (Fbinop FBplus).
  Notation Fmax := (Fbinop FBmax).
  Infix "+" := Fplus : formula_scope.
  Delimit Scope formula_scope with F.
  Open Scope F.

  Definition stats := (formula * formula)%type.

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

  Definition append_path (x : var_path) p : var_path := (fst x, snd x ++ [p]).

  Definition has_pair (s : size) :=
    match s with
      | Svar x => Some (Svar (append_path x Pfst), Svar (append_path x Psnd))
      | Spair a b => Some (a, b)
      | _ => None
    end.

  Definition has_inlinr (s : size) :=
    match s with
      | Svar x => Some (Svar (append_path x Pinl), Svar (append_path x Pinr))
      | Sinlinr a b => Some (a, b)
      | _ => None
    end.

  Definition has_inl (s : size) :=
    match s with
      | Svar x => Some (Svar (append_path x Pinl))
      | Sinlinr a b => Some a
      | Sinl s => Some s
      | _ => None
    end.

  Definition has_inr (s : size) :=
    match s with
      | Svar x => Some (Svar (append_path x Pinr))
      | Sinlinr a b => Some b
      | Sinr s => Some s
      | _ => None
    end.

  Definition is_fold (s : size) :=
    match s with
      | Svar x => Some (Svar (append_path x Punfold))
      | Sfold t => Some t
      | _ => None
    end.

  Definition size1 := Stt.

  Definition query_cmd cmd s :=
    match cmd with
      | Pfst => 
        p <- has_pair s ;;
        ret (fst p)
      | Psnd =>
        p <- has_pair s ;;
        ret (snd p)
      | Pinl => has_inl s
      | Pinr => has_inr s
      | Punfold => is_fold s
    end.

  Fixpoint query_path path s :=
    match path with
      | cmd :: path => 
        s <- query_cmd cmd s ;;
        query_path path s
      | nil => ret s
    end.

  Definition stats_get (idx : stat_idx) (ss : stats) := if idx then snd ss else fst ss.

  Class Max t := 
    {
      max : t -> t -> t
    }.

  Instance Max_formula : Max formula :=
    {
      max := Fmax
    }.

  Fixpoint summarize (s : size) : stats :=
    match s with
      | Svar x => (Fvar x false, Fvar x true)
      | Sstats ss => ss
      | Stt => (F1, F1)
      | Spair a b => 
        let (a1, a2) := summarize a in
        let (b1, b2) := summarize b in
        (a1 + b1, a2 + b2)
      | Sinlinr a b => 
        let (a1, a2) := summarize a in
        let (b1, b2) := summarize b in
        (max a1 b1, max a2 b2)
      | Sinl s => summarize s
      | Sinr s => summarize s
      | Sfold s =>
        let (f1, f2) := summarize s in
        (F1 + f1, F1 + f2)
    end.

  Definition query_idx idx s := stats_get idx $ summarize s.
    
  Definition query_path_idx path idx s :=
    s <- query_path path s ;;
    ret (query_idx idx s).
    
  Fixpoint visit_f f fm :=
    match fm with
      | Fvar (Vbound nv, path) i => f nv path i
      | Fconst c => fm
      | Fbinop o a b => Fbinop o (visit_f f a) (visit_f f b)
      | Funop o n => Funop o (visit_f f n)
    end.

  Definition subst_s_f_f n v nv path i :=
    match nat_cmp nv n with 
      | LT _ => Fvar (#nv, path) i
      | EQ => default (Fvar (#99, path) i) $ query_path_idx path i v
      | GT p => Fvar (#p, path) i
    end.

  Definition subst_size_formula (n : nat) (v : size) (b : formula) : formula :=
    visit_f (subst_s_f_f n v) b.

  (* substitute the outer-most bound variable *)
  Class Subst value body :=
    {
      substn : nat -> value -> body -> body
    }.

  Definition subst `{Subst V B} := substn 0.

  Instance Subst_size_formula : Subst size formula :=
    {
      substn := subst_size_formula
    }.

  Definition lift_f_f n nv path i :=
    let nv :=
        match nat_cmp nv n with
          | LT _ => nv
          | _ => S nv
        end in
    Fvar (#nv, path) i.

  Definition lift_from_f n f :=
    visit_f (lift_f_f n) f.

  Class Lift t := 
    {
      lift_from : nat -> t -> t
    }.

  Definition lift `{Lift t} := lift_from 0.
  Definition liftby `{Lift t} n := iter n lift.
  
  Instance Lift_formula : Lift formula :=
    {
      lift_from := lift_from_f
    }.

  (* 'lower' is a 'dry run' of 'subst', not doing substitution, only lowering bound variables above *)
  Definition lower_f n f :=
    visit_f
      (fun nv path i => 
         match nat_cmp nv n with 
           | GT p => Fvar (#p, path) i
           | _ => Fvar (#nv, path) i
         end) 
      f.

  Class Lower t := 
    {
      lower : nat -> t -> t
    }.

  Instance Lower_formula : Lower formula :=
    {
      lower := lower_f
    }.

  Definition map_stats A (f : formula -> A) (ss : stats) := (f (fst ss), f (snd ss)).
 
  Fixpoint visit_s (f : (nat -> path -> size) * (formula -> formula)) s :=
    let (fv, ff) := f in
    match s with
      | Svar (Vbound nv, path) => fv nv path
      | Sstats ss => Sstats $ map_stats ff ss
      | Stt => Stt
      | Spair a b => Spair (visit_s f a) (visit_s f b)
      | Sinlinr a b => Sinlinr (visit_s f a) (visit_s f b)
      | Sinl s => Sinl (visit_s f s)
      | Sinr s => Sinr (visit_s f s)
      | Sfold s => Sfold (visit_s f s)
    end.

  Definition subst_size_size (n : nat) (v b : size) : size :=
    visit_s 
      (fun nv path =>
         match nat_cmp nv n with 
           | LT _ => Svar (#nv, path)
           | EQ => default Stt $ query_path path v
           | GT p => Svar (#p, path)
         end,
      substn n v) 
      b.

  Instance Subst_size_size : Subst size size :=
    {
      substn := subst_size_size
    }.

  Definition lift_from_s n s :=
    visit_s
      (fun nv path =>
         let nv :=
             match nat_cmp nv n with
               | LT _ => nv
               | _ => S nv
             end in
         Svar (#nv, path),
      lift_from n)
      s.

  Instance Lift_size : Lift size :=
    {
      lift_from := lift_from_s
    }.

  Definition lower_s n s :=
    visit_s
      (fun nv path =>
         match nat_cmp nv n with 
           | GT p => Svar (#p, path)
           | _ => Svar (#nv, path)
         end,
         lower n) 
      s.

  Instance Lower_size : Lower size :=
    {
      lower := lower_s
    }.

  Inductive tconstr :=
  | TCunit
  | TCprod
  | TCsum
  (* | TCint *)
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

  Coercion Tvar : var >-> type.

  Open Scope nat_scope.

  Fixpoint visit_t n (f : (nat -> nat -> type) * (nat -> formula -> formula) * (nat -> size -> size)) b :=
    let fv := fst $ fst f in
    let ff := snd $ fst f in
    let fs := snd f in
    match b with
      | Tvar (Vbound n') => fv n' n
      | Tarrow a time retsize b => Tarrow (visit_t n f a) (ff (S n) time) (fs (S n) retsize) (visit_t (S n) f b)
      | Tconstr _ => b
      | Tuniversal t => Tuniversal (visit_t (S n) f t) 
      | Tabs t => Tabs (visit_t (S n) f t) 
      | Tapp a b => Tapp (visit_t n f a) (visit_t n f b)
      | Trecur t => Trecur (visit_t (S n) f t) 
    end.

  (* nv : the number in Vbound
     nq : the number of surrounding quantification layers 
   *)

  Definition lift_t_f nv nq : type := 
    match nat_cmp nv nq with 
      | LT _ => #nv
      | _ => #(S nv)
    end.

  Definition lift_from_t n t := 
    visit_t n (lift_t_f, lift_from, lift_from) t.

  Instance Lift_type : Lift type :=
    {
      lift_from := lift_from_t
    }.
                    
  Definition subst_t_t_f n v nv nq : type :=
    match nat_cmp nv (n + nq) with 
      | LT _ => #nv
      | EQ => liftby nq v
      | GT p => #p (* variables above n+nq should be lowered *)
    end.

  Definition lower_sub `{Lower B} n nq b := lower (n + nq) b.

  Definition substn_t_t n v b := 
    visit_t 0 (subst_t_t_f n v, lower_sub n, lower_sub n) b.

  Instance Subst_type_type : Subst type type :=
    {
      substn := substn_t_t
    }.

  Definition substn_sub `{Subst V B, Lift V} n v nq b := substn (n + nq) (liftby nq v) b.

  Definition lower_t_f n nv nq : type :=
    match nat_cmp nv (n + nq) with 
      | GT p => #p
      | _ => #nv
    end.

  Definition subst_size_type (n : nat) (v : size) (b : type) : type :=
    visit_t
      0 
      (lower_t_f n,
       substn_sub n v,
       substn_sub n v)
      b.

  Instance Subst_size_type : Subst size type :=
    {
      substn := subst_size_type
    }.

  Definition lower_t n t :=
    visit_t
      0
      (lower_t_f n,
       lower_sub n,
       lower_sub n)
      t.

  Instance Lower_type : Lower type :=
    {
      lower := lower_t
    }.

  Instance Apply_type_type_type : Apply type type type :=
    {
      apply := Tapp
    }.
  
  Definition Tunit := Tconstr TCunit.
  Definition Tprod t1 t2 := Tconstr TCprod $$ t1 $$ t2.
  Definition Tsum t1 t2 := Tconstr TCsum $$ t1 $$ t2.

(*
  Definition tuple4indices : tuple4 nat := (0, 1, 2, 3). 

  Definition get_stats (s : size) :=
    match s with
      | Svar x => map (Fvar x) tuple4indices
      | Sstruct stats _ => stats
    end.
*)

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

  Fixpoint visit_e n (f : (nat -> nat -> expr) * (nat -> type -> type)) b :=
    let (fv, ft) := f in
    match b with
      | Evar (Vbound n') => fv n' n
      | Econstr _ => b
      | Eapp a b => Eapp (visit_e n f a) (visit_e n f b)
      | Eabs t e => Eabs (ft n t) (visit_e (S n) f e)
      | Elet t def main => Elet (ft n t) (visit_e n f def) (visit_e (S n) f main)
      | Eletrec defs main =>
        let m := length defs in
        Eletrec ((fix loop ls := 
                    match ls with
                      | nil => nil
                      | (t1, t2, e) :: xs => (ft n t1, ft (m + n) t2, visit_e (1 + m + n) f e) :: loop xs 
                    end) defs) (visit_e (m + n) f main)
      | Ematch_pair target handler => Ematch_pair (visit_e n f target) (visit_e (2 + n) f handler)
      | Ematch_sum target a b => Ematch_sum (visit_e n f target) (visit_e (S n) f a) (visit_e (S n) f b)
      | Etapp e t => Etapp (visit_e n f e) (ft n t)
      | Etabs e => Etabs (visit_e (S n) f e)
      | Efold e t => Efold (visit_e n f e) (ft n t)
      | Eunfold e t => Eunfold (visit_e n f e) (ft n t)
    end.

  Definition lift_from_e n e := 
    visit_e 
      n
      (fun nv nq =>
         match nat_cmp nv nq with 
           | LT _ => #nv : expr
           | _ => #(S nv) : expr
         end, lift_from) 
      e.

  Instance Lift_expr : Lift expr :=
    {
      lift_from := lift_from_e
    }.

  Definition substn_e_e_f n v nv nq : expr :=
    match nat_cmp nv (n + nq) with 
      | LT _ => #nv
      | EQ => liftby nq v
      | GT p => #p
    end.

  Definition substn_e_e n v b := 
    visit_e 0 (substn_e_e_f n v, lower_sub n) b.

  Instance Subst_expr_expr : Subst expr expr :=
    {
      substn := substn_e_e
    }.

  Definition lower_e_f n nv nq : expr := 
    match nat_cmp nv (n + nq) with 
      | GT p => #p
      | _ => #nv
    end.

  Definition substn_t_e n (v : type) (b : expr) : expr :=
    visit_e
      0
      (lower_e_f n,
       substn_sub n v)
      b.

  Instance Subst_type_expr : Subst type expr :=
    {
      substn := substn_t_e
    }.

  Definition lower_e n e :=
    visit_e 0 (lower_e_f n, lower_sub n) e.

  Instance Lower_expr : Lower expr :=
    {
      lower := lower_e
    }.

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

  Class Find key value container := 
    {
      find : key -> container -> option value
    }.

  Instance Find_list A : Find nat A (list A) :=
    {
      find k c := @nth_error A c k
    }.
      
  Definition subst_list `{Subst V B} (values : list V) (e : B) := fold_left (flip subst) values e.

  Instance Apply_expr_expr_expr : Apply expr expr expr :=
    {
      apply := Eapp
    }.
  
  Instance Apply_expr_type_expr : Apply expr type expr :=
    {
      apply := Etapp
    }.
  
  Definition Epair := Econstr Cpair.
  Definition Einl := Econstr Cinl.
  Definition Einr := Econstr Cinr.
  Definition Ett := Econstr Ctt.

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
        step (Ematch_pair (Epair $$ ta $$ tb $$ a $$ b) k) (subst_list [a; b] k)
    | STmatch_inl ta tb v k1 k2 : 
        IsValue v ->
        step (Ematch_sum (Einl $$ ta $$ tb $$ v) k1 k2) (subst v k1)
    | STmatch_inr ta tb v k1 k2 : 
        IsValue v ->
        step (Ematch_sum (Einr $$ ta $$ tb $$ v) k1 k2) (subst v k2)
    | STtapp body t : step (Etapp (Etabs body) t) (subst t body)
    | STunfold_fold v t1 t2 : 
        IsValue v ->
        step (Eunfold (Efold v t1) t2) v
  .

  (* Typing context.
     The second field of TEtyping is the optional size constraint
   *)
  Inductive tc_entry := 
    | TEtyping (_ : type * option size)
    | TEkinding (_ : kind).

  Arguments rev {A} _.

  Definition cat_options {A} (ls : list (option A)) := fold_right (fun x acc => match x with Some v => v :: acc | _ => acc end) [] ls.

  Definition map_option {A B} (f : A -> option B) := cat_options << map f.

  (* Definition tcontext := StringMap.t tc_entry. *)
  Definition tcontext := list tc_entry.

  Fixpoint repeat A (a : A) n :=
    match n with
      | 0 => nil
      | S n => a :: repeat a n
    end.

  Arguments fst {A B} _.

  Instance Lift_option `{Lift A} : Lift (option A) :=
    {
      lift_from n o := option_map (lift_from n) o
    }.

  Instance Lift_pair `{Lift A, Lift B} : Lift (A * B) :=
    {
      lift_from n p := (lift_from n (fst p), lift_from n (snd p))
    }.

  Definition add_typing t T := TEtyping t :: T.
  Definition add_typings ls T := fst $ fold_left (fun (p : tcontext * nat) t => let (T, n) := p in (add_typing (liftby n t) T, S n)) ls (T, 0).
  Definition add_kinding k T := TEkinding k :: T.

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
      kinding (add_kinding 0 T) t2 0 ->
      kinding T (Tarrow t1 f g t2) 0
  | Kuniversal T t :
      kinding (add_kinding 0 T) t 0 ->
      kinding T (Tuniversal t) 0
  | Krecur T t :
      kinding (add_kinding 0 T) t 0 ->
      kinding T (Trecur t) 0
  | Kunit T :
      kinding T (Tconstr TCunit) 0
  | Kprod T :
      kinding T (Tconstr TCprod) 2
  | Ksum T :
      kinding T (Tconstr TCsum) 2
  (* | Kint T : *)
  (*     kinding T (Tconstr TCint) 0 *)
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

  Definition le_formula : formula -> formula -> Prop.
    admit.
  Defined.

  Instance Le_formula : Le formula :=
    {
      le := le_formula
    }.

  Definition le_size : size -> size -> Prop.
    admit.
  Defined.

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

  Open Scope formula_scope.

  Definition add_snd {A B} (b : B) (a : A) := (a, b).

  Inductive typing : tcontext -> expr -> type -> formula -> size -> Prop :=
  | TPvar T n t s : 
      find n T = Some (TEtyping (t, s)) -> 
      typing T #n (liftby (S n) t) F0 (default (var_to_Svar #n) (liftby (S n) s))
  | TPapp T e1 e2 ta tb f g n1 n2 nouse s2 : 
      typing T e1 (Tarrow ta f g tb) n1 nouse ->
      typing T e2 ta n2 s2 ->
      typing T (Eapp e1 e2) (subst s2 tb) (n1 + n2 + subst s2 f)%F (subst s2 g)
  | TPabs T e t1 t2 n s :
      kinding T t1 0 ->
      typing (add_typing (t1, None) T) e t2 n s ->
      typing T (Eabs t1 e) (Tarrow t1 n s t2) F0 size1
  | TPtapp T e t2 t n s :
      typing T e (Tuniversal t) n s ->
      let t' := subst t2 t in
      typing T (Etapp e t2) t' n s
  | TPtabs T e t nouse1 nouse2 :
      typing (add_kinding 0 T) e t nouse1 nouse2 ->
      typing T (Etabs e) (Tuniversal t) F0 size1
  | TPlet T t1 e1 e2 t2 n1 n2 s1 s2:
      typing T e1 t1 n1 s1 ->
      typing (add_typing (t1, Some s1) T) e2 t2 n2 s2 ->
      typing T (Elet t1 e1 e2) (subst s1 t2) (n1 + subst s1 n2)%F (subst s1 s2)
  | TPletrec T (defs : list letrec_entry) main t n s :
      let len := length defs in
      let T' := add_typings (map (fst >> fst >> add_snd (Some size1)) defs) T in
      (forall lhs_t rhs_t e, 
         In (lhs_t, rhs_t, e) defs -> 
         typing T' (Eabs rhs_t e) (liftby len lhs_t) F0 size1) ->
      typing T' main (liftby len t) (liftby len n) (liftby len s) ->
      typing T (Eletrec defs main) t n s
  | TPmatch_pair T e e' t t1 t2 n s n' s' s1 s2 :
      typing T e (Tprod t1 t2) n s ->
      has_pair s = Some (s1, s2) ->
      let t12 := [(t1, Some s1); (t2, Some s2)] in
      let T' := add_typings t12 T in
      typing T' e' t n' s' ->
      let s12 := [s1; s2] in
      typing T (Ematch_pair e e') (subst_list s12 t) (n + subst_list s12 n') (subst_list s12 s')
  | TPmatch_inlinr T e e1 e2 t1 t2 n s s1 s2 t' na nb s' :
      typing T e (Tsum t1 t2) n s ->
      has_inlinr s = Some (s1, s2) ->
      (* timing constraints are passed forward; size and type constraints are passed backward.
         t' and s' are backward guidance for branches *)
      typing (add_typing (t1, Some s1) T) e1 (lift t') na (lift s') -> 
      typing (add_typing (t2, Some s2) T) e2 (lift t') nb (lift s') -> 
      typing T (Ematch_sum e e1 e2) t' (n + max (subst s1 na) (subst s2 nb)) s'
  | TPmatch_inl T e e1 e2 t1 t2 n s s' t' n' sa :
      typing T e (Tsum t1 t2) n s ->
      s = Sinl s' ->
      typing (add_typing (t1, Some s') T) e1 t' n' sa ->
      typing T (Ematch_sum e e1 e2) (subst s' t') (n + subst s' n') (subst s' sa)
  | TPmatch_inr T e e1 e2 t1 t2 n s s' t' n' sa :
      typing T e (Tsum t1 t2) n s ->
      s = Sinr s' ->
      typing (add_typing (t2, Some s') T) e2 t' n' sa ->
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
      typing T Cpair (Tuniversal $ Tuniversal $ Tarrow #1 F0 size1 $ Tarrow #1 F1 (Spair #1 #0) $ Tprod #3 #2) F0 size1
  | TPinl T :
      typing T Cinl (Tuniversal $ Tuniversal $ Tarrow #1 F1 (Sinl #0) $ Tsum #2 #1) F0 size1
  | TPinr T :
      typing T Cinl (Tuniversal $ Tuniversal $ Tarrow #0 F1 (Sinr #0) $ Tsum #2 #1) F0 size1
  | TPtt T :
      typing T Ctt Tunit F0 size1
  .

  (* examples *)

  Definition Tlist := Tabs $ Trecur $ Tsum Tunit $ Tprod #1 #0.
  Definition Ematch_list (telm : type) e b_nil b_cons := 
    let tlist := Tlist $$ telm in
    Ematch_sum (Eunfold e tlist) (lift b_nil) (Ematch_pair #0 $ lift_from 2 b_cons).

  Definition Tbool := Tsum Tunit Tunit.
  Definition Etrue := Einl $$ Tunit $$ Tunit $$ Ett.
  Definition Efalse := Einr $$ Tunit $$ Tunit $$ Ett.
  Definition Eif e b_true b_false :=
    Ematch_sum e (lift b_true) (lift b_false).

(*  
  Definition Tint := Tconstr TCint.
  Variable int_lt : expr.
  Hypothesis TPint_lt : forall T, typing T int_lt (Tarrow Tint F1 size1 $ Tarrow Tint F1 size1 Tbool) F1 size1.

  Definition list_int := Tlist $$ Tint.
*)
  Instance Apply_expr_var_expr : Apply expr var expr :=
    {
      apply a b := Eapp a b
    }.
  
  Instance Apply_type_var_type : Apply type var type :=
    {
      apply a b := Tapp a b
    }.

  Arguments compose / . 
  Arguments flip / . 
  Arguments apply_arrow / . 
  Arguments add_typing / . 
  Arguments add_typings / . 
  Arguments add_kinding / . 

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
          eapply Kprod'; eapply Kvar; simpl; eauto.
        }
      }
    }
  Qed.

  Lemma TPunfold' T e t n s s1 t1 t' :
    t == Trecur t1 ->
    is_fold s = Some s1 ->
    typing T e t n s ->
    t' = subst t t1 ->
    typing T (Eunfold e t) t' n s1.
  Proof.
    intros; subst; eapply TPunfold; eauto.
  Qed.

  Lemma Qbeta' t1 t2 t' :
    t' = subst t2 t1 ->
    teq (Tapp (Tabs t1) t2) t'.
  Proof.
    intros; subst; eapply Qbeta; eauto.
  Qed.

  Lemma list_equal (t : type) : (Tlist $$ t) == Trecur (Tsum Tunit $ Tprod (lift t) #0).
  Proof.
    eapply Qbeta'.
    simpl; eauto.
  Qed.

  Lemma TPmatch_pair' T e e' t t1 t2 n s n' s' s1 s2 t'' n'' s'' :
    typing T e (Tprod t1 t2) n s ->
    has_pair s = Some (s1, s2) ->
    let t12 := [(t1, Some s1); (t2, Some s2)] in
    let T' := add_typings t12 T in
    typing T' e' t n' s' ->
    let s12 := [s1; s2] in
    t'' = subst_list s12 t ->
    n'' = n + subst_list s12 n' ->
    s'' = subst_list s12 s' ->
    typing T (Ematch_pair e e') t'' n'' s''.
  Proof.
    intros; subst; eapply TPmatch_pair; eauto.
  Qed.

  Lemma Kbool T : kinding T Tbool 0.
  Proof.
    eapply Ksum'; eapply Kunit.
  Qed.

  Definition is_list s :=
    s <- is_fold s ;;
      p <- has_inlinr s ;;
      has_pair (snd p).

  Lemma Sle_refl (a : size) : a <= a.
    admit.
  Qed.

  Lemma Fle_refl (a : formula) : a <= a.
    admit.
  Qed.

  Lemma TPsubs T e t n s s' :
    typing T e t n s ->
    s <= s' ->
    typing T e t n s'.
  Proof.
    intros; eapply TPsub; eauto.
    eapply Fle_refl.
  Qed.
(*
  Lemma TPmatch_inlinr' T e e1 e2 t1 t2 n s s1 s2 t' n' s' n'' :
    typing T e (Tsum t1 t2) n s ->
    has_inlinr s = Some (s1, s2) ->
    (* t', n' and s' are backward guidance and specs for branches *)
    typing (add_typing t1 T) e1 (lift t') (lift n') (lift s') -> 
    typing (add_typing t2 T) e2 (lift t') (lift n') (lift s') -> 
    n'' = n + n' ->
    typing T (Ematch_sum e e1 e2) t' n'' s'.
  Proof.
    intros; subst; eapply TPmatch_inlinr; eauto.
  Qed.
*)
(*
  Lemma Sle_lift (a b : size) : a <= b -> lift a <= lift b.
    admit.
  Qed.
*)
  Lemma is_list_elim s p : is_list s = Some p -> exists s1 s2 s3, is_fold s = Some s1 /\ has_inlinr s1 = Some (s2, s3) /\ has_pair s3 = Some p.
    admit.
  Qed.

  Arguments substn_t_t n v b / .
  Arguments subst_t_t_f n v nv nq / .
  Arguments liftby / .
  Arguments lift_from_t n t / .

  Lemma TPsubn T e t n s n' :
    typing T e t n s ->
    n <= n' ->
    typing T e t n' s.
  Proof.
    intros; eapply TPsub; eauto.
    eapply Sle_refl.
  Qed.

  Lemma TPmatch_list T e e1 e2 telm n s s1 s2 t' na nb s' :
    let list := Tlist $ telm in
    typing T e list n s ->
    is_list s = Some (s1, s2) ->
    typing T e1 t' na s' ->
    typing (add_typings [(telm, Some s1); (list, Some s2)] T) e2 (liftby 2 t') nb (liftby 2 s') ->
    let s12 := [s1; s2] in
    typing T (Ematch_list telm e e1 e2) t' (n + max na (subst_list s12 nb)) s'.
  Proof.
    simpl.
    intros He Hs H1 H2.
    unfold Ematch_list.
    eapply is_list_elim in Hs.
    destruct Hs as [sf [sl [sr [Hsf [Hslr Hsp]]]]].
    eapply TPsubn.
    {
      eapply TPmatch_inlinr.
      {
        eapply TPunfold'; eauto.
        { eapply list_equal. }
        {
          simpl.
          Lemma fold_substn_t_t n v b : visit_t 0 (subst_t_t_f n v, lower_sub n, lower_sub n) b = substn_t_t n v b.
          Proof.
            eauto.
          Qed.
          rewrite fold_substn_t_t in *.
          Lemma fold_lift_from_t n t : visit_t n (lift_t_f, lift_from, lift_from) t = lift_from_t n t.
          Proof.
            eauto.
          Qed.
          rewrite fold_lift_from_t in *.
          Lemma subst_lift v (b : type) : substn_t_t 0 v (lift_from_t 0 b) = b.
            admit.
          Qed.
          rewrite subst_lift.
          unfold Tsum.
          eauto.
        }
      }
      { simpl; eauto. }
      {
        rewrite fold_lift_from_t in *.
        Lemma TPlift T e t n s r : typing T e t n s -> typing (r :: T) (lift e) (lift t) (lift n) (lift s).
          admit.
        Qed.
        eapply TPlift; eauto.
      }
      {
        Arguments Tprod / .
        eapply TPmatch_pair'.
        Lemma TPvar' T n t s t' s' : 
          find n T = Some (TEtyping (t, s)) -> 
          t' = liftby (S n) t ->
          s' = default (var_to_Svar #n) (liftby (S n) s) ->
          typing T #n t' F0 s'.
        Proof.
          intros; subst; eapply TPvar; eauto.
        Qed.
        { eapply TPvar'; simpl; eauto; simpl; eauto. }
        {
          simpl.
          Lemma has_pair_lift sp s1 s2 : has_pair sp = Some (s1, s2) -> has_pair (lift sp) = Some (lift s1, lift s2).
            admit.
          Qed.
          eapply has_pair_lift; eauto.
        }
        {
          simpl.
          repeat rewrite fold_lift_from_t in *.
          Definition removen A n ls := @firstn A n ls ++ skipn (S n) ls.
          Definition lift_from_TE n te :=
            match te with
              | TEtyping ty => TEtyping $ lift_from n ty
              | TEkinding k => te
            end.

          Instance Lift_tc_entry : Lift tc_entry :=
            {
              lift_from := lift_from_TE
            }.

          Lemma TPlift2 T e t n s r0 r1 r2 r0' r1' : 
            typing (r0 :: r1 :: T) e t n s ->
            r0' = lift r0 ->
            r1' = lift r1 ->
            typing (r0' :: r1' :: r2 :: T) (lift_from 2 e) (lift_from 2 t) (lift_from 2 n) (lift_from 2 s).
          Proof.
            admit.
          Qed.
          eapply TPlift2; eauto.
        }
        {
          simpl.
          repeat rewrite fold_lift_from_t in *.
          fold (iter 2 (lift_from_t 0) t').
          Lemma lift_from_liftby n t : lift_from_t n (iter n (lift_from_t 0) t) = iter (S n) (lift_from_t 0) t.
            admit.
          Qed.
          rewrite lift_from_liftby.
          simpl.
          Lemma subst_lift_s_t v (b : type) : subst_size_type 0 v (lift_from_t 0 b) = b.
            admit.
          Qed.
          repeat rewrite fold_lift_from_t in *.
          repeat rewrite subst_lift_s_t.
          eauto.
        }
        { eauto. }
        {
          simpl.
          fold (iter 2 (lift_from_s 0) s').
          Lemma lift_from_liftby_s n s : lift_from_s n (iter n (lift_from_s 0) s) = iter (S n) (lift_from_s 0) s.
            admit.
          Qed.
          rewrite (@lift_from_liftby_s 2).
          simpl.
          Lemma subst_lift_s_s v b : subst_size_size 0 v (lift_from_s 0 b) = b.
            admit.
          Qed.
          repeat rewrite subst_lift_s_s.
          eauto.
        }
      }
    }
    {
      simpl.
      Lemma Fle_plus (a a' b b' : formula) : a <= a' -> b <= b' -> a + b <= a' + b'.
        admit.
      Qed.
      eapply Fle_plus; try eapply Fle_refl.
      Lemma subst_lift_s_f v b : subst_size_formula 0 v (lift_from_f 0 b) = b.
        admit.
      Qed.
      repeat rewrite subst_lift_s_f.
      Lemma Fle_maxr (a b b' : formula) : b <= b' -> max a b <= max a b'.
        admit.
      Qed.
      eapply Fle_maxr.
      Arguments subst_size_formula n v b / .
      simpl.
      Lemma fold_subst_s_f n s : visit_f (subst_s_f_f n s) = subst_size_formula n s.
      Proof.
        eauto.
      Qed.
      repeat rewrite fold_subst_s_f in *.
      Lemma Fleadd0r a b : a <= b -> F0 + a <= b.
        admit.
      Qed.
      eapply Fleadd0r.
      Lemma Sle_skip_subst a b v a' : a' = lift a -> a <= b -> subst_size_formula 0 v a' <= b.
        admit.
      Qed.
      eapply Sle_skip_subst.
      {
        Lemma subst2_lift s2 s1 n : subst_size_formula 0 (lift_from_s 0 s2) (subst_size_formula 0 (lift_from_s 0 s1) (lift_from_f 2 n)) = lift (subst_size_formula 0 s2 (subst_size_formula 0 s1 n)).
          admit.
        Qed.
        eapply subst2_lift.
      }
      {
        eapply Fle_refl.
      }
    }
  Qed.

(*
    {
      simpl.
      rewrite Fplus0r.
      fold (iter 2 (lift_from_f 0) n').
      Lemma lift_from_liftby_f n f : lift_from_f n (iter n (lift_from_f 0) f) = iter (S n) (lift_from_f 0) f.
        admit.
      Qed.
      rewrite (@lift_from_liftby_f 2).
      simpl.
      eauto.
    }
*)

  Definition Econs := 
    Etabs $ Eabs #0 $ Eabs (Tlist $ #1) $ 
          let telm := #2 : type in
          let tlist := Tlist $ telm in
          Efold (Epair $$ telm $$ tlist $$ #1 $$ #0) tlist.

  (* loop_body is equivalent to this:

    match xs with
      | nil => ys
      | x :: xs' => match ys with
                      | nil => xs
                      | y :: ys' => if cmp x y then
                                      x :: loop xs' ys
                                    else
                                      y :: loop xs ys' end end
  *)

  Definition loop_body (telm : type) (cmp loop : expr) := 
    Ematch_list telm #1(*xs*) (*level 0*)
                #0(*ys*)
                (Ematch_list (liftby 2 telm) #2(*ys*) (*level 2*)
                             #3(*xs*)
                             (Eif (liftby 4 cmp $$ #3(*x*) $$ #1(*y*)) (*level 4*)
                                  (Econs $$ liftby 4 telm $$ #3(*x*) $$ (liftby 4 loop $$ #2(*xs'*) $$ #4(*ys*)))
                                  (Econs $$ liftby 4 telm $$ #1(*y*) $$ (liftby 4 loop $$ #5(*xs*) $$ #0(*ys'*))))).

  Notation "x '!0'" := (Fvar (x, []) false) (at level 10, format "x '!0'").
  Notation "x '!1'" := (Fvar (x, []) true) (at level 10, format "x '!1'").
 
  Definition loop_type (telm : type) := 
    let list := Tlist $ telm in
    Tarrow list F0 size1 $ Tarrow (lift list) (#1!0 + #0!0) (Sstats (#1!0 + #0!0, #1!1 + #0!1)) (liftby 2 list).

  Definition bool_size := size1.

  Definition cmp_type (A : type) := Tarrow A F0 size1 $ Tarrow (lift A) (#1!0 + #0!0) bool_size Tbool.

  Definition merge :=
    Etabs $ let telm : type := #0 in let list := Tlist $ telm in Eabs (cmp_type telm) $ Eletrec [(loop_type (lift telm), (liftby 2 list), Eabs (liftby 3 list) (loop_body (liftby 4 telm) #3 #2))] #0.

  Definition merge_type := 
    Tuniversal $ Tarrow (cmp_type #0) F0 size1 $ loop_type #1.

  Lemma Kcmp_type T t : kinding T t 0 -> kinding T (cmp_type t) 0.
  Proof.
    intros H.
    eapply Karrow; eauto.
    eapply Karrow; eauto.
    {
      simpl.
      Lemma Klift k' T t k : kinding T t k -> kinding (TEkinding k' :: T) (lift t) k.
        admit.
      Qed.
      eapply Klift; eauto.
    }
    eapply Kbool.
  Qed.

  Lemma Fle0r n : F0 <= n.
    admit.
  Qed.

  Arguments lift_from_s n s / .
  Arguments lift_from_f n f / .
  Arguments map_stats / .
  Arguments lift_t_f nv nq / .
  Arguments lift_f_f n nv path i / .

  Lemma merge_typing : typing [] merge merge_type F0 size1.
  Proof.
    eapply TPtabs.
    eapply TPabs.
    { eapply Kcmp_type; eapply Kvar; eauto. }  
    simpl.
    eapply TPletrec.
    {
      intros until 0.
      intros H.
      eapply in_singleton_iff in H.
      inject H.
      simpl.
      simpl.
      eapply TPabs.
      { eapply Klist; eapply Kvar; eauto. }
      {
        simpl.
        eapply TPabs.
        { eapply Klist; eapply Kvar; eauto. }
        {
          unfold loop_body.
          simpl.
          eapply TPsubn.
          {
            eapply TPmatch_list.
            { eapply TPvar'; simpl; eauto. }
            {
              Arguments is_list / .
              simpl; eauto.
            }
            { 
              eapply TPsubs.
              { eapply TPvar'; simpl; eauto. }
              {
                simpl.
                Lemma Sle_var_addr x n1 n2 : Svar x <= Sstats (n1 + Fvar x false, n2 + Fvar x true).
                  admit.
                Qed.
                eapply Sle_var_addr.
              }
            }
            {
              simpl.
              eapply TPmatch_list.
              { eapply TPvar'; simpl; eauto. }
              { simpl; eauto. }
              { 
                eapply TPsubs.
                { eapply TPvar'; simpl; eauto. }
                {
                  simpl.
                  Lemma Sle_var_addl x n1 n2 : Svar x <= Sstats (Fvar x false + n1, Fvar x true + n2).
                    admit.
                  Qed.
                  eapply Sle_var_addl.
                }
              }
              {
                Lemma TPif T e e1 e2 n s t' na nb s' :
                  typing T e Tbool n s ->
                  typing T e1 t' na s' ->
                  typing T e2 t' nb s' ->
                  typing T (Eif e e1 e2) t' (n + max na nb) s'.
                Proof.
                  admit.
                Qed.
                eapply TPif.
                {
                  Lemma TPapp' T e1 e2 ta tb f g n1 n2 s1 s2 t' n' s' : 
                    typing T e1 (Tarrow ta f g tb) n1 s1 ->
                    typing T e2 ta n2 s2 ->
                    t' = subst s2 tb ->
                    n' = n1 + n2 + subst s2 f ->
                    s' = subst s2 g ->
                    typing T (Eapp e1 e2) t' n' s'.
                  Proof.
                    intros; subst; eapply TPapp; eauto.
                  Qed.
                  eapply TPapp'.
                  {
                    eapply TPapp'. 
                    { eapply TPvar'; simpl; eauto; simpl; eauto. }
                    { eapply TPvar'; simpl; eauto. }
                    {
                      Arguments subst_size_type n v b / .
                      Arguments lower_t_f n nv nq / .
                      simpl; eauto.
                    }
                    { eauto. }
                    { eauto. }
                  }
                  { eapply TPvar'; simpl; eauto. }
                  { simpl; eauto. }
                  { eauto. }
                  { eauto. }
                }
                {
                  simpl.
                  Lemma TPcons_app T telm e ls n1 s1 n2 s2 t' s' : 
                    let tlist := Tlist $ telm in
                    typing T e telm n1 s1 ->
                    typing T ls tlist n2 s2 -> 
                    t' = tlist ->
                    s' = Sfold (Spair s1 s2) ->
                    typing T (Econs $$ telm $$ e $$ ls) t' (n1 + n2 + F1) s'.
                  Proof.
                    admit.
                  Qed.
                  eapply TPsubs.
                  {
                    eapply TPcons_app.
                    { eapply TPvar'; simpl; eauto. }
                    {
                      Arguments lift_from_e n e / .
                      simpl.
                      eapply TPapp'.
                      {
                        eapply TPapp'. 
                        Arguments add_snd {A B} b a / .
                        { eapply TPvar'; simpl; eauto; simpl; eauto. }
                        { eapply TPvar'; simpl; eauto. }
                        { simpl; eauto. }
                        { eauto. }
                        { eauto. }
                      }
                      { eapply TPvar'; simpl; eauto. }
                      { simpl; eauto. }
                      { eauto. }
                      { eauto. }
                    }
                    { simpl; eauto. }
                    { eauto. }
                  }
                  {
                    Arguments subst_size_size n v b / .
                    Arguments subst_s_f_f n v nv path i / .
                    Arguments query_idx idx s / .
                    simpl.
                    Lemma Sle_stats s f1 f2 : let ss := summarize s in fst ss <= f1 -> snd ss <= f2 -> s <= Sstats (f1, f2).
                      admit.
                    Qed.
                    eapply Sle_stats; simpl.
                    { admit. (* Fle pair *) }
                    { admit. (* Fle pair *) }
                  }
                }
                {
                  simpl.
                  eapply TPsubs.
                  {
                    eapply TPcons_app.
                    { eapply TPvar'; simpl; eauto. }
                    {
                      simpl.
                      eapply TPapp'.
                      {
                        eapply TPapp'. 
                        { eapply TPvar'; simpl; eauto; simpl; eauto. }
                        { eapply TPvar'; simpl; eauto. }
                        { simpl; eauto. }
                        { eauto. }
                        { eauto. }
                      }
                      { eapply TPvar'; simpl; eauto. }
                      { simpl; eauto. }
                      { eauto. }
                      { eauto. }
                    }
                    { simpl; eauto. }
                    { eauto. }
                  }
                  {
                    simpl.
                    eapply Sle_stats; simpl.
                    { admit. (* Fle pair *) }
                    { admit. (* Fle pair *) }
                  }
                }
              }
            }
          }
          {
            simpl.
            admit.
          }
        }
      }
    }
    { eapply TPvar'; simpl; eauto. }
  Qed.

(*
  Definition lower0 `{Lower t} := lower 0.

  Definition lowerby `{Lower t} n := iter n lower0.

  Lemma lowerby_liftby n (a b : size) : lowerby n a <= b -> a <= liftby n b.
    admit.
  Qed.

  {
    Arguments lowerby / .
    Arguments lower_s / .
    Arguments lower_f / .
    simpl.
    eapply (@lowerby_liftby 2).
    simpl.

  }
  {
    simpl.
    simpl.
    simpl.
  }
 *)
    
End LambdaO.

