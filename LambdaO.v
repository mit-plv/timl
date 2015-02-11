Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 
Generalizable All Variables.

Require Import ListFacts4.
Require Import Omega.

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
(*  
  Inductive var :=
    | Vbound : nat -> var
    (* | Vfree : string -> var *)
  .
*)
  Notation var := nat (only parsing).
  Notation Vbound n := (n : nat).
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

  Definition stat_idx := nat. (* An index indication the statistics you want. *)
  Inductive path_command :=
  | Pfst
  | Psnd
  | Pinl
  | Pinr
  | Punfold
  | Punhide
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
  Delimit Scope formula_scope with F.
  Open Scope F.
  Delimit Scope general_scope with G.
  Open Scope G.

  Class Plus t := 
    {
      plus : t -> t -> t
    }.

  Infix "+" := plus : G.

  Instance Plus_nat : Plus nat :=
    {
      plus := Peano.plus
    }.

  Instance Plus_formula : Plus formula :=
    {
      plus := Fplus
    }.

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
  | Shide (_ : size)
  .

  Definition append_path (x : var_path) p : var_path := (fst x, snd x ++ [p]).

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

  Definition is_hide (s : size) :=
    match s with
      | Svar x => Some (Svar (append_path x Punhide))
      | Shide t => Some t
      | _ => None
    end.

  Definition query_cmd cmd s :=
    match cmd with
      | Pfst => 
        p <- is_pair s ;;
        ret (fst p)
      | Psnd =>
        p <- is_pair s ;;
        ret (snd p)
      | Pinl => has_inl s
      | Pinr => has_inr s
      | Punfold => is_fold s
      | Punhide => is_hide s
    end.

  Fixpoint query_path path s :=
    match path with
      | cmd :: path => 
        s <- query_cmd cmd s ;;
        query_path path s
      | nil => ret s
    end.

  Definition stats_get (idx : stat_idx) (ss : stats) := 
    match ss with
      | (n0, n1) =>
        match idx with
          | 0 => n0
          | _ => n1
        end
    end.

  Class Max t := 
    {
      max : t -> t -> t
    }.

  Instance Max_formula : Max formula :=
    {
      max := Fmax
    }.

  Definition stats_binop {A} (f : formula -> formula -> A) (a b : stats) :=
    match a, b with
      | (a0, a1), (b0, b1) => (f a0 b0, f a1 b1)
    end.

  Definition stats_plus := stats_binop Fplus.
  Infix "+" := stats_plus : stats_scope.
  Delimit Scope stats_scope with stats.
  Definition stats_max := stats_binop Fmax.
  Instance Max_stats : Max stats :=
    {
      max := stats_max
    }.
  
  Definition ones := (F1, F1).

  Fixpoint summarize (s : size) : stats :=
    match s with
      | Svar x => (Fvar x 0, Fvar x 1)
      | Sstats ss => ss
      | Stt => ones
      | Spair a b => 
        (summarize a + summarize b)%stats
      | Sinlinr a b => 
        max (summarize a) (summarize b)
      | Sinl s => summarize s
      | Sinr s => summarize s
      | Sfold s =>
        (ones + summarize s)%stats
      | Shide s => (F0, F0)
    end.

  Definition query_idx idx s := stats_get idx $ summarize s.
    
  Definition query_path_idx path idx s :=
    s <- query_path path s ;;
    ret (query_idx idx s).
    
  Fixpoint visit_f f fm :=
    match fm with
      | Fvar (nv, path) i => f nv path i
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

  (* 'lower' is a 'dry run' of 'subst', not doing substitution, only lowering bound variables above n *)
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

  Definition map_stats {A} (f : formula -> A) (ss : stats) := 
    match ss with
      | (n0, n1) => (f n0, f n1)
    end.
 
  Fixpoint visit_s (f : (nat -> path -> size) * (formula -> formula)) s :=
    let (fv, ff) := f in
    match s with
      | Svar (nv, path) => fv nv path
      | Sstats ss => Sstats $ map_stats ff ss
      | Stt => Stt
      | Spair a b => Spair (visit_s f a) (visit_s f b)
      | Sinlinr a b => Sinlinr (visit_s f a) (visit_s f b)
      | Sinl s => Sinl (visit_s f s)
      | Sinr s => Sinr (visit_s f s)
      | Sfold s => Sfold (visit_s f s)
      | Shide s => Shide (visit_s f s)
    end.

  Definition subst_s_s_f n v nv path :=
    match nat_cmp nv n with 
      | LT _ => Svar (#nv, path)
      | EQ => default Stt $ query_path path v
      | GT p => Svar (#p, path)
    end.
    
  Definition subst_size_size (n : nat) (v b : size) : size :=
    visit_s 
      (subst_s_s_f n v,
      substn n v) 
      b.

  Instance Subst_size_size : Subst size size :=
    {
      substn := subst_size_size
    }.

  Definition lift_s_f n nv path :=
    let nv :=
        match nat_cmp nv n with
          | LT _ => nv
          | _ => S nv
        end in
    Svar (#nv, path).

  Definition lift_from_s n s :=
    visit_s
      (lift_s_f n,
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
  (* to deal with statistics s2 and s3 *)
  | Thide (_ : type)
  .

  Coercion Tvar : var >-> type.

  Fixpoint visit_t n (f : (nat -> nat -> type) * (nat -> formula -> formula) * (nat -> size -> size)) b :=
    let fv := fst $ fst f in
    let ff := snd $ fst f in
    let fs := snd f in
    match b with
      | Tvar n' => fv n' n
      | Tarrow a time retsize b => Tarrow (visit_t n f a) (ff (S n) time) (fs (S n) retsize) (visit_t (S n) f b)
      | Tconstr _ => b
      | Tuniversal t => Tuniversal (visit_t (S n) f t) 
      | Tabs t => Tabs (visit_t (S n) f t) 
      | Tapp a b => Tapp (visit_t n f a) (visit_t n f b)
      | Trecur t => Trecur (visit_t (S n) f t) 
      | Thide t => Thide (visit_t n f t)
    end.

  (* nv : the number in var
     nq : the number of surrounding quantification layers 
   *)

  Definition lift_t_f nv nq : type := Tvar $
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

  Definition subst_t_t n v b := 
    visit_t 0 (subst_t_t_f n v, lower_sub n, lower_sub n) b.

  Instance Subst_type_type : Subst type type :=
    {
      substn := subst_t_t
    }.

  Definition subst_sub `{Subst V B, Lift V} n v nq b := substn (n + nq) (liftby nq v) b.

  Definition lower_t_f n nv nq : type :=
    match nat_cmp nv (n + nq) with 
      | GT p => #p
      | _ => #nv
    end.

  Definition subst_size_type (n : nat) (v : size) (b : type) : type :=
    visit_t
      0 
      (lower_t_f n,
       subst_sub n v,
       subst_sub n v)
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
    | Efold (_ : type) (_ : expr)
    | Eunfold (_ : type) (_ : expr)
    | Ehide (_ : expr)
    | Eunhide (_ : expr)
  .

  Definition letrec_entry := (type * type * expr)%type.

  Coercion Evar : var >-> expr.
  Coercion Econstr : constr >-> expr.

  Fixpoint visit_e n (f : (nat -> nat -> expr) * (nat -> type -> type)) b :=
    let (fv, ft) := f in
    match b with
      | Evar n' => fv n' n
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
      | Efold t e => Efold (ft n t) (visit_e n f e)
      | Eunfold t e => Eunfold (ft n t) (visit_e n f e)
      | Ehide e =>Ehide (visit_e n f e)
      | Eunhide e =>Eunhide (visit_e n f e)
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

  Definition subst_e_e_f n v nv nq : expr :=
    match nat_cmp nv (n + nq) with 
      | LT _ => #nv
      | EQ => liftby nq v
      | GT p => #p
    end.

  Definition subst_e_e n v b := 
    visit_e 0 (subst_e_e_f n v, lower_sub n) b.

  Instance Subst_expr_expr : Subst expr expr :=
    {
      substn := subst_e_e
    }.

  Definition lower_e_f n nv nq : expr := 
    match nat_cmp nv (n + nq) with 
      | GT p => #p
      | _ => #nv
    end.

  Definition subst_t_e n (v : type) (b : expr) : expr :=
    visit_e
      0
      (lower_e_f n,
       subst_sub n v)
      b.

  Instance Subst_type_expr : Subst type expr :=
    {
      substn := subst_t_e
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
    | Ahide 
  .

  Definition general_apply (f : expr) (a : general_arg) :=
    match a with
      | Aapp e => Eapp f e
      | Atapp t => Etapp f t
      | Afold t => Efold t f
      | Ahide => Ehide f
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
    | CTfold (t : type) (_ : context)
    | CTunfold (t : type) (_ : context)
    | CThide (_ : context)
    | CTunhide (_ : context)
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
      | CTfold t c => Efold t (plug c e)
      | CTunfold t c => Eunfold t (plug c e)
      | CThide c => Ehide (plug c e)
      | CTunhide c => Eunhide (plug c e)
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
        step (Eunfold t2 (Efold t1 v)) v
    | STunhide_hide v :
        IsValue v ->
        step (Eunhide (Ehide v)) v
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
      kinding (add_typing (t1, None) T) t2 0 ->
      kinding T (Tarrow t1 f g t2) 0
  | Kuniversal T t :
      kinding (add_kinding 0 T) t 0 ->
      kinding T (Tuniversal t) 0
  | Krecur T t :
      kinding (add_kinding 0 T) t 0 ->
      kinding T (Trecur t) 0
  | Khide T t :
      kinding T t 0 ->
      kinding T (Thide t) 0
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

  Global Add Relation type teq
      reflexivity proved by Qrefl
      symmetry proved by Qsymm
      transitivity proved by Qtrans
        as teq_rel.

  (* Definition var_to_Svar x := Svar (x, []). *)

  Class Le t :=
    {
      le : t -> t -> Prop
    }.

  Infix "<=" := le : G.

  Instance Le_nat : Le nat :=
    {
      le := Peano.le
    }.

  (* precise less-than relation on formulas *)
  Definition leF : formula -> formula -> Prop.
    admit.
  Defined.

  Instance Le_formula : Le formula :=
    {
      le := leF
    }.

  (* precise less-than relation on sizes *)
  Definition leS : size -> size -> Prop.
    admit.
  Defined.

  Instance Le_size : Le size :=
    {
      le := leS
    }.

  (* big-O less-than relation on formulas *)
  Definition leO : formula -> formula -> Prop.
    admit.
  Defined.

  Infix "<<=" := leO (at level 70) : F.

  Class Equal t :=
    {
      equal : t -> t -> Prop
    }.

  Infix "==" := equal (at level 70) : G.

  Instance Equal_type : Equal type :=
    {
      equal := teq
    }.

  Definition add_snd {A B} (b : B) (a : A) := (a, b).

  Open Scope G.
  Open Scope F.

  Inductive typing : tcontext -> expr -> type -> formula -> size -> Prop :=
  | TPvar T n t s : 
      find n T = Some (TEtyping (t, s)) -> 
      typing T #n (liftby (S n) t) F0 (default (var_to_size #n) (liftby (S n) s))
  | TPapp T e1 e2 ta tb f g n1 n2 nouse s2 : 
      typing T e1 (Tarrow ta f g tb) n1 nouse ->
      typing T e2 ta n2 s2 ->
      typing T (Eapp e1 e2) (subst s2 tb) (n1 + n2 + F1 + subst s2 f) (subst s2 g)
  | TPabs T e t1 t2 n s :
      kinding T t1 0 ->
      typing (add_typing (t1, None) T) e t2 n s ->
      typing T (Eabs t1 e) (Tarrow t1 n s t2) F0 Stt
  (* the metrics on a tapp arrow are fixed to F0 and Stt *)
  | TPtapp T e t2 t n s :
      typing T e (Tuniversal t) n s ->
      typing T (Etapp e t2) (subst t2 t) (n + F1) s
  | TPtabs T e t :
      typing (add_kinding 0 T) e t F0 Stt ->
      typing T (Etabs e) (Tuniversal t) F0 Stt
  | TPlet T t1 e1 e2 t2 n1 n2 s1 s2:
      typing T e1 t1 n1 s1 ->
      typing (add_typing (t1, Some s1) T) e2 t2 n2 s2 ->
      typing T (Elet t1 e1 e2) (subst s1 t2) (n1 + subst s1 n2)%F (subst s1 s2)
  | TPletrec T (defs : list letrec_entry) main t n s :
      let len := length defs in
      let T' := add_typings (map (fst >> fst >> add_snd (Some Stt)) defs) T in
      (forall lhs_t rhs_t e, 
         In (lhs_t, rhs_t, e) defs -> 
         typing T' (Eabs rhs_t e) (liftby len lhs_t) F0 Stt) ->
      typing T' main (liftby len t) (liftby len n) (liftby len s) ->
      typing T (Eletrec defs main) t n s
  | TPmatch_pair T e e' t t1 t2 n s n' s' s1 s2 :
      typing T e (Tprod t1 t2) n s ->
      is_pair s = Some (s1, s2) ->
      let t12 := [(t1, Some s1); (t2, Some s2)] in
      let T' := add_typings t12 T in
      typing T' e' t n' s' ->
      let s12 := [s1; s2] in
      typing T (Ematch_pair e e') (subst_list s12 t) (n + F1 + subst_list s12 n') (subst_list s12 s')
  | TPmatch_inlinr T e e1 e2 t1 t2 n s s1 s2 t n1 n2 s' :
      typing T e (Tsum t1 t2) n s ->
      is_inlinr s = Some (s1, s2) ->
      (* timing constraints are passed forward; size and type constraints are passed backward.
         t' and s' are backward guidance for branches *)
      typing (add_typing (t1, Some s1) T) e1 (lift t) n1 (lift s') -> 
      typing (add_typing (t2, Some s2) T) e2 (lift t) n2 (lift s') -> 
      typing T (Ematch_sum e e1 e2) t (n + F1 + max (subst s1 n1) (subst s2 n2)) s'
  | TPmatch_inl T e e1 e2 t1 t2 n s t' n' s' :
      typing T e (Tsum t1 t2) n (Sinl s) ->
      typing (add_typing (t1, Some s) T) e1 t' n' s' ->
      typing T (Ematch_sum e e1 e2) (subst s t') (n + F1 + subst s n') (subst s s')
  | TPmatch_inr T e e1 e2 t1 t2 n s t' n' s' :
      typing T e (Tsum t1 t2) n (Sinr s) ->
      typing (add_typing (t2, Some s) T) e2 t' n' s' ->
      typing T (Ematch_sum e e1 e2) (subst s t') (n + F1 + subst s n') (subst s s')
  | TPfold T e t n s t1 :
      t == Trecur t1 ->
      typing T e (subst t t1) n s ->
      typing T (Efold t e) t n (Sfold s)
  | TPunfold T e t n s s1 t1 :
      typing T e t n s ->
      is_fold s = Some s1 ->
      t == Trecur t1 ->
      typing T (Eunfold t e) (subst t t1) n s1
  | TPhide T e t n s :
      typing T e t n s ->
      typing T (Ehide e) (Thide t) n (Shide s)
  | TPunhide T e t n s s1 :
      typing T e (Thide t) n s ->
      is_hide s = Some s1 ->
      typing T (Eunhide e) t n s1
  | TPeq T e t1 t2 n s :
      typing T e t1 n s ->
      t1 == t2 ->
      typing T e t2 n s
  | TPsub T e t n n' s s' :
      typing T e t n s ->
      n <<= n' ->
      s <= s' ->
      typing T e t n' s'
  (* built-in constants *)
  | TPpair T : 
      typing T Cpair (Tuniversal $ Tuniversal $ Tarrow #1 F0 Stt $ Tarrow #1 F1 (Spair #1 #0) $ Tprod #3 #2) F0 Stt
  | TPinl T :
      typing T Cinl (Tuniversal $ Tuniversal $ Tarrow #1 F1 (Sinl #0) $ Tsum #2 #1) F0 Stt
  | TPinr T :
      typing T Cinr (Tuniversal $ Tuniversal $ Tarrow #0 F1 (Sinr #0) $ Tsum #2 #1) F0 Stt
  | TPtt T :
      typing T Ctt Tunit F0 Stt
  .

  (* examples *)

  Instance Apply_expr_var_expr : Apply expr var expr :=
    {
      apply a b := Eapp a b
    }.
  
  Instance Apply_type_var_type : Apply type var type :=
    {
      apply a b := Tapp a b
    }.

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

  Definition Tlist := Tabs $ Trecur $ Tsum Tunit $ Tprod (Thide #1) #0.

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
          eapply Kprod'; try eapply Khide; eapply Kvar; simpl; eauto.
        }
      }
    }
  Qed.

  Lemma Qbeta' t1 t2 t' :
    t' = subst t2 t1 ->
    teq (Tapp (Tabs t1) t2) t'.
  Proof.
    intros; subst; eapply Qbeta; eauto.
  Qed.

  Lemma Qlist (t : type) : (Tlist $$ t) == Trecur (Tsum Tunit $ Tprod (Thide (lift t)) #0).
  Proof.
    eapply Qbeta'.
    simpl; eauto.
  Qed.

  Lemma TPapp' T e1 e2 ta tb f g n1 n2 s1 s2 t' : 
    typing T e1 (Tarrow ta f g tb) n1 s1 ->
    typing T e2 ta n2 s2 ->
    t' = subst s2 tb ->
    typing T (Eapp e1 e2) t' (n1 + n2 + F1 + subst s2 f) (subst s2 g).
  Proof.
    intros; subst; eapply TPapp; eauto.
  Qed.

  Lemma TPtapp' T e t2 t n s t' :
    typing T e (Tuniversal t) n s ->
    t' = subst t2 t ->
    typing T (Etapp e t2) t' (n + F1) s.
  Proof.
    intros; subst; eapply TPtapp; eauto.
  Qed.

  Lemma TPvar' T n t s t' s' : 
    find n T = Some (TEtyping (t, s)) -> 
    t' = liftby (S n) t ->
    s' = default (var_to_size #n) (liftby (S n) s) ->
    typing T #n t' F0 s'.
  Proof.
    intros; subst; eapply TPvar; eauto.
  Qed.

  Lemma TPweaken T T' e t n s T'' :
    typing T e t n s ->
    T'' = T ++ T' ->
    typing T'' e t n s.
  Proof.
    admit.
  Qed.

  Lemma TPweaken_empty T e t n s :
    typing [] e t n s ->
    typing T e t n s.
  Proof.
    intros H.
    eapply TPweaken; eauto.
    simpl; eauto.
  Qed.

  Arguments compose / . 
  Arguments flip / . 
  Arguments apply_arrow / . 
  Arguments add_typing / . 
  Arguments add_typings / . 
  Arguments add_kinding / . 

  Arguments subst_t_t n v b / .
  Arguments subst_t_t_f n v nv nq / .
  Arguments liftby / .
  Arguments lift_from_t n t / .

  Arguments Tprod / .

  Arguments subst_size_formula n v b / .

  Arguments add_snd {A B} b a / .

  Arguments lift_from_s n s / .
  Arguments lift_from_f n f / .
  Arguments map_stats / .
  Arguments lift_t_f nv nq / .
  Arguments lift_f_f n nv path i / .

  Arguments subst_size_type n v b / .
  Arguments lower_t_f n nv nq / .

  Arguments lift_s_f n nv path / .
  Arguments subst_size_size n v b / .

  Arguments lift_from_e n e / .

  Arguments subst_s_f_f n v nv path i / .
  Arguments query_idx idx s / .

  Arguments subst_s_s_f n v nv path / .

  Lemma leS_refl (a : size) : a <= a.
    admit.
  Qed.

  Global Add Relation size leS
      reflexivity proved by leS_refl
        as leS_rel.
  
  Lemma leO_refl (a : formula) : a <<= a.
    admit.
  Qed.

  Global Add Relation formula leO
      reflexivity proved by leO_refl
        as leO_rel.
  
  Lemma leF_refl (n : formula) : n <= n.
    admit.
  Qed.

  Global Add Relation formula leF
      reflexivity proved by leF_refl
        as leF_rel.
  
  Lemma TPunfold' T e t n s s1 t1 t' :
    typing T e t n s ->
    is_fold s = Some s1 ->
    t == Trecur t1 ->
    t' = subst t t1 ->
    typing T (Eunfold t e) t' n s1.
  Proof.
    intros; subst; eapply TPunfold; eauto.
  Qed.

  Lemma TPmatch_pair' T e e' t t1 t2 n s n' s' s1 s2 t'' s'' :
    typing T e (Tprod t1 t2) n s ->
    is_pair s = Some (s1, s2) ->
    let t12 := [(t1, Some s1); (t2, Some s2)] in
    let T' := add_typings t12 T in
    typing T' e' t n' s' ->
    let s12 := [s1; s2] in
    t'' = subst_list s12 t ->
    s'' = subst_list s12 s' ->
    typing T (Ematch_pair e e') t'' (n + F1 + subst_list s12 n') s''.
  Proof.
    intros; subst; eapply TPmatch_pair; eauto.
  Qed.

  Definition Eunhide_fst := Etabs $ Etabs $ Eabs (Tprod (Thide #1) #0) $ 
                                       Ematch_pair #0 $
                                       Epair $$ (#4 : type) $$ (#3 : type) $$ (Eunhide #1) $$ #0.

  Lemma TPunhide_fst :
    typing [] Eunhide_fst (Tuniversal $ Tuniversal $ Tarrow (Tprod (Thide #1) #0) F1 (Spair (Svar (#0, [Pfst; Punhide])) (Svar (#0, [Psnd]))) $ Tprod #2 #1) F0 Stt.
  Proof.
    eapply TPtabs.
    eapply TPtabs.
    eapply TPabs.
    { 
      eapply Kprod'; try eapply Khide; eapply Kvar; simpl; eauto.
    }
    simpl.
    eapply TPsub.
    {
      eapply TPmatch_pair'.
      { eapply TPvar'; simpl; eauto; simpl; eauto. }
      { simpl; eauto. }
      {
        simpl.
        eapply TPapp.
        {
          eapply TPapp'.
          {
            eapply TPtapp'.
            {
              eapply TPtapp'.
              { eapply TPpair. }
              { simpl; eauto. }
            }
            { simpl; eauto. }
          }
          {
            eapply TPunhide.
            { eapply TPvar'; simpl; eauto. }
            { simpl; eauto. }
          }
          { simpl; eauto. }
        }
        { eapply TPvar'; simpl; eauto. }
      }
      { simpl; eauto. }
      { eauto. }
    }
    {
      simpl.
      admit. (* leO for time *)
    }
    {
      simpl.
      reflexivity.
    }
  Qed.

  Lemma subst_lift_s_t_n n v (b : type) : visit_t n (lower_t_f 0, subst_sub 0 v, subst_sub 0 v) (iter (S n) (lift_from_t 0) b) = iter n (lift_from_t 0) b.
    admit.
  Qed.
  Lemma subst_lift_s_t v (b : type) : subst_size_type 0 v (lift_from_t 0 b) = b.
    admit.
  Qed.
  Lemma fold_subst_s_t n v b : visit_t 0 (lower_t_f n, subst_sub n v, subst_sub n v) b = subst_size_type n v b.
  Proof.
    eauto.
  Qed.
  Lemma fold_subst_t_t n v b : visit_t 0 (subst_t_t_f n v, lower_sub n, lower_sub n) b = subst_t_t n v b.
  Proof.
    eauto.
  Qed.
  Lemma fold_lift_from_t n t : visit_t n (lift_t_f, lift_from, lift_from) t = lift_from_t n t.
  Proof.
    eauto.
  Qed.

  Lemma fold_lift_from_f n t : visit_f (lift_f_f n) t = lift_from_f n t.
  Proof.
    eauto.
  Qed.

  Lemma fold_lift_from_s n t : visit_s (lift_s_f n, lift_from_f n) t = lift_from_s n t.
  Proof.
    eauto.
  Qed.

  Lemma fold_iter A n f (a : A) : iter n f (f a) = iter (S n) f a.
  Proof.
    eauto.
  Qed.

  Lemma subst_lift_t_t_n' v (x : type) : forall (n m r : nat), m <= r -> (r <= n + m)%nat -> visit_t r (subst_t_t_f 0 v, lower_sub 0, lower_sub 0) (iter (S n) (lift_from_t m) x) = iter n (lift_from_t m) x.
  Proof.
    induction x; intros n m r Hle1 Hle2.
    {
      simpl.
      rename x1 into a.
      rename x2 into b.
      Lemma liftby_arrow n : forall m a tm s b, iter n (lift_from_t m) (Tarrow a tm s b) = Tarrow (iter n (lift_from m) a) (iter n (lift_from (S m)) tm) (iter n (lift_from (S m)) s) (iter n (lift_from (S m)) b).
      Proof.
        induction n; simpl; intros; try rewrite IHn; eauto.
      Qed.
      repeat rewrite liftby_arrow.
      simpl.
      f_equal.
      {
        repeat rewrite fold_lift_from_t in *.
        rewrite fold_iter.
        rewrite IHx1; eauto.
      }
      {
        (* Arguments lower_s n s / . *)
        (* Arguments lower_f n f / . *)
        repeat rewrite fold_lift_from_f in *.
        rewrite fold_iter.
        Lemma lower_iter_lift_f x (n m r : nat) : m <= r -> (r <= n + m)%nat -> lower_f r (iter (S n) (lift_from_f m) x) = iter n (lift_from_f m) x.
          admit.
        Qed.
        eapply lower_iter_lift_f; simpl in *; eauto; omega.
      }
      {
        repeat rewrite fold_lift_from_s in *.
        rewrite fold_iter.
        Lemma lower_iter_lift_s x (n m r : nat) : m <= r -> (r <= n + m)%nat -> lower_s r (iter (S n) (lift_from_s m) x) = iter n (lift_from_s m) x.
          admit.
        Qed.
        eapply lower_iter_lift_s; simpl in *; eauto; omega.
      }
      {
        repeat rewrite fold_lift_from_t in *.
        rewrite fold_iter.
        rewrite IHx2; simpl in *; eauto; omega.
      }
    }
    {
      simpl.
      rename t into c.
      Lemma liftby_constr n : forall m c, iter n (lift_from_t m) (Tconstr c) = Tconstr c.
      Proof.
        induction n; simpl; intros; try rewrite IHn; eauto.
      Qed.
      repeat rewrite liftby_constr.
      simpl.
      eauto.
    }
    {
      Lemma subst_lift_t_t_n_var v (x : var) (n m r : nat) : m <= r -> (r <= n + m)%nat -> visit_t r (subst_t_t_f 0 v, lower_sub 0, lower_sub 0) (iter (S n) (lift_from_t m) x) = iter n (lift_from_t m) x.
      Proof.
        intros Hle1 Hle2.
        simpl.
        Lemma liftby_var n : forall m x, iter n (lift_from_t m) (Tvar x) = Tvar
                                         match nat_cmp x m with
                                           | LT _ => x
                                           | _ => n + x
                                         end.
        Proof.
          induction n; simpl; intros.
          {
            destruct (nat_cmp x m); eauto.
          }
          admit.
          (* destruct (nat_cmp x m). *)
          (* { *)
          (*   rewrite IHn. *)
          (*   destruct (nat_cmp x m); simpl; eauto. *)
        Qed.
        repeat rewrite liftby_var.
        simpl.
        Set Printing Coercions.
        (*here*)
        admit.
      Qed.
      eapply subst_lift_t_t_n_var; eauto.
    }
    {
      simpl.
      Lemma liftby_universal n : forall m x, iter n (lift_from_t m) (Tuniversal x) = Tuniversal (iter n (lift_from_t (S m)) x).
      Proof.
        induction n; simpl; intros; try rewrite IHn; eauto.
      Qed.
      repeat rewrite liftby_universal.
      simpl.
      repeat rewrite fold_lift_from_t in *.
      rewrite fold_iter.
      rewrite IHx; simpl in *; eauto; omega.
    }
    admit.
    admit.
    admit.
    admit.
  Qed.

  Lemma subst_lift_t_t_n (b : type) : forall n v, visit_t n (subst_t_t_f 0 v, lower_sub 0, lower_sub 0) (iter (S n) (lift_from_t 0) b) = iter n (lift_from_t 0) b.
    intros.
    eapply subst_lift_t_t_n'; simpl in *; eauto; omega.
  Qed.

  Lemma subst_lift_t_t v (b : type) : subst_t_t 0 v (lift_from_t 0 b) = b.
  Proof.
    simpl.
    repeat rewrite fold_lift_from_t in *.
    fold (iter 1 (lift_from_t 0) b).
    repeat rewrite subst_lift_t_t_n in *.
    simpl.
    eauto.
  Qed.

  Lemma lift_from_liftby_t n t : lift_from_t n (iter n (lift_from_t 0) t) = iter (S n) (lift_from_t 0) t.
    admit.
  Qed.
  Lemma lift_from_liftby_s n s : lift_from_s n (iter n (lift_from_s 0) s) = iter (S n) (lift_from_s 0) s.
    admit.
  Qed.

  Lemma fold_subst_s_s n v b : visit_s (subst_s_s_f n v, substn n v) b = subst_size_size n v b.
  Proof.
    eauto.
  Qed.

  Lemma subst_lift_s_s v b : subst_size_size 0 v (lift_from_s 0 b) = b.
    admit.
  Qed.

  Lemma fold_subst_s_f n s : visit_f (subst_s_f_f n s) = subst_size_formula n s.
  Proof.
    eauto.
  Qed.
  Lemma subst_lift_s_f v b : subst_size_formula 0 v (lift_from_f 0 b) = b.
    admit.
  Qed.

  Lemma TPunhide_fst_app T A B e n s s1 s2 s1' : 
    typing T e (Tprod (Thide A) B) n s ->
    is_pair s = Some (s1', s2) ->
    is_hide s1' = Some s1 ->
    typing T (Eunhide_fst $$ A $$ B $$ e) (Tprod A B) (n + F1) (Spair s1 s2).
  Proof.
    intros He Hs Hs1'.
    eapply TPsub.
    {
      eapply TPapp'.
      {
        eapply TPtapp'.
        {
          eapply TPtapp'.
          { 
            eapply TPweaken_empty.
            eapply TPunhide_fst.
          }
          { simpl; eauto. }
        }
        { simpl; eauto. }
      }
      {
        repeat rewrite fold_subst_t_t in *.
        repeat rewrite fold_lift_from_t in *.
        repeat rewrite subst_lift_t_t in *.
        eauto.
      }
      { 
        simpl. 
        repeat rewrite fold_lift_from_t in *.
        repeat rewrite fold_subst_s_t in *.
        repeat rewrite subst_lift_s_t in *.
        fold (iter 2 (lift_from_t 0) A).
        repeat rewrite subst_lift_t_t_n in *.
        simpl.
        repeat rewrite fold_subst_s_t in *.
        repeat rewrite fold_lift_from_t in *.
        repeat rewrite subst_lift_s_t in *.
        eauto. 
      }
    }
    {
      simpl.
      admit. (* leO for time *)
    }
    {
      simpl.
      rewrite Hs.
      simpl.
      rewrite Hs1'.
      simpl.
      reflexivity.
    }
  Qed.

  Definition Ematch_list (telm : type) e b_nil b_cons := 
    let tlist := Tlist $$ telm in
    Ematch_sum (Eunfold tlist e) (lift b_nil) (Ematch_pair (Eunhide_fst $$ (lift telm) $$ (lift tlist) $$ #0) $ lift_from 2 b_cons).

  Definition Enil := Etabs $ Efold (Tlist $ #0) (Einl $$ Tunit $$ Tprod (Thide #0) (Tlist $ #0) $$ Ett).
  
  Definition Econs := 
    Etabs $ Eabs #0 $ Eabs (Tlist $ #1) $ 
          let telm := #2 : type in
          let tlist := Tlist $ telm in
          Efold tlist (Einr $$ Tunit $$ Tprod (Thide telm) tlist $$ (Epair $$ Thide telm $$ tlist $$ Ehide #1 $$ #0)).

  Lemma TPcons : 
    typing [] Econs (Tuniversal $ Tarrow #0 F0 Stt $ Tarrow (Tlist $ #1) F1 (Sfold $ Sinr $ Spair (Shide #1) #0) (Tlist $ #2)) F0 Stt.
  Proof.
    eapply TPtabs.
    eapply TPabs.
    { eapply Kvar; eauto. }
    {
      simpl.
      eapply TPabs.
      { eapply Klist; eapply Kvar; eauto. }
      eapply TPfold.
      { eapply Qlist. }
      simpl.
      eapply TPsub.
      {
        eapply TPapp'.
        {
          eapply TPtapp'.
          {
            eapply TPtapp'.
            { eapply TPinr. }
            { simpl; eauto. }
          }              
          { simpl; eauto. }
        }          
        {
          eapply TPapp'.
          {
            eapply TPapp'.
            {
              eapply TPtapp'.
              {
                eapply TPtapp'.
                { eapply TPpair. }
                { simpl; eauto. }
              }
              { simpl; eauto. }
            }
            {
              eapply TPhide.
              eapply TPvar'; simpl; eauto.
            }
            { simpl; eauto. }
          }
          { eapply TPvar'; simpl; eauto. }
          { simpl; eauto. }
        }
        { simpl; eauto. }
      }
      {
        simpl.
        admit. (* leO for time *)
      }
      {
        simpl.
        reflexivity.
      }
    }
  Qed.

  Lemma TPcons_app T telm e ls n1 s1 n2 s2 : 
    let tlist := Tlist $ telm in
    typing T e telm n1 s1 ->
    typing T ls tlist n2 s2 -> 
    typing T (Econs $$ telm $$ e $$ ls) tlist (n1 + n2 + F1) (Sfold $ Sinr $ Spair (Shide s1) s2).
  Proof.
    simpl.
    intros Hx Hxs.
    eapply TPsub.
    {
      eapply TPapp'.
      {
        eapply TPapp'.
        {
          eapply TPtapp'.
          { 
            eapply TPweaken_empty.
            eapply TPcons.
          }
          { 
            simpl. 
            eauto. 
          }
        }
        { eauto. }
        { 
          simpl. 
          eauto. 
        }
      }
      {
        repeat rewrite fold_subst_s_t in *.
        repeat rewrite fold_lift_from_t in *.
        repeat rewrite subst_lift_s_t in *.
        eauto.
      }
      { 
        simpl.
        repeat rewrite fold_subst_s_t in *.
        repeat rewrite fold_lift_from_t in *.
        fold (iter 2 (lift_from_t 0) telm).
        repeat rewrite subst_lift_s_t_n in *.
        simpl.
        repeat rewrite fold_subst_s_t in *.
        repeat rewrite fold_lift_from_t in *.
        repeat rewrite subst_lift_s_t in *.
        eauto. 
      }
    }
    {
      simpl.
      admit. (* leO for time *)
    }
    {
      simpl.
      repeat rewrite fold_subst_s_s in *.
      repeat rewrite fold_lift_from_s in *.
      repeat rewrite subst_lift_s_s in *.
      reflexivity.
    }
  Qed.

  Definition Tbool := Tsum Tunit Tunit.
  Definition Etrue := Einl $$ Tunit $$ Tunit $$ Ett.
  Definition Efalse := Einr $$ Tunit $$ Tunit $$ Ett.
  Definition Eif e b_true b_false :=
    Ematch_sum e (lift b_true) (lift b_false).

(*  
  Definition Tint := Tconstr TCint.
  Variable int_lt : expr.
  Hypothesis TPint_lt : forall T, typing T int_lt (Tarrow Tint F1 Stt $ Tarrow Tint F1 Stt Tbool) F1 Stt.

  Definition list_int := Tlist $$ Tint.
*)

  Lemma Kbool T : kinding T Tbool 0.
  Proof.
    eapply Ksum'; eapply Kunit.
  Qed.

  Definition is_list s :=
    s <- is_fold s ;;
    p <- is_inlinr s ;;
    p <- is_pair (snd p) ;;
    let (s1, s2) := (p : size * size) in
    s1 <- is_hide s1 ;;
    ret (s1, s2).

  Lemma TPsubs T e t n s s' :
    typing T e t n s ->
    s <= s' ->
    typing T e t n s'.
  Proof.
    intros; eapply TPsub; eauto.
    reflexivity.
  Qed.

  Lemma is_list_elim s p : is_list s = Some p -> exists s1 s2 s3 s4, is_fold s = Some s1 /\ is_inlinr s1 = Some (s2, s3) /\ is_pair s3 = Some (s4, snd p) /\ is_hide s4 = Some (fst p).
    admit.
  Qed.

  Lemma TPsubn T e t n s n' :
    typing T e t n s ->
    n <<= n' ->
    typing T e t n' s.
  Proof.
    intros; eapply TPsub; eauto.
    reflexivity.
  Qed.

  Lemma TPmatch_list T e e1 e2 telm n s s1 s2 t' na nb s' :
    let list := Tlist $ telm in
    typing T e list n s ->
    is_list s = Some (s1, s2) ->
    typing T e1 t' na s' ->
    typing (add_typings [(telm, Some s1); (list, Some s2)] T) e2 (liftby 2 t') nb (liftby 2 s') ->
    let s12 := [s1; s2] in
    typing T (Ematch_list telm e e1 e2) t' (n + F1 + max na (subst_list s12 nb)) s'.
  Proof.
    simpl.
    intros He Hs H1 H2.
    unfold Ematch_list.
    eapply is_list_elim in Hs.
    simpl in Hs.
    destruct Hs as [sf [sl [sr [sfst [Hsf [Hslr [Hsp Hh]]]]]]].
    eapply TPsubn.
    {
      eapply TPmatch_inlinr.
      {
        eapply TPunfold'; eauto.
        { eapply Qlist. }
        {
          simpl.
          rewrite fold_subst_t_t in *.
          rewrite fold_lift_from_t in *.
          rewrite subst_lift_t_t.
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
        eapply TPmatch_pair'.
        { 
          simpl.
          eapply TPunhide_fst_app.
          { eapply TPvar'; simpl; eauto; simpl; eauto. }
          Lemma is_pair_lift sp s1 s2 : is_pair sp = Some (s1, s2) -> is_pair (lift sp) = Some (lift s1, lift s2).
            admit.
          Qed.
          { simpl; eapply is_pair_lift; eauto. }
          Lemma is_hide_lift s s' : is_hide s = Some s' -> is_hide (lift s) = Some (lift s').
            admit.
          Qed.
          { simpl; eapply is_hide_lift; eauto. }
        }
        { simpl; eauto. }
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
          rewrite lift_from_liftby_t.
          simpl.
          repeat rewrite fold_subst_s_t in *.
          repeat rewrite fold_lift_from_t in *.
          repeat rewrite subst_lift_s_t.
          eauto.
        }
        {
          simpl.
          repeat rewrite fold_subst_s_s in *.
          repeat rewrite fold_lift_from_s in *.
          fold (iter 2 (lift_from_s 0) s').
          rewrite (@lift_from_liftby_s 2).
          simpl.
          repeat rewrite fold_subst_s_s in *.
          repeat rewrite fold_lift_from_s in *.
          repeat rewrite subst_lift_s_s.
          eauto.
        }
      }
    }
    {
      simpl.
      admit. (* leO *)
      (*
      Lemma leO_plus (a a' b b' : formula) : a <<= a' -> b <<= b' -> a + b <<= a' + b'.
        admit.
      Qed.
      eapply leO_plus; try eapply leO_refl.
      repeat rewrite subst_lift_s_f.
      Lemma leO_maxr (a b b' : formula) : b <<= b' -> max a b <<= max a b'.
        admit.
      Qed.
      eapply leO_maxr.
      simpl.
      repeat rewrite fold_subst_s_f in *.
      Lemma leOadd0r a b : a <<= b -> F0 + a <<= b.
        admit.
      Qed.
      eapply leOadd0r.
      Lemma leO_skip_subst a b v a' : a' = lift a -> a <<= b -> subst_size_formula 0 v a' <<= b.
        admit.
      Qed.
      eapply leO_skip_subst.
      {
        Lemma subst2_lift s2 s1 n : subst_size_formula 0 (lift_from_s 0 s2) (subst_size_formula 0 (lift_from_s 0 s1) (lift_from_f 2 n)) = lift (subst_size_formula 0 s2 (subst_size_formula 0 s1 n)).
          admit.
        Qed.
        eapply subst2_lift.
      }
      {
        eapply leO_refl.
      }
       *)
    }
  Qed.

  Definition Efixpoint tlhs t0 e := Eletrec [(tlhs, t0, e)] #0.

  Lemma TPfixpoint T tlhs t0 e :
    typing (add_typing (tlhs, Some Stt) T) (Eabs t0 e) (lift tlhs) F0 Stt ->
    typing T (Efixpoint tlhs t0 e) tlhs F0 Stt.
  Proof.
    intros H.
    eapply TPletrec.
    {
      intros until 0.
      intros Hin.
      eapply in_singleton_iff in Hin.
      inject Hin.
      simpl.
      eauto.
    }
    { eapply TPvar'; simpl; eauto. }
  Qed.

  Notation Fmult := (Fbinop FBmult).
  Notation Fdiv := (Fbinop FBdiv).
  Notation Flog := (Funop FUlog).

  Class Mult t :=
    {
      mult : t -> t -> t
    }.

  Infix "*" := mult : G.

  Instance Mult_nat : Mult nat :=
    {
      mult := Peano.mult
    }.

  Instance Mult_formula : Mult formula :=
    {
      mult := Fmult
    }.

  Class Div t := 
    {
      div : t -> t -> t
    }.

  Infix "/" := div : G.

  Instance Div_formula : Div formula :=
    {
      div := Fdiv
    }.

  Notation F2 := (F1 + F1).
  Notation Fvar_nil x i := (Fvar (x, []) i).
  Notation "x ! i" := (Fvar_nil x i) (at level 4, format "x ! i").
  Notation "{{ i | f }}" := (Sstats ((fun i => f) 0, (fun i => f) 1)).
  (* Notation "x '!0'" := (Fvar (x, []) false) (at level 3, format "x '!0'"). *)
  (* Notation "x '!1'" := (Fvar (x, []) true) (at level 3, format "x '!1'"). *)
 
  Definition bool_size := Sinlinr Stt Stt.

  Definition merge_loop_type (telm : type) := 
    let list := Tlist $ telm in
    Tarrow list F0 Stt $ Tarrow (lift list) (#1!0 + #0!0) ({{ i | #1!i + #0!i }}) (liftby 2 list).

  Definition cmp_type (A : type) := Tarrow A F0 Stt $ Tarrow (lift A) F1 bool_size Tbool.

  (* merge is equivalent to :
    fun A cmp =>
      fix merge xs ys :=
        match xs with
          | nil => ys
          | x :: xs' => match ys with
                          | nil => xs
                          | y :: ys' => if cmp x y then
                                          x :: merge xs' ys
                                        else
                                          y :: merge xs ys' end end
  *)

  Definition merge_loop (telm : type) (cmp merge : expr) := 
    Ematch_list telm #1(*xs*) (*level 0*)
                #0(*ys*)
                (Ematch_list (liftby 2 telm) #2(*ys*) (*level 2*)
                             #3(*xs*)
                             (Eif (liftby 4 cmp $$ #3(*x*) $$ #1(*y*)) (*level 4*)
                                  (Econs $$ liftby 4 telm $$ #3(*x*) $$ (liftby 4 merge $$ #2(*xs'*) $$ #4(*ys*)))
                                  (Econs $$ liftby 4 telm $$ #1(*y*) $$ (liftby 4 merge $$ #5(*xs*) $$ #0(*ys'*))))).

  Definition merge :=
    Etabs $ Eabs (cmp_type #0) $ 
          Efixpoint (merge_loop_type #1) (Tlist $ #2) $ 
          Eabs (Tlist $ #3) $ 
          merge_loop #4 #3 #2.

  Definition merge_type := 
    Tuniversal $ Tarrow (cmp_type #0) F0 Stt $ merge_loop_type #1.

  Lemma Kcmp_type T t : kinding T t 0 -> kinding T (cmp_type t) 0.
  Proof.
    intros H.
    eapply Karrow; eauto.
    eapply Karrow; eauto.
    {
      simpl.
      Lemma Klift a T t k : kinding T t k -> kinding (a :: T) (lift t) k.
        admit.
      Qed.
      eapply Klift; eauto.
    }
    eapply Kbool.
  Qed.
(*
  Lemma leF0r n : F0 <= n.
    admit.
  Qed.
*)
  (* Ltac copy_as h h' := generalize h; intro h'. *)

  Lemma TPif T e e1 e2 n s' t n1 n2 s s1 s2 :
    typing T e Tbool n s' ->
    is_inlinr s' = Some (s1, s2) ->
    typing T e1 t n1 s ->
    typing T e2 t n2 s ->
    typing T (Eif e e1 e2) t (n + F1 + max n1 n2) s.
  Proof.
    intros He Hs H1 H2.
    {
      eapply TPsubn.
      {
        eapply TPmatch_inlinr.
        { eauto. }
        { eauto. }
        { eapply TPlift; eauto. }
        { eapply TPlift; eauto. }
      }
      {
        simpl.
        repeat rewrite fold_subst_s_f.
        repeat rewrite fold_lift_from_f.
        repeat rewrite subst_lift_s_f.
        reflexivity.
      }
    }
  Qed.
  (*
   *)

  Lemma TPmerge : typing [] merge merge_type F0 Stt.
  Proof.
    eapply TPtabs.
    eapply TPabs.
    { eapply Kcmp_type; eapply Kvar; eauto. }  
    simpl.
    eapply TPfixpoint.
    simpl.
    eapply TPabs.
    { eapply Klist; eapply Kvar; eauto. }
    {
      simpl.
      eapply TPabs.
      { eapply Klist; eapply Kvar; eauto. }
      {
        unfold merge_loop.
        simpl.
        eapply TPsubn.
        {
          eapply TPmatch_list.
          { eapply TPvar'; simpl; eauto. }
          {
            Arguments is_list s / .
            simpl; eauto.
          }
          { 
            eapply TPsubs.
            { eapply TPvar'; simpl; eauto. }
            {
              simpl.
              Lemma leS_var_addr x n0 n1 : Svar x <= Sstats (n0 + Fvar x 0, n1 + Fvar x 1).
                admit.
              Qed.
              eapply leS_var_addr.
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
                Lemma leS_var_addl x n0 n1 : Svar x <= Sstats (Fvar x 0 + n0, Fvar x 1 + n1).
                  admit.
                Qed.
                eapply leS_var_addl.
              }
            }
            {
              simpl.
              eapply TPif.
              {
                eapply TPapp'.
                {
                  eapply TPapp'. 
                  { eapply TPvar'; simpl; eauto; simpl; eauto. }
                  { eapply TPvar'; simpl; eauto. }
                  {
                    simpl; eauto.
                  }
                }
                { eapply TPvar'; simpl; eauto. }
                { simpl; eauto. }
              }
              {
                simpl; eauto.
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
                    }
                    { eapply TPvar'; simpl; eauto. }
                    { simpl; eauto. }
                  }
                }
                {
                  simpl.
                  Lemma leS_stats s f0 f1 : 
                    let ss := summarize s in 
                    stats_get 0 ss <= f0 -> 
                    stats_get 1 ss <= f1 -> 
                    s <= Sstats (f0, f1).
                    admit.
                  Qed.
                  eapply leS_stats; simpl.
                  { admit. (* leF pair *) }
                  { admit. (* leF pair *) }
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
                    }
                    { eapply TPvar'; simpl; eauto. }
                    { simpl; eauto. }
                  }
                }
                {
                  simpl.
                  eapply leS_stats; simpl.
                  { admit. (* leF pair *) }
                  { admit. (* leF pair *) }
                }
              }
            }
          }
        }
        {
          simpl.
          admit. (* leO for time *)
        }
      }
    }
  Qed.

  Definition split_type telm :=
    Tarrow (Tlist $ telm) ((#0!0 + F1) / F2) (Spair {{ i | (#0!i + F1) / F2 }} {{ i | #0!i / F2 }}) (Tprod (Tlist $ lift telm) (Tlist $ lift telm)).

  Definition msort_loop_type telm :=
    Tarrow (Tlist $ telm) (#0!0 * Flog #0!0) (Sstats (#0!0, #0!1)) (Tlist $ lift telm).

  (* msort is equivalent to : 
    fun A split cmp => 
      fix msort xs :=  
        match xs with
          | nil => xs
          | _ :: xs' => match xs' with
                          | nil => xs 
                          | _ => match split xs with
                                   | (ys, zs) => merge (msort ys) (msort zs) end end end
   *)
  
  Definition msort :=
    Etabs $ Eabs (split_type #0) $ Eabs (cmp_type #1) $ Efixpoint (msort_loop_type #2) (Tlist $ #3)
          (Ematch_list #4 #0 
                       #0
                       (Ematch_list #6 #0
                                    #2
                                    (Ematch_pair (Eapp #7 #4)
                                                 (Etapp merge #10 $$ #8 $$ (Eapp #7 #1) $$ (Eapp #7 #0))))).

  Definition msort_type :=
    Tuniversal $ Tarrow (split_type #0) F0 Stt $ Tarrow (cmp_type #1) F0 Stt $ msort_loop_type #2.

  Lemma Ksplit_type T t : kinding T t 0 -> kinding T (split_type t) 0.
  Proof.
    intros H.
    eapply Karrow; eauto.
    { eapply Klist; eauto. }
    eapply Kprod'; eapply Klist; eauto; simpl; eapply Klift; eauto.
  Qed.

  Lemma TPmsort : typing [] msort msort_type F0 Stt.
  Proof.
    eapply TPtabs.
    eapply TPabs.
    { eapply Ksplit_type; eapply Kvar; eauto. }  
    eapply TPabs.
    { eapply Kcmp_type; eapply Kvar; eauto. }  
    simpl.
    eapply TPfixpoint.
    simpl.
    eapply TPabs.
    { eapply Klist; eapply Kvar; eauto. }
    {
      simpl.
      eapply TPsubn.
      {
        eapply TPmatch_list.
        { eapply TPvar'; simpl; eauto. }
        { simpl; eauto. }
        {
          eapply TPsubs.
          { eapply TPvar'; simpl; eauto. }
          {
            simpl.
            eapply leS_stats; simpl; reflexivity.
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
              eapply leS_stats; simpl; reflexivity.
            }
          }
          {
            simpl.
            eapply TPsubs.
            {
              eapply TPmatch_pair'.
              {
                eapply TPapp'.
                { eapply TPvar'; simpl; eauto; simpl; eauto. }
                { eapply TPvar'; simpl; eauto. }
                { simpl; eauto. }
              }
              { simpl; eauto. }
              {
                eapply TPapp'.
                {
                  eapply TPapp'.
                  {
                    eapply TPapp'.
                    {
                      eapply TPeq.
                      {
                        eapply TPtapp.
                        eapply TPweaken_empty.
                        eapply TPmerge.
                      }
                      { simpl; reflexivity. }
                    }
                    { eapply TPvar'; simpl; eauto. }
                    { simpl; eauto. }
                  }
                  {
                    eapply TPapp'.
                    { eapply TPvar'; simpl; eauto; simpl; eauto. }
                    { eapply TPvar'; simpl; eauto. }
                    { simpl; eauto. }
                  }
                  { simpl; eauto. }
                }
                {
                  eapply TPapp'.
                  { eapply TPvar'; simpl; eauto; simpl; eauto. }
                  { eapply TPvar'; simpl; eauto. }
                  { simpl; eauto. }
                }
                { eauto. }
              }
              { eauto. }
              { eauto. }
            }
            {
              simpl.
              Lemma leF_ceil_floor n : (n + F1) / F2 + n / F2 <= n.
                admit.
              Qed.
              eapply leS_stats; simpl; eapply leF_ceil_floor.
            }
          }
        }
      }
      {
        simpl.
        admit. (* leO *)
      }
    }
  Qed.

  Definition split :=
    Etabs $ Efixpoint (split_type #0) #1 $ Ematch_list #2 #0 
          (Epair $$ (Tlist $ #2) $$ (Tlist $ #2) $$ #0 $$ (Enil $ #2))
          $ Ematch_list #4 #0 
          (Epair $$ (Tlist $ #4) $$ (Tlist $ #4) $$ #2 $$ (Enil $ #4))
          $ Ematch_pair ((#5 : expr) $ #0) $ Epair $$ (Tlist $ #8) $$ (Tlist $8) $$ (Econs $$ #8 $$ #5 $$ #1) $$ (Econs $$ #8 $$ #3 $$ #0).

  Lemma TPsplit : typing [] split (Tuniversal (split_type #0)) F0 Stt.
    admit.
  Qed.

  Definition merge_sort := Etabs $ msort $$ #0 $ split $$ #0.

  Definition merge_sort_type :=
    Tuniversal $ Tarrow (cmp_type #0) F0 Stt $ msort_loop_type #1.

  Lemma TPmerge_sort : typing [] merge_sort merge_sort_type F0 Stt.
    admit.
  Qed.

(*

  Definition lower0 `{Lower t} := lower 0.

  Definition lowerby `{Lower t} n := iter n lower0.

  Lemma lowerby_liftby n (a b : size) : lowerby n a <= b -> a <= liftby n b.
    admit.
  Qed.

  Arguments lowerby / .
 *)

End LambdaO.


