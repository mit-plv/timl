Require Import List.
Require Import Util.
Require Import Syntax.
Require Import Subst.

Export Syntax.

Import ListNotations.
Local Open Scope list_scope.
Local Open Scope prog_scope.

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

(* evaluation context *)
Inductive econtext :=
  | ECempty
  | ECapp1 (f : econtext) (arg : expr)
  | ECapp2 (f : expr) (arg : econtext) : IsValue f -> econtext
  | EClet (t : type) (def : econtext) (main : expr)
  | ECletrec (defs : list letrec_entry) (main : econtext) (* Only evaluate main. All the definitions are already values, since that are all functions *)
  | ECmatch_pair (target : econtext) (_ : expr)
  | ECmatch_sum (target : econtext) (a b : expr)
  | ECtapp (f : econtext) (t : type)
  | ECfold (t : type) (_ : econtext)
  | ECunfold (t : type) (_ : econtext)
  | EChide (_ : econtext)
  | ECunhide (_ : econtext)
.

Fixpoint plug (c : econtext) (e : expr) : expr :=
  match c with
    | ECempty => e
    | ECapp1 f arg => Eapp (plug f e) arg
    | ECapp2 f arg _ => Eapp f (plug arg e)
    | EClet t def main => Elet t (plug def e) main
    | ECletrec defs main => Eletrec defs (plug main e)
    | ECmatch_pair target k => Ematch_pair (plug target e) k
    | ECmatch_sum target a b => Ematch_sum (plug target e) a b
    | ECtapp f t => Etapp (plug f e) t
    | ECfold t c => Efold t (plug c e)
    | ECunfold t c => Eunfold t (plug c e)
    | EChide c => Ehide (plug c e)
    | ECunhide c => Eunhide (plug c e)
  end.

Inductive step : expr -> expr -> Prop :=
  | STecontext c e1 e2 : step e1 e2 -> step (plug c e1) (plug c e2)
  | STapp t body arg : IsValue arg -> step (Eapp (Eabs t body) arg) (subst arg body)
  | STlet t v main : IsValue v -> step (Elet t v main) (subst v main)
  | STletrec_instantiate defs c (n : nat) t e : 
      find n defs = Some (t, e) -> 
      step (Eletrec defs (plug c (Evar #n))) (Eletrec defs (plug c e))  (* the definitions are only simplified, but not making any recursive or mutual-recursive call. All these calls are made only in the evaluation of 'main' *)
  | STletrec_finish defs v : IsValue v -> step (Eletrec defs v) v (* this is wrong *)
  (* missing some rules for letrec *)
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

