Set Implicit Arguments.

Definition option_dec A (x : option A) : {a | x = Some a} + {x = None}.
  destruct x.
  left.
  exists a.
  eauto.
  right.
  eauto.
Qed.

Require Import Frap.
Export Frap.

Fixpoint insert A new n (ls : list A) :=
  match n with
  | 0 => new ++ ls
  | S n => 
    match ls with
    | [] => new
    | a :: ls => a :: insert new n ls
    end
  end.

Fixpoint removen A n (ls : list A) {struct ls} :=
  match ls with
  | [] => []
  | a :: ls =>
    match n with
    | 0 => ls
    | S n => a :: removen n ls
    end
  end.

Definition fmap_forall K A (p : A -> Prop) (m : fmap K A) : Prop := forall k v, m $? k = Some v -> p v.
  
