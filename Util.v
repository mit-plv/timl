Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 
Generalizable All Variables.

Class Apply a b c := 
  {
    apply : a -> b -> c
  }.

Infix "$" := apply (at level 85, right associativity) : prog_scope.
Infix "$$" := apply (at level 15, left associativity) : prog_scope.

Definition apply_arrow {A B} (f : A -> B) x := f x.

Instance Apply_arrow A B : Apply (A -> B) A B :=
  {
    apply := apply_arrow
  }.

Class Max t := 
  {
    max : t -> t -> t
  }.

