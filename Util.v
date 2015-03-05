Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 
Generalizable All Variables.

Require Import List.
Require Import Program.

Class Apply a b c := 
  {
    apply : a -> b -> c
  }.

Infix "$" := apply (at level 85, right associativity) : prog_scope.
Infix "$$" := apply (at level 15, left associativity) : prog_scope.
Infix "<<" := compose (at level 40) : prog_scope.
Infix ">>" := (flip compose) (at level 40) : prog_scope.

Definition apply_arrow {A B} (f : A -> B) x := f x.

Instance Apply_arrow A B : Apply (A -> B) A B :=
  {
    apply := apply_arrow
  }.

Class Max t := 
  {
    max : t -> t -> t
  }.

Class Find key value container := 
  {
    find : key -> container -> option value
  }.

Instance Find_list A : Find nat A (list A) :=
  {
    find k c := @nth_error A c k
  }.

