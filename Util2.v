Set Implicit Arguments.

Require Import List.
Require Import Program.
Require Import Util.

Import ListNotations.
Local Open Scope list_scope.

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

Arguments rev {A} _.

Definition cat_options {A} (ls : list (option A)) := fold_right (fun x acc => match x with Some v => v :: acc | _ => acc end) [] ls.

Local Open Scope prog_scope.

Definition map_option {A B} (f : A -> option B) := cat_options << map f.

Definition add_snd {A B} (b : B) (a : A) := (a, b).

