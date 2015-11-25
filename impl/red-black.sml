
(* Red/Black Trees *)
(* Author: Frank Pfenning *)

(* Sorts added by: Frank Pfenning and Rowan Davies *)
(* 
   This is a new version that should be exactly what is in Twelf,
   other than the refinement annotations.  In particular, it uses a
   functor, and creates two instances via functor application.  (There
   was earlier version here from 1997 before functors were
   implemented).
*)

(* First, an interface for Tables *)
(* This provides a common interface to hash tables *)
(* red/black trees and similar data structures *)

signature TABLE =
sig
  type key (* parameter *)
  type 'a entry (* = key * 'a *)

  type 'a Table
  val new : int -> 'a Table             (* includes size hint *)
  val insert : 'a Table -> 'a entry -> unit
  val insertShadow : 'a Table -> 'a entry -> ('a entry) option
  val lookup : 'a Table -> key -> 'a option
  val clear : 'a Table -> unit

  val app : ('a entry -> unit) -> 'a Table -> unit
end;


(* Now the implementation of Red/Black trees in a functor parameterized by the
   type of keys. *)

functor RedBlackTree
  (type key'
   val compare : key' * key' -> order) 
     :> TABLE where type key = key' =  
struct

  type key = key'
  type 'a entry = key * 'a

  datatype 'a dict =                                     (* general dictionaries *)
    Empty | Black of 'a entry * 'a dict * 'a dict        (* Empty is considered black *)
  | Red of 'a entry * 'a dict * 'a dict

(*[  datasort 'a rbt =  Empty | Black of 'a entry * 'a rbt * 'a rbt   (* red/black trees *)
                   | Red of 'a entry * 'a bt * 'a bt
          and 'a bt = Empty | Black of 'a entry * 'a rbt * 'a rbt     (* black root node *)  ]*)
(*[  datasort 'a red = Red of 'a entry * 'a bt * 'a bt             ]*)   (* red root node *)

(*[  datasort 'a badRoot                    (* invariant possibly violated at the root *)
     = Empty | Black of 'a entry * 'a rbt * 'a rbt | Red of 'a entry * 'a rbt * 'a bt
     | Red of 'a entry * 'a bt * 'a rbt  ]*)

(*[  datasort 'a badLeft               (* invariant possibly violated at the left child *)
     = Empty | Black of 'a entry * 'a rbt * 'a rbt | Red of 'a entry * 'a bt * 'a bt
     | Black of 'a entry * 'a badRoot * 'a rbt   ]*)

(*[  datasort 'a badRight              (* invariant possibly violated at the right child *)
     = Empty | Black of 'a entry * 'a rbt * 'a rbt | Red of 'a entry * 'a bt * 'a bt
     | Black of 'a entry * 'a rbt * 'a badRoot  ]*)

  type 'a Table = 'a dict ref

  (* The default refinement is 'a rbt ref.  In particular, this is the sort used to 
     satisfy the signature specification "sort 'a Table", which is implicit in
     "type 'a Table".  Thus, externally to this module, every 'a Table must have this
     refinement. - Rowan *)
  (*[ sortdef 'a Table = 'a rbt ref ]*)

  (* Representation Invariants *)
  (*
     1. The tree is ordered: for every node Red((key1,datum1), left, right) or
        Black ((key1,datum1), left, right), every key in left is less than
        key1 and every key in right is greater than key1.

     2. The children of a red node are black (color invariant).

     3. Every path from the root to a leaf has the same number of
        black nodes, called the black height of the tree.
  *)

  local

  (*[ lookup <: 'a rbt -> key -> 'a option ]*)
  fun lookup (dict:'a dict) key =
    let
      fun lk (Empty) = NONE
        | lk (Red tree) = lk' tree
        | lk (Black tree) = lk' tree
      and lk' ((key1, datum1), left, right) =
            (case compare(key,key1)
               of EQUAL => SOME(datum1)
                | LESS => lk left
                | GREATER => lk right)
      in
        lk dict
      end


  (*
     restore_right (Black(e,l,r)) >=> dict
     where (1) Black(e,l,r) is ordered,
           (2) Black(e,l,r) has black height n,
           (3) color invariant may be violated at the root of r:
               one of its children might be red.
     and dict is a re-balanced red/black tree (satisfying all invariants)
     and same black height n.
  *)
  (*[ restore_right <: 'a badRight -> 'a rbt ]*)
  fun restore_right (Black(e:'a entry, Red lt, Red (rt as (_,Red _,_)))) =
         Red(e, Black lt, Black rt)     (* re-color *)
    | restore_right (Black(e, Red lt, Red (rt as (_,_,Red _)))) =
         Red(e, Black lt, Black rt)     (* re-color *)
    | restore_right (Black(e, l, Red(re, Red(rle, rll, rlr), rr))) =
         (* l is black, deep rotate *)
         Black(rle, Red(e, l, rll), Red(re, rlr, rr))
    | restore_right (Black(e, l, Red(re, rl, rr as Red _))) =
         (* l is black, shallow rotate *)
         Black(re, Red(e, l, rl), rr)
    | restore_right dict = dict


  (* restore_left is like restore_right, except *)
  (* the color invariant may be violated only at the root of left child *)
  (*[ restore_left <: 'a badLeft -> 'a rbt ]*)
  fun restore_left (Black(e:'a entry, Red (lt as (_,Red _,_)), Red rt)) =
         Red(e, Black lt, Black rt)     (* re-color *)
    | restore_left (Black(e, Red (lt as (_,_,Red _)), Red rt)) =
         Red(e, Black lt, Black rt)     (* re-color *)
    | restore_left (Black(e, Red(le, ll as Red _, lr), r)) =
         (* r is black, shallow rotate *)
         Black(le, ll, Red(e, lr, r))
    | restore_left (Black(e, Red(le, ll, Red(lre, lrl, lrr)), r)) =
         (* r is black, deep rotate *)
         Black(lre, Red(le, ll, lrl), Red(e, lrr, r))
    | restore_left dict = dict

  (*[    insert <: 'a rbt * 'a entry -> 'a rbt ]*)
  fun 'a insert (dict, entry as (key,datum)) =
    let
      (* val ins : 'a dict -> 'a dict  inserts entry *)
      (* ins (Red _) may violate color invariant at root *)
      (* ins (Black _) or ins (Empty) will be red/black tree *)
      (* ins preserves black height *)
      (*[ ins1 <: 'a rbt -> 'a badRoot 
                & 'a bt -> 'a rbt  ]*)
      fun ins1 (Empty) = Red(entry, Empty, Empty)
        | ins1 (Red(entry1 as (key1, datum1), left, right)) =
          (case compare(key,key1)
             of EQUAL => Red(entry, left, right)
              | LESS => Red(entry1, ins1 left, right)
              | GREATER => Red(entry1, left, ins1 right))
        | ins1 (Black(entry1 as (key1, datum1), left, right)) =
          (case compare(key,key1)
             of EQUAL => Black(entry, left, right)
              | LESS => restore_left (Black(entry1, ins1 left, right))
              | GREATER => restore_right (Black(entry1, left, ins1 right)))
    in                (* the second conjuct is needed for the recursive cases *)
      case ins1 dict
        of Red (t as (_, Red _, _)) => Black t (* re-color *)
         | Red (t as (_, _, Red _)) => Black t (* re-color *)
         | dict => dict                        (* depend on sequential matching *)
    end


  (* use non-imperative version? *)
  (*[    insertShadow <: 'a rbt * 'a entry -> 'a rbt * 'a entry option ]*)
  fun 'a insertShadow (dict, entry as (key,datum)) =
      let val oldEntry = ref NONE (* : 'a entry option ref *)
          (*[ ins <: 'a rbt -> 'a badRoot  & 'a bt -> 'a rbt   ]*)
          fun ins (Empty) = Red(entry, Empty, Empty)
            | ins (Red(entry1 as (key1, datum1), left, right)) =
              (case compare(key,key1)
                 of EQUAL => (oldEntry := SOME(entry1);
                              Red(entry, left, right))
                  | LESS => Red(entry1, ins left, right)
                  | GREATER => Red(entry1, left, ins right))
            | ins (Black(entry1 as (key1, datum1), left, right)) =
              (case compare(key,key1)
                 of EQUAL => (oldEntry := SOME(entry1);
                              Black(entry, left, right))
                  | LESS => restore_left (Black(entry1, ins left, right))
                  | GREATER => restore_right (Black(entry1, left, ins right)))
      in
        (oldEntry := NONE;
         ((case ins dict
             of Red (t as (_, Red _, _)) => Black t (* re-color *)
              | Red (t as (_, _, Red _)) => Black t (* re-color *)
              | dict => dict),
          !oldEntry))
      end
  
  (*[ app <: ('a entry -> unit) -> 'a rbt -> unit ]*)
  fun app (f:'a entry -> unit) dict =
      let fun ap (Empty) = ()
            | ap (Red tree) = ap' tree
            | ap (Black tree) = ap' tree
          and ap' (entry1, left, right) =
              (ap left; f entry1; ap right)
      in
        ap dict
      end

  in
    (*[ new <: int -> 'a rbt ref ]*)
    fun new (n:int) = ref (Empty : 'a dict) (* ignore size spec *)
    (*[ insert  <: 'a rbt ref -> 'a entry -> unit  ]*)
    val insert = (fn table => fn entry : 'a entry => (table := insert (!table, entry)))
    (*[ insertShadow <: 'a rbt ref -> 'a entry -> 'a entry option ]*)
    val insertShadow =
        (fn table => fn entry : 'a entry => 
         let
           val (dict, oldEntry) = insertShadow (!table, entry)
         in
           (table := dict; oldEntry)
         end)

    (*[ lookup <: 'a rbt ref -> key -> 'a  option  ]*)
    val lookup = (fn table : 'a dict ref => fn key => lookup (!table) key)
    (*[ clear <: 'a rbt ref -> unit  ]*)
    val clear = (fn table : 'a dict ref => (table := Empty))
    (*[ app <: ('a entry -> unit) -> 'a rbt ref -> unit  ]*)
    val app = (fn f => fn table : 'a dict ref => app f (!table))
  end
end;  (* structure RedBlackTree *)

structure StringRedBlackTree =
  RedBlackTree (type key' = string
                val compare = String.compare)

structure IntRedBlackTree =
  RedBlackTree (type key' = int
                val compare = Int.compare)

