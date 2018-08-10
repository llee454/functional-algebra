(*
  This module defines basic properties for functions.
*)

(* Defines the injective predicate. *)
Definition is_injective (A B : Type) (f : A -> B) : Prop
  := forall x y : A, f x = f y -> x = y.

(* Defines the onto predicate. *)
Definition is_onto (A B : Type) (f : A -> B) : Prop
  := forall y : B, exists x : A, f x = y.

(* Defines the bijective predicate. *)
Definition is_bijective (A B : Type) (f : A -> B) : Prop
  := is_injective A B f /\ is_onto A B f.
