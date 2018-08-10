(*
  The Set module defines the set record type which can be used to
  represent sets and provides a collection of axioms and theorems
  about them.
*)

Inductive set (E : Type) : Type
  := set_null : set E
  |  set_add : set E -> E -> set E.

Axiom set_add_comm : forall (E : Type) (s : set E) (x y : E), set_add (set_add s x) y = set_add (set_add s y) x. 

Parameter set_in : forall E : Type, set E -> E -> bool.

Axiom set_add_in : forall (E : Type) (s : set E) (x : E), set_in (set_add s x) x = true.
