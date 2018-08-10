(*
  This module defines functions and notations shared by all of the
  modules in this package.
*)

(*
  The following notations are introduced here
  to simplify sequences of algebraic rewrites
  which would otherwise be expressed as long
  sequences of eq_ind*.
*)

Notation "A || B @ X 'by' E"
  := (eq_ind_r (fun X => B) A E) (at level 40, left associativity).

Notation "A || B @ X 'by' <- H"
  := (eq_ind_r (fun X => B) A (eq_sym H)) (at level 40, left associativity).

(*
  The following notation can be used to define
  equality assertions. These are like unittests
  in that they check that a given expression
  reduces to a given value.
*)
Notation "A =:= B"
  := (eq_refl A : A = B) (at level 90).

