(**
  This module defines the commutative_ring record type which
  represents algebraic commutative rings and provides a collection
  of axioms and theorems describing them.

  Copyright (C) 2018 Larry D. Lee Jr. <llee454@gmail.com>

  This program is free software: you can redistribute it and/or modify
  it under the terms of the GNU Lesser General Public License as
  published by the Free Software Foundation, either version 3 of the
  License, or (at your option) any later version.

  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU Lesser General Public License for more details.

  You should have received a copy of the GNU Lesser General Public
  License along with this program. If not, see
  <https://www.gnu.org/licenses/>.
*)

Require Import Description.
Require Import FunctionalExtensionality.
Require Import base.
Require Import function.
Require Import monoid.
Require Import group.
Require Import abelian_group.
Require Import ring.

Module Commutative_Ring.

(** Represents algebraic commutative rings. *)
Structure Commutative_Ring : Type := commutative_ring {

  (** Represents the set of ring elements. *)
  E : Set;

  (** Represents 0 - the additive identity. *)
  E_0 : E;

  (** Represents 1 - the multiplicative identity. *)
  E_1 : E;

  (** Represents addition. *)
  sum : E -> E -> E;

  (** Represents multiplication. *)
  prod : E -> E -> E;

  (** Asserts that 0 /= 1. *)
  distinct_0_1: E_0 <> E_1;

  (** Asserts that addition is associative. *)
  sum_is_assoc : Monoid.is_assoc E sum;

  (** Asserts that addition is commutative. *)
  sum_is_comm : Abelian_Group.is_comm E sum;

  (** Asserts that 0 is the left identity element. *)
  sum_id_l : Monoid.is_id_l E sum E_0;

  (**
    Asserts that every element has an additive
    inverse.
  *)
  sum_inv_l_ex : forall x : E, exists y : E, sum y x = E_0;

  (** Asserts that multiplication is associative. *)
  prod_is_assoc : Monoid.is_assoc E prod;

  (** Asserts that multiplication is commutative. *)
  prod_is_comm : Abelian_Group.is_comm E prod;

  (** Asserts that 1 is the left identity element. *)
   prod_id_l : Monoid.is_id_l E prod E_1;

  (**
    Asserts that multiplication is left distributive
    over addition.
  *)
  prod_sum_distrib_l : Ring.is_distrib_l E prod sum
}.
 
(**
  Enable implicit arguments for commutative
  ring properties.
*)

Arguments E_0 {c}.

Arguments E_1 {c}.

Arguments sum {c} x y.

Arguments prod {c} x y.

Arguments distinct_0_1 {c} _.

Arguments sum_is_assoc {c} x y z.

Arguments sum_is_comm {c} x y.

Arguments sum_id_l {c} x.

Arguments sum_inv_l_ex {c} x.

Arguments prod_is_assoc {c} x y z.

Arguments prod_id_l {c} x.

Arguments prod_sum_distrib_l {c} x y z.

Arguments prod_is_comm {c} x y.

(** Define notations for ring properties. *)

Notation "0" := E_0 : commutative_ring_scope.

Notation "1" := E_1 : commutative_ring_scope.

Notation "x + y" := (sum x y) (at level 50, left associativity) : commutative_ring_scope.

Notation "{+}" := sum : commutative_ring_scope.

Notation "x # y" := (prod x y) (at level 50, left associativity) : commutative_ring_scope.

Notation "{#}" := prod : commutative_ring_scope.

Open Scope commutative_ring_scope.

Section Theorems.

(**
  Represents an arbitrary commutative ring.

  Note: we use Variable rather than Parameter
  to ensure that the following theorems are
  generalized w.r.t r.
*)
Variable r : Commutative_Ring.

(**
  Represents the set of group elements.

  Note: We use Let to define E as a 
  local abbreviation.
*)
Let E := E r.

(**
  Accepts one ring element, x, and asserts
  that x is the left identity element.
*)
Definition sum_is_id_l := Monoid.is_id_l E {+}.

(**
  Accepts one ring element, x, and asserts
  that x is the right identity element.
*)
Definition sum_is_id_r := Monoid.is_id_r E {+}.

(**
  Accepts one ring element, x, and asserts
  that x is the identity element.
*)
Definition sum_is_id := Monoid.is_id E {+}.

(**
  Accepts one ring element, x, and asserts
  that x is the left identity element.
*)
Definition prod_is_id_l := Monoid.is_id_l E {#}.

(**
  Accepts one ring element, x, and asserts
  that x is the right identity element.
*)
Definition prod_is_id_r := Monoid.is_id_r E {#}.

(**
  Accepts one ring element, x, and asserts
  that x is the identity element.
*)
Definition prod_is_id := Monoid.is_id E {#}.

(** Proves that 1 is the right identity element. *)
Definition prod_id_r
  :  prod_is_id_r 1
  := fun x : E
       => eq_ind_r
            (fun a => a = x)
            (prod_id_l x)
            (prod_is_comm x 1).
 
(**
  Proves that multiplication is right distributive
  over addition.
*)
Definition prod_sum_distrib_r
  :  Ring.is_distrib_r E {#} {+}
  := fun x y z : E
       =>  prod_sum_distrib_l x y z
       || x # (y + z) = a + (x # z) @a by <- prod_is_comm x y
       || x # (y + z) = (y # x) + a @a by <- prod_is_comm x z
       || a = (y # x) + (z # x)     @a by <- prod_is_comm x (y + z).

(**
  Represents the non-commutative ring formed
  by addition and multiplication over E.
*)
Definition ring := Ring.ring E 0 1 {+} {#} distinct_0_1 sum_is_assoc sum_is_comm sum_id_l sum_inv_l_ex prod_is_assoc prod_id_l prod_id_r prod_sum_distrib_l prod_sum_distrib_r.

(**
  Represents the abelian group formed by
  addition over E.
*)
Definition sum_abelian_group := Ring.sum_abelian_group ring.

(**
  Represents the group formed by addition
  over E.
*)
Definition sum_group := Ring.sum_group ring.

(**
  Represents the monoid formed by addition
  over E.
*)
Definition sum_monoid := Ring.sum_monoid ring.

(**
  Represents the monoid formed by
  multiplication over E.
*)
Definition prod_monoid := Ring.prod_monoid ring.

(** Proves that 1 <> 0. *)
Definition distinct_1_0
  :  E_1 (c := r) <> E_0 (c := r)
  := fun H : E_1 = E_0
       => distinct_0_1 (eq_sym H).  

(**
  A predicate that accepts one element, x,
  and asserts that x is nonzero.
*)
Definition nonzero
  : E -> Prop
  := Ring.nonzero ring.

(** Proves that 0 is the right identity element. *)
Definition sum_id_r
  :  sum_is_id_r 0
  := Ring.sum_id_r ring.

(** Proves that 0 is the identity element. *)
Definition sum_id
  :  sum_is_id 0
  := Ring.sum_id ring.

(**
  Accepts two elements, x and y, and
  asserts that y is x's left inverse.
*)
Definition sum_is_inv_l := Monoid.is_inv_l E {+} 0 sum_id. 

(**
  Accepts two elements, x and y, and
  asserts that y is x's right inverse.
*)
Definition sum_is_inv_r := Monoid.is_inv_r E {+} 0 sum_id.

(**
  Accepts two elements, x and y, and
  asserts that y is x's inverse.
*)
Definition sum_is_inv := Monoid.is_inv E {+} 0 sum_id.

(** Asserts that every element has a right inverse. *)
Definition sum_inv_r_ex
  :  forall x : E, exists y : E, sum_is_inv_r x y
  := Ring.sum_inv_r_ex ring.

(** Proves that the left identity element is unique. *)
Definition sum_id_l_uniq
  :  forall x : E, Monoid.is_id_l E {+} x -> x = 0
  := Ring.sum_id_l_uniq ring.

(** Proves that the right identity element is unique. *)
Definition sum_id_r_uniq
  :  forall x : E, Monoid.is_id_r E {+} x -> x = 0
  := Ring.sum_id_r_uniq ring.

(** Proves that the identity element is unique. *)
Definition sum_id_uniq
  :  forall x : E, Monoid.is_id E {+} x -> x = 0
  := Ring.sum_id_uniq ring.

(**
  Proves that for every group element, x,
  its left and right inverses are equal.
*)
Definition sum_inv_l_r_eq
  :  forall x y : E, sum_is_inv_l x y -> forall z : E, sum_is_inv_r x z -> y = z
  := Ring.sum_inv_l_r_eq ring.

(**
  Proves that the inverse relation is
  symmetrical.
*)
Definition sum_inv_sym
  :  forall x y : E, sum_is_inv x y <-> sum_is_inv y x
  := Ring.sum_inv_sym ring.

(** Proves that an element's inverse is unique. *)
Definition sum_inv_uniq
  :  forall x y z :  E, sum_is_inv x y -> sum_is_inv x z -> z = y
  := Ring.sum_inv_uniq ring.

(** Proves that every element has an inverse. *)
Definition sum_inv_ex
  :  forall x : E, exists y : E, sum_is_inv x y
  := Ring.sum_inv_ex ring.

(**
  Proves explicitly that every element has a
  unique inverse.
*)
Definition sum_inv_uniq_ex
  :  forall x : E, exists! y : E, sum_is_inv x y
  := Ring.sum_inv_uniq_ex ring.

(** Proves the left introduction rule. *)
Definition sum_intro_l
  :  forall x y z : E, x = y -> z + x = z + y
  := Ring.sum_intro_l ring.

(** Proves the right introduction rule. *)
Definition sum_intro_r
  :  forall x y z : E, x = y -> x + z = y + z
  := Ring.sum_intro_r ring.

(** Proves the left cancellation rule. *)
Definition sum_cancel_l
  :   forall x y z : E, z + x = z + y -> x = y
  := Ring.sum_cancel_l ring.

(** Proves the right cancellation rule. *)
Definition sum_cancel_r
  :   forall x y z : E, x + z = y + z -> x = y
  := Ring.sum_cancel_r ring.

(**
  Proves that an element's left inverse
  is unique.
*)
Definition sum_inv_l_uniq
  :  forall x y z : E, sum_is_inv_l x y -> sum_is_inv_l x z -> z = y
  := Ring.sum_inv_l_uniq ring.

(**
  Proves that an element's right inverse
  is unique.
*)
Definition sum_inv_r_uniq
  :  forall x y z : E, sum_is_inv_r x y -> sum_is_inv_r x z -> z = y
  := Ring.sum_inv_r_uniq ring.

(**
  Proves that 0 is its own left additive
  inverse.
*)
Definition sum_0_inv_l
  :  sum_is_inv_l 0 0
  := Ring.sum_0_inv_l ring.

(**
  Proves that 0 is its own right additive
  inverse.
*)
Definition sum_0_inv_r
  :  sum_is_inv_r 0 0
  := Ring.sum_0_inv_r ring.

(** Proves that 0 is it's own additive inverse. *)
Definition sum_0_inv
  :  sum_is_inv 0 0
  := Ring.sum_0_inv ring.

(** Represents strongly-specified negation. *)
Definition sum_neg_strong
  :  forall x : E, { y | sum_is_inv x y }
  := Ring.sum_neg_strong ring.

(** Represents negation. *)
Definition sum_neg 
  :  E -> E
  := Ring.sum_neg ring.

Notation "{-}" := (sum_neg) : commutative_ring_scope.

Notation "- x" := (sum_neg x) : commutative_ring_scope.

(**
  Asserts that the negation returns the inverse
  of its argument.
*)
Definition sum_neg_def 
  :  forall x : E, sum_is_inv x (- x)
  := Ring.sum_neg_def ring.

(** Proves that negation is one-to-one *)
Definition sum_neg_inj
  :  is_injective E E sum_neg
  := Ring.sum_neg_inj ring.

(** Proves the cancellation property for negation. *)
Definition sum_cancel_neg
  :  forall x : E, sum_neg (- x) = x
  := Ring.sum_cancel_neg ring.

(** Proves that negation is onto *)
Definition sum_neg_onto
  :  is_onto E E sum_neg
  := Ring.sum_neg_onto ring.

(** Proves that negation is surjective *)
Definition sum_neg_bijective
  :  is_bijective E E sum_neg
  := Ring.sum_neg_bijective ring.

(** Proves that 0's negation is 0. *)
Definition sum_0_neg
  :  - 0 = 0
  := proj2 (sum_neg_def 0)
     || a = 0 @a by <- sum_id_l (- 0).

(**
  Proves that if an element's, x, negation
  equals 0, x must equal 0.
*)
Definition sum_neg_0
  :  forall x : E, - x = 0 -> x = 0
  := fun x H
       => proj2 (sum_neg_def x)
         || x + a = 0 @a by <- H
         || a = 0     @a by <- sum_id_r x.

(**
  Prove that 0 is the only element whose additive
  inverse (negation) equals 0.
*)
Definition sum_neg_0_uniq
  :  unique (fun x => - x = 0) 0
  := conj sum_0_neg 
       (fun x H => eq_sym (sum_neg_0 x H)).

(**
  Accepts one element, x, and asserts
  that x is the identity element.
*)
Definition prod_id
  :  prod_is_id 1
  := Ring.prod_id ring.

(** Proves that the left identity element is unique. *)
Definition prod_id_l_uniq
  :  forall x : E, (Monoid.is_id_l E {#} x) -> x = 1
  := Ring.prod_id_l_uniq ring.

(** Proves that the right identity element is unique. *)
Definition prod_id_r_uniq
  :  forall x : E, (Monoid.is_id_r E {#} x) -> x = 1
  := Ring.prod_id_r_uniq ring.

(** Proves that the identity element is unique. *)
Definition prod_id_uniq
  :  forall x : E, (Monoid.is_id E {#} x) -> x = 1
  := Ring.prod_id_uniq ring.

(** Proves the left introduction rule. *)
Definition prod_intro_l
  :  forall x y z : E, x = y -> z # x = z # y
  := Ring.prod_intro_l ring.

(** Proves the right introduction rule. *)
Definition prod_intro_r
  :  forall x y z : E, x = y -> x # z = y # z
  := Ring.prod_intro_r ring.

(**
  Accepts two elements, x and y, and
  asserts that y is x's left inverse.
*)
Definition prod_is_inv_l := Ring.prod_is_inv_l ring.

(**
  Accepts two elements, x and y, and
  asserts that y is x's right inverse.
*)
Definition prod_is_inv_r := Ring.prod_is_inv_r ring.

(**
  Accepts two elements, x and y, and
  asserts that y is x's inverse.
*)
Definition prod_is_inv := Ring.prod_is_inv ring.

(**
  Accepts one argument, x, and asserts that
  x has a left inverse.
*)
Definition prod_has_inv_l := Ring.prod_has_inv_l ring.

(**
  Accepts one argument, x, and asserts that
  x has a right inverse.
*)
Definition prod_has_inv_r := Ring.prod_has_inv_r ring.

(**
  Accepts one argument, x, and asserts that
  x has an inverse.
*)
Definition prod_has_inv := Ring.prod_has_inv ring.

(**
  Proves that every left inverse must also
  be a right inverse.
*)
Definition prod_is_inv_lr 
  :  forall x y : E, prod_is_inv_l x y -> prod_is_inv_r x y
  := fun x y H
       => H || a = 1 @a by prod_is_comm x y.

(**
  Proves that the left and right inverses of
  an element must be equal.
*)
Definition prod_inv_l_r_eq := Ring.prod_inv_l_r_eq ring.

(**
  Proves that the inverse relationship is
  symmetric.
*)
Definition prod_inv_sym := Ring.prod_inv_sym ring.

(**
  Proves the left cancellation law for elements
  possessing a left inverse.
*)
Definition prod_cancel_l := Ring.prod_cancel_l ring.

(**
  Proves the right cancellation law for
  elements possessing a right inverse.
*)
Definition prod_cancel_r := Ring.prod_cancel_r ring.

(**
  Proves that an element's left inverse
  is unique.
*)
Definition prod_inv_l_uniq := Ring.prod_inv_l_uniq ring.

(**
  Proves that an element's right inverse
  is unique.
*)
Definition prod_inv_r_uniq := Ring.prod_inv_r_uniq ring.

(** Proves that an element's inverse is unique. *)
Definition prod_inv_uniq := Ring.prod_inv_uniq ring.

(** Proves that 1 is its own left multiplicative inverse. *)
Definition recipr_1_l
  :  prod_is_inv_l 1 1
  := Ring.recipr_1_l ring.

(** Proves that 1 is its own right multiplicative inverse. *)
Definition recipr_1_r
  :  prod_is_inv_r 1 1
  := Ring.recipr_1_r ring.

(** Proves that 1 is its own recriprical. *)
Definition recipr_1
  :  prod_is_inv 1 1
  := Ring.recipr_1 ring.

(** Proves that 1 has a left multiplicative inverse. *)
Definition prod_has_inv_l_1
  :  prod_has_inv_l 1
  := Ring.prod_has_inv_l_1 ring.

(** Proves that 1 has a right multiplicative inverse. *)
Definition prod_has_inv_r_1
  :  prod_has_inv_r 1
  := Ring.prod_has_inv_r_1 ring.

(** Proves that 1 has a reciprical *)
Definition prod_has_inv_1
  :  prod_has_inv 1
  := Ring.prod_has_inv_1 ring.

(**
  Asserts that multiplication is
  distributive over addition.
*)
Definition prod_sum_distrib
  :  Ring.is_distrib E {#} {+}
  := Ring.prod_sum_distrib ring.

(**
  Proves that 0 times every number equals 0.

  0 x = 0 x
  (0 + 0) x = 0 x
  0 x + 0 x = 0 x
        0 x = 0
*)
Definition prod_0_l
  :  forall x : E, 0 # x = 0
  := Ring.prod_0_l ring.

(** Proves that 0 times every number equals 0. *)
Definition prod_0_r
  :  forall x : E, x # 0 = 0
  := Ring.prod_0_r ring.

(** Proves that 0 does not have a left multiplicative inverse. *)
Definition prod_0_inv_l
  :  ~ prod_has_inv_l 0
  := Ring.prod_0_inv_l ring.

(** Proves that 0 does not have a right multiplicative inverse. *)
Definition prod_0_inv_r
  :  ~ prod_has_inv_r 0
  := Ring.prod_0_inv_r ring.

(**
  Proves that 0 does not have a multiplicative
  inverse - I.E. 0 does not have a
  reciprocal.
*)
Definition prod_0_inv
  :  ~ prod_has_inv 0
  := Ring.prod_0_inv ring.

(**
  Proves that multiplicative inverses, when
  they exist are always nonzero.
*)
Definition prod_inv_0
  :  forall x y : E, prod_is_inv x y -> nonzero y
  := Ring.prod_inv_0 ring.

(** Represents -1 and proves that it exists. *)
Definition E_n1_strong
  :  { x : E | sum_is_inv 1 x }
  := Ring.E_n1_strong ring.

(** Represents -1. *)
Definition E_n1 : E := Ring.E_n1 ring.

(**
  Defines a symbolic representation for -1
  
  Note: here we represent the inverse of 1
  rather than the negation of 1. Letter we prove
  that the negation equals the inverse.

  Note: brackets are needed to ensure Coq parses
  the symbol as a single token instead of a
  prefixed function call.
*)
Notation "{-1}" := E_n1 : commutative_ring_scope.

(** Asserts that -1 is the additive inverse of 1. *)
Definition E_n1_def
  :  sum_is_inv 1 {-1}
  := Ring.E_n1_def ring.
      
(** Asserts that -1 is the left inverse of 1. *)
Definition E_n1_inv_l
  :  sum_is_inv_l 1 {-1}
  := Ring.E_n1_inv_l ring.

(** Asserts that -1 is the right inverse of 1. *)
Definition E_n1_inv_r
  :  sum_is_inv_r 1 {-1}
  := Ring.E_n1_inv_r ring.

(**
  Asserts that every additive inverse
  of 1 must be equal to -1.
*)
Definition E_n1_uniq
  :  forall x : E, sum_is_inv 1 x -> x = {-1}
  := Ring.E_n1_uniq ring.

(**
  Proves that -1 * x equals the multiplicative
  inverse of x.

  -1 x + x = 0
  -1 x + 1 x = 0
  (-1 + 1) x = 0
  0 x = 0
  0 = 0
*) 
Definition prod_n1_x_inv_l
  :  forall x : E, sum_is_inv_l x ({-1} # x)
  := Ring.prod_n1_x_inv_l ring.

(**
  Proves that x * -1 equals the multiplicative
  inverse of x.

  x -1 + x = 0
*)
Definition prod_x_n1_inv_l
  :  forall x : E, sum_is_inv_l x (x # {-1})
  := Ring.prod_x_n1_inv_l ring.

(** Proves that x + -1 x = 0. *)
Definition prod_n1_x_inv_r
  :  forall x : E, sum_is_inv_r x ({-1} # x)
  := Ring.prod_n1_x_inv_r ring.

(** Proves that x + x -1 = 0. *)
Definition prod_x_n1_inv_r
  :  forall x : E, sum_is_inv_r x (x # {-1})
  := Ring.prod_x_n1_inv_r ring.

(** Proves that -1 x is the additive inverse of x. *)
Definition prod_n1_x_inv
  :  forall x : E, sum_is_inv x ({-1} # x)
  := Ring.prod_n1_x_inv ring.

(** Proves that x -1 is the additive inverse of x. *)
Definition prod_x_n1_inv
  :  forall x : E, sum_is_inv x (x # {-1})
  := Ring.prod_x_n1_inv ring.

(**
  Proves that multiplying by -1 is equivalent
  to negation.
*)
Definition prod_n1_neg
  :  {#} {-1} = sum_neg
  := Ring.prod_n1_neg ring.

(**
  Accepts one element, x, and proves that
  x -1 equals the additive negation of x.
*)
Definition prod_x_n1_neg
  :  forall x : E, x # {-1} = - x
  := Ring.prod_x_n1_neg ring.

(**
  Accepts one element, x, and proves that
  -1 x equals the additive negation of x.
*)
Definition prod_n1_x_neg
  :  forall x : E, {-1} # x = - x
  := Ring.prod_n1_x_neg ring.

(** Proves that -1 x = x -1. *)
Definition prod_n1_eq
  :  forall x : E, {-1} # x = x # {-1} 
  := Ring.prod_n1_eq ring.

(** Proves that the additive negation of 1 equals -1. *)
Definition neg_1
  :  {-} 1 = {-1}
  := Ring.neg_1 ring.

(** Proves that the additive negation of -1 equals 1. *)
Definition neg_n1
  :  sum_neg {-1} = 1
  := Ring.neg_n1 ring.

(**
  Proves that -1 * -1 = 1.

  -1 * -1 = -1 * -1
  -1 * -1 = prod -1 -1
  -1 * -1 = sum_neg -1
  -1 * -1 = 1 
*)
Definition prod_n1_n1
  :  {-1} # {-1} = 1
  := Ring.prod_n1_n1 ring.

(**
  Proves that -1 is its own multiplicative
  inverse.
*)
Definition E_n1_inv
  :  prod_is_inv {-1} {-1}
  := Ring.E_n1_inv ring.

End Theorems.

End Commutative_Ring.
