(**
  This module can be used to automatically solve equations concerning
  group expressions.

  To do this, we use a technique called reflection. Briefly, we
  represent group expressions as abstract trees, then we call a
  function that "simplifies" these trees to some canonical form. We
  prove that, if two group expressions have the same canonical
  representation, the expressions are equal.

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

Require Import base.
Require Import monoid.
Require Import monoid_expr.
Require Import group.
Import Group.

Module GroupExpr.

Variable g : Group.

Let E := E g.

Let F := Monoid.E (op_monoid g).

Section Unittests.

Variables a b c d : E.

Let map := MonoidExpr.MTerm_map (op_monoid g).

(**
  Proves that every group has a monoid set
  and that group elements can be coerced into
  monoid elements.

  Note: this is significant because it allows
  us to reduce group expressions using functions
  provided by MonoidExpr.
*)
Let E_test_0
  :  F = E
  := eq_refl _.

Let reflect_test_0
  :  (a + b) + (c + ({-} d)) = a + ((b + c) + ({-} d))
  := reflect 
       (a + b) + (c + ({-} d))
         as (({{a : F}} # {{b : F}}) # ({{c : F}} # {{({-} d) : F}}))
       ==>
       a + ((b + c) + ({-} d))
         as ({{a : F}} # (({{b : F}} # {{c : F}}) # {{({-} d) : F}}))
       using map.

End Unittests.

(**
  Note: the unittests given above demonstrate that we use monoid terms to simplify group expressions, but we lose information about negation when we do so. Accordingly, we define an alternate term type that captures this information. 

  The critical functions are BTree_rassoc and reduce. BTree_rassoc needs the fact that terms encapsulate monoidic values to prove its correctness theorem. 
*)

End GroupExpr.
