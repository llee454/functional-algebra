(**
  This module defines the group of integers and provides a simplifier
  that can be used to simplify integer expressions such as [a +
  -a + b].

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

Require Import monoid.
Require Import monoid_expr.
Require Import group.
Require Import group_expr.
Require Import simplify.
Require Import List.
Import ListNotations.
Import Group.
Require Import ZArith.

Open Scope Z_scope.

Definition int_group : Group
  := group Z Z0 Z.add Z.add_assoc Z.add_0_l Z.add_0_r
       (fun x : Z
          => ex_intro _ (- x) (Z.add_opp_diag_l x))
       (fun x : Z
          => ex_intro _ (-x) (Z.add_opp_diag_r x)).

Close Scope Z_scope.

Module IntGroupExprMap <: GroupExprMapType.

Definition group
  :  Group
  := int_group.

Let monoid
  :  Monoid.Monoid
  := op_monoid int_group.

Let monoid_term_map
  :  Monoid_Expr.Term_map
  := Monoid_Expr.MTerm_map monoid.

Definition term_map
  :  GroupExpr.Group_term_map
  := GroupExpr.group_term_map int_group
       (Monoid_Expr.term_map_term monoid_term_map) 
       (@Monoid_Expr.term_map_eval monoid_term_map)
       (@Monoid_Expr.term_map_is_zero monoid_term_map)
       (@Monoid_Expr.term_map_is_zero_thm monoid_term_map).

(* TODO: this is now called equal *)
Definition eq_dec
  :  forall x y : E int_group, {x = y} + {x <> y}
  := Z.eq_dec.

End IntGroupExprMap.

Module IntGroupExprSemantics <: SemanticsType := GroupExprSemantics (IntGroupExprMap).

Module IntGroupExprSimplifier := Simplifier (IntGroupExprSemantics).

Import IntGroupExprSimplifier.

Open Scope simplify_scope.

(**
  Defines a notation that can be used to prove
  that two monoid expressions, A and B, are
  equal given the term map C.
*)
Notation "'rewrite' A ==> B 'using' C"
  := (reflect A
       as (ltac:(GroupExpr.encode (op_monoid (GroupExpr.group_term_map_group C)) A))
      ==> B
       as (ltac:(GroupExpr.encode (op_monoid (GroupExpr.group_term_map_group C)) B))
      : A = B)
     (at level 40, left associativity)
  : group_expr_scope.

Close Scope simplify_scope.

Section unittest.

Let term_map
  :  GroupExpr.Group_term_map 
  := IntGroupExprMap.term_map.

Let term
  :  Set
  := GroupExpr.group_term_map_term term_map.

Let group
  :  Group
  := GroupExpr.group_term_map_group term_map.

Let monoid
  :  Monoid.Monoid
  := op_monoid group.

Let a := 5%Z : E group.

Let b := 7%Z : E group.

Let E := E group.

Let eq_dec := IntGroupExprMap.eq_dec.

Let xs
  := [
       GroupExpr.monoid_group_term_const a;
       GroupExpr.monoid_group_term_neg a
     ].

Open Scope nat_scope.

Lemma has_neg_pairs_xs
  :  GroupExpr.has_neg_pairs group eq_dec xs.
Proof
  Nat.lt_0_1.

Lemma elim_neg_pair_xs
  :  proj1_sig (GroupExpr.elim_neg_pair group eq_dec xs has_neg_pairs_xs) = [].
Proof
  eq_refl [].

Lemma elim_neg_pairs_xs
  :  proj1_sig (GroupExpr.elim_neg_pairs group eq_dec xs) = [].
Proof
  eq_refl [].

Close Scope nat_scope.

Open Scope group_expr_scope.

Let reflect_test_2
  :  - a + a = 0
  := rewrite (- a + a) ==> (E_0 (g:=group)) using term_map.

Let reflect_test_3
  :  a + - a = 0
  := rewrite (a + - a) ==> (E_0 (g:=group)) using term_map.

Let reflect_test_4
  :  a + - a + b = b
  := rewrite (a + - a + b) ==> b using term_map.

Let reflect_test_5
  :  b + (- a + a) = b
  := rewrite (b + (- a + a)) ==> b using term_map.

Let reflect_test_6
  :  (b + - a) + a = b
  := rewrite (b + - a) + a ==> b using term_map.

Close Scope group_expr_scope.

End unittest.
