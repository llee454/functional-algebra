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

Section Definitions.

(**
  Represents group values.

  Note: for groups we distinguish between
  negated and unnegated terms. We will use this
  distinction to cancel adjacent terms.
*)
Variable Term : Set.

(**
  Represents group expressions.

  We use trees to represent group
  expressions. Significantly, we add nodes that
  represent negation. Our intention is to
  represent experessions such as `-(x + y)`. We
  will define a transform that "pushes" negations
  down toward the leaves within the tree using
  Group.op_neg_distrib.

  Once pushed down to the leaf level, we can
  use the binary trees that represent monoids
  to simplify the expression. When done, the
  monoid expressions will return a list which
  we can iterate over to cancel terms.
*)
Inductive Tree : Set
  := node_op  : Tree -> Tree -> Tree
  |  node_neg : Tree -> Tree
  |  leaf     : Term -> Tree.

(**
*)
Inductive STree : Set
 := node     : STree -> STree -> STree
 |  leaf_neg : Term -> STree
 |  leaf     : Term -> STree.

End Definitions.

Arguments leaf {Term} x.

Arguments node_op {Term} t u.

Arguments node_neg {Term} t.

(**
  Represents a mapping from abstract terms to
  group set elements.
*)
Structure Term_map : Type := term_map {
  (**
    Represents the group set that terms will be
    projected onto.
  *)
  term_map_m: Group;

  (*
    Represents the set of terms that will be
    used to represent group values.
  *)
  term_map_term : Set;

  (**
    Accepts a term and returns its projection
    in E.
  *)
  term_map_eval : term_map_term -> E term_map_m;

  (**
    Accepts a term and returns true iff the term
    represents the group identity element (0).
  *)
  term_map_is_zero : term_map_term -> bool;

  (**
    Accepts a term and proves that zero terms
    evaluate to 0.
  *)
  term_map_is_zero_thm : forall t, term_map_is_zero t = true -> term_map_eval t = 0
}.

Arguments term_map_eval {t} x.

Arguments term_map_is_zero {t} x.

Arguments term_map_is_zero_thm {t} t0 H.

Section Functions.

(**
  Represents an arbitrary homomorphism mapping
  binary trees onto some set.
*)
Variable map : Term_map.

(** Represents the set of monoid values. *)
Let E := E (term_map_m map).

(** Represents the set of terms. *)
Let Term := term_map_term map.

(** Maps group trees onto group expressions. *)
Definition Tree_eval
  :  Tree Term -> E
  := Tree_rec Term
       (fun _ => E)
       (fun _ f _ g => f + g)
       (fun _ f => {-} f)
       (fun t => term_map_eval t).

(**
  Accepts two monoid expressions and returns
  true iff they are denotationally equivalent -
  I.E. represent the same monoid value.
*)
Definition Tree_eq
  :  Tree Term -> Tree Term -> Prop
  := fun t u => Tree_eval t = Tree_eval u.

(**
  
*)
Definition Tree_simp_neg
  :  forall t : Tree Term, {u : Tree Term | Tree_is_simp_neg u = true /\ Tree_eq t u}

End Functions.

Section Theorems.

(** Represents an arbitrary group. *)
Variable g : Group.

(** Represents the set of group elements. *)
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

End Theorems.

(**
  Note: the unittests given above demonstrate that we use monoid terms to simplify group expressions, but we lose information about negation when we do so. Accordingly, we define an alternate term type that captures this information. 

  The critical functions are BTree_rassoc and reduce. BTree_rassoc needs the fact that terms encapsulate monoidic values to prove its correctness theorem. 
*)

End GroupExpr.
