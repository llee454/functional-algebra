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
Require Import binary_tree.
Import Binary_Tree.
Require Import monoid.
Require Import monoid_expr.
Require Import group.
Require Import Bool.
Require Import List.
Import ListNotations.
Import Group.

Module GroupExpr.

Open Scope group_scope.

(*
Section Definitions.

  Our plan:

  I. represent group expressions as trees
  II. push negations to leaves
  III. right associate trees to form lists
  IV. cancel negations
  V. filter identities

  Now, the monoid_expr module defines a type for representing arbitrary binary trees - BTree.
  It then defines a projection from terms to monoids. We need a projection from terms to groups.
  With this projection, it defines a function for mapping trees to monoids. We need a projection from trees to groups.
  With this projection to monoids, it defines equality between trees.
  Then we define the shift operation and prove that the resulting tree is equivalent to the original tree.

  The shift operation preserves equality over trees that represents groups.
  How do we reuse this result?
  we need to be able to prove Monoid.BTree_eq -> Group.BTree_eq

  When we say that every group is a monoid, we literally pass the group element set to Monoid as the monoid element set. Accordingly, every x : Group.E is in Monoid.E.
  BTree_eval t is an element of E. 

  We need to define a tree that represents group expressions - that has nodes that represent negation.
  We then map these onto binary trees with terms that can represent 0, constants, and negated constants, we assume group element equality is decidable.
  We then take the monoid from the group and use monoid_expr to reduce everything.
  This results in a list with terms coding negation.
  The term_map function used by monoid_expr does not require the terms themselves to lose any group information (negation), only that the interface works with them. Accordingly, we can use the group term map interface to cancel negated terms.

  1. define the group term type
  2. define the group term tree type
  3. map group term trees onto binary trees by pushing negation to leaf/term level.
  4. call Monoid_Expr.reduce to produce filtered list of terms equal to original group term tree.
  5. cancelPairs :: [term] -> [term]
     cancelPairs [] = []
     cancelPairs (t0:ts)
       | containsInverse t0 ts
         = cancelPairs $ removeInverse t0 ts -- allows proof that all remaining terms do not have an inverse in list.
       | otherwise
         = t0 :: cancelPairs ts
*)

Section syntax_tree.

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
Inductive Syntax_tree : Set
  := node_op  : Syntax_tree -> Syntax_tree -> Syntax_tree
  |  node_neg : Syntax_tree -> Syntax_tree
  |  leaf     : Term -> Syntax_tree.

End syntax_tree.

Arguments node_op {Term} t u.

Arguments node_neg {Term} t.

Arguments leaf {Term} t.

(*
  TODO: Define a generic term map from a generic term set onto group values.
  then define a function that maps trees containing these terms onto a tree containing monoid_group_terms
*)
Section group_term_map.

(**
  Represents a mapping from abstract terms
  to monoid set elements.
*)
Structure Group_term_map : Type := group_term_map {
  (**
    Represents the monoid set that terms will be 
    projected onto. 
  *)
  group_term_map_group: Group;

  (**
    Represents the set of terms that will be
    used to represent monoid values.
  *)
  group_term_map_term : Set;

  (**
    Accepts a term and returns its projection
    in E.
  *)
  group_term_map_eval : group_term_map_term -> E group_term_map_group;

  (**
    Accepts a term and returns true iff the term
    represents the monoid identity element (0).
  *)
  group_term_map_is_zero : group_term_map_term -> bool;

  (**
    Accepts a term and proves that zero terms
    evaluate to 0.
  *)
  group_term_map_is_zero_thm : forall t, group_term_map_is_zero t = true -> group_term_map_eval t = 0
}.

End group_term_map.

(**
  This section defines the evaluation function for group syntax
  trees.
*)
Section eval_syntax_tree.

(** Represents an arbitrary term map. *)
Variable map : Group_term_map.

Let group : Group := group_term_map_group map. 

(** Represents terms. *)
Let term : Set := group_term_map_term map.

(** Represents syntax trees containing the given terms. *)
Let syntax_tree := Syntax_tree term.

Let E := E (group_term_map_group map).

(** Evaluates syntax trees. *)
Definition syntax_tree_eval
  :  syntax_tree -> E
  := Syntax_tree_rec term
       (fun _ => E)
       (fun _ f _ g => f + g)
       (fun _ f => {-} f)
       (fun t => group_term_map_eval map t).

End eval_syntax_tree.

(**
  We defines a canonical monoid tree for representing group trees
  in which negation has been pushed to the leaves.
*)
Section monoid_group_terms.

(** A group whose values are represented by the given terms. *)
Variable group : Group.

(** The monoid defined over the elements in group. *)
Let monoid : Monoid.Monoid := op_monoid group.

(** Represents values from the given group within monoid trees. *) 
Inductive monoid_group_term : Set
  := monoid_group_term_0     : monoid_group_term
  |  monoid_group_term_const : E group -> monoid_group_term
  |  monoid_group_term_neg   : E group -> monoid_group_term.

(** *)
Definition monoid_group_term_map_eval 
  :  monoid_group_term -> E group
  := monoid_group_term_rec
       (fun _ => E group)
       0
       (fun x => x)
       (fun x => - x).

(**
*)
Definition monoid_group_term_map_is_zero (t : monoid_group_term) : bool
  := match t with
       | monoid_group_term_0 => true
       | _            => false
     end.

(**
*)
Theorem monoid_group_term_map_is_zero_thm
  :  forall t : monoid_group_term, monoid_group_term_map_is_zero t = true -> monoid_group_term_map_eval t = 0.
Proof
  monoid_group_term_ind
    (fun t => monoid_group_term_map_is_zero t = true -> monoid_group_term_map_eval t = 0)
    (fun _ => eq_refl 0)
    (fun _ (H : false = true)
      => False_ind _ (diff_false_true H))
    (fun _ (H : false = true)
      => False_ind _ (diff_false_true H)).

(* Represents the monoid term map. *)
Definition monoid_term_map
  :  Monoid_Expr.Term_map
  := Monoid_Expr.term_map
       monoid
       monoid_group_term
       (monoid_group_term_map_eval)
       (monoid_group_term_map_is_zero)
       (monoid_group_term_map_is_zero_thm).

End monoid_group_terms.

Arguments monoid_group_term_0 {group}.

Arguments monoid_group_term_const {group} t.

Arguments monoid_group_term_neg {group} t.

Arguments monoid_group_term_map_eval {group} t.

Arguments monoid_group_term_map_is_zero {group} t.

Arguments monoid_group_term_map_is_zero_thm {group} t H.

Section push_neg_to_leaves.

(** *)
Variable group_term_map : Group_term_map.

(**
  Represents the group whose values are being represented by the
  given syntax trees.
*)
Let group : Group := group_term_map_group group_term_map.

(** Represents the terms that will be stored in the monoid tree below. *)
Let group_term : Set := group_term_map_term group_term_map.

(* Represents the group syntax trees. From *)
Let group_syntax_tree : Set := Syntax_tree group_term.

(** *)
Let group_syntax_tree_eval
  :  Syntax_tree group_term -> E group
  := syntax_tree_eval group_term_map.

(* Represents the monoid associated with the group. *)
Let monoid := op_monoid group.

(** *)
Let monoid_term_map : Monoid_Expr.Term_map := monoid_term_map group.

(** *)
Let monoid_term : Set := monoid_group_term group.

(** Represents the monoid syntax trees. To *)
Let monoid_syntax_tree : Set := BTree monoid_term.

(** *)
Let monoid_syntax_tree_eval
  :  BTree monoid_term -> E group
  := Monoid_Expr.BTree_eval monoid_term_map.

(**
  Accepts a syntax tree containing [group_monoid_term]s that
  represents a group value [x] and returns a new syntax tree that
  equals [-x].
*)
Definition negate_syntax_tree
  : forall t : monoid_syntax_tree,  
      {u : monoid_syntax_tree | - (monoid_syntax_tree_eval t) = monoid_syntax_tree_eval u}
  := BTree_rec
       monoid_term
       (fun t
          => {u : monoid_syntax_tree | {-} (monoid_syntax_tree_eval t) = monoid_syntax_tree_eval u})
       (fun t
          => exist
               (fun u
                  => {-} (monoid_syntax_tree_eval (Binary_Tree.leaf t)) = monoid_syntax_tree_eval u)
               (Binary_Tree.leaf
                 (monoid_group_term_neg
                   (monoid_group_term_map_eval t)))
               (eq_refl
                 (monoid_syntax_tree_eval
                   (Binary_Tree.leaf
                     (monoid_group_term_const
                       (- (monoid_group_term_map_eval t)))))))
       (fun t f u g
          => let (x, H)  := f in
             let (y, H0) := g in
             exist
               (fun v
                 => {-} (monoid_syntax_tree_eval (Binary_Tree.node t u)) =
                    (monoid_syntax_tree_eval v))
               (Binary_Tree.node y x)
               (eq_refl (monoid_syntax_tree_eval (Binary_Tree.node y x))
                || a + (monoid_syntax_tree_eval x) =
                   (monoid_syntax_tree_eval y) + (monoid_syntax_tree_eval x)
                   @a by H0
                || (- (monoid_syntax_tree_eval u)) + a = _
                   @a by H
                || a = _
                   @a by op_neg_distrib group
                           (monoid_syntax_tree_eval t)
                           (monoid_syntax_tree_eval u))). 

(**
  Accepts a syntax tree containing arbitrary group terms and returns
  an equivalent monoid syntax tree containing [monoid_group_term]s.

  This function effectively distributes negations contained within
  the expression represented by [t] down to the leaf terms. For
  example, given an expression like [-(x + y)] it performs the
  transformation [-y + -x].
*)
Definition push_negation
  :  forall t : group_syntax_tree,
       {u : monoid_syntax_tree | group_syntax_tree_eval t = monoid_syntax_tree_eval u}
  := Syntax_tree_rec
       group_term
       (fun t => {u : monoid_syntax_tree | group_syntax_tree_eval t = monoid_syntax_tree_eval u})
       (fun t f u g
         => let (x, H)  := f in
            let (y, H0) := g in
            exist
              (fun v
                 => group_syntax_tree_eval (node_op t u) = monoid_syntax_tree_eval v)
              (Binary_Tree.node x y)
              (eq_refl (monoid_syntax_tree_eval (Binary_Tree.node x y))
               || a + (monoid_syntax_tree_eval y) = monoid_syntax_tree_eval (Binary_Tree.node x y)
                  @a by H
               || (group_syntax_tree_eval t) + a = monoid_syntax_tree_eval (Binary_Tree.node x y)
                  @a by H0))
       (fun t (f : {u | group_syntax_tree_eval t = monoid_syntax_tree_eval u})
         => let (x, H)  := f in
            let (y, H0) := negate_syntax_tree x in
            exist
              (fun u
                => {-} (group_syntax_tree_eval t) = monoid_syntax_tree_eval u)
              y
              ((f_equal {-} H)
               || {-} (group_syntax_tree_eval t) = a
                  @a by <- H0))
       (fun t
         => exist
              (fun u
                => group_syntax_tree_eval (leaf t) = monoid_syntax_tree_eval u)
              (Binary_Tree.leaf
                (monoid_group_term_const
                  (group_term_map_eval group_term_map t)))
              (eq_refl
                (group_term_map_eval group_term_map t))).

End push_neg_to_leaves.

(**
  This section defines a function that accepts a list of
  [monoid_group_term]s and eliminates pairs of the form
  [[... x, -x, ...]].
*)
Section cancel_negations.

End cancel_negations.

(**
  This section defines the reduce function, which takes a group
  syntax tree that represents a group expression and returns
  an equivalent list of monoid_group_terms that represents the
  original expression with negations distributed and canceled,
  and zero terms eliminated.
*)
Section reduce.

(**
  A mapping from terms used to construct syntax trees and group
  values.
*)
Variable group_term_map : Group_term_map.

(**
  Represents the group whose values are being represented by the
  given syntax trees.
*)
Let group : Group := group_term_map_group group_term_map.

(** Represents the terms that will be stored in the monoid tree below. *)
Let group_term : Set := group_term_map_term group_term_map.

(* Represents the group syntax trees. From *)
Let group_syntax_tree : Set := Syntax_tree group_term.

(** *)
Let group_syntax_tree_eval
  :  Syntax_tree group_term -> E group
  := syntax_tree_eval group_term_map.

(** Represents a map from [monoid_term_map_term]s onto group elements. *)
Let monoid_term_map : Monoid_Expr.Term_map := monoid_term_map group.

(** The terms stored within the syntax tree. *)
Let monoid_term : Set := monoid_group_term group.

(** Represents the monoid syntax trees. To *)
Let monoid_syntax_tree : Set := BTree monoid_term.

(** *)
Let monoid_syntax_tree_eval
  :  BTree monoid_term -> E group
  := Monoid_Expr.BTree_eval monoid_term_map.

(**
*)
Definition reduce
  (t : group_syntax_tree)
  :  {xs : list monoid_term |
       group_syntax_tree_eval t = Monoid_Expr.list_eval monoid_term_map xs}
  := let (u, H)   := push_negation group_term_map t in
     let (xs, H0) := Monoid_Expr.reduce monoid_term_map u in
     exist
       (fun ys => group_syntax_tree_eval t = Monoid_Expr.list_eval monoid_term_map ys)
       xs
       (H || group_syntax_tree_eval t = a @a by <- H0).

End reduce.

Close Scope group_scope.

End GroupExpr.
