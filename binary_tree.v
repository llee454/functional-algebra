(**
  This module defines the binary tree data type, which is used to
  represent binary trees.

  This library uses binary trees to represent syntax trees.

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
Require Import Bool.

Module Binary_Tree.

Section binary_tree.

(** Represents the values stored in binary trees. *)
Variable Term : Set.

(**
  Represents binary trees.

  Binary trees can be used to represent
  many different types of algebraic
  expressions. Importantly, when flattened,
  they are isomorphic with lists. Flattening,
  projecting onto lists, sorting, and folding
  may be used normalize ("simplify") algebraic
  expressions.
*)
Inductive BTree : Set
  := leaf : Term -> BTree
  |  node : BTree -> BTree -> BTree.

(**
  Accepts a binary tree and returns true iff
  the tree is a node term.
*)
Definition BTree_is_node
  :  BTree -> bool
  := BTree_rec
       (fun _ => bool)
       (fun _ => false)
       (fun _ _ _ _ => true).

(**
  Accepts a binary tree and returns true iff
  the tree is a leaf term.
*)
Definition BTree_is_leaf
  :  BTree -> bool
  := BTree_rec
       (fun _ => bool)
       (fun _ => true)
       (fun _ _ _ _ => false).

(**
  Accepts a binary tree and returns true
  iff the tree is right associative.

  Note: right associative trees are isomorphic
  to lists.
*)
Definition BTree_is_rassoc
  :  BTree -> bool
  := BTree_rec
       (fun _ => bool)
       (fun _ => true)
       (fun t _ _ f
         => BTree_is_leaf t && f).

(**
  Proves that the right subtree in a right
  associative binary tree is also right
  associative.
*)
Theorem BTree_rassoc_thm
  :  forall t u : BTree, BTree_is_rassoc (node t u) = true -> BTree_is_rassoc u = true.
Proof
  fun t u H
    => proj2 (
            andb_prop 
              (BTree_is_leaf t)
              (BTree_is_rassoc u)
              H).

End binary_tree.

Arguments leaf {Term} x.

Arguments node {Term} t u.

Arguments BTree_is_leaf {Term} t.

Arguments BTree_is_node {Term} t.

Arguments BTree_is_rassoc {Term} t.

Arguments BTree_rassoc_thm {Term} t u H.

End Binary_Tree.
