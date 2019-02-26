(**
  This module defines a functor used by other modules to define
  notations for simplifying algebraic expressions.

  This functor accepts a module that contains a data structure that
  represents syntax trees, a reduction function that simplifies
  expressions encoded by these trees into term lists, and an encoding
  function that parses Gallina expressions into syntax trees. The
  functor then defines a rewrite notation that accepts two Gallina
  terms representing expressions and returns a proof that they are
  equivalent if they can be reduced to the same expression according
  to the given simplification function.

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

Module Type SemanticsType.

Parameter E : Set.

Parameter term : Set.

Parameter syntax_tree : Set.

Parameter syntax_tree_eval : syntax_tree -> E.

Parameter list_eval : list term -> E.

Parameter reduce
  : forall t : syntax_tree,
      {xs : list term | syntax_tree_eval t = list_eval xs}.

End SemanticsType.

Module Simplifier (Semantics : SemanticsType).

(**
  Defines a notation that can be used to prove
  that two monoid expressions are equal using
  proof by reflection.

  We represent both expressions as binary trees
  and reduce both trees to the same canonical
  form demonstrating that their associated monoid
  expressions are equivalent.
*)
Notation "'reflect' x 'as' t ==> y 'as' u"
  := (let r := Semantics.reduce t in
      let s := Semantics.reduce u in
      let v := proj1_sig r in
      let w := proj1_sig s in
      let H
        :  Semantics.list_eval v = Semantics.list_eval w
        := eq_refl (Semantics.list_eval v) : Semantics.list_eval v = Semantics.list_eval w in
      let H0
        :  Semantics.syntax_tree_eval t = Semantics.list_eval v
        := proj2_sig r in
      let H1
        :  Semantics.syntax_tree_eval u = Semantics.list_eval w
        := proj2_sig s in
      let H2
        :  Semantics.syntax_tree_eval t = x
        := eq_refl (Semantics.syntax_tree_eval t) : Semantics.syntax_tree_eval t = x in
      let H3
        :  Semantics.syntax_tree_eval u = y
        := eq_refl (Semantics.syntax_tree_eval u) : Semantics.syntax_tree_eval u = y in
      H
      || a = Semantics.list_eval w @a by H0
      || a = Semantics.list_eval w @a by H2
      || x = a @a by H1
      || x = a @a by H3
      : x = y)
      (at level 40, left associativity).

End Simplifier.
