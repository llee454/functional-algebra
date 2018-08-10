Functional Algebra Module Readme
================================

This package provides a Coq formalization of abstract algebra using a functional programming style.

The modules contained within the package span monoids, groups, rings, and fields and provides both axiom definitions for these structures and proofs of foundational results. The current package contains over 800 definitions and proofs.

Why Another Algebra Module?
---------------------------

This module is unique in that it eschews the imperative tactic-oriented style of traditional Coq developments. As pointed out by others, programs written using tactics are brittle, hard to read, and generally inefficient. 

While tactic driven development is useful for sketching out proofs, these disadvantages should dissuade us from leaving proofs in this form.

In this library, I provide a worked example of using Gallina directly and demonstrate both the feasibility of this approach and its advantages in terms of clarity, maintainability, and compile-time efficiency.

In doing so, I follow the practice of the Agda community in exploiting the beauty of a dependently typed functional programming language to full effect.

Hopefully, this example will inspire others within the Coq community to do the same.

Organization
------------

This package uses record structures to represent algebraic structures. In the development, I parallel the traditional hierarchy of algebraic structures. Accordingly, I start by defining monoids (monoid.v), then proceed to define groups, abelian groups, etc.. The current development progresses to fields (field.v).

Every algebraic structure is represented by a module and a record type. For example, monoids are defined by the Monoid module, which is defined in monoid.v. Each monoid has an associated set of components and axioms. For example, every monoid has a binary function (a component) and an axiom saying that this function is associative (an axiom). These components and axioms are defined within a record.

The module defining the algebraic structure includes both the record and any basic theorems associated with the structure. 

The hierarchy of algebraic structures is modeled through inclusion. For example, every group has an associated monoid; every ring has an associated group and an associated monoid; etc.

We map theorems from one level to the next. For example, identity elements are unique in both groups and monoids, and groups inherit their proof of this property from monoids. Instead of requiring users to call this theorem from the monoid associated with a group, we define a theorem at the group level that maps onto the underlying monoid proof.



