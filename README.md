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
