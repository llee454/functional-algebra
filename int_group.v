(**
  This module defines the group of integers.

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

Require Import group.
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
