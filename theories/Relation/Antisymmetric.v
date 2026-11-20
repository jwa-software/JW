(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

From jwa Require Import Core.All.
From jwa Require Import Core.Class.

Module Antisymmetric. (* Antisymmetric *)

Class T {A : Type} (R : A -> A -> Prop) : Prop :=
  { antisymmetry
    : forall (x : A) (y : A) . R x y -> R y x -> x = y }.

Abbreviation Antisymmetric := T.

End Antisymmetric. (* Antisymmetric *)

Abbreviation Antisymmetric := Antisymmetric.T.
