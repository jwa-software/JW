(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

From JW Require Import Core.All.
From JW Require Import Core.Class.

Module Transitive. (* Transitive *)

Class T {A : Type} (R : A -> A -> Prop) : Prop :=
  { transitivity
    : forall (x : A) (y : A) (z : A) . R x y -> R y z -> R x z }.

Abbreviation Transitive := T.

End Transitive. (* Transitive *)

Abbreviation Transitive := Transitive.T.
