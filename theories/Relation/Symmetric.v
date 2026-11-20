(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

From JW Require Import Core.All.
From JW Require Import Core.Class.

Module Symmetric. (* Symmetric *)

Class T {A : Type} (R : A -> A -> Prop) : Prop :=
  { symmetry
    : forall (x : A) (y : A) . R x y -> R y x }.

Abbreviation Symmetric := T.

End Symmetric. (* Symmetric *)

Abbreviation Symmetric := Symmetric.T.
