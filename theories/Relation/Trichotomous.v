(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

From JW Require Import Core.All.
From JW Require Import Core.Class.

Module Trichotomous. (* Trichotomous *)

Class T {A : Type} (R : A -> A -> Prop) : Prop :=
  { trichotomy
    : forall (x : A) (y : A) . R x y \/ x = y \/ R y x }.

Abbreviation Trichotomous := T.

End Trichotomous. (* Trichotomous *)

Abbreviation Trichotomous := Trichotomous.T.
