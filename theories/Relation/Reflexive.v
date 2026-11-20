(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

From JW Require Import Core.All.
From JW Require Import Core.Class.

Module Reflexive. (* Reflexive *)

Class T {A : Type} (R : A -> A -> Prop) : Prop :=
  { reflexivity
    : forall (x : A) . R x x }.

Abbreviation Reflexive := T.

End Reflexive. (* Reflexive *)

Abbreviation Reflexive := Reflexive.T.
