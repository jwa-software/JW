(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

From JW Require Import Core.All.
From JW Require Import Core.Class.

Module Cancellative. (* Cancellative *)

Class T {A : Type} (op : A -> A -> A) : Prop :=
  { cancellation
    : forall (x : A) (y : A) (z : A) .
      (op x y = op x z -> y = z) /\ (op x y = op z y -> x = z) }.

Abbreviation Cancellative := T.

End Cancellative. (* Cancellative *)

Abbreviation Cancellative := Cancellative.T.
