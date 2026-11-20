(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

From JW Require Import Core.All.
From JW Require Import Core.Class.

Module Semigroup. (* Semigroup *)

Class T {A : Type} (op : A -> A -> A) : Prop :=
  { associativity
    : forall (x : A) (y : A) (z : A) . op (op x y) z = op x (op y z) }.

Abbreviation Semigroup := T.

End Semigroup. (* Semigroup *)

Abbreviation Semigroup := Semigroup.T.
