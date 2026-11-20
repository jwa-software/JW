(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

From JW Require Import Algebra.Monoid.
From JW Require Import Core.All.
From JW Require Import Core.Class.

Module Group. (* Group *)

Class T {A : Type} (op : A -> A -> A) (identity : A) (inverse : A -> A) : Prop :=
  { monoid
    :: Monoid op identity
  ; inverse
    : forall (x : A) . op (inverse x) x = identity /\ op x (inverse x) = identity }.

Abbreviation Group := T.

End Group. (* Group *)

Abbreviation Group := Group.T.

(* A [::] field is an instance only where its module is imported;
 * this line makes it one wherever this file is.
 *)
#[export] Existing Instance Group.monoid.
