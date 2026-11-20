(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

From JW Require Import Core.All.
From JW Require Import Core.Class.
From JW Require Import Relation.Order.StrictPartialOrder.
From JW Require Import Relation.Trichotomous.

Module StrictTotalOrder. (* StrictTotalOrder *)

Class T {A : Type} (R : A -> A -> Prop) : Prop :=
  { strict_partial_order :: StrictPartialOrder R
  ; trichotomy           :: Trichotomous       R }.

Abbreviation StrictTotalOrder := T.

End StrictTotalOrder. (* StrictTotalOrder *)

Abbreviation StrictTotalOrder := StrictTotalOrder.T.

(* A [::] field is an instance only where its module is imported;
 * these lines make each one an instance wherever this file is.
 *)
#[export] Existing Instance StrictTotalOrder.strict_partial_order.
#[export] Existing Instance StrictTotalOrder.trichotomy.
