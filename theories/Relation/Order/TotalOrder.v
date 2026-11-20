(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

From JW Require Import Core.All.
From JW Require Import Core.Class.
From JW Require Import Relation.Order.PartialOrder.
From JW Require Import Relation.Total.

Module TotalOrder. (* TotalOrder *)

Class T {A : Type} (R : A -> A -> Prop) : Prop :=
  { partial_order :: PartialOrder R
  ; totality      :: Total        R }.

Abbreviation TotalOrder := T.

End TotalOrder. (* TotalOrder *)

Abbreviation TotalOrder := TotalOrder.T.

(* A [::] field is an instance only where its module is imported;
 * these lines make each one an instance wherever this file is.
 *)
#[export] Existing Instance TotalOrder.partial_order.
#[export] Existing Instance TotalOrder.totality.
