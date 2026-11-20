(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

From JW Require Import Core.All.
From JW Require Import Core.Class.
From JW Require Import Relation.Irreflexive.
From JW Require Import Relation.Transitive.

Module StrictPartialOrder. (* StrictPartialOrder *)

Class T {A : Type} (R : A -> A -> Prop) : Prop :=
  { irreflexivity :: Irreflexive R
  ; transitivity  :: Transitive  R }.

Abbreviation StrictPartialOrder := T.

End StrictPartialOrder. (* StrictPartialOrder *)

Abbreviation StrictPartialOrder := StrictPartialOrder.T.

(* A [::] field is an instance only where its module is imported;
 * these lines make each one an instance wherever this file is.
 *)
#[export] Existing Instance StrictPartialOrder.irreflexivity.
#[export] Existing Instance StrictPartialOrder.transitivity.
