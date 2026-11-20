(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

From JW Require Import Core.All.
From JW Require Import Core.Class.
From JW Require Import Relation.Antisymmetric.
From JW Require Import Relation.Reflexive.
From JW Require Import Relation.Transitive.

Module PartialOrder. (* PartialOrder *)

Class T {A : Type} (R : A -> A -> Prop) : Prop :=
  { reflexivity  :: Reflexive     R
  ; antisymmetry :: Antisymmetric R
  ; transitivity :: Transitive    R }.

Abbreviation PartialOrder := T.

End PartialOrder. (* PartialOrder *)

Abbreviation PartialOrder := PartialOrder.T.

(* A [::] field is an instance only where its module is imported;
 * these lines make each one an instance wherever this file is.
 *)
#[export] Existing Instance PartialOrder.reflexivity.
#[export] Existing Instance PartialOrder.antisymmetry.
#[export] Existing Instance PartialOrder.transitivity.
