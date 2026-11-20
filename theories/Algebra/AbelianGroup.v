(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

From JW Require Import Algebra.Commutative.
From JW Require Import Algebra.Group.
From JW Require Import Core.All.
From JW Require Import Core.Class.

Module AbelianGroup. (* AbelianGroup *)

Class T {A : Type} (op : A -> A -> A) (identity : A) (inverse : A -> A) : Prop :=
  { group
    :: Group op identity inverse
  ; commutative
    :: Commutative op }.

Abbreviation AbelianGroup := T.

End AbelianGroup. (* AbelianGroup *)

Abbreviation AbelianGroup := AbelianGroup.T.

(* A [::] field is an instance only where its module is imported;
 * these lines make each one an instance wherever this file is.
 *)
#[export] Existing Instance AbelianGroup.group.
#[export] Existing Instance AbelianGroup.commutative.
