(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

From JW Require Import Algebra.Commutative.
From JW Require Import Algebra.Monoid.
From JW Require Import Core.All.
From JW Require Import Core.Class.

Module AbelianMonoid. (* AbelianMonoid *)

Class T {A : Type} (op : A -> A -> A) (identity : A) : Prop :=
  { monoid
    :: Monoid op identity
  ; commutative
    :: Commutative op }.

Abbreviation AbelianMonoid := T.

End AbelianMonoid. (* AbelianMonoid *)

Abbreviation AbelianMonoid := AbelianMonoid.T.

(* A [::] field is an instance only where its module is imported;
 * these lines make each one an instance wherever this file is.
 *)
#[export] Existing Instance AbelianMonoid.monoid.
#[export] Existing Instance AbelianMonoid.commutative.
