(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

(* Umbrella for [JW.Algebra]: re-exports every module of the layer, so a
 * client imports the whole layer with [From JW Require Import Algebra.All].
 *)

(* The modules below only [Import] [Core.All], so the open scope reaches a
 * client of this umbrella only from here.
 *)
From JW Require Export Core.All.

From JW Require Export Algebra.AbelianGroup.
From JW Require Export Algebra.AbelianMonoid.
From JW Require Export Algebra.Cancellative.
From JW Require Export Algebra.Commutative.
From JW Require Export Algebra.Group.
From JW Require Export Algebra.Monoid.
From JW Require Export Algebra.Ring.
From JW Require Export Algebra.Semigroup.
From JW Require Export Algebra.Semiring.
