(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

(* Umbrella for [JW.Relation.Order]: re-exports the four order classes, and
 * the six classes their fields hold, so a client imports them with
 * [From JW Require Import Relation.Order.All].
 *)

(* The modules below only [Import] [Core.All], so the open scope reaches a
 * client of this umbrella only from here.
 *)
From JW Require Export Core.All.

From JW Require Export Relation.Order.PartialOrder.
From JW Require Export Relation.Order.StrictPartialOrder.
From JW Require Export Relation.Order.StrictTotalOrder.
From JW Require Export Relation.Order.TotalOrder.

From JW Require Export Relation.Antisymmetric.
From JW Require Export Relation.Irreflexive.
From JW Require Export Relation.Reflexive.
From JW Require Export Relation.Total.
From JW Require Export Relation.Transitive.
From JW Require Export Relation.Trichotomous.
