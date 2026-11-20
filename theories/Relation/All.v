(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

(* Umbrella for [JW.Relation]: re-exports every module of the layer, so a
 * client imports the whole layer with [From JW Require Import Relation.All].
 *)

(* The modules below only [Import] [Core.All], so the open scope reaches a
 * client of this umbrella only from here.
 *)
From JW Require Export Core.All.

From JW Require Export Relation.Accessible.
From JW Require Export Relation.Antisymmetric.
From JW Require Export Relation.Descent.
From JW Require Export Relation.Equivalence.
From JW Require Export Relation.Induced.
From JW Require Export Relation.Irreflexive.
From JW Require Export Relation.Order.All.
From JW Require Export Relation.Reflexive.
From JW Require Export Relation.Symmetric.
From JW Require Export Relation.Total.
From JW Require Export Relation.Transitive.
From JW Require Export Relation.Trichotomous.
From JW Require Export Relation.WellFounded.
