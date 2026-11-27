(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

(* Umbrella for [JW.Data]: re-exports every module of the layer, so a
 * client imports the whole layer with [From JW Require Import Data.All].
 *)

(* Without [Core.All] a client of this umbrella has no [->]. *)
From JW Require Export Algebra.All.
From JW Require Export Core.All.
From JW Require Export Relation.All.

(* [Export] so a client writes [Option A], not [Option.Option A]. *)
From JW Require Export Data.Assert.
From JW Require Export Data.Base.All.
From JW Require Export Data.Calendar.All.
From JW Require Export Data.Collection.All.
From JW Require Export Data.Comparable.
From JW Require Export Data.Coproduct.
From JW Require Export Data.Discernible.
From JW Require Export Data.Functor.
From JW Require Export Data.Literal.
From JW Require Export Data.Machine.All.
From JW Require Export Data.Number.All.
From JW Require Export Data.Option.
From JW Require Export Data.Product.
From JW Require Export Data.Text.All.
