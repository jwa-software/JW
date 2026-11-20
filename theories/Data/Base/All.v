(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

(* Umbrella for [JW.Data.Base]: re-exports the base types, so a client
 * imports them with [From JW Require Import Data.Base.All].
 *
 * A base type is built from no other type: every ctor takes no argument,
 * so the values can be listed. [Empty] has none, [Unit] one, [Bool] two,
 * [Comparison] and [Kleene3] three.
 *)
(* The modules below only [Import] [Core.All], so the open scope reaches a
 * client of this umbrella only from here.
 *)
From JW Require Export Core.All.

From JW Require Export Data.Base.Bool.
From JW Require Export Data.Base.Comparison.
From JW Require Export Data.Base.Empty.
From JW Require Export Data.Base.Kleene3.
From JW Require Export Data.Base.Unit.
