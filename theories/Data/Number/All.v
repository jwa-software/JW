(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

(* Umbrella for [JW.Data.Number]: re-exports the seven number types, so a
 * client imports them with [From JW Require Import Data.Number.All]. The
 * three binary ones arrive through their own group umbrella.
 *)

(* The modules below only [Import] [Core.All], so the open scope reaches a
 * client of this umbrella only from here.
 *)
From JW Require Export Core.All.

(* An umbrella exports every type the interfaces under it name, so that a
 * client can write down what they take and return: [Comparison] for
 * [compare], [Bool] for [eq], [Option] for [sub] and the narrowings, and
 * [Accessible], [Induced] and [WellFounded] for the descent theorems and the
 * instances -- [Nat.order.strict.wellfoundedness] states [Accessible (<) n]
 * outright. Without them a client can call an operation and still be unable
 * to name its result.
 *)
From JW Require Export Data.Base.Bool.
From JW Require Export Data.Base.Comparison.
From JW Require Export Data.Option.
From JW Require Export Relation.Accessible.
From JW Require Export Relation.Induced.
From JW Require Export Relation.WellFounded.

From JW Require Export Data.Number.Binary.All.
From JW Require Export Data.Number.Integer.
From JW Require Export Data.Number.Nat.
From JW Require Export Data.Number.Nat0.
From JW Require Export Data.Number.Numeral.
From JW Require Export Data.Number.Rational.

(* A numeral with no [%] key is an [Integer] wherever no number type is
 * expected: [Nat], [Nat0] and [Integer] bind their scopes to themselves, and
 * this opens the integer one for a client of the umbrella. It opens the
 * scope's notations as well, so a bare [a + b] reads as [Integer.add].
 *)
Open Scope jw_integer_scope.
