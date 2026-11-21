(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

(* Umbrella for [JW.Data.Number.Binary]: re-exports the three binary number
 * types, so a client imports them with
 * [From JW Require Import Data.Number.Binary.All].
 *
 * A binary number carries its digits, where the unary types carry their value
 * in units, so an operation costs a step per digit rather than per unit.
 * [BinBase] is the positives, [BinWithZero] adds zero, [SignedBin] adds a sign.
 *)
(* The modules below only [Import] [Core.All], so the open scope reaches a
 * client of this umbrella only from here.
 *)
From JW Require Export Core.All.

(* An umbrella exports every type the interfaces under it name, so that a
 * client can write down what they take and return: [Comparison] for
 * [compare], [Bool] for [eq] and [append_bit], [Option] for [sub] and the
 * narrowings, [Nat], [Nat0] and [Integer] for the conversions, the
 * shift counts and the bit indices, [Numeral] for the literals, [Product]
 * for [div], and [Accessible], [Induced] and [WellFounded] for the descent
 * theorems and the instances.
 *)
From JW Require Export Data.Base.Bool.
From JW Require Export Data.Base.Comparison.
From JW Require Export Data.Number.Integer.
From JW Require Export Data.Number.Nat.
From JW Require Export Data.Number.Nat0.
From JW Require Export Data.Number.Numeral.
From JW Require Export Data.Option.
From JW Require Export Data.Product.
From JW Require Export Relation.Accessible.
From JW Require Export Relation.Induced.
From JW Require Export Relation.WellFounded.

From JW Require Export Data.Number.Binary.BinBase.
From JW Require Export Data.Number.Binary.SignedBin.
From JW Require Export Data.Number.Binary.BinWithZero.
