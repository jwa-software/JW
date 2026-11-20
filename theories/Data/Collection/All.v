(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

(* Umbrella for [JW.Data.Collection]: re-exports every collection type and
 * every interface they answer to, so a client imports them with
 * [From JW Require Import Data.Collection.All].
 *)

(* The modules below only [Import] [Core.All], so the open scope reaches a
 * client of this umbrella only from here.
 *)
From JW Require Export Core.All.

(* An umbrella exports every type the interfaces under it name: [Nat0]
 * for the index [nth], [take] and [drop] count with, [Option] for what [nth]
 * returns, [Nat] for [NonEmptyList]'s length, [Bool] for the deciders,
 * [Assert] for the reflection laws that read a decider as a proposition,
 * [Comparison] for what [compare] returns, [Comparable] for the premise of
 * its laws, and [Product] for the pairs that [pop], [zip], [unzip],
 * [partition], [split_at] and [BST.pop_minimum] return.
 *)
From JW Require Export Data.Assert.
From JW Require Export Data.Base.Bool.
From JW Require Export Data.Base.Comparison.
From JW Require Export Data.Comparable.
From JW Require Export Data.Number.Nat.
From JW Require Export Data.Number.Nat0.
From JW Require Export Data.Option.
From JW Require Export Data.Product.

From JW Require Export Data.Collection.AVL.
From JW Require Export Data.Collection.BST.
From JW Require Export Data.Collection.BinaryTree.
From JW Require Export Data.Collection.List.
From JW Require Export Data.Collection.Membership.
From JW Require Export Data.Collection.NonEmptyList.
From JW Require Export Data.Collection.Sized.
From JW Require Export Data.Collection.SortedSet.
From JW Require Export Data.Functor.
