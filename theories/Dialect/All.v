(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

(* Umbrella for [JW.Dialect]: re-exports every module of the layer, so a
 * file writes its proofs in this library's tactic language by importing
 * [From JW Require Import Dialect.All].
 *
 * The layer is the tactic language itself: Ltac2 with Rocq's own tactic
 * syntax hidden, and the tactics that name no definition of this tree. The
 * tactics built on its logic live in [JW.Tactics].
 *)
From JW Require Export Dialect.Context.
From JW Require Export Dialect.DivideEtImpera.
From JW Require Export Dialect.ExFalso.
From JW Require Export Dialect.Idem.
From JW Require Export Dialect.Ipso.
From JW Require Export Dialect.Leibniz.
From JW Require Export Dialect.Lemma.
From JW Require Export Dialect.Let.
From JW Require Export Dialect.Loanword.
From JW Require Export Dialect.Local.
From JW Require Export Dialect.Ltac.
From JW Require Export Dialect.Match.
From JW Require Export Dialect.Place.
From JW Require Export Dialect.Simpl.
