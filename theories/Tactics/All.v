(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

(* Umbrella for [JW.Tactics]: re-exports every module of the layer, so a
 * client imports the whole layer with [From JW Require Import Tactics.All].
 *)

(* [Require Export], not a plain [Require]: a tactic notation reaches a client
 * only through [Import].
 *)
From JW Require Export Tactics.DeMorgan.
From JW Require Export Tactics.DoubleNegation.
From JW Require Export Tactics.Equation.
From JW Require Export Tactics.Join.
From JW Require Export Tactics.Modus.
From JW Require Export Tactics.Syllogism.
From JW Require Export Tactics.Witness.
