(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

(* Umbrella for [JW.Core.Logic]: re-exports every connective, so a client
 * imports them all with [From JW Require Import Core.Logic.All].
 *)

(* [Require Export], not a plain [Require]: a notation reaches a client only
 * through [Import].
 *)
From JW Require Export Core.Logic.Abjunction.
From JW Require Export Core.Logic.Biconditional.
From JW Require Export Core.Logic.Conditional.
From JW Require Export Core.Logic.Conjunction.
From JW Require Export Core.Logic.Disjunction.
From JW Require Export Core.Logic.Exists.
From JW Require Export Core.Logic.Falsum.
From JW Require Export Core.Logic.Negation.
From JW Require Export Core.Logic.Sejunction.
From JW Require Export Core.Logic.Syllogism.
From JW Require Export Core.Logic.Verum.

(* Each connective only [Import]s [Core.Notations], so the open scope reaches
 * a client of this umbrella only from here.
 *)
From JW Require Export Core.Notations.
