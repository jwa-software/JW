(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

(* The tactic language is Ltac2, a compiled plugin rather than Rocq syntax.
 * [Ltac2.Init] loads it and makes Ltac2 the proof mode of every file that
 * imports this one; [Export] is what carries both that far, and every file
 * of this layer exports this one in turn.
 *
 * Only the core is loaded. The syntax of Rocq's own tactics -- [intros],
 * [exact] and the rest -- lives in [Ltac2.Notations], which is not imported,
 * so a tactic is written only once this layer has declared it.
 *)
From Ltac2 Require Export Init.
