(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

From JW Require Import Core.Logic.Conditional.
From JW Require Import Core.Notations.
From JW Require Import Dialect.All.

(* Falsum is the false proposition: no constructor, so no proof.
 * [discriminate] looks this up by registered name and reports
 * [not found in table: core.False.type] without it.
 *)

Inductive Falsum : Prop := .

Register Falsum as core.False.type.

Module Falsum.

(* Ex falso: a proof of [Falsum] proves anything, since there is no case to
 * handle.
 *)
Theorem elimination : forall (A : Prop) . Falsum -> A.
Proof.
  intro A.
  intro f.
  ex f quodlibet.
Qed.

End Falsum.
