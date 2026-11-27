(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

From JW Require Import Core.Logic.Conditional.
From JW Require Import Core.Notations.
From JW Require Import Dialect.All.

Local Unset Elimination Schemes.

(* Falsum is the false proposition: no constructor, so no proof.
 * [discriminate] looks this up by registered name and reports
 * [not found in table: core.False.type] without it.
 *)

Inductive Falsum : Prop := .

Register Falsum as core.False.type.

Module Falsum.

(* The eliminator that [match ... per] takes, written out. With no ctor the
 * [match] has no branch, and that is the whole proof.
 *)
(* [forall (P : Falsum -> Prop) (f : Falsum) . P f] *)
Definition induction
  : forall (P : Falsum -> Prop) (f : Falsum) . P f
  := fun (P : Falsum -> Prop) (f : Falsum) .
       match f with end.

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

(* [discriminate] closes its goal with the eliminator of the false
 * proposition, which it finds by this registration.
 *)
Register Scheme Falsum.induction as ind_dep for Falsum.
