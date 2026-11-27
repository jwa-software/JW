(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

From JW Require Import Core.All.
From JW Require Import Data.Base.Bool.
From JW Require Import Data.Discernible.

Local Unset Elimination Schemes.

Module Endian. (* Endian *)

(* The order in which the bytes of a word are laid out: [Little] puts the
 * least significant byte first, [Big] the most significant.
 *)
Inductive T : Type :=
  | Little : T
  | Big : T.

Abbreviation Endian := T.

(* [Endian -> Endian -> Bool] *)
Definition test := fun (e1 : Endian) (e2 : Endian) .
  match e1, e2 with
  | Little, Little => true
  | Big,    Big    => true
  | _,      _      => false
  end.

(* [Endian -> Endian -> Bool] *)
Abbreviation equivalent := Discernible.equivalent.

(* [Endian -> Endian -> Bool] *)
Abbreviation discern := Discernible.discern.

Module test. (* test *)

(* test.reflection *)
Theorem reflection
  : forall (e1 : Endian) (e2 : Endian) . test e1 e2 = true <-> e1 = e2.
Proof.
  intros e1 e2.
  match &e1 with | | end; match &e2 with | | end; simpl in |- *.
  - divide et impera; intro e; quod idem est.
  - divide et impera; intro e; ex &e quodlibet.
  - divide et impera; intro e; ex &e quodlibet.
  - divide et impera; intro e; quod idem est.
Qed.

End test. (* test *)

Instance discernible
  : Discernible test :=
  {| Discernible.reflection := test.reflection |}.

End Endian. (* Endian *)

Abbreviation Endian := Endian.T.

Existing Instance Endian.discernible.
