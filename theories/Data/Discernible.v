(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

From JW Require Import Core.All.
From JW Require Import Data.Base.Bool.
From JW Require Import Tactics.Equation.
From JW Require Import Tactics.Modus.

Module Discernible. (* Discernible *)

(* A [test] that tells any two values of [A] apart: it answers [true]
 * exactly when the two are equal.
 *)
Class T {A : Type} (test : A -> A -> Bool) : Prop :=
  { reflection
    : forall (a : A) (b : A) .
      test a b = true <-> a = b }.

Abbreviation Discernible := T.

(* [true] when [a] and [b] are equal. [test] is found through its instance
 * when it is left out, and is written [(test := t)] when it is given.
 *)
(* [forall {A : Type} {test : A -> A -> Bool} {D : Discernible test} . A -> A -> Bool] *)
Definition equivalent := fun {A : Type} {test : A -> A -> Bool} {D : Discernible test}
  (a : A) (b : A) .
  test a b.

(* [true] when [a] and [b] differ, the opposite of [equivalent]. *)
(* [forall {A : Type} {test : A -> A -> Bool} {D : Discernible test} . A -> A -> Bool] *)
Definition discern := fun {A : Type} {test : A -> A -> Bool} {D : Discernible test}
  (a : A) (b : A) .
  Bool.negate (test a b).

Module equivalence. (* equivalence *)

(* equivalence.reflection *)
Theorem reflection
  : forall {A : Type} {test : A -> A -> Bool} {D : Discernible test} (a : A) (b : A) .
      equivalent a b = true <-> a = b.
Proof.
  intros A test D a b.
  simpl equivalent in |- *.
  ipso (Discernible.reflection &a &b).
Qed.

(* equivalence.reflexivity *)
Theorem reflexivity
  : forall {A : Type} {test : A -> A -> Bool} {D : Discernible test} (a : A) .
      equivalent a a = true.
Proof.
  intros A test D a.
  ipso (modus aequans (equivalence.reflection &a &a), (Identity.reflexivity &a)).
Qed.

(* equivalence.refutation *)
Theorem refutation
  : forall {A : Type} {test : A -> A -> Bool} {D : Discernible test} (a : A) (b : A) .
      equivalent a b = false <-> ~ (a = b).
Proof.
  intros A test D a b.
  let proof r := equivalence.reflection &a &b.
  match (equivalent &a &b) with | | end.
  - divide et impera.
    + intro e.
      ex &e quodlibet.
    + intro n.
      ex (&n (modus aequans &r, (Identity.reflexivity true))) quodlibet.
  - divide et impera.
    + intro e.
      simpl (~ _) in |- *.
      intro h.
      let proof t := modus aequans &r, &h.
      ex &t quodlibet.
    + intro n.
      quod idem est.
Qed.

(* equivalence.symmetry *)
Theorem symmetry
  : forall {A : Type} {test : A -> A -> Bool} {D : Discernible test} (a : A) (b : A) .
      equivalent a b = equivalent b a.
Proof.
  intros A test D a b.
  let proof forth := equivalence.reflection &a &b.
  let proof back := equivalence.reflection &b &a.
  match (equivalent &a &b) with | | end; match (equivalent &b &a) with | | end.
  - quod idem est.
  - let proof ab := modus aequans &forth, (Identity.reflexivity true).
    let proof t := modus aequans &back, (symm &ab).
    ex &t quodlibet.
  - let proof ba := modus aequans &back, (Identity.reflexivity true).
    let proof t := modus aequans &forth, (symm &ba).
    ex &t quodlibet.
  - quod idem est.
Qed.

End equivalence. (* equivalence *)

Module discernment. (* discernment *)

(* discernment.complement *)
Theorem complement
  : forall {A : Type} {test : A -> A -> Bool} {D : Discernible test} (a : A) (b : A) .
      discern a b = Bool.negate (equivalent a b).
Proof.
  intros A test D a b.
  simpl discern, equivalent in |- *.
  quod idem est.
Qed.

(* discernment.reflection *)
Theorem reflection
  : forall {A : Type} {test : A -> A -> Bool} {D : Discernible test} (a : A) (b : A) .
      discern a b = true <-> ~ (a = b).
Proof.
  intros A test D a b.
  leibniz (discernment.complement &a &b) in |- *.
  let proof r := equivalence.refutation &a &b.
  match (equivalent &a &b) with | | end; simpl in |- *.
  - divide et impera.
    + intro e.
      ex &e quodlibet.
    + intro n.
      let proof t := modus aequans &r, &n.
      ex &t quodlibet.
  - divide et impera.
    + intro e.
      ipso (modus aequans &r, (Identity.reflexivity false)).
    + intro n.
      quod idem est.
Qed.

(* discernment.refutation *)
Theorem refutation
  : forall {A : Type} {test : A -> A -> Bool} {D : Discernible test} (a : A) (b : A) .
      discern a b = false <-> a = b.
Proof.
  intros A test D a b.
  leibniz (discernment.complement &a &b) in |- *.
  let proof r := equivalence.reflection &a &b.
  match (equivalent &a &b) with | | end; simpl in |- *.
  - divide et impera.
    + intro e.
      ipso (modus aequans &r, (Identity.reflexivity true)).
    + intro e.
      quod idem est.
  - divide et impera.
    + intro e.
      ex &e quodlibet.
    + intro h.
      let proof t := modus aequans &r, &h.
      ex &t quodlibet.
Qed.

End discernment. (* discernment *)

End Discernible. (* Discernible *)

Abbreviation Discernible := Discernible.T.

(* [Bool] is the type a test answers in, so its file stands below this one
 * and its instance is declared here.
 *)
#[export] Instance Bool_discernible
  : Discernible Bool.test :=
  {| Discernible.reflection := Bool.test.reflection |}.
