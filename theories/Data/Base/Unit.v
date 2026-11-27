(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

From JW Require Import Core.All.
From JW Require Import Data.Base.Bool.
From JW Require Import Data.Discernible.

Local Unset Elimination Schemes.

Module Unit.

(* The type with exactly one element, the unit of [Product]: [Unit] is to
 * types what [Verum] is to propositions.
 *)
Inductive T : Type :=
  | introduction : T.

Abbreviation Unit := T.

(* [forall (P : Unit -> Prop) . P Unit.introduction -> forall (u : Unit) . P u] *)
Definition induction
  : forall (P : Unit -> Prop) . P Unit.introduction -> forall (u : Unit) . P u
  := fun (P : Unit -> Prop) (base : P Unit.introduction) (u : Unit) .
       match u with
       | Unit.introduction => base
       end.

(* The one element is equal to itself, so the answer is always [true]. *)
(* [Unit -> Unit -> Bool] *)
Definition test := fun (u1 : Unit) (u2 : Unit) . true.

(* [Unit -> Unit -> Bool] *)
Abbreviation equivalent := Discernible.equivalent.

(* [Unit -> Unit -> Bool] *)
Abbreviation discern := Discernible.discern.

(* [Unit.introduction] is surjective: every element is the one ctor. This is
 * the eta rule for [Unit], which an [Inductive] does not compute, so it is
 * proved.
 *)
Theorem surjectivity : forall (u : Unit) . u = Unit.introduction.
Proof.
  intros u. match u with end. quod idem est.
Qed.

Module test. (* test *)

(* test.reflection *)
Theorem reflection
  : forall (u1 : Unit) (u2 : Unit) . test u1 u2 = true <-> u1 = u2.
Proof.
  intros u1 u2.
  match &u1 with | end; match &u2 with | end; simpl test in |- *.
  divide et impera; intro e; quod idem est.
Qed.

End test. (* test *)

Instance discernible
  : Discernible test :=
  {| Discernible.reflection := test.reflection |}.

End Unit.

Abbreviation Unit := Unit.T.

Existing Instance Unit.discernible.
