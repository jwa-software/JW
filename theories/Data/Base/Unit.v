(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

From jwa Require Import Core.All.

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

(* [Unit.introduction] is surjective: every element is the one ctor. This is
 * the eta rule for [Unit], which an [Inductive] does not compute, so it is
 * proved.
 *)
Theorem surjectivity : forall (u : Unit) . u = Unit.introduction.
Proof.
  intros u. match u with end. quod idem est.
Qed.

End Unit.

Abbreviation Unit := Unit.T.
