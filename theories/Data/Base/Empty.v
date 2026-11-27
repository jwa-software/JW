(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

From JW Require Import Core.All.
From JW Require Import Data.Base.Bool.
From JW Require Import Data.Discernible.

Local Unset Elimination Schemes.

Module Empty.

(* The type with no element, the unit of [Coproduct]. No ctor, so the
 * definition ends at the [:=]; [Empty] is to types what [Falsum] is to
 * propositions.
 *)
Inductive T : Type := .

Abbreviation Empty := T.

(* The eliminator that [match ... per] takes, written out. With no ctor the [match]
 * has no branch, and that is the whole proof: there is no [e] to prove
 * anything about.
 *)
(* [forall (P : Empty -> Prop) (e : Empty) . P e] *)
Definition induction
  : forall (P : Empty -> Prop) (e : Empty) . P e
  := fun (P : Empty -> Prop) (e : Empty) .
       match e with | end.

(* From nothing, anything: the [Type]-level counterpart of [Falsum.elimination]. *)
(* [forall (A : Type) . Empty -> A] *)
Definition elimination := fun (A : Type) (e : Empty) .
  match e return A with | end.

(* There is no element to compare, so no answer is ever given. *)
(* [Empty -> Empty -> Bool] *)
Definition test := fun (e1 : Empty) (e2 : Empty) . elimination Bool e1.

(* [Empty -> Empty -> Bool] *)
Abbreviation equivalent := Discernible.equivalent.

(* [Empty -> Empty -> Bool] *)
Abbreviation discern := Discernible.discern.

Module test. (* test *)

(* test.reflection *)
Theorem reflection
  : forall (e1 : Empty) (e2 : Empty) . test e1 e2 = true <-> e1 = e2.
Proof.
  intros e1 e2.
  ex &e1 quodlibet.
Qed.

End test. (* test *)

Instance discernible
  : Discernible test :=
  {| Discernible.reflection := test.reflection |}.

End Empty.

Abbreviation Empty := Empty.T.

Existing Instance Empty.discernible.
