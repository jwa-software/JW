(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

From JW Require Import Core.All.
From JW Require Import Data.Base.Bool.
From JW Require Import Data.Discernible.

Local Unset Elimination Schemes.

Module Comparison. (* Comparison *)

(* The answer of a three-way comparison,
 * read as "the first argument is ... the second".
 *)
Inductive T : Type :=
  | Lt : T
  | Eq : T
  | Gt : T.

Abbreviation Comparison := T.

(* [forall (P : Comparison -> Prop) . P Lt -> P Eq -> P Gt -> forall (c : Comparison) . P c] *)
Definition induction
  : forall (P : Comparison -> Prop) .
      P Lt ->
      P Eq ->
      P Gt ->
      forall (c : Comparison) . P c
  := fun (P : Comparison -> Prop)
         (lt : P Lt)
         (eq : P Eq)
         (gt : P Gt)
         (c : Comparison) .
       match c with
       | Lt => lt
       | Eq => eq
       | Gt => gt
       end.

(* [Comparison -> Comparison] *)
Definition transpose := fun (c : Comparison) .
  match c with
  | Lt => Gt
  | Eq => Eq
  | Gt => Lt
  end.

(* [Comparison -> Comparison -> Bool] *)
Definition test := fun (c1 : Comparison) (c2 : Comparison) .
  match c1, c2 with
  | Lt, Lt => true
  | Eq, Eq => true
  | Gt, Gt => true
  | _,  _  => false
  end.

(* [Comparison -> Comparison -> Bool] *)
Abbreviation equivalent := Discernible.equivalent.

(* [Comparison -> Comparison -> Bool] *)
Abbreviation discern := Discernible.discern.

Module transposition. (* transposition *)

(* transposition.involution *)
Theorem involution
  : forall (c : Comparison) . transpose (transpose c) = c.
Proof.
  intros c.
  match c with | | | end; simpl in |- *; quod idem est.
Qed.

End transposition. (* transposition *)

Module test. (* test *)

(* test.reflection *)
Theorem reflection
  : forall (c1 : Comparison) (c2 : Comparison) . test c1 c2 = true <-> c1 = c2.
Proof.
  intros c1 c2.
  match &c1 with | | | end; match &c2 with | | | end; simpl in |- *.
  - divide et impera; intro e; quod idem est.
  - divide et impera; intro e; ex &e quodlibet.
  - divide et impera; intro e; ex &e quodlibet.
  - divide et impera; intro e; ex &e quodlibet.
  - divide et impera; intro e; quod idem est.
  - divide et impera; intro e; ex &e quodlibet.
  - divide et impera; intro e; ex &e quodlibet.
  - divide et impera; intro e; ex &e quodlibet.
  - divide et impera; intro e; quod idem est.
Qed.

End test. (* test *)

Instance discernible
  : Discernible test :=
  {| Discernible.reflection := test.reflection |}.

End Comparison. (* Comparison *)

Abbreviation Comparison := Comparison.T.

Existing Instance Comparison.discernible.
