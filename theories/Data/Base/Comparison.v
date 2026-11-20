(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

From JW Require Import Core.All.

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

Module transposition. (* transposition *)

(* transposition.involution *)
Theorem involution
  : forall (c : Comparison) . transpose (transpose c) = c.
Proof.
  intros c.
  match c with | | | end; simpl in |- *; quod idem est.
Qed.

End transposition. (* transposition *)

End Comparison. (* Comparison *)

Abbreviation Comparison := Comparison.T.
