(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

From JW Require Import Algebra.AbelianGroup.
From JW Require Import Algebra.Commutative.
From JW Require Import Algebra.Group.
From JW Require Import Algebra.Monoid.
From JW Require Import Algebra.Ring.
From JW Require Import Algebra.Semigroup.
From JW Require Import Core.All.

Module Bool. (* Bool *)

(* [true] first: [if] takes the first constructor as its [then] branch. *)
Inductive T : Type :=
  | true  : T
  | false : T.

Abbreviation Bool := T.

(* [Bool -> Bool] *)
Definition negate := fun (b : Bool) .
  match b with
  | true  => false
  | false => true
  end.

Notation "! b" := (negate b) (only parsing)
  : jw_bool_scope.

(* [Bool -> Bool -> Bool] *)
Definition and := fun (b1 : Bool) (b2 : Bool) .
  match b1 with
  | true  => b2
  | false => false
  end.

Notation "b1 && b2" := (and b1 b2) (only parsing)
  : jw_bool_scope.

(* [Bool -> Bool -> Bool] *)
Definition or := fun (b1 : Bool) (b2 : Bool) .
  match b1 with
  | true  => true
  | false => b2
  end.

Notation "b1 || b2" := (or b1 b2) (only parsing)
  : jw_bool_scope.

(* [Bool -> Bool -> Bool] *)
Definition xor := fun (b1 : Bool) (b2 : Bool) .
  match b1 with
  | true  => negate b2
  | false => b2
  end.

Notation "b1 ^^ b2" := (xor b1 b2) (only parsing)
  : jw_bool_scope.

Local Open Scope jw_bool_scope.

Module distinctness. (* distinctness *)

(* distinctness.forward *)
Theorem forward : ~ (true = false).
Proof.
  simpl (~ _) in |- *.
  intro e.
  ex e quodlibet.
Qed.

(* distinctness.backward *)
Theorem backward : ~ (false = true).
Proof.
  simpl (~ _) in |- *.
  intro e.
  ex e quodlibet.
Qed.

End distinctness. (* distinctness *)

(* distinctness *)
Theorem distinctness : ~ (true = false) /\ ~ (false = true).
Proof.
  divide et impera.
  - ipso distinctness.forward.
  - ipso distinctness.backward.
Qed.

Module negation. (* negation *)

(* negation.involution *)
Theorem involution : forall (b : Bool) . ! ! b = b.
Proof.
  intros b.
  match b with | | end; simpl in |- *; quod idem est.
Qed.

Module de_morgan. (* negation.de_morgan *)

(* An equation both ways, where [Negation.de_morgan.conjunction] holds one way
 * only: a [Bool] is already decided.
 *)
(* negation.de_morgan.conjunction *)
Theorem conjunction
  : forall (b1 : Bool) (b2 : Bool) . ! (b1 && b2) = ! b1 || ! b2.
Proof.
  intros b1 b2.
  match b1 with | | end; match b2 with | | end; simpl in |- *; quod idem est.
Qed.

(* negation.de_morgan.disjunction *)
Theorem disjunction
  : forall (b1 : Bool) (b2 : Bool) . ! (b1 || b2) = ! b1 && ! b2.
Proof.
  intros b1 b2.
  match b1 with | | end; match b2 with | | end; simpl in |- *; quod idem est.
Qed.

End de_morgan. (* negation.de_morgan *)

End negation. (* negation *)

Module conjunction. (* conjunction *)

(* conjunction.associativity *)
Theorem associativity
  : forall (b1 : Bool) (b2 : Bool) (b3 : Bool) .
      (b1 && b2) && b3 = b1 && (b2 && b3).
Proof.
  intros b1 b2 b3.
  match b1 with | | end; match b2 with | | end; match b3 with | | end; simpl in |- *; quod idem est.
Qed.

(* conjunction.commutativity *)
Theorem commutativity
  : forall (b1 : Bool) (b2 : Bool) . b1 && b2 = b2 && b1.
Proof.
  intros b1 b2.
  match b1 with | | end; match b2 with | | end; simpl in |- *; quod idem est.
Qed.

(* conjunction.identity *)
Theorem identity
  : forall (b : Bool) . (true && b = b) /\ (b && true = b).
Proof.
  intros b.
  divide et impera.
  - simpl in |- *.
    quod idem est.
  - leibniz (conjunction.commutativity b true) in |- *.
    simpl in |- *.
    quod idem est.
Qed.

Module left. (* conjunction.left *)

Module distributivity. (* conjunction.left.distributivity *)

Module over. (* conjunction.left.distributivity.over *)

(* conjunction.left.distributivity.over.sejunction *)
Theorem sejunction
  : forall (b1 : Bool) (b2 : Bool) (b3 : Bool) .
      b1 && (b2 ^^ b3) = (b1 && b2) ^^ (b1 && b3).
Proof.
  intros b1 b2 b3.
  match b1 with | | end; match b2 with | | end; match b3 with | | end; simpl in |- *; quod idem est.
Qed.

End over. (* conjunction.left.distributivity.over *)

End distributivity. (* conjunction.left.distributivity *)

End left. (* conjunction.left *)

Module right. (* conjunction.right *)

Module distributivity. (* conjunction.right.distributivity *)

Module over. (* conjunction.right.distributivity.over *)

(* conjunction.right.distributivity.over.sejunction *)
Theorem sejunction
  : forall (b1 : Bool) (b2 : Bool) (b3 : Bool) .
      (b2 ^^ b3) && b1 = (b2 && b1) ^^ (b3 && b1).
Proof.
  intros b1 b2 b3.
  match b1 with | | end; match b2 with | | end; match b3 with | | end; simpl in |- *; quod idem est.
Qed.

End over. (* conjunction.right.distributivity.over *)

End distributivity. (* conjunction.right.distributivity *)

End right. (* conjunction.right *)

Module distributivity. (* conjunction.distributivity *)

Module over. (* conjunction.distributivity.over *)

(* conjunction.distributivity.over.sejunction *)
Theorem sejunction
  : forall (b1 : Bool) (b2 : Bool) (b3 : Bool) .
      (b1 && (b2 ^^ b3) = (b1 && b2) ^^ (b1 && b3))
    /\ ((b2 ^^ b3) && b1 = (b2 && b1) ^^ (b3 && b1)).
Proof.
  intros b1 b2 b3.
  divide et impera.
  - ipso (conjunction.left.distributivity.over.sejunction  b1 b2 b3).
  - ipso (conjunction.right.distributivity.over.sejunction b1 b2 b3).
Qed.

End over. (* conjunction.distributivity.over *)

End distributivity. (* conjunction.distributivity *)

End conjunction. (* conjunction *)

Module disjunction. (* disjunction *)

(* disjunction.associativity *)
Theorem associativity
  : forall (b1 : Bool) (b2 : Bool) (b3 : Bool) .
      (b1 || b2) || b3 = b1 || (b2 || b3).
Proof.
  intros b1 b2 b3.
  match b1 with | | end; match b2 with | | end; match b3 with | | end; simpl in |- *; quod idem est.
Qed.

(* disjunction.commutativity *)
Theorem commutativity : forall (b1 : Bool) (b2 : Bool) . b1 || b2 = b2 || b1.
Proof.
  intros b1 b2.
  match b1 with | | end; match b2 with | | end; simpl in |- *; quod idem est.
Qed.

(* disjunction.identity *)
Theorem identity
  : forall (b : Bool) . (false || b = b) /\ (b || false = b).
Proof.
  intros b.
  divide et impera.
  - simpl in |- *.
    quod idem est.
  - leibniz (disjunction.commutativity b false) in |- *.
    simpl in |- *.
    quod idem est.
Qed.

End disjunction. (* disjunction *)

Module sejunction. (* sejunction *)

(* sejunction.associativity *)
Theorem associativity
  : forall (b1 : Bool) (b2 : Bool) (b3 : Bool) .
      (b1 ^^ b2) ^^ b3 = b1 ^^ (b2 ^^ b3).
Proof.
  intros b1 b2 b3.
  match b1 with | | end; match b2 with | | end; match b3 with | | end; simpl in |- *; quod idem est.
Qed.

(* sejunction.commutativity *)
Theorem commutativity
  : forall (b1 : Bool) (b2 : Bool) . b1 ^^ b2 = b2 ^^ b1.
Proof.
  intros b1 b2.
  match b1 with | | end; match b2 with | | end; simpl in |- *; quod idem est.
Qed.

(* sejunction.identity *)
Theorem identity
  : forall (b : Bool) . (false ^^ b = b) /\ (b ^^ false = b).
Proof.
  intros b.
  divide et impera.
  - simpl in |- *.
    quod idem est.
  - leibniz (sejunction.commutativity b false) in |- *.
    simpl in |- *.
    quod idem est.
Qed.

(* sejunction.irreflexivity *)
Theorem irreflexivity : forall (b : Bool) . b ^^ b = false.
Proof.
  intros b.
  match b with | | end; simpl in |- *; quod idem est.
Qed.

(* sejunction.inverse *)
Theorem inverse
  : forall (b : Bool) . (b ^^ b = false) /\ (b ^^ b = false).
Proof.
  intros b.
  divide et impera; ipso (sejunction.irreflexivity b).
Qed.

End sejunction. (* sejunction *)

End Bool. (* Bool *)

Abbreviation Bool  := Bool.T.
Abbreviation true  := Bool.true.
Abbreviation false := Bool.false.

Export (notations) Bool.

Instance Bool_and_monoid
  : Monoid Bool.and true :=
  {| Monoid.semigroup      :=
       {| Semigroup.associativity := Bool.conjunction.associativity |}
   ; Monoid.identity       := Bool.conjunction.identity |}.

Instance Bool_or_monoid
  : Monoid Bool.or false :=
  {| Monoid.semigroup      :=
       {| Semigroup.associativity := Bool.disjunction.associativity |}
   ; Monoid.identity       := Bool.disjunction.identity |}.

Instance Bool_xor_monoid
  : Monoid Bool.xor false :=
  {| Monoid.semigroup      :=
       {| Semigroup.associativity := Bool.sejunction.associativity |}
   ; Monoid.identity       := Bool.sejunction.identity |}.

Instance Bool_and_commutative
  : Commutative Bool.and :=
  {| Commutative.commutativity := Bool.conjunction.commutativity |}.

Instance Bool_or_commutative
  : Commutative Bool.or :=
  {| Commutative.commutativity := Bool.disjunction.commutativity |}.

Instance Bool_xor_commutative
  : Commutative Bool.xor :=
  {| Commutative.commutativity := Bool.sejunction.commutativity |}.

Instance Bool_xor_group
  : Group Bool.xor false (fun (b : Bool) . b) :=
  {| Group.monoid  := Bool_xor_monoid
   ; Group.inverse := Bool.sejunction.inverse |}.

Instance Bool_xor_abelian_group
  : AbelianGroup Bool.xor false (fun (b : Bool) . b) :=
  {| AbelianGroup.group       := Bool_xor_group
   ; AbelianGroup.commutative := Bool_xor_commutative |}.

Instance Bool_ring
  : Ring Bool.xor false (fun (b : Bool) . b) Bool.and true :=
  {| Ring.abelian_group  := Bool_xor_abelian_group
   ; Ring.monoid         := Bool_and_monoid
   ; Ring.distributivity := Bool.conjunction.distributivity.over.sejunction |}.
