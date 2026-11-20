(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

From jwa Require Import Algebra.Commutative.
From jwa Require Import Algebra.Monoid.
From jwa Require Import Algebra.Semigroup.
From jwa Require Import Core.All.
From jwa Require Import Data.Base.Bool.
From jwa Require Import Data.Base.Comparison.
From jwa Require Import Data.Comparable.

(* Kleene's strong three-valued logic. *)
Module Kleene3. (* Kleene3 *)

(* The ctors in the truth order, from the greatest to the least: [and] takes
 * the lesser of its arguments and [or] the greater.
 *)
Inductive T : Type :=
  | true    : T
  | unknown : T
  | false   : T.

Abbreviation Kleene3 := T.

(* [Kleene3 -> Kleene3] *)
Definition negate := fun (v : Kleene3) .
  match v with
  | true    => false
  | unknown => unknown
  | false   => true
  end.

Notation "! v" := (negate v) (only parsing)
  : jwa_kleene3_scope.

(* [Kleene3 -> Kleene3 -> Kleene3] *)
Definition and := fun (v1 : Kleene3) (v2 : Kleene3) .
  match v1 with
  | true    => v2
  | unknown =>
      match v2 with
      | true    => unknown
      | unknown => unknown
      | false   => false
      end
  | false   => false
  end.

Notation "v1 && v2" := (and v1 v2) (only parsing)
  : jwa_kleene3_scope.

(* [Kleene3 -> Kleene3 -> Kleene3] *)
Definition or := fun (v1 : Kleene3) (v2 : Kleene3) .
  match v1 with
  | true    => true
  | unknown =>
      match v2 with
      | true    => true
      | unknown => unknown
      | false   => unknown
      end
  | false   => v2
  end.

Notation "v1 || v2" := (or v1 v2) (only parsing)
  : jwa_kleene3_scope.

Local Open Scope jwa_kleene3_scope.

(* Kleene's implication, [! v1 || v2]: [implies unknown unknown] is
 * [unknown], not [true], since neither side is known.
 *)
(* [Kleene3 -> Kleene3 -> Kleene3] *)
Definition implies := fun (v1 : Kleene3) (v2 : Kleene3) . ! v1 || v2.

(* The known values, [Bool.true] to [true] and [Bool.false] to [false]. *)
(* [Bool -> Kleene3] *)
Definition from_bool := fun (b : Bool) .
  match b with
  | Bool.true  => true
  | Bool.false => false
  end.

(* The truth order, [false] below [unknown] below [true], read as the answer
 * of a three-way comparison.
 *)
(* [Kleene3 -> Kleene3 -> Comparison] *)
Definition compare := fun (v1 : Kleene3) (v2 : Kleene3) .
  match v1 with
  | true    =>
      match v2 with
      | true    => Comparison.Eq
      | unknown => Comparison.Gt
      | false   => Comparison.Gt
      end
  | unknown =>
      match v2 with
      | true    => Comparison.Lt
      | unknown => Comparison.Eq
      | false   => Comparison.Gt
      end
  | false   =>
      match v2 with
      | true    => Comparison.Lt
      | unknown => Comparison.Lt
      | false   => Comparison.Eq
      end
  end.

(* The strict truth order, [false < unknown < true]. [<t] in the bilattice literature. *)
(* [Kleene3 -> Kleene3 -> Prop] *)
Definition TruthLessThan := fun (v1 : Kleene3) (v2 : Kleene3) .
  match v1 with
  | true    => Falsum
  | unknown =>
      match v2 with
      | true    => Verum
      | unknown => Falsum
      | false   => Falsum
      end
  | false   =>
      match v2 with
      | true    => Verum
      | unknown => Verum
      | false   => Falsum
      end
  end.

Notation "v1 < v2" := (TruthLessThan v1 v2) (only parsing)
  : jwa_kleene3_scope.

(* The truth order, [<=t] in the bilattice literature. *)
(* [Kleene3 -> Kleene3 -> Prop] *)
Definition TruthLessOrEqual := fun (v1 : Kleene3) (v2 : Kleene3) .
  v1 = v2 \/ TruthLessThan v1 v2.

Notation "v1 <= v2" := (TruthLessOrEqual v1 v2) (only parsing)
  : jwa_kleene3_scope.

Notation "v1 > v2" := (TruthLessThan v2 v1) (only parsing)
  : jwa_kleene3_scope.
Notation "v1 >= v2" := (TruthLessOrEqual v2 v1) (only parsing)
  : jwa_kleene3_scope.

Notation "'(<)'" := TruthLessThan (only parsing)
  : jwa_kleene3_scope.
Notation "'(<=)'" := TruthLessOrEqual (only parsing)
  : jwa_kleene3_scope.

Module negation. (* negation *)

(* negation.involution *)
Theorem involution : forall (v : Kleene3) . ! ! v = v.
Proof.
  intros v.
  match v with | | | end; simpl in |- *; quod idem est.
Qed.

Module de_morgan. (* negation.de_morgan *)

(* negation.de_morgan.conjunction *)
Theorem conjunction
  : forall (v1 : Kleene3) (v2 : Kleene3) . ! (v1 && v2) = ! v1 || ! v2.
Proof.
  intros v1 v2.
  match v1 with | | | end; match v2 with | | | end; simpl in |- *; quod idem est.
Qed.

(* negation.de_morgan.disjunction *)
Theorem disjunction
  : forall (v1 : Kleene3) (v2 : Kleene3) . ! (v1 || v2) = ! v1 && ! v2.
Proof.
  intros v1 v2.
  match v1 with | | | end; match v2 with | | | end; simpl in |- *; quod idem est.
Qed.

End de_morgan. (* negation.de_morgan *)

(* [v1 && ! v1] can only be either [false] or [unknown], and [v2 || ! v2]
 * can only be either [true] or [unknown]; therefore the first is never
 * above the second in the truth order.
 *)
(* negation.kleene *)
Theorem kleene : forall (v1 : Kleene3) (v2 : Kleene3) . v1 && ! v1 <= v2 || ! v2.
Proof.
  intros v1 v2.
  match &v1 with | | | end; match &v2 with | | | end; simpl TruthLessOrEqual in |- *;
    simpl in |- *.
  - ipso (disjoin _, I).
  - ipso (disjoin _, I).
  - ipso (disjoin _, I).
  - ipso (disjoin _, I).
  - ipso (disjoin (Identity.reflexivity unknown), _).
  - ipso (disjoin _, I).
  - ipso (disjoin _, I).
  - ipso (disjoin _, I).
  - ipso (disjoin _, I).
Qed.

End negation. (* negation *)

Module conjunction. (* conjunction *)

(* conjunction.associativity *)
Theorem associativity
  : forall (v1 : Kleene3) (v2 : Kleene3) (v3 : Kleene3) .
      (v1 && v2) && v3 = v1 && (v2 && v3).
Proof.
  intros v1 v2 v3.
  match v1 with | | | end;
    match v2 with | | | end;
    match v3 with | | | end;
    simpl in |- *;
    quod idem est.
Qed.

(* conjunction.commutativity *)
Theorem commutativity
  : forall (v1 : Kleene3) (v2 : Kleene3) . v1 && v2 = v2 && v1.
Proof.
  intros v1 v2.
  match v1 with | | | end; match v2 with | | | end; simpl in |- *; quod idem est.
Qed.

(* conjunction.identity *)
Theorem identity
  : forall (v : Kleene3) . (true && v = v) /\ (v && true = v).
Proof.
  intros v.
  divide et impera.
  - simpl in |- *.
    quod idem est.
  - leibniz (conjunction.commutativity v true) in |- *.
    simpl in |- *.
    quod idem est.
Qed.

(* conjunction.idempotence *)
Theorem idempotence : forall (v : Kleene3) . v && v = v.
Proof.
  intros v.
  match v with | | | end; simpl in |- *; quod idem est.
Qed.

(* conjunction.absorption *)
Theorem absorption
  : forall (v1 : Kleene3) (v2 : Kleene3) . v1 && (v1 || v2) = v1.
Proof.
  intros v1 v2.
  match v1 with | | | end; match v2 with | | | end; simpl in |- *; quod idem est.
Qed.

Module left. (* conjunction.left *)

Module distributivity. (* conjunction.left.distributivity *)

Module over. (* conjunction.left.distributivity.over *)

(* conjunction.left.distributivity.over.disjunction *)
Theorem disjunction
  : forall (v1 : Kleene3) (v2 : Kleene3) (v3 : Kleene3) .
      v1 && (v2 || v3) = (v1 && v2) || (v1 && v3).
Proof.
  intros v1 v2 v3.
  match v1 with | | | end;
    match v2 with | | | end;
    match v3 with | | | end;
    simpl in |- *;
    quod idem est.
Qed.

End over. (* conjunction.left.distributivity.over *)

End distributivity. (* conjunction.left.distributivity *)

End left. (* conjunction.left *)

Module right. (* conjunction.right *)

Module distributivity. (* conjunction.right.distributivity *)

Module over. (* conjunction.right.distributivity.over *)

(* conjunction.right.distributivity.over.disjunction *)
Theorem disjunction
  : forall (v1 : Kleene3) (v2 : Kleene3) (v3 : Kleene3) .
      (v2 || v3) && v1 = (v2 && v1) || (v3 && v1).
Proof.
  intros v1 v2 v3.
  match v1 with | | | end;
    match v2 with | | | end;
    match v3 with | | | end;
    simpl in |- *;
    quod idem est.
Qed.

End over. (* conjunction.right.distributivity.over *)

End distributivity. (* conjunction.right.distributivity *)

End right. (* conjunction.right *)

Module distributivity. (* conjunction.distributivity *)

Module over. (* conjunction.distributivity.over *)

(* conjunction.distributivity.over.disjunction *)
Theorem disjunction
  : forall (v1 : Kleene3) (v2 : Kleene3) (v3 : Kleene3) .
      (v1 && (v2 || v3) = (v1 && v2) || (v1 && v3))
    /\ ((v2 || v3) && v1 = (v2 && v1) || (v3 && v1)).
Proof.
  intros v1 v2 v3.
  divide et impera.
  - ipso (conjunction.left.distributivity.over.disjunction  v1 v2 v3).
  - ipso (conjunction.right.distributivity.over.disjunction v1 v2 v3).
Qed.

End over. (* conjunction.distributivity.over *)

End distributivity. (* conjunction.distributivity *)

(* conjunction.minimum *)
Theorem minimum
  : forall (v1 : Kleene3) (v2 : Kleene3) . v1 && v2 = Comparable.min compare v1 v2.
Proof.
  intros v1 v2.
  simpl Comparable.min in |- *.
  match &v1 with | | | end; match &v2 with | | | end; simpl in |- *; quod idem est.
Qed.

End conjunction. (* conjunction *)

Module disjunction. (* disjunction *)

(* disjunction.associativity *)
Theorem associativity
  : forall (v1 : Kleene3) (v2 : Kleene3) (v3 : Kleene3) .
      (v1 || v2) || v3 = v1 || (v2 || v3).
Proof.
  intros v1 v2 v3.
  match v1 with | | | end;
    match v2 with | | | end;
    match v3 with | | | end;
    simpl in |- *;
    quod idem est.
Qed.

(* disjunction.commutativity *)
Theorem commutativity
  : forall (v1 : Kleene3) (v2 : Kleene3) . v1 || v2 = v2 || v1.
Proof.
  intros v1 v2.
  match v1 with | | | end; match v2 with | | | end; simpl in |- *; quod idem est.
Qed.

(* disjunction.identity *)
Theorem identity
  : forall (v : Kleene3) . (false || v = v) /\ (v || false = v).
Proof.
  intros v.
  divide et impera.
  - simpl in |- *.
    quod idem est.
  - leibniz (disjunction.commutativity v false) in |- *.
    simpl in |- *.
    quod idem est.
Qed.

(* disjunction.idempotence *)
Theorem idempotence : forall (v : Kleene3) . v || v = v.
Proof.
  intros v.
  match v with | | | end; simpl in |- *; quod idem est.
Qed.

(* disjunction.absorption *)
Theorem absorption
  : forall (v1 : Kleene3) (v2 : Kleene3) . v1 || (v1 && v2) = v1.
Proof.
  intros v1 v2.
  match v1 with | | | end; match v2 with | | | end; simpl in |- *; quod idem est.
Qed.

Module left. (* disjunction.left *)

Module distributivity. (* disjunction.left.distributivity *)

Module over. (* disjunction.left.distributivity.over *)

(* disjunction.left.distributivity.over.conjunction *)
Theorem conjunction
  : forall (v1 : Kleene3) (v2 : Kleene3) (v3 : Kleene3) .
      v1 || (v2 && v3) = (v1 || v2) && (v1 || v3).
Proof.
  intros v1 v2 v3.
  match v1 with | | | end;
    match v2 with | | | end;
    match v3 with | | | end;
    simpl in |- *;
    quod idem est.
Qed.

End over. (* disjunction.left.distributivity.over *)

End distributivity. (* disjunction.left.distributivity *)

End left. (* disjunction.left *)

Module right. (* disjunction.right *)

Module distributivity. (* disjunction.right.distributivity *)

Module over. (* disjunction.right.distributivity.over *)

(* disjunction.right.distributivity.over.conjunction *)
Theorem conjunction
  : forall (v1 : Kleene3) (v2 : Kleene3) (v3 : Kleene3) .
      (v2 && v3) || v1 = (v2 || v1) && (v3 || v1).
Proof.
  intros v1 v2 v3.
  match v1 with | | | end;
    match v2 with | | | end;
    match v3 with | | | end;
    simpl in |- *;
    quod idem est.
Qed.

End over. (* disjunction.right.distributivity.over *)

End distributivity. (* disjunction.right.distributivity *)

End right. (* disjunction.right *)

Module distributivity. (* disjunction.distributivity *)

Module over. (* disjunction.distributivity.over *)

(* disjunction.distributivity.over.conjunction *)
Theorem conjunction
  : forall (v1 : Kleene3) (v2 : Kleene3) (v3 : Kleene3) .
      (v1 || (v2 && v3) = (v1 || v2) && (v1 || v3))
    /\ ((v2 && v3) || v1 = (v2 || v1) && (v3 || v1)).
Proof.
  intros v1 v2 v3.
  divide et impera.
  - ipso (disjunction.left.distributivity.over.conjunction  v1 v2 v3).
  - ipso (disjunction.right.distributivity.over.conjunction v1 v2 v3).
Qed.

End over. (* disjunction.distributivity.over *)

End distributivity. (* disjunction.distributivity *)

(* disjunction.maximum *)
Theorem maximum
  : forall (v1 : Kleene3) (v2 : Kleene3) . v1 || v2 = Comparable.max compare v1 v2.
Proof.
  intros v1 v2.
  simpl Comparable.max in |- *.
  match &v1 with | | | end; match &v2 with | | | end; simpl in |- *; quod idem est.
Qed.

End disjunction. (* disjunction *)

Module implication. (* implication *)

(* implication.contraposition *)
Theorem contraposition
  : forall (v1 : Kleene3) (v2 : Kleene3) . implies v1 v2 = implies (! v2) (! v1).
Proof.
  intros v1 v2.
  simpl implies in |- *.
  match v1 with | | | end; match v2 with | | | end; simpl in |- *; quod idem est.
Qed.

End implication. (* implication *)

Module conversion. (* conversion *)

(* conversion.injectivity *)
Theorem injectivity : forall {b1 : Bool} {b2 : Bool} . from_bool b1 = from_bool b2 -> b1 = b2.
Proof.
  intros b1 b2 e.
  match b1 with | | end; match b2 with | | end.
  - quod idem est.
  - simpl in &e.
    ex &e quodlibet.
  - simpl in &e.
    ex &e quodlibet.
  - quod idem est.
Qed.

(* conversion.exclusion *)
Theorem exclusion : forall (b : Bool) . ~ (from_bool b = unknown).
Proof.
  intros b.
  simpl (~ _) in |- *.
  intro e.
  match b with | | end; simpl in &e; ex &e quodlibet.
Qed.

(* conversion.negation *)
Theorem negation : forall (b : Bool) . from_bool (Bool.negate b) = ! from_bool b.
Proof.
  intros b.
  match b with | | end; simpl in |- *; quod idem est.
Qed.

(* conversion.conjunction *)
Theorem conjunction
  : forall (b1 : Bool) (b2 : Bool) .
      from_bool (Bool.and b1 b2) = from_bool b1 && from_bool b2.
Proof.
  intros b1 b2.
  match b1 with | | end; match b2 with | | end; simpl in |- *; quod idem est.
Qed.

(* conversion.disjunction *)
Theorem disjunction
  : forall (b1 : Bool) (b2 : Bool) .
      from_bool (Bool.or b1 b2) = from_bool b1 || from_bool b2.
Proof.
  intros b1 b2.
  match b1 with | | end; match b2 with | | end; simpl in |- *; quod idem est.
Qed.

(* conversion.implication *)
Theorem implication
  : forall (b1 : Bool) (b2 : Bool) .
      from_bool (Bool.or (Bool.negate b1) b2) = implies (from_bool b1) (from_bool b2).
Proof.
  intros b1 b2.
  simpl implies in |- *.
  match b1 with | | end; match b2 with | | end; simpl in |- *; quod idem est.
Qed.

End conversion. (* conversion *)

Module truth. (* truth *)

Module strict. (* truth.strict *)

(* truth.strict.transitivity *)
Theorem transitivity
  : forall {v1 : Kleene3} {v2 : Kleene3} {v3 : Kleene3} . v1 < v2 -> v2 < v3 -> v1 < v3.
Proof.
  intros v1 v2 v3 h1 h2.
  match &v2 with | | | end.
  - simpl in &h2.
    ex &h2 quodlibet.
  - match &v1 with | | | end.
    + simpl in &h1.
      ex &h1 quodlibet.
    + simpl in &h1.
      ex &h1 quodlibet.
    + match &v3 with | | | end.
      * simpl in |- *.
        ipso I.
      * simpl in &h2.
        ex &h2 quodlibet.
      * simpl in &h2.
        ex &h2 quodlibet.
  - match &v1 with | | | end; simpl in &h1; ex &h1 quodlibet.
Qed.

End strict. (* truth.strict *)

End truth. (* truth *)

Module comparison. (* comparison *)

(* Nine cases in three shapes: [compare] answers [Eq] on the diagonal, [Lt]
 * on the three pairs [TruthLessThan] holds of, and [Gt] on the other three.
 *)
(* comparison.specification *)
Theorem specification
  : forall (v1 : Kleene3) (v2 : Kleene3) .
      (compare v1 v2 = Comparison.Lt <-> v1 < v2) /\ (compare v1 v2 = Comparison.Eq <-> v1 = v2).
Proof.
  intros v1 v2.
  match &v1 with | | | end; match &v2 with | | | end; simpl in |- *;
    divide et impera; divide et impera; intro h.
  (* true, true *)
  - ex &h quodlibet.
  - ex &h quodlibet.
  - quod idem est.
  - quod idem est.
  (* true, unknown *)
  - ex &h quodlibet.
  - ex &h quodlibet.
  - ex &h quodlibet.
  - ex &h quodlibet.
  (* true, false *)
  - ex &h quodlibet.
  - ex &h quodlibet.
  - ex &h quodlibet.
  - ex &h quodlibet.
  (* unknown, true *)
  - ipso I.
  - quod idem est.
  - ex &h quodlibet.
  - ex &h quodlibet.
  (* unknown, unknown *)
  - ex &h quodlibet.
  - ex &h quodlibet.
  - quod idem est.
  - quod idem est.
  (* unknown, false *)
  - ex &h quodlibet.
  - ex &h quodlibet.
  - ex &h quodlibet.
  - ex &h quodlibet.
  (* false, true *)
  - ipso I.
  - quod idem est.
  - ex &h quodlibet.
  - ex &h quodlibet.
  (* false, unknown *)
  - ipso I.
  - quod idem est.
  - ex &h quodlibet.
  - ex &h quodlibet.
  (* false, false *)
  - ex &h quodlibet.
  - ex &h quodlibet.
  - quod idem est.
  - quod idem est.
Qed.

(* comparison.antisymmetry *)
Theorem antisymmetry
  : forall (v1 : Kleene3) (v2 : Kleene3) . compare v1 v2 = Comparison.transpose (compare v2 v1).
Proof.
  intros v1 v2.
  match &v1 with | | | end; match &v2 with | | | end; simpl in |- *; quod idem est.
Qed.

End comparison. (* comparison *)

Instance comparable
  : Comparable compare (<) :=
  {| Comparable.transitivity := @truth.strict.transitivity
  ; Comparable.specification := comparison.specification
  ; Comparable.antisymmetry := comparison.antisymmetry |}.

End Kleene3. (* Kleene3 *)

Abbreviation Kleene3 := Kleene3.T.

Export (notations) Kleene3.

Existing Instance Kleene3.comparable.

Instance Kleene3_and_monoid
  : Monoid Kleene3.and Kleene3.true :=
  {| Monoid.semigroup      :=
       {| Semigroup.associativity := Kleene3.conjunction.associativity |}
   ; Monoid.identity       := Kleene3.conjunction.identity |}.

Instance Kleene3_or_monoid
  : Monoid Kleene3.or Kleene3.false :=
  {| Monoid.semigroup      :=
       {| Semigroup.associativity := Kleene3.disjunction.associativity |}
   ; Monoid.identity       := Kleene3.disjunction.identity |}.

Instance Kleene3_and_commutative
  : Commutative Kleene3.and :=
  {| Commutative.commutativity := Kleene3.conjunction.commutativity |}.

Instance Kleene3_or_commutative
  : Commutative Kleene3.or :=
  {| Commutative.commutativity := Kleene3.disjunction.commutativity |}.
