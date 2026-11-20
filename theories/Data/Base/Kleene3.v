(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

From jwa Require Import Core.All.

(* Kleene's strong three-valued logic: [unknown] is a truth value not yet
 * known, and a connective gives a known result whenever its known arguments
 * already decide it.
 *)
Module Kleene3. (* Kleene3 *)

(* The ctors in the truth order, from the greatest to the least: [and] takes
 * the lesser of its arguments and [or] the greater.
 *)
Inductive T : Type :=
  | true    : T
  | unknown : T
  | false   : T.

(* The carrier is named [T] so that the type itself reads [Kleene3] on both
 * sides of the module: here through this abbreviation, outside through the
 * one that follows [End Kleene3].
 *)
Abbreviation Kleene3 := T.

(* [Kleene3 -> Kleene3] *)
Definition negate := fun (v : Kleene3) .
  match v with
  | true    => false
  | unknown => unknown
  | false   => true
  end.

(* The scope is declared in [Core.Notations] and opened only inside this
 * module; after [End Kleene3] a client writes [(v1 && v2)%k3] or opens the
 * scope. The levels are the ones reserved there for the [Bool] spellings.
 * [only parsing] keeps goals printing the operations by name.
 *)
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

End disjunction. (* disjunction *)

End Kleene3. (* Kleene3 *)

(* The counterpart of the abbreviation inside the module: a client writes
 * [Kleene3], not [Kleene3.T].
 *)
Abbreviation Kleene3 := Kleene3.T.

(* Makes the notations declared in [Module Kleene3] usable in every file that
 * imports this one, as [(v1 && v2)%k3] or under an opened
 * [jwa_kleene3_scope]. Only the notations are exported: the ctors, [and] and
 * the laws still need the [Kleene3.] prefix.
 *)
Export (notations) Kleene3.
