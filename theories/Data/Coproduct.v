(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

From JW Require Import Core.All.
From JW Require Import Data.Base.Bool.
From JW Require Import Data.Discernible.
From JW Require Import Data.Functor.
From JW Require Import Tactics.Equation.
From JW Require Import Tactics.Modus.

Local Unset Elimination Schemes.

Module Coproduct. (* Coproduct *)

(* A coproduct holds one [A] or one [B], tagged by which. Both are
 * parameters: the type behind each tag is fixed for the whole coproduct.
 *)
Inductive T (A : Type) (B : Type) : Type :=
  | introduction_left  : A -> T A B
  | introduction_right : B -> T A B.

(* One type is inferred from the value, the other from the expected type; a
 * use that has neither needs [@Coproduct.introduction_left A B a].
 *)
Arguments Coproduct.introduction_left  {A} {B} a.
Arguments Coproduct.introduction_right {A} {B} b.

Abbreviation Coproduct := T.

(* The two ctors under the names a use writes: [Coproduct.left a] and
 * [Coproduct.right b]. An abbreviation is the ctor itself, so it also
 * serves as a pattern; inside this module Rocq prints it as [left a].
 *)
Abbreviation left  := Coproduct.introduction_left.
Abbreviation right := Coproduct.introduction_right.
Abbreviation L     := Coproduct.introduction_left  (only parsing).
Abbreviation R     := Coproduct.introduction_right (only parsing).

(* The eliminator that [match ... per] takes, written out. Nothing recurses: a
 * coproduct holds no smaller coproduct, so one [match] is the whole content.
 *)
Definition induction
  : forall (A : Type) (B : Type) (P : Coproduct A B -> Prop) .
      (forall (a : A) . P (Coproduct.introduction_left a)) ->
      (forall (b : B) . P (Coproduct.introduction_right b)) ->
      forall (cp : Coproduct A B) . P cp
  := fun (A : Type) (B : Type) (P : Coproduct A B -> Prop)
       (left  : forall (a : A) . P (Coproduct.introduction_left a))
       (right : forall (b : B) . P (Coproduct.introduction_right b))
       (cp : Coproduct A B) .
       match cp with
       | Coproduct.introduction_left  a => left  a
       | Coproduct.introduction_right b => right b
       end.

(* [forall {A : Type} {B : Type} {C : Type} . (A -> C) -> (B -> C) -> Coproduct A B -> C] *)
Definition copair := fun {A : Type} {B : Type} {C : Type}
                         (f : A -> C) (g : B -> C) (cp : Coproduct A B) .
  match cp return C with
  | Coproduct.left  a => f a
  | Coproduct.right b => g b
  end.

(* [forall {A : Type} {B : Type} . Coproduct A B -> Coproduct B A] *)
Definition swap := fun {A : Type} {B : Type} (cp : Coproduct A B) .
  match cp return Coproduct B A with
  | Coproduct.left  a => Coproduct.right a
  | Coproduct.right b => Coproduct.left  b
  end.

(* [forall {A : Type} {B : Type} {C : Type} . (A -> C) -> Coproduct A B -> Coproduct C B] *)
Definition map_left := fun {A : Type} {B : Type} {C : Type}
                         (f : A -> C) (cp : Coproduct A B) .
  match cp return Coproduct C B with
  | Coproduct.left  a => Coproduct.left  (f a)
  | Coproduct.right b => Coproduct.right b
  end.

(* [forall {A : Type} {B : Type} {C : Type} . (B -> C) -> Coproduct A B -> Coproduct A C] *)
Definition map_right := fun {A : Type} {B : Type} {C : Type}
                          (f : B -> C) (cp : Coproduct A B) .
  match cp return Coproduct A C with
  | Coproduct.left  a => Coproduct.left  a
  | Coproduct.right b => Coproduct.right (f b)
  end.

(* [forall {A : Type} {B : Type} {C : Type} {D : Type} .
 *    (A -> C) -> (B -> D) -> Coproduct A B -> Coproduct C D]
 *)
Definition bimap := fun {A : Type} {B : Type} {C : Type} {D : Type}
                      (f : A -> C) (g : B -> D) (cp : Coproduct A B) .
  match cp return Coproduct C D with
  | Coproduct.left  a => Coproduct.left  (f a)
  | Coproduct.right b => Coproduct.right (g b)
  end.

(* Both are on one side, and the two values pass that side's tester. *)
(* [forall {A : Type} {B : Type} .
 *    (A -> A -> Bool) -> (B -> B -> Bool) -> Coproduct A B -> Coproduct A B -> Bool]
 *)
Definition test := fun {A : Type} {B : Type}
    (left_tester : A -> A -> Bool) (right_tester : B -> B -> Bool)
    (c1 : Coproduct A B) (c2 : Coproduct A B) .
  match c1, c2 with
  | Coproduct.introduction_left a1,  Coproduct.introduction_left a2  => left_tester a1 a2
  | Coproduct.introduction_right b1, Coproduct.introduction_right b2 => right_tester b1 b2
  | _,                               _                               => false
  end.

(* [forall {A : Type} {B : Type} . Coproduct A B -> Coproduct A B -> Bool] *)
Abbreviation equivalent := Discernible.equivalent.

(* [forall {A : Type} {B : Type} . Coproduct A B -> Coproduct A B -> Bool] *)
Abbreviation discern := Discernible.discern.

(* A law of the type itself rather than of any operation, so it belongs to
 * no topic below.
 *)
Theorem distinctness
  : forall {A : Type} {B : Type} (a : A) (b : B) .
      ~ (Coproduct.left a = Coproduct.right b).
Proof.
  intros A B a b.
  simpl (~ _) in |- *.
  intro e.
  ex e quodlibet.
Qed.

Module left. (* left *)

(* left.injectivity *)
Theorem injectivity
  : forall {A : Type} {B : Type} {a1 : A} {a2 : A} .
      (@Coproduct.left A B a1 = @Coproduct.left A B a2) -> (a1 = a2).
Proof.
  intros A B a1 a2 e.
  let f := fun (cp : Coproduct A B) .
              match cp with | Coproduct.left x => x | Coproduct.right _ => a1 end.
  congru f, e |- e'.
  simpl in e'.
  ipso e'.
Qed.

End left. (* left *)

Module right. (* right *)

(* right.injectivity *)
Theorem injectivity
  : forall {A : Type} {B : Type} {b1 : B} {b2 : B} .
      @Coproduct.right A B b1 = @Coproduct.right A B b2 -> b1 = b2.
Proof.
  intros A B b1 b2 e.
  let f := fun (cp : Coproduct A B) .
             match cp with | Coproduct.left _ => b1 | Coproduct.right y => y end.
  congru f, e |- e'.
  simpl in e'.
  ipso e'.
Qed.

End right. (* right *)

Module swap. (* swap *)

(* swap.involution *)
Theorem involution
  : forall {A : Type} {B : Type} (cp : Coproduct A B) . swap (swap cp) = cp.
Proof.
  intros A B cp.
  match cp with | a | b end; simpl in |- *; quod idem est.
Qed.

End swap. (* swap *)

Module mapping. (* mapping *)

Module left. (* mapping.left *)

(* mapping.left.identity *)
Theorem identity
  : forall {A : Type} {B : Type} (cp : Coproduct A B) . map_left (fun (a : A) . a) cp = cp.
Proof.
  intros A B cp.
  match cp with | a | b end; simpl in |- *; quod idem est.
Qed.

(* mapping.left.composition *)
Theorem composition
  : forall {A : Type} {B : Type} {C : Type} {D : Type}
      (f : A -> C) (g : C -> D) (cp : Coproduct A B) .
      map_left g (map_left f cp) = map_left (fun (a : A) . g (f a)) cp.
Proof.
  intros A B C D f g cp.
  match cp with | a | b end; simpl in |- *; quod idem est.
Qed.

End left. (* mapping.left *)

Module right. (* mapping.right *)

(* mapping.right.identity *)
Theorem identity
  : forall {A : Type} {B : Type} (cp : Coproduct A B) . map_right (fun (b : B) . b) cp = cp.
Proof.
  intros A B cp.
  match cp with | a | b end; simpl in |- *; quod idem est.
Qed.

(* mapping.right.composition *)
Theorem composition
  : forall {A : Type} {B : Type} {C : Type} {D : Type}
      (f : B -> C) (g : C -> D) (cp : Coproduct A B) .
      map_right g (map_right f cp) = map_right (fun (b : B) . g (f b)) cp.
Proof.
  intros A B C D f g cp.
  match cp with | a | b end; simpl in |- *; quod idem est.
Qed.

End right. (* mapping.right *)

(* mapping.commutativity *)
Theorem commutativity
  : forall {A : Type} {B : Type} {C : Type} {D : Type}
      (f : A -> C) (g : B -> D) (cp : Coproduct A B) .
      map_left f (map_right g cp) = map_right g (map_left f cp).
Proof.
  intros A B C D f g cp.
  match cp with | a | b end; simpl in |- *; quod idem est.
Qed.

Module both. (* mapping.both *)

(* mapping.both.identity *)
Theorem identity
  : forall {A : Type} {B : Type} (cp : Coproduct A B) .
      bimap (fun (a : A) . a) (fun (b : B) . b) cp = cp.
Proof.
  intros A B cp.
  match cp with | a | b end; simpl in |- *; quod idem est.
Qed.

(* mapping.both.composition *)
Theorem composition
  : forall {A : Type} {B : Type} {C : Type} {D : Type} {E : Type} {F : Type}
      (f1 : A -> C) (f2 : B -> D) (g1 : C -> E) (g2 : D -> F) (cp : Coproduct A B) .
      bimap g1 g2 (bimap f1 f2 cp)
      = bimap (fun (a : A) . g1 (f1 a)) (fun (b : B) . g2 (f2 b)) cp.
Proof.
  intros A B C D E F f1 f2 g1 g2 cp.
  match cp with | a | b end; simpl in |- *; quod idem est.
Qed.

(* mapping.both.decomposition *)
Theorem decomposition
  : forall {A : Type} {B : Type} {C : Type} {D : Type}
      (f : A -> C) (g : B -> D) (cp : Coproduct A B) .
      bimap f g cp = map_left f (map_right g cp).
Proof.
  intros A B C D f g cp.
  match cp with | a | b end; simpl in |- *; quod idem est.
Qed.

End both. (* mapping.both *)

End mapping. (* mapping *)

Module copair. (* copair *)

(* copair.identity *)
Theorem identity
  : forall {A : Type} {B : Type} (cp : Coproduct A B) .
      copair Coproduct.left Coproduct.right cp = cp.
Proof.
  intros A B cp.
  match cp with | a | b end; simpl in |- *; quod idem est.
Qed.

(* copair.naturality *)
Theorem naturality
  : forall {A : Type} {B : Type} {C : Type} {D : Type}
      (f : A -> C) (g : B -> C) (h : C -> D) (cp : Coproduct A B) .
      h (copair f g cp) = copair (fun (a : A) . h (f a)) (fun (b : B) . h (g b)) cp.
Proof.
  intros A B C D f g h cp.
  match cp with | a | b end; simpl in |- *; quod idem est.
Qed.

End copair. (* copair *)

Module test. (* test *)

(* test.reflection *)
Theorem reflection
  : forall {A : Type} {B : Type}
        (left_tester : A -> A -> Bool) (right_tester : B -> B -> Bool) .
      Discernible left_tester -> Discernible right_tester ->
      forall (c1 : Coproduct A B) (c2 : Coproduct A B) .
        test left_tester right_tester c1 c2 = true <-> c1 = c2.
Proof.
  intros A B left_tester right_tester DA DB c1 c2.
  match &c1 with | a1 | b1 end; match &c2 with | a2 | b2 end; simpl in |- *.
  - let proof r : left_tester &a1 &a2 = true <-> &a1 = &a2
      := Discernible.reflection &a1 &a2.
    divide et impera.
    + intro e.
      leibniz (modus aequans &r, &e) in |- *.
      quod idem est.
    + intro e.
      ipso (modus aequans &r, (left.injectivity &e)).
  - divide et impera; intro e; ex &e quodlibet.
  - divide et impera; intro e; ex &e quodlibet.
  - let proof r : right_tester &b1 &b2 = true <-> &b1 = &b2
      := Discernible.reflection &b1 &b2.
    divide et impera.
    + intro e.
      leibniz (modus aequans &r, &e) in |- *.
      quod idem est.
    + intro e.
      ipso (modus aequans &r, (right.injectivity &e)).
Qed.

End test. (* test *)

(* A coproduct tells its values apart when both sides do. *)
Instance discernible
  : forall {A : Type} {B : Type}
        {left_tester : A -> A -> Bool} {right_tester : B -> B -> Bool} .
      Discernible left_tester -> Discernible right_tester ->
      Discernible (test left_tester right_tester) :=
  fun (A : Type) (B : Type)
      (left_tester : A -> A -> Bool) (right_tester : B -> B -> Bool)
      (DA : Discernible left_tester) (DB : Discernible right_tester) .
    ({| Discernible.reflection := test.reflection left_tester right_tester DA DB |}).

End Coproduct. (* Coproduct *)

Abbreviation Coproduct := Coproduct.T.

Existing Instance Coproduct.discernible.

Notation "A + B" := (Coproduct A B)
  : jw_type_scope.

Instance Coproduct_functor
  : forall (A : Type) . Functor (Coproduct A) :=
  fun (A : Type) .
    ({| Functor.map         := @Coproduct.map_right A
      ; Functor.identity    := @Coproduct.mapping.right.identity A
      ; Functor.composition := @Coproduct.mapping.right.composition A |}).
