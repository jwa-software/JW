(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

From JW Require Import Core.All.
From JW Require Import Data.Base.Bool.
From JW Require Import Data.Discernible.
From JW Require Import Data.Literal.
From JW Require Import Tactics.Modus.

Local Unset Elimination Schemes.

(* The types a numeral literal is read into. The plugin behind
 * [Number Notation] reads the literal into them and hands that to the parsing
 * function a notation names; it finds each type by the name it is registered
 * under and builds its terms by constructor position, so every type here has
 * the shape the plugin expects. Digits run most significant first: [1011] is
 * [One (Zero (One (One End)))].
 *)
Module Numeral. (* Numeral *)

Module Decimal. (* Decimal *)

Module Digits. (* Digits *)

Inductive T : Type :=
  | End   : T
  | Zero  : T -> T
  | One   : T -> T
  | Two   : T -> T
  | Three : T -> T
  | Four  : T -> T
  | Five  : T -> T
  | Six   : T -> T
  | Seven : T -> T
  | Eight : T -> T
  | Nine  : T -> T.

Abbreviation Digits := T.

(* The eliminator that [match ... per] takes, written out. *)
Definition induction
  : forall (P : Digits -> Prop) .
      P Digits.End ->
      (forall (d : Digits) . P d -> P (Digits.Zero d)) ->
      (forall (d : Digits) . P d -> P (Digits.One d)) ->
      (forall (d : Digits) . P d -> P (Digits.Two d)) ->
      (forall (d : Digits) . P d -> P (Digits.Three d)) ->
      (forall (d : Digits) . P d -> P (Digits.Four d)) ->
      (forall (d : Digits) . P d -> P (Digits.Five d)) ->
      (forall (d : Digits) . P d -> P (Digits.Six d)) ->
      (forall (d : Digits) . P d -> P (Digits.Seven d)) ->
      (forall (d : Digits) . P d -> P (Digits.Eight d)) ->
      (forall (d : Digits) . P d -> P (Digits.Nine d)) ->
      (forall (d : Digits) . P d)
  := fun (P : Digits -> Prop) (base : P Digits.End)
       (zero : forall (d : Digits) . P d -> P (Digits.Zero d))
       (one : forall (d : Digits) . P d -> P (Digits.One d))
       (two : forall (d : Digits) . P d -> P (Digits.Two d))
       (three : forall (d : Digits) . P d -> P (Digits.Three d))
       (four : forall (d : Digits) . P d -> P (Digits.Four d))
       (five : forall (d : Digits) . P d -> P (Digits.Five d))
       (six : forall (d : Digits) . P d -> P (Digits.Six d))
       (seven : forall (d : Digits) . P d -> P (Digits.Seven d))
       (eight : forall (d : Digits) . P d -> P (Digits.Eight d))
       (nine : forall (d : Digits) . P d -> P (Digits.Nine d)) .
       fix go (d : Digits) : P d :=
         match d with
         | Digits.End      => base
         | Digits.Zero d'  => zero d' (go d')
         | Digits.One d'   => one d' (go d')
         | Digits.Two d'   => two d' (go d')
         | Digits.Three d' => three d' (go d')
         | Digits.Four d'  => four d' (go d')
         | Digits.Five d'  => five d' (go d')
         | Digits.Six d'   => six d' (go d')
         | Digits.Seven d' => seven d' (go d')
         | Digits.Eight d' => eight d' (go d')
         | Digits.Nine d'  => nine d' (go d')
         end.

(* The same digits in the same order: [007] and [7] differ. *)
(* [Digits -> Digits -> Bool] *)
Fixpoint test (d1 : Digits) (d2 : Digits) : Bool :=
  match d1, d2 with
  | Digits.End,       Digits.End       => true
  | Digits.Zero d1',  Digits.Zero d2'  => test d1' d2'
  | Digits.One d1',   Digits.One d2'   => test d1' d2'
  | Digits.Two d1',   Digits.Two d2'   => test d1' d2'
  | Digits.Three d1', Digits.Three d2' => test d1' d2'
  | Digits.Four d1',  Digits.Four d2'  => test d1' d2'
  | Digits.Five d1',  Digits.Five d2'  => test d1' d2'
  | Digits.Six d1',   Digits.Six d2'   => test d1' d2'
  | Digits.Seven d1', Digits.Seven d2' => test d1' d2'
  | Digits.Eight d1', Digits.Eight d2' => test d1' d2'
  | Digits.Nine d1',  Digits.Nine d2'  => test d1' d2'
  | _,                _                => false
  end.

(* [Digits -> Digits -> Bool] *)
Abbreviation equivalent := Discernible.equivalent.

(* [Digits -> Digits -> Bool] *)
Abbreviation discern := Discernible.discern.

Module test. (* test *)

(* test.reflection *)
Theorem reflection
  : forall (d1 : Digits) (d2 : Digits) . test d1 d2 = true <-> d1 = d2.
Proof.
  intros d1 d2.
  divide et impera.
  - extro &d2.
    match &d1 with
    | | d1' by IH | d1' by IH | d1' by IH | d1' by IH | d1' by IH
      | d1' by IH | d1' by IH | d1' by IH | d1' by IH | d1' by IH
    end per Digits.induction.
    + intros d2 e.
      match &d2 with
      | | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2'
      end; simpl in &e.
      * quod idem est.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
    + intros d2 e.
      match &d2 with
      | | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2'
      end; simpl in &e.
      * ex &e quodlibet.
      * leibniz (&IH &d2' &e) in |- *.
        quod idem est.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
    + intros d2 e.
      match &d2 with
      | | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2'
      end; simpl in &e.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * leibniz (&IH &d2' &e) in |- *.
        quod idem est.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
    + intros d2 e.
      match &d2 with
      | | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2'
      end; simpl in &e.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * leibniz (&IH &d2' &e) in |- *.
        quod idem est.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
    + intros d2 e.
      match &d2 with
      | | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2'
      end; simpl in &e.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * leibniz (&IH &d2' &e) in |- *.
        quod idem est.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
    + intros d2 e.
      match &d2 with
      | | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2'
      end; simpl in &e.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * leibniz (&IH &d2' &e) in |- *.
        quod idem est.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
    + intros d2 e.
      match &d2 with
      | | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2'
      end; simpl in &e.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * leibniz (&IH &d2' &e) in |- *.
        quod idem est.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
    + intros d2 e.
      match &d2 with
      | | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2'
      end; simpl in &e.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * leibniz (&IH &d2' &e) in |- *.
        quod idem est.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
    + intros d2 e.
      match &d2 with
      | | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2'
      end; simpl in &e.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * leibniz (&IH &d2' &e) in |- *.
        quod idem est.
      * ex &e quodlibet.
      * ex &e quodlibet.
    + intros d2 e.
      match &d2 with
      | | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2'
      end; simpl in &e.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * leibniz (&IH &d2' &e) in |- *.
        quod idem est.
      * ex &e quodlibet.
    + intros d2 e.
      match &d2 with
      | | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2'
      end; simpl in &e.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * leibniz (&IH &d2' &e) in |- *.
        quod idem est.
  - intro e.
    leibniz <- &e in |- *.
    rm &e.
    match &d1 with
    | | d1' by IH | d1' by IH | d1' by IH | d1' by IH | d1' by IH
      | d1' by IH | d1' by IH | d1' by IH | d1' by IH | d1' by IH
    end per Digits.induction; simpl in |- *.
    + quod idem est.
    + ipso &IH.
    + ipso &IH.
    + ipso &IH.
    + ipso &IH.
    + ipso &IH.
    + ipso &IH.
    + ipso &IH.
    + ipso &IH.
    + ipso &IH.
    + ipso &IH.
Qed.

End test. (* test *)

Instance discernible
  : Discernible test :=
  {| Discernible.reflection := test.reflection |}.

End Digits. (* Digits *)

Abbreviation Digits := Digits.T.

Module Signed. (* Signed *)

Inductive T : Type :=
  | Positive : Digits -> T
  | Negative : Digits -> T.

Abbreviation Signed := T.

(* The same sign and the same digits. *)
(* [Signed -> Signed -> Bool] *)
Definition test := fun (s1 : Signed) (s2 : Signed) .
  match s1, s2 with
  | Signed.Positive d1, Signed.Positive d2 => Digits.test d1 d2
  | Signed.Negative d1, Signed.Negative d2 => Digits.test d1 d2
  | _,                  _                  => false
  end.

(* [Signed -> Signed -> Bool] *)
Abbreviation equivalent := Discernible.equivalent.

(* [Signed -> Signed -> Bool] *)
Abbreviation discern := Discernible.discern.

Module test. (* test *)

(* test.reflection *)
Theorem reflection
  : forall (s1 : Signed) (s2 : Signed) . test s1 s2 = true <-> s1 = s2.
Proof.
  intros s1 s2.
  divide et impera.
  - intro e.
    match &s1 with | d1 | d1 end; match &s2 with | d2 | d2 end; simpl in &e.
    + leibniz (modus aequans (Digits.test.reflection &d1 &d2), &e) in |- *.
      quod idem est.
    + ex &e quodlibet.
    + ex &e quodlibet.
    + leibniz (modus aequans (Digits.test.reflection &d1 &d2), &e) in |- *.
      quod idem est.
  - intro e.
    leibniz <- &e in |- *.
    rm &e.
    match &s1 with | d1 | d1 end; simpl in |- *.
    + ipso (modus aequans (Digits.test.reflection &d1 &d1), (Identity.reflexivity &d1)).
    + ipso (modus aequans (Digits.test.reflection &d1 &d1), (Identity.reflexivity &d1)).
Qed.

End test. (* test *)

Instance discernible
  : Discernible test :=
  {| Discernible.reflection := test.reflection |}.

End Signed. (* Signed *)

Abbreviation Signed := Signed.T.

(* [1.5] is [Point 1 5], [1.5e3] is [PointExponent 1 5 3]. *)
Module Fractional. (* Fractional *)

Inductive T : Type :=
  | Point         : Signed -> Digits -> T
  | PointExponent : Signed -> Digits -> Signed -> T.

Abbreviation Fractional := T.

(* The same form, and the same parts in it. *)
(* [Fractional -> Fractional -> Bool] *)
Definition test := fun (f1 : Fractional) (f2 : Fractional) .
  match f1, f2 with
  | Fractional.Point s1 d1, Fractional.Point s2 d2 =>
      (Signed.test s1 s2 && Digits.test d1 d2)%bool
  | Fractional.PointExponent s1 d1 x1, Fractional.PointExponent s2 d2 x2 =>
      (Signed.test s1 s2 && (Digits.test d1 d2 && Signed.test x1 x2))%bool
  | _, _ => false
  end.

(* [Fractional -> Fractional -> Bool] *)
Abbreviation equivalent := Discernible.equivalent.

(* [Fractional -> Fractional -> Bool] *)
Abbreviation discern := Discernible.discern.

Module test. (* test *)

(* test.reflection *)
Theorem reflection
  : forall (f1 : Fractional) (f2 : Fractional) . test f1 f2 = true <-> f1 = f2.
Proof.
  intros f1 f2.
  divide et impera.
  - intro e.
    match &f1 with | s1 d1 | s1 d1 x1 end; match &f2 with | s2 d2 | s2 d2 x2 end;
      simpl in &e.
    + modus aequans (Bool.conjunction.truth.specification _ _), &e |- c.
      match &c with | es ed end.
      leibniz
        (modus aequans (Signed.test.reflection &s1 &s2), &es),
        (modus aequans (Digits.test.reflection &d1 &d2), &ed)
        in |- *.
      quod idem est.
    + ex &e quodlibet.
    + ex &e quodlibet.
    + modus aequans (Bool.conjunction.truth.specification _ _), &e |- c.
      match &c with | es rest end.
      modus aequans (Bool.conjunction.truth.specification _ _), &rest |- c'.
      match &c' with | ed ex end.
      leibniz
        (modus aequans (Signed.test.reflection &s1 &s2), &es),
        (modus aequans (Digits.test.reflection &d1 &d2), &ed),
        (modus aequans (Signed.test.reflection &x1 &x2), &ex)
        in |- *.
      quod idem est.
  - intro e.
    leibniz <- &e in |- *.
    rm &e.
    match &f1 with | s1 d1 | s1 d1 x1 end; simpl in |- *.
    + leibniz
        (modus aequans (Signed.test.reflection &s1 &s1), (Identity.reflexivity &s1)),
        (modus aequans (Digits.test.reflection &d1 &d1), (Identity.reflexivity &d1))
        in |- *.
      simpl in |- *.
      quod idem est.
    + leibniz
        (modus aequans (Signed.test.reflection &s1 &s1), (Identity.reflexivity &s1)),
        (modus aequans (Digits.test.reflection &d1 &d1), (Identity.reflexivity &d1)),
        (modus aequans (Signed.test.reflection &x1 &x1), (Identity.reflexivity &x1))
        in |- *.
      simpl in |- *.
      quod idem est.
Qed.

End test. (* test *)

Instance discernible
  : Discernible test :=
  {| Discernible.reflection := test.reflection |}.

End Fractional. (* Fractional *)

Abbreviation Fractional := Fractional.T.

End Decimal. (* Decimal *)

Module Hexadecimal. (* Hexadecimal *)

Module Digits. (* Digits *)

Inductive T : Type :=
  | End      : T
  | Zero     : T -> T
  | One      : T -> T
  | Two      : T -> T
  | Three    : T -> T
  | Four     : T -> T
  | Five     : T -> T
  | Six      : T -> T
  | Seven    : T -> T
  | Eight    : T -> T
  | Nine     : T -> T
  | Ten      : T -> T
  | Eleven   : T -> T
  | Twelve   : T -> T
  | Thirteen : T -> T
  | Fourteen : T -> T
  | Fifteen  : T -> T.

Abbreviation Digits := T.

(* The eliminator that [match ... per] takes, written out. *)
Definition induction
  : forall (P : Digits -> Prop) .
      P Digits.End ->
      (forall (d : Digits) . P d -> P (Digits.Zero d)) ->
      (forall (d : Digits) . P d -> P (Digits.One d)) ->
      (forall (d : Digits) . P d -> P (Digits.Two d)) ->
      (forall (d : Digits) . P d -> P (Digits.Three d)) ->
      (forall (d : Digits) . P d -> P (Digits.Four d)) ->
      (forall (d : Digits) . P d -> P (Digits.Five d)) ->
      (forall (d : Digits) . P d -> P (Digits.Six d)) ->
      (forall (d : Digits) . P d -> P (Digits.Seven d)) ->
      (forall (d : Digits) . P d -> P (Digits.Eight d)) ->
      (forall (d : Digits) . P d -> P (Digits.Nine d)) ->
      (forall (d : Digits) . P d -> P (Digits.Ten d)) ->
      (forall (d : Digits) . P d -> P (Digits.Eleven d)) ->
      (forall (d : Digits) . P d -> P (Digits.Twelve d)) ->
      (forall (d : Digits) . P d -> P (Digits.Thirteen d)) ->
      (forall (d : Digits) . P d -> P (Digits.Fourteen d)) ->
      (forall (d : Digits) . P d -> P (Digits.Fifteen d)) ->
      (forall (d : Digits) . P d)
  := fun (P : Digits -> Prop) (base : P Digits.End)
       (zero : forall (d : Digits) . P d -> P (Digits.Zero d))
       (one : forall (d : Digits) . P d -> P (Digits.One d))
       (two : forall (d : Digits) . P d -> P (Digits.Two d))
       (three : forall (d : Digits) . P d -> P (Digits.Three d))
       (four : forall (d : Digits) . P d -> P (Digits.Four d))
       (five : forall (d : Digits) . P d -> P (Digits.Five d))
       (six : forall (d : Digits) . P d -> P (Digits.Six d))
       (seven : forall (d : Digits) . P d -> P (Digits.Seven d))
       (eight : forall (d : Digits) . P d -> P (Digits.Eight d))
       (nine : forall (d : Digits) . P d -> P (Digits.Nine d))
       (ten : forall (d : Digits) . P d -> P (Digits.Ten d))
       (eleven : forall (d : Digits) . P d -> P (Digits.Eleven d))
       (twelve : forall (d : Digits) . P d -> P (Digits.Twelve d))
       (thirteen : forall (d : Digits) . P d -> P (Digits.Thirteen d))
       (fourteen : forall (d : Digits) . P d -> P (Digits.Fourteen d))
       (fifteen : forall (d : Digits) . P d -> P (Digits.Fifteen d)) .
       fix go (d : Digits) : P d :=
         match d with
         | Digits.End         => base
         | Digits.Zero d'     => zero d' (go d')
         | Digits.One d'      => one d' (go d')
         | Digits.Two d'      => two d' (go d')
         | Digits.Three d'    => three d' (go d')
         | Digits.Four d'     => four d' (go d')
         | Digits.Five d'     => five d' (go d')
         | Digits.Six d'      => six d' (go d')
         | Digits.Seven d'    => seven d' (go d')
         | Digits.Eight d'    => eight d' (go d')
         | Digits.Nine d'     => nine d' (go d')
         | Digits.Ten d'      => ten d' (go d')
         | Digits.Eleven d'   => eleven d' (go d')
         | Digits.Twelve d'   => twelve d' (go d')
         | Digits.Thirteen d' => thirteen d' (go d')
         | Digits.Fourteen d' => fourteen d' (go d')
         | Digits.Fifteen d'  => fifteen d' (go d')
         end.

(* The same digits in the same order: [0x0F] and [0xF] differ. *)
(* [Digits -> Digits -> Bool] *)
Fixpoint test (d1 : Digits) (d2 : Digits) : Bool :=
  match d1, d2 with
  | Digits.End,          Digits.End          => true
  | Digits.Zero d1',     Digits.Zero d2'     => test d1' d2'
  | Digits.One d1',      Digits.One d2'      => test d1' d2'
  | Digits.Two d1',      Digits.Two d2'      => test d1' d2'
  | Digits.Three d1',    Digits.Three d2'    => test d1' d2'
  | Digits.Four d1',     Digits.Four d2'     => test d1' d2'
  | Digits.Five d1',     Digits.Five d2'     => test d1' d2'
  | Digits.Six d1',      Digits.Six d2'      => test d1' d2'
  | Digits.Seven d1',    Digits.Seven d2'    => test d1' d2'
  | Digits.Eight d1',    Digits.Eight d2'    => test d1' d2'
  | Digits.Nine d1',     Digits.Nine d2'     => test d1' d2'
  | Digits.Ten d1',      Digits.Ten d2'      => test d1' d2'
  | Digits.Eleven d1',   Digits.Eleven d2'   => test d1' d2'
  | Digits.Twelve d1',   Digits.Twelve d2'   => test d1' d2'
  | Digits.Thirteen d1', Digits.Thirteen d2' => test d1' d2'
  | Digits.Fourteen d1', Digits.Fourteen d2' => test d1' d2'
  | Digits.Fifteen d1',  Digits.Fifteen d2'  => test d1' d2'
  | _,                   _                   => false
  end.

(* [Digits -> Digits -> Bool] *)
Abbreviation equivalent := Discernible.equivalent.

(* [Digits -> Digits -> Bool] *)
Abbreviation discern := Discernible.discern.

Module test. (* test *)

(* test.reflection *)
Theorem reflection
  : forall (d1 : Digits) (d2 : Digits) . test d1 d2 = true <-> d1 = d2.
Proof.
  intros d1 d2.
  divide et impera.
  - extro &d2.
    match &d1 with
    | | d1' by IH | d1' by IH | d1' by IH | d1' by IH | d1' by IH | d1' by IH | d1' by IH
      | d1' by IH | d1' by IH | d1' by IH | d1' by IH | d1' by IH | d1' by IH | d1' by IH
      | d1' by IH | d1' by IH
    end per Digits.induction.
    + intros d2 e.
      match &d2 with
      | | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2'
        | d2' | d2'
      end; simpl in &e.
      * quod idem est.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
    + intros d2 e.
      match &d2 with
      | | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2'
        | d2' | d2'
      end; simpl in &e.
      * ex &e quodlibet.
      * leibniz (&IH &d2' &e) in |- *.
        quod idem est.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
    + intros d2 e.
      match &d2 with
      | | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2'
        | d2' | d2'
      end; simpl in &e.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * leibniz (&IH &d2' &e) in |- *.
        quod idem est.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
    + intros d2 e.
      match &d2 with
      | | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2'
        | d2' | d2'
      end; simpl in &e.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * leibniz (&IH &d2' &e) in |- *.
        quod idem est.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
    + intros d2 e.
      match &d2 with
      | | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2'
        | d2' | d2'
      end; simpl in &e.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * leibniz (&IH &d2' &e) in |- *.
        quod idem est.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
    + intros d2 e.
      match &d2 with
      | | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2'
        | d2' | d2'
      end; simpl in &e.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * leibniz (&IH &d2' &e) in |- *.
        quod idem est.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
    + intros d2 e.
      match &d2 with
      | | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2'
        | d2' | d2'
      end; simpl in &e.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * leibniz (&IH &d2' &e) in |- *.
        quod idem est.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
    + intros d2 e.
      match &d2 with
      | | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2'
        | d2' | d2'
      end; simpl in &e.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * leibniz (&IH &d2' &e) in |- *.
        quod idem est.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
    + intros d2 e.
      match &d2 with
      | | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2'
        | d2' | d2'
      end; simpl in &e.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * leibniz (&IH &d2' &e) in |- *.
        quod idem est.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
    + intros d2 e.
      match &d2 with
      | | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2'
        | d2' | d2'
      end; simpl in &e.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * leibniz (&IH &d2' &e) in |- *.
        quod idem est.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
    + intros d2 e.
      match &d2 with
      | | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2'
        | d2' | d2'
      end; simpl in &e.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * leibniz (&IH &d2' &e) in |- *.
        quod idem est.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
    + intros d2 e.
      match &d2 with
      | | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2'
        | d2' | d2'
      end; simpl in &e.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * leibniz (&IH &d2' &e) in |- *.
        quod idem est.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
    + intros d2 e.
      match &d2 with
      | | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2'
        | d2' | d2'
      end; simpl in &e.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * leibniz (&IH &d2' &e) in |- *.
        quod idem est.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
    + intros d2 e.
      match &d2 with
      | | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2'
        | d2' | d2'
      end; simpl in &e.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * leibniz (&IH &d2' &e) in |- *.
        quod idem est.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
    + intros d2 e.
      match &d2 with
      | | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2'
        | d2' | d2'
      end; simpl in &e.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * leibniz (&IH &d2' &e) in |- *.
        quod idem est.
      * ex &e quodlibet.
      * ex &e quodlibet.
    + intros d2 e.
      match &d2 with
      | | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2'
        | d2' | d2'
      end; simpl in &e.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * leibniz (&IH &d2' &e) in |- *.
        quod idem est.
      * ex &e quodlibet.
    + intros d2 e.
      match &d2 with
      | | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2' | d2'
        | d2' | d2'
      end; simpl in &e.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * ex &e quodlibet.
      * leibniz (&IH &d2' &e) in |- *.
        quod idem est.
  - intro e.
    leibniz <- &e in |- *.
    rm &e.
    match &d1 with
    | | d1' by IH | d1' by IH | d1' by IH | d1' by IH | d1' by IH | d1' by IH | d1' by IH
      | d1' by IH | d1' by IH | d1' by IH | d1' by IH | d1' by IH | d1' by IH | d1' by IH
      | d1' by IH | d1' by IH
    end per Digits.induction; simpl in |- *.
    + quod idem est.
    + ipso &IH.
    + ipso &IH.
    + ipso &IH.
    + ipso &IH.
    + ipso &IH.
    + ipso &IH.
    + ipso &IH.
    + ipso &IH.
    + ipso &IH.
    + ipso &IH.
    + ipso &IH.
    + ipso &IH.
    + ipso &IH.
    + ipso &IH.
    + ipso &IH.
    + ipso &IH.
Qed.

End test. (* test *)

Instance discernible
  : Discernible test :=
  {| Discernible.reflection := test.reflection |}.

End Digits. (* Digits *)

Abbreviation Digits := Digits.T.

Module Signed. (* Signed *)

Inductive T : Type :=
  | Positive : Digits -> T
  | Negative : Digits -> T.

Abbreviation Signed := T.

(* The same sign and the same digits. *)
(* [Signed -> Signed -> Bool] *)
Definition test := fun (s1 : Signed) (s2 : Signed) .
  match s1, s2 with
  | Signed.Positive d1, Signed.Positive d2 => Digits.test d1 d2
  | Signed.Negative d1, Signed.Negative d2 => Digits.test d1 d2
  | _,                  _                  => false
  end.

(* [Signed -> Signed -> Bool] *)
Abbreviation equivalent := Discernible.equivalent.

(* [Signed -> Signed -> Bool] *)
Abbreviation discern := Discernible.discern.

Module test. (* test *)

(* test.reflection *)
Theorem reflection
  : forall (s1 : Signed) (s2 : Signed) . test s1 s2 = true <-> s1 = s2.
Proof.
  intros s1 s2.
  divide et impera.
  - intro e.
    match &s1 with | d1 | d1 end; match &s2 with | d2 | d2 end; simpl in &e.
    + leibniz (modus aequans (Digits.test.reflection &d1 &d2), &e) in |- *.
      quod idem est.
    + ex &e quodlibet.
    + ex &e quodlibet.
    + leibniz (modus aequans (Digits.test.reflection &d1 &d2), &e) in |- *.
      quod idem est.
  - intro e.
    leibniz <- &e in |- *.
    rm &e.
    match &s1 with | d1 | d1 end; simpl in |- *.
    + ipso (modus aequans (Digits.test.reflection &d1 &d1), (Identity.reflexivity &d1)).
    + ipso (modus aequans (Digits.test.reflection &d1 &d1), (Identity.reflexivity &d1)).
Qed.

End test. (* test *)

Instance discernible
  : Discernible test :=
  {| Discernible.reflection := test.reflection |}.

End Signed. (* Signed *)

Abbreviation Signed := Signed.T.

(* The exponent of a hexadecimal literal is written in decimal. *)
Module Fractional. (* Fractional *)

Inductive T : Type :=
  | Point         : Signed -> Digits -> T
  | PointExponent : Signed -> Digits -> Decimal.Signed -> T.

Abbreviation Fractional := T.

(* The same form, and the same parts in it. *)
(* [Fractional -> Fractional -> Bool] *)
Definition test := fun (f1 : Fractional) (f2 : Fractional) .
  match f1, f2 with
  | Fractional.Point s1 d1, Fractional.Point s2 d2 =>
      (Signed.test s1 s2 && Digits.test d1 d2)%bool
  | Fractional.PointExponent s1 d1 x1, Fractional.PointExponent s2 d2 x2 =>
      (Signed.test s1 s2 && (Digits.test d1 d2 && Decimal.Signed.test x1 x2))%bool
  | _, _ => false
  end.

(* [Fractional -> Fractional -> Bool] *)
Abbreviation equivalent := Discernible.equivalent.

(* [Fractional -> Fractional -> Bool] *)
Abbreviation discern := Discernible.discern.

Module test. (* test *)

(* test.reflection *)
Theorem reflection
  : forall (f1 : Fractional) (f2 : Fractional) . test f1 f2 = true <-> f1 = f2.
Proof.
  intros f1 f2.
  divide et impera.
  - intro e.
    match &f1 with | s1 d1 | s1 d1 x1 end; match &f2 with | s2 d2 | s2 d2 x2 end;
      simpl in &e.
    + modus aequans (Bool.conjunction.truth.specification _ _), &e |- c.
      match &c with | es ed end.
      leibniz
        (modus aequans (Signed.test.reflection &s1 &s2), &es),
        (modus aequans (Digits.test.reflection &d1 &d2), &ed)
        in |- *.
      quod idem est.
    + ex &e quodlibet.
    + ex &e quodlibet.
    + modus aequans (Bool.conjunction.truth.specification _ _), &e |- c.
      match &c with | es rest end.
      modus aequans (Bool.conjunction.truth.specification _ _), &rest |- c'.
      match &c' with | ed ex end.
      leibniz
        (modus aequans (Signed.test.reflection &s1 &s2), &es),
        (modus aequans (Digits.test.reflection &d1 &d2), &ed),
        (modus aequans (Decimal.Signed.test.reflection &x1 &x2), &ex)
        in |- *.
      quod idem est.
  - intro e.
    leibniz <- &e in |- *.
    rm &e.
    match &f1 with | s1 d1 | s1 d1 x1 end; simpl in |- *.
    + leibniz
        (modus aequans (Signed.test.reflection &s1 &s1), (Identity.reflexivity &s1)),
        (modus aequans (Digits.test.reflection &d1 &d1), (Identity.reflexivity &d1))
        in |- *.
      simpl in |- *.
      quod idem est.
    + leibniz
        (modus aequans (Signed.test.reflection &s1 &s1), (Identity.reflexivity &s1)),
        (modus aequans (Digits.test.reflection &d1 &d1), (Identity.reflexivity &d1)),
        (modus aequans (Decimal.Signed.test.reflection &x1 &x1), (Identity.reflexivity &x1))
        in |- *.
      simpl in |- *.
      quod idem est.
Qed.

End test. (* test *)

Instance discernible
  : Discernible test :=
  {| Discernible.reflection := test.reflection |}.

End Fractional. (* Fractional *)

Abbreviation Fractional := Fractional.T.

End Hexadecimal. (* Hexadecimal *)

Module Unsigned. (* Unsigned *)

Inductive T : Type :=
  | Decimal     : Decimal.Digits -> T
  | Hexadecimal : Hexadecimal.Digits -> T.

Abbreviation Unsigned := T.

(* The same base and the same digits. *)
(* [Unsigned -> Unsigned -> Bool] *)
Definition test := fun (u1 : Unsigned) (u2 : Unsigned) .
  match u1, u2 with
  | Unsigned.Decimal d1,     Unsigned.Decimal d2     => Decimal.Digits.test d1 d2
  | Unsigned.Hexadecimal h1, Unsigned.Hexadecimal h2 => Hexadecimal.Digits.test h1 h2
  | _,                       _                       => false
  end.

(* [Unsigned -> Unsigned -> Bool] *)
Abbreviation equivalent := Discernible.equivalent.

(* [Unsigned -> Unsigned -> Bool] *)
Abbreviation discern := Discernible.discern.

Module test. (* test *)

(* test.reflection *)
Theorem reflection
  : forall (u1 : Unsigned) (u2 : Unsigned) . test u1 u2 = true <-> u1 = u2.
Proof.
  intros u1 u2.
  divide et impera.
  - intro e.
    match &u1 with | d1 | h1 end; match &u2 with | d2 | h2 end; simpl in &e.
    + leibniz (modus aequans (Decimal.Digits.test.reflection &d1 &d2), &e) in |- *.
      quod idem est.
    + ex &e quodlibet.
    + ex &e quodlibet.
    + leibniz (modus aequans (Hexadecimal.Digits.test.reflection &h1 &h2), &e) in |- *.
      quod idem est.
  - intro e.
    leibniz <- &e in |- *.
    rm &e.
    match &u1 with | d1 | h1 end; simpl in |- *.
    + ipso
        (modus aequans (Decimal.Digits.test.reflection &d1 &d1), (Identity.reflexivity &d1)).
    + ipso
        (modus aequans (Hexadecimal.Digits.test.reflection &h1 &h1),
           (Identity.reflexivity &h1)).
Qed.

End test. (* test *)

Instance discernible
  : Discernible test :=
  {| Discernible.reflection := test.reflection |}.

End Unsigned. (* Unsigned *)

Abbreviation Unsigned := Unsigned.T.

Module Signed. (* Signed *)

Inductive T : Type :=
  | Decimal     : Decimal.Signed -> T
  | Hexadecimal : Hexadecimal.Signed -> T.

Abbreviation Signed := T.

(* The same base and the same signed digits. *)
(* [Signed -> Signed -> Bool] *)
Definition test := fun (s1 : Signed) (s2 : Signed) .
  match s1, s2 with
  | Signed.Decimal d1,     Signed.Decimal d2     => Decimal.Signed.test d1 d2
  | Signed.Hexadecimal h1, Signed.Hexadecimal h2 => Hexadecimal.Signed.test h1 h2
  | _,                     _                     => false
  end.

(* [Signed -> Signed -> Bool] *)
Abbreviation equivalent := Discernible.equivalent.

(* [Signed -> Signed -> Bool] *)
Abbreviation discern := Discernible.discern.

Module test. (* test *)

(* test.reflection *)
Theorem reflection
  : forall (s1 : Signed) (s2 : Signed) . test s1 s2 = true <-> s1 = s2.
Proof.
  intros s1 s2.
  divide et impera.
  - intro e.
    match &s1 with | d1 | h1 end; match &s2 with | d2 | h2 end; simpl in &e.
    + leibniz (modus aequans (Decimal.Signed.test.reflection &d1 &d2), &e) in |- *.
      quod idem est.
    + ex &e quodlibet.
    + ex &e quodlibet.
    + leibniz (modus aequans (Hexadecimal.Signed.test.reflection &h1 &h2), &e) in |- *.
      quod idem est.
  - intro e.
    leibniz <- &e in |- *.
    rm &e.
    match &s1 with | d1 | h1 end; simpl in |- *.
    + ipso
        (modus aequans (Decimal.Signed.test.reflection &d1 &d1), (Identity.reflexivity &d1)).
    + ipso
        (modus aequans (Hexadecimal.Signed.test.reflection &h1 &h1),
           (Identity.reflexivity &h1)).
Qed.

End test. (* test *)

Instance discernible
  : Discernible test :=
  {| Discernible.reflection := test.reflection |}.

End Signed. (* Signed *)

Abbreviation Signed := Signed.T.

Module Fractional. (* Fractional *)

Inductive T : Type :=
  | Decimal     : Decimal.Fractional -> T
  | Hexadecimal : Hexadecimal.Fractional -> T.

Abbreviation Fractional := T.

(* The same base and the same fractional parts. *)
(* [Fractional -> Fractional -> Bool] *)
Definition test := fun (f1 : Fractional) (f2 : Fractional) .
  match f1, f2 with
  | Fractional.Decimal d1,     Fractional.Decimal d2     => Decimal.Fractional.test d1 d2
  | Fractional.Hexadecimal h1, Fractional.Hexadecimal h2 => Hexadecimal.Fractional.test h1 h2
  | _,                         _                         => false
  end.

(* [Fractional -> Fractional -> Bool] *)
Abbreviation equivalent := Discernible.equivalent.

(* [Fractional -> Fractional -> Bool] *)
Abbreviation discern := Discernible.discern.

Module test. (* test *)

(* test.reflection *)
Theorem reflection
  : forall (f1 : Fractional) (f2 : Fractional) . test f1 f2 = true <-> f1 = f2.
Proof.
  intros f1 f2.
  divide et impera.
  - intro e.
    match &f1 with | d1 | h1 end; match &f2 with | d2 | h2 end; simpl in &e.
    + leibniz (modus aequans (Decimal.Fractional.test.reflection &d1 &d2), &e) in |- *.
      quod idem est.
    + ex &e quodlibet.
    + ex &e quodlibet.
    + leibniz (modus aequans (Hexadecimal.Fractional.test.reflection &h1 &h2), &e) in |- *.
      quod idem est.
  - intro e.
    leibniz <- &e in |- *.
    rm &e.
    match &f1 with | d1 | h1 end; simpl in |- *.
    + ipso
        (modus aequans (Decimal.Fractional.test.reflection &d1 &d1),
           (Identity.reflexivity &d1)).
    + ipso
        (modus aequans (Hexadecimal.Fractional.test.reflection &h1 &h1),
           (Identity.reflexivity &h1)).
Qed.

End test. (* test *)

Instance discernible
  : Discernible test :=
  {| Discernible.reflection := test.reflection |}.

End Fractional. (* Fractional *)

Abbreviation Fractional := Fractional.T.

End Numeral. (* Numeral *)

Existing Instance Numeral.Decimal.Digits.discernible.
Existing Instance Numeral.Decimal.Signed.discernible.
Existing Instance Numeral.Decimal.Fractional.discernible.
Existing Instance Numeral.Hexadecimal.Digits.discernible.
Existing Instance Numeral.Hexadecimal.Signed.discernible.
Existing Instance Numeral.Hexadecimal.Fractional.discernible.
Existing Instance Numeral.Unsigned.discernible.
Existing Instance Numeral.Signed.discernible.
Existing Instance Numeral.Fractional.discernible.

Register Numeral.Decimal.Digits.T         as num.uint.type.
Register Numeral.Decimal.Signed.T         as num.int.type.
Register Numeral.Decimal.Fractional.T     as num.decimal.type.
Register Numeral.Hexadecimal.Digits.T     as num.hexadecimal_uint.type.
Register Numeral.Hexadecimal.Signed.T     as num.hexadecimal_int.type.
Register Numeral.Hexadecimal.Fractional.T as num.hexadecimal.type.
Register Numeral.Unsigned.T               as num.num_uint.type.
Register Numeral.Signed.T                 as num.num_int.type.
Register Numeral.Fractional.T             as num.number.type.
