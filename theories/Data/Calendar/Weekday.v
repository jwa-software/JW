(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

From JW Require Import Core.All.
From JW Require Import Data.Base.Comparison.
From JW Require Import Data.Comparable.
From JW Require Import Data.Discernible.
From JW Require Import Data.Number.Binary.Bin.
From JW Require Import Data.Number.Binary.Bin0.
From JW Require Import Data.Option.
From JW Require Import Tactics.Equation.
From JW Require Import Tactics.Modus.

Local Unset Elimination Schemes.

(* The seven days of the week, numbered as ISO 8601 does. *)
Module Weekday. (* Weekday *)

(* The ctors in the order of the week, [Monday] first. *)
Inductive T : Type :=
  | Monday    : T
  | Tuesday   : T
  | Wednesday : T
  | Thursday  : T
  | Friday    : T
  | Saturday  : T
  | Sunday    : T.

Abbreviation Weekday := T.

(* A weekday's place is written in decimal. *)
Local Open Scope jw_bin_decimal_scope.

(* [Bin] *)
Definition days_in_week : Bin := 7.

(* The weekday's place in the week, [Monday] being 1. *)
(* [Weekday -> Bin] *)
Definition to_b := fun (w : Weekday) .
  match w with
  | Monday    => 1
  | Tuesday   => 2
  | Wednesday => 3
  | Thursday  => 4
  | Friday    => 5
  | Saturday  => 6
  | Sunday    => 7
  end.

(* The weekday at a place in the week, [None] past 7. *)
(* [Bin -> Option Weekday] *)
Definition from_b := fun (n : Bin) .
  match n with
  | 1 => Some Monday
  | 2 => Some Tuesday
  | 3 => Some Wednesday
  | 4 => Some Thursday
  | 5 => Some Friday
  | 6 => Some Saturday
  | 7 => Some Sunday
  | _ => None
  end.

(* The weekday's place in the week counted from 0, [Monday] being 0. *)
(* [Weekday -> Bin0] *)
Definition to_b0 := fun (w : Weekday) .
  match w with
  | Monday    => Bin0.Zero
  | Tuesday   => Bin0.Positive 1
  | Wednesday => Bin0.Positive 2
  | Thursday  => Bin0.Positive 3
  | Friday    => Bin0.Positive 4
  | Saturday  => Bin0.Positive 5
  | Sunday    => Bin0.Positive 6
  end.

(* The weekday at a place in the week counted from 0, [None] past 6. *)
(* [Bin0 -> Option Weekday] *)
Definition from_b0 := fun (k : Bin0) .
  match k with
  | Bin0.Zero       => Some Monday
  | Bin0.Positive 1 => Some Tuesday
  | Bin0.Positive 2 => Some Wednesday
  | Bin0.Positive 3 => Some Thursday
  | Bin0.Positive 4 => Some Friday
  | Bin0.Positive 5 => Some Saturday
  | Bin0.Positive 6 => Some Sunday
  | Bin0.Positive _ => None
  end.

(* The weekday after, [Monday] after [Sunday]. *)
(* [Weekday -> Weekday] *)
Definition next := fun (w : Weekday) .
  match w with
  | Monday    => Tuesday
  | Tuesday   => Wednesday
  | Wednesday => Thursday
  | Thursday  => Friday
  | Friday    => Saturday
  | Saturday  => Sunday
  | Sunday    => Monday
  end.

(* The weekday before, [Sunday] before [Monday]. *)
(* [Weekday -> Weekday] *)
Definition prev := fun (w : Weekday) .
  match w with
  | Monday    => Sunday
  | Tuesday   => Monday
  | Wednesday => Tuesday
  | Thursday  => Wednesday
  | Friday    => Thursday
  | Saturday  => Friday
  | Sunday    => Saturday
  end.

(* The order of the week, [Monday] first, read off the weekdays' places. *)
(* [Weekday -> Weekday -> Comparison] *)
Definition compare := fun (w1 : Weekday) (w2 : Weekday) .
  Bin.compare (to_b w1) (to_b w2).

(* [Weekday -> Weekday -> Bool] *)
Abbreviation eq := (Comparable.eq compare).

(* [Weekday -> Weekday -> Bool] *)
Abbreviation le := (Comparable.le compare).

(* [Weekday -> Weekday -> Bool] *)
Abbreviation lt := (Comparable.lt compare).

(* [Weekday -> Weekday -> Bool] *)
Abbreviation ge := (Comparable.ge compare).

(* [Weekday -> Weekday -> Bool] *)
Abbreviation gt := (Comparable.gt compare).

(* [Weekday -> Weekday -> Weekday] *)
Abbreviation min := (Comparable.min compare).

(* [Weekday -> Weekday -> Weekday] *)
Abbreviation max := (Comparable.max compare).

(* [Weekday -> Weekday -> Bool] *)
Abbreviation equivalent := Discernible.equivalent.

(* [Weekday -> Weekday -> Bool] *)
Abbreviation discern := Discernible.discern.

(* [Weekday -> Weekday -> Prop] *)
Definition LessThan := fun (w1 : Weekday) (w2 : Weekday) .
  (to_b w1 < to_b w2)%b.

Module conversion. (* conversion *)

Module bin. (* conversion.bin *)

(* conversion.bin.retraction *)
Theorem retraction : forall (w : Weekday) . from_b (to_b w) = Some w.
Proof.
  intro w.
  match &w with
  | Monday | Tuesday | Wednesday | Thursday | Friday | Saturday | Sunday
  end; simpl in |- *; quod idem est.
Qed.

(* Every [n] that [from_b] does not map to a weekday is refused within
 * three bits, so the case analysis on [n] ends there.
 *)
(* conversion.bin.specification *)
Theorem specification
  : forall (n : Bin) (w : Weekday) . from_b n = Some w <-> to_b w = n.
Proof.
  intros n w.
  divide et impera.
  - intro e.
    match &n with | One | b0 n1 | b1 n1 end.
    + simpl in &e.
      leibniz <- (Option.some.injectivity &e) in |- *.
      simpl in |- *.
      quod idem est.
    + match &n1 with | One | b0 n2 | b1 n2 end.
      * simpl in &e.
        leibniz <- (Option.some.injectivity &e) in |- *.
        simpl in |- *.
        quod idem est.
      * match &n2 with | One | b0 n3 | b1 n3 end.
        -- simpl in &e.
           leibniz <- (Option.some.injectivity &e) in |- *.
           simpl in |- *.
           quod idem est.
        -- simpl in &e.
           ex &e quodlibet.
        -- simpl in &e.
           ex &e quodlibet.
      * match &n2 with | One | b0 n3 | b1 n3 end.
        -- simpl in &e.
           leibniz <- (Option.some.injectivity &e) in |- *.
           simpl in |- *.
           quod idem est.
        -- simpl in &e.
           ex &e quodlibet.
        -- simpl in &e.
           ex &e quodlibet.
    + match &n1 with | One | b0 n2 | b1 n2 end.
      * simpl in &e.
        leibniz <- (Option.some.injectivity &e) in |- *.
        simpl in |- *.
        quod idem est.
      * match &n2 with | One | b0 n3 | b1 n3 end.
        -- simpl in &e.
           leibniz <- (Option.some.injectivity &e) in |- *.
           simpl in |- *.
           quod idem est.
        -- simpl in &e.
           ex &e quodlibet.
        -- simpl in &e.
           ex &e quodlibet.
      * match &n2 with | One | b0 n3 | b1 n3 end.
        -- simpl in &e.
           leibniz <- (Option.some.injectivity &e) in |- *.
           simpl in |- *.
           quod idem est.
        -- simpl in &e.
           ex &e quodlibet.
        -- simpl in &e.
           ex &e quodlibet.
  - intro e.
    leibniz <- &e in |- *.
    ipso (conversion.bin.retraction &w).
Qed.

(* conversion.bin.injectivity *)
Theorem injectivity
  : forall {w1 : Weekday} {w2 : Weekday} . to_b w1 = to_b w2 -> w1 = w2.
Proof.
  intros w1 w2 e.
  congru from_b, &e |- f.
  leibniz (conversion.bin.retraction &w1), (conversion.bin.retraction &w2) in &f.
  ipso (Option.some.injectivity &f).
Qed.

End bin. (* conversion.bin *)

Module bin0. (* conversion.bin0 *)

(* conversion.bin0.retraction *)
Theorem retraction : forall (w : Weekday) . from_b0 (to_b0 w) = Some w.
Proof.
  intro w.
  match &w with
  | Monday | Tuesday | Wednesday | Thursday | Friday | Saturday | Sunday
  end; simpl in |- *; quod idem est.
Qed.

(* Every [k] that [from_b0] does not map to a weekday is refused within
 * three bits, so the case analysis on [k] ends there.
 *)
(* conversion.bin0.specification *)
Theorem specification
  : forall (k : Bin0) (w : Weekday) . from_b0 k = Some w <-> to_b0 w = k.
Proof.
  intros k w.
  divide et impera.
  - intro e.
    match &k with | | p end.
    + simpl in &e.
      leibniz <- (Option.some.injectivity &e) in |- *.
      simpl in |- *.
      quod idem est.
    + match &p with | One | b0 p1 | b1 p1 end.
      * simpl in &e.
        leibniz <- (Option.some.injectivity &e) in |- *.
        simpl in |- *.
        quod idem est.
      * match &p1 with | One | b0 p2 | b1 p2 end.
        -- simpl in &e.
           leibniz <- (Option.some.injectivity &e) in |- *.
           simpl in |- *.
           quod idem est.
        -- match &p2 with | One | b0 p3 | b1 p3 end.
           ++ simpl in &e.
              leibniz <- (Option.some.injectivity &e) in |- *.
              simpl in |- *.
              quod idem est.
           ++ simpl in &e.
              ex &e quodlibet.
           ++ simpl in &e.
              ex &e quodlibet.
        -- match &p2 with | One | b0 p3 | b1 p3 end.
           ++ simpl in &e.
              leibniz <- (Option.some.injectivity &e) in |- *.
              simpl in |- *.
              quod idem est.
           ++ simpl in &e.
              ex &e quodlibet.
           ++ simpl in &e.
              ex &e quodlibet.
      * match &p1 with | One | b0 p2 | b1 p2 end.
        -- simpl in &e.
           leibniz <- (Option.some.injectivity &e) in |- *.
           simpl in |- *.
           quod idem est.
        -- match &p2 with | One | b0 p3 | b1 p3 end.
           ++ simpl in &e.
              leibniz <- (Option.some.injectivity &e) in |- *.
              simpl in |- *.
              quod idem est.
           ++ simpl in &e.
              ex &e quodlibet.
           ++ simpl in &e.
              ex &e quodlibet.
        -- simpl in &e.
           ex &e quodlibet.
  - intro e.
    leibniz <- &e in |- *.
    ipso (conversion.bin0.retraction &w).
Qed.

(* conversion.bin0.injectivity *)
Theorem injectivity
  : forall {w1 : Weekday} {w2 : Weekday} . to_b0 w1 = to_b0 w2 -> w1 = w2.
Proof.
  intros w1 w2 e.
  congru from_b0, &e |- f.
  leibniz (conversion.bin0.retraction &w1), (conversion.bin0.retraction &w2) in &f.
  ipso (Option.some.injectivity &f).
Qed.

End bin0. (* conversion.bin0 *)

End conversion. (* conversion *)

Module succession. (* succession *)

Module forward. (* succession.forward *)

(* succession.forward.inverse *)
Theorem inverse : forall (w : Weekday) . prev (next w) = w.
Proof.
  intro w.
  match &w with
  | Monday | Tuesday | Wednesday | Thursday | Friday | Saturday | Sunday
  end; simpl in |- *; quod idem est.
Qed.

End forward. (* succession.forward *)

Module backward. (* succession.backward *)

(* succession.backward.inverse *)
Theorem inverse : forall (w : Weekday) . next (prev w) = w.
Proof.
  intro w.
  match &w with
  | Monday | Tuesday | Wednesday | Thursday | Friday | Saturday | Sunday
  end; simpl in |- *; quod idem est.
Qed.

End backward. (* succession.backward *)

End succession. (* succession *)

Module order. (* order *)

Module strict. (* order.strict *)

(* order.strict.transitivity *)
Theorem transitivity
  : forall {w1 : Weekday} {w2 : Weekday} {w3 : Weekday} .
      LessThan w1 w2 -> LessThan w2 w3 -> LessThan w1 w3.
Proof.
  intros w1 w2 w3 h1 h2.
  simpl LessThan in &h1, &h2 |- *.
  ipso (Bin.order.strict.transitivity &h1 &h2).
Qed.

End strict. (* order.strict *)

End order. (* order *)

Module comparison. (* comparison *)

(* comparison.specification *)
Theorem specification
  : forall (w1 : Weekday) (w2 : Weekday) .
      (compare w1 w2 = Comparison.Lt <-> LessThan w1 w2)
      /\ (compare w1 w2 = Comparison.Eq <-> w1 = w2).
Proof.
  intros w1 w2.
  simpl compare, LessThan in |- *.
  let proof s := Bin.comparison.specification (to_b &w1) (to_b &w2).
  match &s with | strict equality end.
  divide et impera.
  - ipso &strict.
  - divide et impera.
    + intro c.
      ipso (conversion.bin.injectivity (modus aequans &equality, &c)).
    + intro e.
      ipso (modus aequans &equality, (congru to_b, &e)).
Qed.

(* comparison.antisymmetry *)
Theorem antisymmetry
  : forall (w1 : Weekday) (w2 : Weekday) . compare w1 w2 = Comparison.transpose (compare w2 w1).
Proof.
  intros w1 w2.
  simpl compare in |- *.
  ipso (Bin.comparison.antisymmetry (to_b &w1) (to_b &w2)).
Qed.

End comparison. (* comparison *)

Instance comparable
  : Comparable compare LessThan :=
  {| Comparable.transitivity := @order.strict.transitivity
  ; Comparable.specification := comparison.specification
  ; Comparable.antisymmetry := comparison.antisymmetry |}.

End Weekday. (* Weekday *)

Abbreviation Weekday := Weekday.T.

Existing Instance Weekday.comparable.
