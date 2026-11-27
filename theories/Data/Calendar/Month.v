(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

From JW Require Import Core.All.
From JW Require Import Data.Base.Comparison.
From JW Require Import Data.Comparable.
From JW Require Import Data.Number.Binary.Bin.
From JW Require Import Data.Number.Binary.Bin0.
From JW Require Import Data.Option.
From JW Require Import Tactics.Equation.
From JW Require Import Tactics.Modus.

Local Unset Elimination Schemes.

(* The twelve months of the year. *)
Module Month. (* Month *)

(* The ctors in the order of the year. *)
Inductive T : Type :=
  | January   : T
  | February  : T
  | March     : T
  | April     : T
  | May       : T
  | June      : T
  | July      : T
  | August    : T
  | September : T
  | October   : T
  | November  : T
  | December  : T.

Abbreviation Month := T.

(* A month's place is written in decimal. *)
Local Open Scope jw_bin_decimal_scope.

(* [Bin] *)
Definition months_in_year : Bin := 12.

(* The month's place in the year, [January] being 1. *)
(* [Month -> Bin] *)
Definition to_b := fun (m : Month) .
  match m with
  | January   =>  1
  | February  =>  2
  | March     =>  3
  | April     =>  4
  | May       =>  5
  | June      =>  6
  | July      =>  7
  | August    =>  8
  | September =>  9
  | October   => 10
  | November  => 11
  | December  => 12
  end.

(* The month at a place in the year, [None] past 12. *)
(* [Bin -> Option Month] *)
Definition from_b := fun (n : Bin) .
  match n with
  |  1 => Some January
  |  2 => Some February
  |  3 => Some March
  |  4 => Some April
  |  5 => Some May
  |  6 => Some June
  |  7 => Some July
  |  8 => Some August
  |  9 => Some September
  | 10 => Some October
  | 11 => Some November
  | 12 => Some December
  | _  => None
  end.

(* The month's place in the year counted from 0, [January] being 0. *)
(* [Month -> Bin0] *)
Definition to_b0 := fun (m : Month) .
  match m with
  | January   => Bin0.Zero
  | February  => Bin0.Positive  1
  | March     => Bin0.Positive  2
  | April     => Bin0.Positive  3
  | May       => Bin0.Positive  4
  | June      => Bin0.Positive  5
  | July      => Bin0.Positive  6
  | August    => Bin0.Positive  7
  | September => Bin0.Positive  8
  | October   => Bin0.Positive  9
  | November  => Bin0.Positive 10
  | December  => Bin0.Positive 11
  end.

(* The month at a place in the year counted from 0, [None] past 11. *)
(* [Bin0 -> Option Month] *)
Definition from_b0 := fun (k : Bin0) .
  match k with
  | Bin0.Zero        => Some January
  | Bin0.Positive  1 => Some February
  | Bin0.Positive  2 => Some March
  | Bin0.Positive  3 => Some April
  | Bin0.Positive  4 => Some May
  | Bin0.Positive  5 => Some June
  | Bin0.Positive  6 => Some July
  | Bin0.Positive  7 => Some August
  | Bin0.Positive  8 => Some September
  | Bin0.Positive  9 => Some October
  | Bin0.Positive 10 => Some November
  | Bin0.Positive 11 => Some December
  | Bin0.Positive  _ => None
  end.

(* The month after, [January] after [December]. *)
(* [Month -> Month] *)
Definition next := fun (m : Month) .
  match m with
  | January   => February
  | February  => March
  | March     => April
  | April     => May
  | May       => June
  | June      => July
  | July      => August
  | August    => September
  | September => October
  | October   => November
  | November  => December
  | December  => January
  end.

(* The month before, [December] before [January]. *)
(* [Month -> Month] *)
Definition prev := fun (m : Month) .
  match m with
  | January   => December
  | February  => January
  | March     => February
  | April     => March
  | May       => April
  | June      => May
  | July      => June
  | August    => July
  | September => August
  | October   => September
  | November  => October
  | December  => November
  end.

(* The order of the year, read off the months' places. *)
(* [Month -> Month -> Comparison] *)
Definition compare := fun (m1 : Month) (m2 : Month) .
  Bin.compare (to_b m1) (to_b m2).

(* [Month -> Month -> Prop] *)
Definition LessThan := fun (m1 : Month) (m2 : Month) .
  (to_b m1 < to_b m2)%b.

Module conversion. (* conversion *)

Module bin. (* conversion.bin *)

(* conversion.bin.retraction *)
Theorem retraction : forall (m : Month) . from_b (to_b m) = Some m.
Proof.
  intro m.
  match &m with
  | January | February | March | April | May | June
  | July | August | September | October | November | December
  end; simpl in |- *; quod idem est.
Qed.

(* Every [n] that [from_b] does not map to a month is refused within
 * four bits, so the case analysis on [n] ends there.
 *)
(* conversion.bin.specification *)
Theorem specification
  : forall (n : Bin) (m : Month) . from_b n = Some m <-> to_b m = n.
Proof.
  intros n m.
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
        -- match &n3 with | One | b0 n4 | b1 n4 end.
           ++ simpl in &e.
              leibniz <- (Option.some.injectivity &e) in |- *.
              simpl in |- *.
              quod idem est.
           ++ simpl in &e.
              ex &e quodlibet.
           ++ simpl in &e.
              ex &e quodlibet.
        -- match &n3 with | One | b0 n4 | b1 n4 end.
           ++ simpl in &e.
              leibniz <- (Option.some.injectivity &e) in |- *.
              simpl in |- *.
              quod idem est.
           ++ simpl in &e.
              ex &e quodlibet.
           ++ simpl in &e.
              ex &e quodlibet.
      * match &n2 with | One | b0 n3 | b1 n3 end.
        -- simpl in &e.
           leibniz <- (Option.some.injectivity &e) in |- *.
           simpl in |- *.
           quod idem est.
        -- match &n3 with | One | b0 n4 | b1 n4 end.
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
        -- match &n3 with | One | b0 n4 | b1 n4 end.
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
      * match &n2 with | One | b0 n3 | b1 n3 end.
        -- simpl in &e.
           leibniz <- (Option.some.injectivity &e) in |- *.
           simpl in |- *.
           quod idem est.
        -- match &n3 with | One | b0 n4 | b1 n4 end.
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
    ipso (conversion.bin.retraction &m).
Qed.

(* conversion.bin.injectivity *)
Theorem injectivity
  : forall {m1 : Month} {m2 : Month} . to_b m1 = to_b m2 -> m1 = m2.
Proof.
  intros m1 m2 e.
  congru from_b, &e |- f.
  leibniz (conversion.bin.retraction &m1), (conversion.bin.retraction &m2) in &f.
  ipso (Option.some.injectivity &f).
Qed.

End bin. (* conversion.bin *)

Module bin0. (* conversion.bin0 *)

(* conversion.bin0.retraction *)
Theorem retraction : forall (m : Month) . from_b0 (to_b0 m) = Some m.
Proof.
  intro m.
  match &m with
  | January | February | March | April | May | June
  | July | August | September | October | November | December
  end; simpl in |- *; quod idem est.
Qed.

(* Every [k] that [from_b0] does not map to a month is refused within
 * four bits, so the case analysis on [k] ends there.
 *)
(* conversion.bin0.specification *)
Theorem specification
  : forall (k : Bin0) (m : Month) . from_b0 k = Some m <-> to_b0 m = k.
Proof.
  intros k m.
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
           ++ match &p3 with | One | b0 p4 | b1 p4 end.
              ** simpl in &e.
                 leibniz <- (Option.some.injectivity &e) in |- *.
                 simpl in |- *.
                 quod idem est.
              ** simpl in &e.
                 ex &e quodlibet.
              ** simpl in &e.
                 ex &e quodlibet.
           ++ simpl in &e.
              ex &e quodlibet.
        -- match &p2 with | One | b0 p3 | b1 p3 end.
           ++ simpl in &e.
              leibniz <- (Option.some.injectivity &e) in |- *.
              simpl in |- *.
              quod idem est.
           ++ match &p3 with | One | b0 p4 | b1 p4 end.
              ** simpl in &e.
                 leibniz <- (Option.some.injectivity &e) in |- *.
                 simpl in |- *.
                 quod idem est.
              ** simpl in &e.
                 ex &e quodlibet.
              ** simpl in &e.
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
           ++ match &p3 with | One | b0 p4 | b1 p4 end.
              ** simpl in &e.
                 leibniz <- (Option.some.injectivity &e) in |- *.
                 simpl in |- *.
                 quod idem est.
              ** simpl in &e.
                 ex &e quodlibet.
              ** simpl in &e.
                 ex &e quodlibet.
           ++ simpl in &e.
              ex &e quodlibet.
        -- match &p2 with | One | b0 p3 | b1 p3 end.
           ++ simpl in &e.
              leibniz <- (Option.some.injectivity &e) in |- *.
              simpl in |- *.
              quod idem est.
           ++ match &p3 with | One | b0 p4 | b1 p4 end.
              ** simpl in &e.
                 leibniz <- (Option.some.injectivity &e) in |- *.
                 simpl in |- *.
                 quod idem est.
              ** simpl in &e.
                 ex &e quodlibet.
              ** simpl in &e.
                 ex &e quodlibet.
           ++ simpl in &e.
              ex &e quodlibet.
  - intro e.
    leibniz <- &e in |- *.
    ipso (conversion.bin0.retraction &m).
Qed.

(* conversion.bin0.injectivity *)
Theorem injectivity
  : forall {m1 : Month} {m2 : Month} . to_b0 m1 = to_b0 m2 -> m1 = m2.
Proof.
  intros m1 m2 e.
  congru from_b0, &e |- f.
  leibniz (conversion.bin0.retraction &m1), (conversion.bin0.retraction &m2) in &f.
  ipso (Option.some.injectivity &f).
Qed.

End bin0. (* conversion.bin0 *)

End conversion. (* conversion *)

Module succession. (* succession *)

Module forward. (* succession.forward *)

(* succession.forward.inverse *)
Theorem inverse : forall (m : Month) . prev (next m) = m.
Proof.
  intro m.
  match &m with
  | January | February | March | April | May | June
  | July | August | September | October | November | December
  end; simpl in |- *; quod idem est.
Qed.

End forward. (* succession.forward *)

Module backward. (* succession.backward *)

(* succession.backward.inverse *)
Theorem inverse : forall (m : Month) . next (prev m) = m.
Proof.
  intro m.
  match &m with
  | January | February | March | April | May | June
  | July | August | September | October | November | December
  end; simpl in |- *; quod idem est.
Qed.

End backward. (* succession.backward *)

End succession. (* succession *)

Module order. (* order *)

Module strict. (* order.strict *)

(* order.strict.transitivity *)
Theorem transitivity
  : forall {m1 : Month} {m2 : Month} {m3 : Month} .
      LessThan m1 m2 -> LessThan m2 m3 -> LessThan m1 m3.
Proof.
  intros m1 m2 m3 h1 h2.
  simpl LessThan in &h1, &h2 |- *.
  ipso (Bin.order.strict.transitivity &h1 &h2).
Qed.

End strict. (* order.strict *)

End order. (* order *)

Module comparison. (* comparison *)

(* comparison.specification *)
Theorem specification
  : forall (m1 : Month) (m2 : Month) .
      (compare m1 m2 = Comparison.Lt <-> LessThan m1 m2)
      /\ (compare m1 m2 = Comparison.Eq <-> m1 = m2).
Proof.
  intros m1 m2.
  simpl compare, LessThan in |- *.
  let proof s := Bin.comparison.specification (to_b &m1) (to_b &m2).
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
  : forall (m1 : Month) (m2 : Month) . compare m1 m2 = Comparison.transpose (compare m2 m1).
Proof.
  intros m1 m2.
  simpl compare in |- *.
  ipso (Bin.comparison.antisymmetry (to_b &m1) (to_b &m2)).
Qed.

End comparison. (* comparison *)

Instance comparable
  : Comparable compare LessThan :=
  {| Comparable.transitivity := @order.strict.transitivity
  ; Comparable.specification := comparison.specification
  ; Comparable.antisymmetry := comparison.antisymmetry |}.

End Month. (* Month *)

Abbreviation Month := Month.T.

Existing Instance Month.comparable.
