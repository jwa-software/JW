(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

From JW Require Import Core.All.
From JW Require Import Data.Base.Comparison.
From JW Require Import Data.Comparable.
From JW Require Import Data.Number.Binary.BinBase.
From JW Require Import Data.Option.
From JW Require Import Tactics.Equation.
From JW Require Import Tactics.Modus.

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

(* The month's place in the year, [January] being 1; a [BinBase] literal is
 * written in binary digits, so [1100%bin_base] is 12.
 *)
(* [Month -> BinBase] *)
Definition to_number := fun (m : Month) .
  match m with
  | January   =>    1%bin_base
  | February  =>   10%bin_base
  | March     =>   11%bin_base
  | April     =>  100%bin_base
  | May       =>  101%bin_base
  | June      =>  110%bin_base
  | July      =>  111%bin_base
  | August    => 1000%bin_base
  | September => 1001%bin_base
  | October   => 1010%bin_base
  | November  => 1011%bin_base
  | December  => 1100%bin_base
  end.

(* The month at a place in the year, [None] past 12. *)
(* [BinBase -> Option Month] *)
Definition from_number := fun (n : BinBase) .
  match n with
  |    1%bin_base => Some January
  |   10%bin_base => Some February
  |   11%bin_base => Some March
  |  100%bin_base => Some April
  |  101%bin_base => Some May
  |  110%bin_base => Some June
  |  111%bin_base => Some July
  | 1000%bin_base => Some August
  | 1001%bin_base => Some September
  | 1010%bin_base => Some October
  | 1011%bin_base => Some November
  | 1100%bin_base => Some December
  | _             => None
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
  BinBase.compare (to_number m1) (to_number m2).

(* [Month -> Month -> Prop] *)
Definition LessThan := fun (m1 : Month) (m2 : Month) .
  (to_number m1 < to_number m2)%bin_base.

Module conversion. (* conversion *)

(* conversion.retraction *)
Theorem retraction : forall (m : Month) . from_number (to_number m) = Some m.
Proof.
  intro m.
  match &m with
  | January | February | March | April | May | June
  | July | August | September | October | November | December
  end; simpl in |- *; quod idem est.
Qed.

(* Every [n] that [from_number] does not map to a month is refused within
 * four bits, so the case analysis on [n] ends there.
 *)
(* conversion.specification *)
Theorem specification
  : forall (n : BinBase) (m : Month) . from_number n = Some m <-> to_number m = n.
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
    ipso (conversion.retraction &m).
Qed.

(* conversion.injectivity *)
Theorem injectivity
  : forall {m1 : Month} {m2 : Month} . to_number m1 = to_number m2 -> m1 = m2.
Proof.
  intros m1 m2 e.
  congru from_number, &e |- f.
  leibniz (conversion.retraction &m1), (conversion.retraction &m2) in &f.
  ipso (Option.some.injectivity &f).
Qed.

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
  ipso (BinBase.order.strict.transitivity &h1 &h2).
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
  let proof s := BinBase.comparison.specification (to_number &m1) (to_number &m2).
  match &s with | strict equality end.
  divide et impera.
  - ipso &strict.
  - divide et impera.
    + intro c.
      ipso (conversion.injectivity (modus aequans &equality, &c)).
    + intro e.
      ipso (modus aequans &equality, (congru to_number, &e)).
Qed.

(* comparison.antisymmetry *)
Theorem antisymmetry
  : forall (m1 : Month) (m2 : Month) . compare m1 m2 = Comparison.transpose (compare m2 m1).
Proof.
  intros m1 m2.
  simpl compare in |- *.
  ipso (BinBase.comparison.antisymmetry (to_number &m1) (to_number &m2)).
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
