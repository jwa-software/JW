(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

From JW Require Import Core.All.
From JW Require Import Data.Assert.
From JW Require Import Data.Base.Bool.
From JW Require Import Data.Base.Comparison.
From JW Require Import Data.Calendar.Month.
From JW Require Import Data.Comparable.
From JW Require Import Data.Number.Binary.BinBase.
From JW Require Import Data.Number.Binary.BinWithZero.
From JW Require Import Data.Option.
From JW Require Import Tactics.Equation.
From JW Require Import Tactics.Modus.
From JW Require Import Tactics.Witness.

(* A date of the proleptic Gregorian calendar: the Gregorian leap rule holds
 * for every year, the years count from 1, and day 0 is 0001-01-01.
 *)
Module Date. (* Date *)

(* Numbers are written in decimal: a bare literal is a [BinBase], which
 * stands for a [BinWithZero] wherever one is expected, so only zero carries
 * its key.
 *)
Local Open Scope jw_bin_with_zero_scope.
Local Open Scope jw_bin_base_decimal_scope.

Abbreviation Year := BinBase (only parsing).
Abbreviation Day := BinBase (only parsing).

(* The ctor takes only a day that its month has, so the checks it asserts
 * come first.
 *)

(* A year divisible by 4 is a leap year, except one divisible by 100 and not
 * by 400.
 *)
(* [BinBase -> Bool] *)
Definition is_leap := fun (y : Year) .
  (BinWithZero.eq (y %. 4) 0%bin_with_zero
    && (! BinWithZero.eq (y %. 100) 0%bin_with_zero
          || BinWithZero.eq (y %. 400) 0%bin_with_zero))%bool.

(* [BinBase -> Month -> BinBase] *)
Definition days_in_month := fun (y : Year) (m : Month) .
  match m with
  | Month.January   => 31
  | Month.February  =>
      match is_leap y with
      | true  => 29
      | false => 28
      end
  | Month.March     => 31
  | Month.April     => 30
  | Month.May       => 31
  | Month.June      => 30
  | Month.July      => 31
  | Month.August    => 31
  | Month.September => 30
  | Month.October   => 31
  | Month.November  => 30
  | Month.December  => 31
  end.

(* A day is a BinBase which is never 0, so the only check is the length of its month. *)
(* [BinBase -> Month -> BinBase -> Bool] *)
Definition is_valid := fun (y : Year) (m : Month) (d : Day) .
  Comparable.le BinBase.compare d (days_in_month y m).

(* The year, the month and the day of the month, with the proof that the
 * month has that day, so no other value can be built.
 *)
Inductive T : Type :=
  | introduction
    : forall (y : Year) (m : Month) (d : Day) . Assert (is_valid y m d) -> T.

Abbreviation Date := T.

(* [Date -> BinBase] *)
Definition year := fun (x : Date) .
  match x with
  | Date.introduction y _ _ _ => y
  end.

(* [Date -> Month] *)
Definition month := fun (x : Date) .
  match x with
  | Date.introduction _ m _ _ => m
  end.

(* [Date -> BinBase] *)
Definition day := fun (x : Date) .
  match x with
  | Date.introduction _ _ d _ => d
  end.

(* The date, [None] when its month has no such day. *)
(* [BinBase -> Month -> BinBase -> Option Date] *)
Definition make := fun (y : Year) (m : Month) (d : Day) .
  Assert.guard (is_valid y m d) (Date.introduction y m d).

(* [BinBase -> BinBase] *)
Definition days_in_year := fun (y : Year) .
  match is_leap y with
  | true  => 366
  | false => 365
  end.

(* The lengths of the periods the leap rule repeats over. Each period's leap
 * year is its last year, so a period that is not complete has no leap day.
 *)
(* [BinWithZero] *)
Definition days_in_common_year : BinWithZero := 365.

(* A quadrennium, four years: three common years and a leap year. *)
(* [BinWithZero] *)
Definition days_in_quadrennium : BinWithZero :=
  (3 * days_in_common_year) + (days_in_common_year + 1).

(* A century, 100 years: 25 quadrennia, but the century year is not leap, so
 * the last quadrennium has four common years.
 *)
(* [BinWithZero] *)
Definition days_in_century : BinWithZero :=
  (24 * days_in_quadrennium) + (4 * days_in_common_year).

(* A quadricentennium, 400 years: four centuries, and the last year of the
 * fourth is leap after all.
 *)
(* [BinWithZero] *)
Definition days_in_quadricentennium : BinWithZero := (4 * days_in_century) + 1.

(* The years before [y], the first year being 1. *)
(* [BinBase -> BinWithZero] *)
Definition years_before := fun (y : Year) . BinWithZero.saturating_sub y 1.

(* The days before January 1 of [y]: the years before [y] taken apart into
 * whole quadricentennia, then whole centuries, then whole quadrennia, then
 * single years.
 *)
(* [BinBase -> BinWithZero] *)
Definition days_before_year := fun (y : Year) .
  let n := years_before y in
  let in_quadricentennium := n %. 400 in
  let in_century := in_quadricentennium %. 100 in
  (days_in_quadricentennium * (n /. 400))
    + (days_in_century * (in_quadricentennium /. 100))
    + (days_in_quadrennium * (in_century /. 4))
    + (days_in_common_year * (in_century %. 4)).

(* The days of [y] before day 1 of [m], each month's count the one before it
 * plus the length of the month before it.
 *)
(* [BinBase -> Month -> BinWithZero] *)
Definition days_before_month := fun (y : Year) (m : Month) .
  let january   := 0%bin_with_zero in
  let february  := january + days_in_month y Month.January in
  let march     := february + days_in_month y Month.February in
  let april     := march + days_in_month y Month.March in
  let may       := april + days_in_month y Month.April in
  let june      := may + days_in_month y Month.May in
  let july      := june + days_in_month y Month.June in
  let august    := july + days_in_month y Month.July in
  let september := august + days_in_month y Month.August in
  let october   := september + days_in_month y Month.September in
  let november  := october + days_in_month y Month.October in
  let december  := november + days_in_month y Month.November in
  match m with
  | Month.January   => january
  | Month.February  => february
  | Month.March     => march
  | Month.April     => april
  | Month.May       => may
  | Month.June      => june
  | Month.July      => july
  | Month.August    => august
  | Month.September => september
  | Month.October   => october
  | Month.November  => november
  | Month.December  => december
  end.

(* The day's place in its year, January 1 being 1. *)
(* [Date -> BinWithZero] *)
Definition day_of_year := fun (x : Date) .
  days_before_month (year x) (month x) + day x.

(* The days from 0001-01-01 to the date, 0001-01-01 itself being 0. *)
(* [Date -> BinWithZero] *)
Definition day_number := fun (x : Date) .
  days_before_year (year x)
    + days_before_month (year x) (month x)
    + BinWithZero.saturating_sub (day x) 1.

(* The order of time: by year, then by month, then by day. *)
(* [Date -> Date -> Comparison] *)
Definition compare := fun (x1 : Date) (x2 : Date) .
  match BinBase.compare (year x1) (year x2) with
  | Comparison.Lt => Comparison.Lt
  | Comparison.Eq =>
      match Month.compare (month x1) (month x2) with
      | Comparison.Lt => Comparison.Lt
      | Comparison.Eq => BinBase.compare (day x1) (day x2)
      | Comparison.Gt => Comparison.Gt
      end
  | Comparison.Gt => Comparison.Gt
  end.

Module leap. (* leap *)

(* The statement adds years, so [+] is read as [BinBase]'s. *)
Local Open Scope jw_bin_base_scope.
Local Open Scope jw_bin_base_decimal_scope.

(* leap.periodicity *)
Theorem periodicity : forall (y : Year) . is_leap (y + 400) = is_leap y.
Proof.
  intro y.
  lemma four : (y + 400) %. 4 = y %. 4.
  {
    lemma zero : 400 %. 4 = 0%bin_with_zero.
    {
      simpl BinWithZero.modulo in |- *.
      simpl in |- *.
      quod idem est.
    }
    ipso (BinWithZero.modulo.sum.right.invariance y 400 4 &zero).
  }
  lemma hundred : (y + 400) %. 100 = y %. 100.
  {
    lemma zero : 400 %. 100 = 0%bin_with_zero.
    {
      simpl BinWithZero.modulo in |- *.
      simpl in |- *.
      quod idem est.
    }
    ipso (BinWithZero.modulo.sum.right.invariance y 400 100 &zero).
  }
  lemma four_hundred : (y + 400) %. 400 = y %. 400.
  {
    lemma zero : 400 %. 400 = 0%bin_with_zero.
    {
      simpl BinWithZero.modulo in |- *.
      simpl in |- *.
      quod idem est.
    }
    ipso (BinWithZero.modulo.sum.right.invariance y 400 400 &zero).
  }
  simpl is_leap in |- *.
  leibniz &four, &hundred, &four_hundred in |- *.
  quod idem est.
Qed.

End leap. (* leap *)

Module month. (* month *)

Module length. (* month.length *)

(* The statement compares days of a month, so [<=] is read as [BinBase]'s. *)
Local Open Scope jw_bin_base_scope.
Local Open Scope jw_bin_base_decimal_scope.

(* month.length.boundedness *)
Theorem boundedness
  : forall (y : Year) (m : Month) . 28 <= days_in_month y m /\ days_in_month y m <= 31.
Proof.
  intros y m.
  lemma lower : Comparable.le BinBase.compare 28 (days_in_month y m) = true.
  {
    simpl days_in_month, Comparable.le, BinBase.compare in |- *.
    match (is_leap &y) with | | end;
      match &m with
      | January | February | March | April | May | June
      | July | August | September | October | November | December
      end; simpl in |- *; quod idem est.
  }
  lemma upper : Comparable.le BinBase.compare (days_in_month y m) 31 = true.
  {
    simpl days_in_month, Comparable.le, BinBase.compare in |- *.
    match (is_leap &y) with | | end;
      match &m with
      | January | February | March | April | May | June
      | July | August | September | October | November | December
      end; simpl in |- *; quod idem est.
  }
  divide et impera.
  - ipso (modus aequans (Comparable.order.reflection 28 (days_in_month &y &m)), &lower).
  - ipso (modus aequans (Comparable.order.reflection (days_in_month &y &m) 31), &upper).
Qed.

End length. (* month.length *)

(* Each month's count is defined as the one before it plus the length of the
 * month before it, so each case reduces to the same term on both sides.
 *)
(* month.succession *)
Theorem succession
  : forall (y : Year) (m : Month) .
      ~ (m = Month.December)
      -> days_before_month y (Month.next m) = days_before_month y m + days_in_month y m.
Proof.
  intros y m h.
  match &m with
  | January | February | March | April | May | June
  | July | August | September | October | November | December
  end.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    quod idem est.
  - ex (&h (refl Month.December)) quodlibet.
Qed.

(* month.completion *)
Theorem completion
  : forall (y : Year) . days_before_month y Month.December + 31 = days_in_year y.
Proof.
  intro y.
  simpl days_before_month, days_in_month, days_in_year in |- *.
  match (is_leap &y) with | | end;
    simpl in |- *; simpl BinBase.add in |- *; simpl in |- *; quod idem est.
Qed.

(* month.boundedness *)
Theorem boundedness
  : forall (y : Year) (m : Month) .
      days_before_month y m + days_in_month y m <= days_in_year y.
Proof.
  intros y m.
  lemma facto
    : Comparable.le BinWithZero.compare
        (days_before_month y m + days_in_month y m) (days_in_year y)
      = true.
  {
    simpl days_before_month, days_in_month, days_in_year, Comparable.le, BinWithZero.compare
      in |- *.
    match (is_leap &y) with | | end;
      match &m with
      | January | February | March | April | May | June
      | July | August | September | October | November | December
      end; simpl in |- *; quod idem est.
  }
  ipso (modus aequans
          (Comparable.order.reflection
             (days_before_month &y &m + days_in_month &y &m) (days_in_year &y)),
          &facto).
Qed.

End month. (* month *)

Module year. (* year *)

Module length. (* year.length *)

(* year.length.dichotomy *)
Theorem dichotomy : forall (y : Year) . days_in_year y = 365 \/ days_in_year y = 366.
Proof.
  intro y.
  simpl days_in_year in |- *.
  match (is_leap &y) with | | end.
  - ipso (disjoin _, (refl 366)).
  - ipso (disjoin (refl 365), _).
Qed.

(* year.length.specification *)
Theorem specification : forall (y : Year) . days_in_year y = 366 <-> is_leap y = true.
Proof.
  intro y.
  simpl days_in_year in |- *.
  match (is_leap &y) with | | end.
  - divide et impera.
    + intro e.
      quod idem est.
    + intro e.
      quod idem est.
  - divide et impera.
    + intro e.
      ex &e quodlibet.
    + intro e.
      ex &e quodlibet.
Qed.

End length. (* year.length *)

End year. (* year *)

Module ordinal. (* ordinal *)

(* ordinal.positivity *)
Theorem positivity : forall (x : Date) . 0%bin_with_zero < day_of_year x.
Proof.
  intro x.
  simpl day_of_year, BinWithZero.LessThan in |- *.
  match (days_before_month (year &x) (month &x)) with | | p end.
  - exists (day &x).
    simpl in |- *.
    quod idem est.
  - exists (&p + day &x)%bin_base.
    simpl in |- *.
    quod idem est.
Qed.

(* ordinal.boundedness *)
Theorem boundedness : forall (x : Date) . day_of_year x <= days_in_year (year x).
Proof.
  intro x.
  match &x with | introduction y m d a end.
  simpl day_of_year, year, month, day in |- *.
  simpl is_valid in &a.
  let proof t := modus aequans (Assert.specification _), &a.
  let proof b := modus aequans (Comparable.order.reflection &d (days_in_month &y &m)), &t.
  lemma widened : (d : BinWithZero) <= days_in_month y m.
  {
    match &b with | e | s end.
    - ipso (disjoin (congru BinWithZero.Positive, &e), _).
    - match &s with | k e end.
      lemma facto : (d : BinWithZero) < days_in_month y m.
      {
        simpl BinWithZero.LessThan in |- *.
        exists &k.
        ipso (congru BinWithZero.Positive, &e).
      }
      ipso (disjoin _, &facto).
  }
  lemma shifted
    : days_before_month y m + d <= days_before_month y m + days_in_month y m.
  {
    match &widened with | e | s end.
    - leibniz &e in |- *.
      ipso (disjoin (refl (days_before_month &y &m + days_in_month &y &m)), _).
    - ipso (disjoin _,
              (BinWithZero.addition.order.strict.monotonicity
                 (days_before_month &y &m) d (days_before_month &y &m) (days_in_month &y &m)
                 (disjoin (refl (days_before_month &y &m)), _) &s)).
  }
  ipso (@Comparable.order.transitivity _ BinWithZero.compare BinWithZero.LessThan _
          (days_before_month &y &m + d)
          (days_before_month &y &m + days_in_month &y &m)
          (days_in_year &y)
          &shifted (month.boundedness &y &m)).
Qed.

End ordinal. (* ordinal *)

End Date. (* Date *)

Abbreviation Date := Date.T.
