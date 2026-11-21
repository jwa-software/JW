(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

From JW Require Import Core.All.
From JW Require Import Data.Assert.
From JW Require Import Data.Base.Bool.
From JW Require Import Data.Base.Comparison.
From JW Require Import Data.Calendar.Gregorian.Date.
From JW Require Import Data.Calendar.Month.
From JW Require Import Data.Calendar.Weekday.
From JW Require Import Data.Comparable.
From JW Require Import Data.Number.Binary.Bin.
From JW Require Import Data.Number.Binary.Bin0.
From JW Require Import Data.Option.
From JW Require Import Tactics.Equation.
From JW Require Import Tactics.Modus.
From JW Require Import Tactics.Witness.

(* A date of the ISO 8601 week calendar: an ISO year, a week of it and a day
 * of that week. Week 1 is the week, Monday first, that holds January 4.
 *)
Module IsoWeekDate. (* IsoWeekDate *)

(* Numbers are written in decimal, as in [Date]. *)
Local Open Scope jw_bin0_scope.
Local Open Scope jw_bin_decimal_scope.

Abbreviation Year := Bin (only parsing).
Abbreviation Week := Bin (only parsing).
Abbreviation Days := Bin0 (only parsing).

(* The ctor takes only a week that its year has, so the checks it asserts
 * come first.
 *)

(* January 4 of [y]: every month has a day 4, so its proof is [I]. *)
(* [Year -> Date] *)
Definition january_4th := fun (y : Year) . Date.introduction y Month.January 4 I.

(* The day number of the Monday of week 1 of ISO year [y]: January 4 less its
 * place in its week.
 *)
(* [Year -> Days] *)
Definition week_one_start := fun (y : Year) .
  let n := Date.day_number (january_4th y) in
  Bin0.saturating_sub n (Weekday.to_b0 (Date.weekday_of_day_number n)).

(* The weeks from the start of week 1 of [y] to that of [y + 1]. *)
(* [Year -> Bin0] *)
Definition weeks_in_year := fun (y : Year) .
  Bin0.saturating_sub (week_one_start (y + 1)%b) (week_one_start y) /. Weekday.days_in_week.

(* A week is a [Bin], never 0, so the only check is the number of weeks of
 * its year.
 *)
(* [Year -> Week -> Bool] *)
Definition is_valid := fun (y : Year) (w : Week) . Bin0.le w (weeks_in_year y).

(* The ISO year, the week of that year and the day of that week, with the
 * proof that the year has that week.
 *)
Inductive T : Type :=
  | introduction
    : forall (y : Year) (w : Week) (d : Weekday) . Assert (is_valid y w) -> T.

Abbreviation IsoWeekDate := T.

(* [IsoWeekDate -> Year] *)
Definition year := fun (x : IsoWeekDate) .
  match x with
  | IsoWeekDate.introduction y _ _ _ => y
  end.

(* [IsoWeekDate -> Week] *)
Definition week := fun (x : IsoWeekDate) .
  match x with
  | IsoWeekDate.introduction _ w _ _ => w
  end.

(* [IsoWeekDate -> Weekday] *)
Definition weekday := fun (x : IsoWeekDate) .
  match x with
  | IsoWeekDate.introduction _ _ d _ => d
  end.

(* The date of the day: the start of week 1, the whole weeks before the
 * week, and the day's place in its week.
 *)
(* [IsoWeekDate -> Date] *)
Definition to_date := fun (x : IsoWeekDate) .
  Date.from_day_number
    (week_one_start (year x) + Bin0.saturating_sub (week x) 1 * Weekday.days_in_week
     + Weekday.to_b0 (weekday x)).

(* Two proofs of one validity are equal, so an ISO week date is its year,
 * week and weekday.
 *)
(* extensionality *)
Theorem extensionality
  : forall (x1 : IsoWeekDate) (x2 : IsoWeekDate) .
      year x1 = year x2 -> week x1 = week x2 -> weekday x1 = weekday x2 -> x1 = x2.
Proof.
  intros x1 x2.
  match &x1 with | introduction y1 w1 d1 a1 end.
  match &x2 with | introduction y2 w2 d2 a2 end.
  simpl year, week, weekday in |- *.
  intros ey ew ed.
  extro &a2.
  match &ey with | end.
  match &ew with | end.
  match &ed with | end.
  intro a2.
  leibniz (Assert.uniqueness _ &a1 &a2) in |- *.
  quod idem est.
Qed.

Module january. (* january *)

(* january.decomposition *)
Theorem decomposition
  : forall (y : Year) . Date.day_number (january_4th y) = Date.days_before_year y + 3.
Proof.
  intro y.
  lemma facto
    : Date.days_before_year y + Date.days_before_month y Month.January
        + Bin0.saturating_sub 4 1
      = Date.days_before_year y + 3.
  {
    lemma start : Date.days_before_month y Month.January = 0%b0.
    {
      ipso (Identity.reflexivity _).
    }
    leibniz &start in |- *.
    match (Bin0.addition.identity (Date.days_before_year &y)) with | _ vanishing end.
    leibniz &vanishing in |- *.
    ipso (Identity.reflexivity (Date.days_before_year &y + 3)).
  }
  ipso facto.
Qed.

(* January 4 of the next year is a year's length later. *)
(* january.succession *)
Theorem succession
  : forall (y : Year) .
      Date.day_number (january_4th (y + 1)%b) = Date.day_number (january_4th y) + Date.days_in_year y.
Proof.
  intro y.
  leibniz
    (january.decomposition (y + 1)%b),
    (january.decomposition &y),
    (Date.year.succession &y)
    in |- *.
  leibniz
    (Bin0.addition.associativity (Date.days_before_year &y) (Date.days_in_year &y) 3),
    (Bin0.addition.commutativity (Date.days_in_year &y) 3),
    <- (Bin0.addition.associativity (Date.days_before_year &y) 3 (Date.days_in_year &y))
    in |- *.
  quod idem est.
Qed.

(* January 4 is three days after January 1, so its place in its week is that
 * of January 1 moved on three times.
 *)
(* january.weekday *)
Theorem weekday
  : forall (y : Year) .
      Date.day_number (january_4th y) %. Weekday.days_in_week
      = Weekday.to_b0
          (Weekday.next (Weekday.next (Weekday.next
             (Date.weekday_of_day_number (Date.days_before_year y))))).
Proof.
  intro y.
  lemma steps : Date.day_number (january_4th y) = Date.days_before_year y + 1 + 1 + 1.
  {
    leibniz (january.decomposition &y) in |- *.
    leibniz
      (Bin0.addition.associativity (Date.days_before_year &y + 1) 1 1),
      (Bin0.addition.associativity (Date.days_before_year &y) 1 (1 + 1))
      in |- *.
    ipso (Identity.reflexivity (Date.days_before_year &y + 3)).
  }
  leibniz <- (Date.weekday.specification (Date.day_number (january_4th &y))) in |- *.
  leibniz &steps in |- *.
  leibniz
    (Date.weekday.succession (Date.days_before_year &y + 1 + 1)),
    (Date.weekday.succession (Date.days_before_year &y + 1)),
    (Date.weekday.succession (Date.days_before_year &y))
    in |- *.
  quod idem est.
Qed.

End january. (* january *)

Module start. (* start *)

(* The start of week 1 is January 4 with its remainder by 7 taken away, so it
 * is the whole weeks of January 4.
 *)
(* start.decomposition *)
Theorem decomposition
  : forall (y : Year) .
      week_one_start y
      = (Date.day_number (january_4th y) /. Weekday.days_in_week) * Weekday.days_in_week.
Proof.
  intro y.
  lemma facto
    : Bin0.saturating_sub (Date.day_number (january_4th y))
        (Weekday.to_b0 (Date.weekday_of_day_number (Date.day_number (january_4th y))))
      = (Date.day_number (january_4th y) /. Weekday.days_in_week) * Weekday.days_in_week.
  {
    leibniz (Date.weekday.specification (Date.day_number (january_4th &y))) in |- *.
    match (Bin0.division.specification (Date.day_number (january_4th &y)) Weekday.days_in_week)
      with | e _ end.
    let proof f :=
      Bin0.subtraction.saturating.inversion.addition
        ((Date.day_number (january_4th &y) /. Weekday.days_in_week) * Weekday.days_in_week)
        (Date.day_number (january_4th &y) %. Weekday.days_in_week).
    leibniz &e in &f.
    ipso &f.
  }
  ipso facto.
Qed.

(* start.weekday *)
Theorem weekday : forall (y : Year) . Date.weekday_of_day_number (week_one_start y) = Weekday.Monday.
Proof.
  intro y.
  leibniz (start.decomposition &y) in |- *.
  let q := Date.day_number (january_4th y) /. Weekday.days_in_week in |- *.
  lemma positive : 0%b0 < Weekday.days_in_week.
  {
    match (Bin0.comparison.specification 0%b0 Weekday.days_in_week) with | strict _ end.
    ipso (modus aequans &strict, (Identity.reflexivity Comparison.Lt)).
  }
  match (Bin0.addition.identity (&q * Weekday.days_in_week)) with | _ vanishing end.
  match (Bin0.division.uniqueness (&q * Weekday.days_in_week) Weekday.days_in_week &q 0%b0
           (conjoin &vanishing, &positive))
    with | _ remainder end.
  simpl Date.weekday_of_day_number in |- *.
  leibniz &remainder in |- *.
  ipso (Identity.reflexivity Weekday.Monday).
Qed.

(* January 4 lies in the week that week 1 starts. *)
(* start.boundedness *)
Theorem boundedness
  : forall (y : Year) .
      week_one_start y <= Date.day_number (january_4th y)
      /\ Date.day_number (january_4th y) < week_one_start y + Weekday.days_in_week.
Proof.
  intro y.
  leibniz (start.decomposition &y) in |- *.
  match (Bin0.division.specification (Date.day_number (january_4th &y)) Weekday.days_in_week)
    with | e below end.
  let q := Date.day_number (january_4th y) /. Weekday.days_in_week in &e |- *.
  let r := Date.day_number (january_4th y) %. Weekday.days_in_week in &e, &below.
  leibniz <- &e in |- *.
  lemma reflexive : &q * Weekday.days_in_week <= &q * Weekday.days_in_week.
  {
    ipso (disjoin (Identity.reflexivity (&q * Weekday.days_in_week)), _).
  }
  divide et impera.
  - leibniz (Bin0.addition.commutativity (&q * Weekday.days_in_week) &r) in |- *.
    ipso (Bin0.addition.right.order.extensivity &r (&q * Weekday.days_in_week)).
  - ipso (Bin0.addition.order.strict.monotonicity
            (&q * Weekday.days_in_week) &r (&q * Weekday.days_in_week) Weekday.days_in_week
            &reflexive &below).
Qed.

End start. (* start *)

Module year. (* year *)

Module length. (* year.length *)

(* January 4 of the next year is a year's length later; a remainder [r] of
 * January 4 by 7 and a length [l] whose sum is [w] weeks and [s] days, [s]
 * under 7, put the next January 4 [w] whole weeks further.
 *)
(* year.length.quotient *)
Lemma quotient
  : forall (y : Year) (w : Bin0) (s : Bin0) {r : Bin0} {l : Bin} .
      Date.day_number (january_4th y) %. Weekday.days_in_week = r
      -> Date.days_in_year y = l
      -> w * Weekday.days_in_week + s = r + l
      -> s < Weekday.days_in_week
      -> Date.day_number (january_4th (y + 1)%b) /. Weekday.days_in_week
         = Date.day_number (january_4th y) /. Weekday.days_in_week + w.
Proof.
  intros y w s r l remainder length counted below.
  match (Bin0.division.specification (Date.day_number (january_4th &y)) Weekday.days_in_week)
    with | e _ end.
  leibniz &remainder in &e.
  let q := Date.day_number (january_4th y) /. Weekday.days_in_week in &e |- *.
  lemma whole
    : (&q + w) * Weekday.days_in_week + s = Date.day_number (january_4th (y + 1)%b).
  {
    leibniz (january.succession &y), &length in |- *.
    leibniz <- &e in |- *.
    match (Bin0.multiplication.distributivity.over.addition Weekday.days_in_week &q &w)
      with | _ distributed end.
    leibniz &distributed in |- *.
    leibniz
      (Bin0.addition.associativity (&q * Weekday.days_in_week) (&w * Weekday.days_in_week) &s),
      (Bin0.addition.associativity (&q * Weekday.days_in_week) &r l)
      in |- *.
    leibniz &counted in |- *.
    quod idem est.
  }
  match (Bin0.division.uniqueness
           (Date.day_number (january_4th (&y + 1)%b)) Weekday.days_in_week (&q + &w) &s
           (conjoin &whole, &below))
    with | quotient _ end.
  ipso &quotient.
Qed.

(* The starts of week 1 are the whole weeks of the two January 4ths, so
 * their distance is the difference of those weeks.
 *)
(* year.length.count *)
Lemma count
  : forall (y : Year) (w : Bin0) .
      Date.day_number (january_4th (y + 1)%b) /. Weekday.days_in_week
      = Date.day_number (january_4th y) /. Weekday.days_in_week + w
      -> weeks_in_year y = w.
Proof.
  intros y w h.
  lemma positive : 0%b0 < Weekday.days_in_week.
  {
    match (Bin0.comparison.specification 0%b0 Weekday.days_in_week) with | strict _ end.
    ipso (modus aequans &strict, (Identity.reflexivity Comparison.Lt)).
  }
  simpl weeks_in_year in |- *.
  leibniz (start.decomposition (&y + 1)%b), (start.decomposition &y), &h in |- *.
  let q := Date.day_number (january_4th y) /. Weekday.days_in_week in |- *.
  match (Bin0.multiplication.distributivity.over.addition Weekday.days_in_week &q &w)
    with | _ distributed end.
  leibniz
    &distributed,
    (Bin0.addition.commutativity (&q * Weekday.days_in_week) (&w * Weekday.days_in_week)),
    (Bin0.subtraction.saturating.inversion.addition
       (&w * Weekday.days_in_week) (&q * Weekday.days_in_week))
    in |- *.
  match (Bin0.addition.identity (&w * Weekday.days_in_week)) with | _ vanishing end.
  match (Bin0.division.uniqueness (&w * Weekday.days_in_week) Weekday.days_in_week &w 0%b0
           (conjoin &vanishing, &positive))
    with | quotient _ end.
  ipso &quotient.
Qed.

(* January 1 has one of seven weekdays and the year one of two lengths;
 * each of the fourteen cases puts the next January 4 52 or 53 whole weeks
 * further.
 *)
(* year.length.tabulation *)
Lemma tabulation
  : forall (y : Year) .
      Date.day_number (january_4th (y + 1)%b) /. Weekday.days_in_week
      = Date.day_number (january_4th y) /. Weekday.days_in_week + 52
      \/ Date.day_number (january_4th (y + 1)%b) /. Weekday.days_in_week
         = Date.day_number (january_4th y) /. Weekday.days_in_week + 53.
Proof.
  intro y.
  lemma below
    : forall (s : Bin0) . Bin0.compare s Weekday.days_in_week = Comparison.Lt -> s < Weekday.days_in_week.
  {
    intros s c.
    match (Bin0.comparison.specification &s Weekday.days_in_week) with | strict _ end.
    ipso (modus aequans &strict, &c).
  }
  let proof weekday := january.weekday &y.
  extro &weekday.
  match (Date.year.length.dichotomy &y) with | common | leap end.
  -
    match (Date.weekday_of_day_number (Date.days_before_year &y)) with
    | Monday | Tuesday | Wednesday | Thursday | Friday | Saturday | Sunday
    end; intro weekday.
    + ipso (disjoin (quotient &y 52 4 &weekday &common (Identity.reflexivity _)
                       (&below 4 (Identity.reflexivity _))), _).
    + ipso (disjoin (quotient &y 52 5 &weekday &common (Identity.reflexivity _)
                       (&below 5 (Identity.reflexivity _))), _).
    + ipso (disjoin (quotient &y 52 6 &weekday &common (Identity.reflexivity _)
                       (&below 6 (Identity.reflexivity _))), _).
    + ipso (disjoin _, (quotient &y 53 0%b0 &weekday &common (Identity.reflexivity _)
                          (&below 0%b0 (Identity.reflexivity _)))).
    + ipso (disjoin (quotient &y 52 1 &weekday &common (Identity.reflexivity _)
                       (&below 1 (Identity.reflexivity _))), _).
    + ipso (disjoin (quotient &y 52 2 &weekday &common (Identity.reflexivity _)
                       (&below 2 (Identity.reflexivity _))), _).
    + ipso (disjoin (quotient &y 52 3 &weekday &common (Identity.reflexivity _)
                       (&below 3 (Identity.reflexivity _))), _).
  -
    match (Date.weekday_of_day_number (Date.days_before_year &y)) with
    | Monday | Tuesday | Wednesday | Thursday | Friday | Saturday | Sunday
    end; intro weekday.
    + ipso (disjoin (quotient &y 52 5 &weekday &leap (Identity.reflexivity _)
                       (&below 5 (Identity.reflexivity _))), _).
    + ipso (disjoin (quotient &y 52 6 &weekday &leap (Identity.reflexivity _)
                       (&below 6 (Identity.reflexivity _))), _).
    + ipso (disjoin _, (quotient &y 53 0%b0 &weekday &leap (Identity.reflexivity _)
                          (&below 0%b0 (Identity.reflexivity _)))).
    + ipso (disjoin _, (quotient &y 53 1 &weekday &leap (Identity.reflexivity _)
                          (&below 1 (Identity.reflexivity _)))).
    + ipso (disjoin (quotient &y 52 2 &weekday &leap (Identity.reflexivity _)
                       (&below 2 (Identity.reflexivity _))), _).
    + ipso (disjoin (quotient &y 52 3 &weekday &leap (Identity.reflexivity _)
                       (&below 3 (Identity.reflexivity _))), _).
    + ipso (disjoin (quotient &y 52 4 &weekday &leap (Identity.reflexivity _)
                       (&below 4 (Identity.reflexivity _))), _).
Qed.

(* year.length.dichotomy *)
Theorem dichotomy : forall (y : Year) . weeks_in_year y = 52 \/ weeks_in_year y = 53.
Proof.
  intro y.
  match (year.length.tabulation &y) with | short | long end.
  - ipso (disjoin (year.length.count &y 52 &short), _).
  - ipso (disjoin _, (year.length.count &y 53 &long)).
Qed.

(* A year of 53 weeks is one whose January 1 is a Thursday, or a leap year
 * whose January 1 is a Wednesday: each of the fourteen cases of
 * [tabulation] is checked.
 *)
(* year.length.specification *)
Theorem specification
  : forall (y : Year) .
      weeks_in_year y = 53
      <-> (Date.weekday_of_day_number (Date.days_before_year y) = Weekday.Thursday
           \/ (Date.is_leap y = true
               /\ Date.weekday_of_day_number (Date.days_before_year y) = Weekday.Wednesday)).
Proof.
  intro y.
  lemma below
    : forall (s : Bin0) . Bin0.compare s Weekday.days_in_week = Comparison.Lt -> s < Weekday.days_in_week.
  {
    intros s c.
    match (Bin0.comparison.specification &s Weekday.days_in_week) with | strict _ end.
    ipso (modus aequans &strict, &c).
  }
  lemma distinct : ~ ((52 : Bin0) = 53).
  {
    simpl (~ _) in |- *.
    intro e.
    let proof f := Option.some.injectivity (congru Bin0.to_b, &e).
    ex &f quodlibet.
  }
  let proof weekday := january.weekday &y.
  extro &weekday.
  match (Date.year.length.dichotomy &y) with | common | leap end.
  -
    lemma ordinary : ~ (Date.is_leap y = true).
    {
      simpl (~ _) in |- *.
      intro l.
      let proof f := modus aequans (Date.year.length.specification &y), &l.
      leibniz &common in &f.
      ex &f quodlibet.
    }
    match (Date.weekday_of_day_number (Date.days_before_year &y)) with
    | Monday | Tuesday | Wednesday | Thursday | Friday | Saturday | Sunday
    end; intro weekday.
    + let proof c := year.length.count &y 52
                       (quotient &y 52 4 &weekday &common (Identity.reflexivity _)
                          (&below 4 (Identity.reflexivity _))).
      divide et impera.
      * intro h.
        leibniz &c in &h.
        ex (&distinct &h) quodlibet.
      * intro h.
        match &h with | thursday | wednesday end.
        -- ex &thursday quodlibet.
        -- match &wednesday with | _ e end.
           ex &e quodlibet.
    + let proof c := year.length.count &y 52
                       (quotient &y 52 5 &weekday &common (Identity.reflexivity _)
                          (&below 5 (Identity.reflexivity _))).
      divide et impera.
      * intro h.
        leibniz &c in &h.
        ex (&distinct &h) quodlibet.
      * intro h.
        match &h with | thursday | wednesday end.
        -- ex &thursday quodlibet.
        -- match &wednesday with | _ e end.
           ex &e quodlibet.
    + let proof c := year.length.count &y 52
                       (quotient &y 52 6 &weekday &common (Identity.reflexivity _)
                          (&below 6 (Identity.reflexivity _))).
      divide et impera.
      * intro h.
        leibniz &c in &h.
        ex (&distinct &h) quodlibet.
      * intro h.
        match &h with | thursday | wednesday end.
        -- ex &thursday quodlibet.
        -- match &wednesday with | l _ end.
           ex (&ordinary &l) quodlibet.
    + let proof c := year.length.count &y 53
                       (quotient &y 53 0%b0 &weekday &common (Identity.reflexivity _)
                          (&below 0%b0 (Identity.reflexivity _))).
      divide et impera.
      * intro h.
        ipso (disjoin (Identity.reflexivity Weekday.Thursday), _).
      * intro h.
        ipso &c.
    + let proof c := year.length.count &y 52
                       (quotient &y 52 1 &weekday &common (Identity.reflexivity _)
                          (&below 1 (Identity.reflexivity _))).
      divide et impera.
      * intro h.
        leibniz &c in &h.
        ex (&distinct &h) quodlibet.
      * intro h.
        match &h with | thursday | wednesday end.
        -- ex &thursday quodlibet.
        -- match &wednesday with | _ e end.
           ex &e quodlibet.
    + let proof c := year.length.count &y 52
                       (quotient &y 52 2 &weekday &common (Identity.reflexivity _)
                          (&below 2 (Identity.reflexivity _))).
      divide et impera.
      * intro h.
        leibniz &c in &h.
        ex (&distinct &h) quodlibet.
      * intro h.
        match &h with | thursday | wednesday end.
        -- ex &thursday quodlibet.
        -- match &wednesday with | _ e end.
           ex &e quodlibet.
    + let proof c := year.length.count &y 52
                       (quotient &y 52 3 &weekday &common (Identity.reflexivity _)
                          (&below 3 (Identity.reflexivity _))).
      divide et impera.
      * intro h.
        leibniz &c in &h.
        ex (&distinct &h) quodlibet.
      * intro h.
        match &h with | thursday | wednesday end.
        -- ex &thursday quodlibet.
        -- match &wednesday with | _ e end.
           ex &e quodlibet.
  -
    lemma leap_year : Date.is_leap y = true.
    {
      ipso (modus aequans (Date.year.length.specification &y), &leap).
    }
    match (Date.weekday_of_day_number (Date.days_before_year &y)) with
    | Monday | Tuesday | Wednesday | Thursday | Friday | Saturday | Sunday
    end; intro weekday.
    + let proof c := year.length.count &y 52
                       (quotient &y 52 5 &weekday &leap (Identity.reflexivity _)
                          (&below 5 (Identity.reflexivity _))).
      divide et impera.
      * intro h.
        leibniz &c in &h.
        ex (&distinct &h) quodlibet.
      * intro h.
        match &h with | thursday | wednesday end.
        -- ex &thursday quodlibet.
        -- match &wednesday with | _ e end.
           ex &e quodlibet.
    + let proof c := year.length.count &y 52
                       (quotient &y 52 6 &weekday &leap (Identity.reflexivity _)
                          (&below 6 (Identity.reflexivity _))).
      divide et impera.
      * intro h.
        leibniz &c in &h.
        ex (&distinct &h) quodlibet.
      * intro h.
        match &h with | thursday | wednesday end.
        -- ex &thursday quodlibet.
        -- match &wednesday with | _ e end.
           ex &e quodlibet.
    + let proof c := year.length.count &y 53
                       (quotient &y 53 0%b0 &weekday &leap (Identity.reflexivity _)
                          (&below 0%b0 (Identity.reflexivity _))).
      divide et impera.
      * intro h.
        ipso (disjoin _, (conjoin &leap_year, (Identity.reflexivity Weekday.Wednesday))).
      * intro h.
        ipso &c.
    + let proof c := year.length.count &y 53
                       (quotient &y 53 1 &weekday &leap (Identity.reflexivity _)
                          (&below 1 (Identity.reflexivity _))).
      divide et impera.
      * intro h.
        ipso (disjoin (Identity.reflexivity Weekday.Thursday), _).
      * intro h.
        ipso &c.
    + let proof c := year.length.count &y 52
                       (quotient &y 52 2 &weekday &leap (Identity.reflexivity _)
                          (&below 2 (Identity.reflexivity _))).
      divide et impera.
      * intro h.
        leibniz &c in &h.
        ex (&distinct &h) quodlibet.
      * intro h.
        match &h with | thursday | wednesday end.
        -- ex &thursday quodlibet.
        -- match &wednesday with | _ e end.
           ex &e quodlibet.
    + let proof c := year.length.count &y 52
                       (quotient &y 52 3 &weekday &leap (Identity.reflexivity _)
                          (&below 3 (Identity.reflexivity _))).
      divide et impera.
      * intro h.
        leibniz &c in &h.
        ex (&distinct &h) quodlibet.
      * intro h.
        match &h with | thursday | wednesday end.
        -- ex &thursday quodlibet.
        -- match &wednesday with | _ e end.
           ex &e quodlibet.
    + let proof c := year.length.count &y 52
                       (quotient &y 52 4 &weekday &leap (Identity.reflexivity _)
                          (&below 4 (Identity.reflexivity _))).
      divide et impera.
      * intro h.
        leibniz &c in &h.
        ex (&distinct &h) quodlibet.
      * intro h.
        match &h with | thursday | wednesday end.
        -- ex &thursday quodlibet.
        -- match &wednesday with | _ e end.
           ex &e quodlibet.
Qed.

(* The whole weeks before January 4 grow by the weeks of the year. *)
(* year.length.carry *)
Theorem carry
  : forall (y : Year) .
      Date.day_number (january_4th (y + 1)%b) /. Weekday.days_in_week
      = Date.day_number (january_4th y) /. Weekday.days_in_week + weeks_in_year y.
Proof.
  intro y.
  match (year.length.tabulation &y) with | short | long end.
  - leibniz (year.length.count &y 52 &short) in |- *.
    ipso &short.
  - leibniz (year.length.count &y 53 &long) in |- *.
    ipso &long.
Qed.

End length. (* year.length *)

(* The next ISO year starts its weeks later by the number of weeks of this
 * one.
 *)
(* year.succession *)
Theorem succession
  : forall (y : Year) .
      week_one_start (y + 1)%b = week_one_start y + weeks_in_year y * Weekday.days_in_week.
Proof.
  intro y.
  leibniz
    (start.decomposition (&y + 1)%b), (start.decomposition &y), (year.length.carry &y)
    in |- *.
  match (Bin0.multiplication.distributivity.over.addition
           Weekday.days_in_week
           (Date.day_number (january_4th &y) /. Weekday.days_in_week) (weeks_in_year &y))
    with | _ distributed end.
  ipso &distributed.
Qed.

End year. (* year *)

Module week. (* week *)

(* Week [k], counted from the week of 0001-01-01, belongs to the ISO year of
 * its Thursday: the Thursday lies in that year, so January 4 of the year is
 * no later than the week, and January 4 of the next year is after it.
 *)
(* week.boundedness *)
Theorem boundedness
  : forall (k : Bin0) .
      let y :=
        Date.year
          (Date.from_day_number (k * Weekday.days_in_week + Weekday.to_b0 Weekday.Thursday)) in
      Date.day_number (january_4th y) /. Weekday.days_in_week <= k
      /\ k < Date.day_number (january_4th (y + 1)%b) /. Weekday.days_in_week.
Proof.
  intros k y.
  lemma thursday : Weekday.to_b0 Weekday.Thursday = 3.
  {
    ipso (Identity.reflexivity _).
  }
  lemma whole
    : forall (m : Bin0) .
        (m + 1) * Weekday.days_in_week = m * Weekday.days_in_week + Weekday.days_in_week.
  {
    intro m.
    match (Bin0.multiplication.distributivity.over.addition Weekday.days_in_week &m 1)
      with | _ distributed end.
    match (Bin0.multiplication.identity Weekday.days_in_week) with | one _ end.
    leibniz &distributed, &one in |- *.
    quod idem est.
  }
  match (Date.number.boundedness
           (Date.from_day_number (&k * Weekday.days_in_week + Weekday.to_b0 Weekday.Thursday)))
    with | low high end.
  let &y in &low, &high.
  leibniz
    (Date.number.retraction (&k * Weekday.days_in_week + Weekday.to_b0 Weekday.Thursday)),
    &thursday
    in &low, &high.
  divide et impera.
  -
    match (Comparable.order.strict.trichotomy
             &k (Date.day_number (january_4th &y) /. Weekday.days_in_week))
      with | smaller | rest end.
    +
      let proof s :=
        Bin0.order.succession
          &k (Date.day_number (january_4th &y) /. Weekday.days_in_week) &smaller.
      let proof t :=
        modus aequans
          (Bin0.division.characterization
             (&k + 1) (Date.day_number (january_4th &y)) Weekday.days_in_week),
          &s.
      leibniz (january.decomposition &y), (&whole &k) in &t.
      let proof u := Bin0.addition.order.monotonicity 3 _ _ &low.
      leibniz
        (Bin0.addition.commutativity 3 (Date.days_before_year &y)),
        (Bin0.addition.commutativity 3 (&k * Weekday.days_in_week + 3))
        in &u.
      lemma short
        : &k * Weekday.days_in_week + 3 + 3 < &k * Weekday.days_in_week + Weekday.days_in_week.
      {
        simpl Bin0.LessThan in |- *.
        exists Bin.One.
        leibniz
          (Bin0.addition.associativity (&k * Weekday.days_in_week + 3) 3 1),
          (Bin0.addition.associativity (&k * Weekday.days_in_week) 3 (3 + 1))
          in |- *.
        ipso (Identity.reflexivity (&k * Weekday.days_in_week + Weekday.days_in_week)).
      }
      let proof v := Comparable.order.mixed.left.transitivity &u &short.
      let proof g := Comparable.order.mixed.left.transitivity &t &v.
      ex (Bin0.order.strict.irreflexivity _ &g) quodlibet.
    +
      match &rest with | same | greater end.
      * ipso (disjoin (symm &same), _).
      * ipso (disjoin _, &greater).
  -
    let proof s :=
      Bin0.order.succession
        (&k * Weekday.days_in_week + 3) (Date.days_before_year (&y + 1)%b) &high.
    let proof u := Bin0.addition.order.monotonicity 3 _ _ &s.
    leibniz
      (Bin0.addition.commutativity 3 (&k * Weekday.days_in_week + 3 + 1)),
      (Bin0.addition.commutativity 3 (Date.days_before_year (&y + 1)%b))
      in &u.
    lemma level
      : &k * Weekday.days_in_week + 3 + 1 + 3 = (&k + 1) * Weekday.days_in_week.
    {
      leibniz (&whole &k) in |- *.
      leibniz
        (Bin0.addition.associativity (&k * Weekday.days_in_week + 3) 1 3),
        (Bin0.addition.associativity (&k * Weekday.days_in_week) 3 (1 + 3))
        in |- *.
      ipso (Identity.reflexivity (&k * Weekday.days_in_week + Weekday.days_in_week)).
    }
    leibniz &level, <- (january.decomposition (&y + 1)%b) in &u.
    let proof q :=
      modus aequans
        (Bin0.division.characterization
           (&k + 1) (Date.day_number (january_4th (&y + 1)%b)) Weekday.days_in_week),
        &u.
    lemma step : &k < &k + 1.
    {
      simpl Bin0.LessThan in |- *.
      exists Bin.One.
      quod idem est.
    }
    ipso (Comparable.order.mixed.right.transitivity &step &q).
Qed.

(* The converse of [boundedness]: a week between the whole weeks of
 * January 4 of [y] and of [y + 1] has its Thursday in [y].
 *)
(* week.location *)
Theorem location
  : forall (y : Year) (k : Bin0) .
      Date.day_number (january_4th y) /. Weekday.days_in_week <= k
      -> k < Date.day_number (january_4th (y + 1)%b) /. Weekday.days_in_week
      -> Date.days_before_year y <= k * Weekday.days_in_week + Weekday.to_b0 Weekday.Thursday
         /\ k * Weekday.days_in_week + Weekday.to_b0 Weekday.Thursday
            < Date.days_before_year (y + 1)%b.
Proof.
  intros y k lower upper.
  lemma thursday : Weekday.to_b0 Weekday.Thursday = 3.
  {
    ipso (Identity.reflexivity _).
  }
  lemma whole
    : forall (m : Bin0) .
        (m + 1) * Weekday.days_in_week = m * Weekday.days_in_week + Weekday.days_in_week.
  {
    intro m.
    match (Bin0.multiplication.distributivity.over.addition Weekday.days_in_week &m 1)
      with | _ distributed end.
    match (Bin0.multiplication.identity Weekday.days_in_week) with | one _ end.
    leibniz &distributed, &one in |- *.
    quod idem est.
  }
  lemma positive : 0%b0 < Weekday.days_in_week.
  {
    match (Bin0.comparison.specification 0%b0 Weekday.days_in_week) with | strict _ end.
    ipso (modus aequans &strict, (Identity.reflexivity Comparison.Lt)).
  }
  leibniz &thursday in |- *.
  divide et impera.
  -
    match (Bin0.division.specification (Date.day_number (january_4th &y)) Weekday.days_in_week)
      with | e below end.
    let a := Date.day_number (january_4th y) /. Weekday.days_in_week in &e, &lower.
    let r := Date.day_number (january_4th y) %. Weekday.days_in_week in &e, &below.
    leibniz (january.decomposition &y) in &e.
    lemma inside
      : Date.days_before_year y + 3 < &a * Weekday.days_in_week + Weekday.days_in_week.
    {
      leibniz <- &e in |- *.
      ipso (Bin0.addition.order.strict.monotonicity
              (&a * Weekday.days_in_week) &r (&a * Weekday.days_in_week) Weekday.days_in_week
              (disjoin (Identity.reflexivity (&a * Weekday.days_in_week)), _) &below).
    }
    let proof s := Bin0.order.succession _ _ &inside.
    lemma wide
      : &a * Weekday.days_in_week + Weekday.days_in_week
        = &a * Weekday.days_in_week + 3 + 3 + 1.
    {
      leibniz
        (Bin0.addition.associativity (&a * Weekday.days_in_week + 3) 3 1),
        (Bin0.addition.associativity (&a * Weekday.days_in_week) 3 (3 + 1))
        in |- *.
      ipso (Identity.reflexivity (&a * Weekday.days_in_week + Weekday.days_in_week)).
    }
    leibniz &wide in &s.
    leibniz
      (Bin0.addition.commutativity (Date.days_before_year &y + 3) 1),
      (Bin0.addition.commutativity (&a * Weekday.days_in_week + 3 + 3) 1)
      in &s.
    let proof c1 := Bin0.addition.order.cancellation 1 _ _ &s.
    leibniz
      (Bin0.addition.commutativity (Date.days_before_year &y) 3),
      (Bin0.addition.commutativity (&a * Weekday.days_in_week + 3) 3)
      in &c1.
    let proof c2 := Bin0.addition.order.cancellation 3 _ _ &c1.
    lemma multiple : &a * Weekday.days_in_week <= &k * Weekday.days_in_week.
    {
      match &lower with | same | smaller end.
      - leibniz &same in |- *.
        ipso (disjoin (Identity.reflexivity (&k * Weekday.days_in_week)), _).
      - leibniz
          (Bin0.multiplication.commutativity &a Weekday.days_in_week),
          (Bin0.multiplication.commutativity &k Weekday.days_in_week)
          in |- *.
        ipso (disjoin _,
                (Bin0.multiplication.left.order.strict.monotonicity
                   Weekday.days_in_week &a &k &positive &smaller)).
    }
    let proof m3 := Bin0.addition.order.monotonicity 3 _ _ &multiple.
    leibniz
      (Bin0.addition.commutativity 3 (&a * Weekday.days_in_week)),
      (Bin0.addition.commutativity 3 (&k * Weekday.days_in_week))
      in &m3.
    ipso (Comparable.order.transitivity _ _ _ &c2 &m3).
  -
    let proof s := Bin0.order.succession _ _ &upper.
    let proof t :=
      modus aequans
        (Bin0.division.characterization
           (&k + 1) (Date.day_number (january_4th (&y + 1)%b)) Weekday.days_in_week),
        &s.
    leibniz (january.decomposition (&y + 1)%b), (&whole &k) in &t.
    lemma level
      : &k * Weekday.days_in_week + Weekday.days_in_week
        = &k * Weekday.days_in_week + 3 + 1 + 3.
    {
      leibniz
        (Bin0.addition.associativity (&k * Weekday.days_in_week + 3) 1 3),
        (Bin0.addition.associativity (&k * Weekday.days_in_week) 3 (1 + 3))
        in |- *.
      ipso (Identity.reflexivity (&k * Weekday.days_in_week + Weekday.days_in_week)).
    }
    leibniz &level in &t.
    leibniz
      (Bin0.addition.commutativity (&k * Weekday.days_in_week + 3 + 1) 3),
      (Bin0.addition.commutativity (Date.days_before_year (&y + 1)%b) 3)
      in &t.
    let proof c := Bin0.addition.order.cancellation 3 _ _ &t.
    lemma step : &k * Weekday.days_in_week + 3 < &k * Weekday.days_in_week + 3 + 1.
    {
      simpl Bin0.LessThan in |- *.
      exists Bin.One.
      quod idem est.
    }
    ipso (Comparable.order.mixed.right.transitivity &step &c).
Qed.

(* The week's place in its ISO year is at most the weeks of that year, by
 * [boundedness] and [year.length.carry].
 *)
(* week.validity *)
Theorem validity
  : forall (k : Bin0) .
      let y :=
        Date.year
          (Date.from_day_number (k * Weekday.days_in_week + Weekday.to_b0 Weekday.Thursday)) in
      Assert
        (is_valid y
           (Bin0.successor
              (Bin0.saturating_sub k (Date.day_number (january_4th y) /. Weekday.days_in_week)))).
Proof.
  intros k y.
  match (week.boundedness &k) with | lower upper end.
  let &y in &lower, &upper.
  leibniz (year.length.carry &y) in &upper.
  let a := Date.day_number (january_4th y) /. Weekday.days_in_week in &lower, &upper |- *.
  let proof restored := Bin0.subtraction.saturating.specification &lower.
  leibniz <- &restored in &upper.
  lemma inner : Bin0.saturating_sub &k &a < weeks_in_year &y.
  {
    simpl Bin0.LessThan in &upper |- *.
    match &upper with | j e end.
    leibniz (Bin0.addition.associativity &a (Bin0.saturating_sub &k &a) (Bin0.Positive &j)) in &e.
    match (Bin0.addition.cancellation
             &a (Bin0.saturating_sub &k &a + Bin0.Positive &j) (weeks_in_year &y))
      with | cancel _ end.
    exists &j.
    ipso (&cancel &e).
  }
  let proof fits := Bin0.order.succession _ _ &inner.
  leibniz <- (Bin0.successor.specification (Bin0.saturating_sub &k &a)) in &fits.
  simpl is_valid in |- *.
  let proof checked :=
    modus aequans
      (Comparable.order.reflection
         (Bin0.Positive (Bin0.successor (Bin0.saturating_sub &k &a))) (weeks_in_year &y)),
      &fits.
  ipso (modus aequans (Assert.specification _), &checked).
Qed.

End week. (* week *)

(* The ISO week date of [d]: its week has [k] whole weeks before it, counted
 * from the week of 0001-01-01, and its ISO year is the year of that week's
 * Thursday. It stands below [week.validity] because its ctor takes that
 * proof.
 *)
(* [Date -> IsoWeekDate] *)
Definition from_date := fun (d : Date) .
  let k := Date.day_number d /. Weekday.days_in_week in
  let y :=
    Date.year (Date.from_day_number (k * Weekday.days_in_week + Weekday.to_b0 Weekday.Thursday)) in
  IsoWeekDate.introduction y
    (Bin0.successor (Bin0.saturating_sub k (Date.day_number (january_4th y) /. Weekday.days_in_week)))
    (Date.weekday d) (week.validity k).

Module conversion. (* conversion *)

Module date. (* conversion.date *)

(* The start of the ISO year and the whole weeks after it give back the whole
 * weeks of the day number, and the weekday its remainder by 7.
 *)
(* conversion.date.retraction *)
Theorem retraction : forall (d : Date) . to_date (from_date d) = d.
Proof.
  intro d.
  lemma facto
    : let k := Date.day_number d /. Weekday.days_in_week in
      let y :=
        Date.year
          (Date.from_day_number (k * Weekday.days_in_week + Weekday.to_b0 Weekday.Thursday)) in
      Date.from_day_number
        (week_one_start y
         + Bin0.saturating_sub
             (Bin0.successor
                (Bin0.saturating_sub k (Date.day_number (january_4th y) /. Weekday.days_in_week)))
             1
           * Weekday.days_in_week
         + Weekday.to_b0 (Date.weekday d))
      = d.
  {
    intros k y.
    match (week.boundedness &k) with | lower _ end.
    let &y in &lower.
    leibniz (start.decomposition &y) in |- *.
    let a := Date.day_number (january_4th y) /. Weekday.days_in_week in &lower |- *.
    leibniz
      (Bin0.successor.specification (Bin0.saturating_sub &k &a)),
      (Bin0.subtraction.saturating.inversion.addition (Bin0.saturating_sub &k &a) 1)
      in |- *.
    simpl Date.weekday in |- *.
    leibniz (Date.weekday.specification (Date.day_number &d)) in |- *.
    match (Bin0.multiplication.distributivity.over.addition
             Weekday.days_in_week &a (Bin0.saturating_sub &k &a))
      with | _ distributed end.
    leibniz <- &distributed in |- *.
    leibniz (Bin0.subtraction.saturating.specification &lower) in |- *.
    match (Bin0.division.specification (Date.day_number &d) Weekday.days_in_week)
      with | e _ end.
    let &k in &e.
    leibniz &e in |- *.
    ipso (Date.number.section &d).
  }
  ipso facto.
Qed.

(* The day number of [to_date x] is the whole weeks before the week of [x]
 * and the day's place, so its quotient by 7 lies between the whole weeks of
 * the two January 4ths around [x], its Thursday lies in the year of [x], and
 * every part of [x] comes back.
 *)
(* conversion.date.section *)
Theorem section : forall (x : IsoWeekDate) . from_date (to_date x) = x.
Proof.
  intro x.
  match &x with | introduction y w d p end.
  lemma place : Weekday.to_b0 d < Weekday.days_in_week.
  {
    match (Bin0.comparison.specification (Weekday.to_b0 &d) Weekday.days_in_week)
      with | strict _ end.
    lemma facto : Bin0.compare (Weekday.to_b0 d) Weekday.days_in_week = Comparison.Lt.
    {
      match &d with
      | Monday | Tuesday | Wednesday | Thursday | Friday | Saturday | Sunday
      end; ipso (Identity.reflexivity _).
    }
    ipso (modus aequans &strict, &facto).
  }
  lemma within : Bin0.Positive w <= weeks_in_year y.
  {
    let proof checked := modus aequans (Assert.specification _), &p.
    simpl is_valid in &checked.
    ipso (modus aequans (Comparable.order.reflection (Bin0.Positive &w) (weeks_in_year &y)),
            &checked).
  }
  lemma restored : Bin0.saturating_sub w 1 + 1 = Bin0.Positive w.
  {
    let proof r := Date.year.antecedence.restoration w.
    simpl Date.years_before in &r.
    ipso &r.
  }
  let X := IsoWeekDate.introduction y w d p in |- *.
  lemma retracted
    : Date.day_number (to_date X)
      = week_one_start y + Bin0.saturating_sub w 1 * Weekday.days_in_week + Weekday.to_b0 d.
  {
    ipso (Date.number.retraction
            (week_one_start &y + Bin0.saturating_sub w 1 * Weekday.days_in_week
             + Weekday.to_b0 &d)).
  }
  lemma spread
    : week_one_start y + Bin0.saturating_sub w 1 * Weekday.days_in_week + Weekday.to_b0 d
      = (Date.day_number (january_4th y) /. Weekday.days_in_week + Bin0.saturating_sub w 1)
          * Weekday.days_in_week
        + Weekday.to_b0 d.
  {
    leibniz (start.decomposition &y) in |- *.
    match (Bin0.multiplication.distributivity.over.addition
             Weekday.days_in_week
             (Date.day_number (january_4th &y) /. Weekday.days_in_week) (Bin0.saturating_sub w 1))
      with | _ distributed end.
    leibniz &distributed in |- *.
    quod idem est.
  }
  match (Bin0.division.uniqueness
           ((Date.day_number (january_4th &y) /. Weekday.days_in_week + Bin0.saturating_sub w 1)
              * Weekday.days_in_week
            + Weekday.to_b0 &d)
           Weekday.days_in_week
           (Date.day_number (january_4th &y) /. Weekday.days_in_week + Bin0.saturating_sub w 1)
           (Weekday.to_b0 &d)
           (conjoin (Identity.reflexivity _), &place))
    with | quotient remainder end.
  leibniz <- &spread in &quotient, &remainder.
  lemma next
    : Date.day_number (january_4th y) /. Weekday.days_in_week + Bin0.saturating_sub w 1 + 1
      <= Date.day_number (january_4th (y + 1)%b) /. Weekday.days_in_week.
  {
    leibniz (year.length.carry &y) in |- *.
    leibniz
      (Bin0.addition.associativity
         (Date.day_number (january_4th &y) /. Weekday.days_in_week) (Bin0.saturating_sub w 1) 1),
      &restored
      in |- *.
    ipso (Bin0.addition.order.monotonicity
            (Date.day_number (january_4th &y) /. Weekday.days_in_week) _ _ &within).
  }
  lemma step
    : Date.day_number (january_4th y) /. Weekday.days_in_week + Bin0.saturating_sub w 1
      < Date.day_number (january_4th y) /. Weekday.days_in_week + Bin0.saturating_sub w 1 + 1.
  {
    simpl Bin0.LessThan in |- *.
    exists Bin.One.
    quod idem est.
  }
  let proof upper := Comparable.order.mixed.right.transitivity &step &next.
  lemma lower
    : Date.day_number (january_4th y) /. Weekday.days_in_week
      <= Date.day_number (january_4th y) /. Weekday.days_in_week + Bin0.saturating_sub w 1.
  {
    leibniz
      (Bin0.addition.commutativity
         (Date.day_number (january_4th &y) /. Weekday.days_in_week) (Bin0.saturating_sub w 1))
      in |- *.
    ipso (Bin0.addition.right.order.extensivity
            (Bin0.saturating_sub w 1) (Date.day_number (january_4th &y) /. Weekday.days_in_week)).
  }
  match (week.location &y
           (Date.day_number (january_4th &y) /. Weekday.days_in_week + Bin0.saturating_sub w 1)
           &lower &upper)
    with | low high end.
  match (Date.number.boundedness
           (Date.from_day_number
              ((Date.day_number (january_4th &y) /. Weekday.days_in_week + Bin0.saturating_sub w 1)
                 * Weekday.days_in_week
               + Weekday.to_b0 Weekday.Thursday)))
    with | own_low own_high end.
  leibniz
    (Date.number.retraction
       ((Date.day_number (january_4th &y) /. Weekday.days_in_week + Bin0.saturating_sub w 1)
          * Weekday.days_in_week
        + Weekday.to_b0 Weekday.Thursday))
    in &own_low, &own_high.
  let proof found := Date.year.uniqueness &own_low &own_high &low &high.
  lemma same_year : year (from_date (to_date X)) = year X.
  {
    lemma facto
      : Date.year
          (Date.from_day_number
             ((Date.day_number (to_date X) /. Weekday.days_in_week) * Weekday.days_in_week
              + Weekday.to_b0 Weekday.Thursday))
        = y.
    {
      leibniz &retracted, &quotient in |- *.
      ipso &found.
    }
    ipso facto.
  }
  lemma same_week : week (from_date (to_date X)) = week X.
  {
    lemma facto
      : Bin0.successor
          (Bin0.saturating_sub
             (Date.day_number (to_date X) /. Weekday.days_in_week)
             (Date.day_number
                (january_4th
                   (Date.year
                      (Date.from_day_number
                         ((Date.day_number (to_date X) /. Weekday.days_in_week)
                            * Weekday.days_in_week
                          + Weekday.to_b0 Weekday.Thursday))))
              /. Weekday.days_in_week))
        = w.
    {
      leibniz &retracted, &quotient, &found in |- *.
      leibniz
        (Bin0.addition.commutativity
           (Date.day_number (january_4th &y) /. Weekday.days_in_week) (Bin0.saturating_sub w 1)),
        (Bin0.subtraction.saturating.inversion.addition
           (Bin0.saturating_sub w 1) (Date.day_number (january_4th &y) /. Weekday.days_in_week))
        in |- *.
      let proof s := Date.year.antecedence.section w.
      simpl Date.years_before in &s.
      ipso &s.
    }
    ipso facto.
  }
  lemma same_weekday : weekday (from_date (to_date X)) = weekday X.
  {
    lemma facto : Date.weekday_of_day_number (Date.day_number (to_date X)) = d.
    {
      leibniz &retracted in |- *.
      simpl Date.weekday_of_day_number in |- *.
      leibniz &remainder, (Weekday.conversion.bin0.retraction &d) in |- *.
      ipso (Identity.reflexivity &d).
    }
    ipso facto.
  }
  ipso (extensionality (from_date (to_date &X)) &X &same_year &same_week &same_weekday).
Qed.

End date. (* conversion.date *)

End conversion. (* conversion *)

Module weekday. (* weekday *)

Module agreement. (* weekday.agreement *)

(* [from_date] takes the date's weekday as it is. *)
(* weekday.agreement.forward *)
Theorem forward : forall (d : Date) . weekday (from_date d) = Date.weekday d.
Proof.
  intro d.
  ipso (Identity.reflexivity (Date.weekday &d)).
Qed.

(* By [conversion.date.section], the weekday of [x] is that of the date
 * [to_date x] read back.
 *)
(* weekday.agreement.backward *)
Theorem backward : forall (x : IsoWeekDate) . Date.weekday (to_date x) = weekday x.
Proof.
  intro x.
  ipso (congru weekday, (conversion.date.section &x)).
Qed.

End agreement. (* weekday.agreement *)

End weekday. (* weekday *)

End IsoWeekDate. (* IsoWeekDate *)

Abbreviation IsoWeekDate := IsoWeekDate.T.
