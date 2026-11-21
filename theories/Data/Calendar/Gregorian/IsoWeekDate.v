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
  lemma carried
    : Date.day_number (january_4th (y + 1)%b) /. Weekday.days_in_week
      = Date.day_number (january_4th y) /. Weekday.days_in_week + weeks_in_year y.
  {
    match (year.length.tabulation &y) with | short | long end.
    - leibniz (year.length.count &y 52 &short) in |- *.
      ipso &short.
    - leibniz (year.length.count &y 53 &long) in |- *.
      ipso &long.
  }
  leibniz (start.decomposition (&y + 1)%b), (start.decomposition &y), &carried in |- *.
  match (Bin0.multiplication.distributivity.over.addition
           Weekday.days_in_week
           (Date.day_number (january_4th &y) /. Weekday.days_in_week) (weeks_in_year &y))
    with | _ distributed end.
  ipso &distributed.
Qed.

End year. (* year *)

End IsoWeekDate. (* IsoWeekDate *)

Abbreviation IsoWeekDate := IsoWeekDate.T.
