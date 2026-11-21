(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

From JW Require Import Core.All.
From JW Require Import Data.Assert.
From JW Require Import Data.Base.Bool.
From JW Require Import Data.Base.Comparison.
From JW Require Import Data.Calendar.Month.
From JW Require Import Data.Calendar.Weekday.
From JW Require Import Data.Comparable.
From JW Require Import Data.Number.Binary.Bin.
From JW Require Import Data.Number.Binary.Bin0.
From JW Require Import Data.Number.Nat.
From JW Require Import Data.Number.Nat0.
From JW Require Import Data.Option.
From JW Require Import Data.Product.
From JW Require Import Tactics.Equation.
From JW Require Import Tactics.Modus.
From JW Require Import Tactics.Witness.

(* A date of the proleptic Gregorian calendar: the Gregorian leap rule holds
 * for every year, the years count from 1, and day 0 is 0001-01-01.
 *)
Module Date. (* Date *)

(* Numbers are written in decimal: a bare literal is a [Bin], which
 * stands for a [Bin0] wherever one is expected, so only zero carries
 * its key.
 *)
Local Open Scope jw_bin0_scope.
Local Open Scope jw_bin_decimal_scope.
Local Open Scope jw_product_scope.

Abbreviation Year := Bin (only parsing).
Abbreviation Day := Bin (only parsing).
Abbreviation Days := Bin0 (only parsing).

(* The ctor takes only a day that its month has, so the checks it asserts
 * come first.
 *)

(* The years of each period of the leap rule. *)
(* [Bin] *)
Definition years_in_quadrennium : Bin := 4.

(* [Bin] *)
Definition years_in_century : Bin := 100.

(* [Bin] *)
Definition years_in_quadricentennium : Bin := 400.

(* A year divisible by 4 is a leap year, except one divisible by 100 and not
 * by 400.
 *)
(* [Year -> Bool] *)
Definition is_leap := fun (y : Year) .
  (Bin0.eq (y %. years_in_quadrennium) 0%b0
    && (! Bin0.eq (y %. years_in_century) 0%b0
          || Bin0.eq (y %. years_in_quadricentennium) 0%b0))%bool.

(* [Year -> Month -> Bin] *)
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

(* A day is a Bin which is never 0, so the only check is the length of its month. *)
(* [Year -> Month -> Day -> Bool] *)
Definition is_valid := fun (y : Year) (m : Month) (d : Day) .
  Comparable.le Bin.compare d (days_in_month y m).

(* The year, the month and the day of the month, with the proof that the
 * month has that day, so no other value can be built.
 *)
Inductive T : Type :=
  | introduction
    : forall (y : Year) (m : Month) (d : Day) . Assert (is_valid y m d) -> T.

Abbreviation Date := T.

(* [Date -> Year] *)
Definition year := fun (x : Date) .
  match x with
  | Date.introduction y _ _ _ => y
  end.

(* [Date -> Month] *)
Definition month := fun (x : Date) .
  match x with
  | Date.introduction _ m _ _ => m
  end.

(* [Date -> Day] *)
Definition day := fun (x : Date) .
  match x with
  | Date.introduction _ _ d _ => d
  end.

(* The date, [None] when its month has no such day. *)
(* [Year -> Month -> Day -> Option Date] *)
Definition make := fun (y : Year) (m : Month) (d : Day) .
  Assert.guard (is_valid y m d) (Date.introduction y m d).

(* The lengths of the periods the leap rule repeats over. Each period's leap
 * year is its last year, so a period that is not complete has no leap day.
 * None is zero, so each is a [Bin] and can divide; it stands for [Days]
 * wherever it is added or multiplied.
 *)
(* [Bin] *)
Definition days_in_common_year : Bin := 365.

(* [Bin] *)
Definition days_in_leap_year : Bin := (days_in_common_year + 1)%b.

(* [Year -> Bin] *)
Definition days_in_year := fun (y : Year) .
  match is_leap y with
  | true  => days_in_leap_year
  | false => days_in_common_year
  end.

(* A quadrennium, four years: three common years and a leap year. *)
(* [Bin] *)
Definition days_in_quadrennium : Bin :=
  ((3%b_decimal * days_in_common_year) + days_in_leap_year)%b.

(* A century, 100 years: 25 quadrennia, but the century year is not leap, so
 * the last quadrennium has four common years.
 *)
(* [Bin] *)
Definition days_in_century : Bin :=
  ((24%b_decimal * days_in_quadrennium) + (years_in_quadrennium * days_in_common_year))%b.

(* A quadricentennium, 400 years: four centuries, and the last year of the
 * fourth is leap after all.
 *)
(* [Bin] *)
Definition days_in_quadricentennium : Bin := ((4%b_decimal * days_in_century) + 1)%b.

(* The years before [y], the first year being 1. *)
(* [Year -> Bin0] *)
Definition years_before := fun (y : Year) . Bin0.saturating_sub y 1.

(* The days before January 1 of [y]: the years before [y] taken apart into
 * whole quadricentennia, then whole centuries, then whole quadrennia, then
 * single years.
 *)
(* [Year -> Days] *)
Definition days_before_year := fun (y : Year) .
  let n := years_before y in
  let in_quadricentennium := n %. years_in_quadricentennium in
  let in_century := in_quadricentennium %. years_in_century in
  (days_in_quadricentennium * (n /. years_in_quadricentennium))
    + (days_in_century * (in_quadricentennium /. years_in_century))
    + (days_in_quadrennium * (in_century /. years_in_quadrennium))
    + (days_in_common_year * (in_century %. years_in_quadrennium)).

(* The days of [y] before day 1 of [m], each month's count the one before it
 * plus the length of the month before it.
 *)
(* [Year -> Month -> Days] *)
Definition days_before_month := fun (y : Year) (m : Month) .
  let january   := 0%b0 in
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
(* [Date -> Day] *)
Definition day_of_year := fun (x : Date) .
  match days_before_month (year x) (month x) with
  | Bin0.Zero       => day x
  | Bin0.Positive p => (p + day x)%b
  end.

(* The days from 0001-01-01 to the date, 0001-01-01 itself being 0. *)
(* [Date -> Days] *)
Definition day_number := fun (x : Date) .
  days_before_year (year x)
    + days_before_month (year x) (month x)
    + Bin0.saturating_sub (day x) 1.

(* The weekday of day number [n], 0001-01-01 being a Monday. The remainder
 * by 7 is below 7, so [Weekday.from_b0] never gives [None] here.
 *)
(* [Days -> Weekday] *)
Definition weekday_of_day_number := fun (n : Days) .
  match Weekday.from_b0 (n %. Weekday.days_in_week) with
  | Some w => w
  | None   => Weekday.Monday
  end.

(* [Date -> Weekday] *)
Definition weekday := fun (x : Date) . weekday_of_day_number (day_number x).

(* [r] divided by [d], the quotient held at 3: a fourth period may be one day
 * longer than [d], and its last day stays in it.
 *)
(* [Bin0 -> Bin -> Product Bin0 Bin0] *)
Definition div_clamped_at_3 := fun (r : Bin0) (d : Bin) .
  let quotient := Bin0.min (r /. d) 3 in
  (quotient, Bin0.saturating_sub r (quotient * d)).

(* The whole years before day number [n], and the days of its year before it,
 * counted through the quadricentennia, the centuries, the quadrennia and the
 * years.
 *)
(* [Days -> Product Bin0 Days] *)
Definition div_year := fun (n : Days) .
  let centuries := div_clamped_at_3 (n %. days_in_quadricentennium) days_in_century in
  let years := div_clamped_at_3 (pi_2 centuries %. days_in_quadrennium) days_in_common_year in
  ((years_in_quadricentennium * (n /. days_in_quadricentennium))
     + (years_in_century * pi_1 centuries)
     + (years_in_quadrennium * (pi_2 centuries /. days_in_quadrennium))
     + pi_1 years,
   pi_2 years).

(* The month and the day of the month of the date which is [days] days after
 * January 1 of year [y].
 *)
(* [Year -> Days -> Product Month Day] *)
Definition calendar_date_after_days := fun (y : Year) (days : Days) .
  let begun := fun (m : Month) . Bin0.le (days_before_month y m) days in
  let month :=
    match begun Month.December with
    | true  => Month.December
    | false =>
        match begun Month.November with
        | true  => Month.November
        | false =>
            match begun Month.October with
            | true  => Month.October
            | false =>
                match begun Month.September with
                | true  => Month.September
                | false =>
                    match begun Month.August with
                    | true  => Month.August
                    | false =>
                        match begun Month.July with
                        | true  => Month.July
                        | false =>
                            match begun Month.June with
                            | true  => Month.June
                            | false =>
                                match begun Month.May with
                                | true  => Month.May
                                | false =>
                                    match begun Month.April with
                                    | true  => Month.April
                                    | false =>
                                        match begun Month.March with
                                        | true  => Month.March
                                        | false =>
                                            match begun Month.February with
                                            | true  => Month.February
                                            | false => Month.January
                                            end
                                        end
                                    end
                                end
                            end
                        end
                    end
                end
            end
        end
    end in
  (month, Bin0.successor (Bin0.saturating_sub days (days_before_month y month))).

(* The month in year [y] that holds the date which is [days] days after January 1. *)
(* [Year -> Days -> Month] *)
Definition month_after_days := fun (y : Year) (days : Days) .
  pi_1 (calendar_date_after_days y days).

(* The day of the month of the date which is [days] days after January 1 of year [y]. *)
(* [Year -> Days -> Day] *)
Definition day_of_month_after_days := fun (y : Year) (days : Days) .
  pi_2 (calendar_date_after_days y days).

(* The order of time: by year, then by month, then by day. *)
(* [Date -> Date -> Comparison] *)
Definition compare := fun (x1 : Date) (x2 : Date) .
  match Bin.compare (year x1) (year x2) with
  | Comparison.Lt => Comparison.Lt
  | Comparison.Eq =>
      match Month.compare (month x1) (month x2) with
      | Comparison.Lt => Comparison.Lt
      | Comparison.Eq => Bin.compare (day x1) (day x2)
      | Comparison.Gt => Comparison.Gt
      end
  | Comparison.Gt => Comparison.Gt
  end.

(* [x1] comes before [x2] in the order of time. *)
(* [Date -> Date -> Prop] *)
Definition LessThan := fun (x1 : Date) (x2 : Date) . compare x1 x2 = Comparison.Lt.

(* antisymmetry *)
Theorem antisymmetry
  : forall (x1 : Date) (x2 : Date) . compare x1 x2 = Comparison.transpose (compare x2 x1).
Proof.
  intros x1 x2.
  match &x1 with | introduction y1 m1 d1 a1 end.
  match &x2 with | introduction y2 m2 d2 a2 end.
  simpl compare, year, month, day in |- *.
  leibniz
    (Bin.comparison.antisymmetry &y1 &y2),
    (Month.comparison.antisymmetry &m1 &m2),
    (Bin.comparison.antisymmetry &d1 &d2)
    in |- *.
  match (Bin.compare &y2 &y1) with | | | end;
    match (Month.compare &m2 &m1) with | | | end;
    match (Bin.compare &d2 &d1) with | | | end;
    simpl in |- *; quod idem est.
Qed.

(* Equal years, months and days make the same date, the proofs of validity
 * being equal by [Assert.uniqueness].
 *)
(* separation *)
Theorem separation : forall (x1 : Date) (x2 : Date) . compare x1 x2 = Comparison.Eq -> x1 = x2.
Proof.
  intros x1 x2 h.
  match &x1 with | introduction y1 m1 d1 a1 end.
  match &x2 with | introduction y2 m2 d2 a2 end.
  simpl compare, year, month, day in &h.
  match (Bin.compare &y1 &y2) with | | | end |- cy.
  - ex &h quodlibet.
  - match (Month.compare &m1 &m2) with | | | end |- cm.
    + ex &h quodlibet.
    + match (Bin.comparison.specification &y1 &y2) with | _ year_equality end.
      match (Month.comparison.specification &m1 &m2) with | _ month_equality end.
      match (Bin.comparison.specification &d1 &d2) with | _ day_equality end.
      let proof ey := modus aequans &year_equality, &cy.
      let proof em := modus aequans &month_equality, &cm.
      let proof ed := modus aequans &day_equality, &h.
      match &ey with | end.
      match &em with | end.
      match &ed with | end.
      leibniz (Assert.uniqueness _ &a1 &a2) in |- *.
      quod idem est.
    + ex &h quodlibet.
  - ex &h quodlibet.
Qed.

Module leap. (* leap *)

(* The statement adds years, so [+] is read as [Bin]'s. *)
Local Open Scope jw_bin_scope.
Local Open Scope jw_bin_decimal_scope.

(* leap.periodicity *)
Theorem periodicity : forall (y : Year) . is_leap (y + 400) = is_leap y.
Proof.
  intro y.
  lemma four : (y + 400) %. 4 = y %. 4.
  {
    lemma zero : 400 %. 4 = 0%b0.
    {
      simpl Bin0.modulo in |- *.
      simpl in |- *.
      quod idem est.
    }
    ipso (Bin0.modulo.sum.right.invariance y 400 4 &zero).
  }
  lemma hundred : (y + 400) %. 100 = y %. 100.
  {
    lemma zero : 400 %. 100 = 0%b0.
    {
      simpl Bin0.modulo in |- *.
      simpl in |- *.
      quod idem est.
    }
    ipso (Bin0.modulo.sum.right.invariance y 400 100 &zero).
  }
  lemma four_hundred : (y + 400) %. 400 = y %. 400.
  {
    lemma zero : 400 %. 400 = 0%b0.
    {
      simpl Bin0.modulo in |- *.
      simpl in |- *.
      quod idem est.
    }
    ipso (Bin0.modulo.sum.right.invariance y 400 400 &zero).
  }
  simpl is_leap in |- *.
  simpl years_in_quadrennium, years_in_century, years_in_quadricentennium in |- *.
  leibniz &four, &hundred, &four_hundred in |- *.
  quod idem est.
Qed.

End leap. (* leap *)

Module month. (* month *)

Module length. (* month.length *)

(* The statement compares days of a month, so [<=] is read as [Bin]'s. *)
Local Open Scope jw_bin_scope.
Local Open Scope jw_bin_decimal_scope.

(* month.length.boundedness *)
Theorem boundedness
  : forall (y : Year) (m : Month) . 28 <= days_in_month y m /\ days_in_month y m <= 31.
Proof.
  intros y m.
  lemma lower : Comparable.le Bin.compare 28 (days_in_month y m) = true.
  {
    simpl days_in_month, Comparable.le, Bin.compare in |- *.
    match (is_leap &y) with | | end;
      match &m with
      | January | February | March | April | May | June
      | July | August | September | October | November | December
      end; simpl in |- *; quod idem est.
  }
  lemma upper : Comparable.le Bin.compare (days_in_month y m) 31 = true.
  {
    simpl days_in_month, Comparable.le, Bin.compare in |- *.
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
  simpl days_in_leap_year, days_in_common_year in |- *.
  match (is_leap &y) with | | end;
    simpl in |- *; simpl Bin.add in |- *; simpl in |- *; quod idem est.
Qed.

(* month.boundedness *)
Theorem boundedness
  : forall (y : Year) (m : Month) .
      days_before_month y m + days_in_month y m <= days_in_year y.
Proof.
  intros y m.
  lemma facto
    : Comparable.le Bin0.compare
        (days_before_month y m + days_in_month y m) (days_in_year y)
      = true.
  {
    simpl days_before_month, days_in_month, days_in_year, Comparable.le, Bin0.compare
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

(* The days through a month are at most the days before any later month.
 * The check is computed for every pair of months and both kinds of year;
 * a pair that is not in order checks [true].
 *)
(* month.monotonicity *)
Theorem monotonicity
  : forall (y : Year) (m1 : Month) (m2 : Month) .
      Month.compare m1 m2 = Comparison.Lt
      -> days_before_month y m1 + days_in_month y m1 <= days_before_month y m2.
Proof.
  intros y m1 m2 h.
  lemma facto
    : match Month.compare m1 m2 with
      | Comparison.Lt =>
          Comparable.le Bin0.compare
            (days_before_month y m1 + days_in_month y m1) (days_before_month y m2)
      | Comparison.Eq => true
      | Comparison.Gt => true
      end
      = true.
  {
    simpl Month.compare in |- *.
    simpl days_before_month, days_in_month, Bin.compare, Comparable.le, Bin0.compare
      in |- *.
    match (is_leap &y) with | | end;
      match &m1 with
      | January | February | March | April | May | June
      | July | August | September | October | November | December
      end;
      match &m2 with
      | January | February | March | April | May | June
      | July | August | September | October | November | December
      end; simpl in |- *; quod idem est.
  }
  leibniz &h in &facto.
  ipso (modus aequans
          (Comparable.order.reflection
             (days_before_month &y &m1 + days_in_month &y &m1) (days_before_month &y &m2)),
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
  simpl days_in_leap_year, days_in_common_year in |- *.
  match (is_leap &y) with | | end.
  - divide et impera.
    + intro e.
      quod idem est.
    + intro e.
      simpl Bin.add in |- *.
      simpl in |- *.
      quod idem est.
  - divide et impera.
    + intro e.
      ex &e quodlibet.
    + intro e.
      ex &e quodlibet.
Qed.

End length. (* year.length *)

Module antecedence. (* year.antecedence *)

(* Both sides are read in [Nat0], where [y] is [1] or a successor and each
 * case computes.
 *)
(* year.antecedence.translation *)
Theorem translation
  : forall (y : Year) (k : Bin) . years_before (y + k)%b = years_before y + k.
Proof.
  intros y k.
  lemma facto
    : Bin0.to_nat0 (years_before (y + k)%b)
      = Bin0.to_nat0 (years_before y + k).
  {
    simpl years_before in |- *.
    leibniz
      (Bin0.conversion.subtraction.saturating (y + k)%b 1),
      (Bin0.conversion.addition (Bin0.saturating_sub y 1) k),
      (Bin0.conversion.subtraction.saturating y 1)
      in |- *.
    simpl Bin0.to_nat0 in |- *.
    leibniz (Bin.conversion.addition &y &k) in |- *.
    let a := Bin.to_nat &y in |- *.
    let proof a := &a.
    extro &a.
    intro a.
    match &a with | One | Successor a' end.
    - simpl in |- *.
      quod idem est.
    - simpl in |- *.
      quod idem est.
  }
  ipso (Bin0.conversion.injectivity &facto).
Qed.

(* Read in [Nat0] as [translation] is, with the [1] put first so that each
 * case computes.
 *)
(* year.antecedence.restoration *)
Theorem restoration : forall (y : Year) . years_before y + 1 = y.
Proof.
  intro y.
  lemma facto : Bin0.to_nat0 (years_before y + 1) = Bin0.to_nat0 y.
  {
    simpl years_before in |- *.
    leibniz
      (Bin0.conversion.addition (Bin0.saturating_sub y 1) 1),
      (Bin0.conversion.subtraction.saturating y 1)
      in |- *.
    simpl Bin0.to_nat0 in |- *.
    leibniz
      (Nat0.addition.commutativity
         (Nat0.saturating_sub
            (Nat0.Positive (Bin.to_nat &y)) (Nat0.Positive (Bin.to_nat 1)))
         (Nat0.Positive (Bin.to_nat 1)))
      in |- *.
    let a := Bin.to_nat &y in |- *.
    let proof a := &a.
    extro &a.
    intro a.
    match &a with | One | Successor a' end.
    - simpl in |- *.
      quod idem est.
    - simpl in |- *.
      quod idem est.
  }
  ipso (Bin0.conversion.injectivity &facto).
Qed.

End antecedence. (* year.antecedence *)

(* 400 more years before [y] add one whole quadricentennium and leave the rest
 * of the decomposition as it was.
 *)
(* year.periodicity *)
Theorem periodicity
  : forall (y : Year) .
      days_before_year (y + 400%b_decimal)%b
      = days_before_year y + days_in_quadricentennium.
Proof.
  intro y.
  simpl days_before_year in |- *.
  simpl years_in_quadrennium, years_in_century, years_in_quadricentennium in |- *.
  leibniz (year.antecedence.translation &y 400) in |- *.
  let n := years_before &y in |- *.
  lemma quotient : (n + 400) /. 400 = (n /. 400) + 1.
  {
    ipso (Bin0.division.translation n 400).
  }
  lemma remainder : (n + 400) %. 400 = n %. 400.
  {
    lemma zero : 400 %. 400 = 0%b0.
    {
      simpl Bin0.modulo in |- *.
      simpl in |- *.
      quod idem est.
    }
    ipso (Bin0.modulo.sum.right.invariance n 400 400 &zero).
  }
  leibniz &quotient, &remainder in |- *.
  match (Bin0.multiplication.distributivity.over.addition
           days_in_quadricentennium (n /. 400) 1)
    with | left _ end.
  leibniz &left in |- *.
  match (Bin0.multiplication.identity days_in_quadricentennium) with | _ right end.
  leibniz &right in |- *.
  lemma swap
    : forall (u : Bin0) (v : Bin0) .
        (u + days_in_quadricentennium) + v = (u + v) + days_in_quadricentennium.
  {
    intros u v.
    leibniz
      (Bin0.addition.associativity &u days_in_quadricentennium &v),
      (Bin0.addition.commutativity days_in_quadricentennium &v),
      <- (Bin0.addition.associativity &u &v days_in_quadricentennium)
      in |- *.
    quod idem est.
  }
  let a := days_in_quadricentennium * (n /. 400) in |- *.
  let b := days_in_century * ((n %. 400) /. 100) in |- *.
  let c := days_in_quadrennium * (((n %. 400) %. 100) /. 4) in |- *.
  let e := days_in_common_year * (((n %. 400) %. 100) %. 4) in |- *.
  leibniz (&swap &a &b), (&swap (&a + &b) &c), (&swap ((&a + &b) + &c) &e) in |- *.
  quod idem est.
Qed.

(* One more year before [y] carries through the decomposition and stops at
 * one of four levels: the single years, which adds a common year; the
 * quadrennia, a leap year; the centuries, a common century year; the
 * quadricentennia, a leap year divisible by 400. Each level of the carry is
 * the one the leap rule reads for [y].
 *)
(* year.succession *)
Theorem succession
  : forall (y : Year) .
      days_before_year (y + 1)%b = days_before_year y + days_in_year y.
Proof.
  intro y.
  simpl days_before_year in |- *.
  simpl years_in_quadrennium, years_in_century, years_in_quadricentennium in |- *.
  leibniz (year.antecedence.translation &y 1) in |- *.
  let n := years_before &y in |- *.
  let proof restored := year.antecedence.restoration &y.
  let &n in &restored.
  match (Bin0.division.specification n 400) with | _ below400 end.
  match (Bin0.division.specification (n %. 400) 100) with | _ below100 end.
  match (Bin0.division.specification ((n %. 400) %. 100) 4) with | _ below4 end.
  lemma hundred : (n %. 400) %. 100 = n %. 100.
  {
    ipso (Bin0.modulo.nesting n 100 4).
  }
  lemma four : ((n %. 400) %. 100) %. 4 = n %. 4.
  {
    leibniz &hundred in |- *.
    ipso (Bin0.modulo.nesting n 4 25).
  }
  lemma hundred_y : (y %. 400) %. 100 = y %. 100.
  {
    ipso (Bin0.modulo.nesting y 100 4).
  }
  lemma four_y : (y %. 100) %. 4 = y %. 4.
  {
    ipso (Bin0.modulo.nesting y 4 25).
  }
  lemma zero_by_hundred : 0%b0 /. 100 = 0%b0.
  {
    simpl Bin0.divide in |- *.
    simpl in |- *.
    quod idem est.
  }
  lemma zero_mod_hundred : 0%b0 %. 100 = 0%b0.
  {
    simpl Bin0.modulo in |- *.
    simpl in |- *.
    quod idem est.
  }
  lemma zero_by_four : 0%b0 /. 4 = 0%b0.
  {
    simpl Bin0.divide in |- *.
    simpl in |- *.
    quod idem est.
  }
  lemma zero_mod_four : 0%b0 %. 4 = 0%b0.
  {
    simpl Bin0.modulo in |- *.
    simpl in |- *.
    quod idem est.
  }
  lemma last_by_hundred : 399 /. 100 = 3.
  {
    simpl Bin0.divide in |- *.
    simpl in |- *.
    quod idem est.
  }
  lemma last_mod_hundred : 399 %. 100 = 99.
  {
    simpl Bin0.modulo in |- *.
    simpl in |- *.
    quod idem est.
  }
  lemma last_by_four : 99 /. 4 = 24.
  {
    simpl Bin0.divide in |- *.
    simpl in |- *.
    quod idem est.
  }
  lemma last_mod_four : 99 %. 4 = 3.
  {
    simpl Bin0.modulo in |- *.
    simpl in |- *.
    quod idem est.
  }
  match (Bin0.multiplication.annihilation days_in_century) with | _ century_zero end.
  match (Bin0.multiplication.annihilation days_in_quadrennium) with | _ quadrennium_zero end.
  match (Bin0.multiplication.annihilation days_in_common_year) with | _ common_zero end.
  match (Bin0.order.succession (n %. 400) 400 &below400) with | carry400 | interior400 end.
  - (* [y] is divisible by 400. *)
    match (Bin0.division.succession.carry n 400 &carry400) with | q400 r400 end.
    lemma r1 : n %. 400 = 399.
    {
      lemma shifted : (n %. 400) + 1 = 399 + 1.
      {
        ipso &carry400.
      }
      match (Bin0.addition.cancellation (n %. 400) 1 399) with | _ right end.
      ipso (&right &shifted).
    }
    lemma y400 : y %. 400 = 0%b0.
    {
      leibniz <- &restored in |- *.
      ipso &r400.
    }
    lemma y100 : y %. 100 = 0%b0.
    {
      leibniz <- &hundred_y, &y400 in |- *.
      ipso &zero_mod_hundred.
    }
    lemma y4 : y %. 4 = 0%b0.
    {
      leibniz <- &four_y, &y100 in |- *.
      ipso &zero_mod_four.
    }
    lemma length : days_in_year y = 366.
    {
      simpl days_in_year, days_in_leap_year, days_in_common_year, is_leap in |- *.
      simpl years_in_quadrennium, years_in_century, years_in_quadricentennium in |- *.
      leibniz &y4, &y100, &y400 in |- *.
      simpl Comparable.eq, Bin0.compare in |- *.
      simpl in |- *.
      simpl Bin.add in |- *.
      simpl in |- *.
      quod idem est.
    }
    leibniz &q400, &r400, &length, &r1 in |- *.
    leibniz
      &zero_by_hundred, &zero_mod_hundred, &zero_by_four, &zero_mod_four,
      &last_by_hundred, &last_mod_hundred, &last_by_four, &last_mod_four
      in |- *.
    leibniz &century_zero, &quadrennium_zero, &common_zero in |- *.
    match (Bin0.addition.identity (days_in_quadricentennium * ((n /. 400) + 1)))
      with | _ plus_zero end.
    leibniz &plus_zero, &plus_zero, &plus_zero in |- *.
    match (Bin0.multiplication.distributivity.over.addition
             days_in_quadricentennium (n /. 400) 1)
      with | distributed _ end.
    match (Bin0.multiplication.identity days_in_quadricentennium) with | _ times_one end.
    leibniz &distributed, &times_one in |- *.
    leibniz
      (Bin0.addition.associativity
         (((days_in_quadricentennium * (n /. 400)) + (days_in_century * 3))
            + (days_in_quadrennium * 24))
         (days_in_common_year * 3) 366),
      (Bin0.addition.associativity
         ((days_in_quadricentennium * (n /. 400)) + (days_in_century * 3))
         (days_in_quadrennium * 24) ((days_in_common_year * 3) + 366)),
      (Bin0.addition.associativity
         (days_in_quadricentennium * (n /. 400)) (days_in_century * 3)
         ((days_in_quadrennium * 24) + ((days_in_common_year * 3) + 366)))
      in |- *.
    lemma constant
      : (days_in_century * 3) + ((days_in_quadrennium * 24) + ((days_in_common_year * 3) + 366))
        = days_in_quadricentennium.
    {
      simpl days_in_quadricentennium, days_in_century, days_in_quadrennium, days_in_common_year
        in |- *.
      simpl in |- *.
      simpl Bin.add in |- *.
      simpl in |- *.
      quod idem est.
    }
    leibniz &constant in |- *.
    quod idem est.
  - (* [y] is not divisible by 400. *)
    match (Bin0.division.succession.interior n 400 &interior400) with | q400 r400 end.
    lemma y400 : y %. 400 = (n %. 400) + 1.
    {
      leibniz <- &restored in |- *.
      ipso &r400.
    }
    leibniz &q400, &r400 in |- *.
    match (Bin0.order.succession ((n %. 400) %. 100) 100 &below100)
      with | carry100 | interior100 end.
    + (* [y] is divisible by 100 and not by 400. *)
      match (Bin0.division.succession.carry (n %. 400) 100 &carry100) with | q100 r100 end.
      lemma r2 : (n %. 400) %. 100 = 99.
      {
        lemma shifted : ((n %. 400) %. 100) + 1 = 99 + 1.
        {
          ipso &carry100.
        }
        match (Bin0.addition.cancellation ((n %. 400) %. 100) 1 99) with | _ right end.
        ipso (&right &shifted).
      }
      lemma carry100n : (n %. 100) + 1 = 100.
      {
        leibniz <- &hundred in |- *.
        ipso &carry100.
      }
      match (Bin0.division.succession.carry n 100 &carry100n) with | _ r100n end.
      lemma y100 : y %. 100 = 0%b0.
      {
        leibniz <- &restored in |- *.
        ipso &r100n.
      }
      lemma y4 : y %. 4 = 0%b0.
      {
        leibniz <- &four_y, &y100 in |- *.
        ipso &zero_mod_four.
      }
      lemma length : days_in_year y = 365.
      {
        simpl days_in_year, days_in_leap_year, days_in_common_year, is_leap in |- *.
        simpl years_in_quadrennium, years_in_century, years_in_quadricentennium in |- *.
        leibniz &y4, &y100, &y400 in |- *.
        match (n %. 400) with | | p end;
          simpl Comparable.eq, Bin0.compare in |- *; simpl in |- *; quod idem est.
      }
      leibniz &q100, &r100, &r2, &length in |- *.
      leibniz &zero_by_four, &zero_mod_four, &last_by_four, &last_mod_four in |- *.
      leibniz &quadrennium_zero, &common_zero in |- *.
      match (Bin0.addition.identity
               ((days_in_quadricentennium * (n /. 400))
                  + (days_in_century * (((n %. 400) /. 100) + 1))))
        with | _ plus_zero end.
      leibniz &plus_zero, &plus_zero in |- *.
      match (Bin0.multiplication.distributivity.over.addition
               days_in_century ((n %. 400) /. 100) 1)
        with | distributed _ end.
      match (Bin0.multiplication.identity days_in_century) with | _ times_one end.
      leibniz &distributed, &times_one in |- *.
      leibniz
        <- (Bin0.addition.associativity
              (days_in_quadricentennium * (n /. 400))
              (days_in_century * ((n %. 400) /. 100)) days_in_century),
        (Bin0.addition.associativity
           (((days_in_quadricentennium * (n /. 400)) + (days_in_century * ((n %. 400) /. 100)))
              + (days_in_quadrennium * 24))
           (days_in_common_year * 3) 365),
        (Bin0.addition.associativity
           ((days_in_quadricentennium * (n /. 400)) + (days_in_century * ((n %. 400) /. 100)))
           (days_in_quadrennium * 24) ((days_in_common_year * 3) + 365))
        in |- *.
      lemma constant
        : (days_in_quadrennium * 24) + ((days_in_common_year * 3) + 365) = days_in_century.
      {
        simpl days_in_century, days_in_quadrennium, days_in_common_year in |- *.
        simpl in |- *.
        simpl Bin.add in |- *.
        simpl in |- *.
        quod idem est.
      }
      leibniz &constant in |- *.
      quod idem est.
    + (* [y] is not divisible by 100. *)
      match (Bin0.division.succession.interior (n %. 400) 100 &interior100)
        with | q100 r100 end.
      leibniz &q100, &r100 in |- *.
      lemma interior100n : (n %. 100) + 1 < 100.
      {
        leibniz <- &hundred in |- *.
        ipso &interior100.
      }
      match (Bin0.division.succession.interior n 100 &interior100n) with | _ r100n end.
      lemma y100 : y %. 100 = (n %. 100) + 1.
      {
        leibniz <- &restored in |- *.
        ipso &r100n.
      }
      match (Bin0.order.succession (((n %. 400) %. 100) %. 4) 4 &below4)
        with | carry4 | interior4 end.
      * (* [y] is divisible by 4 and not by 100. *)
        match (Bin0.division.succession.carry ((n %. 400) %. 100) 4 &carry4)
          with | q4 r4 end.
        lemma r3 : ((n %. 400) %. 100) %. 4 = 3.
        {
          lemma shifted : (((n %. 400) %. 100) %. 4) + 1 = 3 + 1.
          {
            ipso &carry4.
          }
          match (Bin0.addition.cancellation (((n %. 400) %. 100) %. 4) 1 3)
            with | _ right end.
          ipso (&right &shifted).
        }
        lemma carry4n : (n %. 4) + 1 = 4.
        {
          leibniz <- &four in |- *.
          ipso &carry4.
        }
        match (Bin0.division.succession.carry n 4 &carry4n) with | _ r4n end.
        lemma y4 : y %. 4 = 0%b0.
        {
          leibniz <- &restored in |- *.
          ipso &r4n.
        }
        lemma length : days_in_year y = 366.
        {
          simpl days_in_year, days_in_leap_year, days_in_common_year, is_leap in |- *.
          simpl years_in_quadrennium, years_in_century, years_in_quadricentennium in |- *.
          leibniz &y4, &y100 in |- *.
          match (n %. 100) with | | p end;
            simpl Comparable.eq, Bin0.compare in |- *; simpl in |- *;
            simpl Bin.add in |- *; simpl in |- *; quod idem est.
        }
        leibniz &q4, &r4, &r3, &length in |- *.
        leibniz &common_zero in |- *.
        match (Bin0.addition.identity
                 (((days_in_quadricentennium * (n /. 400))
                     + (days_in_century * ((n %. 400) /. 100)))
                    + (days_in_quadrennium * ((((n %. 400) %. 100) /. 4) + 1))))
          with | _ plus_zero end.
        leibniz &plus_zero in |- *.
        match (Bin0.multiplication.distributivity.over.addition
                 days_in_quadrennium (((n %. 400) %. 100) /. 4) 1)
          with | distributed _ end.
        match (Bin0.multiplication.identity days_in_quadrennium) with | _ times_one end.
        leibniz &distributed, &times_one in |- *.
        leibniz
          <- (Bin0.addition.associativity
                ((days_in_quadricentennium * (n /. 400))
                   + (days_in_century * ((n %. 400) /. 100)))
                (days_in_quadrennium * (((n %. 400) %. 100) /. 4)) days_in_quadrennium),
          (Bin0.addition.associativity
             (((days_in_quadricentennium * (n /. 400))
                 + (days_in_century * ((n %. 400) /. 100)))
                + (days_in_quadrennium * (((n %. 400) %. 100) /. 4)))
             (days_in_common_year * 3) 366)
          in |- *.
        lemma constant : (days_in_common_year * 3) + 366 = days_in_quadrennium.
        {
          simpl days_in_quadrennium, days_in_common_year in |- *.
          simpl in |- *.
          simpl Bin.add in |- *.
          simpl in |- *.
          quod idem est.
        }
        leibniz &constant in |- *.
        quod idem est.
      * (* [y] is not divisible by 4. *)
        match (Bin0.division.succession.interior ((n %. 400) %. 100) 4 &interior4)
          with | q4 r4 end.
        lemma interior4n : (n %. 4) + 1 < 4.
        {
          leibniz <- &four in |- *.
          ipso &interior4.
        }
        match (Bin0.division.succession.interior n 4 &interior4n) with | _ r4n end.
        lemma y4 : y %. 4 = (n %. 4) + 1.
        {
          leibniz <- &restored in |- *.
          ipso &r4n.
        }
        lemma length : days_in_year y = 365.
        {
          simpl days_in_year, days_in_leap_year, days_in_common_year, is_leap in |- *.
          simpl years_in_quadrennium, years_in_century, years_in_quadricentennium in |- *.
          leibniz &y4 in |- *.
          match (n %. 4) with | | p end;
            simpl Comparable.eq, Bin0.compare in |- *; simpl in |- *; quod idem est.
        }
        leibniz &q4, &r4, &length in |- *.
        match (Bin0.multiplication.distributivity.over.addition
                 days_in_common_year (((n %. 400) %. 100) %. 4) 1)
          with | distributed _ end.
        match (Bin0.multiplication.identity days_in_common_year) with | _ times_one end.
        leibniz &distributed, &times_one in |- *.
        leibniz
          <- (Bin0.addition.associativity
                (((days_in_quadricentennium * (n /. 400))
                    + (days_in_century * ((n %. 400) /. 100)))
                   + (days_in_quadrennium * (((n %. 400) %. 100) /. 4)))
                (days_in_common_year * (((n %. 400) %. 100) %. 4)) days_in_common_year)
          in |- *.
        simpl days_in_common_year in |- *.
        quod idem est.
Qed.

(* The days through a year are at most the days before any later year: by
 * induction on how many years later, each one adding a year's length by
 * [year.succession].
 *)
(* year.monotonicity *)
Theorem monotonicity
  : forall (y : Year) (k : Bin) .
      days_before_year y + days_in_year y <= days_before_year (y + k)%b.
Proof.
  intros y k.
  leibniz <- (Bin.conversion.section &k) in |- *.
  let n := Bin.to_nat &k in |- *.
  let proof n := &n.
  extro &n.
  intro n.
  match &n with | One | Successor (n' by IH) end per Nat.induction.
  - lemma facto : days_before_year y + days_in_year y <= days_before_year (y + 1)%b.
    {
      leibniz (year.succession &y) in |- *.
      ipso (disjoin (refl (days_before_year &y + days_in_year &y)), _).
    }
    ipso &facto.
  - lemma shift : forall (b : Bin) . (y + (++ b))%b = ((y + b) + 1)%b.
    {
      intro b.
      lemma facto : Bin.to_nat (y + (++ b))%b = Bin.to_nat ((y + b) + 1)%b.
      {
        leibniz
          (Bin.conversion.addition &y (++ &b)%b),
          (Bin.conversion.successor &b),
          (Bin.conversion.addition (&y + &b)%b 1),
          (Bin.conversion.addition &y &b)
          in |- *.
        leibniz
          (Nat.addition.right.successor (Bin.to_nat &y) (Bin.to_nat &b)),
          (Nat.addition.commutativity
             (Bin.to_nat &y + Bin.to_nat &b)%n (Bin.to_nat 1))
          in |- *.
        simpl in |- *.
        quod idem est.
      }
      ipso (Bin.conversion.injectivity &facto).
    }
    lemma extended
      : days_before_year (y + Bin.from_nat n')%b
        <= days_before_year (y + Bin.from_nat n')%b
           + days_in_year (y + Bin.from_nat n')%b.
    {
      leibniz
        (Bin0.addition.commutativity
           (days_before_year (&y + Bin.from_nat &n')%b)
           (days_in_year (&y + Bin.from_nat &n')%b))
        in |- *.
      ipso (Bin0.addition.right.order.extensivity
              (days_in_year (&y + Bin.from_nat &n')%b)
              (days_before_year (&y + Bin.from_nat &n')%b)).
    }
    lemma step
      : days_before_year y + days_in_year y
        <= days_before_year ((y + Bin.from_nat n') + 1)%b.
    {
      leibniz (year.succession (&y + Bin.from_nat &n')%b) in |- *.
      ipso (@Comparable.order.transitivity _ Bin0.compare Bin0.LessThan _
              (days_before_year &y + days_in_year &y)
              (days_before_year (&y + Bin.from_nat &n')%b)
              (days_before_year (&y + Bin.from_nat &n')%b
                 + days_in_year (&y + Bin.from_nat &n')%b)
              &IH &extended).
    }
    lemma facto
      : days_before_year y + days_in_year y
        <= days_before_year (y + (++ Bin.from_nat n'))%b.
    {
      leibniz (&shift (Bin.from_nat &n')) in |- *.
      ipso &step.
    }
    ipso &facto.
Qed.

End year. (* year *)

Module calendar. (* calendar *)

(* The months are tried from December down, so the month found is the last
 * that has begun by the date, and the date comes before the next one begins.
 *)
(* calendar.boundedness *)
Theorem boundedness
  : forall (y : Year) (days : Days) .
      days < days_in_year y
      -> days_before_month y (month_after_days y days) <= days
         /\ days
            < days_before_month y (month_after_days y days)
              + days_in_month y (month_after_days y days).
Proof.
  intros y days h.
  lemma placed
    : forall (m : Month) .
        Bin0.le (days_before_month y m) days = true
        -> days < days_before_month y m + days_in_month y m
        -> days_before_month y m <= days /\ days < days_before_month y m + days_in_month y m.
  {
    intros m after before.
    ipso (conjoin
            (modus aequans (Comparable.order.reflection (days_before_month &y &m) &days), &after),
            &before).
  }
  lemma below : forall (x : Bin0) . Bin0.le x days = false -> days < x.
  {
    intros x f.
    match (Comparable.order.strict.trichotomy days x) with | smaller | rest end.
    - ipso &smaller.
    - lemma reached : x <= days.
      {
        match &rest with | same | greater end.
        - ipso (disjoin (symm &same), _).
        - ipso (disjoin _, &greater).
      }
      let proof t := modus aequans (Comparable.order.reflection &x &days), &reached.
      leibniz &f in &t.
      ex &t quodlibet.
  }
  lemma first : Bin0.le (days_before_month y Month.January) days = true.
  {
    simpl days_before_month, Comparable.le, Bin0.compare in |- *.
    match &days with | | p end; quod idem est.
  }
  lemma last : days < days_before_month y Month.December + days_in_month y Month.December.
  {
    leibniz <- (month.completion &y) in &h.
    ipso &h.
  }
  simpl month_after_days, calendar_date_after_days in |- *.
  match (Bin0.le (days_before_month y Month.December) days) with | | end |- december.
  {
    ipso (&placed Month.December &december &last).
  }
  match (Bin0.le (days_before_month y Month.November) days) with | | end |- november.
  {
    ipso (&placed Month.November &november (&below _ &december)).
  }
  match (Bin0.le (days_before_month y Month.October) days) with | | end |- october.
  {
    ipso (&placed Month.October &october (&below _ &november)).
  }
  match (Bin0.le (days_before_month y Month.September) days) with | | end |- september.
  {
    ipso (&placed Month.September &september (&below _ &october)).
  }
  match (Bin0.le (days_before_month y Month.August) days) with | | end |- august.
  {
    ipso (&placed Month.August &august (&below _ &september)).
  }
  match (Bin0.le (days_before_month y Month.July) days) with | | end |- july.
  {
    ipso (&placed Month.July &july (&below _ &august)).
  }
  match (Bin0.le (days_before_month y Month.June) days) with | | end |- june.
  {
    ipso (&placed Month.June &june (&below _ &july)).
  }
  match (Bin0.le (days_before_month y Month.May) days) with | | end |- may.
  {
    ipso (&placed Month.May &may (&below _ &june)).
  }
  match (Bin0.le (days_before_month y Month.April) days) with | | end |- april.
  {
    ipso (&placed Month.April &april (&below _ &may)).
  }
  match (Bin0.le (days_before_month y Month.March) days) with | | end |- march.
  {
    ipso (&placed Month.March &march (&below _ &april)).
  }
  match (Bin0.le (days_before_month y Month.February) days) with | | end |- february.
  {
    ipso (&placed Month.February &february (&below _ &march)).
  }
  ipso (&placed Month.January &first (&below _ &february)).
Qed.

(* calendar.validity *)
Theorem validity
  : forall (y : Year) (days : Days) .
      days < days_in_year y
      -> Assert (is_valid y (month_after_days y days) (day_of_month_after_days y days)).
Proof.
  intros y days h.
  match (calendar.boundedness &y &days &h) with | started before end.
  lemma facto
    : Assert
        (is_valid y (month_after_days y days)
           (Bin0.successor
              (Bin0.saturating_sub days (days_before_month y (month_after_days y days))))).
  {
    simpl is_valid in |- *.
    let m := month_after_days y days in &started, &before |- *.
    let proof m := &m.
    let c := days_before_month y m in &started, &before |- *.
    let proof c := &c.
    let k := days_in_month y m in &before |- *.
    let proof k := &k.
    let proof restored := Bin0.subtraction.saturating.specification &started.
    let s := Bin0.saturating_sub days c in &restored |- *.
    let proof s := &s.
    lemma inside : s < k.
    {
      leibniz <- &restored in &before.
      match &before with | j e end.
      simpl Bin0.LessThan in |- *.
      exists &j.
      leibniz (Bin0.addition.associativity &c &s (Bin0.Positive &j)) in &e.
      match (Bin0.addition.cancellation &c (&s + Bin0.Positive &j) (Bin0.Positive &k))
        with | left _ end.
      ipso (&left &e).
    }
    let proof fits := Bin0.order.succession &s (Bin0.Positive &k) &inside.
    leibniz <- (Bin0.successor.specification &s) in &fits.
    let proof checked :=
      modus aequans
        (Comparable.order.reflection (Bin0.Positive (Bin0.successor &s)) (Bin0.Positive &k)),
        &fits.
    ipso (modus aequans (Assert.specification _), &checked).
  }
  ipso facto.
Qed.

Module ordinal. (* calendar.ordinal *)

(* The day of the year [d] counts from 1, so [d - 1] days of [y] come
 * before it.
 *)
(* calendar.ordinal.validity *)
Theorem validity
  : forall (y : Year) (d : Day) .
      Assert (Comparable.le Bin.compare d (days_in_year y))
      -> Assert
           (is_valid y
              (month_after_days y (Bin0.saturating_sub d 1))
              (day_of_month_after_days y (Bin0.saturating_sub d 1))).
Proof.
  intros y d a.
  let proof t := modus aequans (Assert.specification _), &a.
  let proof b := modus aequans (Comparable.order.reflection &d (days_in_year &y)), &t.
  lemma within : (d : Bin0) <= days_in_year y.
  {
    match &b with | e | s end.
    - ipso (disjoin (congru Bin0.Positive, &e), _).
    - match &s with | k e end.
      lemma facto : (d : Bin0) < days_in_year y.
      {
        simpl Bin0.LessThan in |- *.
        exists &k.
        ipso (congru Bin0.Positive, &e).
      }
      ipso (disjoin _, &facto).
  }
  lemma earlier : Bin0.saturating_sub d 1 < d.
  {
    simpl Bin0.LessThan in |- *.
    exists 1.
    ipso (year.antecedence.restoration &d).
  }
  ipso (calendar.validity &y (Bin0.saturating_sub d 1)
          (@Comparable.order.mixed.right.transitivity _ Bin0.compare Bin0.LessThan _
             (Bin0.saturating_sub d 1) (Bin0.Positive &d) (Bin0.Positive (days_in_year &y))
             &earlier &within)).
Qed.

End ordinal. (* calendar.ordinal *)

(* The month search finds the month of a valid date back: no other month
 * holds the days before the date, by [month.monotonicity].
 *)
(* calendar.inversion *)
Theorem inversion
  : forall (y : Year) (m : Month) (d : Day) .
      Assert (is_valid y m d)
      -> calendar_date_after_days y (days_before_month y m + Bin0.saturating_sub d 1) = (m, d).
Proof.
  intros y m d a.
  simpl is_valid in &a.
  let proof t := modus aequans (Assert.specification _), &a.
  let proof b := modus aequans (Comparable.order.reflection &d (days_in_month &y &m)), &t.
  lemma fits : (d : Bin0) <= days_in_month y m.
  {
    match &b with | e | s end.
    - ipso (disjoin (congru Bin0.Positive, &e), _).
    - match &s with | k e end.
      lemma facto : (d : Bin0) < days_in_month y m.
      {
        simpl Bin0.LessThan in |- *.
        exists &k.
        ipso (congru Bin0.Positive, &e).
      }
      ipso (disjoin _, &facto).
  }
  lemma earlier : Bin0.saturating_sub d 1 < d.
  {
    simpl Bin0.LessThan in |- *.
    exists 1.
    ipso (year.antecedence.restoration &d).
  }
  let s := Bin0.saturating_sub d 1 in &earlier |- *.
  let proof restored : s + 1 = d := year.antecedence.restoration &d.
  let c := days_before_month y m in |- *.
  lemma lower : c <= c + s.
  {
    leibniz (Bin0.addition.commutativity &c &s) in |- *.
    ipso (Bin0.addition.right.order.extensivity &s &c).
  }
  lemma upper : c + s < c + days_in_month y m.
  {
    ipso (Bin0.addition.order.strict.monotonicity &c &s &c (days_in_month &y &m)
            (disjoin (refl &c), _)
            (@Comparable.order.mixed.right.transitivity _ Bin0.compare Bin0.LessThan _
               &s (Bin0.Positive &d) (Bin0.Positive (days_in_month &y &m)) &earlier &fits)).
  }
  lemma inside : c + s < days_in_year y.
  {
    ipso (@Comparable.order.mixed.right.transitivity _ Bin0.compare Bin0.LessThan _
            (&c + &s) (&c + days_in_month &y &m) (Bin0.Positive (days_in_year &y))
            &upper (month.boundedness &y &m)).
  }
  match (calendar.boundedness &y (&c + &s) &inside) with | started before end.
  lemma same : month_after_days y (c + s) = m.
  {
    match (Month.compare &m (month_after_days &y (&c + &s))) with | | | end |- order.
    - let proof through := month.monotonicity &y &m (month_after_days &y (&c + &s)) &order.
      let proof reached :=
        @Comparable.order.transitivity _ Bin0.compare Bin0.LessThan _
          (days_before_month &y &m + days_in_month &y &m)
          (days_before_month &y (month_after_days &y (&c + &s)))
          (&c + &s)
          &through &started.
      let proof loop := Comparable.order.mixed.left.transitivity &reached &upper.
      ex (Bin0.order.strict.irreflexivity (&c + days_in_month &y &m) &loop) quodlibet.
    - match (Month.comparison.specification &m (month_after_days &y (&c + &s)))
        with | _ equality end.
      ipso (symm (modus aequans &equality, &order)).
    - lemma reversed : Month.compare (month_after_days y (c + s)) m = Comparison.Lt.
      {
        leibniz (Month.comparison.antisymmetry (month_after_days &y (&c + &s)) &m), &order
          in |- *.
        simpl in |- *.
        quod idem est.
      }
      let proof through := month.monotonicity &y (month_after_days &y (&c + &s)) &m &reversed.
      let proof reached :=
        @Comparable.order.transitivity _ Bin0.compare Bin0.LessThan _
          (days_before_month &y (month_after_days &y (&c + &s))
             + days_in_month &y (month_after_days &y (&c + &s)))
          &c (&c + &s)
          &through &lower.
      let proof loop := Comparable.order.mixed.left.transitivity &reached &before.
      ex (Bin0.order.strict.irreflexivity
            (days_before_month &y (month_after_days &y (&c + &s))
               + days_in_month &y (month_after_days &y (&c + &s)))
            &loop)
        quodlibet.
  }
  lemma day : Bin0.successor (Bin0.saturating_sub (c + s) c) = d.
  {
    leibniz (Bin0.addition.commutativity &c &s) in |- *.
    leibniz (Bin0.subtraction.saturating.inversion.addition &s &c) in |- *.
    lemma lifted : Bin0.Positive (Bin0.successor s) = Bin0.Positive d.
    {
      leibniz (Bin0.successor.specification &s) in |- *.
      ipso &restored.
    }
    let proof f :
      Bin0.successor s = d
      := congru (fun (z : Bin0) . match z with | Bin0.Zero => Bin.One | Bin0.Positive p => p end),
           &lifted.
    ipso &f.
  }
  lemma pair
    : calendar_date_after_days y (c + s)
      = (month_after_days y (c + s),
         Bin0.successor
           (Bin0.saturating_sub (c + s) (days_before_month y (month_after_days y (c + s))))).
  {
    ipso (refl (calendar_date_after_days &y (&c + &s))).
  }
  leibniz &pair, &same in |- *.
  let &c in |- *.
  leibniz &day in |- *.
  quod idem est.
Qed.

(* The days before the month the search finds, and the days of that month
 * before the date, are the days the search started from.
 *)
(* calendar.reconstruction *)
Theorem reconstruction
  : forall (y : Year) (days : Days) .
      days < days_in_year y
      -> days_before_month y (month_after_days y days)
           + Bin0.saturating_sub (day_of_month_after_days y days) 1
         = days.
Proof.
  intros y days h.
  match (calendar.boundedness &y &days &h) with | started _ end.
  lemma facto
    : days_before_month y (month_after_days y days)
        + Bin0.saturating_sub
            (Bin0.successor
               (Bin0.saturating_sub days (days_before_month y (month_after_days y days))))
            1
      = days.
  {
    let proof restored := Bin0.subtraction.saturating.specification &started.
    let s := Bin0.saturating_sub days (days_before_month y (month_after_days y days))
      in &restored |- *.
    let proof s := &s.
    leibniz
      (Bin0.successor.specification &s),
      (Bin0.subtraction.saturating.inversion.addition &s 1)
      in |- *.
    ipso &restored.
  }
  ipso facto.
Qed.

End calendar. (* calendar *)

Module division. (* division *)

Module clamped. (* division.clamped *)

Module remainder. (* division.clamped.remainder *)

(* The remainder is below [d], except when [r] is [4 * d], the one case the
 * clamp changes.
 *)
(* division.clamped.remainder.boundedness *)
Lemma boundedness
  : forall (r : Bin0) (d : Bin) .
      r < (4 * d) + 1
      -> pi_2 (div_clamped_at_3 r d) < d
         \/ (r = 4 * d /\ pi_2 (div_clamped_at_3 r d) = d /\ pi_1 (div_clamped_at_3 r d) = 3).
Proof.
  intros r d h.
  lemma discreteness : forall (x : Bin0) (y : Bin0) . x < y + 1 -> x <= y.
  {
    intros x y g.
    match (Comparable.order.strict.trichotomy x y) with | smaller | rest end.
    - ipso (disjoin _, &smaller).
    - match &rest with | same | greater end.
      + ipso (disjoin &same, _).
      + let proof after := Bin0.order.succession &y &x &greater.
        let proof loop := Comparable.order.mixed.left.transitivity &after &g.
        ex (Bin0.order.strict.irreflexivity (&y + 1) &loop) quodlibet.
  }
  simpl div_clamped_at_3 in |- *.
  simpl Product.first, Product.second, Comparable.min in |- *.
  match (Bin0.division.specification r d) with | reconstruction bounded end.
  lemma swapped : r = (r %. d) + ((r /. d) * d).
  {
    leibniz (Bin0.addition.commutativity (r %. d) ((r /. d) * d)), &reconstruction in |- *.
    quod idem est.
  }
  lemma remainder : Bin0.saturating_sub r ((r /. d) * d) < d.
  {
    let proof inverted :=
      Bin0.subtraction.saturating.inversion.addition (r %. d) ((r /. d) * d).
    leibniz <- &swapped in &inverted.
    leibniz &inverted in |- *.
    ipso &bounded.
  }
  match (Bin0.compare (r /. d) 3) with | | | end |- c.
  - ipso (disjoin &remainder, _).
  - ipso (disjoin &remainder, _).
  - lemma reversed : Bin0.compare 3 (r /. d) = Comparison.Lt.
    {
      leibniz (Bin0.comparison.antisymmetry 3 (r /. d)), &c in |- *.
      simpl in |- *.
      quod idem est.
    }
    match (Bin0.comparison.specification 3 (r /. d)) with | strict _ end.
    let proof three := modus aequans &strict, &reversed.
    let proof four := Bin0.order.succession 3 (r /. d) &three.
    lemma positive : 0%b0 < d.
    {
      simpl Bin0.LessThan in |- *.
      exists &d.
      simpl in |- *.
      quod idem est.
    }
    lemma scaled : 4 * d <= (r /. d) * d.
    {
      match &four with | same | smaller end.
      - leibniz <- &same in |- *.
        ipso (disjoin (refl (4 * d)), _).
      - let proof f :=
          Bin0.multiplication.left.order.strict.monotonicity d 4 (r /. d) &positive &smaller.
        leibniz
          (Bin0.multiplication.commutativity d 4),
          (Bin0.multiplication.commutativity d (r /. d))
          in &f.
        ipso (disjoin _, &f).
    }
    lemma widened : (r /. d) * d <= r.
    {
      let proof f := Bin0.addition.right.order.extensivity (r %. d) ((r /. d) * d).
      leibniz <- &swapped in &f.
      ipso &f.
    }
    lemma equal : r = 4 * d.
    {
      ipso (@Comparable.order.antisymmetry _ Bin0.compare Bin0.LessThan _ r (4 * d)
              (&discreteness r (4 * d) &h)
              (@Comparable.order.transitivity _ Bin0.compare Bin0.LessThan _
                 (4 * d) ((r /. d) * d) r &scaled &widened)).
    }
    lemma split : 4 * d = d + (3 * d).
    {
      match (Bin0.multiplication.distributivity.over.addition d 1 3) with | _ right end.
      match (Bin0.multiplication.identity d) with | left _ end.
      leibniz &left in &right.
      ipso &right.
    }
    lemma facto : r = 4 * d /\ Bin0.saturating_sub r (3 * d) = d /\ (3 : Bin0) = 3.
    {
      divide et impera.
      - ipso &equal.
      - divide et impera.
        + leibniz &equal, &split in |- *.
          ipso (Bin0.subtraction.saturating.inversion.addition d (3 * d)).
        + quod idem est.
    }
    ipso (disjoin _, &facto).
Qed.

End remainder. (* division.clamped.remainder *)

Module dividend. (* division.clamped.dividend *)

(* division.clamped.dividend.reconstruction *)
Lemma reconstruction
  : forall (r : Bin0) (d : Bin) .
      (pi_1 (div_clamped_at_3 r d) * d) + pi_2 (div_clamped_at_3 r d) = r.
Proof.
  intros r d.
  simpl div_clamped_at_3 in |- *.
  simpl Product.first, Product.second in |- *.
  let q := Bin0.min (r /. d) 3 in |- *.
  lemma below : q <= r /. d.
  {
    ipso (@Comparable.minimum.left.projection _ Bin0.compare Bin0.LessThan _ (r /. d) 3).
  }
  let proof q := &q.
  lemma positive : 0%b0 < d.
  {
    simpl Bin0.LessThan in |- *.
    exists &d.
    simpl in |- *.
    quod idem est.
  }
  lemma scaled : q * d <= (r /. d) * d.
  {
    match &below with | same | smaller end.
    - leibniz &same in |- *.
      ipso (disjoin (refl ((r /. d) * d)), _).
    - let proof f :=
        Bin0.multiplication.left.order.strict.monotonicity d &q (r /. d) &positive &smaller.
      leibniz
        (Bin0.multiplication.commutativity d &q),
        (Bin0.multiplication.commutativity d (r /. d))
        in &f.
      ipso (disjoin _, &f).
  }
  match (Bin0.division.specification r d) with | reconstruction _ end.
  lemma widened : (r /. d) * d <= r.
  {
    let proof f := Bin0.addition.right.order.extensivity (r %. d) ((r /. d) * d).
    leibniz (Bin0.addition.commutativity (r %. d) ((r /. d) * d)), &reconstruction in &f.
    ipso &f.
  }
  ipso (Bin0.subtraction.saturating.specification
          (@Comparable.order.transitivity _ Bin0.compare Bin0.LessThan _
             (&q * d) ((r /. d) * d) r &scaled &widened)).
Qed.

End dividend. (* division.clamped.dividend *)

Module quotient. (* division.clamped.quotient *)

(* division.clamped.quotient.boundedness *)
Lemma boundedness : forall (r : Bin0) (d : Bin) . pi_1 (div_clamped_at_3 r d) <= 3.
Proof.
  intros r d.
  simpl div_clamped_at_3 in |- *.
  simpl Product.first in |- *.
  ipso (@Comparable.minimum.right.projection _ Bin0.compare Bin0.LessThan _ (r /. d) 3).
Qed.

End quotient. (* division.clamped.quotient *)

End clamped. (* division.clamped *)

(* Only the last day of a quadrennium reaches day 365 of its year, and that
 * year is leap: it ends a quadrennium, and when it also ends a century, the
 * century is the last of a quadricentennium.
 *)
(* division.boundedness *)
Theorem boundedness
  : forall (n : Days) .
      pi_2 (div_year n) < days_in_year (Bin0.successor (pi_1 (div_year n))).
Proof.
  intro n.
  lemma absorption : forall (k : Bin) (a : Bin0) (b : Bin0) . ((k * a) + b) %. k = b %. k.
  {
    intros k a b.
    lemma whole : (Bin0.Positive k) %. k = 0%b0.
    {
      lemma once : (1 * k) + 0%b0 = Bin0.Positive k /\ 0%b0 < k.
      {
        divide et impera.
        - match (Bin0.multiplication.identity k) with | left _ end.
          leibniz &left in |- *.
          match (Bin0.addition.identity k) with | _ right end.
          ipso &right.
        - simpl Bin0.LessThan in |- *.
          exists &k.
          simpl in |- *.
          quod idem est.
      }
      match (Bin0.division.uniqueness (Bin0.Positive k) k 1 0%b0 &once) with | _ r end.
      ipso &r.
    }
    lemma empty : 0%b0 %. k = 0%b0.
    {
      simpl Bin0.modulo in |- *.
      simpl in |- *.
      quod idem est.
    }
    leibniz
      <- (Bin0.modulo.sum.left.absorption (k * a) b k),
      <- (Bin0.modulo.product.left.absorption k a k),
      &whole
      in |- *.
    match (Bin0.multiplication.annihilation a) with | left _ end.
    leibniz &left, &empty in |- *.
    match (Bin0.addition.identity b) with | plus_zero _ end.
    leibniz &plus_zero in |- *.
    quod idem est.
  }
  lemma facto
    : pi_2 (div_clamped_at_3 (pi_2 (div_clamped_at_3 (n %. 146097) 36524) %. 1461) 365)
      < days_in_year
          (Bin0.successor
             ((400 * (n /. 146097))
                + (100 * pi_1 (div_clamped_at_3 (n %. 146097) 36524))
                + (4 * (pi_2 (div_clamped_at_3 (n %. 146097) 36524) /. 1461))
                + pi_1
                    (div_clamped_at_3 (pi_2 (div_clamped_at_3 (n %. 146097) 36524) %. 1461) 365))).
  {
    match (Bin0.division.specification n 146097) with | _ bounded400 end.
    let proof clamped100 :=
      division.clamped.remainder.boundedness (n %. 146097) 36524 &bounded400.
    let q400 := n /. 146097 in |- *.
    let proof q400 := &q400.
    let r400 := n %. 146097 in &clamped100 |- *.
    let proof r400 := &r400.
    let C := div_clamped_at_3 r400 36524 in &clamped100 |- *.
    let proof C := &C.
    let r100 := pi_2 C in &clamped100 |- *.
    let proof r100 := &r100.
    let c := pi_1 C in &clamped100 |- *.
    let proof c := &c.
    match (Bin0.division.specification r100 1461) with | e4 bounded4 end.
    let proof clamped4 := division.clamped.remainder.boundedness (r100 %. 1461) 365 &bounded4.
    let Y := div_clamped_at_3 (r100 %. 1461) 365 in &clamped4 |- *.
    let proof Y := &Y.
    let r1 := pi_2 Y in &clamped4 |- *.
    let proof r1 := &r1.
    let c1 := pi_1 Y in &clamped4 |- *.
    let proof c1 := &c1.
    let q4 := r100 /. 1461 in &e4 |- *.
    let proof q4 := &q4.
    let r4 := r100 %. 1461 in &e4, &clamped4.
    let proof r4 := &r4.
    rm &Y &C &bounded400 &bounded4.
    lemma common_below_leap : (365 : Bin0) < 366.
    {
      simpl Bin0.LessThan in |- *.
      exists 1.
      simpl in |- *.
      simpl Bin.add in |- *.
      simpl in |- *.
      quod idem est.
    }
    match &clamped4 with | short | full end.
    - let y := Bin0.successor ((((400 * q400) + (100 * c)) + (4 * q4)) + c1) in |- *.
      let proof y := &y.
      match (year.length.dichotomy &y) with | common | leap end.
      + leibniz &common in |- *.
        ipso &short.
      + leibniz &leap in |- *.
        ipso (Bin0.order.strict.transitivity &short &common_below_leap).
    - match &full with | four_years rest end.
      match &rest with | last_day third end.
      leibniz &last_day, &third in |- *.
      lemma leap : is_leap (Bin0.successor ((((400 * q400) + (100 * c)) + (4 * q4)) + 3)) = true.
      {
        simpl is_leap in |- *.
        simpl years_in_quadrennium, years_in_century, years_in_quadricentennium in |- *.
        leibniz (Bin0.successor.specification ((((400 * q400) + (100 * c)) + (4 * q4)) + 3))
          in |- *.
        lemma shape
          : ((((400 * q400) + (100 * c)) + (4 * q4)) + 3) + 1
            = (400 * q400) + ((100 * c) + ((4 * q4) + (3 + 1))).
        {
          leibniz
            (Bin0.addition.associativity (((400 * &q400) + (100 * &c)) + (4 * &q4)) 3 1),
            (Bin0.addition.associativity ((400 * &q400) + (100 * &c)) (4 * &q4) (3 + 1)),
            (Bin0.addition.associativity (400 * &q400) (100 * &c) ((4 * &q4) + (3 + 1)))
            in |- *.
          quod idem est.
        }
        leibniz &shape in |- *.
        let X := (100 * c) + ((4 * q4) + (3 + 1)) in |- *.
        let N := (400 * q400) + X in |- *.
        lemma y400 : N %. 400 = X %. 400.
        {
          ipso (&absorption 400 &q400 &X).
        }
        let proof y100 : (N %. 400) %. 100 = N %. 100 := Bin0.modulo.nesting &N 100 4.
        leibniz &y400 in &y100.
        let proof outer100 : (X %. 400) %. 100 = X %. 100 := Bin0.modulo.nesting &X 100 4.
        leibniz &outer100 in &y100.
        let proof y4 : (N %. 100) %. 4 = N %. 4 := Bin0.modulo.nesting &N 4 25.
        leibniz <- &y100 in &y4.
        let proof outer4 : (X %. 100) %. 4 = X %. 4 := Bin0.modulo.nesting &X 4 25.
        leibniz &outer4 in &y4.
        let V := (4 * q4) + (3 + 1) in &X.
        lemma x100 : X %. 100 = V %. 100.
        {
          ipso (&absorption 100 &c &V).
        }
        lemma v4 : V %. 4 = 0%b0.
        {
          simpl &V in |- *.
          leibniz (&absorption 4 &q4 (3 + 1)) in |- *.
          simpl Bin0.modulo in |- *.
          simpl in |- *.
          quod idem est.
        }
        lemma n4 : N %. 4 = 0%b0.
        {
          leibniz <- &y4, <- &outer4, &x100 in |- *.
          let proof nested : (V %. 100) %. 4 = V %. 4 := Bin0.modulo.nesting &V 4 25.
          leibniz &nested, &v4 in |- *.
          quod idem est.
        }
        lemma n100 : N %. 100 = V %. 100.
        {
          leibniz <- &y100, &x100 in |- *.
          quod idem est.
        }
        leibniz &n4, &n100 in |- *.
        leibniz &four_years in &e4.
        match &clamped100 with | inside | boundary end.
        - (* The quadrennium ends inside its century, so the year is not a century year. *)
          leibniz <- &e4 in &inside.
          lemma q4_below : q4 < 24.
          {
            match (Comparable.order.strict.trichotomy q4 24) with | smaller | rest end.
            - ipso &smaller.
            - match &rest with | same | greater end.
              + leibniz &same in &inside.
                ex (Bin0.order.strict.irreflexivity 36524 &inside) quodlibet.
              + lemma positive : 0%b0 < 1461.
                {
                  simpl Bin0.LessThan in |- *.
                  exists 1461.
                  simpl in |- *.
                  quod idem est.
                }
                let proof g :=
                  Bin0.multiplication.left.order.strict.monotonicity 1461 24 &q4 &positive &greater.
                let proof h :=
                  Bin0.addition.order.strict.monotonicity
                    (4 * 365) (1461 * 24) (4 * 365) (1461 * &q4)
                    (disjoin (refl (4 * 365)), _) &g.
                leibniz
                  (Bin0.addition.commutativity (4 * 365) (1461 * &q4)),
                  (Bin0.multiplication.commutativity 1461 &q4)
                  in &h.
                let proof loop := Bin0.order.strict.transitivity &h &inside.
                ex (Bin0.order.strict.irreflexivity 36524 &loop) quodlibet.
          }
          lemma v_below : V < 100.
          {
            lemma positive : 0%b0 < 4.
            {
              simpl Bin0.LessThan in |- *.
              exists 4.
              simpl in |- *.
              quod idem est.
            }
            let proof g :=
              Bin0.multiplication.left.order.strict.monotonicity 4 &q4 24 &positive &q4_below.
            let proof h :=
              Bin0.addition.order.strict.monotonicity
                (3 + 1) (4 * &q4) (3 + 1) (4 * 24) (disjoin (refl (3 + 1)), _) &g.
            leibniz
              (Bin0.addition.commutativity (3 + 1) (4 * &q4)),
              (Bin0.addition.commutativity (3 + 1) (4 * 24))
              in &h.
            ipso &h.
          }
          leibniz (Bin0.modulo.identity &V 100 &v_below) in |- *.
          simpl &V in |- *.
          let proof N := &N.
          let proof X := &X.
          let proof V := &V.
          match &q4 with | | p end;
            simpl Comparable.eq, Bin0.compare in |- *; simpl in |- *; quod idem est.
        - (* The day is the last of a quadricentennium, so the year is divisible by 400. *)
          match &boundary with | _ rest end.
          match &rest with | full_century third_century end.
          lemma q4_value : q4 = 24.
          {
            leibniz &full_century in &e4.
            lemma within : (4 * 365) < 1461.
            {
              simpl Bin0.LessThan in |- *.
              exists 1.
              simpl in |- *.
              simpl Bin.add in |- *.
              simpl in |- *.
              quod idem est.
            }
            match (Bin0.division.uniqueness 36524 1461 &q4 (4 * 365) (conjoin &e4, &within))
              with | quotient _ end.
            leibniz <- &quotient in |- *.
            simpl Bin0.divide in |- *.
            simpl in |- *.
            quod idem est.
          }
          leibniz &y400 in |- *.
          simpl &X, &V in |- *.
          leibniz &third_century, &q4_value in |- *.
          simpl Comparable.eq, Bin0.compare, Bin0.modulo in |- *.
          simpl in |- *.
          quod idem est.
      }
      simpl days_in_year in |- *.
      leibniz &leap in |- *.
      ipso &common_below_leap.
  }
  ipso facto.
Qed.

(* The year that [div_year] finds, taken apart by [days_before_year], gives
 * back the quotients it was built from, since each one is below its limit.
 *)
(* division.reconstruction *)
Theorem reconstruction
  : forall (n : Days) .
      days_before_year (Bin0.successor (pi_1 (div_year n))) + pi_2 (div_year n) = n.
Proof.
  intro n.
  lemma scaled : forall (k : Bin) (a : Bin0) (b : Bin0) . a <= b -> a * k <= b * k.
  {
    intros k a b h.
    lemma positive : 0%b0 < k.
    {
      simpl Bin0.LessThan in |- *.
      exists &k.
      simpl in |- *.
      quod idem est.
    }
    match &h with | same | smaller end.
    - leibniz &same in |- *.
      ipso (disjoin (refl (&b * k)), _).
    - let proof f := Bin0.multiplication.left.order.strict.monotonicity k &a &b &positive &smaller.
      leibniz
        (Bin0.multiplication.commutativity k &a),
        (Bin0.multiplication.commutativity k &b)
        in &f.
      ipso (disjoin _, &f).
  }
  lemma next : forall (a : Bin0) (b : Bin0) . a <= b -> a < b + 1.
  {
    intros a b h.
    lemma step : b < b + 1.
    {
      simpl Bin0.LessThan in |- *.
      exists 1.
      quod idem est.
    }
    ipso (@Comparable.order.mixed.left.transitivity _ Bin0.compare Bin0.LessThan _
            &a &b (&b + 1) &h &step).
  }
  lemma facto
    : let C := div_clamped_at_3 (n %. days_in_quadricentennium) days_in_century in
      let Y := div_clamped_at_3 (pi_2 C %. days_in_quadrennium) days_in_common_year in
      days_before_year
        (Bin0.successor
           ((years_in_quadricentennium * (n /. days_in_quadricentennium))
              + (years_in_century * pi_1 C)
              + (years_in_quadrennium * (pi_2 C /. days_in_quadrennium))
              + pi_1 Y))
        + pi_2 Y
      = n.
  {
    intros C Y.
    match (Bin0.division.specification n days_in_quadricentennium) with | e400 bounded400 end.
    let proof rc := division.clamped.dividend.reconstruction (n %. days_in_quadricentennium)
                      days_in_century.
    let proof qc := division.clamped.quotient.boundedness (n %. days_in_quadricentennium)
                      days_in_century.
    let proof bc := division.clamped.remainder.boundedness (n %. days_in_quadricentennium)
                      days_in_century &bounded400.
    let &C in &rc, &qc, &bc.
    let q400 := n /. days_in_quadricentennium in &e400 |- *.
    let proof q400 := &q400.
    let r400 := n %. days_in_quadricentennium in &e400, &rc, &bc.
    let proof r400 := &r400.
    let c := pi_1 C in &rc, &qc, &bc |- *.
    let proof c := &c.
    let r100 := pi_2 C in &rc, &bc, &Y |- *.
    let proof r100 := &r100.
    match (Bin0.division.specification r100 days_in_quadrennium) with | e4 bounded4 end.
    let proof ry := division.clamped.dividend.reconstruction (r100 %. days_in_quadrennium)
                      days_in_common_year.
    let proof qy := division.clamped.quotient.boundedness (r100 %. days_in_quadrennium)
                      days_in_common_year.
    let &Y in &ry, &qy.
    let q4 := r100 /. days_in_quadrennium in &e4 |- *.
    let proof q4 := &q4.
    let r4 := r100 %. days_in_quadrennium in &e4, &ry.
    let proof r4 := &r4.
    let c1 := pi_1 Y in &ry, &qy |- *.
    let proof c1 := &c1.
    let r1 := pi_2 Y in &ry |- *.
    let proof r1 := &r1.
    rm &C &Y &bounded400 &bounded4.
    lemma century_bounded : r100 <= days_in_century.
    {
      match &bc with | below | rest end.
      - ipso (disjoin _, &below).
      - match &rest with | _ more end.
        match &more with | full _ end.
        ipso (disjoin &full, _).
    }
    lemma quadrennia_bounded : q4 <= 24.
    {
      lemma part : q4 * days_in_quadrennium <= r100.
      {
        let proof f := Bin0.addition.right.order.extensivity &r4 (&q4 * days_in_quadrennium).
        leibniz (Bin0.addition.commutativity &r4 (&q4 * days_in_quadrennium)), &e4 in &f.
        ipso &f.
      }
      match (Comparable.order.strict.trichotomy q4 24) with | smaller | rest end.
      - ipso (disjoin _, &smaller).
      - match &rest with | same | greater end.
        + ipso (disjoin &same, _).
        + let proof g := Bin0.order.succession 24 &q4 &greater.
          let proof h := &scaled days_in_quadrennium (24 + 1) &q4 &g.
          let proof chain :=
            @Comparable.order.transitivity _ Bin0.compare Bin0.LessThan _
              ((24 + 1) * days_in_quadrennium) (&q4 * days_in_quadrennium)
              (Bin0.Positive days_in_century)
              &h
              (@Comparable.order.transitivity _ Bin0.compare Bin0.LessThan _
                 (&q4 * days_in_quadrennium) &r100 (Bin0.Positive days_in_century)
                 &part &century_bounded).
          let proof t :=
            modus aequans
              (Comparable.order.reflection
                 ((24 + 1) * days_in_quadrennium) (Bin0.Positive days_in_century)),
              &chain.
          simpl days_in_century, days_in_quadrennium, days_in_leap_year, days_in_common_year
            in &t.
          simpl in &t.
          simpl Bin.add in &t.
          simpl in &t.
          simpl Comparable.le, Bin0.compare in &t.
          simpl in &t.
          ex &t quodlibet.
    }
    lemma antecedence : forall (x : Bin0) . years_before (Bin0.successor x) = x.
    {
      intro x.
      simpl years_before in |- *.
      leibniz (Bin0.successor.specification &x) in |- *.
      ipso (Bin0.subtraction.saturating.inversion.addition &x 1).
    }
    lemma years_below : (q4 * years_in_quadrennium) + c1 < years_in_century.
    {
      ipso (Bin0.addition.order.strict.monotonicity
              (&q4 * years_in_quadrennium) &c1 (24 * years_in_quadrennium) 4
              (&scaled years_in_quadrennium &q4 24 &quadrennia_bounded)
              (&next &c1 3 &qy)).
    }
    lemma centuries_below
      : (c * years_in_century) + ((q4 * years_in_quadrennium) + c1) < years_in_quadricentennium.
    {
      ipso (Bin0.addition.order.strict.monotonicity
              (&c * years_in_century) ((&q4 * years_in_quadrennium) + &c1)
              (3 * years_in_century) years_in_century
              (&scaled years_in_century &c 3 &qc)
              &years_below).
    }
    lemma shape
      : (years_in_quadricentennium * q400) + (years_in_century * c)
          + (years_in_quadrennium * q4) + c1
        = (q400 * years_in_quadricentennium)
          + ((c * years_in_century) + ((q4 * years_in_quadrennium) + c1)).
    {
      leibniz
        (Bin0.addition.associativity
           ((years_in_quadricentennium * &q400) + (years_in_century * &c))
           (years_in_quadrennium * &q4) &c1),
        (Bin0.addition.associativity
           (years_in_quadricentennium * &q400) (years_in_century * &c)
           ((years_in_quadrennium * &q4) + &c1)),
        (Bin0.multiplication.commutativity years_in_quadricentennium &q400),
        (Bin0.multiplication.commutativity years_in_century &c),
        (Bin0.multiplication.commutativity years_in_quadrennium &q4)
        in |- *.
      quod idem est.
    }
    leibniz &shape in |- *.
    simpl days_before_year in |- *.
    leibniz
      (&antecedence
         ((&q400 * years_in_quadricentennium)
            + ((&c * years_in_century) + ((&q4 * years_in_quadrennium) + &c1))))
      in |- *.
    match (Bin0.division.uniqueness
             ((&q400 * years_in_quadricentennium)
                + ((&c * years_in_century) + ((&q4 * years_in_quadrennium) + &c1)))
             years_in_quadricentennium &q400
             ((&c * years_in_century) + ((&q4 * years_in_quadrennium) + &c1))
             (conjoin
                (refl
                   ((&q400 * years_in_quadricentennium)
                      + ((&c * years_in_century) + ((&q4 * years_in_quadrennium) + &c1)))),
                &centuries_below))
      with | quadricentennia rest400 end.
    leibniz &quadricentennia, &rest400 in |- *.
    match (Bin0.division.uniqueness
             ((&c * years_in_century) + ((&q4 * years_in_quadrennium) + &c1))
             years_in_century &c ((&q4 * years_in_quadrennium) + &c1)
             (conjoin
                (refl ((&c * years_in_century) + ((&q4 * years_in_quadrennium) + &c1))),
                &years_below))
      with | centuries rest100 end.
    leibniz &centuries, &rest100 in |- *.
    match (Bin0.division.uniqueness
             ((&q4 * years_in_quadrennium) + &c1) years_in_quadrennium &q4 &c1
             (conjoin (refl ((&q4 * years_in_quadrennium) + &c1)), (&next &c1 3 &qy)))
      with | quadrennia rest4 end.
    leibniz &quadrennia, &rest4 in |- *.
    leibniz <- &e400, <- &rc, <- &e4, <- &ry in |- *.
    leibniz
      (Bin0.addition.associativity
         (((days_in_quadricentennium * &q400) + (days_in_century * &c))
            + (days_in_quadrennium * &q4))
         (days_in_common_year * &c1) &r1),
      (Bin0.addition.associativity
         ((days_in_quadricentennium * &q400) + (days_in_century * &c))
         (days_in_quadrennium * &q4) ((days_in_common_year * &c1) + &r1)),
      (Bin0.addition.associativity
         (days_in_quadricentennium * &q400) (days_in_century * &c)
         ((days_in_quadrennium * &q4) + ((days_in_common_year * &c1) + &r1))),
      (Bin0.multiplication.commutativity days_in_quadricentennium &q400),
      (Bin0.multiplication.commutativity days_in_century &c),
      (Bin0.multiplication.commutativity days_in_quadrennium &q4),
      (Bin0.multiplication.commutativity days_in_common_year &c1)
      in |- *.
    quod idem est.
  }
  ipso facto.
Qed.

End division. (* division *)

(* The date of day number [n]. It stands below [calendar.validity] and
 * [division.boundedness] because its ctor takes their proofs.
 *)
(* [Days -> Date] *)
Definition from_day_number := fun (n : Days) .
  let y := Bin0.successor (pi_1 (div_year n)) in
  let days := pi_2 (div_year n) in
  Date.introduction y (month_after_days y days) (day_of_month_after_days y days)
    (calendar.validity y days (division.boundedness n)).

(* The date that is day [d] of year [y], [None] when the year has fewer than
 * [d] days. It stands below [calendar.ordinal.validity] because its ctor takes
 * that proof.
 *)
(* [Year -> Day -> Option Date] *)
Definition from_day_of_year := fun (y : Year) (d : Day) .
  Assert.guard (Comparable.le Bin.compare d (days_in_year y))
    (fun (a : Assert (Comparable.le Bin.compare d (days_in_year y))) .
       let days := Bin0.saturating_sub d 1 in
       Date.introduction y (month_after_days y days) (day_of_month_after_days y days)
         (calendar.ordinal.validity y d a)).

Module ordinal. (* ordinal *)

(* ordinal.decomposition *)
Theorem decomposition
  : forall (x : Date) . (day_of_year x : Bin0) = days_before_month (year x) (month x) + day x.
Proof.
  intro x.
  simpl day_of_year in |- *.
  match (days_before_month (year &x) (month &x)) with | | p end.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    quod idem est.
Qed.

(* ordinal.boundedness *)
Theorem boundedness : forall (x : Date) . day_of_year x <= days_in_year (year x).
Proof.
  intro x.
  leibniz (ordinal.decomposition &x) in |- *.
  match &x with | introduction y m d a end.
  simpl year, month, day in |- *.
  simpl is_valid in &a.
  let proof t := modus aequans (Assert.specification _), &a.
  let proof b := modus aequans (Comparable.order.reflection &d (days_in_month &y &m)), &t.
  lemma widened : (d : Bin0) <= days_in_month y m.
  {
    match &b with | e | s end.
    - ipso (disjoin (congru Bin0.Positive, &e), _).
    - match &s with | k e end.
      lemma facto : (d : Bin0) < days_in_month y m.
      {
        simpl Bin0.LessThan in |- *.
        exists &k.
        ipso (congru Bin0.Positive, &e).
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
              (Bin0.addition.order.strict.monotonicity
                 (days_before_month &y &m) d (days_before_month &y &m) (days_in_month &y &m)
                 (disjoin (refl (days_before_month &y &m)), _) &s)).
  }
  ipso (@Comparable.order.transitivity _ Bin0.compare Bin0.LessThan _
          (days_before_month &y &m + d)
          (days_before_month &y &m + days_in_month &y &m)
          (days_in_year &y)
          &shifted (month.boundedness &y &m)).
Qed.

(* The guard of [from_day_of_year] holds by [ordinal.boundedness], and the
 * month search finds the date back by [calendar.inversion].
 *)
(* ordinal.section *)
Theorem section : forall (x : Date) . from_day_of_year (year x) (day_of_year x) = Some x.
Proof.
  intro x.
  match &x with | introduction y m d a end.
  let X := introduction y m d a in |- *.
  lemma within : Assert (Comparable.le Bin.compare (day_of_year X) (days_in_year y)).
  {
    let proof bounded : (day_of_year X : Bin0) <= days_in_year y := ordinal.boundedness &X.
    let proof checked :=
      modus aequans
        (Comparable.order.reflection
           (Bin0.Positive (day_of_year &X)) (Bin0.Positive (days_in_year &y))),
        &bounded.
    ipso (modus aequans (Assert.specification _), &checked).
  }
  lemma located
    : calendar_date_after_days y (Bin0.saturating_sub (day_of_year X) 1) = (m, d).
  {
    lemma days
      : Bin0.saturating_sub (day_of_year X) 1 = days_before_month y m + Bin0.saturating_sub d 1.
    {
      let proof decomposed
        : (day_of_year X : Bin0) = days_before_month y m + d
        := ordinal.decomposition &X.
      leibniz &decomposed in |- *.
      leibniz <- (year.antecedence.restoration &d) in |- *.
      leibniz
        <- (Bin0.addition.associativity (days_before_month &y &m) (years_before &d) 1),
        (Bin0.subtraction.saturating.inversion.addition
           (days_before_month &y &m + years_before &d) 1),
        (Bin0.subtraction.saturating.inversion.addition (years_before &d) 1)
        in |- *.
      quod idem est.
    }
    leibniz &days in |- *.
    ipso (calendar.inversion &y &m &d &a).
  }
  let proof month_found
    : month_after_days y (Bin0.saturating_sub (day_of_year X) 1) = m
    := congru Product.first, &located.
  let proof day_found
    : day_of_month_after_days y (Bin0.saturating_sub (day_of_year X) 1) = d
    := congru Product.second, &located.
  lemma same
    : Date.introduction y
        (month_after_days y (Bin0.saturating_sub (day_of_year X) 1))
        (day_of_month_after_days y (Bin0.saturating_sub (day_of_year X) 1))
        (calendar.ordinal.validity y (day_of_year X) within)
      = X.
  {
    lemma equal
      : compare
          (Date.introduction y
             (month_after_days y (Bin0.saturating_sub (day_of_year X) 1))
             (day_of_month_after_days y (Bin0.saturating_sub (day_of_year X) 1))
             (calendar.ordinal.validity y (day_of_year X) within))
          X
        = Comparison.Eq.
    {
      simpl compare, year, month, day in |- *.
      leibniz &month_found, &day_found in |- *.
      simpl &X in |- *.
      leibniz
        (@Comparable.comparison.reflexivity _ Bin.compare Bin.LessThan _ &y),
        (@Comparable.comparison.reflexivity _ Month.compare Month.LessThan _ &m),
        (@Comparable.comparison.reflexivity _ Bin.compare Bin.LessThan _ &d)
        in |- *.
      simpl in |- *.
      quod idem est.
    }
    ipso (separation _ _ &equal).
  }
  lemma facto : year X = y.
  {
    simpl &X in |- *.
    simpl year in |- *.
    quod idem est.
  }
  simpl from_day_of_year in |- *.
  leibniz &facto in |- *.
  ipso (trans (Assert.guarding.evaluation _ _ &within), (congru Some, &same)).
Qed.

End ordinal. (* ordinal *)

Module validity. (* validity *)

(* The ctor's proof, read as an order between numbers. *)
(* validity.boundedness *)
Theorem boundedness : forall (x : Date) . day x <= days_in_month (year x) (month x).
Proof.
  intro x.
  match &x with | introduction y m d a end.
  simpl year, month, day in |- *.
  simpl is_valid in &a.
  let proof t := modus aequans (Assert.specification _), &a.
  let proof b := modus aequans (Comparable.order.reflection &d (days_in_month &y &m)), &t.
  match &b with | e | s end.
  - ipso (disjoin (congru Bin0.Positive, &e), _).
  - match &s with | k e end.
    lemma facto : (d : Bin0) < days_in_month y m.
    {
      simpl Bin0.LessThan in |- *.
      exists &k.
      ipso (congru Bin0.Positive, &e).
    }
    ipso (disjoin _, &facto).
Qed.

End validity. (* validity *)

Module number. (* number *)

(* One more than the day number counts the days before the year and the
 * days of the year up to and including the date.
 *)
(* number.decomposition *)
Theorem decomposition
  : forall (x : Date) . day_number x + 1 = days_before_year (year x) + day_of_year x.
Proof.
  intro x.
  simpl day_number in |- *.
  leibniz (ordinal.decomposition &x) in |- *.
  leibniz
    (Bin0.addition.associativity
       (days_before_year (year &x) + days_before_month (year &x) (month &x))
       (Bin0.saturating_sub (day &x) 1) 1)
    in |- *.
  lemma restored : Bin0.saturating_sub (day x) 1 + 1 = day x.
  {
    ipso (year.antecedence.restoration (day &x)).
  }
  leibniz &restored in |- *.
  leibniz
    (Bin0.addition.associativity
       (days_before_year (year &x)) (days_before_month (year &x) (month &x)) (day &x))
    in |- *.
  quod idem est.
Qed.

(* An earlier date has the smaller day number: by an earlier year, the
 * earlier date's year ends no later than the later year begins; by an
 * earlier month of the same year, its month ends no later than the later
 * month begins; by an earlier day of the same month, it is a smaller day.
 *)
(* number.monotonicity *)
Theorem monotonicity
  : forall (x1 : Date) (x2 : Date) . LessThan x1 x2 -> day_number x1 < day_number x2.
Proof.
  intros x1 x2 h.
  simpl LessThan in &h.
  lemma cancelled
    : forall (a : Bin0) (b : Bin0) . a + 1 < b + 1 -> a < b.
  {
    intros a b g.
    simpl Bin0.LessThan in &g |- *.
    match &g with | k e end.
    exists &k.
    leibniz
      (Bin0.addition.associativity &a 1 k),
      (Bin0.addition.commutativity 1 k),
      <- (Bin0.addition.associativity &a k 1)
      in &e.
    match (Bin0.addition.cancellation (&a + k) 1 &b) with | _ right end.
    ipso (&right &e).
  }
  lemma widened
    : forall (d1 : Bin) (d2 : Bin) . (d1 < d2)%b -> (d1 : Bin0) < d2.
  {
    intros d1 d2 g.
    match &g with | k e end.
    simpl Bin0.LessThan in |- *.
    exists &k.
    ipso (congru Bin0.Positive, &e).
  }
  lemma ordered
    : days_before_year (year x1) + day_of_year x1 < days_before_year (year x2) + day_of_year x2.
  {
    match &x1 with | introduction y1 m1 d1 a1 end.
    match &x2 with | introduction y2 m2 d2 a2 end.
    simpl compare, year, month, day in &h.
    match (Bin.compare &y1 &y2) with | | | end |- cy.
    - match (Bin.comparison.specification &y1 &y2) with | year_order _ end.
      let proof earlier := modus aequans &year_order, &cy.
      match &earlier with | k e end.
      let proof through := ordinal.boundedness (introduction &y1 &m1 &d1 &a1).
      lemma first
        : days_before_year y1 + day_of_year (introduction y1 m1 d1 a1)
          <= days_before_year y1 + days_in_year y1.
      {
        match &through with | same | smaller end.
        - leibniz &same in |- *.
          ipso (disjoin (refl (days_before_year &y1 + days_in_year &y1)), _).
        - ipso (disjoin _,
                  (Bin0.addition.order.strict.monotonicity
                     (days_before_year &y1) (day_of_year (introduction &y1 &m1 &d1 &a1))
                     (days_before_year &y1) (days_in_year &y1)
                     (disjoin (refl (days_before_year &y1)), _) &smaller)).
      }
      lemma second : days_before_year y1 + days_in_year y1 <= days_before_year y2.
      {
        leibniz <- &e in |- *.
        ipso (year.monotonicity &y1 &k).
      }
      lemma third
        : days_before_year y2 < days_before_year y2 + day_of_year (introduction y2 m2 d2 a2).
      {
        match (Bin0.addition.identity (days_before_year &y2)) with | _ plus_zero end.
        lemma positive : 0%b0 < day_of_year (introduction y2 m2 d2 a2).
        {
          simpl Bin0.LessThan in |- *.
          exists (day_of_year (introduction &y2 &m2 &d2 &a2)).
          simpl in |- *.
          quod idem est.
        }
        let proof s :=
          Bin0.addition.order.strict.monotonicity
            (days_before_year &y2) 0%b0
            (days_before_year &y2) (day_of_year (introduction &y2 &m2 &d2 &a2))
            (disjoin (refl (days_before_year &y2)), _)
            &positive.
        leibniz &plus_zero in &s.
        ipso &s.
      }
      ipso (Comparable.order.mixed.left.transitivity
              (@Comparable.order.transitivity _ Bin0.compare Bin0.LessThan _
                 (days_before_year &y1 + day_of_year (introduction &y1 &m1 &d1 &a1))
                 (days_before_year &y1 + days_in_year &y1)
                 (days_before_year &y2)
                 &first &second)
              &third).
    - match (Bin.comparison.specification &y1 &y2) with | _ year_equality end.
      let proof ey := modus aequans &year_equality, &cy.
      match &ey with | end.
      lemma inner
        : days_before_month y1 m1 + d1 < days_before_month y1 m2 + d2.
      {
        match (Month.compare &m1 &m2) with | | | end |- cm.
        + lemma valid : (d1 : Bin0) <= days_in_month y1 m1.
          {
            ipso (validity.boundedness (introduction &y1 &m1 &d1 &a1)).
          }
          lemma first
            : days_before_month y1 m1 + d1
              <= days_before_month y1 m1 + days_in_month y1 m1.
          {
            match &valid with | same | smaller end.
            - leibniz &same in |- *.
              ipso (disjoin (refl (days_before_month &y1 &m1 + days_in_month &y1 &m1)), _).
            - ipso (disjoin _,
                      (Bin0.addition.order.strict.monotonicity
                         (days_before_month &y1 &m1) d1
                         (days_before_month &y1 &m1) (days_in_month &y1 &m1)
                         (disjoin (refl (days_before_month &y1 &m1)), _) &smaller)).
          }
          lemma third : days_before_month y1 m2 < days_before_month y1 m2 + d2.
          {
            match (Bin0.addition.identity (days_before_month &y1 &m2))
              with | _ plus_zero end.
            lemma positive : 0%b0 < d2.
            {
              simpl Bin0.LessThan in |- *.
              exists &d2.
              simpl in |- *.
              quod idem est.
            }
            let proof s :=
              Bin0.addition.order.strict.monotonicity
                (days_before_month &y1 &m2) 0%b0
                (days_before_month &y1 &m2) d2
                (disjoin (refl (days_before_month &y1 &m2)), _) &positive.
            leibniz &plus_zero in &s.
            ipso &s.
          }
          ipso (Comparable.order.mixed.left.transitivity
                  (@Comparable.order.transitivity _ Bin0.compare Bin0.LessThan _
                     (days_before_month &y1 &m1 + d1)
                     (days_before_month &y1 &m1 + days_in_month &y1 &m1)
                     (days_before_month &y1 &m2)
                     &first (month.monotonicity &y1 &m1 &m2 &cm))
                  &third).
        + match (Month.comparison.specification &m1 &m2) with | _ month_equality end.
          let proof em := modus aequans &month_equality, &cm.
          match &em with | end.
          match (Bin.comparison.specification &d1 &d2) with | day_order _ end.
          let proof smaller := modus aequans &day_order, &h.
          ipso (Bin0.addition.order.strict.monotonicity
                  (days_before_month &y1 &m1) d1 (days_before_month &y1 &m1) d2
                  (disjoin (refl (days_before_month &y1 &m1)), _)
                  (&widened &d1 &d2 &smaller)).
        + ex &h quodlibet.
      }
      leibniz
        (ordinal.decomposition (introduction &y1 &m1 &d1 &a1)),
        (ordinal.decomposition (introduction &y1 &m2 &d2 &a2))
        in |- *.
      ipso (Bin0.addition.order.strict.monotonicity
              (days_before_year &y1) (days_before_month &y1 &m1 + d1)
              (days_before_year &y1) (days_before_month &y1 &m2 + d2)
              (disjoin (refl (days_before_year &y1)), _) &inner).
    - ex &h quodlibet.
  }
  leibniz <- (number.decomposition &x1), <- (number.decomposition &x2) in &ordered.
  ipso (&cancelled (day_number &x1) (day_number &x2) &ordered).
Qed.

(* Spec law 9: the order of dates is the order of their day numbers. *)
(* number.comparison *)
Theorem comparison
  : forall (x1 : Date) (x2 : Date) .
      compare x1 x2 = Bin0.compare (day_number x1) (day_number x2).
Proof.
  intros x1 x2.
  match (compare &x1 &x2) with | | | end |- c.
  - let proof smaller := number.monotonicity &x1 &x2 &c.
    match (Bin0.comparison.specification (day_number &x1) (day_number &x2))
      with | strict _ end.
    ipso (symm (modus aequans &strict, &smaller)).
  - match (separation &x1 &x2 &c) with | end.
    ipso (symm (@Comparable.comparison.reflexivity _ Bin0.compare Bin0.LessThan _
                  (day_number &x1))).
  - lemma reversed : compare x2 x1 = Comparison.Lt.
    {
      leibniz (antisymmetry &x2 &x1), &c in |- *.
      simpl in |- *.
      quod idem est.
    }
    let proof smaller := number.monotonicity &x2 &x1 &reversed.
    match (Bin0.comparison.specification (day_number &x2) (day_number &x1))
      with | strict _ end.
    let proof below := modus aequans &strict, &smaller.
    leibniz
      (Bin0.comparison.antisymmetry (day_number &x1) (day_number &x2)), &below
      in |- *.
    simpl in |- *.
    quod idem est.
Qed.

(* Spec law 9, as an order. *)
(* number.order *)
Theorem order
  : forall (x1 : Date) (x2 : Date) . LessThan x1 x2 <-> day_number x1 < day_number x2.
Proof.
  intros x1 x2.
  divide et impera.
  - ipso (number.monotonicity &x1 &x2).
  - intro smaller.
    simpl LessThan in |- *.
    leibniz (number.comparison &x1 &x2) in |- *.
    match (Bin0.comparison.specification (day_number &x1) (day_number &x2))
      with | strict _ end.
    ipso (modus aequans &strict, &smaller).
Qed.

(* Spec law 10. *)
(* number.injectivity *)
Theorem injectivity
  : forall {x1 : Date} {x2 : Date} . day_number x1 = day_number x2 -> x1 = x2.
Proof.
  intros x1 x2 e.
  lemma same : compare x1 x2 = Comparison.Eq.
  {
    leibniz (number.comparison &x1 &x2), &e in |- *.
    ipso (@Comparable.comparison.reflexivity _ Bin0.compare Bin0.LessThan _
            (day_number &x2)).
  }
  ipso (separation &x1 &x2 &same).
Qed.

(* The days before the month and the day give back the days of the year
 * before the date, by [calendar.reconstruction]; with the days before the
 * year they give back [n], by [division.reconstruction].
 *)
(* number.retraction *)
Theorem retraction : forall (n : Days) . day_number (from_day_number n) = n.
Proof.
  intro n.
  lemma facto
    : let y := Bin0.successor (pi_1 (div_year n)) in
      let days := pi_2 (div_year n) in
      (days_before_year y + days_before_month y (month_after_days y days))
        + Bin0.saturating_sub (day_of_month_after_days y days) 1
      = n.
  {
    intros y days.
    leibniz
      (Bin0.addition.associativity
         (days_before_year &y) (days_before_month &y (month_after_days &y &days))
         (Bin0.saturating_sub (day_of_month_after_days &y &days) 1))
      in |- *.
    leibniz (calendar.reconstruction &y &days (division.boundedness &n)) in |- *.
    ipso (division.reconstruction &n).
  }
  ipso facto.
Qed.

(* [day_number] is injective, so [retraction] decides it. *)
(* number.section *)
Theorem section : forall (x : Date) . from_day_number (day_number x) = x.
Proof.
  intro x.
  ipso (number.injectivity (number.retraction (day_number &x))).
Qed.

End number. (* number *)

Module weekday. (* weekday *)

(* The remainder by 7 is one of 0 to 6, pinned from 6 down, and each has its
 * weekday; so the [None] case of [weekday_of_day_number] never occurs.
 *)
(* weekday.totality *)
Theorem totality
  : forall (n : Days) . ~ (Weekday.from_b0 (n %. Weekday.days_in_week) = None).
Proof.
  intro n.
  match (Bin0.division.specification n Weekday.days_in_week) with | _ below end.
  let r := n %. Weekday.days_in_week in &below |- *.
  let proof r := &r.
  lemma pin : forall (k : Bin0) . r < k + 1 -> r = k \/ r < k.
  {
    intros k h.
    match (Comparable.order.strict.trichotomy r k) with | smaller | rest end.
    - ipso (disjoin _, &smaller).
    - match &rest with | same | greater end.
      + ipso (disjoin &same, _).
      + let proof after := Bin0.order.succession &k &r &greater.
        let proof loop := Comparable.order.mixed.left.transitivity &after &h.
        ex (Bin0.order.strict.irreflexivity (&k + 1) &loop) quodlibet.
  }
  simpl (~ _) in |- *.
  intro e.
  match (&pin 6 &below) with | six | below6 end.
  {
    leibniz &six in &e.
    simpl in &e.
    ex &e quodlibet.
  }
  match (&pin 5 &below6) with | five | below5 end.
  {
    leibniz &five in &e.
    simpl in &e.
    ex &e quodlibet.
  }
  match (&pin 4 &below5) with | four | below4 end.
  {
    leibniz &four in &e.
    simpl in &e.
    ex &e quodlibet.
  }
  match (&pin 3 &below4) with | three | below3 end.
  {
    leibniz &three in &e.
    simpl in &e.
    ex &e quodlibet.
  }
  match (&pin 2 &below3) with | two | below2 end.
  {
    leibniz &two in &e.
    simpl in &e.
    ex &e quodlibet.
  }
  match (&pin 1 &below2) with | one | below1 end.
  {
    leibniz &one in &e.
    simpl in &e.
    ex &e quodlibet.
  }
  match (&pin 0%b0 &below1) with | zero | below0 end.
  {
    leibniz &zero in &e.
    simpl in &e.
    ex &e quodlibet.
  }
  match &below0 with | k f end.
  match &r with | | p end.
  {
    simpl in &f.
    ex &f quodlibet.
  }
  simpl in &f.
  ex &f quodlibet.
Qed.

(* The remainder by 7 either steps up by one or wraps from 6 to 0, and the
 * weekday follows it; every remainder from 6 on is refused by computing its
 * comparison with 7.
 *)
(* weekday.succession *)
Theorem succession
  : forall (n : Days) .
      weekday_of_day_number (n + 1) = Weekday.next (weekday_of_day_number n).
Proof.
  intro n.
  simpl weekday_of_day_number in |- *.
  match (Bin0.division.specification n Weekday.days_in_week) with | _ below end.
  match (Bin0.order.succession (n %. Weekday.days_in_week) Weekday.days_in_week &below)
    with | carry | interior end.
  - match (Bin0.division.succession.carry n Weekday.days_in_week &carry) with | _ wrapped end.
    leibniz &wrapped in |- *.
    lemma last : n %. Weekday.days_in_week = 6.
    {
      lemma shifted : (n %. Weekday.days_in_week) + 1 = 6 + 1.
      {
        ipso &carry.
      }
      match (Bin0.addition.cancellation (n %. Weekday.days_in_week) 1 6) with | _ right end.
      ipso (&right &shifted).
    }
    leibniz &last in |- *.
    simpl in |- *.
    quod idem est.
  - match (Bin0.division.succession.interior n Weekday.days_in_week &interior)
      with | _ stepped end.
    leibniz &stepped in |- *.
    let r := n %. Weekday.days_in_week in &interior, &below |- *.
    let proof r := &r.
    match (Bin0.comparison.specification (&r + 1) Weekday.days_in_week) with | strict _ end.
    let proof c := modus aequans &strict, &interior.
    lemma pin : forall (k : Bin0) . r < k + 1 -> r = k \/ r < k.
    {
      intros k h.
      match (Comparable.order.strict.trichotomy r k) with | smaller | rest end.
      - ipso (disjoin _, &smaller).
      - match &rest with | same | greater end.
        + ipso (disjoin &same, _).
        + let proof after := Bin0.order.succession &k &r &greater.
          let proof loop := Comparable.order.mixed.left.transitivity &after &h.
          ex (Bin0.order.strict.irreflexivity (&k + 1) &loop) quodlibet.
    }
    match (&pin 6 &below) with | six | below6 end.
    {
      leibniz &six in &c.
      simpl Weekday.days_in_week in &c.
      simpl in &c.
      simpl Bin.add in &c.
      simpl in &c.
      simpl Bin.compare in &c.
      simpl in &c.
      ex &c quodlibet.
    }
    match (&pin 5 &below6) with | five | below5 end.
    {
      leibniz &five in |- *.
      simpl in |- *.
      quod idem est.
    }
    match (&pin 4 &below5) with | four | below4 end.
    {
      leibniz &four in |- *.
      simpl in |- *.
      quod idem est.
    }
    match (&pin 3 &below4) with | three | below3 end.
    {
      leibniz &three in |- *.
      simpl in |- *.
      quod idem est.
    }
    match (&pin 2 &below3) with | two | below2 end.
    {
      leibniz &two in |- *.
      simpl in |- *.
      quod idem est.
    }
    match (&pin 1 &below2) with | one | below1 end.
    {
      leibniz &one in |- *.
      simpl in |- *.
      quod idem est.
    }
    match (&pin 0%b0 &below1) with | zero | below0 end.
    {
      leibniz &zero in |- *.
      simpl in |- *.
      quod idem est.
    }
    match &below0 with | k e end.
    match &r with | | p end.
    {
      simpl in &e.
      ex &e quodlibet.
    }
    simpl in &e.
    ex &e quodlibet.
Qed.

(* weekday.periodicity *)
Theorem periodicity
  : forall (n : Days) .
      weekday_of_day_number (n + Weekday.days_in_week) = weekday_of_day_number n.
Proof.
  intro n.
  lemma whole : Weekday.days_in_week %. Weekday.days_in_week = 0%b0.
  {
    simpl Weekday.days_in_week, Bin0.modulo in |- *.
    simpl in |- *.
    quod idem est.
  }
  simpl weekday_of_day_number in |- *.
  leibniz
    (Bin0.modulo.sum.right.invariance n Weekday.days_in_week Weekday.days_in_week &whole)
    in |- *.
  quod idem est.
Qed.

Module quadricentennium. (* weekday.quadricentennium *)

(* A quadricentennium is 20871 whole weeks. *)
(* weekday.quadricentennium.periodicity *)
Theorem periodicity
  : forall (n : Days) .
      weekday_of_day_number (n + days_in_quadricentennium) = weekday_of_day_number n.
Proof.
  intro n.
  lemma whole : days_in_quadricentennium %. Weekday.days_in_week = 0%b0.
  {
    simpl days_in_quadricentennium, days_in_century, days_in_quadrennium, days_in_leap_year,
      days_in_common_year, years_in_quadrennium, Weekday.days_in_week, Bin0.modulo
      in |- *.
    simpl in |- *.
    quod idem est.
  }
  simpl weekday_of_day_number in |- *.
  leibniz
    (Bin0.modulo.sum.right.invariance n days_in_quadricentennium Weekday.days_in_week &whole)
    in |- *.
  quod idem est.
Qed.

End quadricentennium. (* weekday.quadricentennium *)

End weekday. (* weekday *)

Module order. (* order *)

Module strict. (* order.strict *)

(* order.strict.transitivity *)
Theorem transitivity
  : forall {x1 : Date} {x2 : Date} {x3 : Date} .
      LessThan x1 x2 -> LessThan x2 x3 -> LessThan x1 x3.
Proof.
  intros x1 x2 x3 h1 h2.
  let proof n1 := modus aequans (number.order &x1 &x2), &h1.
  let proof n2 := modus aequans (number.order &x2 &x3), &h2.
  ipso (modus aequans (number.order &x1 &x3), (Bin0.order.strict.transitivity &n1 &n2)).
Qed.

End strict. (* order.strict *)

End order. (* order *)

Module comparison. (* comparison *)

(* comparison.specification *)
Theorem specification
  : forall (x1 : Date) (x2 : Date) .
      (compare x1 x2 = Comparison.Lt <-> LessThan x1 x2)
      /\ (compare x1 x2 = Comparison.Eq <-> x1 = x2).
Proof.
  intros x1 x2.
  divide et impera.
  - simpl LessThan in |- *.
    divide et impera.
    + intro c.
      ipso &c.
    + intro c.
      ipso &c.
  - divide et impera.
    + ipso (separation &x1 &x2).
    + intro e.
      leibniz &e, (number.comparison &x2 &x2) in |- *.
      ipso (@Comparable.comparison.reflexivity _ Bin0.compare Bin0.LessThan _
              (day_number &x2)).
Qed.

End comparison. (* comparison *)

Instance comparable
  : Comparable compare LessThan :=
  {| Comparable.transitivity := @order.strict.transitivity
  ; Comparable.specification := comparison.specification
  ; Comparable.antisymmetry := antisymmetry |}.

End Date. (* Date *)

Abbreviation Date := Date.T.

Existing Instance Date.comparable.
