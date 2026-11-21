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
From JW Require Import Data.Number.Nat.
From JW Require Import Data.Number.Nat0.
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

(* [x1] comes before [x2] in the order of time. *)
(* [Date -> Date -> Prop] *)
Definition LessThan := fun (x1 : Date) (x2 : Date) . compare x1 x2 = Comparison.Lt.

(* Each of the three comparisons is antisymmetric, so their order is. *)
(* antisymmetry *)
Theorem antisymmetry
  : forall (x1 : Date) (x2 : Date) . compare x1 x2 = Comparison.transpose (compare x2 x1).
Proof.
  intros x1 x2.
  match &x1 with | introduction y1 m1 d1 a1 end.
  match &x2 with | introduction y2 m2 d2 a2 end.
  simpl compare, year, month, day in |- *.
  leibniz
    (BinBase.comparison.antisymmetry &y1 &y2),
    (Month.comparison.antisymmetry &m1 &m2),
    (BinBase.comparison.antisymmetry &d1 &d2)
    in |- *.
  match (BinBase.compare &y2 &y1) with | | | end;
    match (Month.compare &m2 &m1) with | | | end;
    match (BinBase.compare &d2 &d1) with | | | end;
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
  match (BinBase.compare &y1 &y2) with | | | end |- cy.
  - ex &h quodlibet.
  - match (Month.compare &m1 &m2) with | | | end |- cm.
    + ex &h quodlibet.
    + match (BinBase.comparison.specification &y1 &y2) with | _ year_equality end.
      match (Month.comparison.specification &m1 &m2) with | _ month_equality end.
      match (BinBase.comparison.specification &d1 &d2) with | _ day_equality end.
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
          Comparable.le BinWithZero.compare
            (days_before_month y m1 + days_in_month y m1) (days_before_month y m2)
      | Comparison.Eq => true
      | Comparison.Gt => true
      end
      = true.
  {
    simpl Month.compare in |- *.
    simpl days_before_month, days_in_month, BinBase.compare, Comparable.le, BinWithZero.compare
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

Module antecedence. (* year.antecedence *)

(* Both sides are read in [Nat0], where [y] is [1] or a successor and each
 * case computes.
 *)
(* year.antecedence.translation *)
Theorem translation
  : forall (y : Year) (k : BinBase) . years_before (y + k)%bin_base = years_before y + k.
Proof.
  intros y k.
  lemma facto
    : BinWithZero.to_nat0 (years_before (y + k)%bin_base)
      = BinWithZero.to_nat0 (years_before y + k).
  {
    simpl years_before in |- *.
    leibniz
      (BinWithZero.conversion.subtraction.saturating (y + k)%bin_base 1),
      (BinWithZero.conversion.addition (BinWithZero.saturating_sub y 1) k),
      (BinWithZero.conversion.subtraction.saturating y 1)
      in |- *.
    simpl BinWithZero.to_nat0 in |- *.
    leibniz (BinBase.conversion.addition &y &k) in |- *.
    let a := BinBase.to_nat &y in |- *.
    let proof a := &a.
    extro &a.
    intro a.
    match &a with | One | Successor a' end.
    - simpl in |- *.
      quod idem est.
    - simpl in |- *.
      quod idem est.
  }
  ipso (BinWithZero.conversion.injectivity &facto).
Qed.

(* Read in [Nat0] as [translation] is, with the [1] put first so that each
 * case computes.
 *)
(* year.antecedence.restoration *)
Theorem restoration : forall (y : Year) . years_before y + 1 = y.
Proof.
  intro y.
  lemma facto : BinWithZero.to_nat0 (years_before y + 1) = BinWithZero.to_nat0 y.
  {
    simpl years_before in |- *.
    leibniz
      (BinWithZero.conversion.addition (BinWithZero.saturating_sub y 1) 1),
      (BinWithZero.conversion.subtraction.saturating y 1)
      in |- *.
    simpl BinWithZero.to_nat0 in |- *.
    leibniz
      (Nat0.addition.commutativity
         (Nat0.saturating_sub
            (Nat0.Positive (BinBase.to_nat &y)) (Nat0.Positive (BinBase.to_nat 1)))
         (Nat0.Positive (BinBase.to_nat 1)))
      in |- *.
    let a := BinBase.to_nat &y in |- *.
    let proof a := &a.
    extro &a.
    intro a.
    match &a with | One | Successor a' end.
    - simpl in |- *.
      quod idem est.
    - simpl in |- *.
      quod idem est.
  }
  ipso (BinWithZero.conversion.injectivity &facto).
Qed.

End antecedence. (* year.antecedence *)

(* 400 more years before [y] add one whole quadricentennium and leave the rest
 * of the decomposition as it was.
 *)
(* year.periodicity *)
Theorem periodicity
  : forall (y : Year) .
      days_before_year (y + 400%bin_base_decimal)%bin_base
      = days_before_year y + days_in_quadricentennium.
Proof.
  intro y.
  simpl days_before_year in |- *.
  leibniz (year.antecedence.translation &y 400) in |- *.
  let n := years_before &y in |- *.
  lemma quotient : (n + 400) /. 400 = (n /. 400) + 1.
  {
    ipso (BinWithZero.division.translation n 400).
  }
  lemma remainder : (n + 400) %. 400 = n %. 400.
  {
    lemma zero : 400 %. 400 = 0%bin_with_zero.
    {
      simpl BinWithZero.modulo in |- *.
      simpl in |- *.
      quod idem est.
    }
    ipso (BinWithZero.modulo.sum.right.invariance n 400 400 &zero).
  }
  leibniz &quotient, &remainder in |- *.
  match (BinWithZero.multiplication.distributivity.over.addition
           days_in_quadricentennium (n /. 400) 1)
    with | left _ end.
  leibniz &left in |- *.
  match (BinWithZero.multiplication.identity days_in_quadricentennium) with | _ right end.
  leibniz &right in |- *.
  lemma swap
    : forall (u : BinWithZero) (v : BinWithZero) .
        (u + days_in_quadricentennium) + v = (u + v) + days_in_quadricentennium.
  {
    intros u v.
    leibniz
      (BinWithZero.addition.associativity &u days_in_quadricentennium &v),
      (BinWithZero.addition.commutativity days_in_quadricentennium &v),
      <- (BinWithZero.addition.associativity &u &v days_in_quadricentennium)
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
      days_before_year (y + 1)%bin_base = days_before_year y + days_in_year y.
Proof.
  intro y.
  simpl days_before_year in |- *.
  leibniz (year.antecedence.translation &y 1) in |- *.
  let n := years_before &y in |- *.
  let proof restored := year.antecedence.restoration &y.
  let &n in &restored.
  match (BinWithZero.division.specification n 400) with | _ below400 end.
  match (BinWithZero.division.specification (n %. 400) 100) with | _ below100 end.
  match (BinWithZero.division.specification ((n %. 400) %. 100) 4) with | _ below4 end.
  lemma hundred : (n %. 400) %. 100 = n %. 100.
  {
    ipso (BinWithZero.modulo.nesting n 100 4).
  }
  lemma four : ((n %. 400) %. 100) %. 4 = n %. 4.
  {
    leibniz &hundred in |- *.
    ipso (BinWithZero.modulo.nesting n 4 25).
  }
  lemma hundred_y : (y %. 400) %. 100 = y %. 100.
  {
    ipso (BinWithZero.modulo.nesting y 100 4).
  }
  lemma four_y : (y %. 100) %. 4 = y %. 4.
  {
    ipso (BinWithZero.modulo.nesting y 4 25).
  }
  lemma zero_by_hundred : 0%bin_with_zero /. 100 = 0%bin_with_zero.
  {
    simpl BinWithZero.divide in |- *.
    simpl in |- *.
    quod idem est.
  }
  lemma zero_mod_hundred : 0%bin_with_zero %. 100 = 0%bin_with_zero.
  {
    simpl BinWithZero.modulo in |- *.
    simpl in |- *.
    quod idem est.
  }
  lemma zero_by_four : 0%bin_with_zero /. 4 = 0%bin_with_zero.
  {
    simpl BinWithZero.divide in |- *.
    simpl in |- *.
    quod idem est.
  }
  lemma zero_mod_four : 0%bin_with_zero %. 4 = 0%bin_with_zero.
  {
    simpl BinWithZero.modulo in |- *.
    simpl in |- *.
    quod idem est.
  }
  lemma last_by_hundred : 399 /. 100 = 3.
  {
    simpl BinWithZero.divide in |- *.
    simpl in |- *.
    quod idem est.
  }
  lemma last_mod_hundred : 399 %. 100 = 99.
  {
    simpl BinWithZero.modulo in |- *.
    simpl in |- *.
    quod idem est.
  }
  lemma last_by_four : 99 /. 4 = 24.
  {
    simpl BinWithZero.divide in |- *.
    simpl in |- *.
    quod idem est.
  }
  lemma last_mod_four : 99 %. 4 = 3.
  {
    simpl BinWithZero.modulo in |- *.
    simpl in |- *.
    quod idem est.
  }
  match (BinWithZero.multiplication.annihilation days_in_century) with | _ century_zero end.
  match (BinWithZero.multiplication.annihilation days_in_quadrennium) with | _ quadrennium_zero end.
  match (BinWithZero.multiplication.annihilation days_in_common_year) with | _ common_zero end.
  match (BinWithZero.order.succession (n %. 400) 400 &below400) with | carry400 | interior400 end.
  - (* [y] is divisible by 400. *)
    match (BinWithZero.division.succession.carry n 400 &carry400) with | q400 r400 end.
    lemma r1 : n %. 400 = 399.
    {
      lemma shifted : (n %. 400) + 1 = 399 + 1.
      {
        ipso &carry400.
      }
      match (BinWithZero.addition.cancellation (n %. 400) 1 399) with | _ right end.
      ipso (&right &shifted).
    }
    lemma y400 : y %. 400 = 0%bin_with_zero.
    {
      leibniz <- &restored in |- *.
      ipso &r400.
    }
    lemma y100 : y %. 100 = 0%bin_with_zero.
    {
      leibniz <- &hundred_y, &y400 in |- *.
      ipso &zero_mod_hundred.
    }
    lemma y4 : y %. 4 = 0%bin_with_zero.
    {
      leibniz <- &four_y, &y100 in |- *.
      ipso &zero_mod_four.
    }
    lemma length : days_in_year y = 366.
    {
      simpl days_in_year, is_leap in |- *.
      leibniz &y4, &y100, &y400 in |- *.
      simpl Comparable.eq, BinWithZero.compare in |- *.
      simpl in |- *.
      quod idem est.
    }
    leibniz &q400, &r400, &length, &r1 in |- *.
    leibniz
      &zero_by_hundred, &zero_mod_hundred, &zero_by_four, &zero_mod_four,
      &last_by_hundred, &last_mod_hundred, &last_by_four, &last_mod_four
      in |- *.
    leibniz &century_zero, &quadrennium_zero, &common_zero in |- *.
    match (BinWithZero.addition.identity (days_in_quadricentennium * ((n /. 400) + 1)))
      with | _ plus_zero end.
    leibniz &plus_zero, &plus_zero, &plus_zero in |- *.
    match (BinWithZero.multiplication.distributivity.over.addition
             days_in_quadricentennium (n /. 400) 1)
      with | distributed _ end.
    match (BinWithZero.multiplication.identity days_in_quadricentennium) with | _ times_one end.
    leibniz &distributed, &times_one in |- *.
    leibniz
      (BinWithZero.addition.associativity
         (((days_in_quadricentennium * (n /. 400)) + (days_in_century * 3))
            + (days_in_quadrennium * 24))
         (days_in_common_year * 3) 366),
      (BinWithZero.addition.associativity
         ((days_in_quadricentennium * (n /. 400)) + (days_in_century * 3))
         (days_in_quadrennium * 24) ((days_in_common_year * 3) + 366)),
      (BinWithZero.addition.associativity
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
      simpl BinBase.add in |- *.
      simpl in |- *.
      quod idem est.
    }
    leibniz &constant in |- *.
    quod idem est.
  - (* [y] is not divisible by 400. *)
    match (BinWithZero.division.succession.interior n 400 &interior400) with | q400 r400 end.
    lemma y400 : y %. 400 = (n %. 400) + 1.
    {
      leibniz <- &restored in |- *.
      ipso &r400.
    }
    leibniz &q400, &r400 in |- *.
    match (BinWithZero.order.succession ((n %. 400) %. 100) 100 &below100)
      with | carry100 | interior100 end.
    + (* [y] is divisible by 100 and not by 400. *)
      match (BinWithZero.division.succession.carry (n %. 400) 100 &carry100) with | q100 r100 end.
      lemma r2 : (n %. 400) %. 100 = 99.
      {
        lemma shifted : ((n %. 400) %. 100) + 1 = 99 + 1.
        {
          ipso &carry100.
        }
        match (BinWithZero.addition.cancellation ((n %. 400) %. 100) 1 99) with | _ right end.
        ipso (&right &shifted).
      }
      lemma carry100n : (n %. 100) + 1 = 100.
      {
        leibniz <- &hundred in |- *.
        ipso &carry100.
      }
      match (BinWithZero.division.succession.carry n 100 &carry100n) with | _ r100n end.
      lemma y100 : y %. 100 = 0%bin_with_zero.
      {
        leibniz <- &restored in |- *.
        ipso &r100n.
      }
      lemma y4 : y %. 4 = 0%bin_with_zero.
      {
        leibniz <- &four_y, &y100 in |- *.
        ipso &zero_mod_four.
      }
      lemma length : days_in_year y = 365.
      {
        simpl days_in_year, is_leap in |- *.
        leibniz &y4, &y100, &y400 in |- *.
        match (n %. 400) with | | p end;
          simpl Comparable.eq, BinWithZero.compare in |- *; simpl in |- *; quod idem est.
      }
      leibniz &q100, &r100, &r2, &length in |- *.
      leibniz &zero_by_four, &zero_mod_four, &last_by_four, &last_mod_four in |- *.
      leibniz &quadrennium_zero, &common_zero in |- *.
      match (BinWithZero.addition.identity
               ((days_in_quadricentennium * (n /. 400))
                  + (days_in_century * (((n %. 400) /. 100) + 1))))
        with | _ plus_zero end.
      leibniz &plus_zero, &plus_zero in |- *.
      match (BinWithZero.multiplication.distributivity.over.addition
               days_in_century ((n %. 400) /. 100) 1)
        with | distributed _ end.
      match (BinWithZero.multiplication.identity days_in_century) with | _ times_one end.
      leibniz &distributed, &times_one in |- *.
      leibniz
        <- (BinWithZero.addition.associativity
              (days_in_quadricentennium * (n /. 400))
              (days_in_century * ((n %. 400) /. 100)) days_in_century),
        (BinWithZero.addition.associativity
           (((days_in_quadricentennium * (n /. 400)) + (days_in_century * ((n %. 400) /. 100)))
              + (days_in_quadrennium * 24))
           (days_in_common_year * 3) 365),
        (BinWithZero.addition.associativity
           ((days_in_quadricentennium * (n /. 400)) + (days_in_century * ((n %. 400) /. 100)))
           (days_in_quadrennium * 24) ((days_in_common_year * 3) + 365))
        in |- *.
      lemma constant
        : (days_in_quadrennium * 24) + ((days_in_common_year * 3) + 365) = days_in_century.
      {
        simpl days_in_century, days_in_quadrennium, days_in_common_year in |- *.
        simpl in |- *.
        simpl BinBase.add in |- *.
        simpl in |- *.
        quod idem est.
      }
      leibniz &constant in |- *.
      quod idem est.
    + (* [y] is not divisible by 100. *)
      match (BinWithZero.division.succession.interior (n %. 400) 100 &interior100)
        with | q100 r100 end.
      leibniz &q100, &r100 in |- *.
      lemma interior100n : (n %. 100) + 1 < 100.
      {
        leibniz <- &hundred in |- *.
        ipso &interior100.
      }
      match (BinWithZero.division.succession.interior n 100 &interior100n) with | _ r100n end.
      lemma y100 : y %. 100 = (n %. 100) + 1.
      {
        leibniz <- &restored in |- *.
        ipso &r100n.
      }
      match (BinWithZero.order.succession (((n %. 400) %. 100) %. 4) 4 &below4)
        with | carry4 | interior4 end.
      * (* [y] is divisible by 4 and not by 100. *)
        match (BinWithZero.division.succession.carry ((n %. 400) %. 100) 4 &carry4)
          with | q4 r4 end.
        lemma r3 : ((n %. 400) %. 100) %. 4 = 3.
        {
          lemma shifted : (((n %. 400) %. 100) %. 4) + 1 = 3 + 1.
          {
            ipso &carry4.
          }
          match (BinWithZero.addition.cancellation (((n %. 400) %. 100) %. 4) 1 3)
            with | _ right end.
          ipso (&right &shifted).
        }
        lemma carry4n : (n %. 4) + 1 = 4.
        {
          leibniz <- &four in |- *.
          ipso &carry4.
        }
        match (BinWithZero.division.succession.carry n 4 &carry4n) with | _ r4n end.
        lemma y4 : y %. 4 = 0%bin_with_zero.
        {
          leibniz <- &restored in |- *.
          ipso &r4n.
        }
        lemma length : days_in_year y = 366.
        {
          simpl days_in_year, is_leap in |- *.
          leibniz &y4, &y100 in |- *.
          match (n %. 100) with | | p end;
            simpl Comparable.eq, BinWithZero.compare in |- *; simpl in |- *; quod idem est.
        }
        leibniz &q4, &r4, &r3, &length in |- *.
        leibniz &common_zero in |- *.
        match (BinWithZero.addition.identity
                 (((days_in_quadricentennium * (n /. 400))
                     + (days_in_century * ((n %. 400) /. 100)))
                    + (days_in_quadrennium * ((((n %. 400) %. 100) /. 4) + 1))))
          with | _ plus_zero end.
        leibniz &plus_zero in |- *.
        match (BinWithZero.multiplication.distributivity.over.addition
                 days_in_quadrennium (((n %. 400) %. 100) /. 4) 1)
          with | distributed _ end.
        match (BinWithZero.multiplication.identity days_in_quadrennium) with | _ times_one end.
        leibniz &distributed, &times_one in |- *.
        leibniz
          <- (BinWithZero.addition.associativity
                ((days_in_quadricentennium * (n /. 400))
                   + (days_in_century * ((n %. 400) /. 100)))
                (days_in_quadrennium * (((n %. 400) %. 100) /. 4)) days_in_quadrennium),
          (BinWithZero.addition.associativity
             (((days_in_quadricentennium * (n /. 400))
                 + (days_in_century * ((n %. 400) /. 100)))
                + (days_in_quadrennium * (((n %. 400) %. 100) /. 4)))
             (days_in_common_year * 3) 366)
          in |- *.
        lemma constant : (days_in_common_year * 3) + 366 = days_in_quadrennium.
        {
          simpl days_in_quadrennium, days_in_common_year in |- *.
          simpl in |- *.
          simpl BinBase.add in |- *.
          simpl in |- *.
          quod idem est.
        }
        leibniz &constant in |- *.
        quod idem est.
      * (* [y] is not divisible by 4. *)
        match (BinWithZero.division.succession.interior ((n %. 400) %. 100) 4 &interior4)
          with | q4 r4 end.
        lemma interior4n : (n %. 4) + 1 < 4.
        {
          leibniz <- &four in |- *.
          ipso &interior4.
        }
        match (BinWithZero.division.succession.interior n 4 &interior4n) with | _ r4n end.
        lemma y4 : y %. 4 = (n %. 4) + 1.
        {
          leibniz <- &restored in |- *.
          ipso &r4n.
        }
        lemma length : days_in_year y = 365.
        {
          simpl days_in_year, is_leap in |- *.
          leibniz &y4 in |- *.
          match (n %. 4) with | | p end;
            simpl Comparable.eq, BinWithZero.compare in |- *; simpl in |- *; quod idem est.
        }
        leibniz &q4, &r4, &length in |- *.
        match (BinWithZero.multiplication.distributivity.over.addition
                 days_in_common_year (((n %. 400) %. 100) %. 4) 1)
          with | distributed _ end.
        match (BinWithZero.multiplication.identity days_in_common_year) with | _ times_one end.
        leibniz &distributed, &times_one in |- *.
        leibniz
          <- (BinWithZero.addition.associativity
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
  : forall (y : Year) (k : BinBase) .
      days_before_year y + days_in_year y <= days_before_year (y + k)%bin_base.
Proof.
  intros y k.
  leibniz <- (BinBase.conversion.section &k) in |- *.
  let n := BinBase.to_nat &k in |- *.
  let proof n := &n.
  extro &n.
  intro n.
  match &n with | One | Successor (n' by IH) end per Nat.induction.
  - lemma facto : days_before_year y + days_in_year y <= days_before_year (y + 1)%bin_base.
    {
      leibniz (year.succession &y) in |- *.
      ipso (disjoin (refl (days_before_year &y + days_in_year &y)), _).
    }
    ipso &facto.
  - lemma shift : forall (b : BinBase) . (y + (++ b))%bin_base = ((y + b) + 1)%bin_base.
    {
      intro b.
      lemma facto : BinBase.to_nat (y + (++ b))%bin_base = BinBase.to_nat ((y + b) + 1)%bin_base.
      {
        leibniz
          (BinBase.conversion.addition &y (++ &b)%bin_base),
          (BinBase.conversion.successor &b),
          (BinBase.conversion.addition (&y + &b)%bin_base 1),
          (BinBase.conversion.addition &y &b)
          in |- *.
        leibniz
          (Nat.addition.right.successor (BinBase.to_nat &y) (BinBase.to_nat &b)),
          (Nat.addition.commutativity
             (BinBase.to_nat &y + BinBase.to_nat &b)%n (BinBase.to_nat 1))
          in |- *.
        simpl in |- *.
        quod idem est.
      }
      ipso (BinBase.conversion.injectivity &facto).
    }
    lemma extended
      : days_before_year (y + BinBase.from_nat n')%bin_base
        <= days_before_year (y + BinBase.from_nat n')%bin_base
           + days_in_year (y + BinBase.from_nat n')%bin_base.
    {
      leibniz
        (BinWithZero.addition.commutativity
           (days_before_year (&y + BinBase.from_nat &n')%bin_base)
           (days_in_year (&y + BinBase.from_nat &n')%bin_base))
        in |- *.
      ipso (BinWithZero.addition.right.order.extensivity
              (days_in_year (&y + BinBase.from_nat &n')%bin_base)
              (days_before_year (&y + BinBase.from_nat &n')%bin_base)).
    }
    lemma step
      : days_before_year y + days_in_year y
        <= days_before_year ((y + BinBase.from_nat n') + 1)%bin_base.
    {
      leibniz (year.succession (&y + BinBase.from_nat &n')%bin_base) in |- *.
      ipso (@Comparable.order.transitivity _ BinWithZero.compare BinWithZero.LessThan _
              (days_before_year &y + days_in_year &y)
              (days_before_year (&y + BinBase.from_nat &n')%bin_base)
              (days_before_year (&y + BinBase.from_nat &n')%bin_base
                 + days_in_year (&y + BinBase.from_nat &n')%bin_base)
              &IH &extended).
    }
    lemma facto
      : days_before_year y + days_in_year y
        <= days_before_year (y + (++ BinBase.from_nat n'))%bin_base.
    {
      leibniz (&shift (BinBase.from_nat &n')) in |- *.
      ipso &step.
    }
    ipso &facto.
Qed.

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
  - ipso (disjoin (congru BinWithZero.Positive, &e), _).
  - match &s with | k e end.
    lemma facto : (d : BinWithZero) < days_in_month y m.
    {
      simpl BinWithZero.LessThan in |- *.
      exists &k.
      ipso (congru BinWithZero.Positive, &e).
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
  simpl day_number, day_of_year in |- *.
  leibniz
    (BinWithZero.addition.associativity
       (days_before_year (year &x) + days_before_month (year &x) (month &x))
       (BinWithZero.saturating_sub (day &x) 1) 1)
    in |- *.
  lemma restored : BinWithZero.saturating_sub (day x) 1 + 1 = day x.
  {
    ipso (year.antecedence.restoration (day &x)).
  }
  leibniz &restored in |- *.
  leibniz
    (BinWithZero.addition.associativity
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
    : forall (a : BinWithZero) (b : BinWithZero) . a + 1 < b + 1 -> a < b.
  {
    intros a b g.
    simpl BinWithZero.LessThan in &g |- *.
    match &g with | k e end.
    exists &k.
    leibniz
      (BinWithZero.addition.associativity &a 1 k),
      (BinWithZero.addition.commutativity 1 k),
      <- (BinWithZero.addition.associativity &a k 1)
      in &e.
    match (BinWithZero.addition.cancellation (&a + k) 1 &b) with | _ right end.
    ipso (&right &e).
  }
  lemma widened
    : forall (d1 : BinBase) (d2 : BinBase) . (d1 < d2)%bin_base -> (d1 : BinWithZero) < d2.
  {
    intros d1 d2 g.
    match &g with | k e end.
    simpl BinWithZero.LessThan in |- *.
    exists &k.
    ipso (congru BinWithZero.Positive, &e).
  }
  lemma ordered
    : days_before_year (year x1) + day_of_year x1 < days_before_year (year x2) + day_of_year x2.
  {
    match &x1 with | introduction y1 m1 d1 a1 end.
    match &x2 with | introduction y2 m2 d2 a2 end.
    simpl compare, year, month, day in &h.
    match (BinBase.compare &y1 &y2) with | | | end |- cy.
    - match (BinBase.comparison.specification &y1 &y2) with | year_order _ end.
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
                  (BinWithZero.addition.order.strict.monotonicity
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
        match (BinWithZero.addition.identity (days_before_year &y2)) with | _ plus_zero end.
        let proof s :=
          BinWithZero.addition.order.strict.monotonicity
            (days_before_year &y2) 0%bin_with_zero
            (days_before_year &y2) (day_of_year (introduction &y2 &m2 &d2 &a2))
            (disjoin (refl (days_before_year &y2)), _)
            (ordinal.positivity (introduction &y2 &m2 &d2 &a2)).
        leibniz &plus_zero in &s.
        ipso &s.
      }
      ipso (Comparable.order.mixed.left.transitivity
              (@Comparable.order.transitivity _ BinWithZero.compare BinWithZero.LessThan _
                 (days_before_year &y1 + day_of_year (introduction &y1 &m1 &d1 &a1))
                 (days_before_year &y1 + days_in_year &y1)
                 (days_before_year &y2)
                 &first &second)
              &third).
    - match (BinBase.comparison.specification &y1 &y2) with | _ year_equality end.
      let proof ey := modus aequans &year_equality, &cy.
      match &ey with | end.
      lemma inner
        : days_before_month y1 m1 + d1 < days_before_month y1 m2 + d2.
      {
        match (Month.compare &m1 &m2) with | | | end |- cm.
        + lemma valid : (d1 : BinWithZero) <= days_in_month y1 m1.
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
                      (BinWithZero.addition.order.strict.monotonicity
                         (days_before_month &y1 &m1) d1
                         (days_before_month &y1 &m1) (days_in_month &y1 &m1)
                         (disjoin (refl (days_before_month &y1 &m1)), _) &smaller)).
          }
          lemma third : days_before_month y1 m2 < days_before_month y1 m2 + d2.
          {
            match (BinWithZero.addition.identity (days_before_month &y1 &m2))
              with | _ plus_zero end.
            lemma positive : 0%bin_with_zero < d2.
            {
              simpl BinWithZero.LessThan in |- *.
              exists &d2.
              simpl in |- *.
              quod idem est.
            }
            let proof s :=
              BinWithZero.addition.order.strict.monotonicity
                (days_before_month &y1 &m2) 0%bin_with_zero
                (days_before_month &y1 &m2) d2
                (disjoin (refl (days_before_month &y1 &m2)), _) &positive.
            leibniz &plus_zero in &s.
            ipso &s.
          }
          ipso (Comparable.order.mixed.left.transitivity
                  (@Comparable.order.transitivity _ BinWithZero.compare BinWithZero.LessThan _
                     (days_before_month &y1 &m1 + d1)
                     (days_before_month &y1 &m1 + days_in_month &y1 &m1)
                     (days_before_month &y1 &m2)
                     &first (month.monotonicity &y1 &m1 &m2 &cm))
                  &third).
        + match (Month.comparison.specification &m1 &m2) with | _ month_equality end.
          let proof em := modus aequans &month_equality, &cm.
          match &em with | end.
          match (BinBase.comparison.specification &d1 &d2) with | day_order _ end.
          let proof smaller := modus aequans &day_order, &h.
          ipso (BinWithZero.addition.order.strict.monotonicity
                  (days_before_month &y1 &m1) d1 (days_before_month &y1 &m1) d2
                  (disjoin (refl (days_before_month &y1 &m1)), _)
                  (&widened &d1 &d2 &smaller)).
        + ex &h quodlibet.
      }
      ipso (BinWithZero.addition.order.strict.monotonicity
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
      compare x1 x2 = BinWithZero.compare (day_number x1) (day_number x2).
Proof.
  intros x1 x2.
  match (compare &x1 &x2) with | | | end |- c.
  - let proof smaller := number.monotonicity &x1 &x2 &c.
    match (BinWithZero.comparison.specification (day_number &x1) (day_number &x2))
      with | strict _ end.
    ipso (symm (modus aequans &strict, &smaller)).
  - match (separation &x1 &x2 &c) with | end.
    ipso (symm (@Comparable.comparison.reflexivity _ BinWithZero.compare BinWithZero.LessThan _
                  (day_number &x1))).
  - lemma reversed : compare x2 x1 = Comparison.Lt.
    {
      leibniz (antisymmetry &x2 &x1), &c in |- *.
      simpl in |- *.
      quod idem est.
    }
    let proof smaller := number.monotonicity &x2 &x1 &reversed.
    match (BinWithZero.comparison.specification (day_number &x2) (day_number &x1))
      with | strict _ end.
    let proof below := modus aequans &strict, &smaller.
    leibniz
      (BinWithZero.comparison.antisymmetry (day_number &x1) (day_number &x2)), &below
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
    match (BinWithZero.comparison.specification (day_number &x1) (day_number &x2))
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
    ipso (@Comparable.comparison.reflexivity _ BinWithZero.compare BinWithZero.LessThan _
            (day_number &x2)).
  }
  ipso (separation &x1 &x2 &same).
Qed.

End number. (* number *)

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
  ipso (modus aequans (number.order &x1 &x3), (BinWithZero.order.strict.transitivity &n1 &n2)).
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
      ipso (@Comparable.comparison.reflexivity _ BinWithZero.compare BinWithZero.LessThan _
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
