(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

From JW Require Import Data.Calendar.All.

Local Open Scope jw_bin_decimal_scope.

Definition data_calendar_all_delivers_month
  : Month
  := Month.January.

Definition data_calendar_all_delivers_month_conversion_bin_retraction
  : forall (m : Month) . Month.from_b (Month.to_b m) = Some m
  := Month.conversion.bin.retraction.

Definition data_calendar_all_delivers_month_conversion_bin_specification
  : forall (n : Bin) (m : Month) . Month.from_b n = Some m <-> Month.to_b m = n
  := Month.conversion.bin.specification.

Definition data_calendar_all_delivers_month_conversion_bin0_retraction
  : forall (m : Month) . Month.from_b0 (Month.to_b0 m) = Some m
  := Month.conversion.bin0.retraction.

Definition data_calendar_all_delivers_month_conversion_bin0_specification
  : forall (k : Bin0) (m : Month) . Month.from_b0 k = Some m <-> Month.to_b0 m = k
  := Month.conversion.bin0.specification.

Definition data_calendar_all_delivers_month_succession_forward_inverse
  : forall (m : Month) . Month.prev (Month.next m) = m
  := Month.succession.forward.inverse.

Definition data_calendar_all_delivers_month_succession_backward_inverse
  : forall (m : Month) . Month.next (Month.prev m) = m
  := Month.succession.backward.inverse.

Definition data_calendar_all_delivers_month_comparable
  : Comparable Month.compare Month.LessThan
  := _.

Definition data_calendar_all_computes_month_to_b
  : Month.to_b Month.December = 12
  := Identity.reflexivity _.

Definition data_calendar_all_computes_month_from_b
  : Month.from_b 9 = Some Month.September
  := Identity.reflexivity _.

Definition data_calendar_all_computes_month_from_b_refusal
  : Month.from_b 13 = None
  := Identity.reflexivity _.

Definition data_calendar_all_computes_month_to_b0
  : Month.to_b0 Month.December = 11%b0_decimal
  := Identity.reflexivity _.

Definition data_calendar_all_computes_month_from_b0
  : Month.from_b0 0%b0_decimal = Some Month.January
  := Identity.reflexivity _.

Definition data_calendar_all_computes_month_from_b0_refusal
  : Month.from_b0 12%b0_decimal = None
  := Identity.reflexivity _.

Definition data_calendar_all_computes_month_next
  : Month.next Month.December = Month.January
  := Identity.reflexivity _.

Definition data_calendar_all_computes_month_prev
  : Month.prev Month.January = Month.December
  := Identity.reflexivity _.

Definition data_calendar_all_computes_month_compare
  : Month.compare Month.March Month.October = Comparison.Lt
  := Identity.reflexivity _.

Definition data_calendar_all_delivers_weekday
  : Weekday
  := Weekday.Monday.

Definition data_calendar_all_delivers_weekday_conversion_bin_retraction
  : forall (w : Weekday) . Weekday.from_b (Weekday.to_b w) = Some w
  := Weekday.conversion.bin.retraction.

Definition data_calendar_all_delivers_weekday_conversion_bin_specification
  : forall (n : Bin) (w : Weekday) . Weekday.from_b n = Some w <-> Weekday.to_b w = n
  := Weekday.conversion.bin.specification.

Definition data_calendar_all_delivers_weekday_conversion_bin0_retraction
  : forall (w : Weekday) . Weekday.from_b0 (Weekday.to_b0 w) = Some w
  := Weekday.conversion.bin0.retraction.

Definition data_calendar_all_delivers_weekday_conversion_bin0_specification
  : forall (k : Bin0) (w : Weekday) . Weekday.from_b0 k = Some w <-> Weekday.to_b0 w = k
  := Weekday.conversion.bin0.specification.

Definition data_calendar_all_delivers_weekday_succession_forward_inverse
  : forall (w : Weekday) . Weekday.prev (Weekday.next w) = w
  := Weekday.succession.forward.inverse.

Definition data_calendar_all_delivers_weekday_succession_backward_inverse
  : forall (w : Weekday) . Weekday.next (Weekday.prev w) = w
  := Weekday.succession.backward.inverse.

Definition data_calendar_all_computes_weekday_to_b
  : Weekday.to_b Weekday.Sunday = 7
  := Identity.reflexivity _.

Definition data_calendar_all_computes_weekday_from_b_refusal
  : Weekday.from_b 8 = None
  := Identity.reflexivity _.

Definition data_calendar_all_computes_weekday_to_b0
  : Weekday.to_b0 Weekday.Sunday = 6%b0_decimal
  := Identity.reflexivity _.

Definition data_calendar_all_computes_weekday_from_b0_refusal
  : Weekday.from_b0 7%b0_decimal = None
  := Identity.reflexivity _.

Definition data_calendar_all_computes_weekday_next
  : Weekday.next Weekday.Sunday = Weekday.Monday
  := Identity.reflexivity _.

Definition data_calendar_all_computes_weekday_prev
  : Weekday.prev Weekday.Monday = Weekday.Sunday
  := Identity.reflexivity _.

Definition data_calendar_all_delivers_date
  : Date
  := Date.introduction 2024 Month.February 29 I.

Definition data_calendar_all_computes_date_leap_1900
  : Date.is_leap 1900 = false
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_leap_2000
  : Date.is_leap 2000 = true
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_leap_2023
  : Date.is_leap 2023 = false
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_leap_2024
  : Date.is_leap 2024 = true
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_days_in_common_year
  : Date.days_in_common_year = 365
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_days_in_quadrennium
  : Date.days_in_quadrennium = 1461
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_days_in_century
  : Date.days_in_century = 36524
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_days_in_quadricentennium
  : Date.days_in_quadricentennium = 146097
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_day_number_0001_01_01
  : Date.day_number (Date.introduction 1 Month.January 1 I) = 0%b0_decimal
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_day_number_0004_12_31
  : Date.day_number (Date.introduction 4 Month.December 31 I) = 1460%b0_decimal
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_day_number_0100_12_31
  : Date.day_number (Date.introduction 100 Month.December 31 I) = 36523%b0_decimal
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_day_number_0400_12_31
  : Date.day_number (Date.introduction 400 Month.December 31 I) = 146096%b0_decimal
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_day_number_1970_01_01
  : Date.day_number (Date.introduction 1970 Month.January 1 I) = 719162%b0_decimal
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_day_number_2000_01_01
  : Date.day_number (Date.introduction 2000 Month.January 1 I) = 730119%b0_decimal
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_day_number_2024_02_29
  : Date.day_number (Date.introduction 2024 Month.February 29 I) = 738944%b0_decimal
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_day_number_9999_12_31
  : Date.day_number (Date.introduction 9999 Month.December 31 I) = 3652058%b0_decimal
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_days_before_year_2001
  : Date.days_before_year 2001 = 730485%b0_decimal
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_days_before_year_10000
  : Date.days_before_year 10000 = 3652059%b0_decimal
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_day_of_year_2024_12_31
  : Date.day_of_year (Date.introduction 2024 Month.December 31 I) = 366
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_make
  : Date.make 2024 Month.February 29 = Some (Date.introduction 2024 Month.February 29 I)
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_make_refusal_2023_02_29
  : Date.make 2023 Month.February 29 = None
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_make_refusal_1900_02_29
  : Date.make 1900 Month.February 29 = None
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_make_refusal_2024_04_31
  : Date.make 2024 Month.April 31 = None
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_compare
  : Date.compare
      (Date.introduction 1970 Month.January 1 I) (Date.introduction 2000 Month.January 1 I)
    = Comparison.Lt
  := Identity.reflexivity _.

Definition data_calendar_all_delivers_date_leap_periodicity
  : forall (y : Bin) . Date.is_leap (y + 400%b_decimal)%b = Date.is_leap y
  := Date.leap.periodicity.

Definition data_calendar_all_delivers_date_month_length_boundedness
  : forall (y : Bin) (m : Month) .
      (28%b_decimal <= Date.days_in_month y m
       /\ Date.days_in_month y m <= 31%b_decimal)%b
  := Date.month.length.boundedness.

Definition data_calendar_all_delivers_date_month_succession
  : forall (y : Bin) (m : Month) .
      ~ (m = Month.December)
      -> Date.days_before_month y (Month.next m)
         = (Date.days_before_month y m + Date.days_in_month y m)%b0
  := Date.month.succession.

Definition data_calendar_all_delivers_date_month_completion
  : forall (y : Bin) .
      (Date.days_before_month y Month.December + 31%b_decimal)%b0
      = Date.days_in_year y
  := Date.month.completion.

Definition data_calendar_all_delivers_date_month_boundedness
  : forall (y : Bin) (m : Month) .
      (Date.days_before_month y m + Date.days_in_month y m <= Date.days_in_year y)%b0
  := Date.month.boundedness.

Definition data_calendar_all_delivers_date_year_length_dichotomy
  : forall (y : Bin) . Date.days_in_year y = 365 \/ Date.days_in_year y = 366
  := Date.year.length.dichotomy.

Definition data_calendar_all_delivers_date_year_length_specification
  : forall (y : Bin) . Date.days_in_year y = 366 <-> Date.is_leap y = true
  := Date.year.length.specification.

Definition data_calendar_all_delivers_date_ordinal_decomposition
  : forall (x : Date) .
      (Date.day_of_year x : Bin0)
      = (Date.days_before_month (Date.year x) (Date.month x) + Date.day x)%b0
  := Date.ordinal.decomposition.

Definition data_calendar_all_delivers_date_ordinal_boundedness
  : forall (x : Date) . (Date.day_of_year x <= Date.days_in_year (Date.year x))%b0
  := Date.ordinal.boundedness.

Definition data_calendar_all_delivers_date_year_antecedence_translation
  : forall (y : Bin) (k : Bin) .
      Date.years_before (y + k)%b = (Date.years_before y + k)%b0
  := Date.year.antecedence.translation.

Definition data_calendar_all_delivers_date_year_periodicity
  : forall (y : Bin) .
      Date.days_before_year (y + 400%b_decimal)%b
      = (Date.days_before_year y + Date.days_in_quadricentennium)%b0
  := Date.year.periodicity.

Definition data_calendar_all_delivers_date_year_antecedence_restoration
  : forall (y : Bin) . (Date.years_before y + 1%b_decimal)%b0 = y
  := Date.year.antecedence.restoration.

Definition data_calendar_all_delivers_date_year_succession
  : forall (y : Bin) .
      Date.days_before_year (y + 1)%b
      = (Date.days_before_year y + Date.days_in_year y)%b0
  := Date.year.succession.

Definition data_calendar_all_delivers_date_year_monotonicity
  : forall (y : Bin) (k : Bin) .
      (Date.days_before_year y + Date.days_in_year y
       <= Date.days_before_year (y + k)%b)%b0
  := Date.year.monotonicity.

Definition data_calendar_all_delivers_date_month_monotonicity
  : forall (y : Bin) (m1 : Month) (m2 : Month) .
      Month.compare m1 m2 = Comparison.Lt
      -> (Date.days_before_month y m1 + Date.days_in_month y m1
          <= Date.days_before_month y m2)%b0
  := Date.month.monotonicity.

Definition data_calendar_all_delivers_date_validity_boundedness
  : forall (x : Date) .
      (Date.day x <= Date.days_in_month (Date.year x) (Date.month x))%b0
  := Date.validity.boundedness.

Definition data_calendar_all_delivers_date_antisymmetry
  : forall (x1 : Date) (x2 : Date) .
      Date.compare x1 x2 = Comparison.transpose (Date.compare x2 x1)
  := Date.antisymmetry.

Definition data_calendar_all_delivers_date_separation
  : forall (x1 : Date) (x2 : Date) . Date.compare x1 x2 = Comparison.Eq -> x1 = x2
  := Date.separation.

Definition data_calendar_all_delivers_date_number_decomposition
  : forall (x : Date) .
      (Date.day_number x + 1%b_decimal)%b0
      = (Date.days_before_year (Date.year x) + Date.day_of_year x)%b0
  := Date.number.decomposition.

Definition data_calendar_all_delivers_date_number_comparison
  : forall (x1 : Date) (x2 : Date) .
      Date.compare x1 x2 = Bin0.compare (Date.day_number x1) (Date.day_number x2)
  := Date.number.comparison.

Definition data_calendar_all_delivers_date_number_order
  : forall (x1 : Date) (x2 : Date) .
      Date.LessThan x1 x2 <-> (Date.day_number x1 < Date.day_number x2)%b0
  := Date.number.order.

Definition data_calendar_all_delivers_date_number_injectivity
  : forall (x1 : Date) (x2 : Date) . Date.day_number x1 = Date.day_number x2 -> x1 = x2
  := @Date.number.injectivity.

Definition data_calendar_all_delivers_date_comparable
  : Comparable Date.compare Date.LessThan
  := _.

Definition data_calendar_all_delivers_date_calendar_boundedness
  : forall (y : Bin) (days : Bin0) .
      (days < Date.days_in_year y)%b0
      -> (Date.days_before_month y (Date.month_after_days y days) <= days)%b0
         /\ (days
             < Date.days_before_month y (Date.month_after_days y days)
               + Date.days_in_month y (Date.month_after_days y days))%b0
  := Date.calendar.boundedness.

Definition data_calendar_all_delivers_date_calendar_validity
  : forall (y : Bin) (days : Bin0) .
      (days < Date.days_in_year y)%b0
      -> Assert
           (Date.is_valid y (Date.month_after_days y days) (Date.day_of_month_after_days y days))
  := Date.calendar.validity.

Definition data_calendar_all_delivers_date_calendar_ordinal_validity
  : forall (y : Bin) (d : Bin) .
      Assert (Comparable.le Bin.compare d (Date.days_in_year y))
      -> Assert
           (Date.is_valid y
              (Date.month_after_days y (Bin0.saturating_sub d 1))
              (Date.day_of_month_after_days y (Bin0.saturating_sub d 1)))
  := Date.calendar.ordinal.validity.

Definition data_calendar_all_delivers_date_calendar_inversion
  : forall (y : Bin) (m : Month) (d : Bin) .
      Assert (Date.is_valid y m d)
      -> Date.calendar_date_after_days y
           (Date.days_before_month y m + Bin0.saturating_sub d 1)%b0
         = (m, d)%product
  := Date.calendar.inversion.

Definition data_calendar_all_delivers_date_calendar_reconstruction
  : forall (y : Bin) (days : Bin0) .
      (days < Date.days_in_year y)%b0
      -> (Date.days_before_month y (Date.month_after_days y days)
            + Bin0.saturating_sub (Date.day_of_month_after_days y days) 1)%b0
         = days
  := Date.calendar.reconstruction.

Definition data_calendar_all_delivers_date_division_boundedness
  : forall (n : Bin0) .
      (Product.second (Date.div_year n)
       < Date.days_in_year (Bin0.successor (Product.first (Date.div_year n))))%b0
  := Date.division.boundedness.

Definition data_calendar_all_delivers_date_division_reconstruction
  : forall (n : Bin0) .
      (Date.days_before_year (Bin0.successor (Product.first (Date.div_year n)))
         + Product.second (Date.div_year n))%b0
      = n
  := Date.division.reconstruction.

Definition data_calendar_all_delivers_date_ordinal_section
  : forall (x : Date) . Date.from_day_of_year (Date.year x) (Date.day_of_year x) = Some x
  := Date.ordinal.section.

Definition data_calendar_all_delivers_date_number_retraction
  : forall (n : Bin0) . Date.day_number (Date.from_day_number n) = n
  := Date.number.retraction.

Definition data_calendar_all_delivers_date_number_section
  : forall (x : Date) . Date.from_day_number (Date.day_number x) = x
  := Date.number.section.

Definition data_calendar_all_delivers_date_weekday_totality
  : forall (n : Bin0) . ~ (Weekday.from_b0 (Bin0.modulo n Weekday.days_in_week) = None)
  := Date.weekday.totality.

Definition data_calendar_all_delivers_date_weekday_succession
  : forall (n : Bin0) .
      Date.weekday_of_day_number (n + 1%b_decimal)%b0
      = Weekday.next (Date.weekday_of_day_number n)
  := Date.weekday.succession.

Definition data_calendar_all_delivers_date_weekday_periodicity
  : forall (n : Bin0) .
      Date.weekday_of_day_number (n + Weekday.days_in_week)%b0 = Date.weekday_of_day_number n
  := Date.weekday.periodicity.

Definition data_calendar_all_delivers_date_weekday_quadricentennium_periodicity
  : forall (n : Bin0) .
      Date.weekday_of_day_number (n + Date.days_in_quadricentennium)%b0
      = Date.weekday_of_day_number n
  := Date.weekday.quadricentennium.periodicity.

Definition data_calendar_all_computes_date_from_day_number_0
  : Date.compare (Date.from_day_number 0%b0_decimal) (Date.introduction 1 Month.January 1 I)
    = Comparison.Eq
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_from_day_number_1460
  : Date.compare (Date.from_day_number 1460%b0_decimal) (Date.introduction 4 Month.December 31 I)
    = Comparison.Eq
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_from_day_number_36523
  : Date.compare
      (Date.from_day_number 36523%b0_decimal) (Date.introduction 100 Month.December 31 I)
    = Comparison.Eq
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_from_day_number_146096
  : Date.compare
      (Date.from_day_number 146096%b0_decimal) (Date.introduction 400 Month.December 31 I)
    = Comparison.Eq
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_from_day_number_738944
  : Date.compare
      (Date.from_day_number 738944%b0_decimal) (Date.introduction 2024 Month.February 29 I)
    = Comparison.Eq
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_from_day_number_739940
  : Date.compare
      (Date.from_day_number 739940%b0_decimal) (Date.introduction 2026 Month.November 21 I)
    = Comparison.Eq
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_from_day_number_3652058
  : Date.compare
      (Date.from_day_number 3652058%b0_decimal) (Date.introduction 9999 Month.December 31 I)
    = Comparison.Eq
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_from_day_of_year_2024_60
  : Option.map Date.day_number (Date.from_day_of_year 2024 60) = Some 738944%b0_decimal
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_from_day_of_year_2024_366
  : Option.map Date.day_number (Date.from_day_of_year 2024 366) = Some 739250%b0_decimal
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_from_day_of_year_refusal_2023_366
  : Option.map Date.day_number (Date.from_day_of_year 2023 366) = None
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_weekday_0001_01_01
  : Date.weekday (Date.introduction 1 Month.January 1 I) = Weekday.Monday
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_weekday_0400_12_31
  : Date.weekday (Date.introduction 400 Month.December 31 I) = Weekday.Sunday
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_weekday_1970_01_01
  : Date.weekday (Date.introduction 1970 Month.January 1 I) = Weekday.Thursday
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_weekday_2000_01_01
  : Date.weekday (Date.introduction 2000 Month.January 1 I) = Weekday.Saturday
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_weekday_2026_11_21
  : Date.weekday (Date.introduction 2026 Month.November 21 I) = Weekday.Saturday
  := Identity.reflexivity _.
