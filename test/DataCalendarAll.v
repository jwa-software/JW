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
      (x1 < x2)%date <-> (Date.day_number x1 < Date.day_number x2)%b0
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

Definition data_calendar_all_delivers_date_extensionality
  : forall (x1 : Date) (x2 : Date) .
      Date.year x1 = Date.year x2 -> Date.month x1 = Date.month x2 -> Date.day x1 = Date.day x2
      -> x1 = x2
  := Date.extensionality.

Definition data_calendar_all_delivers_date_year_antecedence_section
  : forall (y : Bin) . Bin0.successor (Date.years_before y) = y
  := Date.year.antecedence.section.

Definition data_calendar_all_delivers_date_month_validity_minimum
  : forall (y : Bin) (m : Month) . Assert (Date.is_valid y m 1)
  := Date.month.validity.minimum.

Definition data_calendar_all_delivers_date_month_validity_maximum
  : forall (y : Bin) (m : Month) . Assert (Date.is_valid y m (Date.days_in_month y m))
  := Date.month.validity.maximum.

Definition data_calendar_all_delivers_date_month_validity_clamping
  : forall (y : Bin) (m : Month) (n : Bin) .
      Assert (Date.is_valid y m (Bin.min n (Date.days_in_month y m)))
  := Date.month.validity.clamping.

Definition data_calendar_all_delivers_date_month_totality
  : forall (n : Bin0) . ~ (Month.from_b0 (n %. Month.months_in_year)%b0 = None)
  := Date.month.totality.

Definition data_calendar_all_delivers_date_first_month_specification
  : forall (d : Date) .
      Date.year (Date.first_day_of_month d) = Date.year d
      /\ Date.month (Date.first_day_of_month d) = Date.month d
      /\ Date.day (Date.first_day_of_month d) = 1
  := Date.first.month.specification.

Definition data_calendar_all_delivers_date_first_month_decomposition
  : forall (d : Date) .
      Date.day_number (Date.first_day_of_month d)
      = (Date.days_before_year (Date.year d) + Date.days_before_month (Date.year d) (Date.month d))%b0
  := Date.first.month.decomposition.

Definition data_calendar_all_delivers_date_first_month_order
  : forall (d : Date) . (Date.day_number (Date.first_day_of_month d) <= Date.day_number d)%b0
  := Date.first.month.order.

Definition data_calendar_all_delivers_date_first_year_specification
  : forall (d : Date) .
      Date.year (Date.first_day_of_year d) = Date.year d
      /\ Date.month (Date.first_day_of_year d) = Month.January
      /\ Date.day (Date.first_day_of_year d) = 1
  := Date.first.year.specification.

Definition data_calendar_all_delivers_date_first_year_decomposition
  : forall (d : Date) . Date.day_number (Date.first_day_of_year d) = Date.days_before_year (Date.year d)
  := Date.first.year.decomposition.

Definition data_calendar_all_delivers_date_first_year_order
  : forall (d : Date) . (Date.day_number (Date.first_day_of_year d) <= Date.day_number d)%b0
  := Date.first.year.order.

Definition data_calendar_all_delivers_date_last_month_specification
  : forall (d : Date) .
      Date.year (Date.last_day_of_month d) = Date.year d
      /\ Date.month (Date.last_day_of_month d) = Date.month d
      /\ Date.day (Date.last_day_of_month d) = Date.days_in_month (Date.year d) (Date.month d)
  := Date.last.month.specification.

Definition data_calendar_all_delivers_date_last_month_decomposition
  : forall (d : Date) .
      (Date.day_number (Date.last_day_of_month d) + 1
       = Date.days_before_year (Date.year d)
         + (Date.days_before_month (Date.year d) (Date.month d)
            + Date.days_in_month (Date.year d) (Date.month d)))%b0
  := Date.last.month.decomposition.

Definition data_calendar_all_delivers_date_last_month_order
  : forall (d : Date) . (Date.day_number d <= Date.day_number (Date.last_day_of_month d))%b0
  := Date.last.month.order.

Definition data_calendar_all_delivers_date_last_year_specification
  : forall (d : Date) .
      Date.year (Date.last_day_of_year d) = Date.year d
      /\ Date.month (Date.last_day_of_year d) = Month.December
      /\ Date.day (Date.last_day_of_year d) = 31
  := Date.last.year.specification.

Definition data_calendar_all_delivers_date_last_year_decomposition
  : forall (d : Date) .
      (Date.day_number (Date.last_day_of_year d) + 1
       = Date.days_before_year (Date.year d) + Date.days_in_year (Date.year d))%b0
  := Date.last.year.decomposition.

Definition data_calendar_all_delivers_date_last_year_order
  : forall (d : Date) . (Date.day_number d <= Date.day_number (Date.last_day_of_year d))%b0
  := Date.last.year.order.

Definition data_calendar_all_delivers_date_addition_specification
  : forall (x : Date) (k : Bin0) .
      Date.day_number (Date.add_days x k) = (Date.day_number x + k)%b0
  := Date.addition.specification.

Definition data_calendar_all_delivers_date_addition_identity
  : forall (x : Date) . Date.add_days x 0%b0 = x
  := Date.addition.identity.

Definition data_calendar_all_delivers_date_addition_associativity
  : forall (x : Date) (k : Bin0) (l : Bin0) .
      Date.add_days (Date.add_days x k) l = Date.add_days x (k + l)%b0
  := Date.addition.associativity.

Definition data_calendar_all_delivers_date_addition_month_specification
  : forall (d : Date) (k : Bin0) .
      Date.month_number (Date.add_months d k) = (Date.month_number d + k)%b0
      /\ Date.day (Date.add_months d k)
         = Bin.min (Date.day d)
             (Date.days_in_month (Date.year (Date.add_months d k)) (Date.month (Date.add_months d k)))
  := Date.addition.month.specification.

Definition data_calendar_all_delivers_date_addition_month_preservation
  : forall (d : Date) (k : Bin0) .
      (Date.day d
       <= Date.days_in_month (Date.year (Date.add_months d k)) (Date.month (Date.add_months d k)))%b
      -> Date.day (Date.add_months d k) = Date.day d
  := Date.addition.month.preservation.

Definition data_calendar_all_delivers_date_addition_month_identity
  : forall (d : Date) . Date.add_months d 0%b0 = d
  := Date.addition.month.identity.

Definition data_calendar_all_delivers_date_addition_year_specification
  : forall (d : Date) (k : Bin0) .
      (Date.year (Date.add_years d k) : Bin0) = (Date.year d + k)%b0
      /\ Date.month (Date.add_years d k) = Date.month d
      /\ Date.day (Date.add_years d k)
         = Bin.min (Date.day d) (Date.days_in_month (Date.year (Date.add_years d k)) (Date.month d))
  := Date.addition.year.specification.

Definition data_calendar_all_delivers_date_addition_year_preservation
  : forall (d : Date) (k : Bin0) .
      (Date.day d <= Date.days_in_month (Date.year (Date.add_years d k)) (Date.month d))%b
      -> Date.day (Date.add_years d k) = Date.day d
  := Date.addition.year.preservation.

Definition data_calendar_all_delivers_date_addition_year_identity
  : forall (d : Date) . Date.add_years d 0%b0 = d
  := Date.addition.year.identity.

Definition data_calendar_all_delivers_date_addition_year_reduction
  : forall (d : Date) (k : Bin0) .
      Date.add_years d k = Date.add_months d (k * Month.months_in_year)%b0
  := Date.addition.year.reduction.

Definition data_calendar_all_delivers_date_subtraction_inversion_addition
  : forall (x : Date) (k : Bin0) . Date.subtract_days (Date.add_days x k) k = Some x
  := Date.subtraction.inversion.addition.

Definition data_calendar_all_delivers_date_subtraction_specification
  : forall (x : Date) (k : Bin0) (y : Date) .
      Date.subtract_days x k = Some y <-> Date.add_days y k = x
  := Date.subtraction.specification.

Definition data_calendar_all_delivers_date_subtraction_failure
  : forall (x : Date) (k : Bin0) .
      Date.subtract_days x k = None <-> (Date.day_number x < k)%b0
  := Date.subtraction.failure.

Definition data_calendar_all_delivers_date_succession_specification
  : forall (x : Date) . Date.day_number (Date.next_day x) = (Date.day_number x + 1)%b0
  := Date.succession.specification.

Definition data_calendar_all_delivers_date_succession_inversion
  : forall (x : Date) (y : Date) . Date.previous_day x = Some y <-> Date.next_day y = x
  := Date.succession.inversion.

Definition data_calendar_all_delivers_date_succession_origin
  : forall (d : Date) .
      Date.previous_day d = None <-> (Date.year d = 1 /\ d = Date.first_day_of_year d)
  := Date.succession.origin.

Definition data_calendar_all_delivers_date_difference_specification
  : forall (x : Date) (k : Bin0) . Date.days_between x (Date.add_days x k) = k
  := Date.difference.specification.

Definition data_calendar_all_delivers_date_unix_addition
  : forall (d : Date) (k : Bin0) .
      Date.unix_day (Date.add_days d k) = (Date.unix_day d + k)%b_signed
  := Date.unix.addition.

Definition data_calendar_all_delivers_date_unix_section
  : forall (d : Date) . Date.from_unix_day (Date.unix_day d) = Some d
  := Date.unix.section.

Definition data_calendar_all_delivers_date_unix_specification
  : forall (u : SignedBin) (d : Date) . Date.from_unix_day u = Some d <-> Date.unix_day d = u
  := Date.unix.specification.

Definition data_calendar_all_computes_date_less_or_equal
  : (Date.introduction 1970 Month.January 1 I <= Date.introduction 2000 Month.January 1 I)%date
  := Disjunction.introduction_right (Identity.reflexivity _).

Definition data_calendar_all_computes_date_next_day_2023_12_31
  : Date.compare
      (Date.next_day (Date.introduction 2023 Month.December 31 I))
      (Date.introduction 2024 Month.January 1 I)
    = Comparison.Eq
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_add_days_2024_02_28
  : Date.compare
      (Date.add_days (Date.introduction 2024 Month.February 28 I) 1%b0_decimal)
      (Date.introduction 2024 Month.February 29 I)
    = Comparison.Eq
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_subtract_days_2024_03_01
  : Option.map Date.day_number
      (Date.subtract_days (Date.introduction 2024 Month.March 1 I) 1%b0_decimal)
    = Some 738944%b0_decimal
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_previous_day_refusal_0001_01_01
  : Date.previous_day (Date.introduction 1 Month.January 1 I) = None
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_days_between_2000_01_01_2024_02_29
  : Date.days_between
      (Date.introduction 2000 Month.January 1 I) (Date.introduction 2024 Month.February 29 I)
    = 8825%b0_decimal
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_days_between_2024_02_29_2000_01_01
  : Date.days_between
      (Date.introduction 2024 Month.February 29 I) (Date.introduction 2000 Month.January 1 I)
    = (- 8825%b0_decimal)%b_signed
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_first_day_of_month_2024_07_15
  : Date.compare
      (Date.first_day_of_month (Date.introduction 2024 Month.July 15 I))
      (Date.introduction 2024 Month.July 1 I)
    = Comparison.Eq
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_last_day_of_month_2024_02_10
  : Date.compare
      (Date.last_day_of_month (Date.introduction 2024 Month.February 10 I))
      (Date.introduction 2024 Month.February 29 I)
    = Comparison.Eq
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_last_day_of_month_2023_02_10
  : Date.compare
      (Date.last_day_of_month (Date.introduction 2023 Month.February 10 I))
      (Date.introduction 2023 Month.February 28 I)
    = Comparison.Eq
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_first_day_of_year_2024_07_15
  : Date.compare
      (Date.first_day_of_year (Date.introduction 2024 Month.July 15 I))
      (Date.introduction 2024 Month.January 1 I)
    = Comparison.Eq
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_last_day_of_year_2024_07_15
  : Date.compare
      (Date.last_day_of_year (Date.introduction 2024 Month.July 15 I))
      (Date.introduction 2024 Month.December 31 I)
    = Comparison.Eq
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_month_number_2024_03_15
  : Date.month_number (Date.introduction 2024 Month.March 15 I) = 24278%b0_decimal
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_add_months_2024_01_31
  : Date.compare
      (Date.add_months (Date.introduction 2024 Month.January 31 I) 1%b0_decimal)
      (Date.introduction 2024 Month.February 29 I)
    = Comparison.Eq
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_add_months_2023_01_31
  : Date.compare
      (Date.add_months (Date.introduction 2023 Month.January 31 I) 1%b0_decimal)
      (Date.introduction 2023 Month.February 28 I)
    = Comparison.Eq
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_add_months_2024_03_15
  : Date.compare
      (Date.add_months (Date.introduction 2024 Month.March 15 I) 11%b0_decimal)
      (Date.introduction 2025 Month.February 15 I)
    = Comparison.Eq
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_add_months_stepwise_2024_01_31
  : Date.compare
      (Date.add_months
         (Date.add_months (Date.introduction 2024 Month.January 31 I) 1%b0_decimal) 1%b0_decimal)
      (Date.introduction 2024 Month.March 29 I)
    = Comparison.Eq
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_add_months_whole_2024_01_31
  : Date.compare
      (Date.add_months (Date.introduction 2024 Month.January 31 I) 2%b0_decimal)
      (Date.introduction 2024 Month.March 31 I)
    = Comparison.Eq
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_add_years_2024_02_29
  : Date.compare
      (Date.add_years (Date.introduction 2024 Month.February 29 I) 1%b0_decimal)
      (Date.introduction 2025 Month.February 28 I)
    = Comparison.Eq
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_add_years_2024_02_29_by_4
  : Date.compare
      (Date.add_years (Date.introduction 2024 Month.February 29 I) 4%b0_decimal)
      (Date.introduction 2028 Month.February 29 I)
    = Comparison.Eq
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_unix_epoch
  : Date.day_number Date.unix_epoch = 719162%b0_decimal
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_unix_day_1970_01_01
  : Date.unix_day (Date.introduction 1970 Month.January 1 I) = 0%b_signed
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_unix_day_2000_01_01
  : Date.unix_day (Date.introduction 2000 Month.January 1 I) = 10957%b0_decimal
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_unix_day_0001_01_01
  : Date.unix_day (Date.introduction 1 Month.January 1 I) = (- 719162%b0_decimal)%b_signed
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_from_unix_day_0
  : Option.map Date.day_number (Date.from_unix_day 0%b_signed) = Some 719162%b0_decimal
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_from_unix_day_refusal
  : Date.from_unix_day (- 719163%b0_decimal)%b_signed = None
  := Identity.reflexivity _.

Definition data_calendar_all_delivers_date_weekday_specification
  : forall (n : Bin0) .
      Weekday.to_b0 (Date.weekday_of_day_number n) = (n %. Weekday.days_in_week)%b0
  := Date.weekday.specification.

Definition data_calendar_all_delivers_date_number_boundedness
  : forall (d : Date) .
      (Date.days_before_year (Date.year d) <= Date.day_number d
       /\ Date.day_number d < Date.days_before_year (Date.year d + 1)%b)%b0
  := Date.number.boundedness.

Definition data_calendar_all_delivers_date_year_uniqueness
  : forall (y1 : Bin) (y2 : Bin) (n : Bin0) .
      (Date.days_before_year y1 <= n)%b0 -> (n < Date.days_before_year (y1 + 1)%b)%b0
      -> (Date.days_before_year y2 <= n)%b0 -> (n < Date.days_before_year (y2 + 1)%b)%b0
      -> y1 = y2
  := @Date.year.uniqueness.

Definition data_calendar_all_delivers_iso_week_date
  : IsoWeekDate
  := IsoWeekDate.introduction 2025 1 Weekday.Monday I.

Definition data_calendar_all_delivers_iso_week_date_january_decomposition
  : forall (y : Bin) .
      Date.day_number (IsoWeekDate.january_4th y) = (Date.days_before_year y + 3%b0_decimal)%b0
  := IsoWeekDate.january.decomposition.

Definition data_calendar_all_delivers_iso_week_date_january_succession
  : forall (y : Bin) .
      Date.day_number (IsoWeekDate.january_4th (y + 1)%b)
      = (Date.day_number (IsoWeekDate.january_4th y) + Date.days_in_year y)%b0
  := IsoWeekDate.january.succession.

Definition data_calendar_all_delivers_iso_week_date_january_weekday
  : forall (y : Bin) .
      (Date.day_number (IsoWeekDate.january_4th y) %. Weekday.days_in_week)%b0
      = Weekday.to_b0
          (Weekday.next (Weekday.next (Weekday.next
             (Date.weekday_of_day_number (Date.days_before_year y)))))
  := IsoWeekDate.january.weekday.

Definition data_calendar_all_delivers_iso_week_date_start_decomposition
  : forall (y : Bin) .
      IsoWeekDate.week_one_start y
      = (Date.day_number (IsoWeekDate.january_4th y) /. Weekday.days_in_week
         * Weekday.days_in_week)%b0
  := IsoWeekDate.start.decomposition.

Definition data_calendar_all_delivers_iso_week_date_start_weekday
  : forall (y : Bin) . Date.weekday_of_day_number (IsoWeekDate.week_one_start y) = Weekday.Monday
  := IsoWeekDate.start.weekday.

Definition data_calendar_all_delivers_iso_week_date_start_boundedness
  : forall (y : Bin) .
      (IsoWeekDate.week_one_start y <= Date.day_number (IsoWeekDate.january_4th y)
       /\ Date.day_number (IsoWeekDate.january_4th y)
          < IsoWeekDate.week_one_start y + Weekday.days_in_week)%b0
  := IsoWeekDate.start.boundedness.

Definition data_calendar_all_delivers_iso_week_date_year_length_dichotomy
  : forall (y : Bin) .
      IsoWeekDate.weeks_in_year y = 52%b0_decimal \/ IsoWeekDate.weeks_in_year y = 53%b0_decimal
  := IsoWeekDate.year.length.dichotomy.

Definition data_calendar_all_delivers_iso_week_date_year_length_specification
  : forall (y : Bin) .
      IsoWeekDate.weeks_in_year y = 53%b0_decimal
      <-> (Date.weekday_of_day_number (Date.days_before_year y) = Weekday.Thursday
           \/ (Date.is_leap y = true
               /\ Date.weekday_of_day_number (Date.days_before_year y) = Weekday.Wednesday))
  := IsoWeekDate.year.length.specification.

Definition data_calendar_all_delivers_iso_week_date_year_length_carry
  : forall (y : Bin) .
      (Date.day_number (IsoWeekDate.january_4th (y + 1)%b) /. Weekday.days_in_week
       = Date.day_number (IsoWeekDate.january_4th y) /. Weekday.days_in_week
         + IsoWeekDate.weeks_in_year y)%b0
  := IsoWeekDate.year.length.carry.

Definition data_calendar_all_delivers_iso_week_date_year_succession
  : forall (y : Bin) .
      IsoWeekDate.week_one_start (y + 1)%b
      = (IsoWeekDate.week_one_start y + IsoWeekDate.weeks_in_year y * Weekday.days_in_week)%b0
  := IsoWeekDate.year.succession.

Definition data_calendar_all_delivers_iso_week_date_extensionality
  : forall (x1 : IsoWeekDate) (x2 : IsoWeekDate) .
      IsoWeekDate.year x1 = IsoWeekDate.year x2
      -> IsoWeekDate.week x1 = IsoWeekDate.week x2
      -> IsoWeekDate.weekday x1 = IsoWeekDate.weekday x2
      -> x1 = x2
  := IsoWeekDate.extensionality.

Definition data_calendar_all_delivers_iso_week_date_week_boundedness
  : forall (k : Bin0) .
      let y :=
        Date.year
          (Date.from_day_number
             (k * Weekday.days_in_week + Weekday.to_b0 Weekday.Thursday)%b0) in
      (Date.day_number (IsoWeekDate.january_4th y) /. Weekday.days_in_week <= k
       /\ k < Date.day_number (IsoWeekDate.january_4th (y + 1)%b) /. Weekday.days_in_week)%b0
  := IsoWeekDate.week.boundedness.

Definition data_calendar_all_delivers_iso_week_date_week_location
  : forall (y : Bin) (k : Bin0) .
      (Date.day_number (IsoWeekDate.january_4th y) /. Weekday.days_in_week <= k
       -> k < Date.day_number (IsoWeekDate.january_4th (y + 1)%b) /. Weekday.days_in_week
       -> Date.days_before_year y <= k * Weekday.days_in_week + Weekday.to_b0 Weekday.Thursday
          /\ k * Weekday.days_in_week + Weekday.to_b0 Weekday.Thursday
             < Date.days_before_year (y + 1)%b)%b0
  := IsoWeekDate.week.location.

Definition data_calendar_all_delivers_iso_week_date_conversion_date_retraction
  : forall (d : Date) . IsoWeekDate.to_date (IsoWeekDate.from_date d) = d
  := IsoWeekDate.conversion.date.retraction.

Definition data_calendar_all_delivers_iso_week_date_conversion_date_section
  : forall (x : IsoWeekDate) . IsoWeekDate.from_date (IsoWeekDate.to_date x) = x
  := IsoWeekDate.conversion.date.section.

Definition data_calendar_all_delivers_iso_week_date_weekday_agreement_forward
  : forall (d : Date) . IsoWeekDate.weekday (IsoWeekDate.from_date d) = Date.weekday d
  := IsoWeekDate.weekday.agreement.forward.

Definition data_calendar_all_delivers_iso_week_date_weekday_agreement_backward
  : forall (x : IsoWeekDate) . Date.weekday (IsoWeekDate.to_date x) = IsoWeekDate.weekday x
  := IsoWeekDate.weekday.agreement.backward.

Definition data_calendar_all_computes_iso_week_date_week_one_start_2025
  : IsoWeekDate.week_one_start 2025
    = Date.day_number (Date.introduction 2024 Month.December 30 I)
  := Identity.reflexivity _.

Definition data_calendar_all_computes_iso_week_date_weeks_in_year_2015
  : IsoWeekDate.weeks_in_year 2015 = 53%b0_decimal
  := Identity.reflexivity _.

Definition data_calendar_all_computes_iso_week_date_weeks_in_year_2020
  : IsoWeekDate.weeks_in_year 2020 = 53%b0_decimal
  := Identity.reflexivity _.

Definition data_calendar_all_computes_iso_week_date_weeks_in_year_2024
  : IsoWeekDate.weeks_in_year 2024 = 52%b0_decimal
  := Identity.reflexivity _.

Definition data_calendar_all_computes_iso_week_date_weeks_in_year_2026
  : IsoWeekDate.weeks_in_year 2026 = 53%b0_decimal
  := Identity.reflexivity _.

Definition data_calendar_all_computes_iso_week_date_is_valid_refusal_2024_53
  : IsoWeekDate.is_valid 2024 53 = false
  := Identity.reflexivity _.

Definition data_calendar_all_computes_iso_week_date_from_date_2024_12_30
  : IsoWeekDate.from_date (Date.introduction 2024 Month.December 30 I)
    = IsoWeekDate.introduction 2025 1 Weekday.Monday I
  := IsoWeekDate.extensionality
       (IsoWeekDate.from_date (Date.introduction 2024 Month.December 30 I))
       (IsoWeekDate.introduction 2025 1 Weekday.Monday I)
       (Identity.reflexivity _) (Identity.reflexivity _) (Identity.reflexivity _).

Definition data_calendar_all_computes_iso_week_date_from_date_2021_01_03
  : IsoWeekDate.from_date (Date.introduction 2021 Month.January 3 I)
    = IsoWeekDate.introduction 2020 53 Weekday.Sunday I
  := IsoWeekDate.extensionality
       (IsoWeekDate.from_date (Date.introduction 2021 Month.January 3 I))
       (IsoWeekDate.introduction 2020 53 Weekday.Sunday I)
       (Identity.reflexivity _) (Identity.reflexivity _) (Identity.reflexivity _).

Definition data_calendar_all_computes_iso_week_date_from_date_2026_11_21
  : IsoWeekDate.from_date (Date.introduction 2026 Month.November 21 I)
    = IsoWeekDate.introduction 2026 47 Weekday.Saturday I
  := IsoWeekDate.extensionality
       (IsoWeekDate.from_date (Date.introduction 2026 Month.November 21 I))
       (IsoWeekDate.introduction 2026 47 Weekday.Saturday I)
       (Identity.reflexivity _) (Identity.reflexivity _) (Identity.reflexivity _).

Definition data_calendar_all_computes_iso_week_date_to_date_2020_53_7
  : Date.compare
      (IsoWeekDate.to_date (IsoWeekDate.introduction 2020 53 Weekday.Sunday I))
      (Date.introduction 2021 Month.January 3 I)
    = Comparison.Eq
  := Identity.reflexivity _.

Definition data_calendar_all_delivers_weekday_comparable
  : Comparable Weekday.compare Weekday.LessThan
  := _.

Definition data_calendar_all_delivers_weekday_order_strict_transitivity
  : forall (w1 : Weekday) (w2 : Weekday) (w3 : Weekday) .
      Weekday.LessThan w1 w2 -> Weekday.LessThan w2 w3 -> Weekday.LessThan w1 w3
  := @Weekday.order.strict.transitivity.

Definition data_calendar_all_delivers_weekday_comparison_specification
  : forall (w1 : Weekday) (w2 : Weekday) .
      (Weekday.compare w1 w2 = Comparison.Lt <-> Weekday.LessThan w1 w2)
      /\ (Weekday.compare w1 w2 = Comparison.Eq <-> w1 = w2)
  := Weekday.comparison.specification.

Definition data_calendar_all_delivers_weekday_comparison_antisymmetry
  : forall (w1 : Weekday) (w2 : Weekday) .
      Weekday.compare w1 w2 = Comparison.transpose (Weekday.compare w2 w1)
  := Weekday.comparison.antisymmetry.

Definition data_calendar_all_computes_weekday_compare_monday_sunday
  : Weekday.compare Weekday.Monday Weekday.Sunday = Comparison.Lt
  := Identity.reflexivity _.

Definition data_calendar_all_computes_weekday_compare_friday_friday
  : Weekday.compare Weekday.Friday Weekday.Friday = Comparison.Eq
  := Identity.reflexivity _.

Definition data_calendar_all_delivers_iso_week_date_comparable
  : Comparable IsoWeekDate.compare IsoWeekDate.LessThan
  := _.

Definition data_calendar_all_delivers_iso_week_date_conversion_date_injectivity
  : forall (x1 : IsoWeekDate) (x2 : IsoWeekDate) .
      IsoWeekDate.to_date x1 = IsoWeekDate.to_date x2 -> x1 = x2
  := @IsoWeekDate.conversion.date.injectivity.

Definition data_calendar_all_delivers_iso_week_date_order_strict_transitivity
  : forall (x1 : IsoWeekDate) (x2 : IsoWeekDate) (x3 : IsoWeekDate) .
      IsoWeekDate.LessThan x1 x2 -> IsoWeekDate.LessThan x2 x3 -> IsoWeekDate.LessThan x1 x3
  := @IsoWeekDate.order.strict.transitivity.

Definition data_calendar_all_delivers_iso_week_date_comparison_specification
  : forall (x1 : IsoWeekDate) (x2 : IsoWeekDate) .
      (IsoWeekDate.compare x1 x2 = Comparison.Lt <-> IsoWeekDate.LessThan x1 x2)
      /\ (IsoWeekDate.compare x1 x2 = Comparison.Eq <-> x1 = x2)
  := IsoWeekDate.comparison.specification.

Definition data_calendar_all_delivers_iso_week_date_comparison_antisymmetry
  : forall (x1 : IsoWeekDate) (x2 : IsoWeekDate) .
      IsoWeekDate.compare x1 x2 = Comparison.transpose (IsoWeekDate.compare x2 x1)
  := IsoWeekDate.comparison.antisymmetry.

Definition data_calendar_all_computes_iso_week_date_compare_across_a_year
  : IsoWeekDate.compare
      (IsoWeekDate.introduction 2020 53 Weekday.Sunday I)
      (IsoWeekDate.introduction 2021 1 Weekday.Monday I)
    = Comparison.Lt
  := Identity.reflexivity _.
