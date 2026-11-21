(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

From JW Require Import Data.Calendar.All.

Local Open Scope jw_bin_base_decimal_scope.

Definition data_calendar_all_delivers_month
  : Month
  := Month.January.

Definition data_calendar_all_delivers_month_conversion_retraction
  : forall (m : Month) . Month.from_number (Month.to_number m) = Some m
  := Month.conversion.retraction.

Definition data_calendar_all_delivers_month_conversion_specification
  : forall (n : BinBase) (m : Month) . Month.from_number n = Some m <-> Month.to_number m = n
  := Month.conversion.specification.

Definition data_calendar_all_delivers_month_succession_forward_inverse
  : forall (m : Month) . Month.prev (Month.next m) = m
  := Month.succession.forward.inverse.

Definition data_calendar_all_delivers_month_succession_backward_inverse
  : forall (m : Month) . Month.next (Month.prev m) = m
  := Month.succession.backward.inverse.

Definition data_calendar_all_delivers_month_comparable
  : Comparable Month.compare Month.LessThan
  := _.

Definition data_calendar_all_computes_month_to_number
  : Month.to_number Month.December = 12
  := Identity.reflexivity _.

Definition data_calendar_all_computes_month_from_number
  : Month.from_number 9 = Some Month.September
  := Identity.reflexivity _.

Definition data_calendar_all_computes_month_from_number_refusal
  : Month.from_number 13 = None
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
  : Date.days_in_common_year = 365%b0_decimal
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_days_in_quadrennium
  : Date.days_in_quadrennium = 1461%b0_decimal
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_days_in_century
  : Date.days_in_century = 36524%b0_decimal
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_days_in_quadricentennium
  : Date.days_in_quadricentennium = 146097%b0_decimal
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
  : Date.day_of_year (Date.introduction 2024 Month.December 31 I) = 366%b0_decimal
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
  : forall (y : BinBase) . Date.is_leap (y + 400%bin_base_decimal)%bin_base = Date.is_leap y
  := Date.leap.periodicity.

Definition data_calendar_all_delivers_date_month_length_boundedness
  : forall (y : BinBase) (m : Month) .
      (28%bin_base_decimal <= Date.days_in_month y m
       /\ Date.days_in_month y m <= 31%bin_base_decimal)%bin_base
  := Date.month.length.boundedness.

Definition data_calendar_all_delivers_date_month_succession
  : forall (y : BinBase) (m : Month) .
      ~ (m = Month.December)
      -> Date.days_before_month y (Month.next m)
         = (Date.days_before_month y m + Date.days_in_month y m)%b0
  := Date.month.succession.

Definition data_calendar_all_delivers_date_month_completion
  : forall (y : BinBase) .
      (Date.days_before_month y Month.December + 31%bin_base_decimal)%b0
      = Date.days_in_year y
  := Date.month.completion.

Definition data_calendar_all_delivers_date_month_boundedness
  : forall (y : BinBase) (m : Month) .
      (Date.days_before_month y m + Date.days_in_month y m <= Date.days_in_year y)%b0
  := Date.month.boundedness.

Definition data_calendar_all_delivers_date_year_length_dichotomy
  : forall (y : BinBase) . Date.days_in_year y = 365 \/ Date.days_in_year y = 366
  := Date.year.length.dichotomy.

Definition data_calendar_all_delivers_date_year_length_specification
  : forall (y : BinBase) . Date.days_in_year y = 366 <-> Date.is_leap y = true
  := Date.year.length.specification.

Definition data_calendar_all_delivers_date_ordinal_positivity
  : forall (x : Date) . (0 < Date.day_of_year x)%b0
  := Date.ordinal.positivity.

Definition data_calendar_all_delivers_date_ordinal_boundedness
  : forall (x : Date) . (Date.day_of_year x <= Date.days_in_year (Date.year x))%b0
  := Date.ordinal.boundedness.

Definition data_calendar_all_delivers_date_year_antecedence_translation
  : forall (y : BinBase) (k : BinBase) .
      Date.years_before (y + k)%bin_base = (Date.years_before y + k)%b0
  := Date.year.antecedence.translation.

Definition data_calendar_all_delivers_date_year_periodicity
  : forall (y : BinBase) .
      Date.days_before_year (y + 400%bin_base_decimal)%bin_base
      = (Date.days_before_year y + Date.days_in_quadricentennium)%b0
  := Date.year.periodicity.

Definition data_calendar_all_delivers_date_year_antecedence_restoration
  : forall (y : BinBase) . (Date.years_before y + 1%bin_base_decimal)%b0 = y
  := Date.year.antecedence.restoration.

Definition data_calendar_all_delivers_date_year_succession
  : forall (y : BinBase) .
      Date.days_before_year (y + 1)%bin_base
      = (Date.days_before_year y + Date.days_in_year y)%b0
  := Date.year.succession.

Definition data_calendar_all_delivers_date_year_monotonicity
  : forall (y : BinBase) (k : BinBase) .
      (Date.days_before_year y + Date.days_in_year y
       <= Date.days_before_year (y + k)%bin_base)%b0
  := Date.year.monotonicity.

Definition data_calendar_all_delivers_date_month_monotonicity
  : forall (y : BinBase) (m1 : Month) (m2 : Month) .
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
      (Date.day_number x + 1%bin_base_decimal)%b0
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
