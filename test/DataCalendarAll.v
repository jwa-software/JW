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
  : Date.days_in_common_year = 365%bin_with_zero_decimal
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_days_in_quadrennium
  : Date.days_in_quadrennium = 1461%bin_with_zero_decimal
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_days_in_century
  : Date.days_in_century = 36524%bin_with_zero_decimal
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_days_in_quadricentennium
  : Date.days_in_quadricentennium = 146097%bin_with_zero_decimal
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_day_number_0001_01_01
  : Date.day_number (Date.introduction 1 Month.January 1 I) = 0%bin_with_zero_decimal
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_day_number_0004_12_31
  : Date.day_number (Date.introduction 4 Month.December 31 I) = 1460%bin_with_zero_decimal
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_day_number_0100_12_31
  : Date.day_number (Date.introduction 100 Month.December 31 I) = 36523%bin_with_zero_decimal
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_day_number_0400_12_31
  : Date.day_number (Date.introduction 400 Month.December 31 I) = 146096%bin_with_zero_decimal
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_day_number_1970_01_01
  : Date.day_number (Date.introduction 1970 Month.January 1 I) = 719162%bin_with_zero_decimal
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_day_number_2000_01_01
  : Date.day_number (Date.introduction 2000 Month.January 1 I) = 730119%bin_with_zero_decimal
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_day_number_2024_02_29
  : Date.day_number (Date.introduction 2024 Month.February 29 I) = 738944%bin_with_zero_decimal
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_day_number_9999_12_31
  : Date.day_number (Date.introduction 9999 Month.December 31 I) = 3652058%bin_with_zero_decimal
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_days_before_year_2001
  : Date.days_before_year 2001 = 730485%bin_with_zero_decimal
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_days_before_year_10000
  : Date.days_before_year 10000 = 3652059%bin_with_zero_decimal
  := Identity.reflexivity _.

Definition data_calendar_all_computes_date_day_of_year_2024_12_31
  : Date.day_of_year (Date.introduction 2024 Month.December 31 I) = 366%bin_with_zero_decimal
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
