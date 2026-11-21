(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

From JW Require Import Data.Calendar.All.

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
  : forall (m : Month) . Month.previous (Month.next m) = m
  := Month.succession.forward.inverse.

Definition data_calendar_all_delivers_month_succession_backward_inverse
  : forall (m : Month) . Month.next (Month.previous m) = m
  := Month.succession.backward.inverse.

Definition data_calendar_all_delivers_month_comparable
  : Comparable Month.compare Month.LessThan
  := _.

Definition data_calendar_all_computes_month_to_number
  : Month.to_number Month.December = 1100%bin_base
  := Identity.reflexivity _.

Definition data_calendar_all_computes_month_from_number
  : Month.from_number 1001%bin_base = Some Month.September
  := Identity.reflexivity _.

Definition data_calendar_all_computes_month_from_number_refusal
  : Month.from_number 1101%bin_base = None
  := Identity.reflexivity _.

Definition data_calendar_all_computes_month_next
  : Month.next Month.December = Month.January
  := Identity.reflexivity _.

Definition data_calendar_all_computes_month_previous
  : Month.previous Month.January = Month.December
  := Identity.reflexivity _.

Definition data_calendar_all_computes_month_compare
  : Month.compare Month.March Month.October = Comparison.Lt
  := Identity.reflexivity _.
