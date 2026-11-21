(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

open JW

(* The extracted numbers are unary, so OCaml integers go in and come out
   through these conversions. *)
let rec nat0 k = if k = 0 then Nat0.Zero else Nat0.inc (nat0 (k - 1))

let rec int_of_nat = function
  | Nat.One -> 1
  | Nat.Successor n -> 1 + int_of_nat n
;;

let int_of_nat0 = function
  | Nat0.Zero -> 0
  | Nat0.Positive p -> int_of_nat p
;;

(* The binary numbers carry their bits, lowest outermost. *)
let rec bin k =
  if k = 1
  then Bin.One
  else if k mod 2 = 0
  then Bin.Coq_b0 (bin (k / 2))
  else Bin.Coq_b1 (bin (k / 2))
;;

let rec int_of_bin = function
  | Bin.One -> 1
  | Bin.Coq_b0 b -> 2 * int_of_bin b
  | Bin.Coq_b1 b -> (2 * int_of_bin b) + 1
;;

let int_of_bin0 = function
  | Bin0.Zero -> 0
  | Bin0.Positive p -> int_of_bin p
;;

let signed_bin k =
  if k = 0
  then SignedBin.Zero
  else if k > 0
  then SignedBin.Positive (bin k)
  else SignedBin.Negative (bin (-k))
;;

let int_of_signed_bin = function
  | SignedBin.Zero -> 0
  | SignedBin.Positive p -> int_of_bin p
  | SignedBin.Negative p -> -int_of_bin p
;;

(* A flag and an [Int8] result, as OCaml integers. *)
let int8_flagged (flag, x) = flag = Bit.One, int_of_signed_bin (Int8.to_b_signed x)
let int8 k = Int8.from_b_signed (signed_bin k)

(* A carry or borrow and a [UInt8] result, as OCaml integers. *)
let uint8_flagged (flag, x) = flag = Bit.One, int_of_bin0 (UInt8.to_b0 x)
let uint8 k = UInt8.from_b_signed (signed_bin k)

(* [2^n - 1] and [2^n] as [Bin] values, for numbers past OCaml's [int]. *)
let rec ones n = if n = 1 then Bin.One else Bin.Coq_b1 (ones (n - 1))
let rec power2 n = if n = 0 then Bin.One else Bin.Coq_b0 (power2 (n - 1))
let date y m d = Date.make (bin y) m (bin d)

let day_number y m d =
  match date y m d with
  | Some x -> int_of_bin0 (Date.day_number x)
  | None -> -1
;;

let bin0 k = if k = 0 then Bin0.Zero else Bin0.Positive (bin k)

(* A date as its year, month and day, the proof having been erased. *)
let calendar x = int_of_bin (Date.year x), Date.month x, int_of_bin (Date.day x)
let from_day_number n = calendar (Date.from_day_number (bin0 n))

let from_day_of_year y d =
  match Date.from_day_of_year (bin y) (bin d) with
  | Some x -> Some (calendar x)
  | None -> None
;;

(* The date [y]-[m]-[d] moved by [f], as its year, month and day. *)
let moved f y m d =
  match date y m d with
  | Some x -> Some (calendar (f x))
  | None -> None
;;

let days_between (y1, m1, d1) (y2, m2, d2) =
  match date y1 m1 d1, date y2 m2 d2 with
  | Some x1, Some x2 -> Some (int_of_signed_bin (Date.days_between x1 x2))
  | _ -> None
;;

let unix_day y m d =
  match date y m d with
  | Some x -> Some (int_of_signed_bin (Date.unix_day x))
  | None -> None
;;

let from_unix_day u =
  match Date.from_unix_day (signed_bin u) with
  | Some x -> Some (calendar x)
  | None -> None
;;

(* The ISO week date of [y]-[m]-[d] as its ISO year, week and weekday. *)
let iso_week_date y m d =
  match date y m d with
  | Some x ->
    let w = IsoWeekDate.from_date x in
    Some
      ( int_of_bin (IsoWeekDate.year w)
      , int_of_bin (IsoWeekDate.week w)
      , IsoWeekDate.weekday w )
  | None -> None
;;

(* The date [y]-[m]-[d] taken to its ISO week date and back. *)
let iso_week_date_round_trip y m d =
  match date y m d with
  | Some x -> Some (calendar (IsoWeekDate.to_date (IsoWeekDate.from_date x)))
  | None -> None
;;

(* [JW] has a [List] module of its own, which [open JW] puts in front of
   OCaml's. *)
let ints l = Stdlib.List.map int_of_nat0 l
let check name ok = if not ok then failwith ("extraction test failed: " ^ name)

let () =
  let cmp = Nat0.compare in
  let s =
    SortedSet.insert
      cmp
      (nat0 2)
      (SortedSet.insert
         cmp
         (nat0 3)
         (SortedSet.insert cmp (nat0 1) (SortedSet.empty cmp)))
  in
  check "SortedSet.to_list" (ints (SortedSet.to_list cmp s) = [ 1; 2; 3 ]);
  check "SortedSet.contains" (SortedSet.contains cmp (nat0 2) s);
  check "SortedSet.contains, absent" (not (SortedSet.contains cmp (nat0 4) s));
  let t = SortedSet.remove cmp (nat0 2) s in
  check "SortedSet.remove" (ints (SortedSet.to_list cmp t) = [ 1; 3 ]);
  check "SortedSet.size" (int_of_nat0 (SortedSet.size cmp t) = 2);
  let sum = UInt8.add (UInt8.from_nat0 (nat0 200)) (UInt8.from_nat0 (nat0 100)) in
  check "UInt8.add" (int_of_nat0 (UInt8.to_nat0 sum) = 44);
  check
    "Kleene3.and"
    (Kleene3.coq_and Kleene3.Coq_unknown Kleene3.Coq_false = Kleene3.Coq_false);
  check
    "Kleene3.or"
    (Kleene3.coq_or Kleene3.Coq_unknown Kleene3.Coq_true = Kleene3.Coq_true);
  check "bool" (Bool.coq_and true false = false && Bool.coq_or false true = true);
  check
    "option"
    (int_of_nat0 (Option.unwrap_or (nat0 0) (Some (nat0 5))) = 5
     && int_of_nat0 (Option.unwrap_or (nat0 7) None) = 7);
  check "product" (int_of_nat0 (Product.first (nat0 1, nat0 2)) = 1);
  check "product, second" (int_of_nat0 (Product.second (nat0 1, nat0 2)) = 2);
  check "list" (ints (List.concat [ nat0 1 ] [ nat0 2; nat0 3 ]) = [ 1; 2; 3 ]);
  check
    "Date.is_leap"
    ((not (Date.is_leap (bin 1900)))
     && Date.is_leap (bin 2000)
     && (not (Date.is_leap (bin 2023)))
     && Date.is_leap (bin 2024));
  check "Date.day_number 0001-01-01" (day_number 1 Month.January 1 = 0);
  check "Date.day_number 1970-01-01" (day_number 1970 Month.January 1 = 719162);
  check "Date.day_number 2000-01-01" (day_number 2000 Month.January 1 = 730119);
  check "Date.day_number 2024-02-29" (day_number 2024 Month.February 29 = 738944);
  check "Date.day_number 9999-12-31" (day_number 9999 Month.December 31 = 3652058);
  check "Date.from_day_number 0" (from_day_number 0 = (1, Month.January, 1));
  check "Date.from_day_number 36523" (from_day_number 36523 = (100, Month.December, 31));
  check "Date.from_day_number 146096" (from_day_number 146096 = (400, Month.December, 31));
  check "Date.from_day_number 738944" (from_day_number 738944 = (2024, Month.February, 29));
  check "Date.from_day_number 739940" (from_day_number 739940 = (2026, Month.November, 21));
  check
    "Date.from_day_number 3652058"
    (from_day_number 3652058 = (9999, Month.December, 31));
  check
    "Date.from_day_of_year"
    (from_day_of_year 2024 60 = Some (2024, Month.February, 29)
     && from_day_of_year 2024 366 = Some (2024, Month.December, 31)
     && from_day_of_year 2023 366 = None);
  check
    "Date.weekday_of_day_number"
    (Date.weekday_of_day_number (bin0 0) = Weekday.Monday
     && Date.weekday_of_day_number (bin0 719162) = Weekday.Thursday
     && Date.weekday_of_day_number (bin0 146096) = Weekday.Sunday
     && Date.weekday_of_day_number (bin0 739940) = Weekday.Saturday);
  check
    "Date.days_before_year 2001"
    (int_of_bin0 (Date.days_before_year (bin 2001)) = 730485);
  check
    "Date.make, refusal"
    (date 2023 Month.February 29 = None
     && date 1900 Month.February 29 = None
     && date 2024 Month.April 31 = None);
  check
    "Date.add_days 2024-02-28 1"
    (moved (fun x -> Date.add_days x (bin0 1)) 2024 Month.February 28
     = Some (2024, Month.February, 29));
  check
    "Date.days_between 2000-01-01 2024-02-29"
    (days_between (2000, Month.January, 1) (2024, Month.February, 29) = Some 8825);
  check
    "Date.add_months 2024-01-31 1"
    (moved (fun x -> Date.add_months x (bin0 1)) 2024 Month.January 31
     = Some (2024, Month.February, 29));
  check
    "Date.add_years 2024-02-29 1"
    (moved (fun x -> Date.add_years x (bin0 1)) 2024 Month.February 29
     = Some (2025, Month.February, 28));
  check
    "Date.unix_day"
    (unix_day 1970 Month.January 1 = Some 0
     && unix_day 2000 Month.January 1 = Some 10957
     && unix_day 1 Month.January 1 = Some (-719162));
  check
    "Date.from_unix_day"
    (from_unix_day 0 = Some (1970, Month.January, 1) && from_unix_day (-719163) = None);
  check
    "IsoWeekDate.from_date"
    (iso_week_date 2024 Month.December 30 = Some (2025, 1, Weekday.Monday)
     && iso_week_date 2021 Month.January 3 = Some (2020, 53, Weekday.Sunday)
     && iso_week_date 2026 Month.November 21 = Some (2026, 47, Weekday.Saturday));
  check
    "IsoWeekDate.to_date"
    (iso_week_date_round_trip 2024 Month.December 30 = Some (2024, Month.December, 30)
     && iso_week_date_round_trip 2021 Month.January 3 = Some (2021, Month.January, 3));
  check
    "IsoWeekDate.weeks_in_year"
    (int_of_bin0 (IsoWeekDate.weeks_in_year (bin 2015)) = 53
     && int_of_bin0 (IsoWeekDate.weeks_in_year (bin 2020)) = 53
     && int_of_bin0 (IsoWeekDate.weeks_in_year (bin 2024)) = 52
     && int_of_bin0 (IsoWeekDate.weeks_in_year (bin 2026)) = 53);
  check
    "Int8.add_with_overflow 100 27"
    (int8_flagged (Int8.add_with_overflow (int8 100) (int8 27)) = (false, 127));
  check
    "Int8.add_with_overflow 127 1"
    (int8_flagged (Int8.add_with_overflow (int8 127) (int8 1)) = (true, -128));
  check
    "Int8.add_with_overflow (-128) (-1)"
    (int8_flagged (Int8.add_with_overflow (int8 (-128)) (int8 (-1))) = (true, 127));
  check
    "Int8.sub_with_overflow (-128) 1"
    (int8_flagged (Int8.sub_with_overflow (int8 (-128)) (int8 1)) = (true, 127));
  check
    "Int8.sub_with_overflow 0 (-128)"
    (int8_flagged (Int8.sub_with_overflow (int8 0) (int8 (-128))) = (true, -128));
  check
    "Int8.negate (-128)"
    (int_of_signed_bin (Int8.to_b_signed (Int8.negate (int8 (-128)))) = -128);
  check
    "UInt8.add_with_carry 0 200 100"
    (uint8_flagged (UInt8.add_with_carry Bit.Zero (uint8 200) (uint8 100)) = (true, 44));
  check
    "UInt8.sub_with_borrow 0 3 5"
    (uint8_flagged (UInt8.sub_with_borrow Bit.Zero (uint8 3) (uint8 5)) = (true, 254));
  check
    "UInt8.add_with_carry 0 100 27"
    (uint8_flagged (UInt8.add_with_carry Bit.Zero (uint8 100) (uint8 27)) = (false, 127));
  check
    "UInt8.mul_with_overflow 16 16"
    (uint8_flagged (UInt8.mul_with_overflow (uint8 16) (uint8 16)) = (true, 0));
  check
    "UInt8.mul_with_overflow 15 17"
    (uint8_flagged (UInt8.mul_with_overflow (uint8 15) (uint8 17)) = (false, 255));
  check
    "Int8.mul_with_overflow 16 8"
    (int8_flagged (Int8.mul_with_overflow (int8 16) (int8 8)) = (true, -128));
  check
    "Int8.mul_with_overflow (-16) 8"
    (int8_flagged (Int8.mul_with_overflow (int8 (-16)) (int8 8)) = (false, -128));
  (let flag, sum =
     Int64.add_with_overflow
       (Int64.from_b_signed (SignedBin.Positive (ones 63)))
       (Int64.from_b_signed (SignedBin.Positive Bin.One))
   in
   check
     "Int64.add_with_overflow 9223372036854775807 1"
     (flag = Bit.One && Int64.to_b_signed sum = SignedBin.Negative (power2 63)));
  let flag, sum =
    Int64.add_with_overflow
      (Int64.from_b_signed (SignedBin.Positive (Bin.Coq_b0 (ones 62))))
      (Int64.from_b_signed (SignedBin.Positive Bin.One))
  in
  check
    "Int64.add_with_overflow 9223372036854775806 1"
    (flag = Bit.Zero && Int64.to_b_signed sum = SignedBin.Positive (ones 63))
;;
