<!--
SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
SPDX-License-Identifier: MIT
-->

# Calendar

`Data/Calendar/` holds the months of the year, the days of the week and the proleptic Gregorian calendar:

| Type | What it is |
|:---|:---|
| `Month` | The twelve months, `Month.January` to `Month.December` |
| `Weekday` | The seven days of the week, `Weekday.Monday` to `Weekday.Sunday` |
| `Date` | A date of the proleptic Gregorian calendar: a year, a month and a day of that month |

- **Proleptic.** The Gregorian leap rule holds for every year, also for the years before 1582, when the calendar came into use.
- **The years count from 1.** There is no year 0 and no negative year, so every number is a binary number without a sign: `Bin` for the year and the day, which are never 0, and `Bin0` for a count of days. `Date.v` names them `Year`, `Day` and `Days`.
- **Day 0 is 0001-01-01.** `Date.day_number` counts the days from it.

`From JW Require Import Data.Calendar.All` brings the three types. The laws are written with the type's prefix: `Date.year.succession`.

---

## Month

- **The number of a month.** `Month.to_b` gives the month's place in the year, `Month.January` being 1, and `Month.from_b` goes back, `None` past 12. `Month.conversion.bin.retraction` states `Month.from_b (Month.to_b m) = Some m`, and `Month.conversion.bin.specification` states that `Month.from_b n = Some m` exactly when `Month.to_b m = n`.
- **The number counted from 0.** `Month.to_b0` gives the same place counted from 0, `Month.January` being 0, and `Month.from_b0` goes back, `None` past 11. The laws are the same, under `Month.conversion.bin0`.
- **The next and the previous month.** `Month.next` and `Month.prev` go round the year, `Month.January` after `Month.December`. Each undoes the other: `Month.succession.forward.inverse` and `Month.succession.backward.inverse`.
- **The order of the year.** `Month.compare` compares the months' numbers, and `Month.comparable` makes it an instance of `Comparable`.

---

## Weekday

- **The number of a weekday.** `Weekday.to_b` gives the weekday's place in the week as ISO 8601 numbers it, `Weekday.Monday` being 1 and `Weekday.Sunday` 7, and `Weekday.from_b` goes back, `None` past 7. `Weekday.to_b0` and `Weekday.from_b0` count from 0, `Weekday.Monday` being 0, `None` past 6. The laws are `Weekday.conversion.bin.retraction`, `.specification` and `.injectivity`, and the same under `Weekday.conversion.bin0`.
- **The length of a week.** `Weekday.days_in_week` is 7.
- **The next and the previous weekday.** `Weekday.next` and `Weekday.prev` go round the week, `Weekday.Monday` after `Weekday.Sunday`. Each undoes the other: `Weekday.succession.forward.inverse` and `Weekday.succession.backward.inverse`.

---

## Date

- **Only a real date can be built.** The constructor `Date.introduction y m d` takes, as its last argument, a proof of `Assert (Date.is_valid y m d)`: the month `m` of the year `y` has a day `d`. For a written date the proof is `I`, and a date that does not exist is a type error, since its `Assert` is `Falsum`:

  ```
  Date.introduction 2024 Month.February 29 I    (* a date *)
  Date.introduction 2023 Month.February 29 I    (* refused: 2023 is not a leap year *)
  ```

  `Date.make y m d` checks at run time and answers `None` for a date that does not exist. Two dates with the same year, month and day are equal, the proofs being equal by `Assert.uniqueness`.
- **Write the numbers in decimal.** Under `jw_bin_decimal_scope`, `2024` is a `Bin` and stands for a `Bin0` wherever one is expected. The binary scopes read `2024` as binary digits and refuse it.

### The leap rule

- **The rule.** A year divisible by 4 is a leap year, except a year divisible by 100 that is not divisible by 400. So 2024 and 2000 are leap years, and 1900 and 2100 are not. `Date.is_leap` computes it.
- **The rule repeats every 400 years.** `Date.leap.periodicity` states `Date.is_leap (y + 400) = Date.is_leap y`. Four and 100 are not periods: 1896 is a leap year and 1900 is not; 2000 is a leap year and 2100 is not.
- **The lengths.** `Date.days_in_month` gives 28 to 31 days (`Date.month.length.boundedness`), and `Date.days_in_year` gives 365 or 366 (`Date.year.length.dichotomy`), 366 exactly for a leap year (`Date.year.length.specification`).

### From a date to a day number

- **The periods of the rule.** Each period that the rule repeats over has a fixed length, and its leap year is its last year:

  | Constant | Period | Days |
  |:---|:---|:---|
  | `Date.days_in_common_year` | one year | 365 |
  | `Date.days_in_quadrennium` | four years: three common years and a leap year | 1461 |
  | `Date.days_in_century` | 100 years: 25 quadrennia, the century year not leap | 36524 |
  | `Date.days_in_quadricentennium` | 400 years: four centuries, the 400th year leap | 146097 |

- **The days before a year.** `Date.days_before_year y` takes the years before `y` apart into whole quadricentennia, centuries, quadrennia and single years, and adds their lengths. For 2024: 5 quadricentennia, no century, 5 quadrennia and 3 years give 738885 days.
- **The days before a month.** `Date.days_before_month y m` adds the lengths of the months before `m`, each month's count being the one before it plus the length of the month before it.
- **The day number.** `Date.day_number x` is the days before the year, plus the days before the month, plus the day less one. `Date.day_of_year x` is the day's place in its year, 1 for January 1.

| Date | `Date.day_number` |
|:---|:---|
| 0001-01-01 | 0 |
| 1970-01-01 | 719162 |
| 2000-01-01 | 730119 |
| 2024-02-29 | 738944 |
| 9999-12-31 | 3652058 |

### Laws

- **One year more.** `Date.year.succession` states `Date.days_before_year (y + 1) = Date.days_before_year y + Date.days_in_year y`. The carry of one more year stops at the single years, the quadrennia, the centuries or the quadricentennia, which adds 365, 366, 365 or 366 days: the four cases of the leap rule.
- **400 years more.** `Date.year.periodicity` states `Date.days_before_year (y + 400) = Date.days_before_year y + Date.days_in_quadricentennium`.
- **One month more.** `Date.month.succession` states that, for a month `m` before December, the days before the next month are the days before `m` plus the length of `m`. `Date.month.completion` closes the year: the days before December plus 31 are the year's length.
- **The day of the year.** `Date.day_of_year x` is a `Bin`, so it is never 0; `Date.ordinal.decomposition` states it is the days before the month plus the day, and `Date.ordinal.boundedness` keeps it within the length of the year.

### From a day number to a date

- **The day number taken apart.** `Date.div_year n` divides the day number `n` by the periods of the rule, from the quadricentennium down, and gives the whole years before the day and the days of its year before it. A fourth century, or a fourth year of a quadrennium, may be one day longer than the others; its last day would give a quotient of 4, so `Date.div_clamped_at_3` holds the quotient at 3 and leaves that day in the fourth period.
- **The month and the day.** `Date.calendar_date_after_days y days` gives the month and the day of the month of the date `days` days after January 1 of `y`, searching the months from December down. `Date.month_after_days` and `Date.day_of_month_after_days` are its two components.
- **The date.** `Date.from_day_number n` is the date of day number `n`, for every `n`. `Date.from_day_of_year y d` is day `d` of year `y`, `None` when the year has fewer days:

| Day number | `Date.from_day_number` | Weekday |
|:---|:---|:---|
| 0 | 0001-01-01 | Monday |
| 36523 | 0100-12-31 | Friday |
| 146096 | 0400-12-31 | Sunday |
| 719162 | 1970-01-01 | Thursday |
| 738944 | 2024-02-29 | Thursday |
| 3652058 | 9999-12-31 | Friday |

- **Every date it builds is valid.** The constructor of `Date` takes a proof, so `Date.from_day_number` stands on two laws: `Date.division.boundedness`, the days of the year before the date are fewer than the year has, and `Date.calendar.validity`, the month and the day found pass `Date.is_valid`. `Date.calendar.ordinal.validity` does the same for `Date.from_day_of_year`.

### Round trips

- **From a day number and back.** `Date.number.retraction` states `Date.day_number (Date.from_day_number n) = n`. It rests on `Date.division.reconstruction` and `Date.calendar.reconstruction`: each step of the division gives its number back.
- **From a date and back.** `Date.number.section` states `Date.from_day_number (Date.day_number x) = x`, and `Date.ordinal.section` states `Date.from_day_of_year (Date.year x) (Date.day_of_year x) = Some x`. `Date.calendar.inversion` finds the month and the day of a valid date back from the days before it.

### The weekday

- **The weekday of a date.** `Date.weekday x` is `Date.weekday_of_day_number (Date.day_number x)`, which reads the remainder of the day number by 7 through `Weekday.from_b0`: 0001-01-01 was a Monday. `Date.weekday.totality` states that the remainder always names a weekday.
- **One day more.** `Date.weekday.succession` states `Date.weekday_of_day_number (n + 1) = Weekday.next (Date.weekday_of_day_number n)`.
- **A week more, and 400 years more.** `Date.weekday.periodicity` states that `n` and `n + Weekday.days_in_week` have the same weekday, and `Date.weekday.quadricentennium.periodicity` the same for `n + Date.days_in_quadricentennium`: a quadricentennium is 20871 whole weeks, so the weekdays repeat every 400 years.

### The order of dates

- **By year, then by month, then by day.** `Date.compare` compares the dates that way, and `Date.LessThan x1 x2` states that `x1` comes first. `Date.comparable` makes it an instance of `Comparable`.
- **The order is the order of the day numbers.** `Date.number.comparison` states `Date.compare x1 x2 = Bin0.compare (Date.day_number x1) (Date.day_number x2)`, and `Date.number.order` states that `x1` comes first exactly when its day number is the smaller.
- **A day number names one date.** `Date.number.injectivity` states that two dates with the same day number are the same date.
