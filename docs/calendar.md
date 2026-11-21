<!--
SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
SPDX-License-Identifier: MIT
-->

# Calendar

`Data/Calendar/` holds the months of the year and the proleptic Gregorian calendar:

| Type | What it is |
|:---|:---|
| `Month` | The twelve months, `Month.January` to `Month.December` |
| `Date` | A date of the proleptic Gregorian calendar: a year, a month and a day of that month |

- **Proleptic.** The Gregorian leap rule holds for every year, also for the years before 1582, when the calendar came into use.
- **The years count from 1.** There is no year 0 and no negative year, so every number is a binary number without a sign: `BinBase` for the year and the day, which are never 0, and `Bin0` for a count of days.
- **Day 0 is 0001-01-01.** `Date.day_number` counts the days from it.

`From JW Require Import Data.Calendar.All` brings both types. The laws are written with the type's prefix: `Date.year.succession`.

---

## Month

- **The number of a month.** `Month.to_number` gives the month's place in the year, `Month.January` being 1, and `Month.from_number` goes back, `None` past 12. `Month.conversion.retraction` states `Month.from_number (Month.to_number m) = Some m`, and `Month.conversion.specification` states that `Month.from_number n = Some m` exactly when `Month.to_number m = n`.
- **The next and the previous month.** `Month.next` and `Month.prev` go round the year, `Month.January` after `Month.December`. Each undoes the other: `Month.succession.forward.inverse` and `Month.succession.backward.inverse`.
- **The order of the year.** `Month.compare` compares the months' numbers, and `Month.comparable` makes it an instance of `Comparable`.

---

## Date

- **Only a real date can be built.** The constructor `Date.introduction y m d` takes, as its last argument, a proof of `Assert (Date.is_valid y m d)`: the month `m` of the year `y` has a day `d`. For a written date the proof is `I`, and a date that does not exist is a type error, since its `Assert` is `Falsum`:

  ```
  Date.introduction 2024 Month.February 29 I    (* a date *)
  Date.introduction 2023 Month.February 29 I    (* refused: 2023 is not a leap year *)
  ```

  `Date.make y m d` checks at run time and answers `None` for a date that does not exist. Two dates with the same year, month and day are equal, the proofs being equal by `Assert.uniqueness`.
- **Write the numbers in decimal.** Under `jw_bin_base_decimal_scope`, `2024` is a `BinBase` and stands for a `Bin0` wherever one is expected. The binary scopes read `2024` as binary digits and refuse it.

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
- **The day of the year.** `Date.ordinal.positivity` and `Date.ordinal.boundedness` place `Date.day_of_year x` between 1 and the length of the year.

### The order of dates

- **By year, then by month, then by day.** `Date.compare` compares the dates that way, and `Date.LessThan x1 x2` states that `x1` comes first. `Date.comparable` makes it an instance of `Comparable`.
- **The order is the order of the day numbers.** `Date.number.comparison` states `Date.compare x1 x2 = Bin0.compare (Date.day_number x1) (Date.day_number x2)`, and `Date.number.order` states that `x1` comes first exactly when its day number is the smaller.
- **A day number names one date.** `Date.number.injectivity` states that two dates with the same day number are the same date.
