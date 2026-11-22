<!--
SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
SPDX-License-Identifier: MIT
-->

# Numbers

`JW.Data` holds seven number types:

| Type | Values | Scope key |
|:---|:---|:---|
| `Nat` | from 1 | `%n` |
| `Nat0` | from 0 | `%n0` |
| `Integer` | every integer | `%z` |
| `Rational` | every fraction | `%q` |
| `Bin` | from 1, in binary | `%b` |
| `Bin0` | from 0, in binary | `%b0` |
| `SignedBin` | every integer, in binary | `%b_signed` |

---

## Conversions

**Upward, without being written.** A `Nat` stands wherever a `Nat0`, an `Integer` or a `Rational` is expected, and so on up; a `Bin` stands wherever a `Bin0` or a `SignedBin` is. So `(numerator x * denominator y)%z` multiplies an `Integer` by a `Nat`. **Every such conversion is still printed** in the goal, as `Integer.Positive (denominator y)`, so a `leibniz` step can be aimed at what the goal shows.

**Downward, by name, into an `Option`**, since there may be no answer: `Nat0.to_nat`, `Integer.to_nat0`, `Integer.to_nat`, `Rational.to_integer`, `Rational.to_nat0` and `Rational.to_nat`. Each is `None` exactly where the value has no counterpart below, such as `Integer.to_nat0` below zero or `Rational.to_integer` at a denominator other than one. Its laws sit in a `narrowing` module:

- `retraction`: going up, then down, gives the value back (`Rational.narrowing.integer.retraction`);
- `specification`: `to_integer x = Some n` holds exactly when `x` is `n`;
- `failure`: when the answer is `None`.

Take the value out with `Option.unwrap_or d o`, which falls back to `d`, or with `Option.unwrap o h`, where `h` proves `~ (o = None)`: nothing fails at run time, so the proof takes the place of the failure.

---

## Arithmetic and literals

Arithmetic is written with each type's notation and scope key, `(a + b)%n`, `(p /. q)%n0`, `(x * y)%q`, `(m && n)%b0`, and goals print the operations by name, `Rational.mul x y`.

**`Nat`, `Nat0` and `Integer` are written in decimal or hexadecimal**: `3%n`, `0x1F%n0`, `(-5)%z`. A closed value prints back in decimal, and `0%n` is refused, `Nat` having no zero.

- Where one of the three types is expected, the key can go: `Nat0.add 3 4`.
- Under `Data.Number.All` a numeral with no key is an `Integer`, `3` and `-3` alike, and a bare `a + b` is `Integer.add`.

**Subtraction is written `x - y` on the types where it is total**, `Integer`, `Rational` and `SignedBin`: `(3 - 5)%z` is `-2`.

- A chain with a `-` is written grouped, `((1 - 2) - 3)%z`, never `(1 - 2 - 3)%z`, though both parse alike.
- `Nat`, `Nat0`, `Bin` and `Bin0` keep `sub` by name, since it answers an `Option` that is `None` where the result would not be in the type, beside `saturating_sub` where the type has it.
- The laws are the same in the three types: `subtraction.specification` (`x - y = x + negate y`), `subtraction.inversion.addition` (`(x + y) - y = x`), `addition.inversion.subtraction` (`(x - y) + y = x`), `subtraction.right.identity` (`x - 0 = x`) and `subtraction.annihilation` (`x - x = 0`).
- These types spend one constructor per unit, so a `Nat0` or `Integer` literal of 5000 or more stays a call to its parsing function until something computes it, and a `Nat` literal that large, which is built in full, draws a warning.

---

## Binary numbers

**They compute.** A `Bin` is `One` with bits appended at the low end, `b0` for a 0 and `b1` for a 1; `Bin0` adds zero, and `SignedBin` adds a sign. Their arithmetic works bit by bit, so `(10 ^ 11001000)%b0`, two to the power two hundred, reduces in the kernel at once, where a `Nat` that large could not even be written out.

**They are written in binary digits**: `1011%b`, `1011%b0` and `1011%b_signed` are eleven, and `(-1011)%b_signed` is minus eleven. A closed value prints the same way. Any other digit is refused, and so is a `Bin` literal opening with 0. The short key `%b_signed` goes to `SignedBin` because only its literals can carry a sign.

**`Bin` and `Bin0` also read decimal digits**, under a key of their own: `2024%b_decimal` is the same term as `11111101000%b`, and `738944%b0_decimal` the same as `10110100011010000000%b0`. A `Bin` literal opening with 0 is refused here too. A closed value still prints in binary, unless the decimal scope is open.

**Division takes a `Bin` divisor, which is never zero:**

- `(1011 /. 11%b)%b0` is three, and `(1011 %. 11%b)%b0` is two;
- `SignedBin` divides the magnitude and keeps the sign, so `((-1011) /. 11%b)%b_signed` is minus three, and it has no remainder, as `Integer` has none.

**`Bin0` also has:**

- `Bin0.gcd`, by Euclid's algorithm; a quotient or a gcd of two 64-bit numbers reduces in the kernel at once;
- the bitwise `&&`, `||` and `^^`, with `shift_left`, `shift_right` and `test_bit`; `shift_right` is division by a power of two (`Bin0.shift.right.quotient`).

**Their laws are proved through the unary types.** `Bin.to_nat`, `Bin0.to_nat0` and `SignedBin.to_integer` convert each to its counterpart, and the laws go through them (`Bin0.conversion.addition`, `SignedBin.conversion.difference`). The algebraic laws and instances are those of `Nat`, `Nat0` and `Integer`: `SignedBin` is a ring, and its addition an abelian group.

**`SignedBin`'s order meets its arithmetic.** The laws of `<` and `<=` against the operations:

- **addition:** `SignedBin.addition.order.strict.monotonicity` (`y < z -> x + y < x + z`), its `cancellation`, `SignedBin.addition.order.monotonicity` for `<=`, `SignedBin.addition.order.mixed.monotonicity` (`a <= c -> b < d -> a + b < c + d`) and `SignedBin.addition.order.accumulation` (both `<=`);
- **negation and subtraction:** `SignedBin.order.negation.strict.reversal` (`x < y <-> - y < - x`), `SignedBin.order.negation.reversal` for `<=`, and `SignedBin.order.subtraction.{left.monotonicity, right.antitonicity, positivity}`;
- **the successor:** `SignedBin.order.increment.{extensivity, specification, adjacency}`, `SignedBin.order.decrement.extensivity` and `SignedBin.order.discreteness` (`x < y + 1 <-> x <= y`);
- **signs:** `SignedBin.order.sign.negativity` (`Negative p < 0`) and `SignedBin.order.sign.positivity` (`0 < Positive p`), and `SignedBin.order.embedding.{preservation, nonnegativity}` for a `Bin0` read as a `SignedBin`;
- **multiplication:** `SignedBin.multiplication.left.order.strict.{monotonicity, reversal}` (by a positive factor, by a negative one), `SignedBin.multiplication.left.order.monotonicity`, `SignedBin.multiplication.left.negation` and the signs of a product, `SignedBin.multiplication.sign.*`; `Bin0.multiplication.left.order.strict.monotonicity` is the same law for `Bin0`;
- **comparison, minimum and maximum:** `SignedBin.comparison.{translation, negation}`, `SignedBin.minimum.left.distributivity.addition`, `SignedBin.maximum.left.distributivity.addition` and `SignedBin.minimum.duality`.

**`Bin0`'s order meets its arithmetic** in the same way, with no sign to track:

- **the least number:** `Bin0.order.minimum` (`0 <= n`);
- **addition:** `Bin0.addition.right.order.extensivity` (`n <= m + n`), `Bin0.addition.order.monotonicity` (`m <= n -> k + m <= k + n`), its `cancellation`, `Bin0.addition.order.strict.monotonicity` (`a <= c -> b < d -> a + b < c + d`) and `Bin0.addition.order.accumulation` (both `<=`);
- **the successor:** `Bin0.order.succession` (`m < n -> m + 1 <= n`) and `Bin0.order.discreteness` (`n < 1 -> n = 0`);
- **multiplication:** `Bin0.multiplication.left.order.strict.monotonicity` (by a positive factor) and `Bin0.multiplication.left.order.monotonicity`, which needs no premise on the factor;
- **division:** `Bin0.division.characterization` (`m * d <= n <-> m <= n /. d`);
- **positional numbers:** for a count `q` of units `k` and a rest `r < k`, `Bin0.order.positional.boundedness` (`q < b -> k * q + r < k * b`) and `Bin0.order.positional.monotonicity` (`q1 < q2 -> k * q1 + r1 < k * q2 + r2`, whatever `r2`).
