(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

(* Guards [JW.Data.Number.Binary.All] by importing that umbrella and nothing
 * else, so anything it fails to re-export is a build failure here. What
 * [Data.Number.All] forwards from it is guarded separately in
 * [DataNumberAll.v].
 *)
From JW Require Import Data.Number.Binary.All.

Definition data_number_binary_all_delivers_types
  : BinBase -> BinWithZero -> Bin -> Verum
  := fun (_ : BinBase) (_ : BinWithZero) (_ : Bin) . I.

Definition data_number_binary_all_delivers_bin_base_notation
  : forall (a : BinBase) (b : BinBase) . (a + b)%bin_base = (b + a)%bin_base
  := BinBase.addition.commutativity.

Definition data_number_binary_all_delivers_bin_with_zero_notation
  : forall (m : BinWithZero) (n : BinWithZero) .
      (m && n)%bin_with_zero = (n && m)%bin_with_zero
  := BinWithZero.conjunction.commutativity.

Definition data_number_binary_all_delivers_bin_notation
  : forall (x : Bin) (y : Bin) (z : Bin) .
      ((x + y) + z = x + (y + z))%b
  := Bin.addition.associativity.

Definition data_number_binary_all_delivers_bin_subtraction_notation
  : (11 - 1011)%b = (-1000)%b /\ ((1011 - 11) - 1)%b = 111%b
  := conjoin (Identity.reflexivity _), (Identity.reflexivity _).

Definition data_number_binary_all_delivers_bin_subtraction_specification
  : forall (x : Bin) (y : Bin) . (x - y)%b = (x + Bin.negate y)%b
  := Bin.subtraction.specification.

Definition data_number_binary_all_delivers_bin_subtraction_inversion_addition
  : forall (x : Bin) (y : Bin) . ((x + y) - y)%b = x
  := Bin.subtraction.inversion.addition.

Definition data_number_binary_all_delivers_bin_addition_inversion_subtraction
  : forall (x : Bin) (y : Bin) . ((x - y) + y)%b = x
  := Bin.addition.inversion.subtraction.

Definition data_number_binary_all_delivers_bin_subtraction_right_identity
  : forall (x : Bin) . (x - Bin.Zero)%b = x
  := Bin.subtraction.right.identity.

Definition data_number_binary_all_delivers_bin_subtraction_annihilation
  : forall (x : Bin) . (x - x)%b = Bin.Zero
  := Bin.subtraction.annihilation.

Definition data_number_binary_all_delivers_bin_involution
  : forall (x : Bin) .
      Bin.negate (Bin.negate x) = x
  := Bin.negation.involution.

Definition data_number_binary_all_delivers_bin_distributivity
  : forall (x : Bin) (y : Bin) (z : Bin) .
      (x * (y + z) = (x * y) + (x * z) /\ (y + z) * x = (y * x) + (z * x))%b
  := Bin.multiplication.distributivity.over.addition.

Definition data_number_binary_all_delivers_bin_with_zero_division_specification
  : forall (n : BinWithZero) (d : BinBase) .
      ((n /. d) * d + (n %. d) = n /\ (n %. d) < d)%bin_with_zero
  := BinWithZero.division.specification.

Definition data_number_binary_all_delivers_bin_with_zero_gcd_commutativity
  : forall (a : BinWithZero) (b : BinWithZero) . BinWithZero.gcd a b = BinWithZero.gcd b a
  := BinWithZero.gcd.commutativity.

Definition data_number_binary_all_delivers_bin_with_zero_shift_quotient
  : forall (n : BinWithZero) (k : BinBase) .
      BinWithZero.shift_right n (BinBase.to_nat k) = (n /. (10 ^ k)%bin_base)%bin_with_zero
  := BinWithZero.shift.right.quotient.

Definition data_number_binary_all_delivers_bin_division_magnitude
  : forall (x : Bin) (d : BinBase) .
      Bin.abs (x /. d)%b = (Bin.abs x /. d)%bin_with_zero
  := Bin.division.magnitude.

Definition data_number_binary_all_delivers_bin_base_literal
  : (1011 + 1)%bin_base = 1100%bin_base
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_bin_with_zero_literal
  : (1011 + 1)%bin_with_zero = 1100%bin_with_zero
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_bin_base_decimal_literal
  : 2024%bin_base_decimal = 11111101000%bin_base
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_bin_base_decimal_digits
  : BinBase.to_decimal 11111101000%bin_base
    = Numeral.Decimal.Digits.Two
        (Numeral.Decimal.Digits.Zero
          (Numeral.Decimal.Digits.Two
            (Numeral.Decimal.Digits.Four Numeral.Decimal.Digits.End)))
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_bin_with_zero_decimal_literal
  : 738944%bin_with_zero_decimal = 10110100011010000000%bin_with_zero
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_bin_with_zero_decimal_zero
  : 0%bin_with_zero_decimal = 0%bin_with_zero
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_bin_literal
  : (1011 + 1)%b = 1100%b
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_bin_literal_negative
  : ((-1011) + 1011)%b = 0%b
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_bin_multiplication_computes
  : ((-11) * 101)%b = (-1111)%b
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_bin_with_zero_division_computes
  : (1011 /. 11%bin_base)%bin_with_zero = 11%bin_with_zero
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_bin_with_zero_modulo_computes
  : (1011 %. 11%bin_base)%bin_with_zero = 10%bin_with_zero
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_bin_with_zero_gcd_computes
  : BinWithZero.gcd 1100%bin_with_zero 10010%bin_with_zero = 110%bin_with_zero
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_bin_division_computes
  : ((-1011) /. 11%bin_base)%b = (-11)%b
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_large_division_computes
  : (1111111111111111111111111111111111111111111111111111111111111111
      /. 100000000000000000000000000000001%bin_base)%bin_with_zero
    = 11111111111111111111111111111111%bin_with_zero
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_large_gcd_computes
  : BinWithZero.gcd
      1111111111111111111111111111111111111111111111111111111111111111%bin_with_zero
      100000000000000000000000000000001%bin_with_zero
    = 100000000000000000000000000000001%bin_with_zero
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_bin_base_comparison
  : BinBase.compare (BinBase.b1 BinBase.One) (BinBase.b0 BinBase.One) = Comparison.Gt
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_bin_comparison
  : Bin.compare (-1011)%b 1011%b = Comparison.Lt
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_bin_base_maximum_computes
  : BinBase.max (BinBase.b1 BinBase.One) (BinBase.b0 BinBase.One) = BinBase.b1 BinBase.One
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_bin_maximum_computes
  : Bin.max (-1011)%b 1011%b = 1011%b
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_bin_minimum_computes
  : Bin.min (-1011)%b 1011%b = (-1011)%b
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_modulo_identity
  : forall (n : BinWithZero) (d : BinBase) .
      (n < BinWithZero.Positive d -> n %. d = n)%bin_with_zero
  := BinWithZero.modulo.identity.

Definition data_number_binary_all_delivers_modulo_sum_absorption
  : forall (a : BinWithZero) (b : BinWithZero) (d : BinBase) .
      (((a %. d) + b) %. d = (a + b) %. d)%bin_with_zero
  := BinWithZero.modulo.sum.left.absorption.

Definition data_number_binary_all_delivers_modulo_sum_invariance
  : forall (a : BinWithZero) (b : BinWithZero) (d : BinBase) .
      (b %. d = 0 -> (a + b) %. d = a %. d)%bin_with_zero
  := BinWithZero.modulo.sum.right.invariance.

Definition data_number_binary_all_delivers_division_translation
  : forall (n : BinWithZero) (d : BinBase) .
      ((n + BinWithZero.Positive d) /. d = (n /. d) + 1)%bin_with_zero
  := BinWithZero.division.translation.

Definition data_number_binary_all_delivers_division_succession_interior
  : forall (n : BinWithZero) (d : BinBase) .
      ((n %. d) + 1 < BinWithZero.Positive d
       -> ((n + 1) /. d = n /. d) /\ ((n + 1) %. d = (n %. d) + 1))%bin_with_zero
  := BinWithZero.division.succession.interior.

Definition data_number_binary_all_delivers_division_succession_carry
  : forall (n : BinWithZero) (d : BinBase) .
      ((n %. d) + 1 = BinWithZero.Positive d
       -> ((n + 1) /. d = (n /. d) + 1) /\ ((n + 1) %. d = 0))%bin_with_zero
  := BinWithZero.division.succession.carry.

Definition data_number_binary_all_delivers_modulo_nesting
  : forall (n : BinWithZero) (d : BinBase) (k : BinBase) .
      ((n %. (d * k)%bin_base) %. d = n %. d)%bin_with_zero
  := BinWithZero.modulo.nesting.

Definition data_number_binary_all_delivers_order_succession
  : forall (m : BinWithZero) (n : BinWithZero) . (m < n -> m + 1 <= n)%bin_with_zero
  := BinWithZero.order.succession.

Definition data_number_binary_all_delivers_modulo_product_absorption
  : forall (a : BinWithZero) (b : BinWithZero) (d : BinBase) .
      (((a %. d) * b) %. d = (a * b) %. d)%bin_with_zero
  := BinWithZero.modulo.product.left.absorption.

Definition data_number_binary_all_delivers_shift_left_multiplication
  : forall (n : BinWithZero) (k : Nat0) .
      BinWithZero.shift_left n k = (n * BinWithZero.shift_left 1 k)%bin_with_zero
  := BinWithZero.shift.left.multiplication.

Definition data_number_binary_all_delivers_decimal_reading_computes
  : BinWithZero.from_decimal 0%bin_with_zero
      (Numeral.Decimal.Digits.Two
        (Numeral.Decimal.Digits.Five
          (Numeral.Decimal.Digits.Five Numeral.Decimal.Digits.End)))
    = 11111111%bin_with_zero
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_decimal_printing_computes
  : BinWithZero.to_decimal 11111111%bin_with_zero
    = Numeral.Decimal.Digits.Two
        (Numeral.Decimal.Digits.Five
          (Numeral.Decimal.Digits.Five Numeral.Decimal.Digits.End))
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_difference_additivity
  : forall (a : BinWithZero) (b : BinWithZero) (c : BinWithZero) (d : BinWithZero) .
      (Bin.bin_with_zero_difference a b + Bin.bin_with_zero_difference c d
        = Bin.bin_with_zero_difference (a + c)%bin_with_zero (b + d)%bin_with_zero)%b
  := Bin.difference.additivity.

Definition data_number_binary_all_delivers_difference_invariance
  : forall (a : BinWithZero) (b : BinWithZero) (c : BinWithZero) (d : BinWithZero) .
      (a + d = c + b)%bin_with_zero ->
      Bin.bin_with_zero_difference a b = Bin.bin_with_zero_difference c d
  := @Bin.difference.invariance.

(* The types the operations above take and return, named rather than merely
 * produced: a client who cannot write them cannot state anything about them.
 *)
Definition data_number_binary_all_delivers_bool
  : Bool
  := BinBase.eq BinBase.One BinBase.One.

Definition data_number_binary_all_delivers_option
  : Option BinBase
  := BinBase.sub (BinBase.b0 BinBase.One) BinBase.One.

Definition data_number_binary_all_delivers_product
  : Product BinWithZero BinWithZero
  := BinWithZero.div 1011%bin_with_zero 11%bin_base.

Definition data_number_binary_all_delivers_nat
  : Nat
  := BinBase.to_nat BinBase.One.

Definition data_number_binary_all_delivers_nat0
  : Nat0
  := BinWithZero.to_nat0 1011%bin_with_zero.

Definition data_number_binary_all_delivers_integer
  : Integer
  := Bin.to_integer (-1011)%b.

Definition data_number_binary_all_delivers_numeral
  : Numeral.Signed
  := Bin.to_numeral (-1011)%b.

Definition data_number_binary_all_delivers_well_founded
  : forall (x : Bin) . Accessible (Induced (<)%bin_with_zero Bin.abs) x
  := fun (x : Bin) . WellFounded.accessibility x.

Definition data_number_binary_all_delivers_bin_addition_order_strict_monotonicity
  : forall (x : Bin) (y : Bin) (z : Bin) . (y < z -> x + y < x + z)%b
  := Bin.addition.order.strict.monotonicity.

Definition data_number_binary_all_delivers_bin_addition_order_strict_cancellation
  : forall (x : Bin) (y : Bin) (z : Bin) . (x + y < x + z -> y < z)%b
  := Bin.addition.order.strict.cancellation.

Definition data_number_binary_all_delivers_bin_addition_order_monotonicity
  : forall (x : Bin) (y : Bin) (z : Bin) . (y <= z -> x + y <= x + z)%b
  := Bin.addition.order.monotonicity.

Definition data_number_binary_all_delivers_bin_addition_order_mixed_monotonicity
  : forall (a : Bin) (b : Bin) (c : Bin) (d : Bin) . (a <= c -> b < d -> a + b < c + d)%b
  := Bin.addition.order.mixed.monotonicity.

Definition data_number_binary_all_delivers_bin_addition_order_accumulation
  : forall (a : Bin) (b : Bin) (c : Bin) (d : Bin) . (a <= c -> b <= d -> a + b <= c + d)%b
  := Bin.addition.order.accumulation.

Definition data_number_binary_all_delivers_bin_order_sign_negativity
  : forall (p : BinBase) . (Bin.Negative p < 0)%b
  := Bin.order.sign.negativity.

Definition data_number_binary_all_delivers_bin_order_sign_positivity
  : forall (p : BinBase) . (0 < Bin.Positive p)%b
  := Bin.order.sign.positivity.

Definition data_number_binary_all_delivers_bin_order_negation_strict_reversal
  : forall (x : Bin) (y : Bin) . (x < y <-> - y < - x)%b
  := Bin.order.negation.strict.reversal.

Definition data_number_binary_all_delivers_bin_order_negation_reversal
  : forall (x : Bin) (y : Bin) . (x <= y -> - y <= - x)%b
  := Bin.order.negation.reversal.

Definition data_number_binary_all_delivers_bin_order_subtraction_left_monotonicity
  : forall (x : Bin) (y : Bin) (z : Bin) . (y < z -> y - x < z - x)%b
  := Bin.order.subtraction.left.monotonicity.

Definition data_number_binary_all_delivers_bin_order_subtraction_right_antitonicity
  : forall (x : Bin) (y : Bin) (z : Bin) . (y < z -> x - z < x - y)%b
  := Bin.order.subtraction.right.antitonicity.

Definition data_number_binary_all_delivers_bin_order_subtraction_positivity
  : forall (x : Bin) (y : Bin) . (x < y <-> 0 < y - x)%b
  := Bin.order.subtraction.positivity.

Definition data_number_binary_all_delivers_bin_order_increment_extensivity
  : forall (x : Bin) . (x < x + 1)%b
  := Bin.order.increment.extensivity.

Definition data_number_binary_all_delivers_bin_order_increment_specification
  : forall (x : Bin) (y : Bin) . (x < y <-> x + 1 <= y)%b
  := Bin.order.increment.specification.

Definition data_number_binary_all_delivers_bin_order_increment_adjacency
  : forall (x : Bin) (y : Bin) . (~ (x < y /\ y < x + 1))%b
  := Bin.order.increment.adjacency.

Definition data_number_binary_all_delivers_bin_order_decrement_extensivity
  : forall (x : Bin) . (x - 1 < x)%b
  := Bin.order.decrement.extensivity.

Definition data_number_binary_all_delivers_bin_order_discreteness
  : forall (x : Bin) (y : Bin) . (x < y + 1 <-> x <= y)%b
  := Bin.order.discreteness.

Definition data_number_binary_all_delivers_bin_order_embedding_preservation
  : forall (m : BinWithZero) (n : BinWithZero) .
      (m < n)%bin_with_zero <-> (Bin.from_bin_with_zero m < Bin.from_bin_with_zero n)%b
  := Bin.order.embedding.preservation.

Definition data_number_binary_all_delivers_bin_order_embedding_nonnegativity
  : forall (n : BinWithZero) . (0 <= Bin.from_bin_with_zero n)%b
  := Bin.order.embedding.nonnegativity.

Definition data_number_binary_all_delivers_bin_multiplication_left_negation
  : forall (x : Bin) (y : Bin) . (- x * y = - (x * y))%b
  := Bin.multiplication.left.negation.

Definition data_number_binary_all_delivers_bin_multiplication_left_order_strict_monotonicity
  : forall (k : Bin) (x : Bin) (y : Bin) . (0 < k -> x < y -> k * x < k * y)%b
  := Bin.multiplication.left.order.strict.monotonicity.

Definition data_number_binary_all_delivers_bin_multiplication_left_order_strict_reversal
  : forall (k : Bin) (x : Bin) (y : Bin) . (k < 0 -> x < y -> k * y < k * x)%b
  := Bin.multiplication.left.order.strict.reversal.

Definition data_number_binary_all_delivers_bin_multiplication_left_order_monotonicity
  : forall (k : Bin) (x : Bin) (y : Bin) . (0 <= k -> x <= y -> k * x <= k * y)%b
  := Bin.multiplication.left.order.monotonicity.

Definition data_number_binary_all_delivers_bin_multiplication_sign_positivity
  : forall (x : Bin) (y : Bin) . (0 < x -> 0 < y -> 0 < x * y)%b
  := Bin.multiplication.sign.positivity.

Definition data_number_binary_all_delivers_bin_multiplication_sign_negation_positivity
  : forall (x : Bin) (y : Bin) . (x < 0 -> y < 0 -> 0 < x * y)%b
  := Bin.multiplication.sign.negation.positivity.

Definition data_number_binary_all_delivers_bin_multiplication_sign_left_negativity
  : forall (x : Bin) (y : Bin) . (x < 0 -> 0 < y -> x * y < 0)%b
  := Bin.multiplication.sign.left.negativity.

Definition data_number_binary_all_delivers_bin_multiplication_sign_right_negativity
  : forall (x : Bin) (y : Bin) . (0 < x -> y < 0 -> x * y < 0)%b
  := Bin.multiplication.sign.right.negativity.

Definition data_number_binary_all_delivers_bin_comparison_translation
  : forall (z : Bin) (x : Bin) (y : Bin) . Bin.compare (z + x)%b (z + y)%b = Bin.compare x y
  := Bin.comparison.translation.

Definition data_number_binary_all_delivers_bin_comparison_negation
  : forall (x : Bin) (y : Bin) . Bin.compare (- x)%b (- y)%b = Bin.compare y x
  := Bin.comparison.negation.

Definition data_number_binary_all_delivers_bin_minimum_left_distributivity_addition
  : forall (z : Bin) (x : Bin) (y : Bin) .
      (z + Bin.min x y)%b = Bin.min (z + x)%b (z + y)%b
  := Bin.minimum.left.distributivity.addition.

Definition data_number_binary_all_delivers_bin_maximum_left_distributivity_addition
  : forall (z : Bin) (x : Bin) (y : Bin) .
      (z + Bin.max x y)%b = Bin.max (z + x)%b (z + y)%b
  := Bin.maximum.left.distributivity.addition.

Definition data_number_binary_all_delivers_bin_minimum_duality
  : forall (x : Bin) (y : Bin) . (- Bin.min x y)%b = Bin.max (- x)%b (- y)%b
  := Bin.minimum.duality.
