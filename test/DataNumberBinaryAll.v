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
  : BinBase -> Bin0 -> SignedBin -> Verum
  := fun (_ : BinBase) (_ : Bin0) (_ : SignedBin) . I.

Definition data_number_binary_all_delivers_bin_base_notation
  : forall (a : BinBase) (b : BinBase) . (a + b)%bin_base = (b + a)%bin_base
  := BinBase.addition.commutativity.

Definition data_number_binary_all_delivers_bin0_notation
  : forall (m : Bin0) (n : Bin0) .
      (m && n)%b0 = (n && m)%b0
  := Bin0.conjunction.commutativity.

Definition data_number_binary_all_delivers_signed_bin_notation
  : forall (x : SignedBin) (y : SignedBin) (z : SignedBin) .
      ((x + y) + z = x + (y + z))%b_signed
  := SignedBin.addition.associativity.

Definition data_number_binary_all_delivers_signed_bin_subtraction_notation
  : (11 - 1011)%b_signed = (-1000)%b_signed /\ ((1011 - 11) - 1)%b_signed = 111%b_signed
  := conjoin (Identity.reflexivity _), (Identity.reflexivity _).

Definition data_number_binary_all_delivers_signed_bin_subtraction_specification
  : forall (x : SignedBin) (y : SignedBin) . (x - y)%b_signed = (x + SignedBin.negate y)%b_signed
  := SignedBin.subtraction.specification.

Definition data_number_binary_all_delivers_signed_bin_subtraction_inversion_addition
  : forall (x : SignedBin) (y : SignedBin) . ((x + y) - y)%b_signed = x
  := SignedBin.subtraction.inversion.addition.

Definition data_number_binary_all_delivers_signed_bin_addition_inversion_subtraction
  : forall (x : SignedBin) (y : SignedBin) . ((x - y) + y)%b_signed = x
  := SignedBin.addition.inversion.subtraction.

Definition data_number_binary_all_delivers_signed_bin_subtraction_right_identity
  : forall (x : SignedBin) . (x - SignedBin.Zero)%b_signed = x
  := SignedBin.subtraction.right.identity.

Definition data_number_binary_all_delivers_signed_bin_subtraction_annihilation
  : forall (x : SignedBin) . (x - x)%b_signed = SignedBin.Zero
  := SignedBin.subtraction.annihilation.

Definition data_number_binary_all_delivers_signed_bin_involution
  : forall (x : SignedBin) .
      SignedBin.negate (SignedBin.negate x) = x
  := SignedBin.negation.involution.

Definition data_number_binary_all_delivers_signed_bin_distributivity
  : forall (x : SignedBin) (y : SignedBin) (z : SignedBin) .
      (x * (y + z) = (x * y) + (x * z) /\ (y + z) * x = (y * x) + (z * x))%b_signed
  := SignedBin.multiplication.distributivity.over.addition.

Definition data_number_binary_all_delivers_bin0_division_specification
  : forall (n : Bin0) (d : BinBase) .
      ((n /. d) * d + (n %. d) = n /\ (n %. d) < d)%b0
  := Bin0.division.specification.

Definition data_number_binary_all_delivers_bin0_gcd_commutativity
  : forall (a : Bin0) (b : Bin0) . Bin0.gcd a b = Bin0.gcd b a
  := Bin0.gcd.commutativity.

Definition data_number_binary_all_delivers_bin0_shift_quotient
  : forall (n : Bin0) (k : BinBase) .
      Bin0.shift_right n (BinBase.to_nat k) = (n /. (10 ^ k)%bin_base)%b0
  := Bin0.shift.right.quotient.

Definition data_number_binary_all_delivers_signed_bin_division_magnitude
  : forall (x : SignedBin) (d : BinBase) .
      SignedBin.abs (x /. d)%b_signed = (SignedBin.abs x /. d)%b0
  := SignedBin.division.magnitude.

Definition data_number_binary_all_delivers_bin_base_literal
  : (1011 + 1)%bin_base = 1100%bin_base
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_bin0_literal
  : (1011 + 1)%b0 = 1100%b0
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

Definition data_number_binary_all_delivers_bin0_decimal_literal
  : 738944%b0_decimal = 10110100011010000000%b0
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_bin0_decimal_zero
  : 0%b0_decimal = 0%b0
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_signed_bin_literal
  : (1011 + 1)%b_signed = 1100%b_signed
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_signed_bin_literal_negative
  : ((-1011) + 1011)%b_signed = 0%b_signed
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_signed_bin_multiplication_computes
  : ((-11) * 101)%b_signed = (-1111)%b_signed
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_bin0_division_computes
  : (1011 /. 11%bin_base)%b0 = 11%b0
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_bin0_modulo_computes
  : (1011 %. 11%bin_base)%b0 = 10%b0
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_bin0_gcd_computes
  : Bin0.gcd 1100%b0 10010%b0 = 110%b0
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_signed_bin_division_computes
  : ((-1011) /. 11%bin_base)%b_signed = (-11)%b_signed
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_large_division_computes
  : (1111111111111111111111111111111111111111111111111111111111111111
      /. 100000000000000000000000000000001%bin_base)%b0
    = 11111111111111111111111111111111%b0
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_large_gcd_computes
  : Bin0.gcd
      1111111111111111111111111111111111111111111111111111111111111111%b0
      100000000000000000000000000000001%b0
    = 100000000000000000000000000000001%b0
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_bin_base_comparison
  : BinBase.compare (BinBase.b1 BinBase.One) (BinBase.b0 BinBase.One) = Comparison.Gt
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_signed_bin_comparison
  : SignedBin.compare (-1011)%b_signed 1011%b_signed = Comparison.Lt
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_bin_base_maximum_computes
  : BinBase.max (BinBase.b1 BinBase.One) (BinBase.b0 BinBase.One) = BinBase.b1 BinBase.One
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_signed_bin_maximum_computes
  : SignedBin.max (-1011)%b_signed 1011%b_signed = 1011%b_signed
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_signed_bin_minimum_computes
  : SignedBin.min (-1011)%b_signed 1011%b_signed = (-1011)%b_signed
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_modulo_identity
  : forall (n : Bin0) (d : BinBase) .
      (n < Bin0.Positive d -> n %. d = n)%b0
  := Bin0.modulo.identity.

Definition data_number_binary_all_delivers_modulo_sum_absorption
  : forall (a : Bin0) (b : Bin0) (d : BinBase) .
      (((a %. d) + b) %. d = (a + b) %. d)%b0
  := Bin0.modulo.sum.left.absorption.

Definition data_number_binary_all_delivers_modulo_sum_invariance
  : forall (a : Bin0) (b : Bin0) (d : BinBase) .
      (b %. d = 0 -> (a + b) %. d = a %. d)%b0
  := Bin0.modulo.sum.right.invariance.

Definition data_number_binary_all_delivers_division_translation
  : forall (n : Bin0) (d : BinBase) .
      ((n + Bin0.Positive d) /. d = (n /. d) + 1)%b0
  := Bin0.division.translation.

Definition data_number_binary_all_delivers_division_succession_interior
  : forall (n : Bin0) (d : BinBase) .
      ((n %. d) + 1 < Bin0.Positive d
       -> ((n + 1) /. d = n /. d) /\ ((n + 1) %. d = (n %. d) + 1))%b0
  := Bin0.division.succession.interior.

Definition data_number_binary_all_delivers_division_succession_carry
  : forall (n : Bin0) (d : BinBase) .
      ((n %. d) + 1 = Bin0.Positive d
       -> ((n + 1) /. d = (n /. d) + 1) /\ ((n + 1) %. d = 0))%b0
  := Bin0.division.succession.carry.

Definition data_number_binary_all_delivers_modulo_nesting
  : forall (n : Bin0) (d : BinBase) (k : BinBase) .
      ((n %. (d * k)%bin_base) %. d = n %. d)%b0
  := Bin0.modulo.nesting.

Definition data_number_binary_all_delivers_order_succession
  : forall (m : Bin0) (n : Bin0) . (m < n -> m + 1 <= n)%b0
  := Bin0.order.succession.

Definition data_number_binary_all_delivers_modulo_product_absorption
  : forall (a : Bin0) (b : Bin0) (d : BinBase) .
      (((a %. d) * b) %. d = (a * b) %. d)%b0
  := Bin0.modulo.product.left.absorption.

Definition data_number_binary_all_delivers_shift_left_multiplication
  : forall (n : Bin0) (k : Nat0) .
      Bin0.shift_left n k = (n * Bin0.shift_left 1 k)%b0
  := Bin0.shift.left.multiplication.

Definition data_number_binary_all_delivers_decimal_reading_computes
  : Bin0.from_decimal 0%b0
      (Numeral.Decimal.Digits.Two
        (Numeral.Decimal.Digits.Five
          (Numeral.Decimal.Digits.Five Numeral.Decimal.Digits.End)))
    = 11111111%b0
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_decimal_printing_computes
  : Bin0.to_decimal 11111111%b0
    = Numeral.Decimal.Digits.Two
        (Numeral.Decimal.Digits.Five
          (Numeral.Decimal.Digits.Five Numeral.Decimal.Digits.End))
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_difference_additivity
  : forall (a : Bin0) (b : Bin0) (c : Bin0) (d : Bin0) .
      (SignedBin.b0_difference a b + SignedBin.b0_difference c d
        = SignedBin.b0_difference (a + c)%b0 (b + d)%b0)%b_signed
  := SignedBin.difference.additivity.

Definition data_number_binary_all_delivers_difference_invariance
  : forall (a : Bin0) (b : Bin0) (c : Bin0) (d : Bin0) .
      (a + d = c + b)%b0 ->
      SignedBin.b0_difference a b = SignedBin.b0_difference c d
  := @SignedBin.difference.invariance.

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
  : Product Bin0 Bin0
  := Bin0.div 1011%b0 11%bin_base.

Definition data_number_binary_all_delivers_nat
  : Nat
  := BinBase.to_nat BinBase.One.

Definition data_number_binary_all_delivers_nat0
  : Nat0
  := Bin0.to_nat0 1011%b0.

Definition data_number_binary_all_delivers_integer
  : Integer
  := SignedBin.to_integer (-1011)%b_signed.

Definition data_number_binary_all_delivers_numeral
  : Numeral.Signed
  := SignedBin.to_numeral (-1011)%b_signed.

Definition data_number_binary_all_delivers_well_founded
  : forall (x : SignedBin) . Accessible (Induced (<)%b0 SignedBin.abs) x
  := fun (x : SignedBin) . WellFounded.accessibility x.

Definition data_number_binary_all_delivers_signed_bin_addition_order_strict_monotonicity
  : forall (x : SignedBin) (y : SignedBin) (z : SignedBin) . (y < z -> x + y < x + z)%b_signed
  := SignedBin.addition.order.strict.monotonicity.

Definition data_number_binary_all_delivers_signed_bin_addition_order_strict_cancellation
  : forall (x : SignedBin) (y : SignedBin) (z : SignedBin) . (x + y < x + z -> y < z)%b_signed
  := SignedBin.addition.order.strict.cancellation.

Definition data_number_binary_all_delivers_signed_bin_addition_order_monotonicity
  : forall (x : SignedBin) (y : SignedBin) (z : SignedBin) . (y <= z -> x + y <= x + z)%b_signed
  := SignedBin.addition.order.monotonicity.

Definition data_number_binary_all_delivers_signed_bin_addition_order_mixed_monotonicity
  : forall (a : SignedBin) (b : SignedBin) (c : SignedBin) (d : SignedBin) . (a <= c -> b < d -> a + b < c + d)%b_signed
  := SignedBin.addition.order.mixed.monotonicity.

Definition data_number_binary_all_delivers_signed_bin_addition_order_accumulation
  : forall (a : SignedBin) (b : SignedBin) (c : SignedBin) (d : SignedBin) . (a <= c -> b <= d -> a + b <= c + d)%b_signed
  := SignedBin.addition.order.accumulation.

Definition data_number_binary_all_delivers_signed_bin_order_sign_negativity
  : forall (p : BinBase) . (SignedBin.Negative p < 0)%b_signed
  := SignedBin.order.sign.negativity.

Definition data_number_binary_all_delivers_signed_bin_order_sign_positivity
  : forall (p : BinBase) . (0 < SignedBin.Positive p)%b_signed
  := SignedBin.order.sign.positivity.

Definition data_number_binary_all_delivers_signed_bin_order_negation_strict_reversal
  : forall (x : SignedBin) (y : SignedBin) . (x < y <-> - y < - x)%b_signed
  := SignedBin.order.negation.strict.reversal.

Definition data_number_binary_all_delivers_signed_bin_order_negation_reversal
  : forall (x : SignedBin) (y : SignedBin) . (x <= y -> - y <= - x)%b_signed
  := SignedBin.order.negation.reversal.

Definition data_number_binary_all_delivers_signed_bin_order_subtraction_left_monotonicity
  : forall (x : SignedBin) (y : SignedBin) (z : SignedBin) . (y < z -> y - x < z - x)%b_signed
  := SignedBin.order.subtraction.left.monotonicity.

Definition data_number_binary_all_delivers_signed_bin_order_subtraction_right_antitonicity
  : forall (x : SignedBin) (y : SignedBin) (z : SignedBin) . (y < z -> x - z < x - y)%b_signed
  := SignedBin.order.subtraction.right.antitonicity.

Definition data_number_binary_all_delivers_signed_bin_order_subtraction_positivity
  : forall (x : SignedBin) (y : SignedBin) . (x < y <-> 0 < y - x)%b_signed
  := SignedBin.order.subtraction.positivity.

Definition data_number_binary_all_delivers_signed_bin_order_increment_extensivity
  : forall (x : SignedBin) . (x < x + 1)%b_signed
  := SignedBin.order.increment.extensivity.

Definition data_number_binary_all_delivers_signed_bin_order_increment_specification
  : forall (x : SignedBin) (y : SignedBin) . (x < y <-> x + 1 <= y)%b_signed
  := SignedBin.order.increment.specification.

Definition data_number_binary_all_delivers_signed_bin_order_increment_adjacency
  : forall (x : SignedBin) (y : SignedBin) . (~ (x < y /\ y < x + 1))%b_signed
  := SignedBin.order.increment.adjacency.

Definition data_number_binary_all_delivers_signed_bin_order_decrement_extensivity
  : forall (x : SignedBin) . (x - 1 < x)%b_signed
  := SignedBin.order.decrement.extensivity.

Definition data_number_binary_all_delivers_signed_bin_order_discreteness
  : forall (x : SignedBin) (y : SignedBin) . (x < y + 1 <-> x <= y)%b_signed
  := SignedBin.order.discreteness.

Definition data_number_binary_all_delivers_signed_bin_order_embedding_preservation
  : forall (m : Bin0) (n : Bin0) .
      (m < n)%b0 <-> (SignedBin.from_b0 m < SignedBin.from_b0 n)%b_signed
  := SignedBin.order.embedding.preservation.

Definition data_number_binary_all_delivers_signed_bin_order_embedding_nonnegativity
  : forall (n : Bin0) . (0 <= SignedBin.from_b0 n)%b_signed
  := SignedBin.order.embedding.nonnegativity.

Definition data_number_binary_all_delivers_signed_bin_multiplication_left_negation
  : forall (x : SignedBin) (y : SignedBin) . (- x * y = - (x * y))%b_signed
  := SignedBin.multiplication.left.negation.

Definition data_number_binary_all_delivers_signed_bin_multiplication_left_order_strict_monotonicity
  : forall (k : SignedBin) (x : SignedBin) (y : SignedBin) . (0 < k -> x < y -> k * x < k * y)%b_signed
  := SignedBin.multiplication.left.order.strict.monotonicity.

Definition data_number_binary_all_delivers_signed_bin_multiplication_left_order_strict_reversal
  : forall (k : SignedBin) (x : SignedBin) (y : SignedBin) . (k < 0 -> x < y -> k * y < k * x)%b_signed
  := SignedBin.multiplication.left.order.strict.reversal.

Definition data_number_binary_all_delivers_signed_bin_multiplication_left_order_monotonicity
  : forall (k : SignedBin) (x : SignedBin) (y : SignedBin) . (0 <= k -> x <= y -> k * x <= k * y)%b_signed
  := SignedBin.multiplication.left.order.monotonicity.

Definition data_number_binary_all_delivers_signed_bin_multiplication_sign_positivity
  : forall (x : SignedBin) (y : SignedBin) . (0 < x -> 0 < y -> 0 < x * y)%b_signed
  := SignedBin.multiplication.sign.positivity.

Definition data_number_binary_all_delivers_signed_bin_multiplication_sign_negation_positivity
  : forall (x : SignedBin) (y : SignedBin) . (x < 0 -> y < 0 -> 0 < x * y)%b_signed
  := SignedBin.multiplication.sign.negation.positivity.

Definition data_number_binary_all_delivers_signed_bin_multiplication_sign_left_negativity
  : forall (x : SignedBin) (y : SignedBin) . (x < 0 -> 0 < y -> x * y < 0)%b_signed
  := SignedBin.multiplication.sign.left.negativity.

Definition data_number_binary_all_delivers_signed_bin_multiplication_sign_right_negativity
  : forall (x : SignedBin) (y : SignedBin) . (0 < x -> y < 0 -> x * y < 0)%b_signed
  := SignedBin.multiplication.sign.right.negativity.

Definition data_number_binary_all_delivers_signed_bin_comparison_translation
  : forall (z : SignedBin) (x : SignedBin) (y : SignedBin) . SignedBin.compare (z + x)%b_signed (z + y)%b_signed = SignedBin.compare x y
  := SignedBin.comparison.translation.

Definition data_number_binary_all_delivers_signed_bin_comparison_negation
  : forall (x : SignedBin) (y : SignedBin) . SignedBin.compare (- x)%b_signed (- y)%b_signed = SignedBin.compare y x
  := SignedBin.comparison.negation.

Definition data_number_binary_all_delivers_signed_bin_minimum_left_distributivity_addition
  : forall (z : SignedBin) (x : SignedBin) (y : SignedBin) .
      (z + SignedBin.min x y)%b_signed = SignedBin.min (z + x)%b_signed (z + y)%b_signed
  := SignedBin.minimum.left.distributivity.addition.

Definition data_number_binary_all_delivers_signed_bin_maximum_left_distributivity_addition
  : forall (z : SignedBin) (x : SignedBin) (y : SignedBin) .
      (z + SignedBin.max x y)%b_signed = SignedBin.max (z + x)%b_signed (z + y)%b_signed
  := SignedBin.maximum.left.distributivity.addition.

Definition data_number_binary_all_delivers_signed_bin_minimum_duality
  : forall (x : SignedBin) (y : SignedBin) . (- SignedBin.min x y)%b_signed = SignedBin.max (- x)%b_signed (- y)%b_signed
  := SignedBin.minimum.duality.
