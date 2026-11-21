(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

From JW Require Import Algebra.AbelianGroup.
From JW Require Import Algebra.Commutative.
From JW Require Import Algebra.Group.
From JW Require Import Algebra.Monoid.
From JW Require Import Algebra.Ring.
From JW Require Import Algebra.Semigroup.
From JW Require Import Core.All.
From JW Require Import Data.Base.Comparison.
From JW Require Import Data.Comparable.
From JW Require Import Data.Machine.Bit.
From JW Require Import Data.Machine.Byte.
From JW Require Import Data.Machine.Modular.
From JW Require Import Data.Machine.Signed.
From JW Require Import Data.Number.Binary.Bin.
From JW Require Import Data.Number.Binary.BinBase.
From JW Require Import Data.Number.Binary.BinWithZero.
From JW Require Import Data.Number.Integer.
From JW Require Import Data.Number.Nat.
From JW Require Import Data.Number.Nat0.
From JW Require Import Data.Number.Numeral.
From JW Require Import Data.Option.
From JW Require Import Data.Product.
From JW Require Import Tactics.Equation.
From JW Require Import Tactics.Modus.
From JW Require Import Tactics.Witness.

(* A signed integer of eight bits: a [Byte] read in two's complement, from
 * -128 (-2^7) to 127 (2^7 - 1), its arithmetic wrapping modulo 256 (2^8). In
 * this file [100000000] is 2^8, [10000000] is 2^7 and [1111111] is 2^7 - 1,
 * written in binary digits.
 *)

Module Int8. (* Int8 *)

Inductive T : Type :=
  | introduction : Byte -> T.

Abbreviation Int8 := T.

(* The number of values, 256 (2^8), the arithmetic wrapping modulo it. *)
(* [BinBase] *)
Definition modulus := 100000000%bin_base.

(* [Int8 -> Byte] *)
Definition to_byte := fun (x : Int8) .
  match x with
  | Int8.introduction b => b
  end.

(* [Byte -> Int8] *)
Definition from_byte := fun (b : Byte) . Int8.introduction b.

(* The bits read as a number in base two, the most significant first, from 0
 * to 255: the value of the bit pattern, through which the arithmetic is
 * proved and from which [to_bin] takes the signed value; [10] is two in
 * binary digits.
 *)
(* [Int8 -> BinWithZero] *)
Definition unsigned_value := fun (x : Int8) .
  match x with
  | Int8.introduction (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
      (10 * (10 * (10 * (10 * (10 * (10 * (10 * Bit.to_bin_with_zero x7
        + Bit.to_bin_with_zero x6) + Bit.to_bin_with_zero x5) + Bit.to_bin_with_zero x4)
        + Bit.to_bin_with_zero x3) + Bit.to_bin_with_zero x2) + Bit.to_bin_with_zero x1)
        + Bit.to_bin_with_zero x0)%bin_with_zero
  end.

(* The top bit, [1] for a negative value. *)
(* [Int8 -> Bit] *)
Definition sign_bit := fun (x : Int8) .
  match x with
  | Int8.introduction (Byte.introduction x7 _ _ _ _ _ _ _) => x7
  end.

(* The value in two's complement: the unsigned value, less 256 when the sign
 * bit is set.
 *)
(* [Int8 -> Bin] *)
Definition to_bin := fun (x : Int8) .
  Bin.bin_with_zero_difference
    (unsigned_value x) (modulus * Bit.to_bin_with_zero (sign_bit x))%bin_with_zero.

(* From here to the end of the module an [Int8] stands where a [Bin] is expected,
 * read as its value; the conversion is printed.
 *)
Local Coercion to_bin : T >-> Bin.
Add Printing Coercion to_bin.

(* The value in [Integer], through [to_bin]; [Integer] is unary, so it is for
 * stating and proving, and computing goes through [to_bin].
 *)
(* [Int8 -> Integer] *)
Definition to_integer := fun (x : Int8) . Bin.to_integer (to_bin x).

(* [Int8] *)
Definition Zero := Int8.introduction Byte.Zero.

(* [Int8] *)
Definition One :=
  Int8.introduction
    (Byte.introduction
      0 0 0 0 0 0 0 1).

(* The least value, -128: only the sign bit set. *)
(* [Int8] *)
Definition Min :=
  Int8.introduction
    (Byte.introduction
      1 0 0 0 0 0 0 0).

(* The greatest value, 127: every bit but the sign bit set. *)
(* [Int8] *)
Definition Max :=
  Int8.introduction
    (Byte.introduction
      0 1 1 1 1 1 1 1).

(* [Int8 -> Nat0 -> Int8] *)
Definition shift_left := fun (x : Int8) (k : Nat0) .
  match x with
  | Int8.introduction b => Int8.introduction (Byte.shift_left b k)
  end.

(* [k] places toward the least significant end, the sign bit copied in at
 * the other; one place first, then [k - 1].
 *)
(* [Int8 -> Nat -> Int8] *)
Fixpoint shift_right_nat (x : Int8) (k : Nat) : Int8 :=
  let y :=
    match x with
    | Int8.introduction (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
        Int8.introduction (Byte.introduction x7 x7 x6 x5 x4 x3 x2 x1)
    end in
  match k with
  | Nat.One          => y
  | Nat.Successor k' => shift_right_nat y k'
  end.

(* [Int8 -> Nat0 -> Int8] *)
Definition shift_right := fun (x : Int8) (k : Nat0) .
  match k with
  | Nat0.Zero       => x
  | Nat0.Positive n => shift_right_nat x n
  end.

(* [x] with [b] written after its lowest bit, the highest bit dropped. *)
(* [Bit -> Int8 -> Int8] *)
Definition append_bit := fun (b : Bit) (x : Int8) .
  match x with
  | Int8.introduction (Byte.introduction _ x6 x5 x4 x3 x2 x1 x0) =>
      Int8.introduction (Byte.introduction x6 x5 x4 x3 x2 x1 x0 b)
  end.

(* The carry out and the sum of [carry + x + y], the carry rippling up from
 * the least significant place.
 *)
(* [Bit -> Int8 -> Int8 -> Product Bit Int8] *)
Definition add_with_carry := fun (carry : Bit) (x : Int8) (y : Int8) .
  match x with
  | Int8.introduction (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
      match y with
      | Int8.introduction (Byte.introduction y7 y6 y5 y4 y3 y2 y1 y0) =>
          let r0 := Bit.add_with_carry carry x0 y0 in
          let r1 := Bit.add_with_carry (pi_1 r0) x1 y1 in
          let r2 := Bit.add_with_carry (pi_1 r1) x2 y2 in
          let r3 := Bit.add_with_carry (pi_1 r2) x3 y3 in
          let r4 := Bit.add_with_carry (pi_1 r3) x4 y4 in
          let r5 := Bit.add_with_carry (pi_1 r4) x5 y5 in
          let r6 := Bit.add_with_carry (pi_1 r5) x6 y6 in
          let r7 := Bit.add_with_carry (pi_1 r6) x7 y7 in
          (pi_1 r7,
            Int8.introduction
              (Byte.introduction
                (pi_2 r7) (pi_2 r6) (pi_2 r5) (pi_2 r4)
                (pi_2 r3) (pi_2 r2) (pi_2 r1) (pi_2 r0)))
      end
  end%product.

(* [Int8 -> Int8 -> Int8] *)
Definition add := fun (x : Int8) (y : Int8) . (pi_2 (add_with_carry 0 x y))%product.

(* [only parsing] keeps goals printing the operations by name. *)
Notation "x + y" := (add x y) (only parsing)
  : jw_int8_scope.

(* The borrow out and the difference of [x - y - borrow], the borrow
 * rippling up as the carry does in [add_with_carry].
 *)
(* [Bit -> Int8 -> Int8 -> Product Bit Int8] *)
Definition sub_with_borrow := fun (borrow : Bit) (x : Int8) (y : Int8) .
  match x with
  | Int8.introduction (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
      match y with
      | Int8.introduction (Byte.introduction y7 y6 y5 y4 y3 y2 y1 y0) =>
          let r0 := Bit.sub_with_borrow borrow x0 y0 in
          let r1 := Bit.sub_with_borrow (pi_1 r0) x1 y1 in
          let r2 := Bit.sub_with_borrow (pi_1 r1) x2 y2 in
          let r3 := Bit.sub_with_borrow (pi_1 r2) x3 y3 in
          let r4 := Bit.sub_with_borrow (pi_1 r3) x4 y4 in
          let r5 := Bit.sub_with_borrow (pi_1 r4) x5 y5 in
          let r6 := Bit.sub_with_borrow (pi_1 r5) x6 y6 in
          let r7 := Bit.sub_with_borrow (pi_1 r6) x7 y7 in
          (pi_1 r7,
            Int8.introduction
              (Byte.introduction
                (pi_2 r7) (pi_2 r6) (pi_2 r5) (pi_2 r4)
                (pi_2 r3) (pi_2 r2) (pi_2 r1) (pi_2 r0)))
      end
  end%product.

(* [Int8 -> Int8 -> Int8] *)
Definition sub := fun (x : Int8) (y : Int8) . (pi_2 (sub_with_borrow 0 x y))%product.

Notation "x - y" := (sub x y) (only parsing)
  : jw_int8_scope.

(* [x] taken from [Zero], wrapping. *)
(* [Int8 -> Int8] *)
Definition negate := fun (x : Int8) . sub Zero x.

(* Also what makes the minus of a negative literal parse: [Numeral.Signed]
 * lets [from_numeral] receive a sign but puts none in the grammar.
 *)
Notation "- x" := (negate x)
  (at level 35, right associativity, only parsing)
  : jw_int8_scope.

(* [y]'s bits from the most significant, each step doubling the product so
 * far and adding [x] for a 1, all modulo 256.
 *)
(* [Int8 -> Int8 -> Int8] *)
Definition mul := fun (x : Int8) (y : Int8) .
  let step := fun (p : Int8) (b : Bit) .
    add (shift_left p 1%n0)
      match b with
      | 0%bit => Zero
      | 1%bit => x
      end in
  match y with
  | Int8.introduction (Byte.introduction y7 y6 y5 y4 y3 y2 y1 y0) =>
      step (step (step (step (step (step (step (step Zero y7) y6) y5) y4) y3) y2) y1) y0
  end.

Notation "x * y" := (mul x y) (only parsing)
  : jw_int8_scope.

(* The bit pattern of [p] modulo 256, its bits appended from the most
 * significant.
 *)
(* [BinBase -> Int8] *)
Fixpoint from_bin_base (p : BinBase) : Int8 :=
  match p with
  | BinBase.One   => One
  | BinBase.b0 p' => append_bit 0 (from_bin_base p')
  | BinBase.b1 p' => append_bit 1 (from_bin_base p')
  end.

(* [BinWithZero -> Int8] *)
Definition from_bin_with_zero := fun (n : BinWithZero) .
  match n with
  | BinWithZero.Zero       => Zero
  | BinWithZero.Positive p => from_bin_base p
  end.

(* [Nat -> Int8] *)
Definition from_nat := fun (n : Nat) . from_bin_base (BinBase.from_nat n).

(* [Nat0 -> Int8] *)
Definition from_nat0 := fun (n : Nat0) . from_bin_with_zero (BinWithZero.from_nat0 n).

(* [z] modulo 256 into the range -128 to 127: its positive part less its
 * negative part, wrapping.
 *)
(* [Bin -> Int8] *)
Definition from_bin := fun (z : Bin) .
  add (from_bin_with_zero (Bin.ramp z)) (negate (from_bin_with_zero (Bin.ramp (Bin.negate z)))).

(* The quotient through [Bin], toward zero, [None] when [y] is zero. [Bin.divide]
 * takes a positive divisor, so the divisor's sign is matched here; -128 (-2^7)
 * over -1 wraps to itself.
 *)
(* [Int8 -> Int8 -> Option Int8] *)
Definition divide := fun (x : Int8) (y : Int8) .
  match to_bin y with
  | Bin.Negative d => Some (from_bin (Bin.negate (x /. d)%b))
  | Bin.Zero       => None
  | Bin.Positive d => Some (from_bin (x /. d)%b)
  end.

Notation "x /. y" := (divide x y) (only parsing)
  : jw_int8_scope.

(* [x] modulo 256 into the range -128 to 127. *)
(* [Integer -> Int8] *)
Definition from_integer := fun (x : Integer) .
  match x with
  | Integer.Negative p => negate (from_nat p)
  | Integer.Zero       => Zero
  | Integer.Positive p => from_nat p
  end.

(* The overflow flag and the sum of [x + y]: the flag is set when [x] and [y]
 * have the same sign and the sum the other, the true sum lying past -128 or
 * 127.
 *)
(* [Int8 -> Int8 -> Product Bit Int8] *)
Definition add_with_overflow := fun (x : Int8) (y : Int8) .
  let flag :=
    Bit.and
      (Bit.flip (Bit.xor (sign_bit x) (sign_bit y)))
      (Bit.xor (sign_bit (add x y)) (sign_bit x)) in
  (flag, add x y)%product.

(* The overflow flag and the difference of [x - y]: the flag is set when [x]
 * and [y] have different signs and the difference has the sign of [y], the
 * true difference lying past -128 or 127.
 *)
(* [Int8 -> Int8 -> Product Bit Int8] *)
Definition sub_with_overflow := fun (x : Int8) (y : Int8) .
  let flag :=
    Bit.and
      (Bit.xor (sign_bit x) (sign_bit y))
      (Bit.xor (sign_bit (sub x y)) (sign_bit x)) in
  (flag, sub x y)%product.

(* [Int8 -> Int8 -> Prop] *)
Definition LessThan := fun (x : Int8) (y : Int8) . (to_bin x < to_bin y)%b.

Notation "x < y" := (LessThan x y) (only parsing)
  : jw_int8_scope.

(* [Int8 -> Int8 -> Prop] *)
Definition LessOrEqual := fun (x : Int8) (y : Int8) . x = y \/ LessThan x y.

Notation "x <= y" := (LessOrEqual x y) (only parsing)
  : jw_int8_scope.

Notation "x > y" := (LessThan y x) (only parsing)
  : jw_int8_scope.
Notation "x >= y" := (LessOrEqual y x) (only parsing)
  : jw_int8_scope.

Notation "'(<)'" := LessThan (only parsing)
  : jw_int8_scope.
Notation "'(<=)'" := LessOrEqual (only parsing)
  : jw_int8_scope.

(* [Int8 -> Int8 -> Comparison] *)
Definition compare := fun (x : Int8) (y : Int8) . Bin.compare (to_bin x) (to_bin y).

(* [Int8 -> Int8 -> Bool] *)
Abbreviation eq := (Comparable.eq compare).

(* [Int8 -> Int8 -> Bool] *)
Abbreviation le := (Comparable.le compare).

(* [Int8 -> Int8 -> Int8] *)
Abbreviation min := (Comparable.min compare).

(* [Int8 -> Int8 -> Int8] *)
Abbreviation max := (Comparable.max compare).

(* A literal of -128 to 127, in decimal or hexadecimal, read in binary; any
 * wider is refused.
 *)
(* [Numeral.Signed -> Option Int8] *)
Definition from_numeral := fun (s : Numeral.Signed) .
  let positive := fun (v : BinWithZero) .
    match BinWithZero.compare v 1111111%bin_with_zero with
    | Comparison.Lt => Some (from_bin_with_zero v)
    | Comparison.Eq => Some (from_bin_with_zero v)
    | Comparison.Gt => None
    end in
  let negative := fun (v : BinWithZero) .
    match BinWithZero.compare v 10000000%bin_with_zero with
    | Comparison.Lt => Some (negate (from_bin_with_zero v))
    | Comparison.Eq => Some (negate (from_bin_with_zero v))
    | Comparison.Gt => None
    end in
  match s with
  | Numeral.Signed.Decimal (Numeral.Decimal.Signed.Positive d) =>
      positive (BinWithZero.from_decimal 0%bin_with_zero d)
  | Numeral.Signed.Decimal (Numeral.Decimal.Signed.Negative d) =>
      negative (BinWithZero.from_decimal 0%bin_with_zero d)
  | Numeral.Signed.Hexadecimal (Numeral.Hexadecimal.Signed.Positive h) =>
      positive (BinWithZero.from_hexadecimal 0%bin_with_zero h)
  | Numeral.Signed.Hexadecimal (Numeral.Hexadecimal.Signed.Negative h) =>
      negative (BinWithZero.from_hexadecimal 0%bin_with_zero h)
  end.

(* [x] as a literal, in decimal; zero prints as [0], not [-0]. *)
(* [Int8 -> Numeral.Signed] *)
Definition to_numeral := fun (x : Int8) .
  match to_bin x with
  | Bin.Negative p =>
      Numeral.Signed.Decimal
        (Numeral.Decimal.Signed.Negative (BinWithZero.to_decimal (BinWithZero.Positive p)))
  | Bin.Zero =>
      Numeral.Signed.Decimal
        (Numeral.Decimal.Signed.Positive
          (Numeral.Decimal.Digits.Zero Numeral.Decimal.Digits.End))
  | Bin.Positive p =>
      Numeral.Signed.Decimal
        (Numeral.Decimal.Signed.Positive (BinWithZero.to_decimal (BinWithZero.Positive p)))
  end.

Local Open Scope jw_int8_scope.

Module reinterpretation. (* reinterpretation *)

(* reinterpretation.zero *)
Theorem zero : unsigned_value Zero = 0%bin_with_zero.
Proof.
  simpl in |- *.
  quod idem est.
Qed.

(* reinterpretation.one *)
Theorem one : unsigned_value One = 1%bin_with_zero.
Proof.
  simpl in |- *.
  quod idem est.
Qed.

(* reinterpretation.boundedness *)
Theorem boundedness : forall (x : Int8) . (unsigned_value x < modulus)%bin_with_zero.
Proof.
  intros x.
  match &x with | introduction xb end.
  match &xb with | introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  simpl unsigned_value in |- *.
  ipso
    (Bit.conversion.binary.boundedness.propagation _ _ _
      (Bit.conversion.binary.boundedness.propagation _ _ _
        (Bit.conversion.binary.boundedness.propagation _ _ _
          (Bit.conversion.binary.boundedness.propagation _ _ _
            (Bit.conversion.binary.boundedness.propagation _ _ _
              (Bit.conversion.binary.boundedness.propagation _ _ _
                (Bit.conversion.binary.boundedness.propagation _ _ _
                  (Bit.conversion.binary.boundedness &x7)))))))).
Qed.

(* reinterpretation.injectivity *)
Theorem injectivity
  : forall {x : Int8} {y : Int8} . unsigned_value x = unsigned_value y -> x = y.
Proof.
  intros x y e.
  match &x with | introduction xb end.
  match &xb with | introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | introduction yb end.
  match &yb with | introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
  simpl unsigned_value in &e.
  match (Bit.conversion.binary.halving.injectivity &e) with | e1 b0 end.
  match (Bit.conversion.binary.halving.injectivity &e1) with | e2 b1 end.
  match (Bit.conversion.binary.halving.injectivity &e2) with | e3 b2 end.
  match (Bit.conversion.binary.halving.injectivity &e3) with | e4 b3 end.
  match (Bit.conversion.binary.halving.injectivity &e4) with | e5 b4 end.
  match (Bit.conversion.binary.halving.injectivity &e5) with | e6 b5 end.
  match (Bit.conversion.binary.halving.injectivity &e6) with | e7 b6 end.
  leibniz
    &b0, &b1, &b2, &b3, &b4, &b5, &b6, (Bit.conversion.binary.injectivity &e7)
    in |- *.
  quod idem est.
Qed.

(* The numbers are added place by place from the most significant, each
 * place one [Bit.conversion.binary.carry.propagation] around the places
 * above it.
 *)
(* reinterpretation.carry *)
Theorem carry
  : forall (carry : Bit) (x : Int8) (y : Int8) .
      (Bit.to_bin_with_zero carry + unsigned_value x + unsigned_value y
        = modulus * Bit.to_bin_with_zero (pi_1 (add_with_carry carry x y))%product
          + unsigned_value (pi_2 (add_with_carry carry x y))%product)%bin_with_zero.
Proof.
  intros carry x y.
  match &x with | introduction xb end.
  match &xb with | introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | introduction yb end.
  match &yb with | introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
  simpl unsigned_value, add_with_carry in |- *.
  ipso
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
      (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
        (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
          (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
            (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
              (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
                (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
                  (Bit.conversion.binary.carry _ &x7 &y7)))))))).
Qed.

(* reinterpretation.borrow *)
Theorem borrow
  : forall (borrow : Bit) (x : Int8) (y : Int8) .
      (unsigned_value x
        + modulus * Bit.to_bin_with_zero (pi_1 (sub_with_borrow borrow x y))%product
        = unsigned_value y + Bit.to_bin_with_zero borrow
          + unsigned_value (pi_2 (sub_with_borrow borrow x y))%product)%bin_with_zero.
Proof.
  intros borrow x y.
  match &x with | introduction xb end.
  match &xb with | introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | introduction yb end.
  match &yb with | introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
  simpl unsigned_value, sub_with_borrow in |- *.
  ipso
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
      (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
        (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
          (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
            (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
              (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
                (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
                  (Bit.conversion.binary.borrow _ &x7 &y7)))))))).
Qed.

(* reinterpretation.addition *)
Theorem addition
  : forall (x : Int8) (y : Int8) .
      (unsigned_value (x + y)%int8
        = (unsigned_value x + unsigned_value y) %. modulus)%bin_with_zero.
Proof.
  intros x y.
  lemma witness
    : (Bit.to_bin_with_zero (pi_1 (add_with_carry 0 &x &y))%product * modulus
        + unsigned_value (&x + &y)%int8
        = unsigned_value &x + unsigned_value &y
      /\ unsigned_value (&x + &y)%int8 < modulus)%bin_with_zero.
  {
    divide et impera.
    - simpl add in |- *.
      leibniz
        (BinWithZero.multiplication.commutativity
          (Bit.to_bin_with_zero (pi_1 (add_with_carry 0 &x &y))%product)
          modulus),
        <- (reinterpretation.carry 0 &x &y)
        in |- *.
      simpl in |- *.
      quod idem est.
    - ipso (reinterpretation.boundedness (&x + &y)).
  }
  match (BinWithZero.division.uniqueness
          (unsigned_value &x + unsigned_value &y)%bin_with_zero modulus
          (Bit.to_bin_with_zero (pi_1 (add_with_carry 0 &x &y))%product)
          (unsigned_value (&x + &y)%int8)
          &witness)
  with | _ facto end.
  ipso (symm &facto).
Qed.

(* reinterpretation.subtraction *)
Theorem subtraction
  : forall (x : Int8) (y : Int8) .
      ((unsigned_value (sub x y) + unsigned_value y) %. modulus
        = unsigned_value x)%bin_with_zero.
Proof.
  intros x y.
  lemma witness
    : (Bit.to_bin_with_zero (pi_1 (sub_with_borrow 0 &x &y))%product * modulus
        + unsigned_value &x
        = unsigned_value (sub &x &y) + unsigned_value &y
      /\ unsigned_value &x < modulus)%bin_with_zero.
  {
    divide et impera.
    - simpl sub in |- *.
      leibniz
        (BinWithZero.multiplication.commutativity
          (Bit.to_bin_with_zero (pi_1 (sub_with_borrow 0 &x &y))%product)
          modulus),
        (BinWithZero.addition.commutativity
          (modulus
            * Bit.to_bin_with_zero (pi_1 (sub_with_borrow 0 &x &y))%product)%bin_with_zero
          (unsigned_value &x)),
        (reinterpretation.borrow 0 &x &y),
        (BinWithZero.addition.commutativity
          (unsigned_value &y) (Bit.to_bin_with_zero 0))
        in |- *.
      simpl in |- *.
      leibniz
        (BinWithZero.addition.commutativity
          (unsigned_value &y)
          (unsigned_value (pi_2 (sub_with_borrow 0 &x &y))%product))
        in |- *.
      quod idem est.
    - ipso (reinterpretation.boundedness &x).
  }
  match (BinWithZero.division.uniqueness
          (unsigned_value (sub &x &y) + unsigned_value &y)%bin_with_zero modulus
          (Bit.to_bin_with_zero (pi_1 (sub_with_borrow 0 &x &y))%product)
          (unsigned_value &x)
          &witness)
  with | _ facto end.
  ipso facto.
Qed.

(* reinterpretation.negation *)
Theorem negation
  : forall (x : Int8) .
      ((unsigned_value (- x)%int8 + unsigned_value x) %. modulus
        = 0)%bin_with_zero.
Proof.
  intros x.
  simpl negate in |- *.
  leibniz (reinterpretation.subtraction Zero &x), reinterpretation.zero in |- *.
  quod idem est.
Qed.

(* The bits of [x] and then [b] read from the most significant: [b] goes in
 * below and the highest bit falls out, one
 * [Bit.conversion.binary.appending.propagation] per place.
 *)
(* reinterpretation.appending *)
Theorem appending
  : forall (b : Bit) (x : Int8) .
      (unsigned_value (append_bit b x)
        = (10 * unsigned_value x + Bit.to_bin_with_zero b) %. modulus)%bin_with_zero.
Proof.
  intros b x.
  match &x with | introduction xb end.
  match &xb with | introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  lemma witness
    : (Bit.to_bin_with_zero &x7 * modulus
        + unsigned_value
            (append_bit &b
              (Int8.introduction (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)))
        = 10
            * unsigned_value
                (Int8.introduction (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0))
          + Bit.to_bin_with_zero &b
      /\ unsigned_value
          (append_bit &b
            (Int8.introduction (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)))
        < modulus)%bin_with_zero.
  {
    divide et impera.
    - lemma top
        : (Bit.to_bin_with_zero &x7 = Bit.to_bin_with_zero &x7 * 1 + 0)%bin_with_zero.
      {
        match (BinWithZero.addition.identity (Bit.to_bin_with_zero &x7 * 1)%bin_with_zero)
        with | _ sum end.
        match (BinWithZero.multiplication.identity (Bit.to_bin_with_zero &x7))
        with | _ product end.
        leibniz &sum, &product in |- *.
        quod idem est.
      }
      simpl unsigned_value, append_bit in |- *.
      ipso
        (symm
          (Bit.conversion.binary.appending.propagation _ _ _ _ &b
            (Bit.conversion.binary.appending.propagation _ _ _ _ &x0
              (Bit.conversion.binary.appending.propagation _ _ _ _ &x1
                (Bit.conversion.binary.appending.propagation _ _ _ _ &x2
                  (Bit.conversion.binary.appending.propagation _ _ _ _ &x3
                    (Bit.conversion.binary.appending.propagation _ _ _ _ &x4
                      (Bit.conversion.binary.appending.propagation _ _ _ _ &x5
                        (Bit.conversion.binary.appending.propagation _ _ _ _ &x6
                          &top))))))))).
    - ipso
        (reinterpretation.boundedness
          (append_bit &b
            (Int8.introduction (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)))).
  }
  match (BinWithZero.division.uniqueness
          (10 * unsigned_value
                  (Int8.introduction (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0))
            + Bit.to_bin_with_zero &b)%bin_with_zero
          modulus
          (Bit.to_bin_with_zero &x7)
          (unsigned_value
            (append_bit &b
              (Int8.introduction (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0))))
          &witness)
  with | _ facto end.
  ipso (symm &facto).
Qed.

(* reinterpretation.reduction *)
Theorem reduction
  : forall (n : BinWithZero) .
      unsigned_value (from_bin_with_zero n) = (n %. modulus)%bin_with_zero.
Proof.
  intros n.
  match &n with | Zero | Positive p end.
  - simpl from_bin_with_zero, BinWithZero.modulo, BinWithZero.div, Product.second in |- *.
    simpl in |- *.
    quod idem est.
  - simpl from_bin_with_zero in |- *.
    match p with | One | b0 (p' by IH) | b1 (p' by IH) end per BinBase.induction.
    + simpl BinWithZero.modulo, BinWithZero.div in |- *.
      simpl in |- *.
      quod idem est.
    + lemma unfolding
        : from_bin_base (BinBase.b0 &p') = append_bit 0 (from_bin_base &p').
      {
        simpl in |- *.
        quod idem est.
      }
      leibniz
        &unfolding,
        (reinterpretation.appending 0 (from_bin_base &p')),
        &IH,
        <- (BinWithZero.modulo.sum.left.absorption
          (10 * (BinWithZero.Positive &p' %. modulus))%bin_with_zero
          (Bit.to_bin_with_zero 0) modulus),
        (BinWithZero.modulo.product.right.absorption
          10%bin_with_zero (BinWithZero.Positive &p') modulus),
        (BinWithZero.modulo.sum.left.absorption
          (10 * BinWithZero.Positive &p')%bin_with_zero
          (Bit.to_bin_with_zero 0) modulus)
        in |- *.
      simpl in |- *.
      quod idem est.
    + lemma unfolding
        : from_bin_base (BinBase.b1 &p') = append_bit 1 (from_bin_base &p').
      {
        simpl in |- *.
        quod idem est.
      }
      leibniz
        &unfolding,
        (reinterpretation.appending 1 (from_bin_base &p')),
        &IH,
        <- (BinWithZero.modulo.sum.left.absorption
          (10 * (BinWithZero.Positive &p' %. modulus))%bin_with_zero
          (Bit.to_bin_with_zero 1) modulus),
        (BinWithZero.modulo.product.right.absorption
          10%bin_with_zero (BinWithZero.Positive &p') modulus),
        (BinWithZero.modulo.sum.left.absorption
          (10 * BinWithZero.Positive &p')%bin_with_zero
          (Bit.to_bin_with_zero 1) modulus)
        in |- *.
      simpl in |- *.
      simpl BinBase.add in |- *.
      simpl in |- *.
      quod idem est.
Qed.

Module reduction. (* reinterpretation.reduction *)

(* reinterpretation.reduction.additivity *)
Theorem additivity
  : forall (m : BinWithZero) (n : BinWithZero) .
      from_bin_with_zero (m + n)%bin_with_zero = from_bin_with_zero m + from_bin_with_zero n.
Proof.
  intros m n.
  lemma facto
    : unsigned_value (from_bin_with_zero (&m + &n)%bin_with_zero)
      = unsigned_value (from_bin_with_zero &m + from_bin_with_zero &n).
  {
    leibniz
      (reinterpretation.reduction (&m + &n)%bin_with_zero),
      (reinterpretation.addition (from_bin_with_zero &m) (from_bin_with_zero &n)),
      (reinterpretation.reduction &m),
      (reinterpretation.reduction &n),
      (BinWithZero.modulo.sum.left.absorption
        &m (&n %. modulus)%bin_with_zero modulus),
      (BinWithZero.modulo.sum.right.absorption &m &n modulus)
      in |- *.
    quod idem est.
  }
  ipso (reinterpretation.injectivity &facto).
Qed.

End reduction. (* reinterpretation.reduction *)

(* reinterpretation.section *)
Theorem section : forall (x : Int8) . from_bin_with_zero (unsigned_value x) = x.
Proof.
  intros x.
  lemma facto
    : unsigned_value (from_bin_with_zero (unsigned_value &x)) = unsigned_value &x.
  {
    leibniz
      (reinterpretation.reduction (unsigned_value &x)),
      (BinWithZero.modulo.identity
        (unsigned_value &x) modulus (reinterpretation.boundedness &x))
      in |- *.
    quod idem est.
  }
  ipso (reinterpretation.injectivity &facto).
Qed.

Module left. (* reinterpretation.left *)

(* reinterpretation.left.doubling *)
Lemma doubling
  : forall (x : Int8) .
      (unsigned_value (shift_left x 1%n0)
        = (10 * unsigned_value x) %. modulus)%bin_with_zero.
Proof.
  intros x.
  lemma appended : shift_left &x 1%n0 = append_bit 0 &x.
  {
    match &x with | introduction xb end.
    match &xb with | introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
    simpl in |- *.
    quod idem est.
  }
  match (BinWithZero.addition.identity (10 * unsigned_value &x)%bin_with_zero)
  with | _ sum end.
  leibniz &appended, (reinterpretation.appending 0 &x) in |- *.
  simpl Bit.to_bin_with_zero in |- *.
  leibniz &sum in |- *.
  quod idem est.
Qed.

End left. (* reinterpretation.left *)

Module multiplication. (* reinterpretation.multiplication *)

(* One step of [mul]: the product so far doubled, plus [x] for a 1. *)
(* reinterpretation.multiplication.step *)
Lemma step
  : forall (x : Int8) (p : Int8) (h : BinWithZero) (b : Bit) .
      (unsigned_value p = (unsigned_value x * h) %. modulus)%bin_with_zero ->
      unsigned_value
        (add (shift_left p 1%n0)
          match b with
          | 0%bit => Zero
          | 1%bit => x
          end)
      = ((unsigned_value x * (10 * h + Bit.to_bin_with_zero b))
          %. modulus)%bin_with_zero.
Proof.
  intros x p h b e.
  lemma doubled
    : ((10 * unsigned_value &p) %. modulus
        = (10 * (unsigned_value &x * &h)) %. modulus)%bin_with_zero.
  {
    leibniz
      &e,
      (BinWithZero.modulo.product.right.absorption
        10%bin_with_zero (unsigned_value &x * &h)%bin_with_zero modulus)
      in |- *.
    quod idem est.
  }
  lemma regrouped
    : (unsigned_value &x * (10 * &h) = 10 * (unsigned_value &x * &h))%bin_with_zero.
  {
    leibniz
      <- (BinWithZero.multiplication.associativity (unsigned_value &x) 10%bin_with_zero &h),
      (BinWithZero.multiplication.commutativity (unsigned_value &x) 10%bin_with_zero),
      (BinWithZero.multiplication.associativity 10%bin_with_zero (unsigned_value &x) &h)
      in |- *.
    quod idem est.
  }
  match &b with | Zero | One end.
  - lemma facto
      : unsigned_value (add (shift_left &p 1%n0) Zero)
        = ((unsigned_value &x * (10 * &h + Bit.to_bin_with_zero 0))
            %. modulus)%bin_with_zero.
    {
      match (BinWithZero.addition.identity (10 * unsigned_value &p)%bin_with_zero)
      with | _ right end.
      match (BinWithZero.addition.identity (10 * &h)%bin_with_zero) with | _ right' end.
      leibniz
        (reinterpretation.addition (shift_left &p 1%n0) Zero),
        (reinterpretation.left.doubling &p),
        reinterpretation.zero,
        (BinWithZero.modulo.sum.left.absorption
          (10 * unsigned_value &p)%bin_with_zero 0%bin_with_zero modulus),
        &right,
        &doubled
        in |- *.
      simpl Bit.to_bin_with_zero in |- *.
      leibniz &right', &regrouped in |- *.
      quod idem est.
    }
    ipso facto.
  - lemma facto
      : unsigned_value (add (shift_left &p 1%n0) &x)
        = ((unsigned_value &x * (10 * &h + Bit.to_bin_with_zero 1))
            %. modulus)%bin_with_zero.
    {
      match (BinWithZero.multiplication.identity (unsigned_value &x)) with | _ right end.
      match (BinWithZero.multiplication.distributivity.over.addition
              (unsigned_value &x) (10 * &h)%bin_with_zero 1%bin_with_zero)
      with | spread _ end.
      leibniz
        (reinterpretation.addition (shift_left &p 1%n0) &x),
        (reinterpretation.left.doubling &p),
        &doubled,
        (BinWithZero.modulo.sum.left.absorption
          (10 * (unsigned_value &x * &h))%bin_with_zero (unsigned_value &x)
          modulus)
        in |- *.
      simpl Bit.to_bin_with_zero in |- *.
      leibniz &spread, &right, &regrouped in |- *.
      quod idem est.
    }
    ipso facto.
Qed.

End multiplication. (* reinterpretation.multiplication *)

(* reinterpretation.multiplication *)
Theorem multiplication
  : forall (x : Int8) (y : Int8) .
      (unsigned_value (x * y)%int8
        = (unsigned_value x * unsigned_value y) %. modulus)%bin_with_zero.
Proof.
  intros x y.
  lemma base
    : (unsigned_value Zero
        = (unsigned_value &x * 0) %. modulus)%bin_with_zero.
  {
    match (BinWithZero.multiplication.annihilation (unsigned_value &x)) with | _ right end.
    leibniz &right, reinterpretation.zero in |- *.
    simpl BinWithZero.modulo, BinWithZero.div, Product.second in |- *.
    quod idem est.
  }
  match &y with | introduction yb end.
  match &yb with | introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
  simpl mul in |- *.
  ipso
    (reinterpretation.multiplication.step _ _ _ _
      (reinterpretation.multiplication.step _ _ _ _
        (reinterpretation.multiplication.step _ _ _ _
          (reinterpretation.multiplication.step _ _ _ _
            (reinterpretation.multiplication.step _ _ _ _
              (reinterpretation.multiplication.step _ _ _ _
                (reinterpretation.multiplication.step _ _ _ _
                  (reinterpretation.multiplication.step _ _ _ _ &base)))))))).
Qed.

Module sign. (* reinterpretation.sign *)

(* reinterpretation.sign.clear *)
Theorem clear
  : forall (x : Int8) . sign_bit x = 0%bit -> (unsigned_value x < 10000000)%bin_with_zero.
Proof.
  intros x e.
  match &x with | introduction xb end.
  match &xb with | introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  simpl sign_bit in &e.
  simpl unsigned_value in |- *.
  leibniz &e in |- *.
  lemma base : (Bit.to_bin_with_zero 0 < 1)%bin_with_zero.
  {
    simpl BinWithZero.LessThan in |- *.
    exists BinBase.One.
    simpl in |- *.
    quod idem est.
  }
  ipso
    (Bit.conversion.binary.boundedness.propagation _ _ _
      (Bit.conversion.binary.boundedness.propagation _ _ _
        (Bit.conversion.binary.boundedness.propagation _ _ _
          (Bit.conversion.binary.boundedness.propagation _ _ _
            (Bit.conversion.binary.boundedness.propagation _ _ _
              (Bit.conversion.binary.boundedness.propagation _ _ _
                (Bit.conversion.binary.boundedness.propagation _ _ _ &base))))))).
Qed.

(* reinterpretation.sign.set *)
Theorem set
  : forall (x : Int8) . sign_bit x = 1%bit -> (10000000 <= unsigned_value x)%bin_with_zero.
Proof.
  intros x e.
  match &x with | introduction xb end.
  match &xb with | introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  simpl sign_bit in &e.
  simpl unsigned_value in |- *.
  leibniz &e in |- *.
  lemma base : (1 <= Bit.to_bin_with_zero 1)%bin_with_zero.
  {
    simpl BinWithZero.LessOrEqual, Bit.to_bin_with_zero in |- *.
    ipso (disjoin (refl 1%bin_with_zero), _).
  }
  ipso
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
      (Bit.conversion.binary.boundedness.lower.propagation _ _ _
        (Bit.conversion.binary.boundedness.lower.propagation _ _ _
          (Bit.conversion.binary.boundedness.lower.propagation _ _ _
            (Bit.conversion.binary.boundedness.lower.propagation _ _ _
              (Bit.conversion.binary.boundedness.lower.propagation _ _ _
                (Bit.conversion.binary.boundedness.lower.propagation _ _ _ &base))))))).
Qed.

End sign. (* reinterpretation.sign *)

End reinterpretation. (* reinterpretation *)

(* [Int8] as a [Modular.Width]: its unsigned values are the residues modulo
 * 256, and the laws of addition, subtraction and multiplication are read
 * through them.
 *)
Module Residue <: Modular.Width.

Definition T := T.
Definition Zero := Zero.
Definition One := One.
Definition to_bin_with_zero := unsigned_value.
Definition add := add.
Definition sub := sub.
Definition negate := negate.
Definition mul := mul.
Definition modulus := modulus.

Module conversion. (* Residue.conversion *)

Definition zero := Int8.reinterpretation.zero.
Definition one := Int8.reinterpretation.one.
Definition boundedness := Int8.reinterpretation.boundedness.
Definition injectivity := @Int8.reinterpretation.injectivity.
Definition addition := Int8.reinterpretation.addition.
Definition subtraction := Int8.reinterpretation.subtraction.
Definition negation := Int8.reinterpretation.negation.
Definition multiplication := Int8.reinterpretation.multiplication.

End conversion. (* Residue.conversion *)

End Residue.

Include Modular.Laws Residue.

Module conversion. (* conversion *)

(* The bit pattern of [a - b] is that of [a] less that of [b]. *)
(* conversion.difference *)
Lemma difference
  : forall (a : BinWithZero) (b : BinWithZero) .
      from_bin (Bin.bin_with_zero_difference a b)
      = from_bin_with_zero a + - from_bin_with_zero b.
Proof.
  intros a b.
  let proof e := congru from_bin_with_zero, (Bin.difference.specification &a &b).
  leibniz
    (reinterpretation.reduction.additivity (Bin.ramp (Bin.bin_with_zero_difference &a &b)) &b),
    (reinterpretation.reduction.additivity
      (Bin.ramp (Bin.negate (Bin.bin_with_zero_difference &a &b))) &a)
    in &e.
  simpl from_bin in |- *.
  let p := from_bin_with_zero (Bin.ramp (Bin.bin_with_zero_difference &a &b)) in &e |- *.
  let q :=
    from_bin_with_zero (Bin.ramp (Bin.negate (Bin.bin_with_zero_difference &a &b)))
    in &e |- *.
  lemma rewritten : &p = (&q + from_bin_with_zero &a) + - from_bin_with_zero &b.
  {
    match (addition.inverse (from_bin_with_zero &b)) with | _ cancel end.
    match (addition.identity &p) with | _ unit end.
    leibniz
      <- &e,
      (addition.associativity &p (from_bin_with_zero &b) (- from_bin_with_zero &b)),
      &cancel,
      &unit
      in |- *.
    quod idem est.
  }
  match (addition.inverse &q) with | _ cancel end.
  match (addition.identity (- from_bin_with_zero &b)) with | _ unit end.
  leibniz
    &rewritten,
    (addition.commutativity &q (from_bin_with_zero &a)),
    (addition.associativity (from_bin_with_zero &a) &q (- from_bin_with_zero &b)),
    (addition.commutativity &q (- from_bin_with_zero &b)),
    (addition.associativity (from_bin_with_zero &a) (- from_bin_with_zero &b + &q) (- &q)),
    (addition.associativity (- from_bin_with_zero &b) &q (- &q)),
    &cancel,
    &unit
    in |- *.
  quod idem est.
Qed.

(* conversion.section *)
Theorem section : forall (x : Int8) . from_bin (to_bin x) = x.
Proof.
  intros x.
  lemma vanishing
    : from_bin_with_zero (modulus * Bit.to_bin_with_zero (sign_bit &x))%bin_with_zero = Zero.
  {
    lemma facto
      : unsigned_value
          (from_bin_with_zero (modulus * Bit.to_bin_with_zero (sign_bit &x))%bin_with_zero)
        = unsigned_value Zero.
    {
      leibniz
        (reinterpretation.reduction (modulus * Bit.to_bin_with_zero (sign_bit &x))%bin_with_zero),
        reinterpretation.zero
        in |- *.
      match (sign_bit &x) with | Zero | One end.
      - simpl Bit.to_bin_with_zero, BinWithZero.modulo, BinWithZero.div, Product.second
          in |- *.
        simpl in |- *.
        quod idem est.
      - simpl Bit.to_bin_with_zero, BinWithZero.modulo, BinWithZero.div, Product.second
          in |- *.
        simpl in |- *.
        quod idem est.
    }
    ipso (reinterpretation.injectivity &facto).
  }
  lemma unsigned : - Zero = Zero.
  {
    match (addition.inverse Zero) with | _ right end.
    match (addition.identity (- Zero)) with | left _ end.
    ipso (trans (symm &left), &right).
  }
  match (addition.identity &x) with | _ right end.
  simpl to_bin in |- *.
  leibniz
    (conversion.difference
      (unsigned_value &x) (modulus * Bit.to_bin_with_zero (sign_bit &x))%bin_with_zero),
    (reinterpretation.section &x),
    &vanishing,
    &unsigned,
    &right
    in |- *.
  quod idem est.
Qed.

(* conversion.injectivity *)
Theorem injectivity : forall {x : Int8} {y : Int8} . to_bin x = to_bin y -> x = y.
Proof.
  intros x y e.
  leibniz <- (conversion.section &x), <- (conversion.section &y), &e in |- *.
  quod idem est.
Qed.

(* Without an overflow, the sign bits of [x] and [y] sum to the carry out of
 * [x + y] and its sign bit.
 *)
(* conversion.sign *)
Lemma sign
  : forall (x : Int8) (y : Int8) .
      (pi_1 (add_with_overflow x y))%product = 0%bit ->
      (Bit.to_bin_with_zero (sign_bit x) + Bit.to_bin_with_zero (sign_bit y)
        = Bit.to_bin_with_zero (pi_1 (add_with_carry 0 x y))%product
          + Bit.to_bin_with_zero (sign_bit (x + y)%int8))%bin_with_zero.
Proof.
  intros x y o.
  match &x with | introduction xb end.
  match &xb with | introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | introduction yb end.
  match &yb with | introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
  simpl in &o |- *.
  ipso (Bit.conversion.binary.carry.conservation _ &x7 &y7 &o).
Qed.

(* conversion.addition *)
Theorem addition
  : forall (x : Int8) (y : Int8) .
      (pi_1 (add_with_overflow x y))%product = 0%bit ->
      to_bin (x + y) = (x + y)%b.
Proof.
  intros x y o.
  let proof t := conversion.sign &x &y &o.
  let proof a
    : (unsigned_value &x + unsigned_value &y
        = modulus * Bit.to_bin_with_zero (pi_1 (add_with_carry 0 &x &y))%product
          + unsigned_value (&x + &y)%int8)%bin_with_zero
    := reinterpretation.carry 0 &x &y.
  lemma balance
    : (unsigned_value (&x + &y)%int8
        + (modulus * Bit.to_bin_with_zero (sign_bit &x)
          + modulus * Bit.to_bin_with_zero (sign_bit &y))
        = (unsigned_value &x + unsigned_value &y)
          + modulus * Bit.to_bin_with_zero (sign_bit (&x + &y)%int8))%bin_with_zero.
  {
    match (BinWithZero.multiplication.distributivity.over.addition
            modulus
            (Bit.to_bin_with_zero (sign_bit &x)) (Bit.to_bin_with_zero (sign_bit &y)))
    with | signs _ end.
    match (BinWithZero.multiplication.distributivity.over.addition
            modulus
            (Bit.to_bin_with_zero (pi_1 (add_with_carry 0 &x &y))%product)
            (Bit.to_bin_with_zero (sign_bit (&x + &y)%int8)))
    with | carries _ end.
    leibniz
      <- &signs,
      &t,
      &carries,
      <- (BinWithZero.addition.associativity
        (unsigned_value (&x + &y)%int8)
        (modulus
          * Bit.to_bin_with_zero (pi_1 (add_with_carry 0 &x &y))%product)%bin_with_zero
        (modulus * Bit.to_bin_with_zero (sign_bit (&x + &y)%int8))%bin_with_zero),
      (BinWithZero.addition.commutativity
        (unsigned_value (&x + &y)%int8)
        (modulus
          * Bit.to_bin_with_zero (pi_1 (add_with_carry 0 &x &y))%product)%bin_with_zero),
      &a
      in |- *.
    quod idem est.
  }
  simpl to_bin in |- *.
  leibniz
    (Bin.difference.additivity
      (unsigned_value &x) (modulus * Bit.to_bin_with_zero (sign_bit &x))%bin_with_zero
      (unsigned_value &y) (modulus * Bit.to_bin_with_zero (sign_bit &y))%bin_with_zero)
    in |- *.
  ipso (Bin.difference.invariance &balance).
Qed.

Module right. (* conversion.right *)

(* A shift to the right by one place halves the value, rounding down: the
 * lowest bit is what it drops, and the sign bit copied in keeps the sign.
 *)
(* conversion.right.halving *)
Theorem halving
  : forall (x7 : Bit) (x6 : Bit) (x5 : Bit) (x4 : Bit)
      (x3 : Bit) (x2 : Bit) (x1 : Bit) (x0 : Bit) .
      to_bin (Int8.introduction (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0))
      = (10
          * shift_right (Int8.introduction (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0)) 1%n0
          + Bit.to_bin_with_zero x0)%b.
Proof.
  intros x7 x6 x5 x4 x3 x2 x1 x0.
  lemma shifted
    : shift_right
        (Int8.introduction (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)) 1%n0
      = Int8.introduction (Byte.introduction &x7 &x7 &x6 &x5 &x4 &x3 &x2 &x1).
  {
    simpl in |- *.
    quod idem est.
  }
  lemma split
    : (10 * unsigned_value
              (Int8.introduction (Byte.introduction &x7 &x7 &x6 &x5 &x4 &x3 &x2 &x1))
        + Bit.to_bin_with_zero &x0
        = Bit.to_bin_with_zero &x7 * modulus
          + unsigned_value
              (Int8.introduction
                (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)))%bin_with_zero.
  {
    lemma top
      : (Bit.to_bin_with_zero &x7 = Bit.to_bin_with_zero &x7 * 1 + 0)%bin_with_zero.
    {
      match (BinWithZero.addition.identity (Bit.to_bin_with_zero &x7 * 1)%bin_with_zero)
      with | _ sum end.
      match (BinWithZero.multiplication.identity (Bit.to_bin_with_zero &x7))
      with | _ product end.
      leibniz &sum, &product in |- *.
      quod idem est.
    }
    simpl unsigned_value in |- *.
    ipso
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x0
        (Bit.conversion.binary.appending.propagation _ _ _ _ &x1
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x2
            (Bit.conversion.binary.appending.propagation _ _ _ _ &x3
              (Bit.conversion.binary.appending.propagation _ _ _ _ &x4
                (Bit.conversion.binary.appending.propagation _ _ _ _ &x5
                  (Bit.conversion.binary.appending.propagation _ _ _ _ &x6
                    (Bit.conversion.binary.appending.propagation _ _ _ _ &x7
                      &top)))))))).
  }
  lemma twice : forall (z : Bin) . (10 * z = z + z)%b.
  {
    intros z.
    lemma ten : (10 = 1 + 1)%b.
    {
      simpl Bin.add in |- *.
      simpl in |- *.
      simpl BinBase.add in |- *.
      simpl in |- *.
      quod idem est.
    }
    match (Bin.multiplication.distributivity.over.addition &z 1%b 1%b) with | _ spread end.
    match (Bin.multiplication.identity &z) with | unit _ end.
    leibniz &ten, &spread, &unit in |- *.
    quod idem est.
  }
  lemma doubled
    : forall (n : BinWithZero) . (n + n = 10 * n)%bin_with_zero.
  {
    intros n.
    lemma ten : (10 = 1 + 1)%bin_with_zero.
    {
      simpl in |- *.
      simpl BinBase.add in |- *.
      simpl in |- *.
      quod idem est.
    }
    match (BinWithZero.multiplication.distributivity.over.addition &n 1%bin_with_zero
            1%bin_with_zero)
    with | _ spread end.
    match (BinWithZero.multiplication.identity &n) with | unit _ end.
    leibniz &ten, &spread, &unit in |- *.
    quod idem est.
  }
  lemma embedding
    : forall (n : BinWithZero) .
        Bin.from_bin_with_zero n = Bin.bin_with_zero_difference n 0%bin_with_zero.
  {
    intros n.
    match &n with | Zero | Positive p end; simpl in |- *; quod idem est.
  }
  lemma balance
    : (unsigned_value (Int8.introduction (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0))
        + (modulus * Bit.to_bin_with_zero &x7 + modulus * Bit.to_bin_with_zero &x7 + 0)
        = (unsigned_value
            (Int8.introduction (Byte.introduction &x7 &x7 &x6 &x5 &x4 &x3 &x2 &x1))
          + unsigned_value
              (Int8.introduction (Byte.introduction &x7 &x7 &x6 &x5 &x4 &x3 &x2 &x1))
          + Bit.to_bin_with_zero &x0)
          + modulus * Bit.to_bin_with_zero &x7)%bin_with_zero.
  {
    match (BinWithZero.addition.identity
            (modulus * Bit.to_bin_with_zero &x7
              + modulus * Bit.to_bin_with_zero &x7)%bin_with_zero)
    with | _ unit end.
    leibniz
      &unit,
      (&doubled
        (unsigned_value
          (Int8.introduction (Byte.introduction &x7 &x7 &x6 &x5 &x4 &x3 &x2 &x1)))),
      &split,
      (BinWithZero.multiplication.commutativity
        (Bit.to_bin_with_zero &x7) modulus),
      (BinWithZero.addition.commutativity
        (modulus * Bit.to_bin_with_zero &x7)%bin_with_zero
        (unsigned_value
          (Int8.introduction (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)))),
      (BinWithZero.addition.associativity
        (unsigned_value
          (Int8.introduction (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)))
        (modulus * Bit.to_bin_with_zero &x7)%bin_with_zero
        (modulus * Bit.to_bin_with_zero &x7)%bin_with_zero)
      in |- *.
    quod idem est.
  }
  leibniz &shifted in |- *.
  simpl to_bin, sign_bit in |- *.
  leibniz
    (&twice
      (Bin.bin_with_zero_difference
        (unsigned_value
          (Int8.introduction (Byte.introduction &x7 &x7 &x6 &x5 &x4 &x3 &x2 &x1)))
        (modulus * Bit.to_bin_with_zero &x7)%bin_with_zero)),
    (Bin.difference.additivity
      (unsigned_value
        (Int8.introduction (Byte.introduction &x7 &x7 &x6 &x5 &x4 &x3 &x2 &x1)))
      (modulus * Bit.to_bin_with_zero &x7)%bin_with_zero
      (unsigned_value
        (Int8.introduction (Byte.introduction &x7 &x7 &x6 &x5 &x4 &x3 &x2 &x1)))
      (modulus * Bit.to_bin_with_zero &x7)%bin_with_zero),
    (&embedding (Bit.to_bin_with_zero &x0)),
    (Bin.difference.additivity
      (unsigned_value
        (Int8.introduction (Byte.introduction &x7 &x7 &x6 &x5 &x4 &x3 &x2 &x1))
        + unsigned_value
            (Int8.introduction
              (Byte.introduction &x7 &x7 &x6 &x5 &x4 &x3 &x2 &x1)))%bin_with_zero
      (modulus * Bit.to_bin_with_zero &x7
        + modulus * Bit.to_bin_with_zero &x7)%bin_with_zero
      (Bit.to_bin_with_zero &x0) 0%bin_with_zero)
    in |- *.
  ipso (Bin.difference.invariance &balance).
Qed.

End right. (* conversion.right *)

Module bin. (* conversion.bin *)

(* conversion.bin.nonnegative *)
Lemma nonnegative
  : forall (n : BinWithZero) . from_bin (Bin.from_bin_with_zero n) = from_bin_with_zero n.
Proof.
  intros n.
  lemma nothing : - from_bin_with_zero BinWithZero.Zero = Zero.
  {
    simpl from_bin_with_zero in |- *.
    match (addition.inverse Zero) with | _ right end.
    match (addition.identity (- Zero)) with | left _ end.
    ipso (trans (symm &left), &right).
  }
  match &n with | Zero | Positive p end.
  - simpl Bin.from_bin_with_zero, from_bin in |- *.
    simpl Bin.ramp, Bin.negate in |- *.
    leibniz &nothing in |- *.
    match (addition.identity (from_bin_with_zero BinWithZero.Zero)) with | _ right end.
    ipso &right.
  - simpl Bin.from_bin_with_zero, from_bin in |- *.
    simpl Bin.ramp, Bin.negate in |- *.
    leibniz &nothing in |- *.
    match (addition.identity (from_bin_with_zero (BinWithZero.Positive &p))) with
    | _ right end.
    ipso &right.
Qed.

(* conversion.bin.negative *)
Lemma negative : forall (p : BinBase) . from_bin (Bin.Negative p) = - from_bin_base p.
Proof.
  intros p.
  simpl from_bin in |- *.
  simpl Bin.ramp, Bin.negate in |- *.
  lemma nothing : from_bin_with_zero BinWithZero.Zero = Zero.
  {
    simpl from_bin_with_zero in |- *.
    quod idem est.
  }
  lemma unfolded : from_bin_with_zero (BinWithZero.Positive &p) = from_bin_base &p.
  {
    simpl from_bin_with_zero in |- *.
    quod idem est.
  }
  leibniz &nothing, &unfolded in |- *.
  match (addition.identity (- from_bin_base &p)) with | left _ end.
  ipso &left.
Qed.

End bin. (* conversion.bin *)

Module boundedness. (* conversion.boundedness *)

(* conversion.boundedness.positive *)
Theorem positive
  : forall (x : Int8) (p : BinBase) . to_bin x = Bin.Positive p -> (p < 10000000)%bin_with_zero.
Proof.
  intros x p e.
  simpl to_bin in &e.
  match (sign_bit &x) with | Zero | One end |- s.
  - lemma scaled : (modulus * Bit.to_bin_with_zero 0 = 0)%bin_with_zero.
    {
      simpl modulus, Bit.to_bin_with_zero in |- *.
      simpl in |- *.
      quod idem est.
    }
    leibniz &scaled in &e.
    let proof small := reinterpretation.sign.clear &x &s.
    match (unsigned_value &x) with | Zero | Positive q end |- f.
    + simpl Bin.bin_with_zero_difference in &e.
      ex &e quodlibet.
    + simpl Bin.bin_with_zero_difference in &e.
      let proof g := congru Bin.ramp, &e.
      simpl Bin.ramp in &g.
      leibniz &g in &small.
      ipso &small.
  - lemma whole : (modulus * Bit.to_bin_with_zero 1 = modulus)%bin_with_zero.
    {
      simpl modulus in |- *.
      simpl in |- *.
      quod idem est.
    }
    leibniz &whole in &e.
    let proof sp := Bin.difference.specification (unsigned_value &x) modulus.
    leibniz &e in &sp.
    simpl Bin.ramp, Bin.negate in &sp.
    match (BinWithZero.addition.identity (unsigned_value &x)) with | left _ end.
    leibniz &left in &sp.
    let proof bound := reinterpretation.boundedness &x.
    leibniz <- &sp in &bound.
    ex
      (BinWithZero.order.strict.irreflexivity _
        (Comparable.order.mixed.left.transitivity
          (BinWithZero.addition.right.order.extensivity p modulus) &bound))
      quodlibet.
Qed.

(* conversion.boundedness.negative *)
Theorem negative
  : forall (x : Int8) (p : BinBase) . to_bin x = Bin.Negative p -> (p <= 10000000)%bin_with_zero.
Proof.
  intros x p e.
  simpl to_bin in &e.
  match (sign_bit &x) with | Zero | One end |- s.
  - lemma scaled : (modulus * Bit.to_bin_with_zero 0 = 0)%bin_with_zero.
    {
      simpl modulus, Bit.to_bin_with_zero in |- *.
      simpl in |- *.
      quod idem est.
    }
    leibniz &scaled in &e.
    match (unsigned_value &x) with | Zero | Positive q end |- f.
    + simpl Bin.bin_with_zero_difference in &e.
      ex &e quodlibet.
    + simpl Bin.bin_with_zero_difference in &e.
      ex &e quodlibet.
  - lemma whole : (modulus * Bit.to_bin_with_zero 1 = modulus)%bin_with_zero.
    {
      simpl modulus in |- *.
      simpl in |- *.
      quod idem est.
    }
    leibniz &whole in &e.
    let proof big := reinterpretation.sign.set &x &s.
    let proof sp := Bin.difference.specification (unsigned_value &x) modulus.
    leibniz &e in &sp.
    simpl Bin.ramp, Bin.negate in &sp.
    match (BinWithZero.addition.identity modulus) with | left _ end.
    leibniz &left in &sp.
    match (Comparable.order.strict.trichotomy (BinWithZero.Positive p) 10000000%bin_with_zero) with
    | below | rest end.
    + simpl BinWithZero.LessOrEqual in |- *.
      ipso (disjoin _, &below).
    + match &rest with | same | above end.
      * simpl BinWithZero.LessOrEqual in |- *.
        ipso (disjoin &same, _).
      * lemma double : (10000000 + 10000000 = modulus)%bin_with_zero.
        {
          simpl modulus, BinWithZero.add in |- *.
          simpl BinBase.add in |- *.
          simpl in |- *.
          quod idem est.
        }
        let proof total := BinWithZero.addition.order.strict.monotonicity _ _ _ _ &big &above.
        leibniz
          &double,
          (BinWithZero.addition.commutativity (unsigned_value &x) p),
          <- &sp
          in &total.
        ex (BinWithZero.order.strict.irreflexivity _ &total) quodlibet.
Qed.

End boundedness. (* conversion.boundedness *)

Module retraction. (* conversion.retraction *)

(* conversion.retraction.nonnegative *)
Theorem nonnegative
  : forall (n : BinWithZero) .
      (n < 10000000)%bin_with_zero
      -> to_bin (from_bin (Bin.from_bin_with_zero n)) = Bin.from_bin_with_zero n.
Proof.
  intros n h.
  lemma half : (10000000 < modulus)%bin_with_zero.
  {
    simpl BinWithZero.LessThan in |- *.
    exists 10000000%bin_base.
    simpl modulus, BinWithZero.add in |- *.
    simpl BinBase.add in |- *.
    simpl in |- *.
    quod idem est.
  }
  lemma value : unsigned_value (from_bin_with_zero &n) = &n.
  {
    leibniz
      (reinterpretation.reduction &n),
      (BinWithZero.modulo.identity &n modulus (BinWithZero.order.strict.transitivity &h &half))
      in |- *.
    quod idem est.
  }
  lemma sign : sign_bit (from_bin_with_zero &n) = 0%bit.
  {
    match (sign_bit (from_bin_with_zero &n)) with | Zero | One end |- s.
    - quod idem est.
    - let proof big := reinterpretation.sign.set _ &s.
      leibniz &value in &big.
      ex
        (BinWithZero.order.strict.irreflexivity _
          (Comparable.order.mixed.left.transitivity &big &h))
        quodlibet.
  }
  leibniz (conversion.bin.nonnegative &n) in |- *.
  simpl to_bin in |- *.
  leibniz &value, &sign in |- *.
  match &n with | Zero | Positive p end.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    quod idem est.
Qed.

(* conversion.retraction.negative *)
Theorem negative
  : forall (p : BinBase) .
      (p <= 10000000)%bin_with_zero -> to_bin (from_bin (Bin.Negative p)) = Bin.Negative p.
Proof.
  intros p h.
  leibniz (conversion.bin.negative &p) in |- *.
  lemma half : (10000000 < modulus)%bin_with_zero.
  {
    simpl BinWithZero.LessThan in |- *.
    exists 10000000%bin_base.
    simpl modulus, BinWithZero.add in |- *.
    simpl BinBase.add in |- *.
    simpl in |- *.
    quod idem est.
  }
  lemma below : (p < modulus)%bin_with_zero.
  {
    match &h with | same | smaller end.
    - leibniz &same in |- *.
      ipso &half.
    - ipso (BinWithZero.order.strict.transitivity &smaller &half).
  }
  let proof pbelow := &below.
  match &below with | k ek end.
  lemma kbelow : (k < modulus)%bin_with_zero.
  {
    simpl BinWithZero.LessThan in |- *.
    exists &p.
    leibniz (BinWithZero.addition.commutativity k p) in |- *.
    ipso &ek.
  }
  lemma valuek : unsigned_value (from_bin_base &k) = k.
  {
    lemma through : from_bin_base &k = from_bin_with_zero k.
    {
      simpl from_bin_with_zero in |- *.
      quod idem est.
    }
    leibniz
      &through, (reinterpretation.reduction k), (BinWithZero.modulo.identity k modulus &kbelow)
      in |- *.
    quod idem est.
  }
  lemma valuep : unsigned_value (from_bin_base &p) = p.
  {
    lemma through : from_bin_base &p = from_bin_with_zero p.
    {
      simpl from_bin_with_zero in |- *.
      quod idem est.
    }
    leibniz
      &through, (reinterpretation.reduction p), (BinWithZero.modulo.identity p modulus &pbelow)
      in |- *.
    quod idem est.
  }
  lemma sum : from_bin_base &k + from_bin_base &p = Zero.
  {
    lemma facto : unsigned_value (from_bin_base &k + from_bin_base &p) = unsigned_value Zero.
    {
      leibniz
        (reinterpretation.addition (from_bin_base &k) (from_bin_base &p)),
        &valuek, &valuep, reinterpretation.zero,
        (BinWithZero.addition.commutativity k p),
        &ek
        in |- *.
      simpl modulus in |- *.
      simpl BinWithZero.modulo, BinWithZero.div in |- *.
      simpl in |- *.
      quod idem est.
    }
    ipso (reinterpretation.injectivity &facto).
  }
  lemma complement : - from_bin_base &p = from_bin_base &k.
  {
    match (addition.identity (- from_bin_base &p)) with | left _ end.
    match (addition.inverse (from_bin_base &p)) with | _ right end.
    match (addition.identity (from_bin_base &k)) with | _ right' end.
    leibniz
      <- &left,
      <- &sum,
      (addition.associativity (from_bin_base &k) (from_bin_base &p) (- from_bin_base &p)),
      &right,
      &right'
      in |- *.
    quod idem est.
  }
  leibniz &complement in |- *.
  lemma double : (10000000 + 10000000 = modulus)%bin_with_zero.
  {
    simpl modulus, BinWithZero.add in |- *.
    simpl BinBase.add in |- *.
    simpl in |- *.
    quod idem est.
  }
  lemma sign : sign_bit (from_bin_base &k) = 1%bit.
  {
    match (sign_bit (from_bin_base &k)) with | Zero | One end |- s.
    - let proof small := reinterpretation.sign.clear _ &s.
      leibniz &valuek in &small.
      let proof total := BinWithZero.addition.order.strict.monotonicity _ _ _ _ &h &small.
      leibniz &ek, &double in &total.
      ex (BinWithZero.order.strict.irreflexivity _ &total) quodlibet.
    - quod idem est.
  }
  lemma whole : (modulus * Bit.to_bin_with_zero 1 = modulus)%bin_with_zero.
  {
    simpl modulus in |- *.
    simpl in |- *.
    quod idem est.
  }
  lemma swap : (k + p = 0 + modulus)%bin_with_zero.
  {
    match (BinWithZero.addition.identity modulus) with | left _ end.
    leibniz (BinWithZero.addition.commutativity k p), &ek, &left in |- *.
    quod idem est.
  }
  simpl to_bin in |- *.
  leibniz &valuek, &sign, &whole, (Bin.difference.invariance &swap) in |- *.
  simpl Bin.bin_with_zero_difference in |- *.
  quod idem est.
Qed.

End retraction. (* conversion.retraction *)

Module division. (* conversion.division *)

(* conversion.division.positive *)
Theorem positive
  : forall (x : Int8) (y : Int8) (d : BinBase) .
      to_bin y = Bin.Positive d -> Option.map to_bin (x /. y)%int8 = Some (x /. d)%b.
Proof.
  intros x y d e.
  lemma origin : to_bin (from_bin 0%b) = 0%b.
  {
    lemma nothing : (0 < 10000000)%bin_with_zero.
    {
      simpl BinWithZero.LessThan in |- *.
      exists 10000000%bin_base.
      simpl BinWithZero.add in |- *.
      quod idem est.
    }
    let proof r := conversion.retraction.nonnegative 0%bin_with_zero &nothing.
    simpl Bin.from_bin_with_zero in &r.
    ipso &r.
  }
  lemma fits : to_bin (from_bin (x /. &d)%b) = (x /. &d)%b.
  {
    match (to_bin &x) with | Negative p | Zero | Positive p end |- t.
    - let proof r := conversion.boundedness.negative &x &p &t.
      let proof b := BinWithZero.division.quotient.boundedness p &d.
      simpl Bin.divide in |- *.
      match ((p /. &d)%bin_with_zero) with | Zero | Positive q end |- f.
      + simpl Bin.from_bin_with_zero, Bin.negate in |- *.
        ipso &origin.
      + simpl Bin.from_bin_with_zero, Bin.negate in |- *.
        lemma bounded : (q <= 10000000)%bin_with_zero.
        {
          match &r with | same | smaller end.
          - leibniz &same in &b.
            ipso &b.
          - simpl BinWithZero.LessOrEqual in |- *.
            ipso (disjoin _, (Comparable.order.mixed.left.transitivity &b &smaller)).
        }
        ipso (conversion.retraction.negative &q &bounded).
    - simpl Bin.divide in |- *.
      ipso &origin.
    - let proof r := conversion.boundedness.positive &x &p &t.
      let proof b := BinWithZero.division.quotient.boundedness p &d.
      simpl Bin.divide in |- *.
      ipso
        (conversion.retraction.nonnegative (p /. &d)%bin_with_zero
          (Comparable.order.mixed.left.transitivity &b &r)).
  }
  simpl divide in |- *.
  leibniz &e in |- *.
  simpl Option.map in |- *.
  leibniz &fits in |- *.
  quod idem est.
Qed.

(* conversion.division.negative *)
Theorem negative
  : forall (x : Int8) (y : Int8) (d : BinBase) .
      to_bin y = Bin.Negative d
      -> ~ (to_bin x = (-10000000)%b /\ d = BinBase.One)
      -> Option.map to_bin (x /. y)%int8 = Some (Bin.negate (x /. d)%b).
Proof.
  intros x y d e h.
  lemma origin : to_bin (from_bin 0%b) = 0%b.
  {
    lemma nothing : (0 < 10000000)%bin_with_zero.
    {
      simpl BinWithZero.LessThan in |- *.
      exists 10000000%bin_base.
      simpl BinWithZero.add in |- *.
      quod idem est.
    }
    let proof r := conversion.retraction.nonnegative 0%bin_with_zero &nothing.
    simpl Bin.from_bin_with_zero in &r.
    ipso &r.
  }
  lemma fits : to_bin (from_bin (Bin.negate (x /. &d)%b)) = Bin.negate (x /. &d)%b.
  {
    match (to_bin &x) with | Negative p | Zero | Positive p end |- t.
    - let proof r := conversion.boundedness.negative &x &p &t.
      lemma below : ((p /. &d) < 10000000)%bin_with_zero.
      {
        match &r with | same | smaller end.
        - match &d with | One | b0 d' | b1 d' end.
          + let proof g := congru BinWithZero.to_bin_base, &same.
            simpl BinWithZero.to_bin_base in &g.
            let proof k := Option.some.injectivity &g.
            leibniz &k in &h.
            ex
              (&h
                (conjoin
                  (refl (-10000000)%b),
                  (refl BinBase.One)))
              quodlibet.
          + lemma differ : ~ (BinBase.b0 &d' = BinBase.One).
            {
              intro k.
              ex &k quodlibet.
            }
            leibniz <- &same in |- *.
            ipso (BinWithZero.division.quotient.strict.boundedness &p (BinBase.b0 &d') &differ).
          + lemma differ : ~ (BinBase.b1 &d' = BinBase.One).
            {
              intro k.
              ex &k quodlibet.
            }
            leibniz <- &same in |- *.
            ipso (BinWithZero.division.quotient.strict.boundedness &p (BinBase.b1 &d') &differ).
        - ipso
            (Comparable.order.mixed.left.transitivity
              (BinWithZero.division.quotient.boundedness p &d) &smaller).
      }
      simpl Bin.divide in |- *.
      leibniz (Bin.negation.involution (Bin.from_bin_with_zero (p /. &d)%bin_with_zero)) in |- *.
      ipso (conversion.retraction.nonnegative (p /. &d)%bin_with_zero &below).
    - simpl Bin.divide, Bin.negate in |- *.
      ipso &origin.
    - let proof r := conversion.boundedness.positive &x &p &t.
      let proof b := BinWithZero.division.quotient.boundedness p &d.
      simpl Bin.divide in |- *.
      match ((p /. &d)%bin_with_zero) with | Zero | Positive q end |- f.
      + simpl Bin.from_bin_with_zero, Bin.negate in |- *.
        ipso &origin.
      + simpl Bin.from_bin_with_zero, Bin.negate in |- *.
        lemma bounded : (q <= 10000000)%bin_with_zero.
        {
          simpl BinWithZero.LessOrEqual in |- *.
          ipso (disjoin _, (Comparable.order.mixed.left.transitivity &b &r)).
        }
        ipso (conversion.retraction.negative &q &bounded).
  }
  simpl divide in |- *.
  leibniz &e in |- *.
  simpl Option.map in |- *.
  leibniz &fits in |- *.
  quod idem est.
Qed.

End division. (* conversion.division *)

Module byte. (* conversion.byte *)

(* conversion.byte.retraction *)
Theorem retraction : forall (b : Byte) . to_byte (from_byte b) = b.
Proof.
  intros b.
  simpl to_byte, from_byte in |- *.
  quod idem est.
Qed.

(* conversion.byte.section *)
Theorem section : forall (x : Int8) . from_byte (to_byte x) = x.
Proof.
  intros x.
  match &x with | introduction b end.
  simpl to_byte, from_byte in |- *.
  quod idem est.
Qed.

End byte. (* conversion.byte *)

End conversion. (* conversion *)

(* [Int8] as a [Signed.Width]: its operations, the laws above, and its
 * constants, 128, 256 and 384. The facts about fixed values are closed
 * computations, checked by the kernel.
 *)
Module Width <: Signed.Width.

Definition T := T.
Definition Zero := Zero.
Definition One := One.
Definition Min := Min.
Definition Max := Max.
Definition to_bin := to_bin.
Definition from_bin := from_bin.
Definition from_bin_with_zero := from_bin_with_zero.
Definition unsigned_value := unsigned_value.
Definition sign_bit := sign_bit.
Definition add := add.
Definition sub := sub.
Definition negate := negate.
Definition LessThan := LessThan.
Definition LessOrEqual := LessOrEqual.
Definition add_with_overflow := add_with_overflow.
Definition sub_with_overflow := sub_with_overflow.
Definition compare := compare.
Definition half := 10000000%bin_base.
Definition modulus := modulus.
Definition beyond := 110000000%bin_base.

Module order. (* Width.order *)

Module strict. (* Width.order.strict *)

Theorem specification : forall (x : T) (y : T) . LessThan x y <-> (to_bin x < to_bin y)%b.
Proof.
  intros x y.
  divide et impera.
  - intro h.
    ipso &h.
  - intro h.
    ipso &h.
Qed.

End strict. (* Width.order.strict *)

Theorem specification : forall (x : T) (y : T) . LessOrEqual x y <-> x = y \/ LessThan x y.
Proof.
  intros x y.
  divide et impera.
  - intro h.
    ipso &h.
  - intro h.
    ipso &h.
Qed.

End order. (* Width.order *)

Module conversion. (* Width.conversion *)

Definition section := Int8.conversion.section.

Theorem comparison
  : forall (x : T) (y : T) . compare x y = Bin.compare (to_bin x) (to_bin y).
Proof.
  intros x y.
  ipso (refl (compare &x &y)).
Qed.

Definition addition := Int8.conversion.addition.
Definition difference := Int8.conversion.difference.

Module forward. (* Width.conversion.forward *)

Theorem specification
  : forall (x : T) .
      to_bin x
      = Bin.bin_with_zero_difference (unsigned_value x)
          (BinWithZero.Positive modulus * Bit.to_bin_with_zero (sign_bit x))%bin_with_zero.
Proof.
  intro x.
  ipso (refl (to_bin &x)).
Qed.

End forward. (* Width.conversion.forward *)

Module backward. (* Width.conversion.backward *)

Theorem specification
  : forall (z : Bin) .
      from_bin z
      = add (from_bin_with_zero (Bin.ramp z))
          (negate (from_bin_with_zero (Bin.ramp (Bin.negate z)))).
Proof.
  intro z.
  ipso (refl (from_bin &z)).
Qed.

End backward. (* Width.conversion.backward *)

Module boundedness. (* Width.conversion.boundedness *)

Definition positive := Int8.conversion.boundedness.positive.
Definition negative := Int8.conversion.boundedness.negative.

End boundedness. (* Width.conversion.boundedness *)

Module retraction. (* Width.conversion.retraction *)

Definition nonnegative := Int8.conversion.retraction.nonnegative.
Definition negative := Int8.conversion.retraction.negative.

End retraction. (* Width.conversion.retraction *)

End conversion. (* Width.conversion *)

Module reinterpretation. (* Width.reinterpretation *)

Definition boundedness := Int8.reinterpretation.boundedness.

Module reduction. (* Width.reinterpretation.reduction *)

Definition additivity := Int8.reinterpretation.reduction.additivity.

Theorem zero : from_bin_with_zero BinWithZero.Zero = Zero.
Proof.
  ipso (refl Zero).
Qed.

End reduction. (* Width.reinterpretation.reduction *)

End reinterpretation. (* Width.reinterpretation *)

Module addition. (* Width.addition *)

Definition associativity := Int8.addition.associativity.
Definition commutativity := Int8.addition.commutativity.
Definition identity := Int8.addition.identity.
Definition inverse := Int8.addition.inverse.

End addition. (* Width.addition *)

Module subtraction. (* Width.subtraction *)

Definition specification := Int8.subtraction.specification.

End subtraction. (* Width.subtraction *)

Module flag. (* Width.flag *)

Module addition. (* Width.flag.addition *)

Theorem specification
  : forall (x : T) (y : T) .
      (pi_1 (add_with_overflow x y))%product
      = Bit.and (Bit.flip (Bit.xor (sign_bit x) (sign_bit y)))
          (Bit.xor (sign_bit (add x y)) (sign_bit x)).
Proof.
  intros x y.
  ipso (refl ((pi_1 (add_with_overflow &x &y))%product)).
Qed.

End addition. (* Width.flag.addition *)

Module subtraction. (* Width.flag.subtraction *)

Theorem specification
  : forall (x : T) (y : T) .
      (pi_1 (sub_with_overflow x y))%product
      = Bit.and (Bit.xor (sign_bit x) (sign_bit y)) (Bit.xor (sign_bit (sub x y)) (sign_bit x)).
Proof.
  intros x y.
  ipso (refl ((pi_1 (sub_with_overflow &x &y))%product)).
Qed.

End subtraction. (* Width.flag.subtraction *)

End flag. (* Width.flag *)

Module minimum. (* Width.minimum *)

Theorem specification : to_bin Min = Bin.Negative half.
Proof.
  ipso (refl (Bin.Negative half)).
Qed.

Theorem negation : negate Min = Min.
Proof.
  ipso (refl Min).
Qed.

End minimum. (* Width.minimum *)

Module maximum. (* Width.maximum *)

Theorem specification : (to_bin Max + 1 = Bin.Positive half)%b.
Proof.
  ipso (refl (Bin.Positive half)).
Qed.

Theorem positivity : (0 < to_bin Max)%b.
Proof.
  simpl Bin.LessThan in |- *.
  exists 1111111%bin_base.
  ipso (refl (to_bin Max)).
Qed.

End maximum. (* Width.maximum *)

Module one. (* Width.one *)

Theorem specification : to_bin One = 1%b.
Proof.
  ipso (refl 1%b).
Qed.

End one. (* Width.one *)

Module modulus. (* Width.modulus *)

Theorem specification : (Bin.Positive modulus = Bin.Positive half + Bin.Positive half)%b.
Proof.
  ipso (refl (Bin.Positive modulus)).
Qed.

Theorem wrapping : from_bin (Bin.Positive modulus) = Zero.
Proof.
  ipso (refl Zero).
Qed.

End modulus. (* Width.modulus *)

Module beyond. (* Width.beyond *)

Theorem specification : (Bin.Positive beyond = Bin.Positive modulus + Bin.Positive half)%b.
Proof.
  ipso (refl (Bin.Positive beyond)).
Qed.

End beyond. (* Width.beyond *)

End Width.

Include Signed.Laws Width.

Instance comparable
  : Comparable compare (<) :=
  {| Comparable.transitivity := @order.strict.transitivity
  ; Comparable.specification := comparison.specification
  ; Comparable.antisymmetry := comparison.antisymmetry |}.

End Int8. (* Int8 *)

Abbreviation Int8 := Int8.T.

Export (notations) Int8.

(* A number of the type is written in decimal or hexadecimal under its
 * scope, [100%int8], [(-100)%int8] or [0x7F%int8], and a closed one prints
 * in decimal.
 *)
Number Notation Int8.T Int8.from_numeral Int8.to_numeral
  : jw_int8_scope.

(* Where an [Int8] is expected, a literal or a notation reads in this scope
 * without its [%int8].
 *)
Bind Scope jw_int8_scope with Int8.T.

(* An [Int8] stands wherever a [Bin] is expected, read as its value in two's
 * complement, and wherever an [Integer] is, through that value; each
 * conversion is printed where it happened.
 *)
Coercion Int8.to_bin : Int8 >-> Bin.
Add Printing Coercion Int8.to_bin.
Coercion Int8.to_integer : Int8 >-> Integer.
Add Printing Coercion Int8.to_integer.

(* Declared inside [Module Int8]; an instance declared there is dropped at
 * the module's [End], so it is announced again here.
 *)
Existing Instance Int8.comparable.

Instance Int8_add_monoid
  : Monoid Int8.add Int8.Zero :=
  {| Monoid.semigroup :=
      {| Semigroup.associativity := Int8.addition.associativity |}
  ; Monoid.identity := Int8.addition.identity |}.

Instance Int8_mul_monoid
  : Monoid Int8.mul Int8.One :=
  {| Monoid.semigroup :=
      {| Semigroup.associativity := Int8.multiplication.associativity |}
  ; Monoid.identity := Int8.multiplication.identity |}.

Instance Int8_add_commutative
  : Commutative Int8.add :=
  {| Commutative.commutativity := Int8.addition.commutativity |}.

Instance Int8_mul_commutative
  : Commutative Int8.mul :=
  {| Commutative.commutativity := Int8.multiplication.commutativity |}.

Instance Int8_add_group
  : Group Int8.add Int8.Zero Int8.negate :=
  {| Group.monoid := Int8_add_monoid
  ; Group.inverse := Int8.addition.inverse |}.

Instance Int8_add_abelian_group
  : AbelianGroup Int8.add Int8.Zero Int8.negate :=
  {| AbelianGroup.group := Int8_add_group
  ; AbelianGroup.commutative := Int8_add_commutative |}.

Instance Int8_ring
  : Ring Int8.add Int8.Zero Int8.negate Int8.mul Int8.One :=
  {| Ring.abelian_group := Int8_add_abelian_group
  ; Ring.monoid := Int8_mul_monoid
  ; Ring.distributivity := Int8.multiplication.distributivity.over.addition |}.
