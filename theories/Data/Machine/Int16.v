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
From JW Require Import Data.Machine.Endian.
From JW Require Import Data.Machine.HWord.
From JW Require Import Data.Machine.Modular.
From JW Require Import Data.Machine.Signed.
From JW Require Import Data.Number.Binary.SignedBin.
From JW Require Import Data.Number.Binary.BinBase.
From JW Require Import Data.Number.Binary.Bin0.
From JW Require Import Data.Number.Integer.
From JW Require Import Data.Number.Nat.
From JW Require Import Data.Number.Nat0.
From JW Require Import Data.Number.Numeral.
From JW Require Import Data.Option.
From JW Require Import Data.Product.
From JW Require Import Tactics.Equation.
From JW Require Import Tactics.Modus.
From JW Require Import Tactics.Witness.

(* A signed integer of sixteen bits: two [Byte]s read in two's complement, from
 * -32768 (-2^15) to 32767 (2^15 - 1), its arithmetic wrapping modulo 65536
 * (2^16). In this file [10000000000000000] is 2^16, [1000000000000000] is 2^15
 * and [111111111111111] is 2^15 - 1, written in binary digits.
 *)

Module Int16. (* Int16 *)

Inductive T : Type :=
  | introduction : Byte -> Byte -> T.

Abbreviation Int16 := T.

(* The number of values, 65536 (2^16), the arithmetic wrapping modulo it. *)
(* [BinBase] *)
Definition modulus := 10000000000000000%bin_base.

(* [x] laid out as a [HWord] in the order [e] names. *)
(* [Endian -> Int16 -> HWord] *)
Definition to_hword := fun (e : Endian) (x : Int16) .
  match x with
  | Int16.introduction b1 b0 => HWord.make e b0 b1
  end.

(* The value of the bytes of [w], whatever the order they are laid out in. *)
(* [HWord -> Int16] *)
Definition from_hword := fun (w : HWord) . Int16.introduction (HWord.high w) (HWord.low w).

(* The bits read as a number in base two, the most significant first, from 0 to
 * 65535: the value of the bit pattern, through which the arithmetic is proved
 * and from which [to_b_signed] takes the signed value; [10] is two in binary digits.
 *)
(* [Int16 -> Bin0] *)
Definition unsigned_value := fun (x : Int16) .
  match x with
  | Int16.introduction (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8)
      (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
      (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (
        10 * Bit.to_b0 x15 + Bit.to_b0 x14) + Bit.to_b0 x13)
        + Bit.to_b0 x12) + Bit.to_b0 x11) + Bit.to_b0 x10)
        + Bit.to_b0 x9) + Bit.to_b0 x8) + Bit.to_b0 x7)
        + Bit.to_b0 x6) + Bit.to_b0 x5) + Bit.to_b0 x4)
        + Bit.to_b0 x3) + Bit.to_b0 x2) + Bit.to_b0 x1)
        + Bit.to_b0 x0)%b0
  end.

(* The top bit, [1] for a negative value. *)
(* [Int16 -> Bit] *)
Definition sign_bit := fun (x : Int16) .
  match x with
  | Int16.introduction (Byte.introduction x15 _ _ _ _ _ _ _) _ => x15
  end.

(* The value in two's complement: the unsigned value, less 65536 when the sign
 * bit is set.
 *)
(* [Int16 -> SignedBin] *)
Definition to_b_signed := fun (x : Int16) .
  SignedBin.b0_difference
    (unsigned_value x) (modulus * Bit.to_b0 (sign_bit x))%b0.

(* From here to the end of the module an [Int16] stands where a [SignedBin] is expected,
 * read as its value; the conversion is printed.
 *)
Local Coercion to_b_signed : T >-> SignedBin.
Add Printing Coercion to_b_signed.

(* The value in [Integer], through [to_b_signed]; [Integer] is unary, so it is for
 * stating and proving, and computing goes through [to_b_signed].
 *)
(* [Int16 -> Integer] *)
Definition to_integer := fun (x : Int16) . SignedBin.to_integer (to_b_signed x).

(* [Int16] *)
Definition Zero := Int16.introduction Byte.Zero Byte.Zero.

(* [Int16] *)
Definition One :=
  Int16.introduction
    Byte.Zero
    (Byte.introduction
      0 0 0 0 0 0 0 1).

(* The least value, -32768: only the sign bit set. *)
(* [Int16] *)
Definition Min :=
  Int16.introduction
    (Byte.introduction
      1 0 0 0 0 0 0 0)
    Byte.Zero.

(* The greatest value, 32767: every bit but the sign bit set. *)
(* [Int16] *)
Definition Max :=
  Int16.introduction
    (Byte.introduction
      0 1 1 1 1 1 1 1)
    (Byte.introduction
      1 1 1 1 1 1 1 1).

(* [k] places toward the most significant end, a 0 coming in at the
 * other; one place first, then [k - 1].
 *)
(* [Int16 -> Nat -> Int16] *)
Fixpoint shift_left_nat (x : Int16) (k : Nat) : Int16 :=
  let y :=
    match x with
    | Int16.introduction (Byte.introduction _ x14 x13 x12 x11 x10 x9 x8)
        (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
        Int16.introduction (Byte.introduction x14 x13 x12 x11 x10 x9 x8 x7)
          (Byte.introduction x6 x5 x4 x3 x2 x1 x0 0)
    end in
  match k with
  | Nat.One          => y
  | Nat.Successor k' => shift_left_nat y k'
  end.

(* [Int16 -> Nat0 -> Int16] *)
Definition shift_left := fun (x : Int16) (k : Nat0) .
  match k with
  | Nat0.Zero       => x
  | Nat0.Positive n => shift_left_nat x n
  end.

(* [k] places toward the least significant end, the sign bit copied in at
 * the other; one place first, then [k - 1].
 *)
(* [Int16 -> Nat -> Int16] *)
Fixpoint shift_right_nat (x : Int16) (k : Nat) : Int16 :=
  let y :=
    match x with
    | Int16.introduction (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8)
        (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
        Int16.introduction (Byte.introduction x15 x15 x14 x13 x12 x11 x10 x9)
          (Byte.introduction x8 x7 x6 x5 x4 x3 x2 x1)
    end in
  match k with
  | Nat.One          => y
  | Nat.Successor k' => shift_right_nat y k'
  end.

(* [Int16 -> Nat0 -> Int16] *)
Definition shift_right := fun (x : Int16) (k : Nat0) .
  match k with
  | Nat0.Zero       => x
  | Nat0.Positive n => shift_right_nat x n
  end.

(* [x] with [b] written after its lowest bit, the highest bit dropped. *)
(* [Bit -> Int16 -> Int16] *)
Definition append_bit := fun (b : Bit) (x : Int16) .
  match x with
  | Int16.introduction (Byte.introduction _ x14 x13 x12 x11 x10 x9 x8)
      (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
      Int16.introduction (Byte.introduction x14 x13 x12 x11 x10 x9 x8 x7)
        (Byte.introduction x6 x5 x4 x3 x2 x1 x0 b)
  end.

(* The carry out and the sum of [carry + x + y], the carry rippling up from
 * the least significant place.
 *)
(* [Bit -> Int16 -> Int16 -> Product Bit Int16] *)
Definition add_with_carry := fun (carry : Bit) (x : Int16) (y : Int16) .
  match x with
  | Int16.introduction (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8)
      (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
      match y with
      | Int16.introduction (Byte.introduction y15 y14 y13 y12 y11 y10 y9 y8)
          (Byte.introduction y7 y6 y5 y4 y3 y2 y1 y0) =>
          let r0 := Bit.add_with_carry carry x0 y0 in
          let r1 := Bit.add_with_carry (pi_1 r0) x1 y1 in
          let r2 := Bit.add_with_carry (pi_1 r1) x2 y2 in
          let r3 := Bit.add_with_carry (pi_1 r2) x3 y3 in
          let r4 := Bit.add_with_carry (pi_1 r3) x4 y4 in
          let r5 := Bit.add_with_carry (pi_1 r4) x5 y5 in
          let r6 := Bit.add_with_carry (pi_1 r5) x6 y6 in
          let r7 := Bit.add_with_carry (pi_1 r6) x7 y7 in
          let r8 := Bit.add_with_carry (pi_1 r7) x8 y8 in
          let r9 := Bit.add_with_carry (pi_1 r8) x9 y9 in
          let r10 := Bit.add_with_carry (pi_1 r9) x10 y10 in
          let r11 := Bit.add_with_carry (pi_1 r10) x11 y11 in
          let r12 := Bit.add_with_carry (pi_1 r11) x12 y12 in
          let r13 := Bit.add_with_carry (pi_1 r12) x13 y13 in
          let r14 := Bit.add_with_carry (pi_1 r13) x14 y14 in
          let r15 := Bit.add_with_carry (pi_1 r14) x15 y15 in
          (pi_1 r15,
            Int16.introduction
              (Byte.introduction
                (pi_2 r15) (pi_2 r14) (pi_2 r13) (pi_2 r12)
                (pi_2 r11) (pi_2 r10) (pi_2 r9) (pi_2 r8))
              (Byte.introduction
                (pi_2 r7) (pi_2 r6) (pi_2 r5) (pi_2 r4)
                (pi_2 r3) (pi_2 r2) (pi_2 r1) (pi_2 r0)))
      end
  end%product.

(* [Int16 -> Int16 -> Int16] *)
Definition add := fun (x : Int16) (y : Int16) . (pi_2 (add_with_carry 0 x y))%product.

(* [only parsing] keeps goals printing the operations by name. *)
Notation "x + y" := (add x y) (only parsing)
  : jw_int16_scope.

(* The borrow out and the difference of [x - y - borrow], the borrow
 * rippling up as the carry does in [add_with_carry].
 *)
(* [Bit -> Int16 -> Int16 -> Product Bit Int16] *)
Definition sub_with_borrow := fun (borrow : Bit) (x : Int16) (y : Int16) .
  match x with
  | Int16.introduction (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8)
      (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
      match y with
      | Int16.introduction (Byte.introduction y15 y14 y13 y12 y11 y10 y9 y8)
          (Byte.introduction y7 y6 y5 y4 y3 y2 y1 y0) =>
          let r0 := Bit.sub_with_borrow borrow x0 y0 in
          let r1 := Bit.sub_with_borrow (pi_1 r0) x1 y1 in
          let r2 := Bit.sub_with_borrow (pi_1 r1) x2 y2 in
          let r3 := Bit.sub_with_borrow (pi_1 r2) x3 y3 in
          let r4 := Bit.sub_with_borrow (pi_1 r3) x4 y4 in
          let r5 := Bit.sub_with_borrow (pi_1 r4) x5 y5 in
          let r6 := Bit.sub_with_borrow (pi_1 r5) x6 y6 in
          let r7 := Bit.sub_with_borrow (pi_1 r6) x7 y7 in
          let r8 := Bit.sub_with_borrow (pi_1 r7) x8 y8 in
          let r9 := Bit.sub_with_borrow (pi_1 r8) x9 y9 in
          let r10 := Bit.sub_with_borrow (pi_1 r9) x10 y10 in
          let r11 := Bit.sub_with_borrow (pi_1 r10) x11 y11 in
          let r12 := Bit.sub_with_borrow (pi_1 r11) x12 y12 in
          let r13 := Bit.sub_with_borrow (pi_1 r12) x13 y13 in
          let r14 := Bit.sub_with_borrow (pi_1 r13) x14 y14 in
          let r15 := Bit.sub_with_borrow (pi_1 r14) x15 y15 in
          (pi_1 r15,
            Int16.introduction
              (Byte.introduction
                (pi_2 r15) (pi_2 r14) (pi_2 r13) (pi_2 r12)
                (pi_2 r11) (pi_2 r10) (pi_2 r9) (pi_2 r8))
              (Byte.introduction
                (pi_2 r7) (pi_2 r6) (pi_2 r5) (pi_2 r4)
                (pi_2 r3) (pi_2 r2) (pi_2 r1) (pi_2 r0)))
      end
  end%product.

(* [Int16 -> Int16 -> Int16] *)
Definition sub := fun (x : Int16) (y : Int16) . (pi_2 (sub_with_borrow 0 x y))%product.

Notation "x - y" := (sub x y) (only parsing)
  : jw_int16_scope.

(* [x] taken from [Zero], wrapping. *)
(* [Int16 -> Int16] *)
Definition negate := fun (x : Int16) . sub Zero x.

(* Also what makes the minus of a negative literal parse: [Numeral.Signed]
 * lets [from_numeral] receive a sign but puts none in the grammar.
 *)
Notation "- x" := (negate x)
  (at level 35, right associativity, only parsing)
  : jw_int16_scope.

(* [y]'s bits from the most significant, each step doubling the product so
 * far and adding [x] for a 1, all modulo 65536.
 *)
(* [Int16 -> Int16 -> Int16] *)
Definition mul := fun (x : Int16) (y : Int16) .
  let step := fun (p : Int16) (b : Bit) .
    add (shift_left p 1%n0)
      match b with
      | 0%bit => Zero
      | 1%bit => x
      end in
  match y with
  | Int16.introduction (Byte.introduction y15 y14 y13 y12 y11 y10 y9 y8)
      (Byte.introduction y7 y6 y5 y4 y3 y2 y1 y0) =>
      step (step (step (step (step (step (step (step (step (step (step (step (step (step (step (step
        Zero y15) y14) y13) y12) y11) y10) y9) y8) y7) y6) y5) y4) y3) y2) y1) y0
  end.

Notation "x * y" := (mul x y) (only parsing)
  : jw_int16_scope.

(* The flag and the wrapped product: the flag is set when the product of the
 * signed values lies outside the range, below [Min] or above [Max].
 *)
(* [Int16 -> Int16 -> Product Bit Int16] *)
Definition mul_with_overflow := fun (x : Int16) (y : Int16) .
  (match SignedBin.compare (to_b_signed x * to_b_signed y)%b_signed (to_b_signed Min) with
   | Comparison.Lt => 1%bit
   | Comparison.Eq => 0%bit
   | Comparison.Gt =>
       match SignedBin.compare (to_b_signed x * to_b_signed y)%b_signed (to_b_signed Max) with
       | Comparison.Lt => 0%bit
       | Comparison.Eq => 0%bit
       | Comparison.Gt => 1%bit
       end
   end,
   mul x y)%product.

(* The bit pattern of [p] modulo 65536, its bits appended from the most
 * significant.
 *)
(* [BinBase -> Int16] *)
Fixpoint from_bin_base (p : BinBase) : Int16 :=
  match p with
  | BinBase.One   => One
  | BinBase.b0 p' => append_bit 0 (from_bin_base p')
  | BinBase.b1 p' => append_bit 1 (from_bin_base p')
  end.

(* [Bin0 -> Int16] *)
Definition from_b0 := fun (n : Bin0) .
  match n with
  | Bin0.Zero       => Zero
  | Bin0.Positive p => from_bin_base p
  end.

(* [Nat -> Int16] *)
Definition from_nat := fun (n : Nat) . from_bin_base (BinBase.from_nat n).

(* [Nat0 -> Int16] *)
Definition from_nat0 := fun (n : Nat0) . from_b0 (Bin0.from_nat0 n).

(* [z] modulo 65536 into the range -32768 to 32767: its positive part less its
 * negative part, wrapping.
 *)
(* [SignedBin -> Int16] *)
Definition from_b_signed := fun (z : SignedBin) .
  add (from_b0 (SignedBin.ramp z)) (negate (from_b0 (SignedBin.ramp (SignedBin.negate z)))).

(* The quotient through [SignedBin], toward zero, [None] when [y] is zero. [SignedBin.divide]
 * takes a positive divisor, so the divisor's sign is matched here; -32768
 * (-2^15) over -1 wraps to itself.
 *)
(* [Int16 -> Int16 -> Option Int16] *)
Definition divide := fun (x : Int16) (y : Int16) .
  match to_b_signed y with
  | SignedBin.Negative d => Some (from_b_signed (SignedBin.negate (x /. d)%b_signed))
  | SignedBin.Zero       => None
  | SignedBin.Positive d => Some (from_b_signed (x /. d)%b_signed)
  end.

Notation "x /. y" := (divide x y) (only parsing)
  : jw_int16_scope.

(* [x] modulo 65536 into the range -32768 to 32767. *)
(* [Integer -> Int16] *)
Definition from_integer := fun (x : Integer) .
  match x with
  | Integer.Negative p => negate (from_nat p)
  | Integer.Zero       => Zero
  | Integer.Positive p => from_nat p
  end.

(* The overflow flag and the sum of [x + y]: the flag is set when [x] and [y]
 * have the same sign and the sum the other, the true sum lying past -32768 or
 * 32767.
 *)
(* [Int16 -> Int16 -> Product Bit Int16] *)
Definition add_with_overflow := fun (x : Int16) (y : Int16) .
  let flag :=
    Bit.and
      (Bit.flip (Bit.xor (sign_bit x) (sign_bit y)))
      (Bit.xor (sign_bit (add x y)) (sign_bit x)) in
  (flag, add x y)%product.

(* The overflow flag and the difference of [x - y]: the flag is set when [x]
 * and [y] have different signs and the difference has the sign of [y], the
 * true difference lying past -32768 or 32767.
 *)
(* [Int16 -> Int16 -> Product Bit Int16] *)
Definition sub_with_overflow := fun (x : Int16) (y : Int16) .
  let flag :=
    Bit.and
      (Bit.xor (sign_bit x) (sign_bit y))
      (Bit.xor (sign_bit (sub x y)) (sign_bit x)) in
  (flag, sub x y)%product.

(* [Int16 -> Int16 -> Prop] *)
Definition LessThan := fun (x : Int16) (y : Int16) . (to_b_signed x < to_b_signed y)%b_signed.

Notation "x < y" := (LessThan x y) (only parsing)
  : jw_int16_scope.

(* [Int16 -> Int16 -> Prop] *)
Definition LessOrEqual := fun (x : Int16) (y : Int16) . x = y \/ LessThan x y.

Notation "x <= y" := (LessOrEqual x y) (only parsing)
  : jw_int16_scope.

Notation "x > y" := (LessThan y x) (only parsing)
  : jw_int16_scope.
Notation "x >= y" := (LessOrEqual y x) (only parsing)
  : jw_int16_scope.

Notation "'(<)'" := LessThan (only parsing)
  : jw_int16_scope.
Notation "'(<=)'" := LessOrEqual (only parsing)
  : jw_int16_scope.

(* [Int16 -> Int16 -> Comparison] *)
Definition compare := fun (x : Int16) (y : Int16) . SignedBin.compare (to_b_signed x) (to_b_signed y).

(* [Int16 -> Int16 -> Bool] *)
Abbreviation eq := (Comparable.eq compare).

(* [Int16 -> Int16 -> Bool] *)
Abbreviation le := (Comparable.le compare).

(* [Int16 -> Int16 -> Int16] *)
Abbreviation min := (Comparable.min compare).

(* [Int16 -> Int16 -> Int16] *)
Abbreviation max := (Comparable.max compare).

(* A literal of -32768 to 32767, in decimal or hexadecimal, read in binary; any
 * wider is refused.
 *)
(* [Numeral.Signed -> Option Int16] *)
Definition from_numeral := fun (s : Numeral.Signed) .
  let positive := fun (v : Bin0) .
    match Bin0.compare v 111111111111111%b0 with
    | Comparison.Lt => Some (from_b0 v)
    | Comparison.Eq => Some (from_b0 v)
    | Comparison.Gt => None
    end in
  let negative := fun (v : Bin0) .
    match Bin0.compare v 1000000000000000%b0 with
    | Comparison.Lt => Some (negate (from_b0 v))
    | Comparison.Eq => Some (negate (from_b0 v))
    | Comparison.Gt => None
    end in
  match s with
  | Numeral.Signed.Decimal (Numeral.Decimal.Signed.Positive d) =>
      positive (Bin0.from_decimal 0%b0 d)
  | Numeral.Signed.Decimal (Numeral.Decimal.Signed.Negative d) =>
      negative (Bin0.from_decimal 0%b0 d)
  | Numeral.Signed.Hexadecimal (Numeral.Hexadecimal.Signed.Positive h) =>
      positive (Bin0.from_hexadecimal 0%b0 h)
  | Numeral.Signed.Hexadecimal (Numeral.Hexadecimal.Signed.Negative h) =>
      negative (Bin0.from_hexadecimal 0%b0 h)
  end.

(* [x] as a literal, in decimal; zero prints as [0], not [-0]. *)
(* [Int16 -> Numeral.Signed] *)
Definition to_numeral := fun (x : Int16) .
  match to_b_signed x with
  | SignedBin.Negative p =>
      Numeral.Signed.Decimal
        (Numeral.Decimal.Signed.Negative (Bin0.to_decimal (Bin0.Positive p)))
  | SignedBin.Zero =>
      Numeral.Signed.Decimal
        (Numeral.Decimal.Signed.Positive
          (Numeral.Decimal.Digits.Zero Numeral.Decimal.Digits.End))
  | SignedBin.Positive p =>
      Numeral.Signed.Decimal
        (Numeral.Decimal.Signed.Positive (Bin0.to_decimal (Bin0.Positive p)))
  end.

Local Open Scope jw_int16_scope.

Module reinterpretation. (* reinterpretation *)

(* reinterpretation.zero *)
Theorem zero : unsigned_value Zero = 0%b0.
Proof.
  simpl in |- *.
  quod idem est.
Qed.

(* reinterpretation.one *)
Theorem one : unsigned_value One = 1%b0.
Proof.
  simpl in |- *.
  quod idem est.
Qed.

(* reinterpretation.boundedness *)
Theorem boundedness : forall (x : Int16) . (unsigned_value x < modulus)%b0.
Proof.
  intros x.
  match &x with | introduction xb1 xb0 end.
  match &xb1 with | introduction x15 x14 x13 x12 x11 x10 x9 x8 end.
  match &xb0 with | introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  simpl unsigned_value in |- *.
  ipso
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness &x15)))))))))))))))).
Qed.

(* reinterpretation.injectivity *)
Theorem injectivity
  : forall {x : Int16} {y : Int16} . unsigned_value x = unsigned_value y -> x = y.
Proof.
  intros x y e.
  match &x with | introduction xb1 xb0 end.
  match &xb1 with | introduction x15 x14 x13 x12 x11 x10 x9 x8 end.
  match &xb0 with | introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | introduction yb1 yb0 end.
  match &yb1 with | introduction y15 y14 y13 y12 y11 y10 y9 y8 end.
  match &yb0 with | introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
  simpl unsigned_value in &e.
  match (Bit.conversion.binary.halving.injectivity &e) with | e1 b0 end.
  match (Bit.conversion.binary.halving.injectivity &e1) with | e2 b1 end.
  match (Bit.conversion.binary.halving.injectivity &e2) with | e3 b2 end.
  match (Bit.conversion.binary.halving.injectivity &e3) with | e4 b3 end.
  match (Bit.conversion.binary.halving.injectivity &e4) with | e5 b4 end.
  match (Bit.conversion.binary.halving.injectivity &e5) with | e6 b5 end.
  match (Bit.conversion.binary.halving.injectivity &e6) with | e7 b6 end.
  match (Bit.conversion.binary.halving.injectivity &e7) with | e8 b7 end.
  match (Bit.conversion.binary.halving.injectivity &e8) with | e9 b8 end.
  match (Bit.conversion.binary.halving.injectivity &e9) with | e10 b9 end.
  match (Bit.conversion.binary.halving.injectivity &e10) with | e11 b10 end.
  match (Bit.conversion.binary.halving.injectivity &e11) with | e12 b11 end.
  match (Bit.conversion.binary.halving.injectivity &e12) with | e13 b12 end.
  match (Bit.conversion.binary.halving.injectivity &e13) with | e14 b13 end.
  match (Bit.conversion.binary.halving.injectivity &e14) with | e15 b14 end.
  leibniz
    &b0, &b1, &b2, &b3, &b4, &b5, &b6, &b7, &b8, &b9, &b10, &b11, &b12, &b13, &b14,
    (Bit.conversion.binary.injectivity &e15)
    in |- *.
  quod idem est.
Qed.

(* The numbers are added place by place from the most significant, each
 * place one [Bit.conversion.binary.carry.propagation] around the places
 * above it.
 *)
(* reinterpretation.carry *)
Theorem carry
  : forall (carry : Bit) (x : Int16) (y : Int16) .
      (Bit.to_b0 carry + unsigned_value x + unsigned_value y
        = modulus * Bit.to_b0 (pi_1 (add_with_carry carry x y))%product
          + unsigned_value (pi_2 (add_with_carry carry x y))%product)%b0.
Proof.
  intros carry x y.
  match &x with | introduction xb1 xb0 end.
  match &xb1 with | introduction x15 x14 x13 x12 x11 x10 x9 x8 end.
  match &xb0 with | introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | introduction yb1 yb0 end.
  match &yb1 with | introduction y15 y14 y13 y12 y11 y10 y9 y8 end.
  match &yb0 with | introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
  simpl unsigned_value, add_with_carry in |- *.
  ipso
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry _ &x15 &y15)))))))))))))))).
Qed.

(* reinterpretation.borrow *)
Theorem borrow
  : forall (borrow : Bit) (x : Int16) (y : Int16) .
      (unsigned_value x
        + modulus * Bit.to_b0 (pi_1 (sub_with_borrow borrow x y))%product
        = unsigned_value y + Bit.to_b0 borrow
          + unsigned_value (pi_2 (sub_with_borrow borrow x y))%product)%b0.
Proof.
  intros borrow x y.
  match &x with | introduction xb1 xb0 end.
  match &xb1 with | introduction x15 x14 x13 x12 x11 x10 x9 x8 end.
  match &xb0 with | introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | introduction yb1 yb0 end.
  match &yb1 with | introduction y15 y14 y13 y12 y11 y10 y9 y8 end.
  match &yb0 with | introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
  simpl unsigned_value, sub_with_borrow in |- *.
  ipso
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow _ &x15 &y15)))))))))))))))).
Qed.

(* reinterpretation.addition *)
Theorem addition
  : forall (x : Int16) (y : Int16) .
      (unsigned_value (x + y)%int16
        = (unsigned_value x + unsigned_value y) %. modulus)%b0.
Proof.
  intros x y.
  lemma witness
    : (Bit.to_b0 (pi_1 (add_with_carry 0 &x &y))%product * modulus
        + unsigned_value (&x + &y)%int16
        = unsigned_value &x + unsigned_value &y
      /\ unsigned_value (&x + &y)%int16 < modulus)%b0.
  {
    divide et impera.
    - simpl add in |- *.
      leibniz
        (Bin0.multiplication.commutativity
          (Bit.to_b0 (pi_1 (add_with_carry 0 &x &y))%product)
          modulus),
        <- (reinterpretation.carry 0 &x &y)
        in |- *.
      simpl in |- *.
      quod idem est.
    - ipso (reinterpretation.boundedness (&x + &y)).
  }
  match (Bin0.division.uniqueness
          (unsigned_value &x + unsigned_value &y)%b0 modulus
          (Bit.to_b0 (pi_1 (add_with_carry 0 &x &y))%product)
          (unsigned_value (&x + &y)%int16)
          &witness)
  with | _ facto end.
  ipso (symm &facto).
Qed.

(* reinterpretation.subtraction *)
Theorem subtraction
  : forall (x : Int16) (y : Int16) .
      ((unsigned_value (sub x y) + unsigned_value y) %. modulus
        = unsigned_value x)%b0.
Proof.
  intros x y.
  lemma witness
    : (Bit.to_b0 (pi_1 (sub_with_borrow 0 &x &y))%product * modulus
        + unsigned_value &x
        = unsigned_value (sub &x &y) + unsigned_value &y
      /\ unsigned_value &x < modulus)%b0.
  {
    divide et impera.
    - simpl sub in |- *.
      leibniz
        (Bin0.multiplication.commutativity
          (Bit.to_b0 (pi_1 (sub_with_borrow 0 &x &y))%product)
          modulus),
        (Bin0.addition.commutativity
          (modulus
            * Bit.to_b0 (pi_1 (sub_with_borrow 0 &x &y))%product)%b0
          (unsigned_value &x)),
        (reinterpretation.borrow 0 &x &y),
        (Bin0.addition.commutativity
          (unsigned_value &y) (Bit.to_b0 0))
        in |- *.
      simpl in |- *.
      leibniz
        (Bin0.addition.commutativity
          (unsigned_value &y)
          (unsigned_value (pi_2 (sub_with_borrow 0 &x &y))%product))
        in |- *.
      quod idem est.
    - ipso (reinterpretation.boundedness &x).
  }
  match (Bin0.division.uniqueness
          (unsigned_value (sub &x &y) + unsigned_value &y)%b0 modulus
          (Bit.to_b0 (pi_1 (sub_with_borrow 0 &x &y))%product)
          (unsigned_value &x)
          &witness)
  with | _ facto end.
  ipso facto.
Qed.

(* reinterpretation.negation *)
Theorem negation
  : forall (x : Int16) .
      ((unsigned_value (- x)%int16 + unsigned_value x) %. modulus
        = 0)%b0.
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
  : forall (b : Bit) (x : Int16) .
      (unsigned_value (append_bit b x)
        = (10 * unsigned_value x + Bit.to_b0 b) %. modulus)%b0.
Proof.
  intros b x.
  match &x with | introduction xb1 xb0 end.
  match &xb1 with | introduction x15 x14 x13 x12 x11 x10 x9 x8 end.
  match &xb0 with | introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  lemma witness
    : (Bit.to_b0 &x15 * modulus
        + unsigned_value
            (append_bit &b
              (Int16.introduction (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
                (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)))
        = 10
            * unsigned_value
                (Int16.introduction (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
                  (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0))
          + Bit.to_b0 &b
      /\ unsigned_value
          (append_bit &b
            (Int16.introduction (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
              (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)))
        < modulus)%b0.
  {
    divide et impera.
    - lemma top
        : (Bit.to_b0 &x15 = Bit.to_b0 &x15 * 1 + 0)%b0.
      {
        match (Bin0.addition.identity (Bit.to_b0 &x15 * 1)%b0)
        with | _ sum end.
        match (Bin0.multiplication.identity (Bit.to_b0 &x15))
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
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x7
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x8
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x9
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x10
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x11
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x12
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x13
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x14
          &top))))))))))))))))).
    - ipso
        (reinterpretation.boundedness
          (append_bit &b
            (Int16.introduction (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
              (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)))).
  }
  match (Bin0.division.uniqueness
          (10 * unsigned_value
                  (Int16.introduction (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
                    (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0))
            + Bit.to_b0 &b)%b0
          modulus
          (Bit.to_b0 &x15)
          (unsigned_value
            (append_bit &b
              (Int16.introduction (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
                (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0))))
          &witness)
  with | _ facto end.
  ipso (symm &facto).
Qed.

(* reinterpretation.reduction *)
Theorem reduction
  : forall (n : Bin0) .
      unsigned_value (from_b0 n) = (n %. modulus)%b0.
Proof.
  intros n.
  match &n with | Zero | Positive p end.
  - simpl from_b0, Bin0.modulo, Bin0.div, Product.second in |- *.
    simpl in |- *.
    quod idem est.
  - simpl from_b0 in |- *.
    match p with | One | b0 (p' by IH) | b1 (p' by IH) end per BinBase.induction.
    + simpl Bin0.modulo, Bin0.div in |- *.
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
        <- (Bin0.modulo.sum.left.absorption
          (10 * (Bin0.Positive &p' %. modulus))%b0
          (Bit.to_b0 0) modulus),
        (Bin0.modulo.product.right.absorption
          10%b0 (Bin0.Positive &p') modulus),
        (Bin0.modulo.sum.left.absorption
          (10 * Bin0.Positive &p')%b0
          (Bit.to_b0 0) modulus)
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
        <- (Bin0.modulo.sum.left.absorption
          (10 * (Bin0.Positive &p' %. modulus))%b0
          (Bit.to_b0 1) modulus),
        (Bin0.modulo.product.right.absorption
          10%b0 (Bin0.Positive &p') modulus),
        (Bin0.modulo.sum.left.absorption
          (10 * Bin0.Positive &p')%b0
          (Bit.to_b0 1) modulus)
        in |- *.
      simpl in |- *.
      simpl BinBase.add in |- *.
      simpl in |- *.
      quod idem est.
Qed.

Module reduction. (* reinterpretation.reduction *)

(* reinterpretation.reduction.additivity *)
Theorem additivity
  : forall (m : Bin0) (n : Bin0) .
      from_b0 (m + n)%b0 = from_b0 m + from_b0 n.
Proof.
  intros m n.
  lemma facto
    : unsigned_value (from_b0 (&m + &n)%b0)
      = unsigned_value (from_b0 &m + from_b0 &n).
  {
    leibniz
      (reinterpretation.reduction (&m + &n)%b0),
      (reinterpretation.addition (from_b0 &m) (from_b0 &n)),
      (reinterpretation.reduction &m),
      (reinterpretation.reduction &n),
      (Bin0.modulo.sum.left.absorption
        &m (&n %. modulus)%b0 modulus),
      (Bin0.modulo.sum.right.absorption &m &n modulus)
      in |- *.
    quod idem est.
  }
  ipso (reinterpretation.injectivity &facto).
Qed.

End reduction. (* reinterpretation.reduction *)

(* reinterpretation.section *)
Theorem section : forall (x : Int16) . from_b0 (unsigned_value x) = x.
Proof.
  intros x.
  lemma facto
    : unsigned_value (from_b0 (unsigned_value &x)) = unsigned_value &x.
  {
    leibniz
      (reinterpretation.reduction (unsigned_value &x)),
      (Bin0.modulo.identity
        (unsigned_value &x) modulus (reinterpretation.boundedness &x))
      in |- *.
    quod idem est.
  }
  ipso (reinterpretation.injectivity &facto).
Qed.

Module left. (* reinterpretation.left *)

(* reinterpretation.left.doubling *)
Lemma doubling
  : forall (x : Int16) .
      (unsigned_value (shift_left x 1%n0)
        = (10 * unsigned_value x) %. modulus)%b0.
Proof.
  intros x.
  lemma appended : shift_left &x 1%n0 = append_bit 0 &x.
  {
    match &x with | introduction xb1 xb0 end.
    match &xb1 with | introduction x15 x14 x13 x12 x11 x10 x9 x8 end.
    match &xb0 with | introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
    simpl in |- *.
    quod idem est.
  }
  match (Bin0.addition.identity (10 * unsigned_value &x)%b0)
  with | _ sum end.
  leibniz &appended, (reinterpretation.appending 0 &x) in |- *.
  simpl Bit.to_b0 in |- *.
  leibniz &sum in |- *.
  quod idem est.
Qed.

End left. (* reinterpretation.left *)

Module multiplication. (* reinterpretation.multiplication *)

(* One step of [mul]: the product so far doubled, plus [x] for a 1. *)
(* reinterpretation.multiplication.step *)
Lemma step
  : forall (x : Int16) (p : Int16) (h : Bin0) (b : Bit) .
      (unsigned_value p = (unsigned_value x * h) %. modulus)%b0 ->
      unsigned_value
        (add (shift_left p 1%n0)
          match b with
          | 0%bit => Zero
          | 1%bit => x
          end)
      = ((unsigned_value x * (10 * h + Bit.to_b0 b))
          %. modulus)%b0.
Proof.
  intros x p h b e.
  lemma doubled
    : ((10 * unsigned_value &p) %. modulus
        = (10 * (unsigned_value &x * &h)) %. modulus)%b0.
  {
    leibniz
      &e,
      (Bin0.modulo.product.right.absorption
        10%b0 (unsigned_value &x * &h)%b0 modulus)
      in |- *.
    quod idem est.
  }
  lemma regrouped
    : (unsigned_value &x * (10 * &h) = 10 * (unsigned_value &x * &h))%b0.
  {
    leibniz
      <- (Bin0.multiplication.associativity (unsigned_value &x) 10%b0 &h),
      (Bin0.multiplication.commutativity (unsigned_value &x) 10%b0),
      (Bin0.multiplication.associativity 10%b0 (unsigned_value &x) &h)
      in |- *.
    quod idem est.
  }
  match &b with | Zero | One end.
  - lemma facto
      : unsigned_value (add (shift_left &p 1%n0) Zero)
        = ((unsigned_value &x * (10 * &h + Bit.to_b0 0))
            %. modulus)%b0.
    {
      match (Bin0.addition.identity (10 * unsigned_value &p)%b0)
      with | _ right end.
      match (Bin0.addition.identity (10 * &h)%b0) with | _ right' end.
      leibniz
        (reinterpretation.addition (shift_left &p 1%n0) Zero),
        (reinterpretation.left.doubling &p),
        reinterpretation.zero,
        (Bin0.modulo.sum.left.absorption
          (10 * unsigned_value &p)%b0 0%b0 modulus),
        &right,
        &doubled
        in |- *.
      simpl Bit.to_b0 in |- *.
      leibniz &right', &regrouped in |- *.
      quod idem est.
    }
    ipso facto.
  - lemma facto
      : unsigned_value (add (shift_left &p 1%n0) &x)
        = ((unsigned_value &x * (10 * &h + Bit.to_b0 1))
            %. modulus)%b0.
    {
      match (Bin0.multiplication.identity (unsigned_value &x)) with | _ right end.
      match (Bin0.multiplication.distributivity.over.addition
              (unsigned_value &x) (10 * &h)%b0 1%b0)
      with | spread _ end.
      leibniz
        (reinterpretation.addition (shift_left &p 1%n0) &x),
        (reinterpretation.left.doubling &p),
        &doubled,
        (Bin0.modulo.sum.left.absorption
          (10 * (unsigned_value &x * &h))%b0 (unsigned_value &x)
          modulus)
        in |- *.
      simpl Bit.to_b0 in |- *.
      leibniz &spread, &right, &regrouped in |- *.
      quod idem est.
    }
    ipso facto.
Qed.

End multiplication. (* reinterpretation.multiplication *)

(* reinterpretation.multiplication *)
Theorem multiplication
  : forall (x : Int16) (y : Int16) .
      (unsigned_value (x * y)%int16
        = (unsigned_value x * unsigned_value y) %. modulus)%b0.
Proof.
  intros x y.
  lemma base
    : (unsigned_value Zero
        = (unsigned_value &x * 0) %. modulus)%b0.
  {
    match (Bin0.multiplication.annihilation (unsigned_value &x)) with | _ right end.
    leibniz &right, reinterpretation.zero in |- *.
    simpl Bin0.modulo, Bin0.div, Product.second in |- *.
    quod idem est.
  }
  match &y with | introduction yb1 yb0 end.
  match &yb1 with | introduction y15 y14 y13 y12 y11 y10 y9 y8 end.
  match &yb0 with | introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
  simpl mul in |- *.
  ipso
    (reinterpretation.multiplication.step _ _ _ _
    (reinterpretation.multiplication.step _ _ _ _
    (reinterpretation.multiplication.step _ _ _ _
    (reinterpretation.multiplication.step _ _ _ _
    (reinterpretation.multiplication.step _ _ _ _
    (reinterpretation.multiplication.step _ _ _ _
    (reinterpretation.multiplication.step _ _ _ _
    (reinterpretation.multiplication.step _ _ _ _
    (reinterpretation.multiplication.step _ _ _ _
    (reinterpretation.multiplication.step _ _ _ _
    (reinterpretation.multiplication.step _ _ _ _
    (reinterpretation.multiplication.step _ _ _ _
    (reinterpretation.multiplication.step _ _ _ _
    (reinterpretation.multiplication.step _ _ _ _
    (reinterpretation.multiplication.step _ _ _ _
    (reinterpretation.multiplication.step _ _ _ _ &base)))))))))))))))).
Qed.

Module sign. (* reinterpretation.sign *)

(* reinterpretation.sign.clear *)
Theorem clear
  : forall (x : Int16) .
      sign_bit x = 0%bit -> (unsigned_value x < 1000000000000000)%b0.
Proof.
  intros x e.
  match &x with | introduction xb1 xb0 end.
  match &xb1 with | introduction x15 x14 x13 x12 x11 x10 x9 x8 end.
  match &xb0 with | introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  simpl sign_bit in &e.
  simpl unsigned_value in |- *.
  leibniz &e in |- *.
  lemma base : (Bit.to_b0 0 < 1)%b0.
  {
    simpl Bin0.LessThan in |- *.
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
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    &base))))))))))))))).
Qed.

(* reinterpretation.sign.set *)
Theorem set
  : forall (x : Int16) .
      sign_bit x = 1%bit -> (1000000000000000 <= unsigned_value x)%b0.
Proof.
  intros x e.
  match &x with | introduction xb1 xb0 end.
  match &xb1 with | introduction x15 x14 x13 x12 x11 x10 x9 x8 end.
  match &xb0 with | introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  simpl sign_bit in &e.
  simpl unsigned_value in |- *.
  leibniz &e in |- *.
  lemma base : (1 <= Bit.to_b0 1)%b0.
  {
    simpl Bin0.LessOrEqual, Bit.to_b0 in |- *.
    ipso (disjoin (refl 1%b0), _).
  }
  ipso
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    &base))))))))))))))).
Qed.

End sign. (* reinterpretation.sign *)

End reinterpretation. (* reinterpretation *)

(* [Int16] as a [Modular.Width]: its unsigned values are the residues modulo
 * 65536, and the laws of addition, subtraction and multiplication are read
 * through them.
 *)
Module Residue <: Modular.Width.

Definition T := T.
Definition Zero := Zero.
Definition One := One.
Definition to_b0 := unsigned_value.
Definition add := add.
Definition sub := sub.
Definition negate := negate.
Definition mul := mul.
Definition modulus := modulus.

Module conversion. (* Residue.conversion *)

Definition zero := Int16.reinterpretation.zero.
Definition one := Int16.reinterpretation.one.
Definition boundedness := Int16.reinterpretation.boundedness.
Definition injectivity := @Int16.reinterpretation.injectivity.
Definition addition := Int16.reinterpretation.addition.
Definition subtraction := Int16.reinterpretation.subtraction.
Definition negation := Int16.reinterpretation.negation.
Definition multiplication := Int16.reinterpretation.multiplication.

End conversion. (* Residue.conversion *)

End Residue.

Include Modular.Laws Residue.

Module conversion. (* conversion *)

(* The bit pattern of [a - b] is that of [a] less that of [b]. *)
(* conversion.difference *)
Lemma difference
  : forall (a : Bin0) (b : Bin0) .
      from_b_signed (SignedBin.b0_difference a b)
      = from_b0 a + - from_b0 b.
Proof.
  intros a b.
  let proof e := congru from_b0, (SignedBin.difference.specification &a &b).
  leibniz
    (reinterpretation.reduction.additivity (SignedBin.ramp (SignedBin.b0_difference &a &b)) &b),
    (reinterpretation.reduction.additivity
      (SignedBin.ramp (SignedBin.negate (SignedBin.b0_difference &a &b))) &a)
    in &e.
  simpl from_b_signed in |- *.
  let p := from_b0 (SignedBin.ramp (SignedBin.b0_difference &a &b)) in &e |- *.
  let q :=
    from_b0 (SignedBin.ramp (SignedBin.negate (SignedBin.b0_difference &a &b)))
    in &e |- *.
  lemma rewritten : &p = (&q + from_b0 &a) + - from_b0 &b.
  {
    match (addition.inverse (from_b0 &b)) with | _ cancel end.
    match (addition.identity &p) with | _ unit end.
    leibniz
      <- &e,
      (addition.associativity &p (from_b0 &b) (- from_b0 &b)),
      &cancel,
      &unit
      in |- *.
    quod idem est.
  }
  match (addition.inverse &q) with | _ cancel end.
  match (addition.identity (- from_b0 &b)) with | _ unit end.
  leibniz
    &rewritten,
    (addition.commutativity &q (from_b0 &a)),
    (addition.associativity (from_b0 &a) &q (- from_b0 &b)),
    (addition.commutativity &q (- from_b0 &b)),
    (addition.associativity (from_b0 &a) (- from_b0 &b + &q) (- &q)),
    (addition.associativity (- from_b0 &b) &q (- &q)),
    &cancel,
    &unit
    in |- *.
  quod idem est.
Qed.

(* conversion.section *)
Theorem section : forall (x : Int16) . from_b_signed (to_b_signed x) = x.
Proof.
  intros x.
  lemma vanishing
    : from_b0 (modulus * Bit.to_b0 (sign_bit &x))%b0 = Zero.
  {
    lemma facto
      : unsigned_value
          (from_b0 (modulus * Bit.to_b0 (sign_bit &x))%b0)
        = unsigned_value Zero.
    {
      leibniz
        (reinterpretation.reduction (modulus * Bit.to_b0 (sign_bit &x))%b0),
        reinterpretation.zero
        in |- *.
      match (sign_bit &x) with | Zero | One end.
      - simpl Bit.to_b0, Bin0.modulo, Bin0.div, Product.second
          in |- *.
        simpl in |- *.
        quod idem est.
      - simpl Bit.to_b0, Bin0.modulo, Bin0.div, Product.second
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
  simpl to_b_signed in |- *.
  leibniz
    (conversion.difference
      (unsigned_value &x) (modulus * Bit.to_b0 (sign_bit &x))%b0),
    (reinterpretation.section &x),
    &vanishing,
    &unsigned,
    &right
    in |- *.
  quod idem est.
Qed.

(* conversion.injectivity *)
Theorem injectivity : forall {x : Int16} {y : Int16} . to_b_signed x = to_b_signed y -> x = y.
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
  : forall (x : Int16) (y : Int16) .
      (pi_1 (add_with_overflow x y))%product = 0%bit ->
      (Bit.to_b0 (sign_bit x) + Bit.to_b0 (sign_bit y)
        = Bit.to_b0 (pi_1 (add_with_carry 0 x y))%product
          + Bit.to_b0 (sign_bit (x + y)%int16))%b0.
Proof.
  intros x y o.
  match &x with | introduction xb1 xb0 end.
  match &xb1 with | introduction x15 x14 x13 x12 x11 x10 x9 x8 end.
  match &xb0 with | introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | introduction yb1 yb0 end.
  match &yb1 with | introduction y15 y14 y13 y12 y11 y10 y9 y8 end.
  match &yb0 with | introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
  simpl in &o |- *.
  ipso (Bit.conversion.binary.carry.conservation _ &x15 &y15 &o).
Qed.

(* conversion.addition *)
Theorem addition
  : forall (x : Int16) (y : Int16) .
      (pi_1 (add_with_overflow x y))%product = 0%bit ->
      to_b_signed (x + y) = (x + y)%b_signed.
Proof.
  intros x y o.
  let proof t := conversion.sign &x &y &o.
  let proof a
    : (unsigned_value &x + unsigned_value &y
        = modulus * Bit.to_b0 (pi_1 (add_with_carry 0 &x &y))%product
          + unsigned_value (&x + &y)%int16)%b0
    := reinterpretation.carry 0 &x &y.
  lemma balance
    : (unsigned_value (&x + &y)%int16
        + (modulus * Bit.to_b0 (sign_bit &x)
          + modulus * Bit.to_b0 (sign_bit &y))
        = (unsigned_value &x + unsigned_value &y)
          + modulus * Bit.to_b0 (sign_bit (&x + &y)%int16))%b0.
  {
    match (Bin0.multiplication.distributivity.over.addition
            modulus
            (Bit.to_b0 (sign_bit &x)) (Bit.to_b0 (sign_bit &y)))
    with | signs _ end.
    match (Bin0.multiplication.distributivity.over.addition
            modulus
            (Bit.to_b0 (pi_1 (add_with_carry 0 &x &y))%product)
            (Bit.to_b0 (sign_bit (&x + &y)%int16)))
    with | carries _ end.
    leibniz
      <- &signs,
      &t,
      &carries,
      <- (Bin0.addition.associativity
        (unsigned_value (&x + &y)%int16)
        (modulus
          * Bit.to_b0 (pi_1 (add_with_carry 0 &x &y))%product)%b0
        (modulus * Bit.to_b0 (sign_bit (&x + &y)%int16))%b0),
      (Bin0.addition.commutativity
        (unsigned_value (&x + &y)%int16)
        (modulus
          * Bit.to_b0 (pi_1 (add_with_carry 0 &x &y))%product)%b0),
      &a
      in |- *.
    quod idem est.
  }
  simpl to_b_signed in |- *.
  leibniz
    (SignedBin.difference.additivity
      (unsigned_value &x) (modulus * Bit.to_b0 (sign_bit &x))%b0
      (unsigned_value &y) (modulus * Bit.to_b0 (sign_bit &y))%b0)
    in |- *.
  ipso (SignedBin.difference.invariance &balance).
Qed.

Module right. (* conversion.right *)

(* A shift to the right by one place halves the value, rounding down: the
 * lowest bit is what it drops, and the sign bit copied in keeps the sign.
 *)
(* conversion.right.halving *)
Theorem halving
  : forall (x15 : Bit) (x14 : Bit) (x13 : Bit) (x12 : Bit)
      (x11 : Bit) (x10 : Bit) (x9 : Bit) (x8 : Bit)
      (x7 : Bit) (x6 : Bit) (x5 : Bit) (x4 : Bit)
      (x3 : Bit) (x2 : Bit) (x1 : Bit) (x0 : Bit) .
      to_b_signed (Int16.introduction (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8)
                (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0))
      = (10
          * shift_right
            (Int16.introduction (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8)
              (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0)) 1%n0
          + Bit.to_b0 x0)%b_signed.
Proof.
  intros x15 x14 x13 x12 x11 x10 x9 x8 x7 x6 x5 x4 x3 x2 x1 x0.
  lemma shifted
    : shift_right
        (Int16.introduction (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
          (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)) 1%n0
      = Int16.introduction (Byte.introduction &x15 &x15 &x14 &x13 &x12 &x11 &x10 &x9)
        (Byte.introduction &x8 &x7 &x6 &x5 &x4 &x3 &x2 &x1).
  {
    simpl in |- *.
    quod idem est.
  }
  lemma split
    : (10 * unsigned_value
              (Int16.introduction (Byte.introduction &x15 &x15 &x14 &x13 &x12 &x11 &x10 &x9)
                (Byte.introduction &x8 &x7 &x6 &x5 &x4 &x3 &x2 &x1))
        + Bit.to_b0 &x0
        = Bit.to_b0 &x15 * modulus
          + unsigned_value
              (Int16.introduction
                (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
                  (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)))%b0.
  {
    lemma top
      : (Bit.to_b0 &x15 = Bit.to_b0 &x15 * 1 + 0)%b0.
    {
      match (Bin0.addition.identity (Bit.to_b0 &x15 * 1)%b0)
      with | _ sum end.
      match (Bin0.multiplication.identity (Bit.to_b0 &x15))
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
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x8
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x9
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x10
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x11
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x12
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x13
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x14
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x15
      &top)))))))))))))))).
  }
  lemma twice : forall (z : SignedBin) . (10 * z = z + z)%b_signed.
  {
    intros z.
    lemma ten : (10 = 1 + 1)%b_signed.
    {
      simpl SignedBin.add in |- *.
      simpl in |- *.
      simpl BinBase.add in |- *.
      simpl in |- *.
      quod idem est.
    }
    match (SignedBin.multiplication.distributivity.over.addition &z 1%b_signed 1%b_signed) with | _ spread end.
    match (SignedBin.multiplication.identity &z) with | unit _ end.
    leibniz &ten, &spread, &unit in |- *.
    quod idem est.
  }
  lemma doubled
    : forall (n : Bin0) . (n + n = 10 * n)%b0.
  {
    intros n.
    lemma ten : (10 = 1 + 1)%b0.
    {
      simpl in |- *.
      simpl BinBase.add in |- *.
      simpl in |- *.
      quod idem est.
    }
    match (Bin0.multiplication.distributivity.over.addition &n 1%b0
            1%b0)
    with | _ spread end.
    match (Bin0.multiplication.identity &n) with | unit _ end.
    leibniz &ten, &spread, &unit in |- *.
    quod idem est.
  }
  lemma embedding
    : forall (n : Bin0) .
        SignedBin.from_b0 n = SignedBin.b0_difference n 0%b0.
  {
    intros n.
    match &n with | Zero | Positive p end; simpl in |- *; quod idem est.
  }
  lemma balance
    : (unsigned_value
        (Int16.introduction (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
          (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0))
        + (modulus * Bit.to_b0 &x15 + modulus * Bit.to_b0 &x15 + 0)
        = (unsigned_value
            (Int16.introduction (Byte.introduction &x15 &x15 &x14 &x13 &x12 &x11 &x10 &x9)
              (Byte.introduction &x8 &x7 &x6 &x5 &x4 &x3 &x2 &x1))
          + unsigned_value
              (Int16.introduction (Byte.introduction &x15 &x15 &x14 &x13 &x12 &x11 &x10 &x9)
                (Byte.introduction &x8 &x7 &x6 &x5 &x4 &x3 &x2 &x1))
          + Bit.to_b0 &x0)
          + modulus * Bit.to_b0 &x15)%b0.
  {
    match (Bin0.addition.identity
            (modulus * Bit.to_b0 &x15
              + modulus * Bit.to_b0 &x15)%b0)
    with | _ unit end.
    leibniz
      &unit,
      (&doubled
        (unsigned_value
          (Int16.introduction (Byte.introduction &x15 &x15 &x14 &x13 &x12 &x11 &x10 &x9)
            (Byte.introduction &x8 &x7 &x6 &x5 &x4 &x3 &x2 &x1)))),
      &split,
      (Bin0.multiplication.commutativity
        (Bit.to_b0 &x15) modulus),
      (Bin0.addition.commutativity
        (modulus * Bit.to_b0 &x15)%b0
        (unsigned_value
          (Int16.introduction (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
            (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)))),
      (Bin0.addition.associativity
        (unsigned_value
          (Int16.introduction (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
            (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)))
        (modulus * Bit.to_b0 &x15)%b0
        (modulus * Bit.to_b0 &x15)%b0)
      in |- *.
    quod idem est.
  }
  leibniz &shifted in |- *.
  simpl to_b_signed, sign_bit in |- *.
  leibniz
    (&twice
      (SignedBin.b0_difference
        (unsigned_value
          (Int16.introduction (Byte.introduction &x15 &x15 &x14 &x13 &x12 &x11 &x10 &x9)
            (Byte.introduction &x8 &x7 &x6 &x5 &x4 &x3 &x2 &x1)))
        (modulus * Bit.to_b0 &x15)%b0)),
    (SignedBin.difference.additivity
      (unsigned_value
        (Int16.introduction (Byte.introduction &x15 &x15 &x14 &x13 &x12 &x11 &x10 &x9)
          (Byte.introduction &x8 &x7 &x6 &x5 &x4 &x3 &x2 &x1)))
      (modulus * Bit.to_b0 &x15)%b0
      (unsigned_value
        (Int16.introduction (Byte.introduction &x15 &x15 &x14 &x13 &x12 &x11 &x10 &x9)
          (Byte.introduction &x8 &x7 &x6 &x5 &x4 &x3 &x2 &x1)))
      (modulus * Bit.to_b0 &x15)%b0),
    (&embedding (Bit.to_b0 &x0)),
    (SignedBin.difference.additivity
      (unsigned_value
        (Int16.introduction (Byte.introduction &x15 &x15 &x14 &x13 &x12 &x11 &x10 &x9)
          (Byte.introduction &x8 &x7 &x6 &x5 &x4 &x3 &x2 &x1))
        + unsigned_value
            (Int16.introduction
              (Byte.introduction &x15 &x15 &x14 &x13 &x12 &x11 &x10 &x9)
                (Byte.introduction &x8 &x7 &x6 &x5 &x4 &x3 &x2 &x1)))%b0
      (modulus * Bit.to_b0 &x15
        + modulus * Bit.to_b0 &x15)%b0
      (Bit.to_b0 &x0) 0%b0)
    in |- *.
  ipso (SignedBin.difference.invariance &balance).
Qed.

End right. (* conversion.right *)

Module signed_bin. (* conversion.signed_bin *)

(* conversion.signed_bin.nonnegative *)
Lemma nonnegative
  : forall (n : Bin0) . from_b_signed (SignedBin.from_b0 n) = from_b0 n.
Proof.
  intros n.
  lemma nothing : - from_b0 Bin0.Zero = Zero.
  {
    simpl from_b0 in |- *.
    match (addition.inverse Zero) with | _ right end.
    match (addition.identity (- Zero)) with | left _ end.
    ipso (trans (symm &left), &right).
  }
  match &n with | Zero | Positive p end.
  - simpl SignedBin.from_b0, from_b_signed in |- *.
    simpl SignedBin.ramp, SignedBin.negate in |- *.
    leibniz &nothing in |- *.
    match (addition.identity (from_b0 Bin0.Zero)) with | _ right end.
    ipso &right.
  - simpl SignedBin.from_b0, from_b_signed in |- *.
    simpl SignedBin.ramp, SignedBin.negate in |- *.
    leibniz &nothing in |- *.
    match (addition.identity (from_b0 (Bin0.Positive &p))) with
    | _ right end.
    ipso &right.
Qed.

(* conversion.signed_bin.negative *)
Lemma negative : forall (p : BinBase) . from_b_signed (SignedBin.Negative p) = - from_bin_base p.
Proof.
  intros p.
  simpl from_b_signed in |- *.
  simpl SignedBin.ramp, SignedBin.negate in |- *.
  lemma nothing : from_b0 Bin0.Zero = Zero.
  {
    simpl from_b0 in |- *.
    quod idem est.
  }
  lemma unfolded : from_b0 (Bin0.Positive &p) = from_bin_base &p.
  {
    simpl from_b0 in |- *.
    quod idem est.
  }
  leibniz &nothing, &unfolded in |- *.
  match (addition.identity (- from_bin_base &p)) with | left _ end.
  ipso &left.
Qed.

End signed_bin. (* conversion.signed_bin *)

Module boundedness. (* conversion.boundedness *)

(* conversion.boundedness.positive *)
Theorem positive
  : forall (x : Int16) (p : BinBase) .
      to_b_signed x = SignedBin.Positive p -> (p < 1000000000000000)%b0.
Proof.
  intros x p e.
  simpl to_b_signed in &e.
  match (sign_bit &x) with | Zero | One end |- s.
  - lemma scaled : (modulus * Bit.to_b0 0 = 0)%b0.
    {
      simpl modulus, Bit.to_b0 in |- *.
      simpl in |- *.
      quod idem est.
    }
    leibniz &scaled in &e.
    let proof small := reinterpretation.sign.clear &x &s.
    match (unsigned_value &x) with | Zero | Positive q end |- f.
    + simpl SignedBin.b0_difference in &e.
      ex &e quodlibet.
    + simpl SignedBin.b0_difference in &e.
      let proof g := congru SignedBin.ramp, &e.
      simpl SignedBin.ramp in &g.
      leibniz &g in &small.
      ipso &small.
  - lemma whole : (modulus * Bit.to_b0 1 = modulus)%b0.
    {
      simpl modulus in |- *.
      simpl in |- *.
      quod idem est.
    }
    leibniz &whole in &e.
    let proof sp := SignedBin.difference.specification (unsigned_value &x) modulus.
    leibniz &e in &sp.
    simpl SignedBin.ramp, SignedBin.negate in &sp.
    match (Bin0.addition.identity (unsigned_value &x)) with | left _ end.
    leibniz &left in &sp.
    let proof bound := reinterpretation.boundedness &x.
    leibniz <- &sp in &bound.
    ex
      (Bin0.order.strict.irreflexivity _
        (Comparable.order.mixed.left.transitivity
          (Bin0.addition.right.order.extensivity p modulus) &bound))
      quodlibet.
Qed.

(* conversion.boundedness.negative *)
Theorem negative
  : forall (x : Int16) (p : BinBase) .
      to_b_signed x = SignedBin.Negative p -> (p <= 1000000000000000)%b0.
Proof.
  intros x p e.
  simpl to_b_signed in &e.
  match (sign_bit &x) with | Zero | One end |- s.
  - lemma scaled : (modulus * Bit.to_b0 0 = 0)%b0.
    {
      simpl modulus, Bit.to_b0 in |- *.
      simpl in |- *.
      quod idem est.
    }
    leibniz &scaled in &e.
    match (unsigned_value &x) with | Zero | Positive q end |- f.
    + simpl SignedBin.b0_difference in &e.
      ex &e quodlibet.
    + simpl SignedBin.b0_difference in &e.
      ex &e quodlibet.
  - lemma whole : (modulus * Bit.to_b0 1 = modulus)%b0.
    {
      simpl modulus in |- *.
      simpl in |- *.
      quod idem est.
    }
    leibniz &whole in &e.
    let proof big := reinterpretation.sign.set &x &s.
    let proof sp := SignedBin.difference.specification (unsigned_value &x) modulus.
    leibniz &e in &sp.
    simpl SignedBin.ramp, SignedBin.negate in &sp.
    match (Bin0.addition.identity modulus) with | left _ end.
    leibniz &left in &sp.
    match
      (Comparable.order.strict.trichotomy
        (Bin0.Positive p) 1000000000000000%b0)
    with
    | below | rest end.
    + simpl Bin0.LessOrEqual in |- *.
      ipso (disjoin _, &below).
    + match &rest with | same | above end.
      * simpl Bin0.LessOrEqual in |- *.
        ipso (disjoin &same, _).
      * lemma double : (1000000000000000 + 1000000000000000 = modulus)%b0.
        {
          simpl modulus, Bin0.add in |- *.
          simpl BinBase.add in |- *.
          simpl in |- *.
          quod idem est.
        }
        let proof total := Bin0.addition.order.strict.monotonicity _ _ _ _ &big &above.
        leibniz
          &double,
          (Bin0.addition.commutativity (unsigned_value &x) p),
          <- &sp
          in &total.
        ex (Bin0.order.strict.irreflexivity _ &total) quodlibet.
Qed.

End boundedness. (* conversion.boundedness *)

Module retraction. (* conversion.retraction *)

(* conversion.retraction.nonnegative *)
Theorem nonnegative
  : forall (n : Bin0) .
      (n < 1000000000000000)%b0
      -> to_b_signed (from_b_signed (SignedBin.from_b0 n)) = SignedBin.from_b0 n.
Proof.
  intros n h.
  lemma half : (1000000000000000 < modulus)%b0.
  {
    simpl Bin0.LessThan in |- *.
    exists 1000000000000000%bin_base.
    simpl modulus, Bin0.add in |- *.
    simpl BinBase.add in |- *.
    simpl in |- *.
    quod idem est.
  }
  lemma value : unsigned_value (from_b0 &n) = &n.
  {
    leibniz
      (reinterpretation.reduction &n),
      (Bin0.modulo.identity &n modulus (Bin0.order.strict.transitivity &h &half))
      in |- *.
    quod idem est.
  }
  lemma sign : sign_bit (from_b0 &n) = 0%bit.
  {
    match (sign_bit (from_b0 &n)) with | Zero | One end |- s.
    - quod idem est.
    - let proof big := reinterpretation.sign.set _ &s.
      leibniz &value in &big.
      ex
        (Bin0.order.strict.irreflexivity _
          (Comparable.order.mixed.left.transitivity &big &h))
        quodlibet.
  }
  leibniz (conversion.signed_bin.nonnegative &n) in |- *.
  simpl to_b_signed in |- *.
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
      (p <= 1000000000000000)%b0
      -> to_b_signed (from_b_signed (SignedBin.Negative p)) = SignedBin.Negative p.
Proof.
  intros p h.
  leibniz (conversion.signed_bin.negative &p) in |- *.
  lemma half : (1000000000000000 < modulus)%b0.
  {
    simpl Bin0.LessThan in |- *.
    exists 1000000000000000%bin_base.
    simpl modulus, Bin0.add in |- *.
    simpl BinBase.add in |- *.
    simpl in |- *.
    quod idem est.
  }
  lemma below : (p < modulus)%b0.
  {
    match &h with | same | smaller end.
    - leibniz &same in |- *.
      ipso &half.
    - ipso (Bin0.order.strict.transitivity &smaller &half).
  }
  let proof pbelow := &below.
  match &below with | k ek end.
  lemma kbelow : (k < modulus)%b0.
  {
    simpl Bin0.LessThan in |- *.
    exists &p.
    leibniz (Bin0.addition.commutativity k p) in |- *.
    ipso &ek.
  }
  lemma valuek : unsigned_value (from_bin_base &k) = k.
  {
    lemma through : from_bin_base &k = from_b0 k.
    {
      simpl from_b0 in |- *.
      quod idem est.
    }
    leibniz
      &through, (reinterpretation.reduction k), (Bin0.modulo.identity k modulus &kbelow)
      in |- *.
    quod idem est.
  }
  lemma valuep : unsigned_value (from_bin_base &p) = p.
  {
    lemma through : from_bin_base &p = from_b0 p.
    {
      simpl from_b0 in |- *.
      quod idem est.
    }
    leibniz
      &through, (reinterpretation.reduction p), (Bin0.modulo.identity p modulus &pbelow)
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
        (Bin0.addition.commutativity k p),
        &ek
        in |- *.
      simpl modulus in |- *.
      simpl Bin0.modulo, Bin0.div in |- *.
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
  lemma double : (1000000000000000 + 1000000000000000 = modulus)%b0.
  {
    simpl modulus, Bin0.add in |- *.
    simpl BinBase.add in |- *.
    simpl in |- *.
    quod idem est.
  }
  lemma sign : sign_bit (from_bin_base &k) = 1%bit.
  {
    match (sign_bit (from_bin_base &k)) with | Zero | One end |- s.
    - let proof small := reinterpretation.sign.clear _ &s.
      leibniz &valuek in &small.
      let proof total := Bin0.addition.order.strict.monotonicity _ _ _ _ &h &small.
      leibniz &ek, &double in &total.
      ex (Bin0.order.strict.irreflexivity _ &total) quodlibet.
    - quod idem est.
  }
  lemma whole : (modulus * Bit.to_b0 1 = modulus)%b0.
  {
    simpl modulus in |- *.
    simpl in |- *.
    quod idem est.
  }
  lemma swap : (k + p = 0 + modulus)%b0.
  {
    match (Bin0.addition.identity modulus) with | left _ end.
    leibniz (Bin0.addition.commutativity k p), &ek, &left in |- *.
    quod idem est.
  }
  simpl to_b_signed in |- *.
  leibniz &valuek, &sign, &whole, (SignedBin.difference.invariance &swap) in |- *.
  simpl SignedBin.b0_difference in |- *.
  quod idem est.
Qed.

End retraction. (* conversion.retraction *)

Module division. (* conversion.division *)

(* conversion.division.positive *)
Theorem positive
  : forall (x : Int16) (y : Int16) (d : BinBase) .
      to_b_signed y = SignedBin.Positive d -> Option.map to_b_signed (x /. y)%int16 = Some (x /. d)%b_signed.
Proof.
  intros x y d e.
  lemma origin : to_b_signed (from_b_signed 0%b_signed) = 0%b_signed.
  {
    lemma nothing : (0 < 1000000000000000)%b0.
    {
      simpl Bin0.LessThan in |- *.
      exists 1000000000000000%bin_base.
      simpl Bin0.add in |- *.
      quod idem est.
    }
    let proof r := conversion.retraction.nonnegative 0%b0 &nothing.
    simpl SignedBin.from_b0 in &r.
    ipso &r.
  }
  lemma fits : to_b_signed (from_b_signed (x /. &d)%b_signed) = (x /. &d)%b_signed.
  {
    match (to_b_signed &x) with | Negative p | Zero | Positive p end |- t.
    - let proof r := conversion.boundedness.negative &x &p &t.
      let proof b := Bin0.division.quotient.boundedness p &d.
      simpl SignedBin.divide in |- *.
      match ((p /. &d)%b0) with | Zero | Positive q end |- f.
      + simpl SignedBin.from_b0, SignedBin.negate in |- *.
        ipso &origin.
      + simpl SignedBin.from_b0, SignedBin.negate in |- *.
        lemma bounded : (q <= 1000000000000000)%b0.
        {
          match &r with | same | smaller end.
          - leibniz &same in &b.
            ipso &b.
          - simpl Bin0.LessOrEqual in |- *.
            ipso (disjoin _, (Comparable.order.mixed.left.transitivity &b &smaller)).
        }
        ipso (conversion.retraction.negative &q &bounded).
    - simpl SignedBin.divide in |- *.
      ipso &origin.
    - let proof r := conversion.boundedness.positive &x &p &t.
      let proof b := Bin0.division.quotient.boundedness p &d.
      simpl SignedBin.divide in |- *.
      ipso
        (conversion.retraction.nonnegative (p /. &d)%b0
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
  : forall (x : Int16) (y : Int16) (d : BinBase) .
      to_b_signed y = SignedBin.Negative d
      -> ~ (to_b_signed x = (-1000000000000000)%b_signed /\ d = BinBase.One)
      -> Option.map to_b_signed (x /. y)%int16 = Some (SignedBin.negate (x /. d)%b_signed).
Proof.
  intros x y d e h.
  lemma origin : to_b_signed (from_b_signed 0%b_signed) = 0%b_signed.
  {
    lemma nothing : (0 < 1000000000000000)%b0.
    {
      simpl Bin0.LessThan in |- *.
      exists 1000000000000000%bin_base.
      simpl Bin0.add in |- *.
      quod idem est.
    }
    let proof r := conversion.retraction.nonnegative 0%b0 &nothing.
    simpl SignedBin.from_b0 in &r.
    ipso &r.
  }
  lemma fits : to_b_signed (from_b_signed (SignedBin.negate (x /. &d)%b_signed)) = SignedBin.negate (x /. &d)%b_signed.
  {
    match (to_b_signed &x) with | Negative p | Zero | Positive p end |- t.
    - let proof r := conversion.boundedness.negative &x &p &t.
      lemma below : ((p /. &d) < 1000000000000000)%b0.
      {
        match &r with | same | smaller end.
        - match &d with | One | b0 d' | b1 d' end.
          + let proof g := congru Bin0.to_bin_base, &same.
            simpl Bin0.to_bin_base in &g.
            let proof k := Option.some.injectivity &g.
            leibniz &k in &h.
            ex
              (&h
                (conjoin
                  (refl (-1000000000000000)%b_signed),
                  (refl BinBase.One)))
              quodlibet.
          + lemma differ : ~ (BinBase.b0 &d' = BinBase.One).
            {
              intro k.
              ex &k quodlibet.
            }
            leibniz <- &same in |- *.
            ipso (Bin0.division.quotient.strict.boundedness &p (BinBase.b0 &d') &differ).
          + lemma differ : ~ (BinBase.b1 &d' = BinBase.One).
            {
              intro k.
              ex &k quodlibet.
            }
            leibniz <- &same in |- *.
            ipso (Bin0.division.quotient.strict.boundedness &p (BinBase.b1 &d') &differ).
        - ipso
            (Comparable.order.mixed.left.transitivity
              (Bin0.division.quotient.boundedness p &d) &smaller).
      }
      simpl SignedBin.divide in |- *.
      leibniz (SignedBin.negation.involution (SignedBin.from_b0 (p /. &d)%b0)) in |- *.
      ipso (conversion.retraction.nonnegative (p /. &d)%b0 &below).
    - simpl SignedBin.divide, SignedBin.negate in |- *.
      ipso &origin.
    - let proof r := conversion.boundedness.positive &x &p &t.
      let proof b := Bin0.division.quotient.boundedness p &d.
      simpl SignedBin.divide in |- *.
      match ((p /. &d)%b0) with | Zero | Positive q end |- f.
      + simpl SignedBin.from_b0, SignedBin.negate in |- *.
        ipso &origin.
      + simpl SignedBin.from_b0, SignedBin.negate in |- *.
        lemma bounded : (q <= 1000000000000000)%b0.
        {
          simpl Bin0.LessOrEqual in |- *.
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

Module hword. (* conversion.hword *)

(* conversion.hword.retraction *)
Theorem retraction : forall (w : HWord) . to_hword (HWord.endian w) (from_hword w) = w.
Proof.
  intros w.
  match &w with | introduction e b0 b1 end.
  match &e with | Little | Big end;
    simpl from_hword, to_hword in |- *;
    simpl in |- *;
    quod idem est.
Qed.

(* conversion.hword.section *)
Theorem section : forall (e : Endian) (x : Int16) . from_hword (to_hword e x) = x.
Proof.
  intros e x.
  match &x with | introduction b1 b0 end.
  match &e with | Little | Big end;
    simpl from_hword, to_hword in |- *;
    simpl in |- *;
    quod idem est.
Qed.

End hword. (* conversion.hword *)

End conversion. (* conversion *)

(* [Int16] as a [Signed.Width]: its operations, the laws above, and its
 * constants, 2^15, 2^16 and 3 * 2^15. The facts about fixed values are closed
 * computations, checked by the kernel.
 *)
Module Width <: Signed.Width.

Definition T := T.
Definition Zero := Zero.
Definition One := One.
Definition Min := Min.
Definition Max := Max.
Definition to_b_signed := to_b_signed.
Definition from_b_signed := from_b_signed.
Definition from_b0 := from_b0.
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
Definition mul := mul.
Definition mul_with_overflow := mul_with_overflow.
Definition half := 1000000000000000%bin_base.
Definition modulus := modulus.
Definition beyond := 11000000000000000%bin_base.

Module order. (* Width.order *)

Module strict. (* Width.order.strict *)

Theorem specification : forall (x : T) (y : T) . LessThan x y <-> (to_b_signed x < to_b_signed y)%b_signed.
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

Definition section := Int16.conversion.section.

Theorem comparison
  : forall (x : T) (y : T) . compare x y = SignedBin.compare (to_b_signed x) (to_b_signed y).
Proof.
  intros x y.
  ipso (refl (compare &x &y)).
Qed.

Definition addition := Int16.conversion.addition.
Definition difference := Int16.conversion.difference.

Module forward. (* Width.conversion.forward *)

Theorem specification
  : forall (x : T) .
      to_b_signed x
      = SignedBin.b0_difference (unsigned_value x)
          (Bin0.Positive modulus * Bit.to_b0 (sign_bit x))%b0.
Proof.
  intro x.
  ipso (refl (to_b_signed &x)).
Qed.

End forward. (* Width.conversion.forward *)

Module backward. (* Width.conversion.backward *)

Theorem specification
  : forall (z : SignedBin) .
      from_b_signed z
      = add (from_b0 (SignedBin.ramp z))
          (negate (from_b0 (SignedBin.ramp (SignedBin.negate z)))).
Proof.
  intro z.
  ipso (refl (from_b_signed &z)).
Qed.

End backward. (* Width.conversion.backward *)

Module boundedness. (* Width.conversion.boundedness *)

Definition positive := Int16.conversion.boundedness.positive.
Definition negative := Int16.conversion.boundedness.negative.

End boundedness. (* Width.conversion.boundedness *)

Module retraction. (* Width.conversion.retraction *)

Definition nonnegative := Int16.conversion.retraction.nonnegative.
Definition negative := Int16.conversion.retraction.negative.

End retraction. (* Width.conversion.retraction *)

End conversion. (* Width.conversion *)

Module reinterpretation. (* Width.reinterpretation *)

Definition boundedness := Int16.reinterpretation.boundedness.
Definition injectivity := @Int16.reinterpretation.injectivity.
Definition multiplication := Int16.reinterpretation.multiplication.
Definition reduction := Int16.reinterpretation.reduction.

Module reduction. (* Width.reinterpretation.reduction *)

Definition additivity := Int16.reinterpretation.reduction.additivity.

Theorem zero : from_b0 Bin0.Zero = Zero.
Proof.
  ipso (refl Zero).
Qed.

End reduction. (* Width.reinterpretation.reduction *)

End reinterpretation. (* Width.reinterpretation *)

Module addition. (* Width.addition *)

Definition associativity := Int16.addition.associativity.
Definition commutativity := Int16.addition.commutativity.
Definition identity := Int16.addition.identity.
Definition inverse := Int16.addition.inverse.

End addition. (* Width.addition *)

Module multiplication. (* Width.multiplication *)

Definition annihilation := Int16.multiplication.annihilation.

Module left. (* Width.multiplication.left *)

Definition negation := Int16.multiplication.left.negation.

End left. (* Width.multiplication.left *)

Module right. (* Width.multiplication.right *)

Definition negation := Int16.multiplication.right.negation.

End right. (* Width.multiplication.right *)

End multiplication. (* Width.multiplication *)

Module subtraction. (* Width.subtraction *)

Definition specification := Int16.subtraction.specification.

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

Module multiplication. (* Width.flag.multiplication *)

Theorem specification
  : forall (x : T) (y : T) .
      mul_with_overflow x y
      = (match SignedBin.compare (to_b_signed x * to_b_signed y)%b_signed (to_b_signed Min) with
         | Comparison.Lt => 1%bit
         | Comparison.Eq => 0%bit
         | Comparison.Gt =>
             match SignedBin.compare (to_b_signed x * to_b_signed y)%b_signed (to_b_signed Max) with
             | Comparison.Lt => 0%bit
             | Comparison.Eq => 0%bit
             | Comparison.Gt => 1%bit
             end
         end,
         mul x y)%product.
Proof.
  intros x y.
  ipso (refl (mul_with_overflow &x &y)).
Qed.

End multiplication. (* Width.flag.multiplication *)

End flag. (* Width.flag *)

Module minimum. (* Width.minimum *)

Theorem specification : to_b_signed Min = SignedBin.Negative half.
Proof.
  ipso (refl (SignedBin.Negative half)).
Qed.

Theorem negation : negate Min = Min.
Proof.
  ipso (refl Min).
Qed.

End minimum. (* Width.minimum *)

Module maximum. (* Width.maximum *)

Theorem specification : (to_b_signed Max + 1 = SignedBin.Positive half)%b_signed.
Proof.
  ipso (refl (SignedBin.Positive half)).
Qed.

Theorem positivity : (0 < to_b_signed Max)%b_signed.
Proof.
  simpl SignedBin.LessThan in |- *.
  exists 111111111111111%bin_base.
  ipso (refl (to_b_signed Max)).
Qed.

End maximum. (* Width.maximum *)

Module one. (* Width.one *)

Theorem specification : to_b_signed One = 1%b_signed.
Proof.
  ipso (refl 1%b_signed).
Qed.

End one. (* Width.one *)

Module modulus. (* Width.modulus *)

Theorem specification : (SignedBin.Positive modulus = SignedBin.Positive half + SignedBin.Positive half)%b_signed.
Proof.
  ipso (refl (SignedBin.Positive modulus)).
Qed.

Theorem wrapping : from_b_signed (SignedBin.Positive modulus) = Zero.
Proof.
  ipso (refl Zero).
Qed.

End modulus. (* Width.modulus *)

Module beyond. (* Width.beyond *)

Theorem specification : (SignedBin.Positive beyond = SignedBin.Positive modulus + SignedBin.Positive half)%b_signed.
Proof.
  ipso (refl (SignedBin.Positive beyond)).
Qed.

End beyond. (* Width.beyond *)

End Width.

Include Signed.Laws Width.

Instance comparable
  : Comparable compare (<) :=
  {| Comparable.transitivity := @order.strict.transitivity
  ; Comparable.specification := comparison.specification
  ; Comparable.antisymmetry := comparison.antisymmetry |}.

End Int16. (* Int16 *)

Abbreviation Int16 := Int16.T.

Export (notations) Int16.

(* A number of the type is written in decimal or hexadecimal under its
 * scope, [100%int16], [(-100)%int16] or [0x7F%int16], and a closed one prints
 * in decimal.
 *)
Number Notation Int16.T Int16.from_numeral Int16.to_numeral
  : jw_int16_scope.

(* Where an [Int16] is expected, a literal or a notation reads in this scope
 * without its [%int16].
 *)
Bind Scope jw_int16_scope with Int16.T.

(* An [Int16] stands wherever a [SignedBin] is expected, read as its value in two's
 * complement, and wherever an [Integer] is, through that value; each
 * conversion is printed where it happened.
 *)
Coercion Int16.to_b_signed : Int16 >-> SignedBin.
Add Printing Coercion Int16.to_b_signed.
Coercion Int16.to_integer : Int16 >-> Integer.
Add Printing Coercion Int16.to_integer.

(* Declared inside [Module Int16]; an instance declared there is dropped at
 * the module's [End], so it is announced again here.
 *)
Existing Instance Int16.comparable.

Instance Int16_add_monoid
  : Monoid Int16.add Int16.Zero :=
  {| Monoid.semigroup :=
      {| Semigroup.associativity := Int16.addition.associativity |}
  ; Monoid.identity := Int16.addition.identity |}.

Instance Int16_mul_monoid
  : Monoid Int16.mul Int16.One :=
  {| Monoid.semigroup :=
      {| Semigroup.associativity := Int16.multiplication.associativity |}
  ; Monoid.identity := Int16.multiplication.identity |}.

Instance Int16_add_commutative
  : Commutative Int16.add :=
  {| Commutative.commutativity := Int16.addition.commutativity |}.

Instance Int16_mul_commutative
  : Commutative Int16.mul :=
  {| Commutative.commutativity := Int16.multiplication.commutativity |}.

Instance Int16_add_group
  : Group Int16.add Int16.Zero Int16.negate :=
  {| Group.monoid := Int16_add_monoid
  ; Group.inverse := Int16.addition.inverse |}.

Instance Int16_add_abelian_group
  : AbelianGroup Int16.add Int16.Zero Int16.negate :=
  {| AbelianGroup.group := Int16_add_group
  ; AbelianGroup.commutative := Int16_add_commutative |}.

Instance Int16_ring
  : Ring Int16.add Int16.Zero Int16.negate Int16.mul Int16.One :=
  {| Ring.abelian_group := Int16_add_abelian_group
  ; Ring.monoid := Int16_mul_monoid
  ; Ring.distributivity := Int16.multiplication.distributivity.over.addition |}.
