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
From JW Require Import Data.Discernible.
From JW Require Import Data.Machine.Bit.
From JW Require Import Data.Machine.Byte.
From JW Require Import Data.Machine.Endian.
From JW Require Import Data.Machine.Modular.
From JW Require Import Data.Machine.Signed.
From JW Require Import Data.Machine.Word.
From JW Require Import Data.Number.Binary.SignedBin.
From JW Require Import Data.Number.Binary.Bin.
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

Local Unset Elimination Schemes.

(* A signed integer of thirty-two bits: four [Byte]s read in two's complement,
 * from -2147483648 (-2^31) to 2147483647 (2^31 - 1), its arithmetic wrapping
 * modulo 4294967296 (2^32). In this file [100000000000000000000000000000000] is
 * 2^32, [10000000000000000000000000000000] is 2^31 and
 * [1111111111111111111111111111111] is 2^31 - 1, written in binary digits.
 *)

Module Int32. (* Int32 *)

Inductive T : Type :=
  | introduction : Byte -> Byte -> Byte -> Byte -> T.

Abbreviation Int32 := T.

(* The number of values, 4294967296 (2^32), the arithmetic wrapping modulo it. *)
(* [Bin] *)
Definition modulus := 100000000000000000000000000000000%b.

(* [x] laid out as a [Word] in the order [e] names. *)
(* [Endian -> Int32 -> Word] *)
Definition to_word := fun (e : Endian) (x : Int32) .
  match x with
  | Int32.introduction b3 b2 b1 b0 => Word.make e b0 b1 b2 b3
  end.

(* The value of the bytes of [w], whatever the order they are laid out in. *)
(* [Word -> Int32] *)
Definition from_word := fun (w : Word) .
  Int32.introduction (Word.byte3 w) (Word.byte2 w) (Word.byte1 w) (Word.byte0 w).

(* The bits read as a number in base two, the most significant first, from 0 to
 * 4294967295: the value of the bit pattern, through which the arithmetic is
 * proved and from which [to_b_signed] takes the signed value; [10] is two in binary
 * digits.
 *)
(* [Int32 -> Bin0] *)
Definition unsigned_value := fun (x : Int32) .
  match x with
  | Int32.introduction (Byte.introduction x31 x30 x29 x28 x27 x26 x25 x24)
      (Byte.introduction x23 x22 x21 x20 x19 x18 x17 x16)
      (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8)
      (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
      (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (
        10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (
        10 * Bit.to_b0 x31 + Bit.to_b0 x30) + Bit.to_b0 x29)
        + Bit.to_b0 x28) + Bit.to_b0 x27) + Bit.to_b0 x26)
        + Bit.to_b0 x25) + Bit.to_b0 x24) + Bit.to_b0 x23)
        + Bit.to_b0 x22) + Bit.to_b0 x21) + Bit.to_b0 x20)
        + Bit.to_b0 x19) + Bit.to_b0 x18) + Bit.to_b0 x17)
        + Bit.to_b0 x16) + Bit.to_b0 x15) + Bit.to_b0 x14)
        + Bit.to_b0 x13) + Bit.to_b0 x12) + Bit.to_b0 x11)
        + Bit.to_b0 x10) + Bit.to_b0 x9) + Bit.to_b0 x8)
        + Bit.to_b0 x7) + Bit.to_b0 x6) + Bit.to_b0 x5)
        + Bit.to_b0 x4) + Bit.to_b0 x3) + Bit.to_b0 x2)
        + Bit.to_b0 x1) + Bit.to_b0 x0)%b0
  end.

(* The top bit, [1] for a negative value. *)
(* [Int32 -> Bit] *)
Definition sign_bit := fun (x : Int32) .
  match x with
  | Int32.introduction (Byte.introduction x31 _ _ _ _ _ _ _) _ _ _ => x31
  end.

(* The value in two's complement: the unsigned value, less 4294967296 when the
 * sign bit is set.
 *)
(* [Int32 -> SignedBin] *)
Definition to_b_signed := fun (x : Int32) .
  SignedBin.b0_difference
    (unsigned_value x) (modulus * Bit.to_b0 (sign_bit x))%b0.

(* From here to the end of the module an [Int32] stands where a [SignedBin] is expected,
 * read as its value; the conversion is printed.
 *)
Local Coercion to_b_signed : T >-> SignedBin.
Add Printing Coercion to_b_signed.

(* The value in [Integer], through [to_b_signed]; [Integer] is unary, so it is for
 * stating and proving, and computing goes through [to_b_signed].
 *)
(* [Int32 -> Integer] *)
Definition to_integer := fun (x : Int32) . SignedBin.to_integer (to_b_signed x).

(* [Int32] *)
Definition Zero := Int32.introduction Byte.Zero Byte.Zero Byte.Zero Byte.Zero.

(* [Int32] *)
Definition One :=
  Int32.introduction
    Byte.Zero
    Byte.Zero
    Byte.Zero
    (Byte.introduction
      0 0 0 0 0 0 0 1).

(* The least value, -2147483648: only the sign bit set. *)
(* [Int32] *)
Definition Min :=
  Int32.introduction
    (Byte.introduction
      1 0 0 0 0 0 0 0)
    Byte.Zero
    Byte.Zero
    Byte.Zero.

(* The greatest value, 2147483647: every bit but the sign bit set. *)
(* [Int32] *)
Definition Max :=
  Int32.introduction
    (Byte.introduction
      0 1 1 1 1 1 1 1)
    (Byte.introduction
      1 1 1 1 1 1 1 1)
    (Byte.introduction
      1 1 1 1 1 1 1 1)
    (Byte.introduction
      1 1 1 1 1 1 1 1).

(* [k] places toward the most significant end, a 0 coming in at the
 * other; one place first, then [k - 1].
 *)
(* [Int32 -> Nat -> Int32] *)
Fixpoint shift_left_nat (x : Int32) (k : Nat) : Int32 :=
  let y :=
    match x with
    | Int32.introduction (Byte.introduction _ x30 x29 x28 x27 x26 x25 x24)
        (Byte.introduction x23 x22 x21 x20 x19 x18 x17 x16)
        (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8)
        (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
        Int32.introduction (Byte.introduction x30 x29 x28 x27 x26 x25 x24 x23)
          (Byte.introduction x22 x21 x20 x19 x18 x17 x16 x15)
          (Byte.introduction x14 x13 x12 x11 x10 x9 x8 x7)
          (Byte.introduction x6 x5 x4 x3 x2 x1 x0 0)
    end in
  match k with
  | Nat.One          => y
  | Nat.Successor k' => shift_left_nat y k'
  end.

(* [Int32 -> Nat0 -> Int32] *)
Definition shift_left := fun (x : Int32) (k : Nat0) .
  match k with
  | Nat0.Zero       => x
  | Nat0.Positive n => shift_left_nat x n
  end.

(* [k] places toward the least significant end, the sign bit copied in at
 * the other; one place first, then [k - 1].
 *)
(* [Int32 -> Nat -> Int32] *)
Fixpoint shift_right_nat (x : Int32) (k : Nat) : Int32 :=
  let y :=
    match x with
    | Int32.introduction (Byte.introduction x31 x30 x29 x28 x27 x26 x25 x24)
        (Byte.introduction x23 x22 x21 x20 x19 x18 x17 x16)
        (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8)
        (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
        Int32.introduction (Byte.introduction x31 x31 x30 x29 x28 x27 x26 x25)
          (Byte.introduction x24 x23 x22 x21 x20 x19 x18 x17)
          (Byte.introduction x16 x15 x14 x13 x12 x11 x10 x9)
          (Byte.introduction x8 x7 x6 x5 x4 x3 x2 x1)
    end in
  match k with
  | Nat.One          => y
  | Nat.Successor k' => shift_right_nat y k'
  end.

(* [Int32 -> Nat0 -> Int32] *)
Definition shift_right := fun (x : Int32) (k : Nat0) .
  match k with
  | Nat0.Zero       => x
  | Nat0.Positive n => shift_right_nat x n
  end.

(* [x] with [b] written after its lowest bit, the highest bit dropped. *)
(* [Bit -> Int32 -> Int32] *)
Definition append_bit := fun (b : Bit) (x : Int32) .
  match x with
  | Int32.introduction (Byte.introduction _ x30 x29 x28 x27 x26 x25 x24)
      (Byte.introduction x23 x22 x21 x20 x19 x18 x17 x16)
      (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8)
      (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
      Int32.introduction (Byte.introduction x30 x29 x28 x27 x26 x25 x24 x23)
        (Byte.introduction x22 x21 x20 x19 x18 x17 x16 x15)
        (Byte.introduction x14 x13 x12 x11 x10 x9 x8 x7)
        (Byte.introduction x6 x5 x4 x3 x2 x1 x0 b)
  end.

(* The carry out and the sum of [carry + x + y], the carry rippling up from
 * the least significant place.
 *)
(* [Bit -> Int32 -> Int32 -> Product Bit Int32] *)
Definition add_with_carry := fun (carry : Bit) (x : Int32) (y : Int32) .
  match x with
  | Int32.introduction (Byte.introduction x31 x30 x29 x28 x27 x26 x25 x24)
      (Byte.introduction x23 x22 x21 x20 x19 x18 x17 x16)
      (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8)
      (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
      match y with
      | Int32.introduction (Byte.introduction y31 y30 y29 y28 y27 y26 y25 y24)
          (Byte.introduction y23 y22 y21 y20 y19 y18 y17 y16)
          (Byte.introduction y15 y14 y13 y12 y11 y10 y9 y8)
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
          let r16 := Bit.add_with_carry (pi_1 r15) x16 y16 in
          let r17 := Bit.add_with_carry (pi_1 r16) x17 y17 in
          let r18 := Bit.add_with_carry (pi_1 r17) x18 y18 in
          let r19 := Bit.add_with_carry (pi_1 r18) x19 y19 in
          let r20 := Bit.add_with_carry (pi_1 r19) x20 y20 in
          let r21 := Bit.add_with_carry (pi_1 r20) x21 y21 in
          let r22 := Bit.add_with_carry (pi_1 r21) x22 y22 in
          let r23 := Bit.add_with_carry (pi_1 r22) x23 y23 in
          let r24 := Bit.add_with_carry (pi_1 r23) x24 y24 in
          let r25 := Bit.add_with_carry (pi_1 r24) x25 y25 in
          let r26 := Bit.add_with_carry (pi_1 r25) x26 y26 in
          let r27 := Bit.add_with_carry (pi_1 r26) x27 y27 in
          let r28 := Bit.add_with_carry (pi_1 r27) x28 y28 in
          let r29 := Bit.add_with_carry (pi_1 r28) x29 y29 in
          let r30 := Bit.add_with_carry (pi_1 r29) x30 y30 in
          let r31 := Bit.add_with_carry (pi_1 r30) x31 y31 in
          (pi_1 r31,
            Int32.introduction
              (Byte.introduction
                (pi_2 r31) (pi_2 r30) (pi_2 r29) (pi_2 r28)
                (pi_2 r27) (pi_2 r26) (pi_2 r25) (pi_2 r24))
              (Byte.introduction
                (pi_2 r23) (pi_2 r22) (pi_2 r21) (pi_2 r20)
                (pi_2 r19) (pi_2 r18) (pi_2 r17) (pi_2 r16))
              (Byte.introduction
                (pi_2 r15) (pi_2 r14) (pi_2 r13) (pi_2 r12)
                (pi_2 r11) (pi_2 r10) (pi_2 r9) (pi_2 r8))
              (Byte.introduction
                (pi_2 r7) (pi_2 r6) (pi_2 r5) (pi_2 r4)
                (pi_2 r3) (pi_2 r2) (pi_2 r1) (pi_2 r0)))
      end
  end%product.

(* [Int32 -> Int32 -> Int32] *)
Definition add := fun (x : Int32) (y : Int32) . (pi_2 (add_with_carry 0 x y))%product.

(* [only parsing] keeps goals printing the operations by name. *)
Notation "x + y" := (add x y) (only parsing)
  : jw_int32_scope.

(* The borrow out and the difference of [x - y - borrow], the borrow
 * rippling up as the carry does in [add_with_carry].
 *)
(* [Bit -> Int32 -> Int32 -> Product Bit Int32] *)
Definition sub_with_borrow := fun (borrow : Bit) (x : Int32) (y : Int32) .
  match x with
  | Int32.introduction (Byte.introduction x31 x30 x29 x28 x27 x26 x25 x24)
      (Byte.introduction x23 x22 x21 x20 x19 x18 x17 x16)
      (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8)
      (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
      match y with
      | Int32.introduction (Byte.introduction y31 y30 y29 y28 y27 y26 y25 y24)
          (Byte.introduction y23 y22 y21 y20 y19 y18 y17 y16)
          (Byte.introduction y15 y14 y13 y12 y11 y10 y9 y8)
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
          let r16 := Bit.sub_with_borrow (pi_1 r15) x16 y16 in
          let r17 := Bit.sub_with_borrow (pi_1 r16) x17 y17 in
          let r18 := Bit.sub_with_borrow (pi_1 r17) x18 y18 in
          let r19 := Bit.sub_with_borrow (pi_1 r18) x19 y19 in
          let r20 := Bit.sub_with_borrow (pi_1 r19) x20 y20 in
          let r21 := Bit.sub_with_borrow (pi_1 r20) x21 y21 in
          let r22 := Bit.sub_with_borrow (pi_1 r21) x22 y22 in
          let r23 := Bit.sub_with_borrow (pi_1 r22) x23 y23 in
          let r24 := Bit.sub_with_borrow (pi_1 r23) x24 y24 in
          let r25 := Bit.sub_with_borrow (pi_1 r24) x25 y25 in
          let r26 := Bit.sub_with_borrow (pi_1 r25) x26 y26 in
          let r27 := Bit.sub_with_borrow (pi_1 r26) x27 y27 in
          let r28 := Bit.sub_with_borrow (pi_1 r27) x28 y28 in
          let r29 := Bit.sub_with_borrow (pi_1 r28) x29 y29 in
          let r30 := Bit.sub_with_borrow (pi_1 r29) x30 y30 in
          let r31 := Bit.sub_with_borrow (pi_1 r30) x31 y31 in
          (pi_1 r31,
            Int32.introduction
              (Byte.introduction
                (pi_2 r31) (pi_2 r30) (pi_2 r29) (pi_2 r28)
                (pi_2 r27) (pi_2 r26) (pi_2 r25) (pi_2 r24))
              (Byte.introduction
                (pi_2 r23) (pi_2 r22) (pi_2 r21) (pi_2 r20)
                (pi_2 r19) (pi_2 r18) (pi_2 r17) (pi_2 r16))
              (Byte.introduction
                (pi_2 r15) (pi_2 r14) (pi_2 r13) (pi_2 r12)
                (pi_2 r11) (pi_2 r10) (pi_2 r9) (pi_2 r8))
              (Byte.introduction
                (pi_2 r7) (pi_2 r6) (pi_2 r5) (pi_2 r4)
                (pi_2 r3) (pi_2 r2) (pi_2 r1) (pi_2 r0)))
      end
  end%product.

(* [Int32 -> Int32 -> Int32] *)
Definition sub := fun (x : Int32) (y : Int32) . (pi_2 (sub_with_borrow 0 x y))%product.

Notation "x - y" := (sub x y) (only parsing)
  : jw_int32_scope.

(* [x] taken from [Zero], wrapping. *)
(* [Int32 -> Int32] *)
Definition negate := fun (x : Int32) . sub Zero x.

(* Also what makes the minus of a negative literal parse: [Numeral.Signed]
 * lets [from_numeral] receive a sign but puts none in the grammar.
 *)
Notation "- x" := (negate x)
  (at level 35, right associativity, only parsing)
  : jw_int32_scope.

(* [y]'s bits from the most significant, each step doubling the product so
 * far and adding [x] for a 1, all modulo 4294967296.
 *)
(* [Int32 -> Int32 -> Int32] *)
Definition mul := fun (x : Int32) (y : Int32) .
  let step := fun (p : Int32) (b : Bit) .
    add (shift_left p 1%n0)
      match b with
      | 0%bit => Zero
      | 1%bit => x
      end in
  match y with
  | Int32.introduction (Byte.introduction y31 y30 y29 y28 y27 y26 y25 y24)
      (Byte.introduction y23 y22 y21 y20 y19 y18 y17 y16)
      (Byte.introduction y15 y14 y13 y12 y11 y10 y9 y8)
      (Byte.introduction y7 y6 y5 y4 y3 y2 y1 y0) =>
      step (step (step (step (step (step (step (step (step (step (step (step (step (step (step (step
        (step (step (step (step (step (step (step (step (step (step (step (step (step (step (step
        (step Zero y31) y30) y29) y28) y27) y26) y25) y24) y23) y22) y21) y20) y19) y18) y17) y16)
        y15) y14) y13) y12) y11) y10) y9) y8) y7) y6) y5) y4) y3) y2) y1) y0
  end.

Notation "x * y" := (mul x y) (only parsing)
  : jw_int32_scope.

(* The flag and the wrapped product: the flag is set when the product of the
 * signed values lies outside the range, below [Min] or above [Max].
 *)
(* [Int32 -> Int32 -> Product Bit Int32] *)
Definition mul_with_overflow := fun (x : Int32) (y : Int32) .
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

(* The bit pattern of [p] modulo 4294967296, its bits appended from the most
 * significant.
 *)
(* [Bin -> Int32] *)
Fixpoint from_b (p : Bin) : Int32 :=
  match p with
  | Bin.One   => One
  | Bin.b0 p' => append_bit 0 (from_b p')
  | Bin.b1 p' => append_bit 1 (from_b p')
  end.

(* [Bin0 -> Int32] *)
Definition from_b0 := fun (n : Bin0) .
  match n with
  | Bin0.Zero       => Zero
  | Bin0.Positive p => from_b p
  end.

(* [Nat -> Int32] *)
Definition from_nat := fun (n : Nat) . from_b (Bin.from_nat n).

(* [Nat0 -> Int32] *)
Definition from_nat0 := fun (n : Nat0) . from_b0 (Bin0.from_nat0 n).

(* [z] modulo 4294967296 into the range -2147483648 to 2147483647: its positive
 * part less its negative part, wrapping.
 *)
(* [SignedBin -> Int32] *)
Definition from_b_signed := fun (z : SignedBin) .
  add (from_b0 (SignedBin.ramp z)) (negate (from_b0 (SignedBin.ramp (SignedBin.negate z)))).

(* The quotient through [SignedBin], toward zero, [None] when [y] is zero. [SignedBin.divide]
 * takes a positive divisor, so the divisor's sign is matched here; -2147483648
 * (-2^31) over -1 wraps to itself.
 *)
(* [Int32 -> Int32 -> Option Int32] *)
Definition divide := fun (x : Int32) (y : Int32) .
  match to_b_signed y with
  | SignedBin.Negative d => Some (from_b_signed (SignedBin.negate (x /. d)%b_signed))
  | SignedBin.Zero       => None
  | SignedBin.Positive d => Some (from_b_signed (x /. d)%b_signed)
  end.

Notation "x /. y" := (divide x y) (only parsing)
  : jw_int32_scope.

(* [x] modulo 4294967296 into the range -2147483648 to 2147483647. *)
(* [Integer -> Int32] *)
Definition from_integer := fun (x : Integer) .
  match x with
  | Integer.Negative p => negate (from_nat p)
  | Integer.Zero       => Zero
  | Integer.Positive p => from_nat p
  end.

(* The overflow flag and the sum of [x + y]: the flag is set when [x] and [y]
 * have the same sign and the sum the other, the true sum lying past -2147483648
 * or 2147483647.
 *)
(* [Int32 -> Int32 -> Product Bit Int32] *)
Definition add_with_overflow := fun (x : Int32) (y : Int32) .
  let flag :=
    Bit.and
      (Bit.flip (Bit.xor (sign_bit x) (sign_bit y)))
      (Bit.xor (sign_bit (add x y)) (sign_bit x)) in
  (flag, add x y)%product.

(* The overflow flag and the difference of [x - y]: the flag is set when [x]
 * and [y] have different signs and the difference has the sign of [y], the
 * true difference lying past -2147483648 or 2147483647.
 *)
(* [Int32 -> Int32 -> Product Bit Int32] *)
Definition sub_with_overflow := fun (x : Int32) (y : Int32) .
  let flag :=
    Bit.and
      (Bit.xor (sign_bit x) (sign_bit y))
      (Bit.xor (sign_bit (sub x y)) (sign_bit x)) in
  (flag, sub x y)%product.

(* [Int32 -> Int32 -> Prop] *)
Definition LessThan := fun (x : Int32) (y : Int32) . (to_b_signed x < to_b_signed y)%b_signed.

Notation "x < y" := (LessThan x y) (only parsing)
  : jw_int32_scope.

(* [Int32 -> Int32 -> Prop] *)
Definition LessOrEqual := fun (x : Int32) (y : Int32) . x = y \/ LessThan x y.

Notation "x <= y" := (LessOrEqual x y) (only parsing)
  : jw_int32_scope.

Notation "x > y" := (LessThan y x) (only parsing)
  : jw_int32_scope.
Notation "x >= y" := (LessOrEqual y x) (only parsing)
  : jw_int32_scope.

Notation "'(<)'" := LessThan (only parsing)
  : jw_int32_scope.
Notation "'(<=)'" := LessOrEqual (only parsing)
  : jw_int32_scope.

(* [Int32 -> Int32 -> Comparison] *)
Definition compare := fun (x : Int32) (y : Int32) . SignedBin.compare (to_b_signed x) (to_b_signed y).

(* [Int32 -> Int32 -> Bool] *)
Abbreviation eq := (Comparable.eq compare).

(* [Int32 -> Int32 -> Bool] *)
Abbreviation le := (Comparable.le compare).

(* [Int32 -> Int32 -> Bool] *)
Abbreviation lt := (Comparable.lt compare).

(* [Int32 -> Int32 -> Bool] *)
Abbreviation ge := (Comparable.ge compare).

(* [Int32 -> Int32 -> Bool] *)
Abbreviation gt := (Comparable.gt compare).

(* [Int32 -> Int32 -> Int32] *)
Abbreviation min := (Comparable.min compare).

(* [Int32 -> Int32 -> Int32] *)
Abbreviation max := (Comparable.max compare).

(* [Int32 -> Int32 -> Bool] *)
Abbreviation equivalent := Discernible.equivalent.

(* [Int32 -> Int32 -> Bool] *)
Abbreviation discern := Discernible.discern.

(* A literal of -2147483648 to 2147483647, in decimal or hexadecimal, read in
 * binary; any wider is refused.
 *)
(* [Numeral.Signed -> Option Int32] *)
Definition from_numeral := fun (s : Numeral.Signed) .
  let positive := fun (v : Bin0) .
    match Bin0.compare v 1111111111111111111111111111111%b0 with
    | Comparison.Lt => Some (from_b0 v)
    | Comparison.Eq => Some (from_b0 v)
    | Comparison.Gt => None
    end in
  let negative := fun (v : Bin0) .
    match Bin0.compare v 10000000000000000000000000000000%b0 with
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
(* [Int32 -> Numeral.Signed] *)
Definition to_numeral := fun (x : Int32) .
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

Local Open Scope jw_int32_scope.

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
Theorem boundedness : forall (x : Int32) . (unsigned_value x < modulus)%b0.
Proof.
  intros x.
  match &x with | introduction xb3 xb2 xb1 xb0 end.
  match &xb3 with | introduction x31 x30 x29 x28 x27 x26 x25 x24 end.
  match &xb2 with | introduction x23 x22 x21 x20 x19 x18 x17 x16 end.
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
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness &x31)))))))))))))))))))))))))))))))).
Qed.

(* reinterpretation.injectivity *)
Theorem injectivity
  : forall {x : Int32} {y : Int32} . unsigned_value x = unsigned_value y -> x = y.
Proof.
  intros x y e.
  match &x with | introduction xb3 xb2 xb1 xb0 end.
  match &xb3 with | introduction x31 x30 x29 x28 x27 x26 x25 x24 end.
  match &xb2 with | introduction x23 x22 x21 x20 x19 x18 x17 x16 end.
  match &xb1 with | introduction x15 x14 x13 x12 x11 x10 x9 x8 end.
  match &xb0 with | introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | introduction yb3 yb2 yb1 yb0 end.
  match &yb3 with | introduction y31 y30 y29 y28 y27 y26 y25 y24 end.
  match &yb2 with | introduction y23 y22 y21 y20 y19 y18 y17 y16 end.
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
  match (Bit.conversion.binary.halving.injectivity &e15) with | e16 b15 end.
  match (Bit.conversion.binary.halving.injectivity &e16) with | e17 b16 end.
  match (Bit.conversion.binary.halving.injectivity &e17) with | e18 b17 end.
  match (Bit.conversion.binary.halving.injectivity &e18) with | e19 b18 end.
  match (Bit.conversion.binary.halving.injectivity &e19) with | e20 b19 end.
  match (Bit.conversion.binary.halving.injectivity &e20) with | e21 b20 end.
  match (Bit.conversion.binary.halving.injectivity &e21) with | e22 b21 end.
  match (Bit.conversion.binary.halving.injectivity &e22) with | e23 b22 end.
  match (Bit.conversion.binary.halving.injectivity &e23) with | e24 b23 end.
  match (Bit.conversion.binary.halving.injectivity &e24) with | e25 b24 end.
  match (Bit.conversion.binary.halving.injectivity &e25) with | e26 b25 end.
  match (Bit.conversion.binary.halving.injectivity &e26) with | e27 b26 end.
  match (Bit.conversion.binary.halving.injectivity &e27) with | e28 b27 end.
  match (Bit.conversion.binary.halving.injectivity &e28) with | e29 b28 end.
  match (Bit.conversion.binary.halving.injectivity &e29) with | e30 b29 end.
  match (Bit.conversion.binary.halving.injectivity &e30) with | e31 b30 end.
  leibniz
    &b0, &b1, &b2, &b3, &b4, &b5, &b6, &b7, &b8, &b9, &b10, &b11, &b12, &b13, &b14, &b15, &b16,
    &b17, &b18, &b19, &b20, &b21, &b22, &b23, &b24, &b25, &b26, &b27, &b28, &b29, &b30,
    (Bit.conversion.binary.injectivity &e31)
    in |- *.
  quod idem est.
Qed.

(* The numbers are added place by place from the most significant, each
 * place one [Bit.conversion.binary.carry.propagation] around the places
 * above it.
 *)
(* reinterpretation.carry *)
Theorem carry
  : forall (carry : Bit) (x : Int32) (y : Int32) .
      (Bit.to_b0 carry + unsigned_value x + unsigned_value y
        = modulus * Bit.to_b0 (pi_1 (add_with_carry carry x y))%product
          + unsigned_value (pi_2 (add_with_carry carry x y))%product)%b0.
Proof.
  intros carry x y.
  match &x with | introduction xb3 xb2 xb1 xb0 end.
  match &xb3 with | introduction x31 x30 x29 x28 x27 x26 x25 x24 end.
  match &xb2 with | introduction x23 x22 x21 x20 x19 x18 x17 x16 end.
  match &xb1 with | introduction x15 x14 x13 x12 x11 x10 x9 x8 end.
  match &xb0 with | introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | introduction yb3 yb2 yb1 yb0 end.
  match &yb3 with | introduction y31 y30 y29 y28 y27 y26 y25 y24 end.
  match &yb2 with | introduction y23 y22 y21 y20 y19 y18 y17 y16 end.
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
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry _ &x31 &y31)))))))))))))))))))))))))))))))).
Qed.

(* reinterpretation.borrow *)
Theorem borrow
  : forall (borrow : Bit) (x : Int32) (y : Int32) .
      (unsigned_value x
        + modulus * Bit.to_b0 (pi_1 (sub_with_borrow borrow x y))%product
        = unsigned_value y + Bit.to_b0 borrow
          + unsigned_value (pi_2 (sub_with_borrow borrow x y))%product)%b0.
Proof.
  intros borrow x y.
  match &x with | introduction xb3 xb2 xb1 xb0 end.
  match &xb3 with | introduction x31 x30 x29 x28 x27 x26 x25 x24 end.
  match &xb2 with | introduction x23 x22 x21 x20 x19 x18 x17 x16 end.
  match &xb1 with | introduction x15 x14 x13 x12 x11 x10 x9 x8 end.
  match &xb0 with | introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | introduction yb3 yb2 yb1 yb0 end.
  match &yb3 with | introduction y31 y30 y29 y28 y27 y26 y25 y24 end.
  match &yb2 with | introduction y23 y22 y21 y20 y19 y18 y17 y16 end.
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
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow _ &x31 &y31)))))))))))))))))))))))))))))))).
Qed.

(* reinterpretation.addition *)
Theorem addition
  : forall (x : Int32) (y : Int32) .
      (unsigned_value (x + y)%int32
        = (unsigned_value x + unsigned_value y) %. modulus)%b0.
Proof.
  intros x y.
  lemma witness
    : (Bit.to_b0 (pi_1 (add_with_carry 0 &x &y))%product * modulus
        + unsigned_value (&x + &y)%int32
        = unsigned_value &x + unsigned_value &y
      /\ unsigned_value (&x + &y)%int32 < modulus)%b0.
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
          (unsigned_value (&x + &y)%int32)
          &witness)
  with | _ facto end.
  ipso (symm &facto).
Qed.

(* reinterpretation.subtraction *)
Theorem subtraction
  : forall (x : Int32) (y : Int32) .
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
  : forall (x : Int32) .
      ((unsigned_value (- x)%int32 + unsigned_value x) %. modulus
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
  : forall (b : Bit) (x : Int32) .
      (unsigned_value (append_bit b x)
        = (10 * unsigned_value x + Bit.to_b0 b) %. modulus)%b0.
Proof.
  intros b x.
  match &x with | introduction xb3 xb2 xb1 xb0 end.
  match &xb3 with | introduction x31 x30 x29 x28 x27 x26 x25 x24 end.
  match &xb2 with | introduction x23 x22 x21 x20 x19 x18 x17 x16 end.
  match &xb1 with | introduction x15 x14 x13 x12 x11 x10 x9 x8 end.
  match &xb0 with | introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  lemma witness
    : (Bit.to_b0 &x31 * modulus
        + unsigned_value
            (append_bit &b
              (Int32.introduction (Byte.introduction &x31 &x30 &x29 &x28 &x27 &x26 &x25 &x24)
                (Byte.introduction &x23 &x22 &x21 &x20 &x19 &x18 &x17 &x16)
                (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
                (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)))
        = 10
            * unsigned_value
                (Int32.introduction (Byte.introduction &x31 &x30 &x29 &x28 &x27 &x26 &x25 &x24)
                  (Byte.introduction &x23 &x22 &x21 &x20 &x19 &x18 &x17 &x16)
                  (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
                  (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0))
          + Bit.to_b0 &b
      /\ unsigned_value
          (append_bit &b
            (Int32.introduction (Byte.introduction &x31 &x30 &x29 &x28 &x27 &x26 &x25 &x24)
              (Byte.introduction &x23 &x22 &x21 &x20 &x19 &x18 &x17 &x16)
              (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
              (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)))
        < modulus)%b0.
  {
    divide et impera.
    - lemma top
        : (Bit.to_b0 &x31 = Bit.to_b0 &x31 * 1 + 0)%b0.
      {
        match (Bin0.addition.identity (Bit.to_b0 &x31 * 1)%b0)
        with | _ sum end.
        match (Bin0.multiplication.identity (Bit.to_b0 &x31))
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
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x15
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x16
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x17
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x18
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x19
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x20
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x21
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x22
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x23
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x24
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x25
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x26
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x27
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x28
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x29
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x30
          &top))))))))))))))))))))))))))))))))).
    - ipso
        (reinterpretation.boundedness
          (append_bit &b
            (Int32.introduction (Byte.introduction &x31 &x30 &x29 &x28 &x27 &x26 &x25 &x24)
              (Byte.introduction &x23 &x22 &x21 &x20 &x19 &x18 &x17 &x16)
              (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
              (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)))).
  }
  match (Bin0.division.uniqueness
          (10 * unsigned_value
                  (Int32.introduction
                    (Byte.introduction &x31 &x30 &x29 &x28 &x27 &x26 &x25 &x24)
                    (Byte.introduction &x23 &x22 &x21 &x20 &x19 &x18 &x17 &x16)
                    (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
                    (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0))
            + Bit.to_b0 &b)%b0
          modulus
          (Bit.to_b0 &x31)
          (unsigned_value
            (append_bit &b
              (Int32.introduction (Byte.introduction &x31 &x30 &x29 &x28 &x27 &x26 &x25 &x24)
                (Byte.introduction &x23 &x22 &x21 &x20 &x19 &x18 &x17 &x16)
                (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
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
    match p with | One | b0 (p' by IH) | b1 (p' by IH) end per Bin.induction.
    + simpl Bin0.modulo, Bin0.div in |- *.
      simpl in |- *.
      quod idem est.
    + lemma unfolding
        : from_b (Bin.b0 &p') = append_bit 0 (from_b &p').
      {
        simpl in |- *.
        quod idem est.
      }
      leibniz
        &unfolding,
        (reinterpretation.appending 0 (from_b &p')),
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
        : from_b (Bin.b1 &p') = append_bit 1 (from_b &p').
      {
        simpl in |- *.
        quod idem est.
      }
      leibniz
        &unfolding,
        (reinterpretation.appending 1 (from_b &p')),
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
      simpl Bin.add in |- *.
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
Theorem section : forall (x : Int32) . from_b0 (unsigned_value x) = x.
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
  : forall (x : Int32) .
      (unsigned_value (shift_left x 1%n0)
        = (10 * unsigned_value x) %. modulus)%b0.
Proof.
  intros x.
  lemma appended : shift_left &x 1%n0 = append_bit 0 &x.
  {
    match &x with | introduction xb3 xb2 xb1 xb0 end.
    match &xb3 with | introduction x31 x30 x29 x28 x27 x26 x25 x24 end.
    match &xb2 with | introduction x23 x22 x21 x20 x19 x18 x17 x16 end.
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
  : forall (x : Int32) (p : Int32) (h : Bin0) (b : Bit) .
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
  : forall (x : Int32) (y : Int32) .
      (unsigned_value (x * y)%int32
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
  match &y with | introduction yb3 yb2 yb1 yb0 end.
  match &yb3 with | introduction y31 y30 y29 y28 y27 y26 y25 y24 end.
  match &yb2 with | introduction y23 y22 y21 y20 y19 y18 y17 y16 end.
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
    (reinterpretation.multiplication.step _ _ _ _
    (reinterpretation.multiplication.step _ _ _ _ &base)))))))))))))))))))))))))))))))).
Qed.

Module sign. (* reinterpretation.sign *)

(* reinterpretation.sign.clear *)
Theorem clear
  : forall (x : Int32) .
      sign_bit x = 0%bit
      -> (unsigned_value x < 10000000000000000000000000000000)%b0.
Proof.
  intros x e.
  match &x with | introduction xb3 xb2 xb1 xb0 end.
  match &xb3 with | introduction x31 x30 x29 x28 x27 x26 x25 x24 end.
  match &xb2 with | introduction x23 x22 x21 x20 x19 x18 x17 x16 end.
  match &xb1 with | introduction x15 x14 x13 x12 x11 x10 x9 x8 end.
  match &xb0 with | introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  simpl sign_bit in &e.
  simpl unsigned_value in |- *.
  leibniz &e in |- *.
  lemma base : (Bit.to_b0 0 < 1)%b0.
  {
    simpl Bin0.LessThan in |- *.
    exists Bin.One.
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
    (Bit.conversion.binary.boundedness.propagation _ _ _
    &base))))))))))))))))))))))))))))))).
Qed.

(* reinterpretation.sign.set *)
Theorem set
  : forall (x : Int32) .
      sign_bit x = 1%bit
      -> (10000000000000000000000000000000 <= unsigned_value x)%b0.
Proof.
  intros x e.
  match &x with | introduction xb3 xb2 xb1 xb0 end.
  match &xb3 with | introduction x31 x30 x29 x28 x27 x26 x25 x24 end.
  match &xb2 with | introduction x23 x22 x21 x20 x19 x18 x17 x16 end.
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
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    &base))))))))))))))))))))))))))))))).
Qed.

End sign. (* reinterpretation.sign *)

End reinterpretation. (* reinterpretation *)

(* [Int32] as a [Modular.Width]: its unsigned values are the residues modulo
 * 4294967296, and the laws of addition, subtraction and multiplication are
 * read through them.
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

Definition zero := Int32.reinterpretation.zero.
Definition one := Int32.reinterpretation.one.
Definition boundedness := Int32.reinterpretation.boundedness.
Definition injectivity := @Int32.reinterpretation.injectivity.
Definition addition := Int32.reinterpretation.addition.
Definition subtraction := Int32.reinterpretation.subtraction.
Definition negation := Int32.reinterpretation.negation.
Definition multiplication := Int32.reinterpretation.multiplication.

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
Theorem section : forall (x : Int32) . from_b_signed (to_b_signed x) = x.
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
Theorem injectivity : forall {x : Int32} {y : Int32} . to_b_signed x = to_b_signed y -> x = y.
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
  : forall (x : Int32) (y : Int32) .
      (pi_1 (add_with_overflow x y))%product = 0%bit ->
      (Bit.to_b0 (sign_bit x) + Bit.to_b0 (sign_bit y)
        = Bit.to_b0 (pi_1 (add_with_carry 0 x y))%product
          + Bit.to_b0 (sign_bit (x + y)%int32))%b0.
Proof.
  intros x y o.
  match &x with | introduction xb3 xb2 xb1 xb0 end.
  match &xb3 with | introduction x31 x30 x29 x28 x27 x26 x25 x24 end.
  match &xb2 with | introduction x23 x22 x21 x20 x19 x18 x17 x16 end.
  match &xb1 with | introduction x15 x14 x13 x12 x11 x10 x9 x8 end.
  match &xb0 with | introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | introduction yb3 yb2 yb1 yb0 end.
  match &yb3 with | introduction y31 y30 y29 y28 y27 y26 y25 y24 end.
  match &yb2 with | introduction y23 y22 y21 y20 y19 y18 y17 y16 end.
  match &yb1 with | introduction y15 y14 y13 y12 y11 y10 y9 y8 end.
  match &yb0 with | introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
  simpl in &o |- *.
  ipso (Bit.conversion.binary.carry.conservation _ &x31 &y31 &o).
Qed.

(* conversion.addition *)
Theorem addition
  : forall (x : Int32) (y : Int32) .
      (pi_1 (add_with_overflow x y))%product = 0%bit ->
      to_b_signed (x + y) = (x + y)%b_signed.
Proof.
  intros x y o.
  let proof t := conversion.sign &x &y &o.
  let proof a
    : (unsigned_value &x + unsigned_value &y
        = modulus * Bit.to_b0 (pi_1 (add_with_carry 0 &x &y))%product
          + unsigned_value (&x + &y)%int32)%b0
    := reinterpretation.carry 0 &x &y.
  lemma balance
    : (unsigned_value (&x + &y)%int32
        + (modulus * Bit.to_b0 (sign_bit &x)
          + modulus * Bit.to_b0 (sign_bit &y))
        = (unsigned_value &x + unsigned_value &y)
          + modulus * Bit.to_b0 (sign_bit (&x + &y)%int32))%b0.
  {
    match (Bin0.multiplication.distributivity.over.addition
            modulus
            (Bit.to_b0 (sign_bit &x)) (Bit.to_b0 (sign_bit &y)))
    with | signs _ end.
    match (Bin0.multiplication.distributivity.over.addition
            modulus
            (Bit.to_b0 (pi_1 (add_with_carry 0 &x &y))%product)
            (Bit.to_b0 (sign_bit (&x + &y)%int32)))
    with | carries _ end.
    leibniz
      <- &signs,
      &t,
      &carries,
      <- (Bin0.addition.associativity
        (unsigned_value (&x + &y)%int32)
        (modulus
          * Bit.to_b0 (pi_1 (add_with_carry 0 &x &y))%product)%b0
        (modulus * Bit.to_b0 (sign_bit (&x + &y)%int32))%b0),
      (Bin0.addition.commutativity
        (unsigned_value (&x + &y)%int32)
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
  : forall (x31 : Bit) (x30 : Bit) (x29 : Bit) (x28 : Bit)
      (x27 : Bit) (x26 : Bit) (x25 : Bit) (x24 : Bit)
      (x23 : Bit) (x22 : Bit) (x21 : Bit) (x20 : Bit)
      (x19 : Bit) (x18 : Bit) (x17 : Bit) (x16 : Bit)
      (x15 : Bit) (x14 : Bit) (x13 : Bit) (x12 : Bit)
      (x11 : Bit) (x10 : Bit) (x9 : Bit) (x8 : Bit)
      (x7 : Bit) (x6 : Bit) (x5 : Bit) (x4 : Bit)
      (x3 : Bit) (x2 : Bit) (x1 : Bit) (x0 : Bit) .
      to_b_signed (Int32.introduction (Byte.introduction x31 x30 x29 x28 x27 x26 x25 x24)
                (Byte.introduction x23 x22 x21 x20 x19 x18 x17 x16)
                (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8)
                (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0))
      = (10
          * shift_right
            (Int32.introduction (Byte.introduction x31 x30 x29 x28 x27 x26 x25 x24)
              (Byte.introduction x23 x22 x21 x20 x19 x18 x17 x16)
              (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8)
              (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0)) 1%n0
          + Bit.to_b0 x0)%b_signed.
Proof.
  intros x31 x30 x29 x28 x27 x26 x25 x24 x23 x22 x21 x20 x19 x18 x17 x16 x15 x14 x13 x12 x11 x10 x9
    x8 x7 x6 x5 x4 x3 x2 x1 x0.
  lemma shifted
    : shift_right
        (Int32.introduction (Byte.introduction &x31 &x30 &x29 &x28 &x27 &x26 &x25 &x24)
          (Byte.introduction &x23 &x22 &x21 &x20 &x19 &x18 &x17 &x16)
          (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
          (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)) 1%n0
      = Int32.introduction (Byte.introduction &x31 &x31 &x30 &x29 &x28 &x27 &x26 &x25)
        (Byte.introduction &x24 &x23 &x22 &x21 &x20 &x19 &x18 &x17)
        (Byte.introduction &x16 &x15 &x14 &x13 &x12 &x11 &x10 &x9)
        (Byte.introduction &x8 &x7 &x6 &x5 &x4 &x3 &x2 &x1).
  {
    simpl in |- *.
    quod idem est.
  }
  lemma split
    : (10 * unsigned_value
              (Int32.introduction (Byte.introduction &x31 &x31 &x30 &x29 &x28 &x27 &x26 &x25)
                (Byte.introduction &x24 &x23 &x22 &x21 &x20 &x19 &x18 &x17)
                (Byte.introduction &x16 &x15 &x14 &x13 &x12 &x11 &x10 &x9)
                (Byte.introduction &x8 &x7 &x6 &x5 &x4 &x3 &x2 &x1))
        + Bit.to_b0 &x0
        = Bit.to_b0 &x31 * modulus
          + unsigned_value
              (Int32.introduction
                (Byte.introduction &x31 &x30 &x29 &x28 &x27 &x26 &x25 &x24)
                  (Byte.introduction &x23 &x22 &x21 &x20 &x19 &x18 &x17 &x16)
                  (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
                  (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)))%b0.
  {
    lemma top
      : (Bit.to_b0 &x31 = Bit.to_b0 &x31 * 1 + 0)%b0.
    {
      match (Bin0.addition.identity (Bit.to_b0 &x31 * 1)%b0)
      with | _ sum end.
      match (Bin0.multiplication.identity (Bit.to_b0 &x31))
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
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x16
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x17
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x18
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x19
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x20
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x21
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x22
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x23
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x24
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x25
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x26
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x27
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x28
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x29
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x30
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x31
      &top)))))))))))))))))))))))))))))))).
  }
  lemma twice : forall (z : SignedBin) . (10 * z = z + z)%b_signed.
  {
    intros z.
    lemma ten : (10 = 1 + 1)%b_signed.
    {
      simpl SignedBin.add in |- *.
      simpl in |- *.
      simpl Bin.add in |- *.
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
      simpl Bin.add in |- *.
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
        (Int32.introduction (Byte.introduction &x31 &x30 &x29 &x28 &x27 &x26 &x25 &x24)
          (Byte.introduction &x23 &x22 &x21 &x20 &x19 &x18 &x17 &x16)
          (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
          (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0))
        + (modulus * Bit.to_b0 &x31 + modulus * Bit.to_b0 &x31 + 0)
        = (unsigned_value
            (Int32.introduction (Byte.introduction &x31 &x31 &x30 &x29 &x28 &x27 &x26 &x25)
              (Byte.introduction &x24 &x23 &x22 &x21 &x20 &x19 &x18 &x17)
              (Byte.introduction &x16 &x15 &x14 &x13 &x12 &x11 &x10 &x9)
              (Byte.introduction &x8 &x7 &x6 &x5 &x4 &x3 &x2 &x1))
          + unsigned_value
              (Int32.introduction (Byte.introduction &x31 &x31 &x30 &x29 &x28 &x27 &x26 &x25)
                (Byte.introduction &x24 &x23 &x22 &x21 &x20 &x19 &x18 &x17)
                (Byte.introduction &x16 &x15 &x14 &x13 &x12 &x11 &x10 &x9)
                (Byte.introduction &x8 &x7 &x6 &x5 &x4 &x3 &x2 &x1))
          + Bit.to_b0 &x0)
          + modulus * Bit.to_b0 &x31)%b0.
  {
    match (Bin0.addition.identity
            (modulus * Bit.to_b0 &x31
              + modulus * Bit.to_b0 &x31)%b0)
    with | _ unit end.
    leibniz
      &unit,
      (&doubled
        (unsigned_value
          (Int32.introduction (Byte.introduction &x31 &x31 &x30 &x29 &x28 &x27 &x26 &x25)
            (Byte.introduction &x24 &x23 &x22 &x21 &x20 &x19 &x18 &x17)
            (Byte.introduction &x16 &x15 &x14 &x13 &x12 &x11 &x10 &x9)
            (Byte.introduction &x8 &x7 &x6 &x5 &x4 &x3 &x2 &x1)))),
      &split,
      (Bin0.multiplication.commutativity
        (Bit.to_b0 &x31) modulus),
      (Bin0.addition.commutativity
        (modulus * Bit.to_b0 &x31)%b0
        (unsigned_value
          (Int32.introduction (Byte.introduction &x31 &x30 &x29 &x28 &x27 &x26 &x25 &x24)
            (Byte.introduction &x23 &x22 &x21 &x20 &x19 &x18 &x17 &x16)
            (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
            (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)))),
      (Bin0.addition.associativity
        (unsigned_value
          (Int32.introduction (Byte.introduction &x31 &x30 &x29 &x28 &x27 &x26 &x25 &x24)
            (Byte.introduction &x23 &x22 &x21 &x20 &x19 &x18 &x17 &x16)
            (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
            (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)))
        (modulus * Bit.to_b0 &x31)%b0
        (modulus * Bit.to_b0 &x31)%b0)
      in |- *.
    quod idem est.
  }
  leibniz &shifted in |- *.
  simpl to_b_signed, sign_bit in |- *.
  leibniz
    (&twice
      (SignedBin.b0_difference
        (unsigned_value
          (Int32.introduction (Byte.introduction &x31 &x31 &x30 &x29 &x28 &x27 &x26 &x25)
            (Byte.introduction &x24 &x23 &x22 &x21 &x20 &x19 &x18 &x17)
            (Byte.introduction &x16 &x15 &x14 &x13 &x12 &x11 &x10 &x9)
            (Byte.introduction &x8 &x7 &x6 &x5 &x4 &x3 &x2 &x1)))
        (modulus * Bit.to_b0 &x31)%b0)),
    (SignedBin.difference.additivity
      (unsigned_value
        (Int32.introduction (Byte.introduction &x31 &x31 &x30 &x29 &x28 &x27 &x26 &x25)
          (Byte.introduction &x24 &x23 &x22 &x21 &x20 &x19 &x18 &x17)
          (Byte.introduction &x16 &x15 &x14 &x13 &x12 &x11 &x10 &x9)
          (Byte.introduction &x8 &x7 &x6 &x5 &x4 &x3 &x2 &x1)))
      (modulus * Bit.to_b0 &x31)%b0
      (unsigned_value
        (Int32.introduction (Byte.introduction &x31 &x31 &x30 &x29 &x28 &x27 &x26 &x25)
          (Byte.introduction &x24 &x23 &x22 &x21 &x20 &x19 &x18 &x17)
          (Byte.introduction &x16 &x15 &x14 &x13 &x12 &x11 &x10 &x9)
          (Byte.introduction &x8 &x7 &x6 &x5 &x4 &x3 &x2 &x1)))
      (modulus * Bit.to_b0 &x31)%b0),
    (&embedding (Bit.to_b0 &x0)),
    (SignedBin.difference.additivity
      (unsigned_value
        (Int32.introduction (Byte.introduction &x31 &x31 &x30 &x29 &x28 &x27 &x26 &x25)
          (Byte.introduction &x24 &x23 &x22 &x21 &x20 &x19 &x18 &x17)
          (Byte.introduction &x16 &x15 &x14 &x13 &x12 &x11 &x10 &x9)
          (Byte.introduction &x8 &x7 &x6 &x5 &x4 &x3 &x2 &x1))
        + unsigned_value
            (Int32.introduction
              (Byte.introduction &x31 &x31 &x30 &x29 &x28 &x27 &x26 &x25)
                (Byte.introduction &x24 &x23 &x22 &x21 &x20 &x19 &x18 &x17)
                (Byte.introduction &x16 &x15 &x14 &x13 &x12 &x11 &x10 &x9)
                (Byte.introduction &x8 &x7 &x6 &x5 &x4 &x3 &x2 &x1)))%b0
      (modulus * Bit.to_b0 &x31
        + modulus * Bit.to_b0 &x31)%b0
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
Lemma negative : forall (p : Bin) . from_b_signed (SignedBin.Negative p) = - from_b p.
Proof.
  intros p.
  simpl from_b_signed in |- *.
  simpl SignedBin.ramp, SignedBin.negate in |- *.
  lemma nothing : from_b0 Bin0.Zero = Zero.
  {
    simpl from_b0 in |- *.
    quod idem est.
  }
  lemma unfolded : from_b0 (Bin0.Positive &p) = from_b &p.
  {
    simpl from_b0 in |- *.
    quod idem est.
  }
  leibniz &nothing, &unfolded in |- *.
  match (addition.identity (- from_b &p)) with | left _ end.
  ipso &left.
Qed.

End signed_bin. (* conversion.signed_bin *)

Module boundedness. (* conversion.boundedness *)

(* conversion.boundedness.positive *)
Theorem positive
  : forall (x : Int32) (p : Bin) .
      to_b_signed x = SignedBin.Positive p -> (p < 10000000000000000000000000000000)%b0.
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
  : forall (x : Int32) (p : Bin) .
      to_b_signed x = SignedBin.Negative p -> (p <= 10000000000000000000000000000000)%b0.
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
        (Bin0.Positive p) 10000000000000000000000000000000%b0)
    with
    | below | rest end.
    + simpl Bin0.LessOrEqual in |- *.
      ipso (disjoin _, &below).
    + match &rest with | same | above end.
      * simpl Bin0.LessOrEqual in |- *.
        ipso (disjoin &same, _).
      * lemma double
          : (10000000000000000000000000000000 + 10000000000000000000000000000000
              = modulus)%b0.
        {
          simpl modulus, Bin0.add in |- *.
          simpl Bin.add in |- *.
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
      (n < 10000000000000000000000000000000)%b0
      -> to_b_signed (from_b_signed (SignedBin.from_b0 n)) = SignedBin.from_b0 n.
Proof.
  intros n h.
  lemma half : (10000000000000000000000000000000 < modulus)%b0.
  {
    simpl Bin0.LessThan in |- *.
    exists 10000000000000000000000000000000%b.
    simpl modulus, Bin0.add in |- *.
    simpl Bin.add in |- *.
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
  : forall (p : Bin) .
      (p <= 10000000000000000000000000000000)%b0
      -> to_b_signed (from_b_signed (SignedBin.Negative p)) = SignedBin.Negative p.
Proof.
  intros p h.
  leibniz (conversion.signed_bin.negative &p) in |- *.
  lemma half : (10000000000000000000000000000000 < modulus)%b0.
  {
    simpl Bin0.LessThan in |- *.
    exists 10000000000000000000000000000000%b.
    simpl modulus, Bin0.add in |- *.
    simpl Bin.add in |- *.
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
  lemma valuek : unsigned_value (from_b &k) = k.
  {
    lemma through : from_b &k = from_b0 k.
    {
      simpl from_b0 in |- *.
      quod idem est.
    }
    leibniz
      &through, (reinterpretation.reduction k), (Bin0.modulo.identity k modulus &kbelow)
      in |- *.
    quod idem est.
  }
  lemma valuep : unsigned_value (from_b &p) = p.
  {
    lemma through : from_b &p = from_b0 p.
    {
      simpl from_b0 in |- *.
      quod idem est.
    }
    leibniz
      &through, (reinterpretation.reduction p), (Bin0.modulo.identity p modulus &pbelow)
      in |- *.
    quod idem est.
  }
  lemma sum : from_b &k + from_b &p = Zero.
  {
    lemma facto : unsigned_value (from_b &k + from_b &p) = unsigned_value Zero.
    {
      leibniz
        (reinterpretation.addition (from_b &k) (from_b &p)),
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
  lemma complement : - from_b &p = from_b &k.
  {
    match (addition.identity (- from_b &p)) with | left _ end.
    match (addition.inverse (from_b &p)) with | _ right end.
    match (addition.identity (from_b &k)) with | _ right' end.
    leibniz
      <- &left,
      <- &sum,
      (addition.associativity (from_b &k) (from_b &p) (- from_b &p)),
      &right,
      &right'
      in |- *.
    quod idem est.
  }
  leibniz &complement in |- *.
  lemma double
    : (10000000000000000000000000000000 + 10000000000000000000000000000000
        = modulus)%b0.
  {
    simpl modulus, Bin0.add in |- *.
    simpl Bin.add in |- *.
    simpl in |- *.
    quod idem est.
  }
  lemma sign : sign_bit (from_b &k) = 1%bit.
  {
    match (sign_bit (from_b &k)) with | Zero | One end |- s.
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
  : forall (x : Int32) (y : Int32) (d : Bin) .
      to_b_signed y = SignedBin.Positive d -> Option.map to_b_signed (x /. y)%int32 = Some (x /. d)%b_signed.
Proof.
  intros x y d e.
  lemma origin : to_b_signed (from_b_signed 0%b_signed) = 0%b_signed.
  {
    lemma nothing : (0 < 10000000000000000000000000000000)%b0.
    {
      simpl Bin0.LessThan in |- *.
      exists 10000000000000000000000000000000%b.
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
        lemma bounded : (q <= 10000000000000000000000000000000)%b0.
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
  : forall (x : Int32) (y : Int32) (d : Bin) .
      to_b_signed y = SignedBin.Negative d
      -> ~ (to_b_signed x = (-10000000000000000000000000000000)%b_signed /\ d = Bin.One)
      -> Option.map to_b_signed (x /. y)%int32 = Some (SignedBin.negate (x /. d)%b_signed).
Proof.
  intros x y d e h.
  lemma origin : to_b_signed (from_b_signed 0%b_signed) = 0%b_signed.
  {
    lemma nothing : (0 < 10000000000000000000000000000000)%b0.
    {
      simpl Bin0.LessThan in |- *.
      exists 10000000000000000000000000000000%b.
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
      lemma below : ((p /. &d) < 10000000000000000000000000000000)%b0.
      {
        match &r with | same | smaller end.
        - match &d with | One | b0 d' | b1 d' end.
          + let proof g := congru Bin0.to_b, &same.
            simpl Bin0.to_b in &g.
            let proof k := Option.some.injectivity &g.
            leibniz &k in &h.
            ex
              (&h
                (conjoin
                  (refl (-10000000000000000000000000000000)%b_signed),
                  (refl Bin.One)))
              quodlibet.
          + lemma differ : ~ (Bin.b0 &d' = Bin.One).
            {
              intro k.
              ex &k quodlibet.
            }
            leibniz <- &same in |- *.
            ipso (Bin0.division.quotient.strict.boundedness &p (Bin.b0 &d') &differ).
          + lemma differ : ~ (Bin.b1 &d' = Bin.One).
            {
              intro k.
              ex &k quodlibet.
            }
            leibniz <- &same in |- *.
            ipso (Bin0.division.quotient.strict.boundedness &p (Bin.b1 &d') &differ).
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
        lemma bounded : (q <= 10000000000000000000000000000000)%b0.
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

Module word. (* conversion.word *)

(* conversion.word.retraction *)
Theorem retraction : forall (w : Word) . to_word (Word.endian w) (from_word w) = w.
Proof.
  intros w.
  match &w with | introduction e b0 b1 b2 b3 end.
  match &e with | Little | Big end;
    simpl from_word, to_word in |- *;
    simpl in |- *;
    quod idem est.
Qed.

(* conversion.word.section *)
Theorem section : forall (e : Endian) (x : Int32) . from_word (to_word e x) = x.
Proof.
  intros e x.
  match &x with | introduction b3 b2 b1 b0 end.
  match &e with | Little | Big end;
    simpl from_word, to_word in |- *;
    simpl in |- *;
    quod idem est.
Qed.

End word. (* conversion.word *)

End conversion. (* conversion *)

(* [Int32] as a [Signed.Width]: its operations, the laws above, and its
 * constants, 2^31, 2^32 and 3 * 2^31. The facts about fixed values are closed
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
Definition half := 10000000000000000000000000000000%b.
Definition modulus := modulus.
Definition beyond := 110000000000000000000000000000000%b.

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

Definition section := Int32.conversion.section.

Theorem comparison
  : forall (x : T) (y : T) . compare x y = SignedBin.compare (to_b_signed x) (to_b_signed y).
Proof.
  intros x y.
  ipso (refl (compare &x &y)).
Qed.

Definition addition := Int32.conversion.addition.
Definition difference := Int32.conversion.difference.

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

Definition positive := Int32.conversion.boundedness.positive.
Definition negative := Int32.conversion.boundedness.negative.

End boundedness. (* Width.conversion.boundedness *)

Module retraction. (* Width.conversion.retraction *)

Definition nonnegative := Int32.conversion.retraction.nonnegative.
Definition negative := Int32.conversion.retraction.negative.

End retraction. (* Width.conversion.retraction *)

End conversion. (* Width.conversion *)

Module reinterpretation. (* Width.reinterpretation *)

Definition boundedness := Int32.reinterpretation.boundedness.
Definition injectivity := @Int32.reinterpretation.injectivity.
Definition multiplication := Int32.reinterpretation.multiplication.
Definition reduction := Int32.reinterpretation.reduction.

Module reduction. (* Width.reinterpretation.reduction *)

Definition additivity := Int32.reinterpretation.reduction.additivity.

Theorem zero : from_b0 Bin0.Zero = Zero.
Proof.
  ipso (refl Zero).
Qed.

End reduction. (* Width.reinterpretation.reduction *)

End reinterpretation. (* Width.reinterpretation *)

Module addition. (* Width.addition *)

Definition associativity := Int32.addition.associativity.
Definition commutativity := Int32.addition.commutativity.
Definition identity := Int32.addition.identity.
Definition inverse := Int32.addition.inverse.

End addition. (* Width.addition *)

Module multiplication. (* Width.multiplication *)

Definition annihilation := Int32.multiplication.annihilation.

Module left. (* Width.multiplication.left *)

Definition negation := Int32.multiplication.left.negation.

End left. (* Width.multiplication.left *)

Module right. (* Width.multiplication.right *)

Definition negation := Int32.multiplication.right.negation.

End right. (* Width.multiplication.right *)

End multiplication. (* Width.multiplication *)

Module subtraction. (* Width.subtraction *)

Definition specification := Int32.subtraction.specification.

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
  exists 1111111111111111111111111111111%b.
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

End Int32. (* Int32 *)

Abbreviation Int32 := Int32.T.

Export (notations) Int32.

(* A number of the type is written in decimal or hexadecimal under its
 * scope, [100%int32], [(-100)%int32] or [0x7F%int32], and a closed one prints
 * in decimal.
 *)
Number Notation Int32.T Int32.from_numeral Int32.to_numeral
  : jw_int32_scope.

(* Where an [Int32] is expected, a literal or a notation reads in this scope
 * without its [%int32].
 *)
Bind Scope jw_int32_scope with Int32.T.

(* An [Int32] stands wherever a [SignedBin] is expected, read as its value in two's
 * complement, and wherever an [Integer] is, through that value; each
 * conversion is printed where it happened.
 *)
Coercion Int32.to_b_signed : Int32 >-> SignedBin.
Add Printing Coercion Int32.to_b_signed.
Coercion Int32.to_integer : Int32 >-> Integer.
Add Printing Coercion Int32.to_integer.

(* Declared inside [Module Int32]; an instance declared there is dropped at
 * the module's [End], so it is announced again here.
 *)
Existing Instance Int32.comparable.

Instance Int32_add_monoid
  : Monoid Int32.add Int32.Zero :=
  {| Monoid.semigroup :=
      {| Semigroup.associativity := Int32.addition.associativity |}
  ; Monoid.identity := Int32.addition.identity |}.

Instance Int32_mul_monoid
  : Monoid Int32.mul Int32.One :=
  {| Monoid.semigroup :=
      {| Semigroup.associativity := Int32.multiplication.associativity |}
  ; Monoid.identity := Int32.multiplication.identity |}.

Instance Int32_add_commutative
  : Commutative Int32.add :=
  {| Commutative.commutativity := Int32.addition.commutativity |}.

Instance Int32_mul_commutative
  : Commutative Int32.mul :=
  {| Commutative.commutativity := Int32.multiplication.commutativity |}.

Instance Int32_add_group
  : Group Int32.add Int32.Zero Int32.negate :=
  {| Group.monoid := Int32_add_monoid
  ; Group.inverse := Int32.addition.inverse |}.

Instance Int32_add_abelian_group
  : AbelianGroup Int32.add Int32.Zero Int32.negate :=
  {| AbelianGroup.group := Int32_add_group
  ; AbelianGroup.commutative := Int32_add_commutative |}.

Instance Int32_ring
  : Ring Int32.add Int32.Zero Int32.negate Int32.mul Int32.One :=
  {| Ring.abelian_group := Int32_add_abelian_group
  ; Ring.monoid := Int32_mul_monoid
  ; Ring.distributivity := Int32.multiplication.distributivity.over.addition |}.
