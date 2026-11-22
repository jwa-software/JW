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
From JW Require Import Data.Machine.DWord.
From JW Require Import Data.Machine.Endian.
From JW Require Import Data.Machine.Modular.
From JW Require Import Data.Machine.Signed.
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

(* A signed integer of sixty-four bits: eight [Byte]s read in two's complement,
 * from -9223372036854775808 (-2^63) to 9223372036854775807 (2^63 - 1), its
 * arithmetic wrapping modulo 18446744073709551616 (2^64). In this file
 * [10000000000000000000000000000000000000000000000000000000000000000] is 2^64,
 * [1000000000000000000000000000000000000000000000000000000000000000] is 2^63
 * and [111111111111111111111111111111111111111111111111111111111111111] is
 * 2^63 - 1, written in binary digits.
 *)

Module Int64. (* Int64 *)

Inductive T : Type :=
  | introduction : Byte -> Byte -> Byte -> Byte -> Byte -> Byte -> Byte -> Byte -> T.

Abbreviation Int64 := T.

(* The number of values, 18446744073709551616 (2^64), the arithmetic wrapping
 * modulo it.
 *)
(* [Bin] *)
Definition modulus := 10000000000000000000000000000000000000000000000000000000000000000%b.

(* [x] laid out as a [DWord] in the order [e] names. *)
(* [Endian -> Int64 -> DWord] *)
Definition to_dword := fun (e : Endian) (x : Int64) .
  match x with
  | Int64.introduction b7 b6 b5 b4 b3 b2 b1 b0 => DWord.make e b0 b1 b2 b3 b4 b5 b6 b7
  end.

(* The value of the bytes of [w], whatever the order they are laid out in. *)
(* [DWord -> Int64] *)
Definition from_dword := fun (w : DWord) .
  Int64.introduction
    (DWord.byte7 w) (DWord.byte6 w) (DWord.byte5 w) (DWord.byte4 w)
    (DWord.byte3 w) (DWord.byte2 w) (DWord.byte1 w) (DWord.byte0 w).

(* The bits read as a number in base two, the most significant first, from 0 to
 * 18446744073709551615: the value of the bit pattern, through which the
 * arithmetic is proved and from which [to_b_signed] takes the signed value; [10] is
 * two in binary digits.
 *)
(* [Int64 -> Bin0] *)
Definition unsigned_value := fun (x : Int64) .
  match x with
  | Int64.introduction (Byte.introduction x63 x62 x61 x60 x59 x58 x57 x56)
      (Byte.introduction x55 x54 x53 x52 x51 x50 x49 x48)
      (Byte.introduction x47 x46 x45 x44 x43 x42 x41 x40)
      (Byte.introduction x39 x38 x37 x36 x35 x34 x33 x32)
      (Byte.introduction x31 x30 x29 x28 x27 x26 x25 x24)
      (Byte.introduction x23 x22 x21 x20 x19 x18 x17 x16)
      (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8)
      (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
      (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (
        10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (
        10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (
        10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (
        10 * (10 * (10 * Bit.to_b0 x63 + Bit.to_b0 x62)
        + Bit.to_b0 x61) + Bit.to_b0 x60) + Bit.to_b0 x59)
        + Bit.to_b0 x58) + Bit.to_b0 x57) + Bit.to_b0 x56)
        + Bit.to_b0 x55) + Bit.to_b0 x54) + Bit.to_b0 x53)
        + Bit.to_b0 x52) + Bit.to_b0 x51) + Bit.to_b0 x50)
        + Bit.to_b0 x49) + Bit.to_b0 x48) + Bit.to_b0 x47)
        + Bit.to_b0 x46) + Bit.to_b0 x45) + Bit.to_b0 x44)
        + Bit.to_b0 x43) + Bit.to_b0 x42) + Bit.to_b0 x41)
        + Bit.to_b0 x40) + Bit.to_b0 x39) + Bit.to_b0 x38)
        + Bit.to_b0 x37) + Bit.to_b0 x36) + Bit.to_b0 x35)
        + Bit.to_b0 x34) + Bit.to_b0 x33) + Bit.to_b0 x32)
        + Bit.to_b0 x31) + Bit.to_b0 x30) + Bit.to_b0 x29)
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
(* [Int64 -> Bit] *)
Definition sign_bit := fun (x : Int64) .
  match x with
  | Int64.introduction (Byte.introduction x63 _ _ _ _ _ _ _) _ _ _ _ _ _ _ => x63
  end.

(* The value in two's complement: the unsigned value, less 18446744073709551616
 * when the sign bit is set.
 *)
(* [Int64 -> SignedBin] *)
Definition to_b_signed := fun (x : Int64) .
  SignedBin.b0_difference
    (unsigned_value x) (modulus * Bit.to_b0 (sign_bit x))%b0.

(* From here to the end of the module an [Int64] stands where a [SignedBin] is expected,
 * read as its value; the conversion is printed.
 *)
Local Coercion to_b_signed : T >-> SignedBin.
Add Printing Coercion to_b_signed.

(* The value in [Integer], through [to_b_signed]; [Integer] is unary, so it is for
 * stating and proving, and computing goes through [to_b_signed].
 *)
(* [Int64 -> Integer] *)
Definition to_integer := fun (x : Int64) . SignedBin.to_integer (to_b_signed x).

(* [Int64] *)
Definition Zero := Int64.introduction Byte.Zero Byte.Zero Byte.Zero Byte.Zero Byte.Zero Byte.Zero
  Byte.Zero Byte.Zero.

(* [Int64] *)
Definition One :=
  Int64.introduction
    Byte.Zero
    Byte.Zero
    Byte.Zero
    Byte.Zero
    Byte.Zero
    Byte.Zero
    Byte.Zero
    (Byte.introduction
      0 0 0 0 0 0 0 1).

(* The least value, -9223372036854775808: only the sign bit set. *)
(* [Int64] *)
Definition Min :=
  Int64.introduction
    (Byte.introduction
      1 0 0 0 0 0 0 0)
    Byte.Zero
    Byte.Zero
    Byte.Zero
    Byte.Zero
    Byte.Zero
    Byte.Zero
    Byte.Zero.

(* The greatest value, 9223372036854775807: every bit but the sign bit set. *)
(* [Int64] *)
Definition Max :=
  Int64.introduction
    (Byte.introduction
      0 1 1 1 1 1 1 1)
    (Byte.introduction
      1 1 1 1 1 1 1 1)
    (Byte.introduction
      1 1 1 1 1 1 1 1)
    (Byte.introduction
      1 1 1 1 1 1 1 1)
    (Byte.introduction
      1 1 1 1 1 1 1 1)
    (Byte.introduction
      1 1 1 1 1 1 1 1)
    (Byte.introduction
      1 1 1 1 1 1 1 1)
    (Byte.introduction
      1 1 1 1 1 1 1 1).

(* [k] places toward the most significant end, a 0 coming in at the
 * other; one place first, then [k - 1].
 *)
(* [Int64 -> Nat -> Int64] *)
Fixpoint shift_left_nat (x : Int64) (k : Nat) : Int64 :=
  let y :=
    match x with
    | Int64.introduction (Byte.introduction _ x62 x61 x60 x59 x58 x57 x56)
        (Byte.introduction x55 x54 x53 x52 x51 x50 x49 x48)
        (Byte.introduction x47 x46 x45 x44 x43 x42 x41 x40)
        (Byte.introduction x39 x38 x37 x36 x35 x34 x33 x32)
        (Byte.introduction x31 x30 x29 x28 x27 x26 x25 x24)
        (Byte.introduction x23 x22 x21 x20 x19 x18 x17 x16)
        (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8)
        (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
        Int64.introduction (Byte.introduction x62 x61 x60 x59 x58 x57 x56 x55)
          (Byte.introduction x54 x53 x52 x51 x50 x49 x48 x47)
          (Byte.introduction x46 x45 x44 x43 x42 x41 x40 x39)
          (Byte.introduction x38 x37 x36 x35 x34 x33 x32 x31)
          (Byte.introduction x30 x29 x28 x27 x26 x25 x24 x23)
          (Byte.introduction x22 x21 x20 x19 x18 x17 x16 x15)
          (Byte.introduction x14 x13 x12 x11 x10 x9 x8 x7)
          (Byte.introduction x6 x5 x4 x3 x2 x1 x0 0)
    end in
  match k with
  | Nat.One          => y
  | Nat.Successor k' => shift_left_nat y k'
  end.

(* [Int64 -> Nat0 -> Int64] *)
Definition shift_left := fun (x : Int64) (k : Nat0) .
  match k with
  | Nat0.Zero       => x
  | Nat0.Positive n => shift_left_nat x n
  end.

(* [k] places toward the least significant end, the sign bit copied in at
 * the other; one place first, then [k - 1].
 *)
(* [Int64 -> Nat -> Int64] *)
Fixpoint shift_right_nat (x : Int64) (k : Nat) : Int64 :=
  let y :=
    match x with
    | Int64.introduction (Byte.introduction x63 x62 x61 x60 x59 x58 x57 x56)
        (Byte.introduction x55 x54 x53 x52 x51 x50 x49 x48)
        (Byte.introduction x47 x46 x45 x44 x43 x42 x41 x40)
        (Byte.introduction x39 x38 x37 x36 x35 x34 x33 x32)
        (Byte.introduction x31 x30 x29 x28 x27 x26 x25 x24)
        (Byte.introduction x23 x22 x21 x20 x19 x18 x17 x16)
        (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8)
        (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
        Int64.introduction (Byte.introduction x63 x63 x62 x61 x60 x59 x58 x57)
          (Byte.introduction x56 x55 x54 x53 x52 x51 x50 x49)
          (Byte.introduction x48 x47 x46 x45 x44 x43 x42 x41)
          (Byte.introduction x40 x39 x38 x37 x36 x35 x34 x33)
          (Byte.introduction x32 x31 x30 x29 x28 x27 x26 x25)
          (Byte.introduction x24 x23 x22 x21 x20 x19 x18 x17)
          (Byte.introduction x16 x15 x14 x13 x12 x11 x10 x9)
          (Byte.introduction x8 x7 x6 x5 x4 x3 x2 x1)
    end in
  match k with
  | Nat.One          => y
  | Nat.Successor k' => shift_right_nat y k'
  end.

(* [Int64 -> Nat0 -> Int64] *)
Definition shift_right := fun (x : Int64) (k : Nat0) .
  match k with
  | Nat0.Zero       => x
  | Nat0.Positive n => shift_right_nat x n
  end.

(* [x] with [b] written after its lowest bit, the highest bit dropped. *)
(* [Bit -> Int64 -> Int64] *)
Definition append_bit := fun (b : Bit) (x : Int64) .
  match x with
  | Int64.introduction (Byte.introduction _ x62 x61 x60 x59 x58 x57 x56)
      (Byte.introduction x55 x54 x53 x52 x51 x50 x49 x48)
      (Byte.introduction x47 x46 x45 x44 x43 x42 x41 x40)
      (Byte.introduction x39 x38 x37 x36 x35 x34 x33 x32)
      (Byte.introduction x31 x30 x29 x28 x27 x26 x25 x24)
      (Byte.introduction x23 x22 x21 x20 x19 x18 x17 x16)
      (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8)
      (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
      Int64.introduction (Byte.introduction x62 x61 x60 x59 x58 x57 x56 x55)
        (Byte.introduction x54 x53 x52 x51 x50 x49 x48 x47)
        (Byte.introduction x46 x45 x44 x43 x42 x41 x40 x39)
        (Byte.introduction x38 x37 x36 x35 x34 x33 x32 x31)
        (Byte.introduction x30 x29 x28 x27 x26 x25 x24 x23)
        (Byte.introduction x22 x21 x20 x19 x18 x17 x16 x15)
        (Byte.introduction x14 x13 x12 x11 x10 x9 x8 x7)
        (Byte.introduction x6 x5 x4 x3 x2 x1 x0 b)
  end.

(* The carry out and the sum of [carry + x + y], the carry rippling up from
 * the least significant place.
 *)
(* [Bit -> Int64 -> Int64 -> Product Bit Int64] *)
Definition add_with_carry := fun (carry : Bit) (x : Int64) (y : Int64) .
  match x with
  | Int64.introduction (Byte.introduction x63 x62 x61 x60 x59 x58 x57 x56)
      (Byte.introduction x55 x54 x53 x52 x51 x50 x49 x48)
      (Byte.introduction x47 x46 x45 x44 x43 x42 x41 x40)
      (Byte.introduction x39 x38 x37 x36 x35 x34 x33 x32)
      (Byte.introduction x31 x30 x29 x28 x27 x26 x25 x24)
      (Byte.introduction x23 x22 x21 x20 x19 x18 x17 x16)
      (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8)
      (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
      match y with
      | Int64.introduction (Byte.introduction y63 y62 y61 y60 y59 y58 y57 y56)
          (Byte.introduction y55 y54 y53 y52 y51 y50 y49 y48)
          (Byte.introduction y47 y46 y45 y44 y43 y42 y41 y40)
          (Byte.introduction y39 y38 y37 y36 y35 y34 y33 y32)
          (Byte.introduction y31 y30 y29 y28 y27 y26 y25 y24)
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
          let r32 := Bit.add_with_carry (pi_1 r31) x32 y32 in
          let r33 := Bit.add_with_carry (pi_1 r32) x33 y33 in
          let r34 := Bit.add_with_carry (pi_1 r33) x34 y34 in
          let r35 := Bit.add_with_carry (pi_1 r34) x35 y35 in
          let r36 := Bit.add_with_carry (pi_1 r35) x36 y36 in
          let r37 := Bit.add_with_carry (pi_1 r36) x37 y37 in
          let r38 := Bit.add_with_carry (pi_1 r37) x38 y38 in
          let r39 := Bit.add_with_carry (pi_1 r38) x39 y39 in
          let r40 := Bit.add_with_carry (pi_1 r39) x40 y40 in
          let r41 := Bit.add_with_carry (pi_1 r40) x41 y41 in
          let r42 := Bit.add_with_carry (pi_1 r41) x42 y42 in
          let r43 := Bit.add_with_carry (pi_1 r42) x43 y43 in
          let r44 := Bit.add_with_carry (pi_1 r43) x44 y44 in
          let r45 := Bit.add_with_carry (pi_1 r44) x45 y45 in
          let r46 := Bit.add_with_carry (pi_1 r45) x46 y46 in
          let r47 := Bit.add_with_carry (pi_1 r46) x47 y47 in
          let r48 := Bit.add_with_carry (pi_1 r47) x48 y48 in
          let r49 := Bit.add_with_carry (pi_1 r48) x49 y49 in
          let r50 := Bit.add_with_carry (pi_1 r49) x50 y50 in
          let r51 := Bit.add_with_carry (pi_1 r50) x51 y51 in
          let r52 := Bit.add_with_carry (pi_1 r51) x52 y52 in
          let r53 := Bit.add_with_carry (pi_1 r52) x53 y53 in
          let r54 := Bit.add_with_carry (pi_1 r53) x54 y54 in
          let r55 := Bit.add_with_carry (pi_1 r54) x55 y55 in
          let r56 := Bit.add_with_carry (pi_1 r55) x56 y56 in
          let r57 := Bit.add_with_carry (pi_1 r56) x57 y57 in
          let r58 := Bit.add_with_carry (pi_1 r57) x58 y58 in
          let r59 := Bit.add_with_carry (pi_1 r58) x59 y59 in
          let r60 := Bit.add_with_carry (pi_1 r59) x60 y60 in
          let r61 := Bit.add_with_carry (pi_1 r60) x61 y61 in
          let r62 := Bit.add_with_carry (pi_1 r61) x62 y62 in
          let r63 := Bit.add_with_carry (pi_1 r62) x63 y63 in
          (pi_1 r63,
            Int64.introduction
              (Byte.introduction
                (pi_2 r63) (pi_2 r62) (pi_2 r61) (pi_2 r60)
                (pi_2 r59) (pi_2 r58) (pi_2 r57) (pi_2 r56))
              (Byte.introduction
                (pi_2 r55) (pi_2 r54) (pi_2 r53) (pi_2 r52)
                (pi_2 r51) (pi_2 r50) (pi_2 r49) (pi_2 r48))
              (Byte.introduction
                (pi_2 r47) (pi_2 r46) (pi_2 r45) (pi_2 r44)
                (pi_2 r43) (pi_2 r42) (pi_2 r41) (pi_2 r40))
              (Byte.introduction
                (pi_2 r39) (pi_2 r38) (pi_2 r37) (pi_2 r36)
                (pi_2 r35) (pi_2 r34) (pi_2 r33) (pi_2 r32))
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

(* [Int64 -> Int64 -> Int64] *)
Definition add := fun (x : Int64) (y : Int64) . (pi_2 (add_with_carry 0 x y))%product.

(* [only parsing] keeps goals printing the operations by name. *)
Notation "x + y" := (add x y) (only parsing)
  : jw_int64_scope.

(* The borrow out and the difference of [x - y - borrow], the borrow
 * rippling up as the carry does in [add_with_carry].
 *)
(* [Bit -> Int64 -> Int64 -> Product Bit Int64] *)
Definition sub_with_borrow := fun (borrow : Bit) (x : Int64) (y : Int64) .
  match x with
  | Int64.introduction (Byte.introduction x63 x62 x61 x60 x59 x58 x57 x56)
      (Byte.introduction x55 x54 x53 x52 x51 x50 x49 x48)
      (Byte.introduction x47 x46 x45 x44 x43 x42 x41 x40)
      (Byte.introduction x39 x38 x37 x36 x35 x34 x33 x32)
      (Byte.introduction x31 x30 x29 x28 x27 x26 x25 x24)
      (Byte.introduction x23 x22 x21 x20 x19 x18 x17 x16)
      (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8)
      (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
      match y with
      | Int64.introduction (Byte.introduction y63 y62 y61 y60 y59 y58 y57 y56)
          (Byte.introduction y55 y54 y53 y52 y51 y50 y49 y48)
          (Byte.introduction y47 y46 y45 y44 y43 y42 y41 y40)
          (Byte.introduction y39 y38 y37 y36 y35 y34 y33 y32)
          (Byte.introduction y31 y30 y29 y28 y27 y26 y25 y24)
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
          let r32 := Bit.sub_with_borrow (pi_1 r31) x32 y32 in
          let r33 := Bit.sub_with_borrow (pi_1 r32) x33 y33 in
          let r34 := Bit.sub_with_borrow (pi_1 r33) x34 y34 in
          let r35 := Bit.sub_with_borrow (pi_1 r34) x35 y35 in
          let r36 := Bit.sub_with_borrow (pi_1 r35) x36 y36 in
          let r37 := Bit.sub_with_borrow (pi_1 r36) x37 y37 in
          let r38 := Bit.sub_with_borrow (pi_1 r37) x38 y38 in
          let r39 := Bit.sub_with_borrow (pi_1 r38) x39 y39 in
          let r40 := Bit.sub_with_borrow (pi_1 r39) x40 y40 in
          let r41 := Bit.sub_with_borrow (pi_1 r40) x41 y41 in
          let r42 := Bit.sub_with_borrow (pi_1 r41) x42 y42 in
          let r43 := Bit.sub_with_borrow (pi_1 r42) x43 y43 in
          let r44 := Bit.sub_with_borrow (pi_1 r43) x44 y44 in
          let r45 := Bit.sub_with_borrow (pi_1 r44) x45 y45 in
          let r46 := Bit.sub_with_borrow (pi_1 r45) x46 y46 in
          let r47 := Bit.sub_with_borrow (pi_1 r46) x47 y47 in
          let r48 := Bit.sub_with_borrow (pi_1 r47) x48 y48 in
          let r49 := Bit.sub_with_borrow (pi_1 r48) x49 y49 in
          let r50 := Bit.sub_with_borrow (pi_1 r49) x50 y50 in
          let r51 := Bit.sub_with_borrow (pi_1 r50) x51 y51 in
          let r52 := Bit.sub_with_borrow (pi_1 r51) x52 y52 in
          let r53 := Bit.sub_with_borrow (pi_1 r52) x53 y53 in
          let r54 := Bit.sub_with_borrow (pi_1 r53) x54 y54 in
          let r55 := Bit.sub_with_borrow (pi_1 r54) x55 y55 in
          let r56 := Bit.sub_with_borrow (pi_1 r55) x56 y56 in
          let r57 := Bit.sub_with_borrow (pi_1 r56) x57 y57 in
          let r58 := Bit.sub_with_borrow (pi_1 r57) x58 y58 in
          let r59 := Bit.sub_with_borrow (pi_1 r58) x59 y59 in
          let r60 := Bit.sub_with_borrow (pi_1 r59) x60 y60 in
          let r61 := Bit.sub_with_borrow (pi_1 r60) x61 y61 in
          let r62 := Bit.sub_with_borrow (pi_1 r61) x62 y62 in
          let r63 := Bit.sub_with_borrow (pi_1 r62) x63 y63 in
          (pi_1 r63,
            Int64.introduction
              (Byte.introduction
                (pi_2 r63) (pi_2 r62) (pi_2 r61) (pi_2 r60)
                (pi_2 r59) (pi_2 r58) (pi_2 r57) (pi_2 r56))
              (Byte.introduction
                (pi_2 r55) (pi_2 r54) (pi_2 r53) (pi_2 r52)
                (pi_2 r51) (pi_2 r50) (pi_2 r49) (pi_2 r48))
              (Byte.introduction
                (pi_2 r47) (pi_2 r46) (pi_2 r45) (pi_2 r44)
                (pi_2 r43) (pi_2 r42) (pi_2 r41) (pi_2 r40))
              (Byte.introduction
                (pi_2 r39) (pi_2 r38) (pi_2 r37) (pi_2 r36)
                (pi_2 r35) (pi_2 r34) (pi_2 r33) (pi_2 r32))
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

(* [Int64 -> Int64 -> Int64] *)
Definition sub := fun (x : Int64) (y : Int64) . (pi_2 (sub_with_borrow 0 x y))%product.

Notation "x - y" := (sub x y) (only parsing)
  : jw_int64_scope.

(* [x] taken from [Zero], wrapping. *)
(* [Int64 -> Int64] *)
Definition negate := fun (x : Int64) . sub Zero x.

(* Also what makes the minus of a negative literal parse: [Numeral.Signed]
 * lets [from_numeral] receive a sign but puts none in the grammar.
 *)
Notation "- x" := (negate x)
  (at level 35, right associativity, only parsing)
  : jw_int64_scope.

(* [y]'s bits from the most significant, each step doubling the product so
 * far and adding [x] for a 1, all modulo 18446744073709551616.
 *)
(* [Int64 -> Int64 -> Int64] *)
Definition mul := fun (x : Int64) (y : Int64) .
  let step := fun (p : Int64) (b : Bit) .
    add (shift_left p 1%n0)
      match b with
      | 0%bit => Zero
      | 1%bit => x
      end in
  match y with
  | Int64.introduction (Byte.introduction y63 y62 y61 y60 y59 y58 y57 y56)
      (Byte.introduction y55 y54 y53 y52 y51 y50 y49 y48)
      (Byte.introduction y47 y46 y45 y44 y43 y42 y41 y40)
      (Byte.introduction y39 y38 y37 y36 y35 y34 y33 y32)
      (Byte.introduction y31 y30 y29 y28 y27 y26 y25 y24)
      (Byte.introduction y23 y22 y21 y20 y19 y18 y17 y16)
      (Byte.introduction y15 y14 y13 y12 y11 y10 y9 y8)
      (Byte.introduction y7 y6 y5 y4 y3 y2 y1 y0) =>
      step (step (step (step (step (step (step (step (step (step (step (step (step (step (step (step
        (step (step (step (step (step (step (step (step (step (step (step (step (step (step (step
        (step (step (step (step (step (step (step (step (step (step (step (step (step (step (step
        (step (step (step (step (step (step (step (step (step (step (step (step (step (step (step
        (step (step (step Zero y63) y62) y61) y60) y59) y58) y57) y56) y55) y54) y53) y52) y51) y50)
        y49) y48) y47) y46) y45) y44) y43) y42) y41) y40) y39) y38) y37) y36) y35) y34) y33) y32)
        y31) y30) y29) y28) y27) y26) y25) y24) y23) y22) y21) y20) y19) y18) y17) y16) y15) y14)
        y13) y12) y11) y10) y9) y8) y7) y6) y5) y4) y3) y2) y1) y0
  end.

Notation "x * y" := (mul x y) (only parsing)
  : jw_int64_scope.

(* The flag and the wrapped product: the flag is set when the product of the
 * signed values lies outside the range, below [Min] or above [Max].
 *)
(* [Int64 -> Int64 -> Product Bit Int64] *)
Definition mul_with_overflow := fun (x : Int64) (y : Int64) .
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

(* The bit pattern of [p] modulo 18446744073709551616, its bits appended from
 * the most significant.
 *)
(* [Bin -> Int64] *)
Fixpoint from_b (p : Bin) : Int64 :=
  match p with
  | Bin.One   => One
  | Bin.b0 p' => append_bit 0 (from_b p')
  | Bin.b1 p' => append_bit 1 (from_b p')
  end.

(* [Bin0 -> Int64] *)
Definition from_b0 := fun (n : Bin0) .
  match n with
  | Bin0.Zero       => Zero
  | Bin0.Positive p => from_b p
  end.

(* [Nat -> Int64] *)
Definition from_nat := fun (n : Nat) . from_b (Bin.from_nat n).

(* [Nat0 -> Int64] *)
Definition from_nat0 := fun (n : Nat0) . from_b0 (Bin0.from_nat0 n).

(* [z] modulo 18446744073709551616 into the range -9223372036854775808 to
 * 9223372036854775807: its positive part less its negative part, wrapping.
 *)
(* [SignedBin -> Int64] *)
Definition from_b_signed := fun (z : SignedBin) .
  add (from_b0 (SignedBin.ramp z)) (negate (from_b0 (SignedBin.ramp (SignedBin.negate z)))).

(* The quotient through [SignedBin], toward zero, [None] when [y] is zero. [SignedBin.divide]
 * takes a positive divisor, so the divisor's sign is matched here;
 * -9223372036854775808 (-2^63) over -1 wraps to itself.
 *)
(* [Int64 -> Int64 -> Option Int64] *)
Definition divide := fun (x : Int64) (y : Int64) .
  match to_b_signed y with
  | SignedBin.Negative d => Some (from_b_signed (SignedBin.negate (x /. d)%b_signed))
  | SignedBin.Zero       => None
  | SignedBin.Positive d => Some (from_b_signed (x /. d)%b_signed)
  end.

Notation "x /. y" := (divide x y) (only parsing)
  : jw_int64_scope.

(* [x] modulo 18446744073709551616 into the range -9223372036854775808 to
 * 9223372036854775807.
 *)
(* [Integer -> Int64] *)
Definition from_integer := fun (x : Integer) .
  match x with
  | Integer.Negative p => negate (from_nat p)
  | Integer.Zero       => Zero
  | Integer.Positive p => from_nat p
  end.

(* The overflow flag and the sum of [x + y]: the flag is set when [x] and [y]
 * have the same sign and the sum the other, the true sum lying past
 * -9223372036854775808 or 9223372036854775807.
 *)
(* [Int64 -> Int64 -> Product Bit Int64] *)
Definition add_with_overflow := fun (x : Int64) (y : Int64) .
  let flag :=
    Bit.and
      (Bit.flip (Bit.xor (sign_bit x) (sign_bit y)))
      (Bit.xor (sign_bit (add x y)) (sign_bit x)) in
  (flag, add x y)%product.

(* The overflow flag and the difference of [x - y]: the flag is set when [x]
 * and [y] have different signs and the difference has the sign of [y], the
 * true difference lying past -9223372036854775808 or 9223372036854775807.
 *)
(* [Int64 -> Int64 -> Product Bit Int64] *)
Definition sub_with_overflow := fun (x : Int64) (y : Int64) .
  let flag :=
    Bit.and
      (Bit.xor (sign_bit x) (sign_bit y))
      (Bit.xor (sign_bit (sub x y)) (sign_bit x)) in
  (flag, sub x y)%product.

(* [Int64 -> Int64 -> Prop] *)
Definition LessThan := fun (x : Int64) (y : Int64) . (to_b_signed x < to_b_signed y)%b_signed.

Notation "x < y" := (LessThan x y) (only parsing)
  : jw_int64_scope.

(* [Int64 -> Int64 -> Prop] *)
Definition LessOrEqual := fun (x : Int64) (y : Int64) . x = y \/ LessThan x y.

Notation "x <= y" := (LessOrEqual x y) (only parsing)
  : jw_int64_scope.

Notation "x > y" := (LessThan y x) (only parsing)
  : jw_int64_scope.
Notation "x >= y" := (LessOrEqual y x) (only parsing)
  : jw_int64_scope.

Notation "'(<)'" := LessThan (only parsing)
  : jw_int64_scope.
Notation "'(<=)'" := LessOrEqual (only parsing)
  : jw_int64_scope.

(* [Int64 -> Int64 -> Comparison] *)
Definition compare := fun (x : Int64) (y : Int64) . SignedBin.compare (to_b_signed x) (to_b_signed y).

(* [Int64 -> Int64 -> Bool] *)
Abbreviation eq := (Comparable.eq compare).

(* [Int64 -> Int64 -> Bool] *)
Abbreviation le := (Comparable.le compare).

(* [Int64 -> Int64 -> Bool] *)
Abbreviation lt := (Comparable.lt compare).

(* [Int64 -> Int64 -> Int64] *)
Abbreviation min := (Comparable.min compare).

(* [Int64 -> Int64 -> Int64] *)
Abbreviation max := (Comparable.max compare).

(* A literal of -9223372036854775808 to 9223372036854775807, in decimal or
 * hexadecimal, read in binary; any wider is refused.
 *)
(* [Numeral.Signed -> Option Int64] *)
Definition from_numeral := fun (s : Numeral.Signed) .
  let positive := fun (v : Bin0) .
    match Bin0.compare v
      111111111111111111111111111111111111111111111111111111111111111%b0 with
    | Comparison.Lt => Some (from_b0 v)
    | Comparison.Eq => Some (from_b0 v)
    | Comparison.Gt => None
    end in
  let negative := fun (v : Bin0) .
    match Bin0.compare v
      1000000000000000000000000000000000000000000000000000000000000000%b0 with
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
(* [Int64 -> Numeral.Signed] *)
Definition to_numeral := fun (x : Int64) .
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

Local Open Scope jw_int64_scope.

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
Theorem boundedness : forall (x : Int64) . (unsigned_value x < modulus)%b0.
Proof.
  intros x.
  match &x with | introduction xb7 xb6 xb5 xb4 xb3 xb2 xb1 xb0 end.
  match &xb7 with | introduction x63 x62 x61 x60 x59 x58 x57 x56 end.
  match &xb6 with | introduction x55 x54 x53 x52 x51 x50 x49 x48 end.
  match &xb5 with | introduction x47 x46 x45 x44 x43 x42 x41 x40 end.
  match &xb4 with | introduction x39 x38 x37 x36 x35 x34 x33 x32 end.
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
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness &x63)
    ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
Qed.

(* reinterpretation.injectivity *)
Theorem injectivity
  : forall {x : Int64} {y : Int64} . unsigned_value x = unsigned_value y -> x = y.
Proof.
  intros x y e.
  match &x with | introduction xb7 xb6 xb5 xb4 xb3 xb2 xb1 xb0 end.
  match &xb7 with | introduction x63 x62 x61 x60 x59 x58 x57 x56 end.
  match &xb6 with | introduction x55 x54 x53 x52 x51 x50 x49 x48 end.
  match &xb5 with | introduction x47 x46 x45 x44 x43 x42 x41 x40 end.
  match &xb4 with | introduction x39 x38 x37 x36 x35 x34 x33 x32 end.
  match &xb3 with | introduction x31 x30 x29 x28 x27 x26 x25 x24 end.
  match &xb2 with | introduction x23 x22 x21 x20 x19 x18 x17 x16 end.
  match &xb1 with | introduction x15 x14 x13 x12 x11 x10 x9 x8 end.
  match &xb0 with | introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | introduction yb7 yb6 yb5 yb4 yb3 yb2 yb1 yb0 end.
  match &yb7 with | introduction y63 y62 y61 y60 y59 y58 y57 y56 end.
  match &yb6 with | introduction y55 y54 y53 y52 y51 y50 y49 y48 end.
  match &yb5 with | introduction y47 y46 y45 y44 y43 y42 y41 y40 end.
  match &yb4 with | introduction y39 y38 y37 y36 y35 y34 y33 y32 end.
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
  match (Bit.conversion.binary.halving.injectivity &e31) with | e32 b31 end.
  match (Bit.conversion.binary.halving.injectivity &e32) with | e33 b32 end.
  match (Bit.conversion.binary.halving.injectivity &e33) with | e34 b33 end.
  match (Bit.conversion.binary.halving.injectivity &e34) with | e35 b34 end.
  match (Bit.conversion.binary.halving.injectivity &e35) with | e36 b35 end.
  match (Bit.conversion.binary.halving.injectivity &e36) with | e37 b36 end.
  match (Bit.conversion.binary.halving.injectivity &e37) with | e38 b37 end.
  match (Bit.conversion.binary.halving.injectivity &e38) with | e39 b38 end.
  match (Bit.conversion.binary.halving.injectivity &e39) with | e40 b39 end.
  match (Bit.conversion.binary.halving.injectivity &e40) with | e41 b40 end.
  match (Bit.conversion.binary.halving.injectivity &e41) with | e42 b41 end.
  match (Bit.conversion.binary.halving.injectivity &e42) with | e43 b42 end.
  match (Bit.conversion.binary.halving.injectivity &e43) with | e44 b43 end.
  match (Bit.conversion.binary.halving.injectivity &e44) with | e45 b44 end.
  match (Bit.conversion.binary.halving.injectivity &e45) with | e46 b45 end.
  match (Bit.conversion.binary.halving.injectivity &e46) with | e47 b46 end.
  match (Bit.conversion.binary.halving.injectivity &e47) with | e48 b47 end.
  match (Bit.conversion.binary.halving.injectivity &e48) with | e49 b48 end.
  match (Bit.conversion.binary.halving.injectivity &e49) with | e50 b49 end.
  match (Bit.conversion.binary.halving.injectivity &e50) with | e51 b50 end.
  match (Bit.conversion.binary.halving.injectivity &e51) with | e52 b51 end.
  match (Bit.conversion.binary.halving.injectivity &e52) with | e53 b52 end.
  match (Bit.conversion.binary.halving.injectivity &e53) with | e54 b53 end.
  match (Bit.conversion.binary.halving.injectivity &e54) with | e55 b54 end.
  match (Bit.conversion.binary.halving.injectivity &e55) with | e56 b55 end.
  match (Bit.conversion.binary.halving.injectivity &e56) with | e57 b56 end.
  match (Bit.conversion.binary.halving.injectivity &e57) with | e58 b57 end.
  match (Bit.conversion.binary.halving.injectivity &e58) with | e59 b58 end.
  match (Bit.conversion.binary.halving.injectivity &e59) with | e60 b59 end.
  match (Bit.conversion.binary.halving.injectivity &e60) with | e61 b60 end.
  match (Bit.conversion.binary.halving.injectivity &e61) with | e62 b61 end.
  match (Bit.conversion.binary.halving.injectivity &e62) with | e63 b62 end.
  leibniz
    &b0, &b1, &b2, &b3, &b4, &b5, &b6, &b7, &b8, &b9, &b10, &b11, &b12, &b13, &b14, &b15, &b16,
    &b17, &b18, &b19, &b20, &b21, &b22, &b23, &b24, &b25, &b26, &b27, &b28, &b29, &b30, &b31, &b32,
    &b33, &b34, &b35, &b36, &b37, &b38, &b39, &b40, &b41, &b42, &b43, &b44, &b45, &b46, &b47, &b48,
    &b49, &b50, &b51, &b52, &b53, &b54, &b55, &b56, &b57, &b58, &b59, &b60, &b61, &b62,
    (Bit.conversion.binary.injectivity &e63)
    in |- *.
  quod idem est.
Qed.

(* The numbers are added place by place from the most significant, each
 * place one [Bit.conversion.binary.carry.propagation] around the places
 * above it.
 *)
(* reinterpretation.carry *)
Theorem carry
  : forall (carry : Bit) (x : Int64) (y : Int64) .
      (Bit.to_b0 carry + unsigned_value x + unsigned_value y
        = modulus * Bit.to_b0 (pi_1 (add_with_carry carry x y))%product
          + unsigned_value (pi_2 (add_with_carry carry x y))%product)%b0.
Proof.
  intros carry x y.
  match &x with | introduction xb7 xb6 xb5 xb4 xb3 xb2 xb1 xb0 end.
  match &xb7 with | introduction x63 x62 x61 x60 x59 x58 x57 x56 end.
  match &xb6 with | introduction x55 x54 x53 x52 x51 x50 x49 x48 end.
  match &xb5 with | introduction x47 x46 x45 x44 x43 x42 x41 x40 end.
  match &xb4 with | introduction x39 x38 x37 x36 x35 x34 x33 x32 end.
  match &xb3 with | introduction x31 x30 x29 x28 x27 x26 x25 x24 end.
  match &xb2 with | introduction x23 x22 x21 x20 x19 x18 x17 x16 end.
  match &xb1 with | introduction x15 x14 x13 x12 x11 x10 x9 x8 end.
  match &xb0 with | introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | introduction yb7 yb6 yb5 yb4 yb3 yb2 yb1 yb0 end.
  match &yb7 with | introduction y63 y62 y61 y60 y59 y58 y57 y56 end.
  match &yb6 with | introduction y55 y54 y53 y52 y51 y50 y49 y48 end.
  match &yb5 with | introduction y47 y46 y45 y44 y43 y42 y41 y40 end.
  match &yb4 with | introduction y39 y38 y37 y36 y35 y34 y33 y32 end.
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
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry _ &x63 &y63)
    ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
Qed.

(* reinterpretation.borrow *)
Theorem borrow
  : forall (borrow : Bit) (x : Int64) (y : Int64) .
      (unsigned_value x
        + modulus * Bit.to_b0 (pi_1 (sub_with_borrow borrow x y))%product
        = unsigned_value y + Bit.to_b0 borrow
          + unsigned_value (pi_2 (sub_with_borrow borrow x y))%product)%b0.
Proof.
  intros borrow x y.
  match &x with | introduction xb7 xb6 xb5 xb4 xb3 xb2 xb1 xb0 end.
  match &xb7 with | introduction x63 x62 x61 x60 x59 x58 x57 x56 end.
  match &xb6 with | introduction x55 x54 x53 x52 x51 x50 x49 x48 end.
  match &xb5 with | introduction x47 x46 x45 x44 x43 x42 x41 x40 end.
  match &xb4 with | introduction x39 x38 x37 x36 x35 x34 x33 x32 end.
  match &xb3 with | introduction x31 x30 x29 x28 x27 x26 x25 x24 end.
  match &xb2 with | introduction x23 x22 x21 x20 x19 x18 x17 x16 end.
  match &xb1 with | introduction x15 x14 x13 x12 x11 x10 x9 x8 end.
  match &xb0 with | introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | introduction yb7 yb6 yb5 yb4 yb3 yb2 yb1 yb0 end.
  match &yb7 with | introduction y63 y62 y61 y60 y59 y58 y57 y56 end.
  match &yb6 with | introduction y55 y54 y53 y52 y51 y50 y49 y48 end.
  match &yb5 with | introduction y47 y46 y45 y44 y43 y42 y41 y40 end.
  match &yb4 with | introduction y39 y38 y37 y36 y35 y34 y33 y32 end.
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
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow _ &x63 &y63)
    ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
Qed.

(* reinterpretation.addition *)
Theorem addition
  : forall (x : Int64) (y : Int64) .
      (unsigned_value (x + y)%int64
        = (unsigned_value x + unsigned_value y) %. modulus)%b0.
Proof.
  intros x y.
  lemma witness
    : (Bit.to_b0 (pi_1 (add_with_carry 0 &x &y))%product * modulus
        + unsigned_value (&x + &y)%int64
        = unsigned_value &x + unsigned_value &y
      /\ unsigned_value (&x + &y)%int64 < modulus)%b0.
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
          (unsigned_value (&x + &y)%int64)
          &witness)
  with | _ facto end.
  ipso (symm &facto).
Qed.

(* reinterpretation.subtraction *)
Theorem subtraction
  : forall (x : Int64) (y : Int64) .
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
  : forall (x : Int64) .
      ((unsigned_value (- x)%int64 + unsigned_value x) %. modulus
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
  : forall (b : Bit) (x : Int64) .
      (unsigned_value (append_bit b x)
        = (10 * unsigned_value x + Bit.to_b0 b) %. modulus)%b0.
Proof.
  intros b x.
  match &x with | introduction xb7 xb6 xb5 xb4 xb3 xb2 xb1 xb0 end.
  match &xb7 with | introduction x63 x62 x61 x60 x59 x58 x57 x56 end.
  match &xb6 with | introduction x55 x54 x53 x52 x51 x50 x49 x48 end.
  match &xb5 with | introduction x47 x46 x45 x44 x43 x42 x41 x40 end.
  match &xb4 with | introduction x39 x38 x37 x36 x35 x34 x33 x32 end.
  match &xb3 with | introduction x31 x30 x29 x28 x27 x26 x25 x24 end.
  match &xb2 with | introduction x23 x22 x21 x20 x19 x18 x17 x16 end.
  match &xb1 with | introduction x15 x14 x13 x12 x11 x10 x9 x8 end.
  match &xb0 with | introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  lemma witness
    : (Bit.to_b0 &x63 * modulus
        + unsigned_value
            (append_bit &b
              (Int64.introduction (Byte.introduction &x63 &x62 &x61 &x60 &x59 &x58 &x57 &x56)
                (Byte.introduction &x55 &x54 &x53 &x52 &x51 &x50 &x49 &x48)
                (Byte.introduction &x47 &x46 &x45 &x44 &x43 &x42 &x41 &x40)
                (Byte.introduction &x39 &x38 &x37 &x36 &x35 &x34 &x33 &x32)
                (Byte.introduction &x31 &x30 &x29 &x28 &x27 &x26 &x25 &x24)
                (Byte.introduction &x23 &x22 &x21 &x20 &x19 &x18 &x17 &x16)
                (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
                (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)))
        = 10
            * unsigned_value
                (Int64.introduction (Byte.introduction &x63 &x62 &x61 &x60 &x59 &x58 &x57 &x56)
                  (Byte.introduction &x55 &x54 &x53 &x52 &x51 &x50 &x49 &x48)
                  (Byte.introduction &x47 &x46 &x45 &x44 &x43 &x42 &x41 &x40)
                  (Byte.introduction &x39 &x38 &x37 &x36 &x35 &x34 &x33 &x32)
                  (Byte.introduction &x31 &x30 &x29 &x28 &x27 &x26 &x25 &x24)
                  (Byte.introduction &x23 &x22 &x21 &x20 &x19 &x18 &x17 &x16)
                  (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
                  (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0))
          + Bit.to_b0 &b
      /\ unsigned_value
          (append_bit &b
            (Int64.introduction (Byte.introduction &x63 &x62 &x61 &x60 &x59 &x58 &x57 &x56)
              (Byte.introduction &x55 &x54 &x53 &x52 &x51 &x50 &x49 &x48)
              (Byte.introduction &x47 &x46 &x45 &x44 &x43 &x42 &x41 &x40)
              (Byte.introduction &x39 &x38 &x37 &x36 &x35 &x34 &x33 &x32)
              (Byte.introduction &x31 &x30 &x29 &x28 &x27 &x26 &x25 &x24)
              (Byte.introduction &x23 &x22 &x21 &x20 &x19 &x18 &x17 &x16)
              (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
              (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)))
        < modulus)%b0.
  {
    divide et impera.
    - lemma top
        : (Bit.to_b0 &x63 = Bit.to_b0 &x63 * 1 + 0)%b0.
      {
        match (Bin0.addition.identity (Bit.to_b0 &x63 * 1)%b0)
        with | _ sum end.
        match (Bin0.multiplication.identity (Bit.to_b0 &x63))
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
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x31
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x32
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x33
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x34
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x35
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x36
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x37
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x38
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x39
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x40
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x41
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x42
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x43
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x44
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x45
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x46
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x47
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x48
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x49
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x50
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x51
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x52
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x53
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x54
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x55
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x56
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x57
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x58
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x59
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x60
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x61
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x62
          &top))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
    - ipso
        (reinterpretation.boundedness
          (append_bit &b
            (Int64.introduction (Byte.introduction &x63 &x62 &x61 &x60 &x59 &x58 &x57 &x56)
              (Byte.introduction &x55 &x54 &x53 &x52 &x51 &x50 &x49 &x48)
              (Byte.introduction &x47 &x46 &x45 &x44 &x43 &x42 &x41 &x40)
              (Byte.introduction &x39 &x38 &x37 &x36 &x35 &x34 &x33 &x32)
              (Byte.introduction &x31 &x30 &x29 &x28 &x27 &x26 &x25 &x24)
              (Byte.introduction &x23 &x22 &x21 &x20 &x19 &x18 &x17 &x16)
              (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
              (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)))).
  }
  match (Bin0.division.uniqueness
          (10 * unsigned_value
                  (Int64.introduction
                    (Byte.introduction &x63 &x62 &x61 &x60 &x59 &x58 &x57 &x56)
                    (Byte.introduction &x55 &x54 &x53 &x52 &x51 &x50 &x49 &x48)
                    (Byte.introduction &x47 &x46 &x45 &x44 &x43 &x42 &x41 &x40)
                    (Byte.introduction &x39 &x38 &x37 &x36 &x35 &x34 &x33 &x32)
                    (Byte.introduction &x31 &x30 &x29 &x28 &x27 &x26 &x25 &x24)
                    (Byte.introduction &x23 &x22 &x21 &x20 &x19 &x18 &x17 &x16)
                    (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
                    (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0))
            + Bit.to_b0 &b)%b0
          modulus
          (Bit.to_b0 &x63)
          (unsigned_value
            (append_bit &b
              (Int64.introduction (Byte.introduction &x63 &x62 &x61 &x60 &x59 &x58 &x57 &x56)
                (Byte.introduction &x55 &x54 &x53 &x52 &x51 &x50 &x49 &x48)
                (Byte.introduction &x47 &x46 &x45 &x44 &x43 &x42 &x41 &x40)
                (Byte.introduction &x39 &x38 &x37 &x36 &x35 &x34 &x33 &x32)
                (Byte.introduction &x31 &x30 &x29 &x28 &x27 &x26 &x25 &x24)
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
Theorem section : forall (x : Int64) . from_b0 (unsigned_value x) = x.
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
  : forall (x : Int64) .
      (unsigned_value (shift_left x 1%n0)
        = (10 * unsigned_value x) %. modulus)%b0.
Proof.
  intros x.
  lemma appended : shift_left &x 1%n0 = append_bit 0 &x.
  {
    match &x with | introduction xb7 xb6 xb5 xb4 xb3 xb2 xb1 xb0 end.
    match &xb7 with | introduction x63 x62 x61 x60 x59 x58 x57 x56 end.
    match &xb6 with | introduction x55 x54 x53 x52 x51 x50 x49 x48 end.
    match &xb5 with | introduction x47 x46 x45 x44 x43 x42 x41 x40 end.
    match &xb4 with | introduction x39 x38 x37 x36 x35 x34 x33 x32 end.
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
  : forall (x : Int64) (p : Int64) (h : Bin0) (b : Bit) .
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
  : forall (x : Int64) (y : Int64) .
      (unsigned_value (x * y)%int64
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
  match &y with | introduction yb7 yb6 yb5 yb4 yb3 yb2 yb1 yb0 end.
  match &yb7 with | introduction y63 y62 y61 y60 y59 y58 y57 y56 end.
  match &yb6 with | introduction y55 y54 y53 y52 y51 y50 y49 y48 end.
  match &yb5 with | introduction y47 y46 y45 y44 y43 y42 y41 y40 end.
  match &yb4 with | introduction y39 y38 y37 y36 y35 y34 y33 y32 end.
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
    (reinterpretation.multiplication.step _ _ _ _
    (reinterpretation.multiplication.step _ _ _ _ &base
    )))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
Qed.

Module sign. (* reinterpretation.sign *)

(* reinterpretation.sign.clear *)
Theorem clear
  : forall (x : Int64) .
      sign_bit x = 0%bit
      -> (unsigned_value x
          < 1000000000000000000000000000000000000000000000000000000000000000)%b0.
Proof.
  intros x e.
  match &x with | introduction xb7 xb6 xb5 xb4 xb3 xb2 xb1 xb0 end.
  match &xb7 with | introduction x63 x62 x61 x60 x59 x58 x57 x56 end.
  match &xb6 with | introduction x55 x54 x53 x52 x51 x50 x49 x48 end.
  match &xb5 with | introduction x47 x46 x45 x44 x43 x42 x41 x40 end.
  match &xb4 with | introduction x39 x38 x37 x36 x35 x34 x33 x32 end.
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
    (Bit.conversion.binary.boundedness.propagation _ _ _
    &base
    ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
Qed.

(* reinterpretation.sign.set *)
Theorem set
  : forall (x : Int64) .
      sign_bit x = 1%bit
      -> (1000000000000000000000000000000000000000000000000000000000000000
          <= unsigned_value x)%b0.
Proof.
  intros x e.
  match &x with | introduction xb7 xb6 xb5 xb4 xb3 xb2 xb1 xb0 end.
  match &xb7 with | introduction x63 x62 x61 x60 x59 x58 x57 x56 end.
  match &xb6 with | introduction x55 x54 x53 x52 x51 x50 x49 x48 end.
  match &xb5 with | introduction x47 x46 x45 x44 x43 x42 x41 x40 end.
  match &xb4 with | introduction x39 x38 x37 x36 x35 x34 x33 x32 end.
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
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    &base
    ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
Qed.

End sign. (* reinterpretation.sign *)

End reinterpretation. (* reinterpretation *)

(* [Int64] as a [Modular.Width]: its unsigned values are the residues modulo
 * 18446744073709551616, and the laws of addition, subtraction and
 * multiplication are read through them.
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

Definition zero := Int64.reinterpretation.zero.
Definition one := Int64.reinterpretation.one.
Definition boundedness := Int64.reinterpretation.boundedness.
Definition injectivity := @Int64.reinterpretation.injectivity.
Definition addition := Int64.reinterpretation.addition.
Definition subtraction := Int64.reinterpretation.subtraction.
Definition negation := Int64.reinterpretation.negation.
Definition multiplication := Int64.reinterpretation.multiplication.

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
Theorem section : forall (x : Int64) . from_b_signed (to_b_signed x) = x.
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
Theorem injectivity : forall {x : Int64} {y : Int64} . to_b_signed x = to_b_signed y -> x = y.
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
  : forall (x : Int64) (y : Int64) .
      (pi_1 (add_with_overflow x y))%product = 0%bit ->
      (Bit.to_b0 (sign_bit x) + Bit.to_b0 (sign_bit y)
        = Bit.to_b0 (pi_1 (add_with_carry 0 x y))%product
          + Bit.to_b0 (sign_bit (x + y)%int64))%b0.
Proof.
  intros x y o.
  match &x with | introduction xb7 xb6 xb5 xb4 xb3 xb2 xb1 xb0 end.
  match &xb7 with | introduction x63 x62 x61 x60 x59 x58 x57 x56 end.
  match &xb6 with | introduction x55 x54 x53 x52 x51 x50 x49 x48 end.
  match &xb5 with | introduction x47 x46 x45 x44 x43 x42 x41 x40 end.
  match &xb4 with | introduction x39 x38 x37 x36 x35 x34 x33 x32 end.
  match &xb3 with | introduction x31 x30 x29 x28 x27 x26 x25 x24 end.
  match &xb2 with | introduction x23 x22 x21 x20 x19 x18 x17 x16 end.
  match &xb1 with | introduction x15 x14 x13 x12 x11 x10 x9 x8 end.
  match &xb0 with | introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | introduction yb7 yb6 yb5 yb4 yb3 yb2 yb1 yb0 end.
  match &yb7 with | introduction y63 y62 y61 y60 y59 y58 y57 y56 end.
  match &yb6 with | introduction y55 y54 y53 y52 y51 y50 y49 y48 end.
  match &yb5 with | introduction y47 y46 y45 y44 y43 y42 y41 y40 end.
  match &yb4 with | introduction y39 y38 y37 y36 y35 y34 y33 y32 end.
  match &yb3 with | introduction y31 y30 y29 y28 y27 y26 y25 y24 end.
  match &yb2 with | introduction y23 y22 y21 y20 y19 y18 y17 y16 end.
  match &yb1 with | introduction y15 y14 y13 y12 y11 y10 y9 y8 end.
  match &yb0 with | introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
  simpl in &o |- *.
  ipso (Bit.conversion.binary.carry.conservation _ &x63 &y63 &o).
Qed.

(* conversion.addition *)
Theorem addition
  : forall (x : Int64) (y : Int64) .
      (pi_1 (add_with_overflow x y))%product = 0%bit ->
      to_b_signed (x + y) = (x + y)%b_signed.
Proof.
  intros x y o.
  let proof t := conversion.sign &x &y &o.
  let proof a
    : (unsigned_value &x + unsigned_value &y
        = modulus * Bit.to_b0 (pi_1 (add_with_carry 0 &x &y))%product
          + unsigned_value (&x + &y)%int64)%b0
    := reinterpretation.carry 0 &x &y.
  lemma balance
    : (unsigned_value (&x + &y)%int64
        + (modulus * Bit.to_b0 (sign_bit &x)
          + modulus * Bit.to_b0 (sign_bit &y))
        = (unsigned_value &x + unsigned_value &y)
          + modulus * Bit.to_b0 (sign_bit (&x + &y)%int64))%b0.
  {
    match (Bin0.multiplication.distributivity.over.addition
            modulus
            (Bit.to_b0 (sign_bit &x)) (Bit.to_b0 (sign_bit &y)))
    with | signs _ end.
    match (Bin0.multiplication.distributivity.over.addition
            modulus
            (Bit.to_b0 (pi_1 (add_with_carry 0 &x &y))%product)
            (Bit.to_b0 (sign_bit (&x + &y)%int64)))
    with | carries _ end.
    leibniz
      <- &signs,
      &t,
      &carries,
      <- (Bin0.addition.associativity
        (unsigned_value (&x + &y)%int64)
        (modulus
          * Bit.to_b0 (pi_1 (add_with_carry 0 &x &y))%product)%b0
        (modulus * Bit.to_b0 (sign_bit (&x + &y)%int64))%b0),
      (Bin0.addition.commutativity
        (unsigned_value (&x + &y)%int64)
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
  : forall (x63 : Bit) (x62 : Bit) (x61 : Bit) (x60 : Bit)
      (x59 : Bit) (x58 : Bit) (x57 : Bit) (x56 : Bit)
      (x55 : Bit) (x54 : Bit) (x53 : Bit) (x52 : Bit)
      (x51 : Bit) (x50 : Bit) (x49 : Bit) (x48 : Bit)
      (x47 : Bit) (x46 : Bit) (x45 : Bit) (x44 : Bit)
      (x43 : Bit) (x42 : Bit) (x41 : Bit) (x40 : Bit)
      (x39 : Bit) (x38 : Bit) (x37 : Bit) (x36 : Bit)
      (x35 : Bit) (x34 : Bit) (x33 : Bit) (x32 : Bit)
      (x31 : Bit) (x30 : Bit) (x29 : Bit) (x28 : Bit)
      (x27 : Bit) (x26 : Bit) (x25 : Bit) (x24 : Bit)
      (x23 : Bit) (x22 : Bit) (x21 : Bit) (x20 : Bit)
      (x19 : Bit) (x18 : Bit) (x17 : Bit) (x16 : Bit)
      (x15 : Bit) (x14 : Bit) (x13 : Bit) (x12 : Bit)
      (x11 : Bit) (x10 : Bit) (x9 : Bit) (x8 : Bit)
      (x7 : Bit) (x6 : Bit) (x5 : Bit) (x4 : Bit)
      (x3 : Bit) (x2 : Bit) (x1 : Bit) (x0 : Bit) .
      to_b_signed (Int64.introduction (Byte.introduction x63 x62 x61 x60 x59 x58 x57 x56)
                (Byte.introduction x55 x54 x53 x52 x51 x50 x49 x48)
                (Byte.introduction x47 x46 x45 x44 x43 x42 x41 x40)
                (Byte.introduction x39 x38 x37 x36 x35 x34 x33 x32)
                (Byte.introduction x31 x30 x29 x28 x27 x26 x25 x24)
                (Byte.introduction x23 x22 x21 x20 x19 x18 x17 x16)
                (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8)
                (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0))
      = (10
          * shift_right
            (Int64.introduction (Byte.introduction x63 x62 x61 x60 x59 x58 x57 x56)
              (Byte.introduction x55 x54 x53 x52 x51 x50 x49 x48)
              (Byte.introduction x47 x46 x45 x44 x43 x42 x41 x40)
              (Byte.introduction x39 x38 x37 x36 x35 x34 x33 x32)
              (Byte.introduction x31 x30 x29 x28 x27 x26 x25 x24)
              (Byte.introduction x23 x22 x21 x20 x19 x18 x17 x16)
              (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8)
              (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0)) 1%n0
          + Bit.to_b0 x0)%b_signed.
Proof.
  intros x63 x62 x61 x60 x59 x58 x57 x56 x55 x54 x53 x52 x51 x50 x49 x48 x47 x46 x45 x44 x43 x42 x41
    x40 x39 x38 x37 x36 x35 x34 x33 x32 x31 x30 x29 x28 x27 x26 x25 x24 x23 x22 x21 x20 x19 x18 x17
    x16 x15 x14 x13 x12 x11 x10 x9 x8 x7 x6 x5 x4 x3 x2 x1 x0.
  lemma shifted
    : shift_right
        (Int64.introduction (Byte.introduction &x63 &x62 &x61 &x60 &x59 &x58 &x57 &x56)
          (Byte.introduction &x55 &x54 &x53 &x52 &x51 &x50 &x49 &x48)
          (Byte.introduction &x47 &x46 &x45 &x44 &x43 &x42 &x41 &x40)
          (Byte.introduction &x39 &x38 &x37 &x36 &x35 &x34 &x33 &x32)
          (Byte.introduction &x31 &x30 &x29 &x28 &x27 &x26 &x25 &x24)
          (Byte.introduction &x23 &x22 &x21 &x20 &x19 &x18 &x17 &x16)
          (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
          (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)) 1%n0
      = Int64.introduction (Byte.introduction &x63 &x63 &x62 &x61 &x60 &x59 &x58 &x57)
        (Byte.introduction &x56 &x55 &x54 &x53 &x52 &x51 &x50 &x49)
        (Byte.introduction &x48 &x47 &x46 &x45 &x44 &x43 &x42 &x41)
        (Byte.introduction &x40 &x39 &x38 &x37 &x36 &x35 &x34 &x33)
        (Byte.introduction &x32 &x31 &x30 &x29 &x28 &x27 &x26 &x25)
        (Byte.introduction &x24 &x23 &x22 &x21 &x20 &x19 &x18 &x17)
        (Byte.introduction &x16 &x15 &x14 &x13 &x12 &x11 &x10 &x9)
        (Byte.introduction &x8 &x7 &x6 &x5 &x4 &x3 &x2 &x1).
  {
    simpl in |- *.
    quod idem est.
  }
  lemma split
    : (10 * unsigned_value
              (Int64.introduction (Byte.introduction &x63 &x63 &x62 &x61 &x60 &x59 &x58 &x57)
                (Byte.introduction &x56 &x55 &x54 &x53 &x52 &x51 &x50 &x49)
                (Byte.introduction &x48 &x47 &x46 &x45 &x44 &x43 &x42 &x41)
                (Byte.introduction &x40 &x39 &x38 &x37 &x36 &x35 &x34 &x33)
                (Byte.introduction &x32 &x31 &x30 &x29 &x28 &x27 &x26 &x25)
                (Byte.introduction &x24 &x23 &x22 &x21 &x20 &x19 &x18 &x17)
                (Byte.introduction &x16 &x15 &x14 &x13 &x12 &x11 &x10 &x9)
                (Byte.introduction &x8 &x7 &x6 &x5 &x4 &x3 &x2 &x1))
        + Bit.to_b0 &x0
        = Bit.to_b0 &x63 * modulus
          + unsigned_value
              (Int64.introduction
                (Byte.introduction &x63 &x62 &x61 &x60 &x59 &x58 &x57 &x56)
                  (Byte.introduction &x55 &x54 &x53 &x52 &x51 &x50 &x49 &x48)
                  (Byte.introduction &x47 &x46 &x45 &x44 &x43 &x42 &x41 &x40)
                  (Byte.introduction &x39 &x38 &x37 &x36 &x35 &x34 &x33 &x32)
                  (Byte.introduction &x31 &x30 &x29 &x28 &x27 &x26 &x25 &x24)
                  (Byte.introduction &x23 &x22 &x21 &x20 &x19 &x18 &x17 &x16)
                  (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
                  (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)))%b0.
  {
    lemma top
      : (Bit.to_b0 &x63 = Bit.to_b0 &x63 * 1 + 0)%b0.
    {
      match (Bin0.addition.identity (Bit.to_b0 &x63 * 1)%b0)
      with | _ sum end.
      match (Bin0.multiplication.identity (Bit.to_b0 &x63))
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
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x32
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x33
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x34
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x35
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x36
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x37
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x38
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x39
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x40
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x41
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x42
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x43
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x44
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x45
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x46
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x47
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x48
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x49
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x50
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x51
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x52
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x53
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x54
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x55
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x56
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x57
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x58
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x59
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x60
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x61
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x62
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x63
      &top)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
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
        (Int64.introduction (Byte.introduction &x63 &x62 &x61 &x60 &x59 &x58 &x57 &x56)
          (Byte.introduction &x55 &x54 &x53 &x52 &x51 &x50 &x49 &x48)
          (Byte.introduction &x47 &x46 &x45 &x44 &x43 &x42 &x41 &x40)
          (Byte.introduction &x39 &x38 &x37 &x36 &x35 &x34 &x33 &x32)
          (Byte.introduction &x31 &x30 &x29 &x28 &x27 &x26 &x25 &x24)
          (Byte.introduction &x23 &x22 &x21 &x20 &x19 &x18 &x17 &x16)
          (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
          (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0))
        + (modulus * Bit.to_b0 &x63 + modulus * Bit.to_b0 &x63 + 0)
        = (unsigned_value
            (Int64.introduction (Byte.introduction &x63 &x63 &x62 &x61 &x60 &x59 &x58 &x57)
              (Byte.introduction &x56 &x55 &x54 &x53 &x52 &x51 &x50 &x49)
              (Byte.introduction &x48 &x47 &x46 &x45 &x44 &x43 &x42 &x41)
              (Byte.introduction &x40 &x39 &x38 &x37 &x36 &x35 &x34 &x33)
              (Byte.introduction &x32 &x31 &x30 &x29 &x28 &x27 &x26 &x25)
              (Byte.introduction &x24 &x23 &x22 &x21 &x20 &x19 &x18 &x17)
              (Byte.introduction &x16 &x15 &x14 &x13 &x12 &x11 &x10 &x9)
              (Byte.introduction &x8 &x7 &x6 &x5 &x4 &x3 &x2 &x1))
          + unsigned_value
              (Int64.introduction (Byte.introduction &x63 &x63 &x62 &x61 &x60 &x59 &x58 &x57)
                (Byte.introduction &x56 &x55 &x54 &x53 &x52 &x51 &x50 &x49)
                (Byte.introduction &x48 &x47 &x46 &x45 &x44 &x43 &x42 &x41)
                (Byte.introduction &x40 &x39 &x38 &x37 &x36 &x35 &x34 &x33)
                (Byte.introduction &x32 &x31 &x30 &x29 &x28 &x27 &x26 &x25)
                (Byte.introduction &x24 &x23 &x22 &x21 &x20 &x19 &x18 &x17)
                (Byte.introduction &x16 &x15 &x14 &x13 &x12 &x11 &x10 &x9)
                (Byte.introduction &x8 &x7 &x6 &x5 &x4 &x3 &x2 &x1))
          + Bit.to_b0 &x0)
          + modulus * Bit.to_b0 &x63)%b0.
  {
    match (Bin0.addition.identity
            (modulus * Bit.to_b0 &x63
              + modulus * Bit.to_b0 &x63)%b0)
    with | _ unit end.
    leibniz
      &unit,
      (&doubled
        (unsigned_value
          (Int64.introduction (Byte.introduction &x63 &x63 &x62 &x61 &x60 &x59 &x58 &x57)
            (Byte.introduction &x56 &x55 &x54 &x53 &x52 &x51 &x50 &x49)
            (Byte.introduction &x48 &x47 &x46 &x45 &x44 &x43 &x42 &x41)
            (Byte.introduction &x40 &x39 &x38 &x37 &x36 &x35 &x34 &x33)
            (Byte.introduction &x32 &x31 &x30 &x29 &x28 &x27 &x26 &x25)
            (Byte.introduction &x24 &x23 &x22 &x21 &x20 &x19 &x18 &x17)
            (Byte.introduction &x16 &x15 &x14 &x13 &x12 &x11 &x10 &x9)
            (Byte.introduction &x8 &x7 &x6 &x5 &x4 &x3 &x2 &x1)))),
      &split,
      (Bin0.multiplication.commutativity
        (Bit.to_b0 &x63) modulus),
      (Bin0.addition.commutativity
        (modulus * Bit.to_b0 &x63)%b0
        (unsigned_value
          (Int64.introduction (Byte.introduction &x63 &x62 &x61 &x60 &x59 &x58 &x57 &x56)
            (Byte.introduction &x55 &x54 &x53 &x52 &x51 &x50 &x49 &x48)
            (Byte.introduction &x47 &x46 &x45 &x44 &x43 &x42 &x41 &x40)
            (Byte.introduction &x39 &x38 &x37 &x36 &x35 &x34 &x33 &x32)
            (Byte.introduction &x31 &x30 &x29 &x28 &x27 &x26 &x25 &x24)
            (Byte.introduction &x23 &x22 &x21 &x20 &x19 &x18 &x17 &x16)
            (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
            (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)))),
      (Bin0.addition.associativity
        (unsigned_value
          (Int64.introduction (Byte.introduction &x63 &x62 &x61 &x60 &x59 &x58 &x57 &x56)
            (Byte.introduction &x55 &x54 &x53 &x52 &x51 &x50 &x49 &x48)
            (Byte.introduction &x47 &x46 &x45 &x44 &x43 &x42 &x41 &x40)
            (Byte.introduction &x39 &x38 &x37 &x36 &x35 &x34 &x33 &x32)
            (Byte.introduction &x31 &x30 &x29 &x28 &x27 &x26 &x25 &x24)
            (Byte.introduction &x23 &x22 &x21 &x20 &x19 &x18 &x17 &x16)
            (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
            (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)))
        (modulus * Bit.to_b0 &x63)%b0
        (modulus * Bit.to_b0 &x63)%b0)
      in |- *.
    quod idem est.
  }
  leibniz &shifted in |- *.
  simpl to_b_signed, sign_bit in |- *.
  leibniz
    (&twice
      (SignedBin.b0_difference
        (unsigned_value
          (Int64.introduction (Byte.introduction &x63 &x63 &x62 &x61 &x60 &x59 &x58 &x57)
            (Byte.introduction &x56 &x55 &x54 &x53 &x52 &x51 &x50 &x49)
            (Byte.introduction &x48 &x47 &x46 &x45 &x44 &x43 &x42 &x41)
            (Byte.introduction &x40 &x39 &x38 &x37 &x36 &x35 &x34 &x33)
            (Byte.introduction &x32 &x31 &x30 &x29 &x28 &x27 &x26 &x25)
            (Byte.introduction &x24 &x23 &x22 &x21 &x20 &x19 &x18 &x17)
            (Byte.introduction &x16 &x15 &x14 &x13 &x12 &x11 &x10 &x9)
            (Byte.introduction &x8 &x7 &x6 &x5 &x4 &x3 &x2 &x1)))
        (modulus * Bit.to_b0 &x63)%b0)),
    (SignedBin.difference.additivity
      (unsigned_value
        (Int64.introduction (Byte.introduction &x63 &x63 &x62 &x61 &x60 &x59 &x58 &x57)
          (Byte.introduction &x56 &x55 &x54 &x53 &x52 &x51 &x50 &x49)
          (Byte.introduction &x48 &x47 &x46 &x45 &x44 &x43 &x42 &x41)
          (Byte.introduction &x40 &x39 &x38 &x37 &x36 &x35 &x34 &x33)
          (Byte.introduction &x32 &x31 &x30 &x29 &x28 &x27 &x26 &x25)
          (Byte.introduction &x24 &x23 &x22 &x21 &x20 &x19 &x18 &x17)
          (Byte.introduction &x16 &x15 &x14 &x13 &x12 &x11 &x10 &x9)
          (Byte.introduction &x8 &x7 &x6 &x5 &x4 &x3 &x2 &x1)))
      (modulus * Bit.to_b0 &x63)%b0
      (unsigned_value
        (Int64.introduction (Byte.introduction &x63 &x63 &x62 &x61 &x60 &x59 &x58 &x57)
          (Byte.introduction &x56 &x55 &x54 &x53 &x52 &x51 &x50 &x49)
          (Byte.introduction &x48 &x47 &x46 &x45 &x44 &x43 &x42 &x41)
          (Byte.introduction &x40 &x39 &x38 &x37 &x36 &x35 &x34 &x33)
          (Byte.introduction &x32 &x31 &x30 &x29 &x28 &x27 &x26 &x25)
          (Byte.introduction &x24 &x23 &x22 &x21 &x20 &x19 &x18 &x17)
          (Byte.introduction &x16 &x15 &x14 &x13 &x12 &x11 &x10 &x9)
          (Byte.introduction &x8 &x7 &x6 &x5 &x4 &x3 &x2 &x1)))
      (modulus * Bit.to_b0 &x63)%b0),
    (&embedding (Bit.to_b0 &x0)),
    (SignedBin.difference.additivity
      (unsigned_value
        (Int64.introduction (Byte.introduction &x63 &x63 &x62 &x61 &x60 &x59 &x58 &x57)
          (Byte.introduction &x56 &x55 &x54 &x53 &x52 &x51 &x50 &x49)
          (Byte.introduction &x48 &x47 &x46 &x45 &x44 &x43 &x42 &x41)
          (Byte.introduction &x40 &x39 &x38 &x37 &x36 &x35 &x34 &x33)
          (Byte.introduction &x32 &x31 &x30 &x29 &x28 &x27 &x26 &x25)
          (Byte.introduction &x24 &x23 &x22 &x21 &x20 &x19 &x18 &x17)
          (Byte.introduction &x16 &x15 &x14 &x13 &x12 &x11 &x10 &x9)
          (Byte.introduction &x8 &x7 &x6 &x5 &x4 &x3 &x2 &x1))
        + unsigned_value
            (Int64.introduction
              (Byte.introduction &x63 &x63 &x62 &x61 &x60 &x59 &x58 &x57)
                (Byte.introduction &x56 &x55 &x54 &x53 &x52 &x51 &x50 &x49)
                (Byte.introduction &x48 &x47 &x46 &x45 &x44 &x43 &x42 &x41)
                (Byte.introduction &x40 &x39 &x38 &x37 &x36 &x35 &x34 &x33)
                (Byte.introduction &x32 &x31 &x30 &x29 &x28 &x27 &x26 &x25)
                (Byte.introduction &x24 &x23 &x22 &x21 &x20 &x19 &x18 &x17)
                (Byte.introduction &x16 &x15 &x14 &x13 &x12 &x11 &x10 &x9)
                (Byte.introduction &x8 &x7 &x6 &x5 &x4 &x3 &x2 &x1)))%b0
      (modulus * Bit.to_b0 &x63
        + modulus * Bit.to_b0 &x63)%b0
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
  : forall (x : Int64) (p : Bin) .
      to_b_signed x = SignedBin.Positive p
      -> (p < 1000000000000000000000000000000000000000000000000000000000000000)%b0.
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
  : forall (x : Int64) (p : Bin) .
      to_b_signed x = SignedBin.Negative p
      -> (p <= 1000000000000000000000000000000000000000000000000000000000000000)%b0.
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
        (Bin0.Positive p)
        1000000000000000000000000000000000000000000000000000000000000000%b0)
    with
    | below | rest end.
    + simpl Bin0.LessOrEqual in |- *.
      ipso (disjoin _, &below).
    + match &rest with | same | above end.
      * simpl Bin0.LessOrEqual in |- *.
        ipso (disjoin &same, _).
      * lemma double
          : (1000000000000000000000000000000000000000000000000000000000000000
              + 1000000000000000000000000000000000000000000000000000000000000000
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
      (n < 1000000000000000000000000000000000000000000000000000000000000000)%b0
      -> to_b_signed (from_b_signed (SignedBin.from_b0 n)) = SignedBin.from_b0 n.
Proof.
  intros n h.
  lemma half
    : (1000000000000000000000000000000000000000000000000000000000000000
        < modulus)%b0.
  {
    simpl Bin0.LessThan in |- *.
    exists 1000000000000000000000000000000000000000000000000000000000000000%b.
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
      (p <= 1000000000000000000000000000000000000000000000000000000000000000)%b0
      -> to_b_signed (from_b_signed (SignedBin.Negative p)) = SignedBin.Negative p.
Proof.
  intros p h.
  leibniz (conversion.signed_bin.negative &p) in |- *.
  lemma half
    : (1000000000000000000000000000000000000000000000000000000000000000
        < modulus)%b0.
  {
    simpl Bin0.LessThan in |- *.
    exists 1000000000000000000000000000000000000000000000000000000000000000%b.
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
    : (1000000000000000000000000000000000000000000000000000000000000000
        + 1000000000000000000000000000000000000000000000000000000000000000
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
  : forall (x : Int64) (y : Int64) (d : Bin) .
      to_b_signed y = SignedBin.Positive d -> Option.map to_b_signed (x /. y)%int64 = Some (x /. d)%b_signed.
Proof.
  intros x y d e.
  lemma origin : to_b_signed (from_b_signed 0%b_signed) = 0%b_signed.
  {
    lemma nothing
      : (0 < 1000000000000000000000000000000000000000000000000000000000000000)%b0.
    {
      simpl Bin0.LessThan in |- *.
      exists 1000000000000000000000000000000000000000000000000000000000000000%b.
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
        lemma bounded
          : (q <= 1000000000000000000000000000000000000000000000000000000000000000)%b0.
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
  : forall (x : Int64) (y : Int64) (d : Bin) .
      to_b_signed y = SignedBin.Negative d
      -> ~ (to_b_signed x = (-1000000000000000000000000000000000000000000000000000000000000000)%b_signed
            /\ d = Bin.One)
      -> Option.map to_b_signed (x /. y)%int64 = Some (SignedBin.negate (x /. d)%b_signed).
Proof.
  intros x y d e h.
  lemma origin : to_b_signed (from_b_signed 0%b_signed) = 0%b_signed.
  {
    lemma nothing
      : (0 < 1000000000000000000000000000000000000000000000000000000000000000)%b0.
    {
      simpl Bin0.LessThan in |- *.
      exists 1000000000000000000000000000000000000000000000000000000000000000%b.
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
      lemma below
        : ((p /. &d)
            < 1000000000000000000000000000000000000000000000000000000000000000)%b0.
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
                  (refl
                    (-1000000000000000000000000000000000000000000000000000000000000000)%b_signed),
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
        lemma bounded
          : (q <= 1000000000000000000000000000000000000000000000000000000000000000)%b0.
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

Module dword. (* conversion.dword *)

(* conversion.dword.retraction *)
Theorem retraction : forall (w : DWord) . to_dword (DWord.endian w) (from_dword w) = w.
Proof.
  intros w.
  match &w with | introduction e b0 b1 b2 b3 b4 b5 b6 b7 end.
  match &e with | Little | Big end;
    simpl from_dword, to_dword in |- *;
    simpl in |- *;
    quod idem est.
Qed.

(* conversion.dword.section *)
Theorem section : forall (e : Endian) (x : Int64) . from_dword (to_dword e x) = x.
Proof.
  intros e x.
  match &x with | introduction b7 b6 b5 b4 b3 b2 b1 b0 end.
  match &e with | Little | Big end;
    simpl from_dword, to_dword in |- *;
    simpl in |- *;
    quod idem est.
Qed.

End dword. (* conversion.dword *)

End conversion. (* conversion *)

(* [Int64] as a [Signed.Width]: its operations, the laws above, and its
 * constants, 2^63, 2^64 and 3 * 2^63. The facts about fixed values are closed
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
Definition half :=
  1000000000000000000000000000000000000000000000000000000000000000%b.
Definition modulus := modulus.
Definition beyond :=
  11000000000000000000000000000000000000000000000000000000000000000%b.

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

Definition section := Int64.conversion.section.

Theorem comparison
  : forall (x : T) (y : T) . compare x y = SignedBin.compare (to_b_signed x) (to_b_signed y).
Proof.
  intros x y.
  ipso (refl (compare &x &y)).
Qed.

Definition addition := Int64.conversion.addition.
Definition difference := Int64.conversion.difference.

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

Definition positive := Int64.conversion.boundedness.positive.
Definition negative := Int64.conversion.boundedness.negative.

End boundedness. (* Width.conversion.boundedness *)

Module retraction. (* Width.conversion.retraction *)

Definition nonnegative := Int64.conversion.retraction.nonnegative.
Definition negative := Int64.conversion.retraction.negative.

End retraction. (* Width.conversion.retraction *)

End conversion. (* Width.conversion *)

Module reinterpretation. (* Width.reinterpretation *)

Definition boundedness := Int64.reinterpretation.boundedness.
Definition injectivity := @Int64.reinterpretation.injectivity.
Definition multiplication := Int64.reinterpretation.multiplication.
Definition reduction := Int64.reinterpretation.reduction.

Module reduction. (* Width.reinterpretation.reduction *)

Definition additivity := Int64.reinterpretation.reduction.additivity.

Theorem zero : from_b0 Bin0.Zero = Zero.
Proof.
  ipso (refl Zero).
Qed.

End reduction. (* Width.reinterpretation.reduction *)

End reinterpretation. (* Width.reinterpretation *)

Module addition. (* Width.addition *)

Definition associativity := Int64.addition.associativity.
Definition commutativity := Int64.addition.commutativity.
Definition identity := Int64.addition.identity.
Definition inverse := Int64.addition.inverse.

End addition. (* Width.addition *)

Module multiplication. (* Width.multiplication *)

Definition annihilation := Int64.multiplication.annihilation.

Module left. (* Width.multiplication.left *)

Definition negation := Int64.multiplication.left.negation.

End left. (* Width.multiplication.left *)

Module right. (* Width.multiplication.right *)

Definition negation := Int64.multiplication.right.negation.

End right. (* Width.multiplication.right *)

End multiplication. (* Width.multiplication *)

Module subtraction. (* Width.subtraction *)

Definition specification := Int64.subtraction.specification.

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
  exists 111111111111111111111111111111111111111111111111111111111111111%b.
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

End Int64. (* Int64 *)

Abbreviation Int64 := Int64.T.

Export (notations) Int64.

(* A number of the type is written in decimal or hexadecimal under its
 * scope, [100%int64], [(-100)%int64] or [0x7F%int64], and a closed one prints
 * in decimal.
 *)
Number Notation Int64.T Int64.from_numeral Int64.to_numeral
  : jw_int64_scope.

(* Where an [Int64] is expected, a literal or a notation reads in this scope
 * without its [%int64].
 *)
Bind Scope jw_int64_scope with Int64.T.

(* An [Int64] stands wherever a [SignedBin] is expected, read as its value in two's
 * complement, and wherever an [Integer] is, through that value; each
 * conversion is printed where it happened.
 *)
Coercion Int64.to_b_signed : Int64 >-> SignedBin.
Add Printing Coercion Int64.to_b_signed.
Coercion Int64.to_integer : Int64 >-> Integer.
Add Printing Coercion Int64.to_integer.

(* Declared inside [Module Int64]; an instance declared there is dropped at
 * the module's [End], so it is announced again here.
 *)
Existing Instance Int64.comparable.

Instance Int64_add_monoid
  : Monoid Int64.add Int64.Zero :=
  {| Monoid.semigroup :=
      {| Semigroup.associativity := Int64.addition.associativity |}
  ; Monoid.identity := Int64.addition.identity |}.

Instance Int64_mul_monoid
  : Monoid Int64.mul Int64.One :=
  {| Monoid.semigroup :=
      {| Semigroup.associativity := Int64.multiplication.associativity |}
  ; Monoid.identity := Int64.multiplication.identity |}.

Instance Int64_add_commutative
  : Commutative Int64.add :=
  {| Commutative.commutativity := Int64.addition.commutativity |}.

Instance Int64_mul_commutative
  : Commutative Int64.mul :=
  {| Commutative.commutativity := Int64.multiplication.commutativity |}.

Instance Int64_add_group
  : Group Int64.add Int64.Zero Int64.negate :=
  {| Group.monoid := Int64_add_monoid
  ; Group.inverse := Int64.addition.inverse |}.

Instance Int64_add_abelian_group
  : AbelianGroup Int64.add Int64.Zero Int64.negate :=
  {| AbelianGroup.group := Int64_add_group
  ; AbelianGroup.commutative := Int64_add_commutative |}.

Instance Int64_ring
  : Ring Int64.add Int64.Zero Int64.negate Int64.mul Int64.One :=
  {| Ring.abelian_group := Int64_add_abelian_group
  ; Ring.monoid := Int64_mul_monoid
  ; Ring.distributivity := Int64.multiplication.distributivity.over.addition |}.
