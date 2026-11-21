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
From JW Require Import Data.Machine.Unsigned.
From JW Require Import Data.Number.Binary.SignedBin.
From JW Require Import Data.Number.Binary.BinBase.
From JW Require Import Data.Number.Binary.Bin0.
From JW Require Import Data.Number.Nat.
From JW Require Import Data.Number.Nat0.
From JW Require Import Data.Number.Numeral.
From JW Require Import Data.Option.
From JW Require Import Data.Product.
From JW Require Import Tactics.Equation.
From JW Require Import Tactics.Modus.

(* An unsigned integer of sixteen bits: two [Byte]s read as a number from 0 to
 * 65535 (2^16 - 1), its arithmetic wrapping modulo 65536 (2^16). In this file
 * [10000000000000000] is 2^16, written in binary digits.
 *)

Module UInt16. (* UInt16 *)

Inductive T : Type :=
  | introduction : Byte -> Byte -> T.

Abbreviation UInt16 := T.

(* The number of values, 65536 (2^16), the arithmetic wrapping modulo it. *)
(* [BinBase] *)
Definition modulus := 10000000000000000%bin_base.

(* [x] laid out as a [HWord] in the order [e] names. *)
(* [Endian -> UInt16 -> HWord] *)
Definition to_hword := fun (e : Endian) (x : UInt16) .
  match x with
  | UInt16.introduction b1 b0 => HWord.make e b0 b1
  end.

(* The value of the bytes of [w], whatever the order they are laid out in. *)
(* [HWord -> UInt16] *)
Definition from_hword := fun (w : HWord) . UInt16.introduction (HWord.high w) (HWord.low w).

(* The bits read as a number in base two, the most significant first; [10]
 * is two in binary digits.
 *)
(* [UInt16 -> Bin0] *)
Definition to_b0 := fun (x : UInt16) .
  match x with
  | UInt16.introduction (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8)
      (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
      (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (
        10 * Bit.to_b0 x15 + Bit.to_b0 x14) + Bit.to_b0 x13)
        + Bit.to_b0 x12) + Bit.to_b0 x11) + Bit.to_b0 x10)
        + Bit.to_b0 x9) + Bit.to_b0 x8) + Bit.to_b0 x7)
        + Bit.to_b0 x6) + Bit.to_b0 x5) + Bit.to_b0 x4)
        + Bit.to_b0 x3) + Bit.to_b0 x2) + Bit.to_b0 x1)
        + Bit.to_b0 x0)%b0
  end.

(* From here to the end of the module a [UInt16] stands where a [Bin0] is
 * expected, read as its value; the conversion is printed.
 *)
Local Coercion to_b0 : T >-> Bin0.
Add Printing Coercion to_b0.

(* The value as a [SignedBin], through [to_b0]. *)
(* [UInt16 -> SignedBin] *)
Definition to_b_signed := fun (x : UInt16) . SignedBin.from_b0 (to_b0 x).

(* The value in [Nat0], through [to_b0]; [Nat0] is unary, so it is
 * for stating and proving, and computing goes through [to_b0].
 *)
(* [UInt16 -> Nat0] *)
Definition to_nat0 := fun (x : UInt16) . Bin0.to_nat0 (to_b0 x).

(* [UInt16] *)
Definition Zero := UInt16.introduction Byte.Zero Byte.Zero.

(* [UInt16] *)
Definition One :=
  UInt16.introduction
    Byte.Zero
    (Byte.introduction
      0 0 0 0 0 0 0 1).

(* The greatest value, 65535: every bit set. *)
(* [UInt16] *)
Definition Max :=
  UInt16.introduction
    (Byte.introduction
      1 1 1 1 1 1 1 1)
    (Byte.introduction
      1 1 1 1 1 1 1 1).

(* [k] places toward the most significant end, a 0 coming in at the
 * other; one place first, then [k - 1].
 *)
(* [UInt16 -> Nat -> UInt16] *)
Fixpoint shift_left_nat (x : UInt16) (k : Nat) : UInt16 :=
  let y :=
    match x with
    | UInt16.introduction (Byte.introduction _ x14 x13 x12 x11 x10 x9 x8)
        (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
        UInt16.introduction (Byte.introduction x14 x13 x12 x11 x10 x9 x8 x7)
          (Byte.introduction x6 x5 x4 x3 x2 x1 x0 0)
    end in
  match k with
  | Nat.One          => y
  | Nat.Successor k' => shift_left_nat y k'
  end.

(* [UInt16 -> Nat0 -> UInt16] *)
Definition shift_left := fun (x : UInt16) (k : Nat0) .
  match k with
  | Nat0.Zero       => x
  | Nat0.Positive n => shift_left_nat x n
  end.

(* [k] places toward the least significant end, a 0 coming in at the
 * other; one place first, then [k - 1].
 *)
(* [UInt16 -> Nat -> UInt16] *)
Fixpoint shift_right_nat (x : UInt16) (k : Nat) : UInt16 :=
  let y :=
    match x with
    | UInt16.introduction (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8)
        (Byte.introduction x7 x6 x5 x4 x3 x2 x1 _) =>
        UInt16.introduction (Byte.introduction 0 x15 x14 x13 x12 x11 x10 x9)
          (Byte.introduction x8 x7 x6 x5 x4 x3 x2 x1)
    end in
  match k with
  | Nat.One          => y
  | Nat.Successor k' => shift_right_nat y k'
  end.

(* [UInt16 -> Nat0 -> UInt16] *)
Definition shift_right := fun (x : UInt16) (k : Nat0) .
  match k with
  | Nat0.Zero       => x
  | Nat0.Positive n => shift_right_nat x n
  end.

(* [x] with [b] written after its lowest bit, the highest bit dropped. *)
(* [Bit -> UInt16 -> UInt16] *)
Definition append_bit := fun (b : Bit) (x : UInt16) .
  match x with
  | UInt16.introduction (Byte.introduction _ x14 x13 x12 x11 x10 x9 x8)
      (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
      UInt16.introduction (Byte.introduction x14 x13 x12 x11 x10 x9 x8 x7)
        (Byte.introduction x6 x5 x4 x3 x2 x1 x0 b)
  end.

(* The carry out and the sum of [carry + x + y], the carry rippling up from
 * the least significant place.
 *)
(* [Bit -> UInt16 -> UInt16 -> Product Bit UInt16] *)
Definition add_with_carry := fun (carry : Bit) (x : UInt16) (y : UInt16) .
  match x with
  | UInt16.introduction (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8)
      (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
      match y with
      | UInt16.introduction (Byte.introduction y15 y14 y13 y12 y11 y10 y9 y8)
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
            UInt16.introduction
              (Byte.introduction
                (pi_2 r15) (pi_2 r14) (pi_2 r13) (pi_2 r12)
                (pi_2 r11) (pi_2 r10) (pi_2 r9) (pi_2 r8))
              (Byte.introduction
                (pi_2 r7) (pi_2 r6) (pi_2 r5) (pi_2 r4)
                (pi_2 r3) (pi_2 r2) (pi_2 r1) (pi_2 r0)))
      end
  end%product.

(* [UInt16 -> UInt16 -> UInt16] *)
Definition add := fun (x : UInt16) (y : UInt16) . (pi_2 (add_with_carry 0 x y))%product.

(* [only parsing] keeps goals printing the operations by name. *)
Notation "x + y" := (add x y) (only parsing)
  : jw_uint16_scope.

(* The borrow out and the difference of [x - y - borrow], the borrow
 * rippling up as the carry does in [add_with_carry].
 *)
(* [Bit -> UInt16 -> UInt16 -> Product Bit UInt16] *)
Definition sub_with_borrow := fun (borrow : Bit) (x : UInt16) (y : UInt16) .
  match x with
  | UInt16.introduction (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8)
      (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
      match y with
      | UInt16.introduction (Byte.introduction y15 y14 y13 y12 y11 y10 y9 y8)
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
            UInt16.introduction
              (Byte.introduction
                (pi_2 r15) (pi_2 r14) (pi_2 r13) (pi_2 r12)
                (pi_2 r11) (pi_2 r10) (pi_2 r9) (pi_2 r8))
              (Byte.introduction
                (pi_2 r7) (pi_2 r6) (pi_2 r5) (pi_2 r4)
                (pi_2 r3) (pi_2 r2) (pi_2 r1) (pi_2 r0)))
      end
  end%product.

(* [UInt16 -> UInt16 -> UInt16] *)
Definition sub := fun (x : UInt16) (y : UInt16) . (pi_2 (sub_with_borrow 0 x y))%product.

Notation "x - y" := (sub x y) (only parsing)
  : jw_uint16_scope.

(* The two's complement: [x] taken from [Zero], wrapping. *)
(* [UInt16 -> UInt16] *)
Definition negate := fun (x : UInt16) . sub Zero x.

Notation "- x" := (negate x)
  (at level 35, right associativity, only parsing)
  : jw_uint16_scope.

(* [y]'s bits from the most significant, each step doubling the product so
 * far and adding [x] for a 1, all modulo 65536.
 *)
(* [UInt16 -> UInt16 -> UInt16] *)
Definition mul := fun (x : UInt16) (y : UInt16) .
  let step := fun (p : UInt16) (b : Bit) .
    add (shift_left p 1%n0)
      match b with
      | 0%bit => Zero
      | 1%bit => x
      end in
  match y with
  | UInt16.introduction (Byte.introduction y15 y14 y13 y12 y11 y10 y9 y8)
      (Byte.introduction y7 y6 y5 y4 y3 y2 y1 y0) =>
      step (step (step (step (step (step (step (step (step (step (step (step (step (step (step (step
        Zero y15) y14) y13) y12) y11) y10) y9) y8) y7) y6) y5) y4) y3) y2) y1) y0
  end.

Notation "x * y" := (mul x y) (only parsing)
  : jw_uint16_scope.

(* The flag and the wrapped product: the flag is set when the product of the
 * values is not below the modulus, as the high half of the full product is
 * then not zero.
 *)
(* [UInt16 -> UInt16 -> Product Bit UInt16] *)
Definition mul_with_overflow := fun (x : UInt16) (y : UInt16) .
  (match Bin0.compare (to_b0 x * to_b0 y)%b0
           (Bin0.Positive modulus) with
   | Comparison.Lt => 0%bit
   | Comparison.Eq => 1%bit
   | Comparison.Gt => 1%bit
   end,
   mul x y)%product.

(* [p] modulo 65536, its bits appended from the most significant. *)
(* [BinBase -> UInt16] *)
Fixpoint from_bin_base (p : BinBase) : UInt16 :=
  match p with
  | BinBase.One   => One
  | BinBase.b0 p' => append_bit 0 (from_bin_base p')
  | BinBase.b1 p' => append_bit 1 (from_bin_base p')
  end.

(* [Bin0 -> UInt16] *)
Definition from_b0 := fun (n : Bin0) .
  match n with
  | Bin0.Zero       => Zero
  | Bin0.Positive p => from_bin_base p
  end.

(* [Nat -> UInt16] *)
Definition from_nat := fun (n : Nat) . from_bin_base (BinBase.from_nat n).

(* [Nat0 -> UInt16] *)
Definition from_nat0 := fun (n : Nat0) . from_b0 (Bin0.from_nat0 n).

(* [z] modulo 65536 (2^16), a negative [z] counted down from 65536. *)
(* [SignedBin -> UInt16] *)
Definition from_b_signed := fun (z : SignedBin) .
  match z with
  | SignedBin.Negative p => negate (from_bin_base p)
  | SignedBin.Zero       => Zero
  | SignedBin.Positive p => from_bin_base p
  end.

(* The quotient through [Bin0], [None] when [y] is zero. It is at most
 * [x], so it always fits.
 *)
(* [UInt16 -> UInt16 -> Option UInt16] *)
Definition divide := fun (x : UInt16) (y : UInt16) .
  match to_b0 y with
  | Bin0.Zero       => None
  | Bin0.Positive d => Some (from_b0 (x /. d)%b0)
  end.

Notation "x /. y" := (divide x y) (only parsing)
  : jw_uint16_scope.

(* The remainder through [Bin0], [None] when [y] is zero. *)
(* [UInt16 -> UInt16 -> Option UInt16] *)
Definition modulo := fun (x : UInt16) (y : UInt16) .
  match to_b0 y with
  | Bin0.Zero       => None
  | Bin0.Positive d => Some (from_b0 (x %. d)%b0)
  end.

Notation "x %. y" := (modulo x y) (only parsing)
  : jw_uint16_scope.

(* [UInt16 -> UInt16 -> Prop] *)
Definition LessThan := fun (x : UInt16) (y : UInt16) .
  (to_b0 x < to_b0 y)%b0.

Notation "x < y" := (LessThan x y) (only parsing)
  : jw_uint16_scope.

(* [UInt16 -> UInt16 -> Prop] *)
Definition LessOrEqual := fun (x : UInt16) (y : UInt16) . x = y \/ LessThan x y.

Notation "x <= y" := (LessOrEqual x y) (only parsing)
  : jw_uint16_scope.

Notation "x > y" := (LessThan y x) (only parsing)
  : jw_uint16_scope.
Notation "x >= y" := (LessOrEqual y x) (only parsing)
  : jw_uint16_scope.

Notation "'(<)'" := LessThan (only parsing)
  : jw_uint16_scope.
Notation "'(<=)'" := LessOrEqual (only parsing)
  : jw_uint16_scope.

(* [UInt16 -> UInt16 -> Comparison] *)
Definition compare := fun (x : UInt16) (y : UInt16) .
  Bin0.compare (to_b0 x) (to_b0 y).

(* [UInt16 -> UInt16 -> Bool] *)
Abbreviation eq := (Comparable.eq compare).

(* [UInt16 -> UInt16 -> Bool] *)
Abbreviation le := (Comparable.le compare).

(* [UInt16 -> UInt16 -> UInt16] *)
Abbreviation min := (Comparable.min compare).

(* [UInt16 -> UInt16 -> UInt16] *)
Abbreviation max := (Comparable.max compare).

(* A literal of 0 to 65535, in decimal or hexadecimal, read in binary; any
 * larger is refused.
 *)
(* [Numeral.Unsigned -> Option UInt16] *)
Definition from_numeral := fun (u : Numeral.Unsigned) .
  let value :=
    match u with
    | Numeral.Unsigned.Decimal d     => Bin0.from_decimal 0%b0 d
    | Numeral.Unsigned.Hexadecimal h => Bin0.from_hexadecimal 0%b0 h
    end in
  match Bin0.compare value modulus with
  | Comparison.Lt => Some (from_b0 value)
  | Comparison.Eq => None
  | Comparison.Gt => None
  end.

(* [x] as a literal, in decimal. *)
(* [UInt16 -> Numeral.Unsigned] *)
Definition to_numeral := fun (x : UInt16) .
  Numeral.Unsigned.Decimal (Bin0.to_decimal (to_b0 x)).

Local Open Scope jw_uint16_scope.

Module conversion. (* conversion *)

(* conversion.zero *)
Theorem zero : to_b0 Zero = 0%b0.
Proof.
  simpl in |- *.
  quod idem est.
Qed.

(* conversion.one *)
Theorem one : to_b0 One = 1%b0.
Proof.
  simpl in |- *.
  quod idem est.
Qed.

(* conversion.boundedness *)
Theorem boundedness : forall (x : UInt16) . (x < modulus)%b0.
Proof.
  intros x.
  match &x with | introduction xb1 xb0 end.
  match &xb1 with | introduction x15 x14 x13 x12 x11 x10 x9 x8 end.
  match &xb0 with | introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  simpl to_b0 in |- *.
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

(* conversion.injectivity *)
Theorem injectivity
  : forall {x : UInt16} {y : UInt16} . to_b0 x = to_b0 y -> x = y.
Proof.
  intros x y e.
  match &x with | introduction xb1 xb0 end.
  match &xb1 with | introduction x15 x14 x13 x12 x11 x10 x9 x8 end.
  match &xb0 with | introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | introduction yb1 yb0 end.
  match &yb1 with | introduction y15 y14 y13 y12 y11 y10 y9 y8 end.
  match &yb0 with | introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
  simpl to_b0 in &e.
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
(* conversion.carry *)
Theorem carry
  : forall (carry : Bit) (x : UInt16) (y : UInt16) .
      (Bit.to_b0 carry + x + y
        = modulus * Bit.to_b0 (pi_1 (add_with_carry carry x y))%product
          + (pi_2 (add_with_carry carry x y))%product)%b0.
Proof.
  intros carry x y.
  match &x with | introduction xb1 xb0 end.
  match &xb1 with | introduction x15 x14 x13 x12 x11 x10 x9 x8 end.
  match &xb0 with | introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | introduction yb1 yb0 end.
  match &yb1 with | introduction y15 y14 y13 y12 y11 y10 y9 y8 end.
  match &yb0 with | introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
  simpl to_b0, add_with_carry in |- *.
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

(* conversion.borrow *)
Theorem borrow
  : forall (borrow : Bit) (x : UInt16) (y : UInt16) .
      (x + modulus * Bit.to_b0 (pi_1 (sub_with_borrow borrow x y))%product
        = y + Bit.to_b0 borrow
          + (pi_2 (sub_with_borrow borrow x y))%product)%b0.
Proof.
  intros borrow x y.
  match &x with | introduction xb1 xb0 end.
  match &xb1 with | introduction x15 x14 x13 x12 x11 x10 x9 x8 end.
  match &xb0 with | introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | introduction yb1 yb0 end.
  match &yb1 with | introduction y15 y14 y13 y12 y11 y10 y9 y8 end.
  match &yb0 with | introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
  simpl to_b0, sub_with_borrow in |- *.
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

(* conversion.addition *)
Theorem addition
  : forall (x : UInt16) (y : UInt16) .
      (to_b0 (x + y)%uint16 = (x + y) %. modulus)%b0.
Proof.
  intros x y.
  lemma witness
    : (Bit.to_b0 (pi_1 (add_with_carry 0 &x &y))%product * modulus
        + to_b0 (&x + &y)%uint16
        = to_b0 &x + to_b0 &y
      /\ to_b0 (&x + &y)%uint16 < modulus)%b0.
  {
    divide et impera.
    - simpl add in |- *.
      leibniz
        (Bin0.multiplication.commutativity
          (Bit.to_b0 (pi_1 (add_with_carry 0 &x &y))%product)
          modulus),
        <- (conversion.carry 0 &x &y)
        in |- *.
      simpl in |- *.
      quod idem est.
    - ipso (conversion.boundedness (&x + &y)).
  }
  match (Bin0.division.uniqueness
          (to_b0 &x + to_b0 &y)%b0 modulus
          (Bit.to_b0 (pi_1 (add_with_carry 0 &x &y))%product)
          (to_b0 (&x + &y)%uint16)
          &witness)
  with | _ facto end.
  ipso (symm &facto).
Qed.

(* conversion.subtraction *)
Theorem subtraction
  : forall (x : UInt16) (y : UInt16) .
      ((sub x y + y) %. modulus = x)%b0.
Proof.
  intros x y.
  lemma witness
    : (Bit.to_b0 (pi_1 (sub_with_borrow 0 &x &y))%product * modulus
        + to_b0 &x
        = to_b0 (sub &x &y) + to_b0 &y
      /\ to_b0 &x < modulus)%b0.
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
          (to_b0 &x)),
        (conversion.borrow 0 &x &y),
        (Bin0.addition.commutativity
          (to_b0 &y) (Bit.to_b0 0))
        in |- *.
      simpl in |- *.
      leibniz
        (Bin0.addition.commutativity
          (to_b0 &y)
          (to_b0 (pi_2 (sub_with_borrow 0 &x &y))%product))
        in |- *.
      quod idem est.
    - ipso (conversion.boundedness &x).
  }
  match (Bin0.division.uniqueness
          (to_b0 (sub &x &y) + to_b0 &y)%b0 modulus
          (Bit.to_b0 (pi_1 (sub_with_borrow 0 &x &y))%product)
          (to_b0 &x)
          &witness)
  with | _ facto end.
  ipso facto.
Qed.

(* conversion.negation *)
Theorem negation
  : forall (x : UInt16) .
      (((- x)%uint16 + x) %. modulus = 0)%b0.
Proof.
  intros x.
  simpl negate in |- *.
  leibniz (conversion.subtraction Zero &x), conversion.zero in |- *.
  quod idem est.
Qed.

(* The bits of [x] and then [b] read from the most significant: [b] goes in
 * below and the highest bit falls out, one
 * [Bit.conversion.binary.appending.propagation] per place.
 *)
(* conversion.appending *)
Theorem appending
  : forall (b : Bit) (x : UInt16) .
      (to_b0 (append_bit b x)
        = (10 * x + Bit.to_b0 b) %. modulus)%b0.
Proof.
  intros b x.
  match &x with | introduction xb1 xb0 end.
  match &xb1 with | introduction x15 x14 x13 x12 x11 x10 x9 x8 end.
  match &xb0 with | introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  lemma witness
    : (Bit.to_b0 &x15 * modulus
        + to_b0
            (append_bit &b
              (UInt16.introduction (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
                (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)))
        = 10
            * to_b0
                (UInt16.introduction (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
                  (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0))
          + Bit.to_b0 &b
      /\ to_b0
          (append_bit &b
            (UInt16.introduction (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
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
      simpl to_b0, append_bit in |- *.
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
        (conversion.boundedness
          (append_bit &b
            (UInt16.introduction (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
              (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)))).
  }
  match (Bin0.division.uniqueness
          (10 * to_b0
                  (UInt16.introduction
                    (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
                    (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0))
            + Bit.to_b0 &b)%b0
          modulus
          (Bit.to_b0 &x15)
          (to_b0
            (append_bit &b
              (UInt16.introduction (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
                (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0))))
          &witness)
  with | _ facto end.
  ipso (symm &facto).
Qed.

(* conversion.reduction *)
Theorem reduction
  : forall (n : Bin0) .
      to_b0 (from_b0 n) = (n %. modulus)%b0.
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
        (conversion.appending 0 (from_bin_base &p')),
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
        (conversion.appending 1 (from_bin_base &p')),
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

(* conversion.section *)
Theorem section : forall (x : UInt16) . from_b0 (to_b0 x) = x.
Proof.
  intros x.
  lemma facto
    : to_b0 (from_b0 (to_b0 &x)) = to_b0 &x.
  {
    leibniz
      (conversion.reduction (to_b0 &x)),
      (Bin0.modulo.identity
        (to_b0 &x) modulus (conversion.boundedness &x))
      in |- *.
    quod idem est.
  }
  ipso (conversion.injectivity &facto).
Qed.

Module left. (* conversion.left *)

(* conversion.left.doubling *)
Lemma doubling
  : forall (x : UInt16) .
      (to_b0 (shift_left x 1%n0) = (10 * x) %. modulus)%b0.
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
  match (Bin0.addition.identity (10 * to_b0 &x)%b0)
  with | _ sum end.
  leibniz &appended, (conversion.appending 0 &x) in |- *.
  simpl Bit.to_b0 in |- *.
  leibniz &sum in |- *.
  quod idem est.
Qed.

(* conversion.left.shift *)
Theorem shift
  : forall (x : UInt16) (k : Nat0) .
      (to_b0 (shift_left x k) = Bin0.shift_left x k %. modulus)%b0.
Proof.
  intros x k.
  match &k with | Zero | Positive n end.
  - lemma unchanged : shift_left &x 0%n0 = &x.
    {
      match &x with | introduction xb1 xb0 end.
      simpl in |- *.
      quod idem est.
    }
    leibniz &unchanged in |- *.
    simpl Bin0.shift_left in |- *.
    leibniz
      (Bin0.modulo.identity
        (to_b0 &x) modulus (conversion.boundedness &x))
      in |- *.
    quod idem est.
  - extro &x.
    match n with | One | Successor (n' by IH) end per Nat.induction.
    + intros x.
      leibniz
        (conversion.left.doubling &x),
        (Bin0.shift.left.doubling (to_b0 &x))
        in |- *.
      quod idem est.
    + intros x.
      lemma unfolding
        : shift_left &x (Nat0.Positive (Nat.Successor &n'))
          = shift_left (shift_left &x 1%n0) (Nat0.Positive &n').
      {
        match &x with | introduction xb1 xb0 end.
        simpl in |- *.
        quod idem est.
      }
      leibniz
        &unfolding,
        (&IH (shift_left &x 1%n0)),
        (conversion.left.doubling &x),
        (Bin0.shift.left.multiplication
          ((10 * to_b0 &x) %. modulus)%b0
          (Nat0.Positive &n')),
        (Bin0.modulo.product.left.absorption
          (10 * to_b0 &x)%b0
          (Bin0.shift_left 1%b0 (Nat0.Positive &n'))
          modulus),
        <- (Bin0.shift.left.multiplication
          (10 * to_b0 &x)%b0 (Nat0.Positive &n')),
        <- (Bin0.shift.left.successor (to_b0 &x) &n')
        in |- *.
      quod idem est.
Qed.

End left. (* conversion.left *)

Module right. (* conversion.right *)

(* conversion.right.halving *)
Lemma halving
  : forall (x : UInt16) .
      to_b0 (shift_right x 1%n0) = Bin0.halve x.
Proof.
  intros x.
  match &x with | introduction xb1 xb0 end.
  match &xb1 with | introduction x15 x14 x13 x12 x11 x10 x9 x8 end.
  match &xb0 with | introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  ipso
    (symm
      (Bit.conversion.binary.halving
        (to_b0
          (shift_right
            (UInt16.introduction (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
              (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0))
            1%n0))
        &x0)).
Qed.

(* conversion.right.shift *)
Theorem shift
  : forall (x : UInt16) (k : Nat0) .
      to_b0 (shift_right x k) = Bin0.shift_right x k.
Proof.
  intros x k.
  match &k with | Zero | Positive n end.
  - lemma unchanged : shift_right &x 0%n0 = &x.
    {
      match &x with | introduction xb1 xb0 end.
      simpl in |- *.
      quod idem est.
    }
    leibniz &unchanged in |- *.
    simpl Bin0.shift_right in |- *.
    quod idem est.
  - extro &x.
    match n with | One | Successor (n' by IH) end per Nat.induction.
    + intros x.
      leibniz (conversion.right.halving &x) in |- *.
      simpl Bin0.shift_right in |- *.
      simpl Bin0.shift_right_nat in |- *.
      quod idem est.
    + intros x.
      lemma unfolding
        : shift_right &x (Nat0.Positive (Nat.Successor &n'))
          = shift_right (shift_right &x 1%n0) (Nat0.Positive &n').
      {
        match &x with | introduction xb1 xb0 end.
        simpl in |- *.
        quod idem est.
      }
      lemma step
        : Bin0.shift_right (to_b0 &x) (Nat0.Positive (Nat.Successor &n'))
          = Bin0.shift_right
              (Bin0.halve (to_b0 &x)) (Nat0.Positive &n').
      {
        ipso (Bin0.shift.right.successor (to_b0 &x) (Nat0.Positive &n')).
      }
      leibniz
        &unfolding,
        (&IH (shift_right &x 1%n0)),
        (conversion.right.halving &x),
        &step
        in |- *.
      quod idem est.
Qed.

End right. (* conversion.right *)

Module multiplication. (* conversion.multiplication *)

(* One step of [mul]: the product so far doubled, plus [x] for a 1. *)
(* conversion.multiplication.step *)
Lemma step
  : forall (x : UInt16) (p : UInt16) (h : Bin0) (b : Bit) .
      (to_b0 p = (x * h) %. modulus)%b0 ->
      to_b0
        (add (shift_left p 1%n0)
          match b with
          | 0%bit => Zero
          | 1%bit => x
          end)
      = ((x * (10 * h + Bit.to_b0 b)) %. modulus)%b0.
Proof.
  intros x p h b e.
  lemma doubled
    : ((10 * to_b0 &p) %. modulus
        = (10 * (to_b0 &x * &h)) %. modulus)%b0.
  {
    leibniz
      &e,
      (Bin0.modulo.product.right.absorption
        10%b0 (to_b0 &x * &h)%b0 modulus)
      in |- *.
    quod idem est.
  }
  lemma regrouped
    : (to_b0 &x * (10 * &h) = 10 * (to_b0 &x * &h))%b0.
  {
    leibniz
      <- (Bin0.multiplication.associativity (to_b0 &x) 10%b0 &h),
      (Bin0.multiplication.commutativity (to_b0 &x) 10%b0),
      (Bin0.multiplication.associativity 10%b0 (to_b0 &x) &h)
      in |- *.
    quod idem est.
  }
  match &b with | Zero | One end.
  - lemma facto
      : to_b0 (add (shift_left &p 1%n0) Zero)
        = ((to_b0 &x * (10 * &h + Bit.to_b0 0))
            %. modulus)%b0.
    {
      match (Bin0.addition.identity (10 * to_b0 &p)%b0)
      with | _ right end.
      match (Bin0.addition.identity (10 * &h)%b0) with | _ right' end.
      leibniz
        (conversion.addition (shift_left &p 1%n0) Zero),
        (conversion.left.doubling &p),
        conversion.zero,
        (Bin0.modulo.sum.left.absorption
          (10 * to_b0 &p)%b0 0%b0 modulus),
        &right,
        &doubled
        in |- *.
      simpl Bit.to_b0 in |- *.
      leibniz &right', &regrouped in |- *.
      quod idem est.
    }
    ipso facto.
  - lemma facto
      : to_b0 (add (shift_left &p 1%n0) &x)
        = ((to_b0 &x * (10 * &h + Bit.to_b0 1))
            %. modulus)%b0.
    {
      match (Bin0.multiplication.identity (to_b0 &x)) with | _ right end.
      match (Bin0.multiplication.distributivity.over.addition
              (to_b0 &x) (10 * &h)%b0 1%b0)
      with | spread _ end.
      leibniz
        (conversion.addition (shift_left &p 1%n0) &x),
        (conversion.left.doubling &p),
        &doubled,
        (Bin0.modulo.sum.left.absorption
          (10 * (to_b0 &x * &h))%b0 (to_b0 &x)
          modulus)
        in |- *.
      simpl Bit.to_b0 in |- *.
      leibniz &spread, &right, &regrouped in |- *.
      quod idem est.
    }
    ipso facto.
Qed.

End multiplication. (* conversion.multiplication *)

(* conversion.multiplication *)
Theorem multiplication
  : forall (x : UInt16) (y : UInt16) .
      (to_b0 (x * y)%uint16 = (x * y) %. modulus)%b0.
Proof.
  intros x y.
  lemma base
    : (to_b0 Zero
        = (to_b0 &x * 0) %. modulus)%b0.
  {
    match (Bin0.multiplication.annihilation (to_b0 &x)) with | _ right end.
    leibniz &right, conversion.zero in |- *.
    simpl Bin0.modulo, Bin0.div, Product.second in |- *.
    quod idem est.
  }
  match &y with | introduction yb1 yb0 end.
  match &yb1 with | introduction y15 y14 y13 y12 y11 y10 y9 y8 end.
  match &yb0 with | introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
  simpl mul in |- *.
  ipso
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _ &base)))))))))))))))).
Qed.

(* conversion.division *)
Theorem division
  : forall (x : UInt16) (y : UInt16) (d : BinBase) .
      to_b0 y = Bin0.Positive d
      -> Option.map to_b0 (x /. y)%uint16 = Some (x /. d)%b0.
Proof.
  intros x y d e.
  lemma below : ((x /. &d) < modulus)%b0.
  {
    match (Bin0.division.quotient.boundedness x &d) with | same | smaller end.
    - leibniz &same in |- *.
      ipso (conversion.boundedness &x).
    - ipso (Bin0.order.strict.transitivity &smaller (conversion.boundedness &x)).
  }
  simpl divide in |- *.
  leibniz &e in |- *.
  simpl Option.map in |- *.
  leibniz
    (conversion.reduction (x /. &d)%b0),
    (Bin0.modulo.identity (x /. &d)%b0 modulus &below)
    in |- *.
  quod idem est.
Qed.

(* conversion.modulo *)
Theorem modulo
  : forall (x : UInt16) (y : UInt16) (d : BinBase) .
      to_b0 y = Bin0.Positive d
      -> Option.map to_b0 (x %. y)%uint16 = Some (x %. d)%b0.
Proof.
  intros x y d e.
  lemma below : ((x %. &d) < modulus)%b0.
  {
    match (Bin0.division.specification x &d) with | _ smaller end.
    let proof bound := conversion.boundedness &y.
    leibniz &e in &bound.
    ipso (Bin0.order.strict.transitivity &smaller &bound).
  }
  simpl modulo in |- *.
  leibniz &e in |- *.
  simpl Option.map in |- *.
  leibniz
    (conversion.reduction (x %. &d)%b0),
    (Bin0.modulo.identity (x %. &d)%b0 modulus &below)
    in |- *.
  quod idem est.
Qed.

Module signed_bin. (* conversion.signed_bin *)

(* conversion.signed_bin.section *)
Theorem section : forall (x : UInt16) . from_b_signed (to_b_signed x) = x.
Proof.
  intros x.
  lemma through
    : forall (n : Bin0) . from_b_signed (SignedBin.from_b0 n) = from_b0 n.
  {
    intros n.
    match &n with | Zero | Positive p end.
    - simpl SignedBin.from_b0, from_b_signed, from_b0 in |- *.
      quod idem est.
    - simpl SignedBin.from_b0, from_b_signed, from_b0 in |- *.
      quod idem est.
  }
  simpl to_b_signed in |- *.
  leibniz (&through (to_b0 &x)), (conversion.section &x) in |- *.
  quod idem est.
Qed.

End signed_bin. (* conversion.signed_bin *)

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
Theorem section : forall (e : Endian) (x : UInt16) . from_hword (to_hword e x) = x.
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

(* [UInt16] as a [Modular.Width]: its values are the residues modulo 65536,
 * and the laws of addition, subtraction and multiplication are read through
 * them.
 *)
Module Residue <: Modular.Width.

Definition T := T.
Definition Zero := Zero.
Definition One := One.
Definition to_b0 := to_b0.
Definition add := add.
Definition sub := sub.
Definition negate := negate.
Definition mul := mul.
Definition modulus := modulus.

Module conversion. (* Residue.conversion *)

Definition zero := UInt16.conversion.zero.
Definition one := UInt16.conversion.one.
Definition boundedness := UInt16.conversion.boundedness.
Definition injectivity := @UInt16.conversion.injectivity.
Definition addition := UInt16.conversion.addition.
Definition subtraction := UInt16.conversion.subtraction.
Definition negation := UInt16.conversion.negation.
Definition multiplication := UInt16.conversion.multiplication.

End conversion. (* Residue.conversion *)

End Residue.

Include Modular.Laws Residue.

(* [UInt16] as an [Unsigned.Width]: its operations, the laws above, and its
 * modulus, 65536. The facts about fixed values are closed computations,
 * checked by the kernel.
 *)
Module Width <: Unsigned.Width.

Definition T := T.
Definition Zero := Zero.
Definition One := One.
Definition Max := Max.
Definition to_b0 := to_b0.
Definition add := add.
Definition sub := sub.
Definition LessThan := LessThan.
Definition LessOrEqual := LessOrEqual.
Definition add_with_carry := add_with_carry.
Definition sub_with_borrow := sub_with_borrow.
Definition compare := compare.
Definition mul := mul.
Definition mul_with_overflow := mul_with_overflow.
Definition modulus := modulus.

Module order. (* Width.order *)

Module strict. (* Width.order.strict *)

Theorem specification
  : forall (x : T) (y : T) .
      LessThan x y <-> (to_b0 x < to_b0 y)%b0.
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

Definition zero := UInt16.conversion.zero.
Definition one := UInt16.conversion.one.
Definition boundedness := UInt16.conversion.boundedness.
Definition injectivity := @UInt16.conversion.injectivity.

Theorem comparison
  : forall (x : T) (y : T) .
      compare x y = Bin0.compare (to_b0 x) (to_b0 y).
Proof.
  intros x y.
  ipso (refl (compare &x &y)).
Qed.

Definition multiplication := UInt16.conversion.multiplication.

End conversion. (* Width.conversion *)

Module flag. (* Width.flag *)

Module addition. (* Width.flag.addition *)

Theorem specification
  : forall (x : T) (y : T) .
      (to_b0 x + to_b0 y
       = Bin0.Positive modulus
           * Bit.to_b0 (pi_1 (add_with_carry 0 x y))%product
         + to_b0 (add x y))%b0.
Proof.
  intros x y.
  ipso (UInt16.conversion.carry 0 &x &y).
Qed.

End addition. (* Width.flag.addition *)

Module subtraction. (* Width.flag.subtraction *)

Theorem specification
  : forall (x : T) (y : T) .
      (to_b0 x
         + Bin0.Positive modulus
             * Bit.to_b0 (pi_1 (sub_with_borrow 0 x y))%product
       = to_b0 y + to_b0 (sub x y))%b0.
Proof.
  intros x y.
  let proof b
    : (to_b0 &x
         + Bin0.Positive modulus
             * Bit.to_b0 (pi_1 (sub_with_borrow 0 &x &y))%product
       = (to_b0 &y + 0) + to_b0 (sub &x &y))%b0
    := UInt16.conversion.borrow 0 &x &y.
  match (Bin0.addition.identity (to_b0 &y)) with | _ r end.
  leibniz &r in &b.
  ipso &b.
Qed.

End subtraction. (* Width.flag.subtraction *)

Module multiplication. (* Width.flag.multiplication *)

Theorem specification
  : forall (x : T) (y : T) .
      mul_with_overflow x y
      = (match Bin0.compare (to_b0 x * to_b0 y)%b0
                 (Bin0.Positive modulus) with
         | Comparison.Lt => 0%bit
         | Comparison.Eq => 1%bit
         | Comparison.Gt => 1%bit
         end,
         mul x y)%product.
Proof.
  intros x y.
  ipso (refl (mul_with_overflow &x &y)).
Qed.

End multiplication. (* Width.flag.multiplication *)

End flag. (* Width.flag *)

Module maximum. (* Width.maximum *)

Theorem specification : (to_b0 Max + 1 = Bin0.Positive modulus)%b0.
Proof.
  ipso (refl (Bin0.Positive modulus)).
Qed.

End maximum. (* Width.maximum *)

End Width.

Include Unsigned.Laws Width.

Instance comparable
  : Comparable compare (<) :=
  {| Comparable.transitivity := @order.strict.transitivity
  ; Comparable.specification := comparison.specification
  ; Comparable.antisymmetry := comparison.antisymmetry |}.

End UInt16. (* UInt16 *)

Abbreviation UInt16 := UInt16.T.

Export (notations) UInt16.

(* A number of the type is written in decimal or hexadecimal under its
 * scope, [200%uint16] or [0xFF%uint16], and a closed one prints in decimal.
 *)
Number Notation UInt16.T UInt16.from_numeral UInt16.to_numeral
  : jw_uint16_scope.

(* Where a [UInt16] is expected, a literal or a notation reads in this scope
 * without its [%uint16].
 *)
Bind Scope jw_uint16_scope with UInt16.T.

(* A [UInt16] stands wherever a [Bin0] is expected, read as its value,
 * and wherever a [Nat0] is, through that value; each conversion is printed
 * where it happened.
 *)
Coercion UInt16.to_b0 : UInt16 >-> Bin0.
Add Printing Coercion UInt16.to_b0.
Coercion UInt16.to_nat0 : UInt16 >-> Nat0.
Add Printing Coercion UInt16.to_nat0.

(* Declared inside [Module UInt16]; an instance declared there is dropped at
 * the module's [End], so it is announced again here.
 *)
Existing Instance UInt16.comparable.

Instance UInt16_add_monoid
  : Monoid UInt16.add UInt16.Zero :=
  {| Monoid.semigroup :=
      {| Semigroup.associativity := UInt16.addition.associativity |}
  ; Monoid.identity := UInt16.addition.identity |}.

Instance UInt16_mul_monoid
  : Monoid UInt16.mul UInt16.One :=
  {| Monoid.semigroup :=
      {| Semigroup.associativity := UInt16.multiplication.associativity |}
  ; Monoid.identity := UInt16.multiplication.identity |}.

Instance UInt16_add_commutative
  : Commutative UInt16.add :=
  {| Commutative.commutativity := UInt16.addition.commutativity |}.

Instance UInt16_mul_commutative
  : Commutative UInt16.mul :=
  {| Commutative.commutativity := UInt16.multiplication.commutativity |}.

Instance UInt16_add_group
  : Group UInt16.add UInt16.Zero UInt16.negate :=
  {| Group.monoid := UInt16_add_monoid
  ; Group.inverse := UInt16.addition.inverse |}.

Instance UInt16_add_abelian_group
  : AbelianGroup UInt16.add UInt16.Zero UInt16.negate :=
  {| AbelianGroup.group := UInt16_add_group
  ; AbelianGroup.commutative := UInt16_add_commutative |}.

Instance UInt16_ring
  : Ring UInt16.add UInt16.Zero UInt16.negate UInt16.mul UInt16.One :=
  {| Ring.abelian_group := UInt16_add_abelian_group
  ; Ring.monoid := UInt16_mul_monoid
  ; Ring.distributivity := UInt16.multiplication.distributivity.over.addition |}.
