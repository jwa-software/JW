(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

From JW Require Import Algebra.AbelianGroup.
From JW Require Import Algebra.Cancellative.
From JW Require Import Algebra.Commutative.
From JW Require Import Algebra.Group.
From JW Require Import Algebra.Monoid.
From JW Require Import Algebra.Ring.
From JW Require Import Algebra.Semigroup.
From JW Require Import Core.All.
From JW Require Import Data.Base.Bool.
From JW Require Import Data.Base.Comparison.
From JW Require Import Data.Comparable.
From JW Require Import Data.Number.Binary.Bin.
From JW Require Import Data.Number.Binary.Bin0.
From JW Require Import Data.Number.Integer.
From JW Require Import Data.Number.Nat.
From JW Require Import Data.Number.Nat0.
From JW Require Import Data.Number.Numeral.
From JW Require Import Data.Option.
From JW Require Import Dialect.ExFalso.
From JW Require Import Dialect.Simpl.
From JW Require Import Relation.Induced.
From JW Require Import Relation.WellFounded.
From JW Require Import Tactics.Equation.
From JW Require Import Tactics.Modus.
From JW Require Import Tactics.Witness.

Local Unset Elimination Schemes.

Module SignedBin. (* SignedBin *)

(* Both sign cases wrap a [Bin], so a nonzero value carries its magnitude in
 * binary and the arithmetic reduces to [Bin]'s, as [Integer]'s reduces to
 * [Nat]'s.
 *
 * Three cases rather than a sign beside a [Bin0]: [Bin] has no zero,
 * so zero has exactly one spelling here. A sign paired with a magnitude that
 * can itself be zero admits both [+ 0] and [- 0], and equality on this type
 * is structural.
 *)
Inductive T : Type :=
  | Negative : Bin -> T
  | Zero     : T
  | Positive : Bin -> T.

Abbreviation SignedBin := T.

(* The eliminator behind the [destruct] tactic, written out: no recursion,
 * since no ctor carries a [SignedBin].
 *)
Definition induction
  : forall (P : SignedBin -> Prop) .
      (forall (p : Bin) . P (Negative p)) ->
      P Zero ->
      (forall (p : Bin) . P (Positive p)) ->
      (forall (x : SignedBin) . P x)
  := fun (P : SignedBin -> Prop)
       (negative : forall (p : Bin) . P (Negative p))
       (zero : P Zero)
       (positive : forall (p : Bin) . P (Positive p))
       (x : SignedBin) .
       match x with
       | Negative p => negative p
       | Zero       => zero
       | Positive p => positive p
       end.

(* Short spellings for this module only: [Local] keeps them out of every file
 * that imports this one. [+ p] and [- p] are prefixes, distinct from the
 * infix [+] declared below.
 *)
Local Notation "0"   := Zero (only parsing).
Local Notation "+ p" := (Positive p) (at level 35, right associativity, only parsing).
Local Notation "- p" := (Negative p) (at level 35, right associativity, only parsing).

(* [SignedBin -> SignedBin] *)
Definition negate := fun (x : SignedBin) .
  match x with
  | - p => + p
  | 0   => 0
  | + p => - p
  end.

(* [SignedBin -> Bin0] *)
Definition abs := fun (x : SignedBin) .
  match x with
  | - p => Bin0.Positive p
  | 0   => Bin0.Zero
  | + p => Bin0.Positive p
  end.

(* The positive part, zero below it; [add] is written from it. *)
(* [SignedBin -> Bin0] *)
Definition ramp := fun (x : SignedBin) .
  match x with
  | - _ => Bin0.Zero
  | 0   => Bin0.Zero
  | + p => Bin0.Positive p
  end.

(* [Bin -> SignedBin] *)
Definition from_b := fun (p : Bin) . (+ p).

(* [Bin0 -> SignedBin] *)
Definition from_b0 := fun (n : Bin0) .
  match n return SignedBin with
  | Bin0.Zero       => 0
  | Bin0.Positive p => + p
  end.

(* The conversions down: [None] below zero for [Bin0], and at or below
 * it for [Bin], which has no zero to answer with.
 *)
(* [SignedBin -> Option Bin0] *)
Definition to_b0 := fun (x : SignedBin) .
  match x with
  | - _ => None
  | 0   => Some Bin0.Zero
  | + p => Some (Bin0.Positive p)
  end.

(* [SignedBin -> Option Bin] *)
Definition to_b := fun (x : SignedBin) .
  match x with
  | - _ => None
  | 0   => None
  | + p => Some p
  end.

(* The bridge to the unary signed type, used to state the laws: [Bin.to_nat]
 * is unary, so this is for proofs, not for computing.
 *)
(* [SignedBin -> Integer] *)
Definition to_integer := fun (x : SignedBin) .
  match x with
  | - p => Integer.Negative (Bin.to_nat p)
  | 0   => Integer.Zero
  | + p => Integer.Positive (Bin.to_nat p)
  end.

(* [Bin.diff p q] forgets the magnitude when [p] is the smaller of the two,
 * reporting a bare [Lt], so the size of a negative answer has to be fetched
 * from the other direction. Both directions are taken and whichever reports
 * [Gt] carries the magnitude; equal arguments report [Eq] both ways and fall
 * through to zero. Total, with no unreachable branch, at the price of walking
 * the bits twice.
 *)
(* [Bin -> Bin -> SignedBin] *)
Definition b_difference := fun (p : Bin) (q : Bin) .
  match Bin.diff p q, Bin.diff q p with
  | Bin.Gt d, _ => + d
  | _, Bin.Gt d => - d
  | _, _            => 0
  end.

(* [Bin0 -> Bin0 -> SignedBin] *)
Definition b0_difference := fun (a : Bin0) (b : Bin0) .
  match a, b with
  | Bin0.Zero, Bin0.Zero             => 0
  | Bin0.Zero, Bin0.Positive q       => - q
  | Bin0.Positive p, Bin0.Zero       => + p
  | Bin0.Positive p, Bin0.Positive q => b_difference p q
  end.

(* Every value is [ramp x] less [ramp (negate x)], one of which is always
 * zero, so a sum is a single difference of two nonnegative numbers instead of
 * nine sign cases. [Integer.add] is written the same way over [Nat0].
 *)
(* [SignedBin -> SignedBin -> SignedBin] *)
Definition add := fun (x : SignedBin) (y : SignedBin) .
  b0_difference (ramp x + ramp y)%b0
                           (ramp (negate x) + ramp (negate y))%b0.

(* The prefix [+ p] above is a separate notation and coexists with this one. *)
Notation "x + y" := (add x y) (only parsing)
  : jw_signed_bin_scope.

Local Open Scope jw_signed_bin_scope.

(* [SignedBin -> SignedBin -> SignedBin] *)
Definition sub := fun (x : SignedBin) (y : SignedBin) . x + negate y.

(* The infix coexists with the prefix [- p] above and with the scope's [- x]
 * of negative literals, as [x + y] does with [+ p].
 *)
Notation "x - y" := (sub x y) (only parsing)
  : jw_signed_bin_scope.

(* The magnitudes multiply in [Bin], and the sign is positive exactly when the
 * two signs agree.
 *)
(* [SignedBin -> SignedBin -> SignedBin] *)
Definition mul := fun (x : SignedBin) (y : SignedBin) .
  match x with
  | - p =>
      match y with
      | - q => + (p * q)%b
      | 0   => 0
      | + q => - (p * q)%b
      end
  | 0 => 0
  | + p =>
      match y with
      | - q => - (p * q)%b
      | 0   => 0
      | + q => + (p * q)%b
      end
  end.

Notation "x * y" := (mul x y) (only parsing)
  : jw_signed_bin_scope.

(* The divisor is a [Bin], so it is never zero: the magnitude is divided and
 * the sign carried over, so the quotient rounds toward zero.
 *)
(* [SignedBin -> Bin -> SignedBin] *)
Definition divide := fun (x : SignedBin) (d : Bin) .
  match x with
  | - p => negate (from_b0 (p /. d)%b0)
  | 0   => 0
  | + p => from_b0 (p /. d)%b0
  end.

Notation "x /. y" := (divide x y) (only parsing)
  : jw_signed_bin_scope.

(* The witness is a [Bin], so it is never zero and [<] is strict.
 *)
(* [SignedBin -> SignedBin -> Prop] *)
Definition LessThan := fun (x : SignedBin) (y : SignedBin) .
  forsome (k : Bin) . x + (+ k) = y.

Notation "x < y" := (LessThan x y) (only parsing)
  : jw_signed_bin_scope.

(* [SignedBin -> SignedBin -> Prop] *)
Definition LessOrEqual := fun (x : SignedBin) (y : SignedBin) . x = y \/ x < y.

Notation "x <= y" := (LessOrEqual x y) (only parsing)
  : jw_signed_bin_scope.

(* The reversed spellings name no new relation: [x > y] is [y < x] with the
 * arguments the other way round, so no law is stated for them.
 *)
Notation "x > y" := (LessThan y x) (only parsing)
  : jw_signed_bin_scope.
Notation "x >= y" := (LessOrEqual y x) (only parsing)
  : jw_signed_bin_scope.

Notation "'(<)'" := LessThan (only parsing)
  : jw_signed_bin_scope.
Notation "'(<=)'" := LessOrEqual (only parsing)
  : jw_signed_bin_scope.

(* Between two negatives the order reverses, the larger magnitude being the
 * smaller number, so those two arguments reach [Bin.compare] the other way
 * round.
 *)
(* [SignedBin -> SignedBin -> Comparison] *)
Definition compare := fun (x : SignedBin) (y : SignedBin) .
  match x with
  | - p =>
      match y with
      | - q => Bin.compare q p
      | 0   => Comparison.Lt
      | + _ => Comparison.Lt
      end
  | 0 =>
      match y with
      | - _ => Comparison.Gt
      | 0   => Comparison.Eq
      | + _ => Comparison.Lt
      end
  | + p =>
      match y with
      | - _ => Comparison.Gt
      | 0   => Comparison.Gt
      | + q => Bin.compare p q
      end
  end.

(* [SignedBin -> SignedBin -> Bool] *)
Abbreviation eq := (Comparable.eq compare).

(* [SignedBin -> SignedBin -> Bool] *)
Abbreviation le := (Comparable.le compare).

(* [SignedBin -> SignedBin -> Bool] *)
Abbreviation lt := (Comparable.lt compare).

(* [SignedBin -> SignedBin -> Bool] *)
Abbreviation ge := (Comparable.ge compare).

(* [SignedBin -> SignedBin -> Bool] *)
Abbreviation gt := (Comparable.gt compare).

(* [SignedBin -> SignedBin -> SignedBin] *)
Abbreviation min := (Comparable.min compare).

(* [SignedBin -> SignedBin -> SignedBin] *)
Abbreviation max := (Comparable.max compare).

(* [Bin0] reads the magnitude, the sign is applied after. [- 0] reads as
 * zero, this type having one zero and [negate] sending it to itself.
 * Hexadecimal is refused there too, so a literal carries only [0] and [1].
 *)
(* [Numeral.Signed -> Option SignedBin] *)
Definition from_numeral := fun (s : Numeral.Signed) .
  match s with
  | Numeral.Signed.Decimal (Numeral.Decimal.Signed.Positive d) =>
      Option.map from_b0 (Bin0.from_digits Bin0.Zero d)
  | Numeral.Signed.Decimal (Numeral.Decimal.Signed.Negative d) =>
      Option.map (fun (n : Bin0) . negate (from_b0 n))
        (Bin0.from_digits Bin0.Zero d)
  | Numeral.Signed.Hexadecimal _ => None
  end.

(* Zero prints as [0], not [-0]: [Numeral.Decimal.Signed] has only the two
 * signs, so one of them carries zero.
 *)
(* [SignedBin -> Numeral.Signed] *)
Definition to_numeral := fun (x : SignedBin) .
  match x with
  | - p =>
      Numeral.Signed.Decimal
        (Numeral.Decimal.Signed.Negative
          (Bin.to_digits p Numeral.Decimal.Digits.End))
  | 0 =>
      Numeral.Signed.Decimal
        (Numeral.Decimal.Signed.Positive
          (Numeral.Decimal.Digits.Zero Numeral.Decimal.Digits.End))
  | + p =>
      Numeral.Signed.Decimal
        (Numeral.Decimal.Signed.Positive
          (Bin.to_digits p Numeral.Decimal.Digits.End))
  end.

(* The laws state this type against [Integer] through [to_integer]. The signed
 * laws are proved there, so agreement carries them.
 *)
Module conversion. (* conversion *)

(* conversion.injectivity *)
Theorem injectivity
  : forall {x : SignedBin} {y : SignedBin} .
      to_integer x = to_integer y -> x = y.
Proof.
  intros x y e.
  match &x with | p | | p end.
  -
    match &y with | q | | q end.
    +
      simpl to_integer in &e.
      leibniz (Bin.conversion.injectivity
                 (Integer.magnitude.negative.injectivity &e)) in |- *.
      quod idem est.
    +
      simpl to_integer in &e.
      ex &e quodlibet.
    +
      simpl to_integer in &e.
      ex &e quodlibet.
  -
    match &y with | q | | q end.
    +
      simpl to_integer in &e.
      ex &e quodlibet.
    +
      quod idem est.
    +
      simpl to_integer in &e.
      ex &e quodlibet.
  -
    match &y with | q | | q end.
    +
      simpl to_integer in &e.
      ex &e quodlibet.
    +
      simpl to_integer in &e.
      ex &e quodlibet.
    +
      simpl to_integer in &e.
      leibniz (Bin.conversion.injectivity
                 (Integer.magnitude.positive.injectivity &e)) in |- *.
      quod idem est.
Qed.

(* conversion.comparison *)
Theorem comparison
  : forall (x : SignedBin) (y : SignedBin) .
      compare x y = Integer.compare (to_integer x) (to_integer y).
Proof.
  intros x y.
  match &x with | p | | p end.
  -
    match &y with | q | | q end.
    + ipso (Bin.conversion.comparison &q &p).
    + simpl in |- *.
      quod idem est.
    + simpl in |- *.
      quod idem est.
  -
    match &y with | q | | q end.
    + simpl in |- *.
      quod idem est.
    + simpl in |- *.
      quod idem est.
    + simpl in |- *.
      quod idem est.
  -
    match &y with | q | | q end.
    + simpl in |- *.
      quod idem est.
    + simpl in |- *.
      quod idem est.
    + ipso (Bin.conversion.comparison &p &q).
Qed.

(* Of the nine pairs of [Bin.diff] outcomes, a [Gt] in the first answers alone.
 * Four of the remaining six cannot arise: [Lt] facing [Lt] or [Eq] either way
 * contradicts the order on [Nat], and [Eq] facing [Gt] would need
 * [to_nat p + to_nat d] to equal [to_nat p], which no [Bin] permits.
 *)
(* conversion.difference *)
Theorem difference
  : forall (p : Bin) (q : Bin) .
      to_integer (b_difference p q)
    = Integer.nat_difference (Bin.to_nat p) (Bin.to_nat q).
Proof.
  intros p q.
  simpl b_difference in |- *.
  let proof forward := Bin.conversion.difference &p &q.
  let proof backward := Bin.conversion.difference &q &p.
  extros &forward &backward.
  match (Bin.diff &p &q) with | | | d end.
  -
    intro forward.
    match (Bin.diff &q &p) with | | | d end.
    +
      intro backward.
      ex (Nat.order.strict.irreflexivity (Bin.to_nat &p)
            (Nat.order.strict.transitivity &forward &backward)) quodlibet.
    +
      intro backward.
      leibniz &backward in &forward.
      ex (Nat.order.strict.irreflexivity (Bin.to_nat &p) &forward) quodlibet.
    +
      intro backward.
      symm in |- *.
      ipso (modus aequans
              (Integer.difference.nat.negative.specification
                 (Bin.to_nat &p) (Bin.to_nat &q) (Bin.to_nat &d)), &backward).
  -
    intro forward.
    match (Bin.diff &q &p) with | | | d end.
    +
      intro backward.
      leibniz &forward in &backward.
      ex (Nat.order.strict.irreflexivity (Bin.to_nat &q) &backward) quodlibet.
    +
      intro backward.
      symm in |- *.
      ipso (modus aequans
              (Integer.difference.nat.zero.specification
                 (Bin.to_nat &p) (Bin.to_nat &q)), &forward).
    +
      intro backward.
      leibniz <- &forward in &backward.
      let proof below := Nat.addition.order.extensivity (Bin.to_nat &p) (Bin.to_nat &d).
      leibniz &backward in &below.
      ex (Nat.order.strict.irreflexivity (Bin.to_nat &p) &below) quodlibet.
  -
    intros forward backward.
    symm in |- *.
    ipso (modus aequans
            (Integer.difference.nat.positive.specification
               (Bin.to_nat &p) (Bin.to_nat &q) (Bin.to_nat &d)), &forward).
Qed.

(* conversion.negation *)
Theorem negation
  : forall (x : SignedBin) .
      to_integer (negate x) = Integer.negate (to_integer x).
Proof.
  intro x.
  match &x with | p | | p end.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    quod idem est.
Qed.

Module difference. (* conversion.difference *)

(* [difference] with the zero cases added. *)
(* conversion.difference.extension *)
Theorem extension
  : forall (a : Bin0) (b : Bin0) .
      to_integer (b0_difference a b)
    = Integer.nat0_difference
        (Bin0.to_nat0 a) (Bin0.to_nat0 b).
Proof.
  intros a b.
  match &a with | | p end.
  - match &b with | | q end.
    + simpl in |- *.
      quod idem est.
    + simpl in |- *.
      quod idem est.
  - match &b with | | q end.
    + simpl in |- *.
      quod idem est.
    + ipso (conversion.difference &p &q).
Qed.

End difference. (* conversion.difference *)

(* conversion.addition *)
Theorem addition
  : forall (x : SignedBin) (y : SignedBin) .
      to_integer (x + y) = Integer.add (to_integer x) (to_integer y).
Proof.
  intros x y.
  (* [Integer.add]'s body is an application, not a match, so Rocq's [simpl]
   * leaves it folded.
   *)
  simpl add, Integer.add in |- *.
  match &x with | p | | p end.
  -
    match &y with | q | | q end.
    +
      simpl in |- *.
      leibniz (Bin.conversion.addition &p &q) in |- *.
      quod idem est.
    +
      simpl in |- *.
      quod idem est.
    +
      ipso (conversion.difference &q &p).
  -
    match &y with | q | | q end.
    + simpl in |- *.
      quod idem est.
    + simpl in |- *.
      quod idem est.
    + simpl in |- *.
      quod idem est.
  -
    match &y with | q | | q end.
    +
      ipso (conversion.difference &p &q).
    +
      simpl in |- *.
      quod idem est.
    +
      simpl in |- *.
      leibniz (Bin.conversion.addition &p &q) in |- *.
      quod idem est.
Qed.

(* conversion.order *)
Theorem order
  : forall (x : SignedBin) (y : SignedBin) .
      x < y <-> (to_integer x < to_integer y)%z.
Proof.
  intros x y.
  divide et impera.
  -
    intro h.
    simpl LessThan in &h.
    match &h with | k e end.
    simpl Integer.LessThan in |- *.
    exists (Bin.to_nat &k).
    leibniz <- &e in |- *.
    leibniz (conversion.addition &x (Positive &k)) in |- *.
    simpl to_integer in |- *.
    quod idem est.
  -
    intro h.
    simpl Integer.LessThan in &h.
    match &h with | j e end.
    simpl LessThan in |- *.
    exists (Bin.from_nat &j).
    lemma f : to_integer (&x + (+ Bin.from_nat &j)) = to_integer &y.
    {
      leibniz (conversion.addition &x (Positive (Bin.from_nat &j))) in |- *.
      simpl to_integer in |- *.
      leibniz (Bin.conversion.retraction &j) in |- *.
      ipso &e.
    }
    ipso (conversion.injectivity &f).
Qed.

(* conversion.multiplication *)
Theorem multiplication
  : forall (x : SignedBin) (y : SignedBin) .
      to_integer (x * y) = Integer.mul (to_integer x) (to_integer y).
Proof.
  intros x y.
  match &x with | p | | p end; match &y with | q | | q end; simpl in |- *.
  -
    leibniz (Bin.conversion.multiplication &p &q) in |- *.
    quod idem est.
  -
    quod idem est.
  -
    leibniz (Bin.conversion.multiplication &p &q) in |- *.
    quod idem est.
  -
    quod idem est.
  -
    quod idem est.
  -
    quod idem est.
  -
    leibniz (Bin.conversion.multiplication &p &q) in |- *.
    quod idem est.
  -
    quod idem est.
  -
    leibniz (Bin.conversion.multiplication &p &q) in |- *.
    quod idem est.
Qed.

(* conversion.division *)
Theorem division
  : forall (x : SignedBin) (d : Bin) .
      to_integer (x /. d) = (to_integer x /. Bin.to_nat d)%z.
Proof.
  intros x d.
  lemma embedding
    : forall (n : Bin0) .
        to_integer (from_b0 n)
        = Integer.from_nat0 (Bin0.to_nat0 n).
  {
    intro n.
    match n with | | q end.
    -
      simpl in |- *.
      quod idem est.
    -
      simpl in |- *.
      quod idem est.
  }
  match &x with | p | | p end.
  -
    let proof c
      : Bin0.to_nat0 (p /. &d)%b0
        = (Bin.to_nat &p /. Bin.to_nat &d)%n0
      := Bin0.conversion.division p &d.
    simpl divide in |- *.
    simpl to_integer at 2 in |- *.
    simpl Integer.divide in |- *.
    leibniz (conversion.negation (from_b0 (p /. &d)%b0)),
      (&embedding (p /. &d)%b0), &c in |- *.
    quod idem est.
  -
    simpl in |- *.
    quod idem est.
  -
    let proof c
      : Bin0.to_nat0 (p /. &d)%b0
        = (Bin.to_nat &p /. Bin.to_nat &d)%n0
      := Bin0.conversion.division p &d.
    simpl divide in |- *.
    simpl to_integer at 2 in |- *.
    simpl Integer.divide in |- *.
    leibniz (&embedding (p /. &d)%b0), &c in |- *.
    quod idem est.
Qed.

(* conversion.ramp *)
Theorem ramp
  : forall (x : SignedBin) . Bin0.to_nat0 (ramp x) = Integer.ramp (to_integer x).
Proof.
  intros x.
  match &x with | Negative p | Zero | Positive p end; simpl in |- *; quod idem est.
Qed.

End conversion. (* conversion *)

(* The laws of [b0_difference], read through [to_integer] as those
 * of [Integer.nat0_difference].
 *)
Module difference. (* difference *)

(* Two differences agree when their sides balance crosswise. *)
(* difference.invariance *)
Theorem invariance
  : forall {a : Bin0} {b : Bin0} {c : Bin0} {d : Bin0} .
      (a + d = c + b)%b0 ->
      b0_difference a b = b0_difference c d.
Proof.
  intros a b c d e.
  let proof f := congru Bin0.to_nat0, &e.
  leibniz
    (Bin0.conversion.addition &a &d),
    (Bin0.conversion.addition &c &b)
    in &f.
  lemma facto
    : to_integer (b0_difference &a &b) = to_integer (b0_difference &c &d).
  {
    leibniz
      (conversion.difference.extension &a &b),
      (conversion.difference.extension &c &d)
      in |- *.
    ipso (Integer.difference.nat0.well_definedness &f).
  }
  ipso (conversion.injectivity &facto).
Qed.

(* difference.additivity *)
Theorem additivity
  : forall (a : Bin0) (b : Bin0) (c : Bin0) (d : Bin0) .
      b0_difference a b + b0_difference c d
      = b0_difference (a + c)%b0 (b + d)%b0.
Proof.
  intros a b c d.
  lemma facto
    : to_integer (b0_difference &a &b + b0_difference &c &d)
      = to_integer
          (b0_difference (&a + &c)%b0 (&b + &d)%b0).
  {
    leibniz
      (conversion.addition (b0_difference &a &b) (b0_difference &c &d)),
      (conversion.difference.extension &a &b),
      (conversion.difference.extension &c &d),
      (conversion.difference.extension (&a + &c)%b0 (&b + &d)%b0),
      (Bin0.conversion.addition &a &c),
      (Bin0.conversion.addition &b &d)
      in |- *.
    ipso
      (Integer.difference.nat0.additivity
        (Bin0.to_nat0 &a) (Bin0.to_nat0 &b)
        (Bin0.to_nat0 &c) (Bin0.to_nat0 &d)).
  }
  ipso (conversion.injectivity &facto).
Qed.

(* The difference's positive part with [b] is its negative part with [a]. *)
(* difference.specification *)
Theorem specification
  : forall (a : Bin0) (b : Bin0) .
      (ramp (b0_difference a b) + b
        = ramp (negate (b0_difference a b)) + a)%b0.
Proof.
  intros a b.
  lemma facto
    : Bin0.to_nat0 (ramp (b0_difference &a &b) + &b)%b0
      = Bin0.to_nat0
          (ramp (negate (b0_difference &a &b)) + &a)%b0.
  {
    leibniz
      (Bin0.conversion.addition (ramp (b0_difference &a &b)) &b),
      (Bin0.conversion.addition (ramp (negate (b0_difference &a &b))) &a),
      (conversion.ramp (b0_difference &a &b)),
      (conversion.ramp (negate (b0_difference &a &b))),
      (conversion.negation (b0_difference &a &b)),
      (conversion.difference.extension &a &b)
      in |- *.
    ipso
      (Integer.difference.nat0.specification (Bin0.to_nat0 &a) (Bin0.to_nat0 &b)).
  }
  ipso (Bin0.conversion.injectivity &facto).
Qed.

(* difference.identity *)
Theorem identity : forall (a : Bin0) . b0_difference a 0%b0 = from_b0 a.
Proof.
  intro a.
  match &a with | | p end; simpl in |- *; quod idem est.
Qed.

(* difference.negation *)
Theorem negation : forall (b : Bin0) . b0_difference 0%b0 b = negate (from_b0 b).
Proof.
  intro b.
  match &b with | | q end; simpl in |- *; quod idem est.
Qed.

End difference. (* difference *)

Module narrowing. (* narrowing *)

Module bin0. (* narrowing.bin0 *)

(* narrowing.bin0.retraction *)
Theorem retraction : forall (n : Bin0) . to_b0 (from_b0 n) = Some n.
Proof.
  intro n.
  match &n with | | p end; simpl in |- *; quod idem est.
Qed.

(* narrowing.bin0.specification *)
Theorem specification : forall (x : SignedBin) (n : Bin0) . to_b0 x = Some n <-> x = from_b0 n.
Proof.
  intros x n.
  divide et impera.
  - intro e.
    match &x with | p | | p end.
    + simpl in &e.
      ex &e quodlibet.
    + simpl in &e.
      leibniz <- (Option.some.injectivity &e) in |- *.
      simpl in |- *.
      quod idem est.
    + simpl in &e.
      leibniz <- (Option.some.injectivity &e) in |- *.
      simpl in |- *.
      quod idem est.
  - intro e.
    leibniz &e in |- *.
    ipso (narrowing.bin0.retraction &n).
Qed.

End bin0. (* narrowing.bin0 *)

End narrowing. (* narrowing *)

Module magnitude. (* magnitude *)

Module negative. (* magnitude.negative *)

(* magnitude.negative.injectivity *)
Lemma injectivity
  : forall {p : Bin} {q : Bin} . (- p) = - q -> p = q.
Proof.
  intros p q e.
  congru (fun (x : SignedBin) . match x with | - r => r | 0 => p | + _ => p end), e |- e'.
  simpl in e'.
  ipso e'.
Qed.

End negative. (* magnitude.negative *)

Module positive. (* magnitude.positive *)

(* magnitude.positive.injectivity *)
Lemma injectivity
  : forall {p : Bin} {q : Bin} . (+ p) = + q -> p = q.
Proof.
  intros p q e.
  congru (fun (x : SignedBin) . match x with | - _ => p | 0 => p | + r => r end), e |- e'.
  simpl in e'.
  ipso e'.
Qed.

End positive. (* magnitude.positive *)

(* magnitude.injectivity *)
Theorem injectivity
  : forall (p : Bin) (q : Bin) .
      ((- p) = - q -> p = q) /\ ((+ p) = + q -> p = q).
Proof.
  intros p q.
  divide et impera.
  - ipso (@magnitude.negative.injectivity p q).
  - ipso (@magnitude.positive.injectivity p q).
Qed.

End magnitude. (* magnitude *)

Module embedding. (* embedding *)

(* embedding.injectivity *)
Theorem injectivity
  : forall {m : Bin0} {n : Bin0} .
      from_b0 m = from_b0 n -> m = n.
Proof.
  intros m n e.
  match &m with | | p end; match &n with | | q end.
  - quod idem est.
  - simpl in &e.
    ex &e quodlibet.
  - simpl in &e.
    ex &e quodlibet.
  - simpl in &e.
    let proof e' := magnitude.positive.injectivity &e.
    leibniz &e' in |- *.
    quod idem est.
Qed.

End embedding. (* embedding *)

Module negation. (* negation *)

(* negation.involution *)
Theorem involution : forall (x : SignedBin) . negate (negate x) = x.
Proof.
  intro x.
  match &x with | p | | p end.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    quod idem est.
Qed.

(* negation.additivity *)
Theorem additivity
  : forall (x : SignedBin) (y : SignedBin) .
      negate (x + y) = negate x + negate y.
Proof.
  intros x y.
  lemma f : to_integer (negate (&x + &y)) = to_integer (negate &x + negate &y).
  {
    leibniz (conversion.negation (&x + &y)), (conversion.addition &x &y),
            (conversion.addition (negate &x) (negate &y)),
            (conversion.negation &x), (conversion.negation &y) in |- *.
    ipso (Integer.negation.additivity (to_integer &x) (to_integer &y)).
  }
  ipso (conversion.injectivity &f).
Qed.

End negation. (* negation *)

Module addition. (* addition *)

(* addition.associativity *)
Theorem associativity
  : forall (x : SignedBin) (y : SignedBin) (z : SignedBin) .
      (x + y) + z = x + (y + z).
Proof.
  intros x y z.
  lemma f : to_integer ((&x + &y) + &z) = to_integer (&x + (&y + &z)).
  {
    leibniz (conversion.addition (&x + &y) &z), (conversion.addition &x &y),
            (conversion.addition &x (&y + &z)), (conversion.addition &y &z) in |- *.
    ipso (Integer.addition.associativity
            (to_integer &x) (to_integer &y) (to_integer &z)).
  }
  ipso (conversion.injectivity &f).
Qed.

(* addition.commutativity *)
Theorem commutativity
  : forall (x : SignedBin) (y : SignedBin) . x + y = y + x.
Proof.
  intros x y.
  lemma f : to_integer (&x + &y) = to_integer (&y + &x).
  {
    leibniz (conversion.addition &x &y), (conversion.addition &y &x) in |- *.
    ipso (Integer.addition.commutativity (to_integer &x) (to_integer &y)).
  }
  ipso (conversion.injectivity &f).
Qed.

Module left. (* addition.left *)

(* addition.left.identity *)
Theorem identity : forall (x : SignedBin) . 0 + x = x.
Proof.
  intro x.
  lemma f : to_integer (0 + &x) = to_integer &x.
  {
    leibniz (conversion.addition 0 &x) in |- *.
    ipso (Integer.addition.left.identity (to_integer &x)).
  }
  ipso (conversion.injectivity &f).
Qed.

(* addition.left.inverse *)
Theorem inverse : forall (x : SignedBin) . negate x + x = 0.
Proof.
  intro x.
  lemma f : to_integer (negate &x + &x) = to_integer 0.
  {
    leibniz (conversion.addition (negate &x) &x), (conversion.negation &x) in |- *.
    ipso (Integer.addition.left.inverse (to_integer &x)).
  }
  ipso (conversion.injectivity &f).
Qed.

(* addition.left.cancellation *)
Theorem cancellation
  : forall {x : SignedBin} {y : SignedBin} {z : SignedBin} .
      x + y = x + z -> y = z.
Proof.
  intros x y z e.
  let proof f := congru to_integer, &e.
  leibniz (conversion.addition &x &y), (conversion.addition &x &z) in &f.
  ipso (conversion.injectivity
          (@Integer.addition.left.cancellation
             (to_integer &x) (to_integer &y) (to_integer &z) &f)).
Qed.

End left. (* addition.left *)

Module right. (* addition.right *)

(* addition.right.identity *)
Theorem identity : forall (x : SignedBin) . x + 0 = x.
Proof.
  intro x.
  lemma f : to_integer (&x + 0) = to_integer &x.
  {
    leibniz (conversion.addition &x 0) in |- *.
    ipso (Integer.addition.right.identity (to_integer &x)).
  }
  ipso (conversion.injectivity &f).
Qed.

(* addition.right.inverse *)
Theorem inverse : forall (x : SignedBin) . x + negate x = 0.
Proof.
  intro x.
  lemma f : to_integer (&x + negate &x) = to_integer 0.
  {
    leibniz (conversion.addition &x (negate &x)), (conversion.negation &x) in |- *.
    ipso (Integer.addition.right.inverse (to_integer &x)).
  }
  ipso (conversion.injectivity &f).
Qed.

(* addition.right.cancellation *)
Theorem cancellation
  : forall {x : SignedBin} {y : SignedBin} {z : SignedBin} .
      x + y = z + y -> x = z.
Proof.
  intros x y z e.
  let proof f := congru to_integer, &e.
  leibniz (conversion.addition &x &y), (conversion.addition &z &y) in &f.
  ipso (conversion.injectivity
          (@Integer.addition.right.cancellation
             (to_integer &x) (to_integer &z) (to_integer &y) &f)).
Qed.

End right. (* addition.right *)

(* addition.identity *)
Theorem identity
  : forall (x : SignedBin) . (0 + x = x) /\ (x + 0 = x).
Proof.
  intro x.
  divide et impera.
  - ipso (addition.left.identity  &x).
  - ipso (addition.right.identity &x).
Qed.

(* addition.inverse *)
Theorem inverse
  : forall (x : SignedBin) . (negate x + x = 0) /\ (x + negate x = 0).
Proof.
  intro x.
  divide et impera.
  - ipso (addition.left.inverse  &x).
  - ipso (addition.right.inverse &x).
Qed.

(* addition.cancellation *)
Theorem cancellation
  : forall (x : SignedBin) (y : SignedBin) (z : SignedBin) .
      (x + y = x + z -> y = z) /\ (x + y = z + y -> x = z).
Proof.
  intros x y z.
  divide et impera.
  - ipso (@addition.left.cancellation  &x &y &z).
  - ipso (@addition.right.cancellation &x &y &z).
Qed.

Module inversion. (* addition.inversion *)

(* addition.inversion.subtraction *)
Theorem subtraction
  : forall (x : SignedBin) (y : SignedBin) . (x - y) + y = x.
Proof.
  intros x y.
  let proof s : &x - &y = &x + negate &y := refl _.
  leibniz &s in |- *.
  leibniz (addition.associativity &x (negate &y) &y) in |- *.
  leibniz (addition.left.inverse &y) in |- *.
  ipso (addition.right.identity &x).
Qed.

End inversion. (* addition.inversion *)

Module order. (* addition.order *)

Module strict. (* addition.order.strict *)

(* addition.order.strict.monotonicity *)
Theorem monotonicity : forall (x : SignedBin) (y : SignedBin) (z : SignedBin) . y < z -> x + y < x + z.
Proof.
  intros x y z h.
  let proof g := modus aequans (conversion.order &y &z), &h.
  let proof s :=
    Integer.addition.order.strict.monotonicity (to_integer &x) (to_integer &y) (to_integer &z) &g.
  leibniz <- (conversion.addition &x &y), <- (conversion.addition &x &z) in &s.
  ipso (modus aequans (conversion.order (&x + &y) (&x + &z)), &s).
Qed.

(* Adding [negate x] to both sides takes [x] away again. *)
(* addition.order.strict.cancellation *)
Theorem cancellation : forall (x : SignedBin) (y : SignedBin) (z : SignedBin) . x + y < x + z -> y < z.
Proof.
  intros x y z h.
  let proof s := addition.order.strict.monotonicity (negate &x) (&x + &y) (&x + &z) &h.
  leibniz
    <- (addition.associativity (negate &x) &x &y),
    <- (addition.associativity (negate &x) &x &z),
    (addition.left.inverse &x),
    (addition.left.identity &y),
    (addition.left.identity &z)
    in &s.
  ipso &s.
Qed.

End strict. (* addition.order.strict *)

(* addition.order.monotonicity *)
Theorem monotonicity : forall (x : SignedBin) (y : SignedBin) (z : SignedBin) . y <= z -> x + y <= x + z.
Proof.
  intros x y z h.
  match &h with | e | smaller end.
  - leibniz &e in |- *.
    ipso (disjoin (refl (&x + &z)), _).
  - ipso (disjoin _, (addition.order.strict.monotonicity &x &y &z &smaller)).
Qed.

Module mixed. (* addition.order.mixed *)

(* [a + b < a + d], and [a + d] is [c + d] or below it. *)
(* addition.order.mixed.monotonicity *)
Theorem monotonicity
  : forall (a : SignedBin) (b : SignedBin) (c : SignedBin) (d : SignedBin) . a <= c -> b < d -> a + b < c + d.
Proof.
  intros a b c d h k.
  let proof first := addition.order.strict.monotonicity &a &b &d &k.
  match &h with | e | smaller end.
  - leibniz <- &e in |- *.
    ipso &first.
  - let proof second := addition.order.strict.monotonicity &d &a &c &smaller.
    leibniz (addition.commutativity &d &a), (addition.commutativity &d &c) in &second.
    ipso (modus aequans (conversion.order (&a + &b) (&c + &d)),
          (Integer.order.strict.transitivity
             (modus aequans (conversion.order (&a + &b) (&a + &d)), &first)
             (modus aequans (conversion.order (&a + &d) (&c + &d)), &second))).
Qed.

End mixed. (* addition.order.mixed *)

(* Equal right summands leave the left ones' order; a smaller right one makes
 * the sum smaller by [addition.order.mixed.monotonicity].
 *)
(* addition.order.accumulation *)
Theorem accumulation
  : forall (a : SignedBin) (b : SignedBin) (c : SignedBin) (d : SignedBin) . a <= c -> b <= d -> a + b <= c + d.
Proof.
  intros a b c d h k.
  match &k with | e | smaller end.
  - leibniz &e in |- *.
    let proof s := addition.order.monotonicity &d &a &c &h.
    leibniz (addition.commutativity &d &a), (addition.commutativity &d &c) in &s.
    ipso &s.
  - ipso (disjoin _, (addition.order.mixed.monotonicity &a &b &c &d &h &smaller)).
Qed.

End order. (* addition.order *)

End addition. (* addition *)

Module subtraction. (* subtraction *)

(* subtraction.specification *)
Theorem specification
  : forall (x : SignedBin) (y : SignedBin) . x - y = x + negate y.
Proof.
  intros x y.
  ipso (refl _).
Qed.

Module inversion. (* subtraction.inversion *)

(* subtraction.inversion.addition *)
Theorem addition
  : forall (x : SignedBin) (y : SignedBin) . (x + y) - y = x.
Proof.
  intros x y.
  leibniz (subtraction.specification (&x + &y) &y) in |- *.
  leibniz (addition.associativity &x &y (negate &y)) in |- *.
  leibniz (addition.right.inverse &y) in |- *.
  ipso (addition.right.identity &x).
Qed.

End inversion. (* subtraction.inversion *)

Module right. (* subtraction.right *)

(* [x - 0] is [x + negate 0]; reading it through [addition.inversion]
 * instead needs no fact about [negate 0].
 *)
(* subtraction.right.identity *)
Theorem identity : forall (x : SignedBin) . x - 0 = x.
Proof.
  intros x.
  leibniz <- (addition.right.identity (&x - 0)) in |- *.
  ipso (addition.inversion.subtraction &x 0).
Qed.

End right. (* subtraction.right *)

(* subtraction.annihilation *)
Theorem annihilation : forall (x : SignedBin) . x - x = 0.
Proof.
  intros x.
  leibniz (subtraction.specification &x &x) in |- *.
  ipso (addition.right.inverse &x).
Qed.

End subtraction. (* subtraction *)

Module order. (* order *)

Module strict. (* order.strict *)

(* order.strict.irreflexivity *)
Theorem irreflexivity : forall (x : SignedBin) . ~ (x < x).
Proof.
  simpl (~ _) in |- *.
  intro x.
  intro h.
  ex (Integer.order.strict.irreflexivity (to_integer &x)
        (modus aequans (conversion.order &x &x), &h)) quodlibet.
Qed.

(* order.strict.transitivity *)
Theorem transitivity
  : forall {x : SignedBin} {y : SignedBin} {z : SignedBin} .
      x < y -> y < z -> x < z.
Proof.
  intros x y z h1 h2.
  ipso (modus aequans (conversion.order &x &z),
        (Integer.order.strict.transitivity
           (modus aequans (conversion.order &x &y), &h1)
           (modus aequans (conversion.order &y &z), &h2))).
Qed.

End strict. (* order.strict *)

Module sign. (* order.sign *)

(* [Negative p] plus [+ p] is 0. *)
(* order.sign.negativity *)
Theorem negativity : forall (p : Bin) . SignedBin.Negative p < 0.
Proof.
  intro p.
  simpl LessThan in |- *.
  exists &p.
  ipso (addition.left.inverse (SignedBin.Positive &p)).
Qed.

(* order.sign.positivity *)
Theorem positivity : forall (p : Bin) . 0 < SignedBin.Positive p.
Proof.
  intro p.
  simpl LessThan in |- *.
  exists &p.
  simpl add in |- *.
  simpl in |- *.
  quod idem est.
Qed.

End sign. (* order.sign *)

Module negation. (* order.negation *)

Module strict. (* order.negation.strict *)

(* Adding [negate x + negate y] to both sides of [x < y] leaves
 * [negate y < negate x].
 *)
(* order.negation.strict.reversal *)
Theorem reversal : forall (x : SignedBin) (y : SignedBin) . x < y <-> negate y < negate x.
Proof.
  intros x y.
  lemma forward : forall (a : SignedBin) (b : SignedBin) . a < b -> negate b < negate a.
  {
    intros a b h.
    let proof s := addition.order.strict.monotonicity (negate &a + negate &b) &a &b &h.
    leibniz
      (addition.associativity (negate &a) (negate &b) &a),
      (addition.associativity (negate &a) (negate &b) &b),
      (addition.commutativity (negate &b) &a),
      <- (addition.associativity (negate &a) &a (negate &b)),
      (addition.left.inverse &a),
      (addition.left.inverse &b),
      (addition.left.identity (negate &b)),
      (addition.right.identity (negate &a))
      in &s.
    ipso &s.
  }
  divide et impera.
  - ipso (&forward &x &y).
  - intro h.
    let proof s := &forward (negate &y) (negate &x) &h.
    leibniz (negation.involution &x), (negation.involution &y) in &s.
    ipso &s.
Qed.

End strict. (* order.negation.strict *)

(* Equal sides stay equal, and a strict order reverses by
 * [order.negation.strict.reversal].
 *)
(* order.negation.reversal *)
Theorem reversal : forall (x : SignedBin) (y : SignedBin) . x <= y -> negate y <= negate x.
Proof.
  intros x y h.
  match &h with | e | smaller end.
  - leibniz &e in |- *.
    ipso (disjoin (refl (negate &y)), _).
  - ipso (disjoin _, (modus aequans (order.negation.strict.reversal &x &y), &smaller)).
Qed.

End negation. (* order.negation *)

Module subtraction. (* order.subtraction *)

Module left. (* order.subtraction.left *)

(* order.subtraction.left.monotonicity *)
Theorem monotonicity : forall (x : SignedBin) (y : SignedBin) (z : SignedBin) . y < z -> y - x < z - x.
Proof.
  intros x y z h.
  leibniz (subtraction.specification &y &x), (subtraction.specification &z &x) in |- *.
  leibniz (addition.commutativity &y (negate &x)), (addition.commutativity &z (negate &x)) in |- *.
  ipso (addition.order.strict.monotonicity (negate &x) &y &z &h).
Qed.

End left. (* order.subtraction.left *)

Module right. (* order.subtraction.right *)

(* order.subtraction.right.antitonicity *)
Theorem antitonicity : forall (x : SignedBin) (y : SignedBin) (z : SignedBin) . y < z -> x - z < x - y.
Proof.
  intros x y z h.
  leibniz (subtraction.specification &x &z), (subtraction.specification &x &y) in |- *.
  ipso (addition.order.strict.monotonicity &x (negate &z) (negate &y)
          (modus aequans (order.negation.strict.reversal &y &z), &h)).
Qed.

End right. (* order.subtraction.right *)

(* order.subtraction.positivity *)
Theorem positivity : forall (x : SignedBin) (y : SignedBin) . x < y <-> 0 < y - x.
Proof.
  intros x y.
  leibniz (subtraction.specification &y &x) in |- *.
  divide et impera.
  - intro h.
    let proof s := addition.order.strict.monotonicity (negate &x) &x &y &h.
    leibniz (addition.left.inverse &x), (addition.commutativity (negate &x) &y) in &s.
    ipso &s.
  - intro h.
    let proof s := addition.order.strict.monotonicity &x 0 (&y + negate &x) &h.
    leibniz
      (addition.right.identity &x),
      (addition.commutativity &y (negate &x)),
      <- (addition.associativity &x (negate &x) &y),
      (addition.right.inverse &x),
      (addition.left.identity &y)
      in &s.
    ipso &s.
Qed.

End subtraction. (* order.subtraction *)

Module increment. (* order.increment *)

(* order.increment.extensivity *)
Theorem extensivity : forall (x : SignedBin) . x < x + (+ Bin.One).
Proof.
  intro x.
  simpl LessThan in |- *.
  exists Bin.One.
  quod idem est.
Qed.

(* A difference [k] is [1] or [1] plus another, read off [Bin.to_nat k];
 * [1] gives [x + 1 = y], [1 + j] gives [(x + 1) + j = y].
 *)
(* order.increment.specification *)
Theorem specification : forall (x : SignedBin) (y : SignedBin) . x < y <-> x + (+ Bin.One) <= y.
Proof.
  intros x y.
  divide et impera.
  - intro h.
    simpl LessThan in &h.
    match &h with | k e end.
    lemma split
      : k = Bin.One \/ forsome (j : Bin) . k = (Bin.One + j)%b.
    {
      match (Bin.to_nat &k) with | One | Successor n end |- t.
      - lemma f : Bin.to_nat k = Bin.to_nat Bin.One.
        {
          ipso &t.
        }
        ipso (disjoin (Bin.conversion.injectivity &f), _).
      - lemma f : Bin.to_nat k = Bin.to_nat (Bin.One + Bin.from_nat n)%b.
        {
          leibniz
            (Bin.conversion.addition Bin.One (Bin.from_nat &n)),
            (Bin.conversion.retraction &n)
            in |- *.
          ipso &t.
        }
        lemma witness : forsome (j : Bin) . k = (Bin.One + j)%b.
        {
          exists (Bin.from_nat &n).
          ipso (Bin.conversion.injectivity &f).
        }
        ipso (disjoin _, &witness).
    }
    match &split with | one | larger end.
    + leibniz &one in &e.
      ipso (disjoin &e, _).
    + match &larger with | j d end.
      leibniz &d in &e.
      lemma facto : (x + (+ Bin.One)) + (+ j) = y.
      {
        leibniz (addition.associativity &x (+ Bin.One) (+ &j)) in |- *.
        ipso &e.
      }
      lemma later : x + (+ Bin.One) < y.
      {
        simpl LessThan in |- *.
        exists &j.
        ipso &facto.
      }
      ipso (disjoin _, &later).
  - intro h.
    match &h with | e | later end.
    + leibniz <- &e in |- *.
      ipso (order.increment.extensivity &x).
    + ipso (order.strict.transitivity (order.increment.extensivity &x) &later).
Qed.

(* order.increment.adjacency *)
Theorem adjacency : forall (x : SignedBin) (y : SignedBin) . ~ (x < y /\ y < x + (+ Bin.One)).
Proof.
  intros x y.
  simpl (~ _) in |- *.
  intro h.
  match &h with | above below end.
  match (modus aequans (order.increment.specification &x &y), &above) with | e | later end.
  - leibniz <- &e in &below.
    ipso (order.strict.irreflexivity (&x + (+ Bin.One)) &below).
  - ipso (order.strict.irreflexivity &y (order.strict.transitivity &below &later)).
Qed.

End increment. (* order.increment *)

Module decrement. (* order.decrement *)

(* order.decrement.extensivity *)
Theorem extensivity : forall (x : SignedBin) . x - (+ Bin.One) < x.
Proof.
  intro x.
  simpl LessThan in |- *.
  exists Bin.One.
  leibniz
    (subtraction.specification &x (+ Bin.One)),
    (addition.associativity &x (negate (+ Bin.One)) (+ Bin.One)),
    (addition.left.inverse (+ Bin.One)),
    (addition.right.identity &x)
    in |- *.
  quod idem est.
Qed.

End decrement. (* order.decrement *)

(* [x < y + 1] is [x + 1 <= y + 1], and [1] cancels from both sides. *)
(* order.discreteness *)
Theorem discreteness : forall (x : SignedBin) (y : SignedBin) . x < y + (+ Bin.One) <-> x <= y.
Proof.
  intros x y.
  divide et impera.
  - intro h.
    match (modus aequans (order.increment.specification &x (&y + (+ Bin.One))), &h)
      with | e | smaller end.
    + ipso (disjoin (addition.right.cancellation &e), _).
    + leibniz
        (addition.commutativity &x (+ Bin.One)),
        (addition.commutativity &y (+ Bin.One))
        in &smaller.
      ipso (disjoin _, (addition.order.strict.cancellation (+ Bin.One) &x &y &smaller)).
  - intro h.
    match &h with | e | smaller end.
    + leibniz &e in |- *.
      ipso (order.increment.extensivity &y).
    + ipso (order.strict.transitivity &smaller (order.increment.extensivity &y)).
Qed.

Module embedding. (* order.embedding *)

(* Both orders are a positive difference added, and [from_b0]
 * carries a sum with a positive [k] to the same sum, case by case.
 *)
(* order.embedding.preservation *)
Theorem preservation
  : forall (m : Bin0) (n : Bin0) .
      (m < n)%b0 <-> from_b0 m < from_b0 n.
Proof.
  intros m n.
  lemma additivity
    : forall (a : Bin0) (k : Bin) .
        from_b0 (a + Bin0.Positive k)%b0
        = from_b0 a + (+ k).
  {
    intros a k.
    match &a with | | p end; simpl add in |- *; simpl in |- *; quod idem est.
  }
  divide et impera.
  - intro h.
    simpl Bin0.LessThan in &h.
    match &h with | k e end.
    simpl LessThan in |- *.
    exists &k.
    leibniz <- (&additivity &m &k), &e in |- *.
    quod idem est.
  - intro h.
    simpl LessThan in &h.
    match &h with | k e end.
    simpl Bin0.LessThan in |- *.
    exists &k.
    leibniz <- (&additivity &m &k) in &e.
    ipso (embedding.injectivity &e).
Qed.

(* order.embedding.nonnegativity *)
Theorem nonnegativity : forall (n : Bin0) . 0 <= from_b0 n.
Proof.
  intro n.
  match &n with | | p end.
  - ipso (disjoin (refl 0), _).
  - lemma facto : 0 < + p.
    {
      simpl LessThan in |- *.
      exists &p.
      simpl add in |- *.
      simpl in |- *.
      quod idem est.
    }
    ipso (disjoin _, &facto).
Qed.

End embedding. (* order.embedding *)

End order. (* order *)

Module multiplication. (* multiplication *)

(* multiplication.commutativity *)
Theorem commutativity
  : forall (x : SignedBin) (y : SignedBin) . x * y = y * x.
Proof.
  intros x y.
  lemma f : to_integer (&x * &y) = to_integer (&y * &x).
  {
    leibniz (conversion.multiplication &x &y), (conversion.multiplication &y &x) in |- *.
    ipso (Integer.multiplication.commutativity (to_integer &x) (to_integer &y)).
  }
  ipso (conversion.injectivity &f).
Qed.

(* multiplication.associativity *)
Theorem associativity
  : forall (x : SignedBin) (y : SignedBin) (z : SignedBin) .
      (x * y) * z = x * (y * z).
Proof.
  intros x y z.
  lemma f : to_integer ((&x * &y) * &z) = to_integer (&x * (&y * &z)).
  {
    leibniz (conversion.multiplication (&x * &y) &z), (conversion.multiplication &x &y),
            (conversion.multiplication &x (&y * &z)), (conversion.multiplication &y &z)
      in |- *.
    ipso (Integer.multiplication.associativity
            (to_integer &x) (to_integer &y) (to_integer &z)).
  }
  ipso (conversion.injectivity &f).
Qed.

(* multiplication.identity *)
Theorem identity
  : forall (x : SignedBin) . ((+ Bin.One) * x = x) /\ (x * (+ Bin.One) = x).
Proof.
  intro x.
  lemma one : to_integer (+ Bin.One) = Nat.One.
  {
    simpl in |- *.
    quod idem est.
  }
  let proof i := Integer.multiplication.identity (to_integer &x).
  match &i with | l r end.
  divide et impera.
  -
    lemma f : to_integer ((+ Bin.One) * &x) = to_integer &x.
    {
      leibniz (conversion.multiplication (+ Bin.One) &x), &one in |- *.
      ipso &l.
    }
    ipso (conversion.injectivity &f).
  -
    lemma f : to_integer (&x * (+ Bin.One)) = to_integer &x.
    {
      leibniz (conversion.multiplication &x (+ Bin.One)), &one in |- *.
      ipso &r.
    }
    ipso (conversion.injectivity &f).
Qed.

(* multiplication.annihilation *)
Theorem annihilation
  : forall (x : SignedBin) . (0 * x = 0) /\ (x * 0 = 0).
Proof.
  intro x.
  divide et impera.
  -
    simpl in |- *.
    quod idem est.
  -
    match &x with | p | | p end; simpl in |- *; quod idem est.
Qed.

Module distributivity. (* multiplication.distributivity *)

Module over. (* multiplication.distributivity.over *)

(* multiplication.distributivity.over.addition *)
Theorem addition
  : forall (x : SignedBin) (y : SignedBin) (z : SignedBin) .
      (x * (y + z) = (x * y) + (x * z)) /\ ((y + z) * x = (y * x) + (z * x)).
Proof.
  intros x y z.
  let proof d := Integer.multiplication.distributivity.over.addition
                   (to_integer &x) (to_integer &y) (to_integer &z).
  match &d with | l r end.
  divide et impera.
  -
    lemma f : to_integer (&x * (&y + &z)) = to_integer ((&x * &y) + (&x * &z)).
    {
      leibniz (conversion.multiplication &x (&y + &z)), (conversion.addition &y &z),
              (conversion.addition (&x * &y) (&x * &z)),
              (conversion.multiplication &x &y), (conversion.multiplication &x &z) in |- *.
      ipso &l.
    }
    ipso (conversion.injectivity &f).
  -
    lemma f : to_integer ((&y + &z) * &x) = to_integer ((&y * &x) + (&z * &x)).
    {
      leibniz (conversion.multiplication (&y + &z) &x), (conversion.addition &y &z),
              (conversion.addition (&y * &x) (&z * &x)),
              (conversion.multiplication &y &x), (conversion.multiplication &z &x) in |- *.
      ipso &r.
    }
    ipso (conversion.injectivity &f).
Qed.

End over. (* multiplication.distributivity.over *)

End distributivity. (* multiplication.distributivity *)

(* multiplication.cancellation *)
Theorem cancellation
  : forall (k : SignedBin) (x : SignedBin) (y : SignedBin) .
      ~ (k = 0) -> k * x = k * y -> x = y.
Proof.
  intros k x y n e.
  lemma m : ~ (to_integer &k = Integer.Zero).
  {
    intro z.
    let proof z : to_integer &k = to_integer 0 := &z.
    ipso (&n (conversion.injectivity &z)).
  }
  let proof f := congru to_integer, &e.
  leibniz (conversion.multiplication &k &x), (conversion.multiplication &k &y) in &f.
  ipso (conversion.injectivity
          (Integer.multiplication.cancellation (to_integer &k) (to_integer &x) (to_integer &y)
             &m &f)).
Qed.

(* multiplication.magnitude *)
Theorem magnitude
  : forall (x : SignedBin) (y : SignedBin) .
      abs (x * y) = (abs x * abs y)%b0.
Proof.
  intros x y.
  match &x with | p | | p end; match &y with | q | | q end; simpl in |- *; quod idem est.
Qed.

Module left. (* multiplication.left *)

(* multiplication.left.negation *)
Theorem negation : forall (x : SignedBin) (y : SignedBin) . negate x * y = negate (x * y).
Proof.
  intros x y.
  lemma facto : to_integer (negate x * y) = to_integer (negate (x * y)).
  {
    leibniz
      (conversion.multiplication (negate &x) &y),
      (conversion.negation &x),
      (conversion.negation (&x * &y)),
      (conversion.multiplication &x &y)
      in |- *.
    ipso (Integer.multiplication.left.negation (to_integer &x) (to_integer &y)).
  }
  ipso (conversion.injectivity &facto).
Qed.

Module order. (* multiplication.left.order *)

Module strict. (* multiplication.left.order.strict *)

(* A positive [k] is [+ q], and [Integer]'s law takes [+ q] as [+ (to_nat q)]. *)
(* multiplication.left.order.strict.monotonicity *)
Theorem monotonicity
  : forall (k : SignedBin) (x : SignedBin) (y : SignedBin) . 0 < k -> x < y -> k * x < k * y.
Proof.
  intros k x y hk h.
  simpl LessThan in &hk.
  match &hk with | q e end.
  lemma positive : k = + q.
  {
    ipso (symm &e).
  }
  leibniz &positive in |- *.
  let proof g := modus aequans (conversion.order &x &y), &h.
  lemma image : (to_integer ((+ q) * x)%b_signed < to_integer ((+ q) * y)%b_signed)%z.
  {
    leibniz (conversion.multiplication (+ &q) &x), (conversion.multiplication (+ &q) &y) in |- *.
    ipso (Integer.multiplication.left.order.strict.monotonicity
            (Bin.to_nat &q) (to_integer &x) (to_integer &y) &g).
  }
  ipso (modus aequans (conversion.order ((+ &q) * &x) ((+ &q) * &y)), &image).
Qed.

(* [negate k] is positive, and [negate k * x] is [negate (k * x)]. *)
(* multiplication.left.order.strict.reversal *)
Theorem reversal
  : forall (k : SignedBin) (x : SignedBin) (y : SignedBin) . k < 0 -> x < y -> k * y < k * x.
Proof.
  intros k x y hk h.
  lemma positive : 0 < negate k.
  {
    ipso (modus aequans (order.negation.strict.reversal &k 0), &hk).
  }
  let proof m := multiplication.left.order.strict.monotonicity (negate &k) &x &y &positive &h.
  leibniz (multiplication.left.negation &k &x), (multiplication.left.negation &k &y) in &m.
  ipso (modus aequans (order.negation.strict.reversal (&k * &y) (&k * &x)), &m).
Qed.

End strict. (* multiplication.left.order.strict *)

(* multiplication.left.order.monotonicity *)
Theorem monotonicity
  : forall (k : SignedBin) (x : SignedBin) (y : SignedBin) . 0 <= k -> x <= y -> k * x <= k * y.
Proof.
  intros k x y hk h.
  match &hk with | zero | positive end.
  - leibniz <- &zero in |- *.
    match (multiplication.annihilation &x) with | zero_x _ end.
    match (multiplication.annihilation &y) with | zero_y _ end.
    leibniz &zero_x, &zero_y in |- *.
    ipso (disjoin (refl 0), _).
  - match &h with | e | smaller end.
    + leibniz &e in |- *.
      ipso (disjoin (refl (&k * &y)), _).
    + ipso (disjoin _,
              (multiplication.left.order.strict.monotonicity &k &x &y &positive &smaller)).
Qed.

End order. (* multiplication.left.order *)

End left. (* multiplication.left *)

Module sign. (* multiplication.sign *)

(* Each sign law multiplies an inequality by the first factor and rewrites
 * [x * 0] to [0].
 *)
(* multiplication.sign.positivity *)
Theorem positivity : forall (x : SignedBin) (y : SignedBin) . 0 < x -> 0 < y -> 0 < x * y.
Proof.
  intros x y hx hy.
  let proof s := multiplication.left.order.strict.monotonicity &x 0 &y &hx &hy.
  match (multiplication.annihilation &x) with | _ zero end.
  leibniz &zero in &s.
  ipso &s.
Qed.

Module negation. (* multiplication.sign.negation *)

(* multiplication.sign.negation.positivity *)
Theorem positivity : forall (x : SignedBin) (y : SignedBin) . x < 0 -> y < 0 -> 0 < x * y.
Proof.
  intros x y hx hy.
  let proof s := multiplication.left.order.strict.reversal &x &y 0 &hx &hy.
  match (multiplication.annihilation &x) with | _ zero end.
  leibniz &zero in &s.
  ipso &s.
Qed.

End negation. (* multiplication.sign.negation *)

Module left. (* multiplication.sign.left *)

(* multiplication.sign.left.negativity *)
Theorem negativity : forall (x : SignedBin) (y : SignedBin) . x < 0 -> 0 < y -> x * y < 0.
Proof.
  intros x y hx hy.
  let proof s := multiplication.left.order.strict.reversal &x 0 &y &hx &hy.
  match (multiplication.annihilation &x) with | _ zero end.
  leibniz &zero in &s.
  ipso &s.
Qed.

End left. (* multiplication.sign.left *)

Module right. (* multiplication.sign.right *)

(* multiplication.sign.right.negativity *)
Theorem negativity : forall (x : SignedBin) (y : SignedBin) . 0 < x -> y < 0 -> x * y < 0.
Proof.
  intros x y hx hy.
  let proof s := multiplication.left.order.strict.monotonicity &x &y 0 &hx &hy.
  match (multiplication.annihilation &x) with | _ zero end.
  leibniz &zero in &s.
  ipso &s.
Qed.

End right. (* multiplication.sign.right *)

End sign. (* multiplication.sign *)

End multiplication. (* multiplication *)

Module division. (* division *)

(* division.magnitude *)
Theorem magnitude
  : forall (x : SignedBin) (d : Bin) .
      abs (x /. d) = (abs x /. d)%b0.
Proof.
  intros x d.
  match &x with | p | | p end.
  -
    simpl divide, abs in |- *.
    match (p /. &d)%b0 with | | k end;
      simpl from_b0, negate in |- *; quod idem est.
  -
    simpl divide, abs in |- *.
    simpl Bin0.divide, Bin0.div in |- *.
    simpl in |- *.
    quod idem est.
  -
    simpl divide, abs in |- *.
    match (p /. &d)%b0 with | | k end;
      simpl from_b0 in |- *; quod idem est.
Qed.

(* division.invariance *)
Theorem invariance
  : forall (x : SignedBin) (d : Bin) (k : Bin) .
      ((+ k) * x) /. (k * d)%b = x /. d.
Proof.
  intros x d k.
  lemma positive : to_integer (+ &k) = Bin.to_nat &k.
  {
    simpl in |- *.
    quod idem est.
  }
  lemma f : to_integer (((+ &k) * &x) /. (&k * &d)%b) = to_integer (&x /. &d).
  {
    leibniz (conversion.division ((+ &k) * &x) (&k * &d)%b),
      (conversion.multiplication (+ &k) &x), (Bin.conversion.multiplication &k &d),
      (conversion.division &x &d), &positive in |- *.
    ipso (Integer.division.invariance (to_integer &x) (Bin.to_nat &d) (Bin.to_nat &k)).
  }
  ipso (conversion.injectivity &f).
Qed.

End division. (* division *)

Module comparison. (* comparison *)

(* comparison.antisymmetry *)
Theorem antisymmetry
  : forall (x : SignedBin) (y : SignedBin) .
      compare x y = Comparison.transpose (compare y x).
Proof.
  intros x y.
  leibniz (conversion.comparison &x &y), (conversion.comparison &y &x) in |- *.
  ipso (Integer.comparison.antisymmetry (to_integer &x) (to_integer &y)).
Qed.

(* comparison.specification *)
Theorem specification
  : forall (x : SignedBin) (y : SignedBin) .
      (compare x y = Comparison.Lt <-> x < y) /\ (compare x y = Comparison.Eq <-> x = y).
Proof.
  intros x y.
  leibniz (conversion.comparison &x &y) in |- *.
  let proof s := Integer.comparison.specification (to_integer &x) (to_integer &y).
  match &s with | strict equality end.
  divide et impera.
  -
    divide et impera.
    +
      intro c.
      ipso (modus aequans (conversion.order &x &y), (modus aequans &strict, &c)).
    +
      intro h.
      ipso (modus aequans &strict, (modus aequans (conversion.order &x &y), &h)).
  -
    divide et impera.
    +
      intro c.
      ipso (conversion.injectivity (modus aequans &equality, &c)).
    +
      intro e.
      ipso (modus aequans &equality, (congru to_integer, &e)).
Qed.

(* Adding [z] on the left keeps each of the three answers: [<] by
 * [addition.order.strict.monotonicity], [=] by rewriting, [>] by the first
 * read backwards.
 *)
(* comparison.translation *)
Theorem translation
  : forall (z : SignedBin) (x : SignedBin) (y : SignedBin) . compare (z + x) (z + y) = compare x y.
Proof.
  intros z x y.
  match (compare &x &y) with | | | end |- c.
  - match (comparison.specification &x &y) with | strict _ end.
    match (comparison.specification (&z + &x) (&z + &y)) with | shifted _ end.
    let proof smaller := modus aequans &strict, &c.
    ipso (modus aequans &shifted, (addition.order.strict.monotonicity &z &x &y &smaller)).
  - match (comparison.specification &x &y) with | _ equality end.
    leibniz (modus aequans &equality, &c) in |- *.
    match (comparison.specification (&z + &y) (&z + &y)) with | _ same end.
    ipso (modus aequans &same, (refl (&z + &y))).
  - lemma reversed : compare y x = Comparison.Lt.
    {
      leibniz (comparison.antisymmetry &y &x), &c in |- *.
      simpl in |- *.
      quod idem est.
    }
    match (comparison.specification &y &x) with | strict_reversed _ end.
    match (comparison.specification (&z + &y) (&z + &x)) with | shifted_reversed _ end.
    let proof below :=
      modus aequans &shifted_reversed,
        (addition.order.strict.monotonicity &z &y &x (modus aequans &strict_reversed, &reversed)).
    leibniz (comparison.antisymmetry (&z + &x) (&z + &y)), &below in |- *.
    simpl in |- *.
    quod idem est.
Qed.

(* Negation reverses each of the three answers, by
 * [order.negation.strict.reversal].
 *)
(* comparison.negation *)
Theorem negation : forall (x : SignedBin) (y : SignedBin) . compare (negate x) (negate y) = compare y x.
Proof.
  intros x y.
  match (compare &y &x) with | | | end |- c.
  - match (comparison.specification &y &x) with | strict _ end.
    match (comparison.specification (negate &x) (negate &y)) with | negated _ end.
    let proof smaller := modus aequans &strict, &c.
    ipso (modus aequans &negated,
          (modus aequans (order.negation.strict.reversal &y &x), &smaller)).
  - match (comparison.specification &y &x) with | _ equality end.
    leibniz (modus aequans &equality, &c) in |- *.
    match (comparison.specification (negate &x) (negate &x)) with | _ same end.
    ipso (modus aequans &same, (refl (negate &x))).
  - lemma reversed : compare x y = Comparison.Lt.
    {
      leibniz (comparison.antisymmetry &x &y), &c in |- *.
      simpl in |- *.
      quod idem est.
    }
    match (comparison.specification &x &y) with | strict_reversed _ end.
    match (comparison.specification (negate &y) (negate &x)) with | negated_reversed _ end.
    let proof below :=
      modus aequans &negated_reversed,
        (modus aequans (order.negation.strict.reversal &x &y),
           (modus aequans &strict_reversed, &reversed)).
    leibniz (comparison.antisymmetry (negate &x) (negate &y)), &below in |- *.
    simpl in |- *.
    quod idem est.
Qed.

End comparison. (* comparison *)

Module minimum. (* minimum *)

Module left. (* minimum.left *)

Module distributivity. (* minimum.left.distributivity *)

(* Both sides choose by [compare x y], once [comparison.translation] takes
 * [z] out of the right side's comparison.
 *)
(* minimum.left.distributivity.addition *)
Theorem addition : forall (z : SignedBin) (x : SignedBin) (y : SignedBin) . z + min x y = min (z + x) (z + y).
Proof.
  intros z x y.
  simpl Comparable.min in |- *.
  leibniz (comparison.translation &z &x &y) in |- *.
  match (compare &x &y) with | | | end; quod idem est.
Qed.

End distributivity. (* minimum.left.distributivity *)

End left. (* minimum.left *)

(* [negate] reverses [compare], so the smaller of two values turns into the
 * greater of their negations.
 *)
(* minimum.duality *)
Theorem duality : forall (x : SignedBin) (y : SignedBin) . negate (min x y) = max (negate x) (negate y).
Proof.
  intros x y.
  simpl Comparable.min, Comparable.max in |- *.
  leibniz (comparison.negation &x &y), (comparison.antisymmetry &y &x) in |- *.
  match (compare &x &y) with | | | end |- c.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    match (comparison.specification &x &y) with | _ equality end.
    leibniz (modus aequans &equality, &c) in |- *.
    quod idem est.
  - simpl in |- *.
    quod idem est.
Qed.

End minimum. (* minimum *)

Module maximum. (* maximum *)

Module left. (* maximum.left *)

Module distributivity. (* maximum.left.distributivity *)

(* maximum.left.distributivity.addition *)
Theorem addition : forall (z : SignedBin) (x : SignedBin) (y : SignedBin) . z + max x y = max (z + x) (z + y).
Proof.
  intros z x y.
  simpl Comparable.max in |- *.
  leibniz (comparison.translation &z &x &y) in |- *.
  match (compare &x &y) with | | | end; quod idem est.
Qed.

End distributivity. (* maximum.left.distributivity *)

End left. (* maximum.left *)

End maximum. (* maximum *)

End SignedBin. (* SignedBin *)

Abbreviation SignedBin := SignedBin.T.

Export (notations) SignedBin.

(* What makes the minus of a negative literal parse. [Numeral.Signed] lets
 * [from_numeral] *receive* a sign, but it does not put one in the grammar:
 * with the prelude off nothing makes [-1011] a term, and without this line
 * [(-1011)%b_signed] is a syntax error at the [-]. Declared outside the module, where
 * it does not collide with the [Local] [- p] for [Negative], and scoped, so
 * [-] keeps whatever else it means elsewhere. Under [only parsing] a negative
 * value still prints as [(-1011)%b_signed], that coming from [to_numeral] below.
 *)
Notation "- x" := (SignedBin.negate x)
  (at level 35, right associativity, only parsing)
  : jw_signed_bin_scope.

(* A number of the type is written in binary digits under its scope, [1011%b_signed]
 * for eleven and [(-1011)%b_signed] for minus eleven, and a closed one prints that
 * way; a literal with any other digit is refused.
 *)
Number Notation SignedBin.T SignedBin.from_numeral SignedBin.to_numeral
  : jw_signed_bin_scope.

(* A [Bin] stands wherever a [SignedBin] is expected, read as its [Positive],
 * and a [Bin0] through [from_b0]; both are printed where
 * they happened. The direct [Bin >-> SignedBin] and the indirect one through
 * [Bin0] give the same term, as [Nat]'s two paths into [Integer] do.
 *)
Coercion SignedBin.Positive : Bin >-> SignedBin.
Coercion SignedBin.from_b0 : Bin0 >-> SignedBin.
Add Printing Coercion SignedBin.Positive.
Add Printing Coercion SignedBin.from_b0.

(* [<] is not well founded on a signed type, there being no least value, so
 * the descent is on the magnitude: [abs] lands in [Bin0], where [<]
 * is well founded, and [Induced] pulls that back. [Integer] descends the same
 * way over [Nat0].
 *)
Instance Bin_magnitude_well_founded
  : WellFounded (Induced (<)%b0 SignedBin.abs) :=
  WellFounded.induced (<)%b0 SignedBin.abs
    Bin0_less_than_well_founded.

Instance Bin_comparable
  : Comparable SignedBin.compare (<)%b_signed :=
  {| Comparable.transitivity  := @SignedBin.order.strict.transitivity
   ; Comparable.specification := SignedBin.comparison.specification
   ; Comparable.antisymmetry  := SignedBin.comparison.antisymmetry |}.

Instance Bin_add_monoid
  : Monoid SignedBin.add SignedBin.Zero :=
  {| Monoid.semigroup :=
      {| Semigroup.associativity := SignedBin.addition.associativity |}
   ; Monoid.identity := SignedBin.addition.identity |}.

Instance Bin_add_cancellative : Cancellative SignedBin.add :=
  {| Cancellative.cancellation := SignedBin.addition.cancellation |}.

Instance Bin_add_commutative : Commutative SignedBin.add :=
  {| Commutative.commutativity := SignedBin.addition.commutativity |}.

(* What the signed type buys over [Bin0]: every value has an inverse,
 * so the additive monoid becomes a group.
 *)
Instance Bin_add_group
  : Group SignedBin.add SignedBin.Zero SignedBin.negate :=
  {| Group.monoid  := Bin_add_monoid
   ; Group.inverse := SignedBin.addition.inverse |}.

Instance Bin_add_abelian_group
  : AbelianGroup SignedBin.add SignedBin.Zero SignedBin.negate :=
  {| AbelianGroup.group       := Bin_add_group
   ; AbelianGroup.commutative := Bin_add_commutative |}.

Instance Bin_mul_monoid
  : Monoid SignedBin.mul Bin.One :=
  {| Monoid.semigroup :=
      {| Semigroup.associativity := SignedBin.multiplication.associativity |}
   ; Monoid.identity := SignedBin.multiplication.identity |}.

Instance Bin_mul_commutative : Commutative SignedBin.mul :=
  {| Commutative.commutativity := SignedBin.multiplication.commutativity |}.

Instance Bin_ring
  : Ring SignedBin.add SignedBin.Zero SignedBin.negate SignedBin.mul
      Bin.One :=
  {| Ring.abelian_group  := Bin_add_abelian_group
   ; Ring.monoid         := Bin_mul_monoid
   ; Ring.distributivity := SignedBin.multiplication.distributivity.over.addition |}.
