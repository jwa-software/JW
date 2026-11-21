(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

From JW Require Import Core.All.
From JW Require Import Data.Base.Comparison.
From JW Require Import Data.Comparable.
From JW Require Import Data.Machine.Bit.
From JW Require Import Data.Number.Binary.SignedBin.
From JW Require Import Data.Number.Binary.Bin.
From JW Require Import Data.Number.Binary.Bin0.
From JW Require Import Data.Product.
From JW Require Import Tactics.Equation.
From JW Require Import Tactics.Modus.
From JW Require Import Tactics.Witness.

(* What a signed fixed-width integer in two's complement provides: its
 * operations, its constants, and facts about them. Each [Parameter] is a field
 * that every width defines or proves, not an axiom. The operations and
 * constants are [Inline]: a width that includes [Laws] gets laws stated with
 * its own operations, such as [Int8.add], so [leibniz] can rewrite with them.
 *)
Module Type Width.

Parameter Inline T : Type.
Parameter Inline Zero : T.
Parameter Inline One : T.
Parameter Inline Min : T.
Parameter Inline Max : T.
Parameter Inline to_b_signed : T -> SignedBin.
Parameter Inline from_b_signed : SignedBin -> T.
Parameter Inline from_b0 : Bin0 -> T.
Parameter Inline unsigned_value : T -> Bin0.
Parameter Inline sign_bit : T -> Bit.
Parameter Inline add : T -> T -> T.
Parameter Inline sub : T -> T -> T.
Parameter Inline negate : T -> T.
Parameter Inline LessThan : T -> T -> Prop.
Parameter Inline LessOrEqual : T -> T -> Prop.
Parameter Inline add_with_overflow : T -> T -> Product Bit T.
Parameter Inline sub_with_overflow : T -> T -> Product Bit T.
Parameter Inline compare : T -> T -> Comparison.
Parameter Inline mul : T -> T -> T.
Parameter Inline mul_with_overflow : T -> T -> Product Bit T.
Parameter Inline half : Bin.
Parameter Inline modulus : Bin.
Parameter Inline beyond : Bin.

Module order. (* order *)

Module strict. (* order.strict *)

Parameter specification
  : forall (x : T) (y : T) . LessThan x y <-> (to_b_signed x < to_b_signed y)%b_signed.

End strict. (* order.strict *)

Parameter specification
  : forall (x : T) (y : T) . LessOrEqual x y <-> x = y \/ LessThan x y.

End order. (* order *)

Module conversion. (* conversion *)

Parameter section
  : forall (x : T) . from_b_signed (to_b_signed x) = x.
Parameter comparison
  : forall (x : T) (y : T) . compare x y = SignedBin.compare (to_b_signed x) (to_b_signed y).
Parameter addition
  : forall (x : T) (y : T) .
      (pi_1 (add_with_overflow x y))%product = 0%bit
      -> to_b_signed (add x y) = (to_b_signed x + to_b_signed y)%b_signed.
Parameter difference
  : forall (a : Bin0) (b : Bin0) .
      from_b_signed (SignedBin.b0_difference a b)
      = add (from_b0 a) (negate (from_b0 b)).

Module forward. (* conversion.forward *)

Parameter specification
  : forall (x : T) .
      to_b_signed x
      = SignedBin.b0_difference (unsigned_value x)
          (Bin0.Positive modulus * Bit.to_b0 (sign_bit x))%b0.

End forward. (* conversion.forward *)

Module backward. (* conversion.backward *)

Parameter specification
  : forall (z : SignedBin) .
      from_b_signed z
      = add (from_b0 (SignedBin.ramp z))
          (negate (from_b0 (SignedBin.ramp (SignedBin.negate z)))).

End backward. (* conversion.backward *)

Module boundedness. (* conversion.boundedness *)

Parameter positive
  : forall (x : T) (p : Bin) .
      to_b_signed x = SignedBin.Positive p
      -> (Bin0.Positive p < Bin0.Positive half)%b0.
Parameter negative
  : forall (x : T) (p : Bin) .
      to_b_signed x = SignedBin.Negative p
      -> (Bin0.Positive p <= Bin0.Positive half)%b0.

End boundedness. (* conversion.boundedness *)

Module retraction. (* conversion.retraction *)

Parameter nonnegative
  : forall (n : Bin0) .
      (n < Bin0.Positive half)%b0
      -> to_b_signed (from_b_signed (SignedBin.from_b0 n)) = SignedBin.from_b0 n.
Parameter negative
  : forall (p : Bin) .
      (Bin0.Positive p <= Bin0.Positive half)%b0
      -> to_b_signed (from_b_signed (SignedBin.Negative p)) = SignedBin.Negative p.

End retraction. (* conversion.retraction *)

End conversion. (* conversion *)

Module reinterpretation. (* reinterpretation *)

Parameter boundedness
  : forall (x : T) . (unsigned_value x < Bin0.Positive modulus)%b0.
Parameter injectivity
  : forall {x : T} {y : T} . unsigned_value x = unsigned_value y -> x = y.
Parameter multiplication
  : forall (x : T) (y : T) .
      (unsigned_value (mul x y)
       = (unsigned_value x * unsigned_value y) %. modulus)%b0.
Parameter reduction
  : forall (n : Bin0) .
      (unsigned_value (from_b0 n) = n %. modulus)%b0.

Module reduction. (* reinterpretation.reduction *)

Parameter additivity
  : forall (m : Bin0) (n : Bin0) .
      from_b0 (m + n)%b0
      = add (from_b0 m) (from_b0 n).
Parameter zero
  : from_b0 Bin0.Zero = Zero.

End reduction. (* reinterpretation.reduction *)

End reinterpretation. (* reinterpretation *)

Module addition. (* addition *)

Parameter associativity
  : forall (x : T) (y : T) (z : T) . add (add x y) z = add x (add y z).
Parameter commutativity
  : forall (x : T) (y : T) . add x y = add y x.
Parameter identity
  : forall (x : T) . (add Zero x = x) /\ (add x Zero = x).
Parameter inverse
  : forall (x : T) . (add (negate x) x = Zero) /\ (add x (negate x) = Zero).

End addition. (* addition *)

Module multiplication. (* multiplication *)

Parameter annihilation
  : forall (x : T) . (mul Zero x = Zero) /\ (mul x Zero = Zero).

Module left. (* multiplication.left *)

Parameter negation
  : forall (x : T) (y : T) . mul (negate x) y = negate (mul x y).

End left. (* multiplication.left *)

Module right. (* multiplication.right *)

Parameter negation
  : forall (x : T) (y : T) . mul x (negate y) = negate (mul x y).

End right. (* multiplication.right *)

End multiplication. (* multiplication *)

Module subtraction. (* subtraction *)

Parameter specification
  : forall (x : T) (y : T) . sub x y = add x (negate y).

End subtraction. (* subtraction *)

Module flag. (* flag *)

Module addition. (* flag.addition *)

Parameter specification
  : forall (x : T) (y : T) .
      (pi_1 (add_with_overflow x y))%product
      = Bit.and (Bit.flip (Bit.xor (sign_bit x) (sign_bit y)))
          (Bit.xor (sign_bit (add x y)) (sign_bit x)).

End addition. (* flag.addition *)

Module subtraction. (* flag.subtraction *)

Parameter specification
  : forall (x : T) (y : T) .
      (pi_1 (sub_with_overflow x y))%product
      = Bit.and (Bit.xor (sign_bit x) (sign_bit y)) (Bit.xor (sign_bit (sub x y)) (sign_bit x)).

End subtraction. (* flag.subtraction *)

Module multiplication. (* flag.multiplication *)

Parameter specification
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

End multiplication. (* flag.multiplication *)

End flag. (* flag *)

Module minimum. (* minimum *)

Parameter specification
  : to_b_signed Min = SignedBin.Negative half.
Parameter negation
  : negate Min = Min.

End minimum. (* minimum *)

Module maximum. (* maximum *)

Parameter specification
  : (to_b_signed Max + 1 = SignedBin.Positive half)%b_signed.
Parameter positivity
  : (0 < to_b_signed Max)%b_signed.

End maximum. (* maximum *)

Module one. (* one *)

Parameter specification
  : to_b_signed One = 1%b_signed.

End one. (* one *)

Module modulus. (* modulus *)

Parameter specification
  : (SignedBin.Positive modulus = SignedBin.Positive half + SignedBin.Positive half)%b_signed.
Parameter wrapping
  : from_b_signed (SignedBin.Positive modulus) = Zero.

End modulus. (* modulus *)

Module beyond. (* beyond *)

Parameter specification
  : (SignedBin.Positive beyond = SignedBin.Positive modulus + SignedBin.Positive half)%b_signed.

End beyond. (* beyond *)

End Width.

(* The laws of the bounds, of overflow, of negation, of the successor, of the
 * order and of the comparison, for every width.
 *)
Module Laws (W : Width).

(* [only parsing] keeps goals printing the operations by name; the scope is
 * bound to [W.T] here only, so an included law leaves the width's own scope
 * alone.
 *)
Local Notation "x + y" := (W.add x y) (only parsing)
  : jw_signed_scope.
Local Notation "x - y" := (W.sub x y) (only parsing)
  : jw_signed_scope.
Local Notation "x * y" := (W.mul x y) (only parsing)
  : jw_signed_scope.
Local Notation "- x" := (W.negate x)
  (at level 35, right associativity, only parsing)
  : jw_signed_scope.
Local Notation "x < y" := (W.LessThan x y) (only parsing)
  : jw_signed_scope.
Local Notation "x <= y" := (W.LessOrEqual x y) (only parsing)
  : jw_signed_scope.
#[local] Bind Scope jw_signed_scope with W.T.
Local Open Scope jw_signed_scope.

(* A value is fixed by its [SignedBin] reading. *)
Lemma injectivity : forall {x : W.T} {y : W.T} . W.to_b_signed x = W.to_b_signed y -> x = y.
Proof.
  intros x y e.
  leibniz <- (W.conversion.section &x), <- (W.conversion.section &y), &e in |- *.
  quod idem est.
Qed.

(* The least value is at most the greatest. *)
Lemma ordered : (SignedBin.Negative W.half <= W.to_b_signed W.Max)%b_signed.
Proof.
  ipso (disjoin _,
        (SignedBin.order.strict.transitivity
           (SignedBin.order.sign.negativity W.half) W.maximum.positivity)).
Qed.

(* [- (- x)] is [- (- x) + (- x + x)], and the first two add up to zero. *)
Lemma involution : forall (x : W.T) . (- (- x)) = x.
Proof.
  intro x.
  match (W.addition.identity (- (- &x))) with | _ i end.
  leibniz <- &i in |- *.
  match (W.addition.inverse &x) with | l _ end.
  leibniz <- &l in |- *.
  leibniz <- (W.addition.associativity (- (- &x)) (- &x) &x) in |- *.
  match (W.addition.inverse (- &x)) with | cancel _ end.
  leibniz &cancel in |- *.
  match (W.addition.identity &x) with | z _ end.
  ipso &z.
Qed.

(* Both sides have the unsigned reading [(m * n) %. W.modulus]. *)
Lemma multiplicativity
  : forall (m : Bin0) (n : Bin0) .
      W.from_b0 (m * n)%b0
      = W.from_b0 m * W.from_b0 n.
Proof.
  intros m n.
  lemma facto
    : W.unsigned_value (W.from_b0 (m * n)%b0)
      = W.unsigned_value (W.from_b0 m * W.from_b0 n).
  {
    leibniz
      (W.reinterpretation.reduction (&m * &n)%b0),
      (W.reinterpretation.multiplication (W.from_b0 &m) (W.from_b0 &n)),
      (W.reinterpretation.reduction &m),
      (W.reinterpretation.reduction &n),
      (Bin0.modulo.product.left.absorption &m (&n %. W.modulus)%b0 W.modulus),
      (Bin0.modulo.product.right.absorption &m &n W.modulus)
      in |- *.
    quod idem est.
  }
  ipso (W.reinterpretation.injectivity &facto).
Qed.

Module bound. (* bound *)

(* The bounds of [W.conversion.boundedness.positive] and
 * [W.conversion.boundedness.negative], read in [SignedBin]'s order.
 *)
(* bound.range *)
Theorem range
  : forall (x : W.T) . (SignedBin.Negative W.half <= W.to_b_signed x /\ W.to_b_signed x <= W.to_b_signed W.Max)%b_signed.
Proof.
  intro x.
  match (W.to_b_signed &x) with | p | | p end |- e.
  - let proof b := W.conversion.boundedness.negative &x &p &e.
    divide et impera.
    + match &b with | same | smaller end.
      * lemma facto : W.half = p.
        {
          ipso (symm (congru (fun (n : Bin0) .
                                match n with
                                | Bin0.Zero       => &p
                                | Bin0.Positive q => q
                                end), &same)).
        }
        leibniz &facto in |- *.
        ipso (disjoin (refl (SignedBin.Negative &p)), _).
      * let proof lifted :=
          modus aequans
            (SignedBin.order.embedding.preservation
               (Bin0.Positive &p) (Bin0.Positive W.half)),
            &smaller.
        lemma facto : (SignedBin.Negative W.half < SignedBin.Negative p)%b_signed.
        {
          ipso (modus aequans
                  (SignedBin.order.negation.strict.reversal (SignedBin.Positive &p) (SignedBin.Positive W.half)),
                  &lifted).
        }
        ipso (disjoin _, &facto).
    + ipso (disjoin _,
            (SignedBin.order.strict.transitivity
               (SignedBin.order.sign.negativity &p) W.maximum.positivity)).
  - divide et impera.
    + ipso (disjoin _, (SignedBin.order.sign.negativity W.half)).
    + ipso (disjoin _, W.maximum.positivity).
  - let proof b := W.conversion.boundedness.positive &x &p &e.
    divide et impera.
    + ipso (disjoin _,
            (SignedBin.order.strict.transitivity
               (SignedBin.order.sign.negativity W.half) (SignedBin.order.sign.positivity &p))).
    + let proof lifted :=
        modus aequans
          (SignedBin.order.embedding.preservation
             (Bin0.Positive &p) (Bin0.Positive W.half)),
          &b.
      lemma facto : (SignedBin.Positive p < W.to_b_signed W.Max + 1)%b_signed.
      {
        leibniz W.maximum.specification in |- *.
        ipso &lifted.
      }
      ipso (modus aequans (SignedBin.order.discreteness (SignedBin.Positive &p) (W.to_b_signed W.Max)), &facto).
Qed.

(* bound.lower *)
Theorem lower : forall (x : W.T) . W.Min <= x.
Proof.
  intro x.
  match (bound.range &x) with | low _ end.
  match &low with | same | smaller end.
  - lemma facto : W.to_b_signed W.Min = W.to_b_signed x.
    {
      leibniz W.minimum.specification in |- *.
      ipso &same.
    }
    ipso (modus aequans (W.order.specification W.Min &x), (disjoin (injectivity &facto), _)).
  - lemma facto : W.Min < x.
    {
      leibniz <- W.minimum.specification in &smaller.
      ipso (modus aequans (W.order.strict.specification W.Min &x), &smaller).
    }
    ipso (modus aequans (W.order.specification W.Min &x), (disjoin _, &facto)).
Qed.

(* bound.upper *)
Theorem upper : forall (x : W.T) . x <= W.Max.
Proof.
  intro x.
  match (bound.range &x) with | _ high end.
  match &high with | same | smaller end.
  - ipso (modus aequans (W.order.specification &x W.Max), (disjoin (injectivity &same), _)).
  - ipso (modus aequans (W.order.specification &x W.Max),
          (disjoin _, (modus aequans (W.order.strict.specification &x W.Max), &smaller))).
Qed.

End bound. (* bound *)

Module sign. (* sign *)

(* A clear sign bit leaves the reading the unsigned value itself. *)
(* sign.clear *)
Theorem clear : forall (x : W.T) . W.sign_bit x = 0%bit -> (0 <= W.to_b_signed x)%b_signed.
Proof.
  intros x s.
  leibniz (W.conversion.forward.specification &x), &s in |- *.
  lemma scaled : (Bin0.Positive W.modulus * Bit.to_b0 0 = 0)%b0.
  {
    simpl Bit.to_b0 in |- *.
    simpl in |- *.
    quod idem est.
  }
  leibniz &scaled in |- *.
  lemma facto
    : SignedBin.b0_difference (W.unsigned_value x) 0%b0
      = SignedBin.from_b0 (W.unsigned_value x).
  {
    match (W.unsigned_value &x) with | | p end; simpl in |- *; quod idem est.
  }
  leibniz &facto in |- *.
  ipso (SignedBin.order.embedding.nonnegativity (W.unsigned_value &x)).
Qed.

(* A set sign bit takes the modulus from an unsigned value below it. *)
(* sign.set *)
Theorem set : forall (x : W.T) . W.sign_bit x = 1%bit -> (W.to_b_signed x < 0)%b_signed.
Proof.
  intros x s.
  leibniz (W.conversion.forward.specification &x), &s in |- *.
  lemma whole
    : (Bin0.Positive W.modulus * Bit.to_b0 1
       = Bin0.Positive W.modulus)%b0.
  {
    match (Bin0.multiplication.identity (Bin0.Positive W.modulus)) with | _ r end.
    ipso &r.
  }
  leibniz &whole in |- *.
  lemma split
    : forall (a : Bin0) (b : Bin0) .
        SignedBin.b0_difference a b
        = (SignedBin.from_b0 a + SignedBin.negate (SignedBin.from_b0 b))%b_signed.
  {
    intros a b.
    match &a with | | p end; match &b with | | q end;
      simpl SignedBin.add in |- *; simpl in |- *; quod idem est.
  }
  leibniz (&split (W.unsigned_value &x) (Bin0.Positive W.modulus)) in |- *.
  let proof lifted :=
    modus aequans
      (SignedBin.order.embedding.preservation (W.unsigned_value &x) (Bin0.Positive W.modulus)),
      (W.reinterpretation.boundedness &x).
  let proof shifted :=
    SignedBin.addition.order.strict.monotonicity
      (SignedBin.negate (SignedBin.from_b0 (Bin0.Positive W.modulus))) _ _ &lifted.
  leibniz
    (SignedBin.addition.commutativity
       (SignedBin.negate (SignedBin.from_b0 (Bin0.Positive W.modulus)))
       (SignedBin.from_b0 (W.unsigned_value &x))),
    (SignedBin.addition.left.inverse (SignedBin.from_b0 (Bin0.Positive W.modulus)))
    in &shifted.
  ipso &shifted.
Qed.

End sign. (* sign *)

Module wrapping. (* wrapping *)

(* [SignedBin.add] is the difference of the summed positive parts and the summed
 * negative parts, and [from_b_signed] carries a difference and a sum over; what is
 * left is regrouping the four parts.
 *)
(* wrapping.additivity *)
Theorem additivity
  : forall (a : SignedBin) (b : SignedBin) . W.from_b_signed (a + b)%b_signed = W.from_b_signed a + W.from_b_signed b.
Proof.
  intros a b.
  lemma inverted : forall (c : W.T) (d : W.T) . (- (c + d)) = - c + - d.
  {
    intros c d.
    lemma undone : (c + d) + (- c + - d) = W.Zero.
    {
      leibniz
        (W.addition.commutativity (- &c) (- &d)),
        (W.addition.associativity &c &d (- &d + - &c)),
        <- (W.addition.associativity &d (- &d) (- &c))
        in |- *.
      match (W.addition.inverse &d) with | _ right_d end.
      match (W.addition.identity (- &c)) with | left_c _ end.
      match (W.addition.inverse &c) with | _ right_c end.
      leibniz &right_d, &left_c, &right_c in |- *.
      quod idem est.
    }
    match (W.addition.identity (- (&c + &d))) with | _ plus_zero end.
    leibniz <- &plus_zero, <- &undone in |- *.
    leibniz <- (W.addition.associativity (- (&c + &d)) (&c + &d) (- &c + - &d)) in |- *.
    match (W.addition.inverse (&c + &d)) with | left_inverse _ end.
    match (W.addition.identity (- &c + - &d)) with | left_identity _ end.
    leibniz &left_inverse, &left_identity in |- *.
    quod idem est.
  }
  simpl SignedBin.add in |- *.
  leibniz
    (W.conversion.difference
       (SignedBin.ramp &a + SignedBin.ramp &b)%b0
       (SignedBin.ramp (SignedBin.negate &a) + SignedBin.ramp (SignedBin.negate &b))%b0),
    (W.reinterpretation.reduction.additivity (SignedBin.ramp &a) (SignedBin.ramp &b)),
    (W.reinterpretation.reduction.additivity (SignedBin.ramp (SignedBin.negate &a)) (SignedBin.ramp (SignedBin.negate &b)))
    in |- *.
  leibniz
    (&inverted
       (W.from_b0 (SignedBin.ramp (SignedBin.negate &a)))
       (W.from_b0 (SignedBin.ramp (SignedBin.negate &b))))
    in |- *.
  leibniz
    (W.conversion.backward.specification &a),
    (W.conversion.backward.specification &b)
    in |- *.
  let pa := W.from_b0 (SignedBin.ramp &a) in |- *.
  let pb := W.from_b0 (SignedBin.ramp &b) in |- *.
  let na := (- W.from_b0 (SignedBin.ramp (SignedBin.negate &a))) in |- *.
  let nb := (- W.from_b0 (SignedBin.ramp (SignedBin.negate &b))) in |- *.
  leibniz
    (W.addition.associativity &pa &pb (&na + &nb)),
    <- (W.addition.associativity &pb &na &nb),
    (W.addition.commutativity &pb &na),
    (W.addition.associativity &na &pb &nb),
    <- (W.addition.associativity &pa &na (&pb + &nb))
    in |- *.
  quod idem est.
Qed.

(* [from_b_signed a] plus [from_b_signed (- a)] is [from_b_signed 0], so the second is the
 * inverse of the first.
 *)
(* wrapping.negation *)
Theorem negation : forall (a : SignedBin) . W.from_b_signed (SignedBin.negate a) = - W.from_b_signed a.
Proof.
  intro a.
  lemma zero : W.from_b_signed a + W.from_b_signed (SignedBin.negate a) = W.Zero.
  {
    leibniz
      <- (wrapping.additivity &a (SignedBin.negate &a)),
      (SignedBin.addition.right.inverse &a),
      (W.conversion.backward.specification 0%b_signed)
      in |- *.
    lemma origin : W.from_b0 (SignedBin.ramp 0%b_signed) = W.Zero.
    {
      ipso W.reinterpretation.reduction.zero.
    }
    lemma negated_origin : W.from_b0 (SignedBin.ramp (SignedBin.negate 0%b_signed)) = W.Zero.
    {
      ipso W.reinterpretation.reduction.zero.
    }
    leibniz &origin, &negated_origin in |- *.
    match (W.addition.inverse W.Zero) with | _ right_inverse end.
    ipso &right_inverse.
  }
  match (W.addition.identity (W.from_b_signed (SignedBin.negate &a))) with | left_identity _ end.
  match (W.addition.inverse (W.from_b_signed &a)) with | left_inverse _ end.
  leibniz <- &left_identity, <- &left_inverse in |- *.
  leibniz
    (W.addition.associativity (- W.from_b_signed &a) (W.from_b_signed &a) (W.from_b_signed (SignedBin.negate &a))),
    &zero
    in |- *.
  match (W.addition.identity (- W.from_b_signed &a)) with | _ right_identity end.
  ipso &right_identity.
Qed.

(* wrapping.summation *)
Theorem summation
  : forall (x : W.T) (y : W.T) . x + y = W.from_b_signed (W.to_b_signed x + W.to_b_signed y)%b_signed.
Proof.
  intros x y.
  leibniz
    (wrapping.additivity (W.to_b_signed &x) (W.to_b_signed &y)),
    (W.conversion.section &x),
    (W.conversion.section &y)
    in |- *.
  quod idem est.
Qed.

(* wrapping.difference *)
Theorem difference
  : forall (x : W.T) (y : W.T) . x - y = W.from_b_signed (W.to_b_signed x - W.to_b_signed y)%b_signed.
Proof.
  intros x y.
  leibniz (W.subtraction.specification &x &y) in |- *.
  simpl SignedBin.sub in |- *.
  leibniz
    (wrapping.additivity (W.to_b_signed &x) (SignedBin.negate (W.to_b_signed &y))),
    (wrapping.negation (W.to_b_signed &y)),
    (W.conversion.section &x),
    (W.conversion.section &y)
    in |- *.
  quod idem est.
Qed.

(* By the signs of [a] and [b]: [W.from_b_signed] of a positive [p] is
 * [W.from_b0 p] and of a negative one its negation, [W.mul] takes
 * the signs out as [SignedBin.mul] does, and [W.from_b0] is
 * multiplicative.
 *)
(* wrapping.multiplicativity *)
Theorem multiplicativity
  : forall (a : SignedBin) (b : SignedBin) . W.from_b_signed (a * b)%b_signed = W.from_b_signed a * W.from_b_signed b.
Proof.
  intros a b.
  lemma negated : - W.Zero = W.Zero.
  {
    match (W.addition.identity (- W.Zero)) with | left_identity _ end.
    match (W.addition.inverse W.Zero) with | _ right_inverse end.
    leibniz <- &left_identity in |- *.
    ipso &right_inverse.
  }
  lemma positive
    : forall (p : Bin) .
        W.from_b_signed (SignedBin.Positive p) = W.from_b0 (Bin0.Positive p).
  {
    intro p.
    leibniz (W.conversion.backward.specification (SignedBin.Positive &p)) in |- *.
    lemma vanishing : W.from_b0 (SignedBin.ramp (SignedBin.negate (SignedBin.Positive &p))) = W.Zero.
    {
      ipso W.reinterpretation.reduction.zero.
    }
    leibniz &vanishing, &negated in |- *.
    match (W.addition.identity (W.from_b0 (SignedBin.ramp (SignedBin.Positive &p)))) with | _ i end.
    leibniz &i in |- *.
    ipso (refl (W.from_b0 (Bin0.Positive &p))).
  }
  lemma negative
    : forall (p : Bin) .
        W.from_b_signed (SignedBin.Negative p) = - W.from_b0 (Bin0.Positive p).
  {
    intro p.
    leibniz (W.conversion.backward.specification (SignedBin.Negative &p)) in |- *.
    lemma vanishing : W.from_b0 (SignedBin.ramp (SignedBin.Negative &p)) = W.Zero.
    {
      ipso W.reinterpretation.reduction.zero.
    }
    leibniz &vanishing in |- *.
    match (W.addition.identity (- W.from_b0 (SignedBin.ramp (SignedBin.negate (SignedBin.Negative &p)))))
      with | i _ end.
    leibniz &i in |- *.
    ipso (refl (- W.from_b0 (Bin0.Positive &p))).
  }
  lemma zero : W.from_b_signed 0%b_signed = W.Zero.
  {
    leibniz (W.conversion.backward.specification 0%b_signed) in |- *.
    lemma vanishing : W.from_b0 (SignedBin.ramp 0%b_signed) = W.Zero.
    {
      ipso W.reinterpretation.reduction.zero.
    }
    lemma vanished : W.from_b0 (SignedBin.ramp (SignedBin.negate 0%b_signed)) = W.Zero.
    {
      ipso W.reinterpretation.reduction.zero.
    }
    leibniz &vanishing, &vanished, &negated in |- *.
    match (W.addition.identity W.Zero) with | i _ end.
    ipso &i.
  }
  lemma product
    : forall (p : Bin) (q : Bin) .
        W.from_b0 (Bin0.Positive (p * q)%b)
        = W.from_b0 (Bin0.Positive p)
          * W.from_b0 (Bin0.Positive q).
  {
    intros p q.
    ipso (multiplicativity (Bin0.Positive &p) (Bin0.Positive &q)).
  }
  match &a with | p | | p end.
  - match &b with | q | | q end.
    + let proof e
        : W.from_b_signed (SignedBin.Negative &p * SignedBin.Negative &q)%b_signed
          = W.from_b0 (Bin0.Positive (&p * &q)%b)
        := &positive (&p * &q)%b.
      leibniz
        &e,
        (&negative &p),
        (&negative &q),
        (W.multiplication.left.negation
           (W.from_b0 (Bin0.Positive &p))
           (- W.from_b0 (Bin0.Positive &q))),
        (W.multiplication.right.negation
           (W.from_b0 (Bin0.Positive &p))
           (W.from_b0 (Bin0.Positive &q))),
        (involution
           (W.from_b0 (Bin0.Positive &p)
            * W.from_b0 (Bin0.Positive &q))),
        (&product &p &q)
        in |- *.
      quod idem est.
    + let proof e : W.from_b_signed (SignedBin.Negative &p * 0)%b_signed = W.Zero := &zero.
      match (W.multiplication.annihilation (- W.from_b0 (Bin0.Positive &p)))
        with | _ r end.
      leibniz &e, (&negative &p), &zero, &r in |- *.
      quod idem est.
    + let proof e
        : W.from_b_signed (SignedBin.Negative &p * SignedBin.Positive &q)%b_signed
          = - W.from_b0 (Bin0.Positive (&p * &q)%b)
        := &negative (&p * &q)%b.
      leibniz
        &e,
        (&negative &p),
        (&positive &q),
        (W.multiplication.left.negation
           (W.from_b0 (Bin0.Positive &p))
           (W.from_b0 (Bin0.Positive &q))),
        (&product &p &q)
        in |- *.
      quod idem est.
  - let proof e : W.from_b_signed (0 * &b)%b_signed = W.Zero := &zero.
    match (W.multiplication.annihilation (W.from_b_signed &b)) with | l _ end.
    leibniz &e, &zero, &l in |- *.
    quod idem est.
  - match &b with | q | | q end.
    + let proof e
        : W.from_b_signed (SignedBin.Positive &p * SignedBin.Negative &q)%b_signed
          = - W.from_b0 (Bin0.Positive (&p * &q)%b)
        := &negative (&p * &q)%b.
      leibniz
        &e,
        (&positive &p),
        (&negative &q),
        (W.multiplication.right.negation
           (W.from_b0 (Bin0.Positive &p))
           (W.from_b0 (Bin0.Positive &q))),
        (&product &p &q)
        in |- *.
      quod idem est.
    + let proof e : W.from_b_signed (SignedBin.Positive &p * 0)%b_signed = W.Zero := &zero.
      match (W.multiplication.annihilation (W.from_b0 (Bin0.Positive &p)))
        with | _ r end.
      leibniz &e, (&positive &p), &zero, &r in |- *.
      quod idem est.
    + let proof e
        : W.from_b_signed (SignedBin.Positive &p * SignedBin.Positive &q)%b_signed
          = W.from_b0 (Bin0.Positive (&p * &q)%b)
        := &positive (&p * &q)%b.
      leibniz &e, (&positive &p), (&positive &q), (&product &p &q) in |- *.
      quod idem est.
Qed.

(* [W.conversion.retraction.nonnegative] and [W.conversion.retraction.negative]
 * together, their bounds read in [SignedBin]'s order.
 *)
(* wrapping.retraction *)
Theorem retraction
  : forall (z : SignedBin) .
      (SignedBin.Negative W.half <= z /\ z <= W.to_b_signed W.Max)%b_signed -> W.to_b_signed (W.from_b_signed z) = z.
Proof.
  intros z h.
  match &h with | low high end.
  match &z with | p | | p end.
  - lemma b : (Bin0.Positive p <= Bin0.Positive W.half)%b0.
    {
      match &low with | same | smaller end.
      + lemma facto : W.half = p.
        {
          ipso (congru (fun (v : SignedBin) .
                          match v with
                          | SignedBin.Negative q => q
                          | SignedBin.Zero       => &p
                          | SignedBin.Positive q => q
                          end), &same).
        }
        leibniz &facto in |- *.
        ipso (disjoin (refl (Bin0.Positive &p)), _).
      + let proof reversed :=
          modus aequans
            (SignedBin.order.negation.strict.reversal (SignedBin.Positive &p) (SignedBin.Positive W.half)),
            &smaller.
        ipso (disjoin _,
                (modus aequans
                   (SignedBin.order.embedding.preservation
                      (Bin0.Positive &p) (Bin0.Positive W.half)),
                   &reversed)).
    }
    ipso (W.conversion.retraction.negative &p &b).
  - lemma small : (0 < Bin0.Positive W.half)%b0.
    {
      simpl Bin0.LessThan in |- *.
      exists W.half.
      simpl in |- *.
      quod idem est.
    }
    ipso (W.conversion.retraction.nonnegative 0%b0 &small).
  - lemma small : (Bin0.Positive p < Bin0.Positive W.half)%b0.
    {
      lemma lifted : (SignedBin.Positive p < SignedBin.Positive W.half)%b_signed.
      {
        leibniz <- W.maximum.specification in |- *.
        ipso (modus aequans (SignedBin.order.discreteness (SignedBin.Positive &p) (W.to_b_signed W.Max)), &high).
      }
      ipso (modus aequans
              (SignedBin.order.embedding.preservation
                 (Bin0.Positive &p) (Bin0.Positive W.half)),
              &lifted).
    }
    ipso (W.conversion.retraction.nonnegative (Bin0.Positive &p) &small).
Qed.

(* [from_b_signed] of the modulus is [Zero], so shifting by the modulus changes
 * nothing that [from_b_signed] gives, and moves a value just past either end back
 * into range.
 *)
(* wrapping.upper *)
Theorem upper
  : forall (s : SignedBin) .
      (W.to_b_signed W.Max < s /\ s < SignedBin.Positive W.beyond)%b_signed
      -> W.to_b_signed (W.from_b_signed s) = (s - SignedBin.Positive W.modulus)%b_signed.
Proof.
  intros s h.
  match &h with | above below end.
  lemma shifted : W.from_b_signed s = W.from_b_signed (s - SignedBin.Positive W.modulus)%b_signed.
  {
    simpl SignedBin.sub in |- *.
    leibniz
      (wrapping.additivity &s (SignedBin.negate (SignedBin.Positive W.modulus))),
      (wrapping.negation (SignedBin.Positive W.modulus)),
      W.modulus.wrapping
      in |- *.
    lemma negated : - W.Zero = W.Zero.
    {
      match (W.addition.identity (- W.Zero)) with | left_identity _ end.
      match (W.addition.inverse W.Zero) with | _ right_inverse end.
      leibniz <- &left_identity in |- *.
      ipso &right_inverse.
    }
    leibniz &negated in |- *.
    match (W.addition.identity (W.from_b_signed &s)) with | _ right_identity end.
    ipso (symm &right_identity).
  }
  (* [half - (half + half)] regrouped. *)
  lemma folded : (SignedBin.Positive W.half - SignedBin.Positive W.modulus = SignedBin.Negative W.half)%b_signed.
  {
    leibniz
      W.modulus.specification,
      (SignedBin.subtraction.specification (SignedBin.Positive W.half)
         (SignedBin.Positive W.half + SignedBin.Positive W.half)%b_signed),
      (SignedBin.negation.additivity (SignedBin.Positive W.half) (SignedBin.Positive W.half)),
      <- (SignedBin.addition.associativity (SignedBin.Positive W.half) (SignedBin.negate (SignedBin.Positive W.half))
            (SignedBin.negate (SignedBin.Positive W.half))),
      (SignedBin.addition.right.inverse (SignedBin.Positive W.half)),
      (SignedBin.addition.left.identity (SignedBin.negate (SignedBin.Positive W.half)))
      in |- *.
    ipso (refl (SignedBin.Negative W.half)).
  }
  lemma low : (SignedBin.Negative W.half <= s - SignedBin.Positive W.modulus)%b_signed.
  {
    let proof least :=
      modus aequans (SignedBin.order.increment.specification (W.to_b_signed W.Max) &s), &above.
    leibniz W.maximum.specification in &least.
    match &least with | same | smaller end.
    + leibniz <- &same, &folded in |- *.
      ipso (disjoin (refl (SignedBin.Negative W.half)), _).
    + let proof lowered :=
        SignedBin.order.subtraction.left.monotonicity (SignedBin.Positive W.modulus) (SignedBin.Positive W.half) &s
          &smaller.
      leibniz &folded in &lowered.
      ipso (disjoin _, &lowered).
  }
  (* [(modulus + half) - modulus] is [half]. *)
  lemma restored : (SignedBin.Positive W.beyond - SignedBin.Positive W.modulus = SignedBin.Positive W.half)%b_signed.
  {
    leibniz
      W.beyond.specification,
      (SignedBin.addition.commutativity (SignedBin.Positive W.modulus) (SignedBin.Positive W.half))
      in |- *.
    ipso (SignedBin.subtraction.inversion.addition (SignedBin.Positive W.half) (SignedBin.Positive W.modulus)).
  }
  lemma high : (s - SignedBin.Positive W.modulus <= W.to_b_signed W.Max)%b_signed.
  {
    let proof lowered :=
      SignedBin.order.subtraction.left.monotonicity (SignedBin.Positive W.modulus) &s (SignedBin.Positive W.beyond)
        &below.
    leibniz &restored, <- W.maximum.specification in &lowered.
    ipso (modus aequans
            (SignedBin.order.discreteness (&s - SignedBin.Positive W.modulus)%b_signed (W.to_b_signed W.Max)), &lowered).
  }
  leibniz &shifted in |- *.
  ipso (wrapping.retraction (&s - SignedBin.Positive W.modulus)%b_signed (conjoin &low, &high)).
Qed.

(* wrapping.lower *)
Theorem lower
  : forall (s : SignedBin) .
      (s < SignedBin.Negative W.half /\ SignedBin.Negative W.beyond < s)%b_signed
      -> W.to_b_signed (W.from_b_signed s) = (s + SignedBin.Positive W.modulus)%b_signed.
Proof.
  intros s h.
  match &h with | below above end.
  lemma shifted : W.from_b_signed s = W.from_b_signed (s + SignedBin.Positive W.modulus)%b_signed.
  {
    leibniz (wrapping.additivity &s (SignedBin.Positive W.modulus)), W.modulus.wrapping in |- *.
    match (W.addition.identity (W.from_b_signed &s)) with | _ right_identity end.
    ipso (symm &right_identity).
  }
  (* [- (modulus + half) + modulus] regrouped. *)
  lemma folded
    : (SignedBin.negate (SignedBin.Positive W.beyond) + SignedBin.Positive W.modulus = SignedBin.Negative W.half)%b_signed.
  {
    leibniz
      W.beyond.specification,
      (SignedBin.negation.additivity (SignedBin.Positive W.modulus) (SignedBin.Positive W.half)),
      (SignedBin.addition.commutativity (SignedBin.negate (SignedBin.Positive W.modulus))
         (SignedBin.negate (SignedBin.Positive W.half))),
      (SignedBin.addition.associativity (SignedBin.negate (SignedBin.Positive W.half))
         (SignedBin.negate (SignedBin.Positive W.modulus)) (SignedBin.Positive W.modulus)),
      (SignedBin.addition.left.inverse (SignedBin.Positive W.modulus)),
      (SignedBin.addition.right.identity (SignedBin.negate (SignedBin.Positive W.half)))
      in |- *.
    ipso (refl (SignedBin.Negative W.half)).
  }
  lemma low : (SignedBin.Negative W.half <= s + SignedBin.Positive W.modulus)%b_signed.
  {
    let proof raised
      : (SignedBin.Positive W.modulus + SignedBin.negate (SignedBin.Positive W.beyond)
         < SignedBin.Positive W.modulus + s)%b_signed
      := SignedBin.addition.order.strict.monotonicity (SignedBin.Positive W.modulus) (SignedBin.Negative W.beyond)
           &s &above.
    leibniz
      (SignedBin.addition.commutativity (SignedBin.Positive W.modulus) (SignedBin.negate (SignedBin.Positive W.beyond))),
      (SignedBin.addition.commutativity (SignedBin.Positive W.modulus) &s),
      &folded
      in &raised.
    ipso (disjoin _, &raised).
  }
  (* [- half + (half + half)] regrouped. *)
  lemma unfolded
    : (SignedBin.negate (SignedBin.Positive W.half) + SignedBin.Positive W.modulus = SignedBin.Positive W.half)%b_signed.
  {
    leibniz
      W.modulus.specification,
      <- (SignedBin.addition.associativity (SignedBin.negate (SignedBin.Positive W.half)) (SignedBin.Positive W.half)
            (SignedBin.Positive W.half)),
      (SignedBin.addition.left.inverse (SignedBin.Positive W.half)),
      (SignedBin.addition.left.identity (SignedBin.Positive W.half))
      in |- *.
    quod idem est.
  }
  lemma high : (s + SignedBin.Positive W.modulus <= W.to_b_signed W.Max)%b_signed.
  {
    let proof raised
      : (SignedBin.Positive W.modulus + s
         < SignedBin.Positive W.modulus + SignedBin.negate (SignedBin.Positive W.half))%b_signed
      := SignedBin.addition.order.strict.monotonicity (SignedBin.Positive W.modulus) &s (SignedBin.Negative W.half)
           &below.
    leibniz
      (SignedBin.addition.commutativity (SignedBin.Positive W.modulus) &s),
      (SignedBin.addition.commutativity (SignedBin.Positive W.modulus) (SignedBin.negate (SignedBin.Positive W.half))),
      &unfolded,
      <- W.maximum.specification
      in &raised.
    ipso (modus aequans
            (SignedBin.order.discreteness (&s + SignedBin.Positive W.modulus)%b_signed (W.to_b_signed W.Max)), &raised).
  }
  leibniz &shifted in |- *.
  ipso (wrapping.retraction (&s + SignedBin.Positive W.modulus)%b_signed (conjoin &low, &high)).
Qed.

End wrapping. (* wrapping *)

Module overflow. (* overflow *)

Module addition. (* overflow.addition *)

(* Clear flag: the sum is [W.to_b_signed (W.add x y)], which is in range. Sum in
 * range: [W.add x y] is [W.from_b_signed] of the [SignedBin] sum, so its reading is that
 * sum; a set flag would mean two operands of one sign and a result of the
 * other, which that equation rules out.
 *)
(* overflow.addition.specification *)
Theorem specification
  : forall (x : W.T) (y : W.T) .
      (pi_1 (W.add_with_overflow x y))%product = 0%bit
      <-> (SignedBin.Negative W.half <= W.to_b_signed x + W.to_b_signed y
           /\ W.to_b_signed x + W.to_b_signed y <= W.to_b_signed W.Max)%b_signed.
Proof.
  intros x y.
  divide et impera.
  - intro f.
    leibniz <- (W.conversion.addition &x &y &f) in |- *.
    ipso (bound.range (&x + &y)).
  - intro r.
    lemma same : W.to_b_signed (x + y) = (W.to_b_signed x + W.to_b_signed y)%b_signed.
    {
      leibniz (wrapping.summation &x &y) in |- *.
      ipso (wrapping.retraction (W.to_b_signed &x + W.to_b_signed &y)%b_signed &r).
    }
    match ((pi_1 (W.add_with_overflow &x &y))%product) with | Zero | One end |- f.
    + quod idem est.
    + leibniz (W.flag.addition.specification &x &y) in &f.
      match (W.sign_bit &x) with | Zero | One end |- sx;
        match (W.sign_bit &y) with | Zero | One end |- sy;
        match (W.sign_bit (&x + &y)) with | Zero | One end |- sxy.
      * simpl in &f.
        ex &f quodlibet.
      * (* Two operands of sign 0 and a negative sum. *)
        let proof cx := sign.clear &x &sx.
        let proof cy := sign.clear &y &sy.
        let proof negative := sign.set (&x + &y) &sxy.
        leibniz &same in &negative.
        let proof widened := SignedBin.addition.order.monotonicity (W.to_b_signed &x) 0%b_signed (W.to_b_signed &y) &cy.
        leibniz (SignedBin.addition.right.identity (W.to_b_signed &x)) in &widened.
        let proof nonnegative :=
          @Comparable.order.transitivity _ SignedBin.compare SignedBin.LessThan _ 0%b_signed (W.to_b_signed &x)
            (W.to_b_signed &x + W.to_b_signed &y)%b_signed &cx &widened.
        ex (SignedBin.order.strict.irreflexivity 0%b_signed
              (Comparable.order.mixed.left.transitivity &nonnegative &negative))
          quodlibet.
      * simpl in &f.
        ex &f quodlibet.
      * simpl in &f.
        ex &f quodlibet.
      * simpl in &f.
        ex &f quodlibet.
      * simpl in &f.
        ex &f quodlibet.
      * (* Two negative operands and a sum of sign 0. *)
        let proof nx := sign.set &x &sx.
        let proof ny := sign.set &y &sy.
        let proof nonnegative := sign.clear (&x + &y) &sxy.
        leibniz &same in &nonnegative.
        let proof negative :=
          SignedBin.addition.order.mixed.monotonicity (W.to_b_signed &x) (W.to_b_signed &y) 0%b_signed 0%b_signed
            (Comparable.order.strict.weakening (W.to_b_signed &x) 0%b_signed &nx) &ny.
        ex (SignedBin.order.strict.irreflexivity 0%b_signed
              (Comparable.order.mixed.left.transitivity &nonnegative &negative))
          quodlibet.
      * simpl in &f.
        ex &f quodlibet.
Qed.

(* A set flag puts the [SignedBin] sum out of range, and the sum of two readings lies
 * between twice the least and twice the greatest, so it is past one end by
 * less than the modulus and [wrapping.upper] or [wrapping.lower] brings it
 * back.
 *)
(* overflow.addition.wrap *)
Theorem wrap
  : forall (x : W.T) (y : W.T) .
      (pi_1 (W.add_with_overflow x y))%product = 1%bit
      -> W.to_b_signed (x + y) = (W.to_b_signed x + W.to_b_signed y - SignedBin.Positive W.modulus)%b_signed
         \/ W.to_b_signed (x + y) = (W.to_b_signed x + W.to_b_signed y + SignedBin.Positive W.modulus)%b_signed.
Proof.
  intros x y f.
  lemma outside
    : ~ ((SignedBin.Negative W.half <= W.to_b_signed x + W.to_b_signed y
          /\ W.to_b_signed x + W.to_b_signed y <= W.to_b_signed W.Max)%b_signed).
  {
    simpl (~ _) in |- *.
    intro r.
    let proof c := modus aequans (overflow.addition.specification &x &y), &r.
    leibniz &f in &c.
    ex &c quodlibet.
  }
  match (bound.range &x) with | low_x high_x end.
  match (bound.range &y) with | low_y high_y end.
  let proof top :=
    SignedBin.addition.order.accumulation (W.to_b_signed &x) (W.to_b_signed &y) (W.to_b_signed W.Max) (W.to_b_signed W.Max)
      &high_x &high_y.
  let proof bottom :=
    SignedBin.addition.order.accumulation (SignedBin.Negative W.half) (SignedBin.Negative W.half) (W.to_b_signed &x)
      (W.to_b_signed &y)
      &low_x &low_y.
  leibniz (wrapping.summation &x &y) in |- *.
  (* [to_b_signed Max] is below [half], so twice it is below [modulus], which is below
   * [beyond].
   *)
  let proof max_below : (W.to_b_signed W.Max < W.to_b_signed W.Max + 1)%b_signed
    := SignedBin.order.increment.extensivity (W.to_b_signed W.Max).
  leibniz W.maximum.specification in &max_below.
  lemma max_at_most : (W.to_b_signed W.Max <= SignedBin.Positive W.half)%b_signed.
  {
    ipso (disjoin _, &max_below).
  }
  lemma modulus_below : (SignedBin.Positive W.modulus < SignedBin.Positive W.beyond)%b_signed.
  {
    simpl SignedBin.LessThan in |- *.
    exists W.half.
    ipso (symm W.beyond.specification).
  }
  lemma sum_below : (W.to_b_signed W.Max + W.to_b_signed W.Max < SignedBin.Positive W.beyond)%b_signed.
  {
    let proof doubled :=
      SignedBin.addition.order.mixed.monotonicity (W.to_b_signed W.Max) (W.to_b_signed W.Max)
        (SignedBin.Positive W.half) (SignedBin.Positive W.half) &max_at_most &max_below.
    leibniz <- W.modulus.specification in &doubled.
    ipso (SignedBin.order.strict.transitivity &doubled &modulus_below).
  }
  lemma sum_above : (SignedBin.Negative W.beyond < SignedBin.Negative W.half + SignedBin.Negative W.half)%b_signed.
  {
    let proof reversed :=
      modus aequans
        (SignedBin.order.negation.strict.reversal (SignedBin.Positive W.modulus) (SignedBin.Positive W.beyond)),
        &modulus_below.
    leibniz
      W.modulus.specification,
      (SignedBin.negation.additivity (SignedBin.Positive W.half) (SignedBin.Positive W.half))
      in &reversed.
    ipso &reversed.
  }
  match (Comparable.order.strict.trichotomy (W.to_b_signed W.Max) (W.to_b_signed &x + W.to_b_signed &y)%b_signed)
    with | above | rest end.
  - let proof below := Comparable.order.mixed.left.transitivity &top &sum_below.
    ipso (disjoin (wrapping.upper (W.to_b_signed &x + W.to_b_signed &y)%b_signed (conjoin &above, &below)), _).
  - match &rest with | same | under end.
    + lemma inside
        : (SignedBin.Negative W.half <= W.to_b_signed x + W.to_b_signed y
           /\ W.to_b_signed x + W.to_b_signed y <= W.to_b_signed W.Max)%b_signed.
      {
        leibniz <- &same in |- *.
        ipso (conjoin ordered, (disjoin (refl (W.to_b_signed W.Max)), _)).
      }
      ex (&outside &inside) quodlibet.
    + match (Comparable.order.strict.trichotomy (W.to_b_signed &x + W.to_b_signed &y)%b_signed (SignedBin.Negative W.half))
        with | beneath | remainder end.
      * let proof above := Comparable.order.mixed.right.transitivity &sum_above &bottom.
        ipso (disjoin _, (wrapping.lower (W.to_b_signed &x + W.to_b_signed &y)%b_signed (conjoin &beneath, &above))).
      * lemma inside
          : (SignedBin.Negative W.half <= W.to_b_signed x + W.to_b_signed y
             /\ W.to_b_signed x + W.to_b_signed y <= W.to_b_signed W.Max)%b_signed.
        {
          lemma low : (SignedBin.Negative W.half <= W.to_b_signed x + W.to_b_signed y)%b_signed.
          {
            match &remainder with | same | over end.
            - leibniz &same in |- *.
              ipso (disjoin (refl (SignedBin.Negative W.half)), _).
            - ipso (disjoin _, &over).
          }
          ipso (conjoin &low, (disjoin _, &under)).
        }
        ex (&outside &inside) quodlibet.
Qed.

(* Two clear flags make both sums exact, and [SignedBin]'s addition keeps the order. *)
(* overflow.addition.monotonicity *)
Theorem monotonicity
  : forall (x : W.T) (y : W.T) (z : W.T) .
      (pi_1 (W.add_with_overflow x y))%product = 0%bit
      -> (pi_1 (W.add_with_overflow x z))%product = 0%bit
      -> y < z -> x + y < x + z.
Proof.
  intros x y z fy fz h.
  let proof g := modus aequans (W.order.strict.specification &y &z), &h.
  let proof s :=
    SignedBin.addition.order.strict.monotonicity (W.to_b_signed &x) (W.to_b_signed &y) (W.to_b_signed &z) &g.
  leibniz <- (W.conversion.addition &x &y &fy), <- (W.conversion.addition &x &z &fz) in &s.
  ipso (modus aequans (W.order.strict.specification (&x + &y) (&x + &z)), &s).
Qed.

End addition. (* overflow.addition *)

Module subtraction. (* overflow.subtraction *)

(* Difference in range: [W.sub x y] is [W.from_b_signed] of the [SignedBin] difference,
 * so it is exact, and a set flag, which needs operands of different signs and
 * a result with the sign of [y], is ruled out by the signs. Difference out of
 * range: it is past one end by less than the modulus, the result wraps to the
 * other sign, and the operands' signs are forced, which sets the flag.
 *)
(* overflow.subtraction.specification *)
Theorem specification
  : forall (x : W.T) (y : W.T) .
      (pi_1 (W.sub_with_overflow x y))%product = 0%bit
      <-> (SignedBin.Negative W.half <= W.to_b_signed x - W.to_b_signed y
           /\ W.to_b_signed x - W.to_b_signed y <= W.to_b_signed W.Max)%b_signed.
Proof.
  intros x y.
  match (bound.range &x) with | low_x high_x end.
  match (bound.range &y) with | low_y high_y end.
  lemma below_y : (SignedBin.negate (W.to_b_signed y) <= SignedBin.Positive W.half)%b_signed.
  {
    ipso (SignedBin.order.negation.reversal (SignedBin.Negative W.half) (W.to_b_signed &y) &low_y).
  }
  let proof above_y := SignedBin.order.negation.reversal (W.to_b_signed &y) (W.to_b_signed W.Max) &high_y.
  (* The ends of the range against [half], [modulus] and [beyond], from
   * [to_b_signed Max < half], [modulus = half + half] and [beyond = modulus + half].
   *)
  let proof max_below : (W.to_b_signed W.Max < W.to_b_signed W.Max + 1)%b_signed
    := SignedBin.order.increment.extensivity (W.to_b_signed W.Max).
  leibniz W.maximum.specification in &max_below.
  lemma modulus_below : (SignedBin.Positive W.modulus < SignedBin.Positive W.beyond)%b_signed.
  {
    simpl SignedBin.LessThan in |- *.
    exists W.half.
    ipso (symm W.beyond.specification).
  }
  lemma negated_below : (SignedBin.Negative W.half < SignedBin.negate (W.to_b_signed W.Max))%b_signed.
  {
    ipso (modus aequans
            (SignedBin.order.negation.strict.reversal (W.to_b_signed W.Max) (SignedBin.Positive W.half)),
            &max_below).
  }
  lemma sum_below : (W.to_b_signed W.Max + SignedBin.Positive W.half < SignedBin.Positive W.beyond)%b_signed.
  {
    let proof raised :=
      SignedBin.addition.order.strict.monotonicity (SignedBin.Positive W.half) (W.to_b_signed W.Max)
        (SignedBin.Positive W.half) &max_below.
    leibniz
      (SignedBin.addition.commutativity (SignedBin.Positive W.half) (W.to_b_signed W.Max)),
      <- W.modulus.specification
      in &raised.
    ipso (SignedBin.order.strict.transitivity &raised &modulus_below).
  }
  lemma sum_successor
    : ((W.to_b_signed W.Max + SignedBin.Positive W.half) + 1 = SignedBin.Positive W.modulus)%b_signed.
  {
    leibniz
      (SignedBin.addition.associativity (W.to_b_signed W.Max) (SignedBin.Positive W.half) 1%b_signed),
      (SignedBin.addition.commutativity (SignedBin.Positive W.half) 1%b_signed),
      <- (SignedBin.addition.associativity (W.to_b_signed W.Max) 1%b_signed (SignedBin.Positive W.half)),
      W.maximum.specification,
      <- W.modulus.specification
      in |- *.
    quod idem est.
  }
  lemma halves_above
    : (SignedBin.negate (SignedBin.Positive W.modulus) < SignedBin.Negative W.half + SignedBin.negate (W.to_b_signed W.Max))%b_signed.
  {
    leibniz
      W.modulus.specification,
      (SignedBin.negation.additivity (SignedBin.Positive W.half) (SignedBin.Positive W.half))
      in |- *.
    ipso (SignedBin.addition.order.strict.monotonicity (SignedBin.Negative W.half) (SignedBin.Negative W.half)
            (SignedBin.negate (W.to_b_signed W.Max)) &negated_below).
  }
  lemma beyond_above
    : (SignedBin.Negative W.beyond < SignedBin.Negative W.half + SignedBin.negate (W.to_b_signed W.Max))%b_signed.
  {
    let proof reversed :=
      modus aequans
        (SignedBin.order.negation.strict.reversal (SignedBin.Positive W.modulus) (SignedBin.Positive W.beyond)),
        &modulus_below.
    ipso (SignedBin.order.strict.transitivity &reversed &halves_above).
  }
  divide et impera.
  - intro f.
    lemma top : (W.to_b_signed x - W.to_b_signed y <= W.to_b_signed W.Max + SignedBin.Positive W.half)%b_signed.
    {
      ipso (SignedBin.addition.order.accumulation
              (W.to_b_signed &x) (SignedBin.negate (W.to_b_signed &y)) (W.to_b_signed W.Max) (SignedBin.Positive W.half)
              &high_x &below_y).
    }
    lemma bottom
      : (SignedBin.Negative W.half + SignedBin.negate (W.to_b_signed W.Max) <= W.to_b_signed x - W.to_b_signed y)%b_signed.
    {
      ipso (SignedBin.addition.order.accumulation
              (SignedBin.Negative W.half) (SignedBin.negate (W.to_b_signed W.Max)) (W.to_b_signed &x)
              (SignedBin.negate (W.to_b_signed &y)) &low_x &above_y).
    }
    match (Comparable.order.strict.trichotomy (W.to_b_signed W.Max) (W.to_b_signed &x - W.to_b_signed &y)%b_signed)
      with | above | rest end.
    + (* Past the greatest: the result wraps below 0, [x] is nonnegative, [y]
       * negative.
       *)
      let proof below := Comparable.order.mixed.left.transitivity &top &sum_below.
      lemma wrapped
        : W.to_b_signed (x - y) = (W.to_b_signed x - W.to_b_signed y - SignedBin.Positive W.modulus)%b_signed.
      {
        leibniz (wrapping.difference &x &y) in |- *.
        ipso (wrapping.upper (W.to_b_signed &x - W.to_b_signed &y)%b_signed (conjoin &above, &below)).
      }
      lemma negative : (W.to_b_signed (x - y) < 0)%b_signed.
      {
        let proof under :=
          modus aequans
            (SignedBin.order.discreteness (W.to_b_signed &x - W.to_b_signed &y)%b_signed
               (W.to_b_signed W.Max + SignedBin.Positive W.half)%b_signed),
            &top.
        leibniz &sum_successor in &under.
        leibniz &wrapped in |- *.
        let proof lowered :=
          SignedBin.order.subtraction.left.monotonicity (SignedBin.Positive W.modulus)
            (W.to_b_signed &x - W.to_b_signed &y)%b_signed (SignedBin.Positive W.modulus) &under.
        leibniz
          (SignedBin.subtraction.specification (SignedBin.Positive W.modulus) (SignedBin.Positive W.modulus)),
          (SignedBin.addition.right.inverse (SignedBin.Positive W.modulus))
          in &lowered.
        ipso &lowered.
      }
      match (W.sign_bit (&x - &y)) with | Zero | One end |- sr.
      * ex (SignedBin.order.strict.irreflexivity 0%b_signed
              (Comparable.order.mixed.left.transitivity
                 (sign.clear (&x - &y) &sr) &negative))
          quodlibet.
      * match (W.sign_bit &x) with | Zero | One end |- sx.
        -- match (W.sign_bit &y) with | Zero | One end |- sy.
           ++ let proof shrunk :=
                SignedBin.addition.order.monotonicity (W.to_b_signed &x) (SignedBin.negate (W.to_b_signed &y)) 0%b_signed
                  (SignedBin.order.negation.reversal 0%b_signed (W.to_b_signed &y) (sign.clear &y &sy)).
              leibniz (SignedBin.addition.right.identity (W.to_b_signed &x)) in &shrunk.
              lemma small : (W.to_b_signed x - W.to_b_signed y <= W.to_b_signed W.Max)%b_signed.
              {
                ipso (@Comparable.order.transitivity _ SignedBin.compare SignedBin.LessThan _
                        (W.to_b_signed &x - W.to_b_signed &y)%b_signed (W.to_b_signed &x) (W.to_b_signed W.Max)
                        &shrunk &high_x).
              }
              ex (SignedBin.order.strict.irreflexivity (W.to_b_signed W.Max)
                    (Comparable.order.mixed.right.transitivity &above &small))
                quodlibet.
           ++ leibniz (W.flag.subtraction.specification &x &y), &sx, &sy, &sr in &f.
              simpl in &f.
              ex &f quodlibet.
        -- let proof shrunk :=
             SignedBin.addition.order.mixed.monotonicity
               (SignedBin.negate (W.to_b_signed &y)) (W.to_b_signed &x) (SignedBin.Positive W.half) 0%b_signed
               &below_y (sign.set &x &sx).
           leibniz
             (SignedBin.addition.commutativity (SignedBin.negate (W.to_b_signed &y)) (W.to_b_signed &x)),
             (SignedBin.addition.right.identity (SignedBin.Positive W.half)),
             <- W.maximum.specification
             in &shrunk.
           lemma small : (W.to_b_signed x - W.to_b_signed y <= W.to_b_signed W.Max)%b_signed.
           {
             ipso (modus aequans
                     (SignedBin.order.discreteness (W.to_b_signed &x - W.to_b_signed &y)%b_signed (W.to_b_signed W.Max)),
                     &shrunk).
           }
           ex (SignedBin.order.strict.irreflexivity (W.to_b_signed W.Max)
                 (Comparable.order.mixed.right.transitivity &above &small))
             quodlibet.
    + match &rest with | same | under end.
      * lemma inside
          : (SignedBin.Negative W.half <= W.to_b_signed x - W.to_b_signed y
             /\ W.to_b_signed x - W.to_b_signed y <= W.to_b_signed W.Max)%b_signed.
        {
          leibniz <- &same in |- *.
          ipso (conjoin ordered, (disjoin (refl (W.to_b_signed W.Max)), _)).
        }
        ipso &inside.
      * match (Comparable.order.strict.trichotomy (W.to_b_signed &x - W.to_b_signed &y)%b_signed
                 (SignedBin.Negative W.half))
          with | beneath | remainder end.
        -- (* Below the least: the result wraps above 0, [x] is negative, [y]
            * nonnegative.
            *)
           let proof above := Comparable.order.mixed.right.transitivity &beyond_above &bottom.
           lemma wrapped
             : W.to_b_signed (x - y) = (W.to_b_signed x - W.to_b_signed y + SignedBin.Positive W.modulus)%b_signed.
           {
             leibniz (wrapping.difference &x &y) in |- *.
             ipso (wrapping.lower (W.to_b_signed &x - W.to_b_signed &y)%b_signed (conjoin &beneath, &above)).
           }
           lemma nonnegative : (0 <= W.to_b_signed (x - y))%b_signed.
           {
             let proof over := Comparable.order.mixed.right.transitivity &halves_above &bottom.
             leibniz &wrapped in |- *.
             let proof raised :=
               SignedBin.addition.order.strict.monotonicity (SignedBin.Positive W.modulus)
                 (SignedBin.negate (SignedBin.Positive W.modulus)) (W.to_b_signed &x - W.to_b_signed &y)%b_signed &over.
             leibniz
               (SignedBin.addition.right.inverse (SignedBin.Positive W.modulus)),
               (SignedBin.addition.commutativity (SignedBin.Positive W.modulus) (W.to_b_signed &x - W.to_b_signed &y)%b_signed)
               in &raised.
             ipso (disjoin _, &raised).
           }
           match (W.sign_bit (&x - &y)) with | Zero | One end |- sr.
           ++ match (W.sign_bit &x) with | Zero | One end |- sx.
              ** let proof grown :=
                   SignedBin.addition.order.accumulation 0%b_signed (SignedBin.negate (W.to_b_signed W.Max)) (W.to_b_signed &x)
                     (SignedBin.negate (W.to_b_signed &y)) (sign.clear &x &sx) &above_y.
                 leibniz (SignedBin.addition.left.identity (SignedBin.negate (W.to_b_signed W.Max))) in &grown.
                 lemma large : (SignedBin.negate (W.to_b_signed W.Max) <= W.to_b_signed x - W.to_b_signed y)%b_signed.
                 {
                   ipso &grown.
                 }
                 ex (SignedBin.order.strict.irreflexivity (SignedBin.Negative W.half)
                       (SignedBin.order.strict.transitivity &negated_below
                          (Comparable.order.mixed.left.transitivity &large &beneath)))
                   quodlibet.
              ** match (W.sign_bit &y) with | Zero | One end |- sy.
                 --- leibniz (W.flag.subtraction.specification &x &y), &sx, &sy, &sr in &f.
                     simpl in &f.
                     ex &f quodlibet.
                 --- lemma positive : (0 < SignedBin.negate (W.to_b_signed y))%b_signed.
                     {
                       ipso (modus aequans (SignedBin.order.negation.strict.reversal (W.to_b_signed &y) 0%b_signed),
                             (sign.set &y &sy)).
                     }
                     let proof grown :=
                       SignedBin.addition.order.strict.monotonicity (W.to_b_signed &x) 0%b_signed
                         (SignedBin.negate (W.to_b_signed &y)) &positive.
                     leibniz (SignedBin.addition.right.identity (W.to_b_signed &x)) in &grown.
                     lemma large : (SignedBin.Negative W.half < W.to_b_signed x - W.to_b_signed y)%b_signed.
                     {
                       ipso (Comparable.order.mixed.left.transitivity &low_x &grown).
                     }
                     ex (SignedBin.order.strict.irreflexivity (SignedBin.Negative W.half)
                           (SignedBin.order.strict.transitivity &large &beneath))
                       quodlibet.
           ++ ex (SignedBin.order.strict.irreflexivity 0%b_signed
                   (Comparable.order.mixed.left.transitivity &nonnegative
                      (sign.set (&x - &y) &sr)))
                quodlibet.
        -- lemma inside
             : (SignedBin.Negative W.half <= W.to_b_signed x - W.to_b_signed y
                /\ W.to_b_signed x - W.to_b_signed y <= W.to_b_signed W.Max)%b_signed.
           {
             lemma low : (SignedBin.Negative W.half <= W.to_b_signed x - W.to_b_signed y)%b_signed.
             {
               match &remainder with | same | over end.
               ++ leibniz &same in |- *.
                  ipso (disjoin (refl (SignedBin.Negative W.half)), _).
               ++ ipso (disjoin _, &over).
             }
             ipso (conjoin &low, (disjoin _, &under)).
           }
           ipso &inside.
  - intro r.
    lemma same : W.to_b_signed (x - y) = (W.to_b_signed x - W.to_b_signed y)%b_signed.
    {
      leibniz (wrapping.difference &x &y) in |- *.
      ipso (wrapping.retraction (W.to_b_signed &x - W.to_b_signed &y)%b_signed &r).
    }
    match ((pi_1 (W.sub_with_overflow &x &y))%product) with | Zero | One end |- f.
    + quod idem est.
    + leibniz (W.flag.subtraction.specification &x &y) in &f.
      match (W.sign_bit &x) with | Zero | One end |- sx;
        match (W.sign_bit &y) with | Zero | One end |- sy;
        match (W.sign_bit (&x - &y)) with | Zero | One end |- sr.
      * simpl in &f.
        ex &f quodlibet.
      * simpl in &f.
        ex &f quodlibet.
      * simpl in &f.
        ex &f quodlibet.
      * (* [x] nonnegative, [y] negative, a negative difference. *)
        let proof negative := sign.set (&x - &y) &sr.
        leibniz &same in &negative.
        lemma positive : (0 < SignedBin.negate (W.to_b_signed y))%b_signed.
        {
          ipso (modus aequans (SignedBin.order.negation.strict.reversal (W.to_b_signed &y) 0%b_signed),
                (sign.set &y &sy)).
        }
        lemma grown : (0 < W.to_b_signed x - W.to_b_signed y)%b_signed.
        {
          ipso (SignedBin.addition.order.mixed.monotonicity
                  0%b_signed 0%b_signed (W.to_b_signed &x) (SignedBin.negate (W.to_b_signed &y))
                  (sign.clear &x &sx) &positive).
        }
        ex (SignedBin.order.strict.irreflexivity 0%b_signed (SignedBin.order.strict.transitivity &grown &negative))
          quodlibet.
      * (* [x] negative, [y] nonnegative, a nonnegative difference. *)
        let proof nonnegative := sign.clear (&x - &y) &sr.
        leibniz &same in &nonnegative.
        let proof shrunk :=
          SignedBin.addition.order.mixed.monotonicity (SignedBin.negate (W.to_b_signed &y)) (W.to_b_signed &x) 0%b_signed 0%b_signed
            (SignedBin.order.negation.reversal 0%b_signed (W.to_b_signed &y) (sign.clear &y &sy)) (sign.set &x &sx).
        leibniz (SignedBin.addition.commutativity (SignedBin.negate (W.to_b_signed &y)) (W.to_b_signed &x)) in &shrunk.
        lemma negative : (W.to_b_signed x - W.to_b_signed y < 0)%b_signed.
        {
          ipso &shrunk.
        }
        ex (SignedBin.order.strict.irreflexivity 0%b_signed
              (Comparable.order.mixed.left.transitivity &nonnegative &negative))
          quodlibet.
      * simpl in &f.
        ex &f quodlibet.
      * simpl in &f.
        ex &f quodlibet.
      * simpl in &f.
        ex &f quodlibet.
Qed.

(* A clear flag puts the difference in range, where it is exact. *)
(* overflow.subtraction.exactness *)
Theorem exactness
  : forall (x : W.T) (y : W.T) .
      (pi_1 (W.sub_with_overflow x y))%product = 0%bit
      -> W.to_b_signed (x - y) = (W.to_b_signed x - W.to_b_signed y)%b_signed.
Proof.
  intros x y f.
  leibniz (wrapping.difference &x &y) in |- *.
  ipso (wrapping.retraction (W.to_b_signed &x - W.to_b_signed &y)%b_signed
          (modus aequans (overflow.subtraction.specification &x &y), &f)).
Qed.

Module left. (* overflow.subtraction.left *)

(* overflow.subtraction.left.monotonicity *)
Theorem monotonicity
  : forall (x : W.T) (y : W.T) (z : W.T) .
      (pi_1 (W.sub_with_overflow y x))%product = 0%bit
      -> (pi_1 (W.sub_with_overflow z x))%product = 0%bit
      -> y < z -> y - x < z - x.
Proof.
  intros x y z fy fz h.
  let proof g := modus aequans (W.order.strict.specification &y &z), &h.
  let proof s :=
    SignedBin.order.subtraction.left.monotonicity (W.to_b_signed &x) (W.to_b_signed &y) (W.to_b_signed &z) &g.
  leibniz
    <- (overflow.subtraction.exactness &y &x &fy),
    <- (overflow.subtraction.exactness &z &x &fz)
    in &s.
  ipso (modus aequans (W.order.strict.specification (&y - &x) (&z - &x)), &s).
Qed.

End left. (* overflow.subtraction.left *)

Module right. (* overflow.subtraction.right *)

(* overflow.subtraction.right.antitonicity *)
Theorem antitonicity
  : forall (x : W.T) (y : W.T) (z : W.T) .
      (pi_1 (W.sub_with_overflow x z))%product = 0%bit
      -> (pi_1 (W.sub_with_overflow x y))%product = 0%bit
      -> y < z -> x - z < x - y.
Proof.
  intros x y z fz fy h.
  let proof g := modus aequans (W.order.strict.specification &y &z), &h.
  let proof s :=
    SignedBin.order.subtraction.right.antitonicity (W.to_b_signed &x) (W.to_b_signed &y) (W.to_b_signed &z) &g.
  leibniz
    <- (overflow.subtraction.exactness &x &z &fz),
    <- (overflow.subtraction.exactness &x &y &fy)
    in &s.
  ipso (modus aequans (W.order.strict.specification (&x - &z) (&x - &y)), &s).
Qed.

End right. (* overflow.subtraction.right *)

End subtraction. (* overflow.subtraction *)

Module multiplication. (* overflow.multiplication *)

(* The flag reads [SignedBin.compare] of the product against both ends of the range:
 * below the least or above the greatest sets it, anything between clears it.
 *)
(* overflow.multiplication.specification *)
Theorem specification
  : forall (x : W.T) (y : W.T) .
      (pi_1 (W.mul_with_overflow x y))%product = 0%bit
      <-> (SignedBin.Negative W.half <= W.to_b_signed x * W.to_b_signed y
           /\ W.to_b_signed x * W.to_b_signed y <= W.to_b_signed W.Max)%b_signed.
Proof.
  intros x y.
  leibniz (W.flag.multiplication.specification &x &y), W.minimum.specification in |- *.
  let proof low :=
    SignedBin.comparison.specification (W.to_b_signed &x * W.to_b_signed &y)%b_signed (SignedBin.Negative W.half).
  match &low with | below equal end.
  let proof above :=
    Comparable.comparison.strict.transposition.specification
      (W.to_b_signed &x * W.to_b_signed &y)%b_signed (SignedBin.Negative W.half).
  let proof high := SignedBin.comparison.specification (W.to_b_signed &x * W.to_b_signed &y)%b_signed (W.to_b_signed W.Max).
  match &high with | under top end.
  let proof past :=
    Comparable.comparison.strict.transposition.specification
      (W.to_b_signed &x * W.to_b_signed &y)%b_signed (W.to_b_signed W.Max).
  match (SignedBin.compare (W.to_b_signed &x * W.to_b_signed &y)%b_signed (SignedBin.Negative W.half))
    with | Lt | Eq | Gt end |- c.
  - divide et impera.
    + intro e.
      simpl in &e.
      ex &e quodlibet.
    + intro r.
      match &r with | l _ end.
      let proof s := modus aequans &below, (refl Comparison.Lt).
      ex (SignedBin.order.strict.irreflexivity (SignedBin.Negative W.half)
            (Comparable.order.mixed.left.transitivity &l &s))
        quodlibet.
  - divide et impera.
    + intro e.
      let proof q := modus aequans &equal, (refl Comparison.Eq).
      leibniz &q in |- *.
      ipso (conjoin (disjoin (refl (SignedBin.Negative W.half)), _), ordered).
    + intro r.
      ipso (refl 0%bit).
  - let proof g := modus aequans &above, (refl Comparison.Gt).
    match (SignedBin.compare (W.to_b_signed &x * W.to_b_signed &y)%b_signed (W.to_b_signed W.Max))
      with | Lt | Eq | Gt end |- d.
    + divide et impera.
      * intro e.
        ipso (conjoin (disjoin _, &g), (disjoin _, (modus aequans &under, (refl Comparison.Lt)))).
      * intro r.
        ipso (refl 0%bit).
    + divide et impera.
      * intro e.
        ipso (conjoin (disjoin _, &g), (disjoin (modus aequans &top, (refl Comparison.Eq)), _)).
      * intro r.
        ipso (refl 0%bit).
    + divide et impera.
      * intro e.
        simpl in &e.
        ex &e quodlibet.
      * intro r.
        match &r with | _ h end.
        let proof m := modus aequans &past, (refl Comparison.Gt).
        ex (SignedBin.order.strict.irreflexivity (W.to_b_signed W.Max)
              (Comparable.order.mixed.right.transitivity &m &h))
          quodlibet.
Qed.

(* A clear flag puts the product in range, where [W.from_b_signed] keeps it. *)
(* overflow.multiplication.exactness *)
Theorem exactness
  : forall (x : W.T) (y : W.T) .
      (pi_1 (W.mul_with_overflow x y))%product = 0%bit
      -> W.to_b_signed (x * y) = (W.to_b_signed x * W.to_b_signed y)%b_signed.
Proof.
  intros x y f.
  let proof r := modus aequans (overflow.multiplication.specification &x &y), &f.
  lemma lifted : &x * &y = W.from_b_signed (W.to_b_signed &x * W.to_b_signed &y)%b_signed.
  {
    leibniz
      (wrapping.multiplicativity (W.to_b_signed &x) (W.to_b_signed &y)),
      (W.conversion.section &x),
      (W.conversion.section &y)
      in |- *.
    quod idem est.
  }
  leibniz &lifted in |- *.
  ipso (wrapping.retraction (W.to_b_signed &x * W.to_b_signed &y)%b_signed &r).
Qed.

(* Two clear flags make both products exact, and a positive factor keeps
 * [SignedBin]'s order.
 *)
(* overflow.multiplication.monotonicity *)
Theorem monotonicity
  : forall (x : W.T) (y : W.T) (z : W.T) .
      (pi_1 (W.mul_with_overflow x y))%product = 0%bit
      -> (pi_1 (W.mul_with_overflow x z))%product = 0%bit
      -> (0 < W.to_b_signed x)%b_signed -> y < z -> x * y < x * z.
Proof.
  intros x y z fy fz hx h.
  let proof g := modus aequans (W.order.strict.specification &y &z), &h.
  let proof s :=
    SignedBin.multiplication.left.order.strict.monotonicity
      (W.to_b_signed &x) (W.to_b_signed &y) (W.to_b_signed &z) &hx &g.
  leibniz
    <- (overflow.multiplication.exactness &x &y &fy),
    <- (overflow.multiplication.exactness &x &z &fz)
    in &s.
  ipso (modus aequans (W.order.strict.specification (&x * &y) (&x * &z)), &s).
Qed.

End multiplication. (* overflow.multiplication *)

End overflow. (* overflow *)

Module negation. (* negation *)

(* [W.add (W.negate x) (W.negate y)] undoes [W.add x y], so it is the
 * inverse of [W.add x y].
 *)
(* negation.additivity *)
Theorem additivity
  : forall (x : W.T) (y : W.T) . (- (x + y)) = - x + - y.
Proof.
  intros x y.
  lemma undone : (x + y) + (- x + - y) = W.Zero.
  {
    leibniz
      (W.addition.commutativity (- &x) (- &y)),
      (W.addition.associativity &x &y (- &y + - &x)),
      <- (W.addition.associativity &y (- &y) (- &x))
      in |- *.
    match (W.addition.inverse &y) with | _ right_y end.
    match (W.addition.identity (- &x)) with | left_x _ end.
    match (W.addition.inverse &x) with | _ right_x end.
    leibniz &right_y, &left_x, &right_x in |- *.
    quod idem est.
  }
  match (W.addition.identity (- (&x + &y))) with | _ plus_zero end.
  leibniz <- &plus_zero, <- &undone in |- *.
  leibniz <- (W.addition.associativity (- (&x + &y)) (&x + &y) (- &x + - &y)) in |- *.
  match (W.addition.inverse (&x + &y)) with | left_inverse _ end.
  match (W.addition.identity (- &x + - &y)) with | left_identity _ end.
  leibniz &left_inverse, &left_identity in |- *.
  quod idem est.
Qed.

(* The least value has no positive counterpart, so its negation wraps to it. *)
(* negation.minimum *)
Theorem minimum : - W.Min = W.Min.
Proof.
  ipso W.minimum.negation.
Qed.

(* Away from [W.Min], the reading lies above the least, so its negation is in
 * range.
 *)
(* negation.exactness *)
Theorem exactness
  : forall (x : W.T) . ~ (x = W.Min) -> W.to_b_signed (- x) = SignedBin.negate (W.to_b_signed x).
Proof.
  intros x h.
  match (bound.range &x) with | low high end.
  lemma above : (SignedBin.Negative W.half < W.to_b_signed x)%b_signed.
  {
    match &low with | same | larger end.
    - lemma e : W.to_b_signed W.Min = W.to_b_signed x.
      {
        leibniz W.minimum.specification in |- *.
        ipso &same.
      }
      ex (&h (symm (injectivity &e))) quodlibet.
    - ipso &larger.
  }
  lemma lifted : - x = W.from_b_signed (SignedBin.negate (W.to_b_signed x)).
  {
    leibniz (wrapping.negation (W.to_b_signed &x)), (W.conversion.section &x) in |- *.
    quod idem est.
  }
  leibniz &lifted in |- *.
  lemma negated_low : (SignedBin.Negative W.half <= SignedBin.negate (W.to_b_signed x))%b_signed.
  {
    let proof max_below : (W.to_b_signed W.Max < W.to_b_signed W.Max + 1)%b_signed
      := SignedBin.order.increment.extensivity (W.to_b_signed W.Max).
    leibniz W.maximum.specification in &max_below.
    lemma negated_below : (SignedBin.Negative W.half < SignedBin.negate (W.to_b_signed W.Max))%b_signed.
    {
      ipso (modus aequans
              (SignedBin.order.negation.strict.reversal (W.to_b_signed W.Max) (SignedBin.Positive W.half)),
              &max_below).
    }
    let proof reversed := SignedBin.order.negation.reversal (W.to_b_signed &x) (W.to_b_signed W.Max) &high.
    ipso (disjoin _, (Comparable.order.mixed.right.transitivity &negated_below &reversed)).
  }
  lemma negated_high : (SignedBin.negate (W.to_b_signed x) <= W.to_b_signed W.Max)%b_signed.
  {
    lemma reversed : (SignedBin.negate (W.to_b_signed x) < SignedBin.Positive W.half)%b_signed.
    {
      ipso (modus aequans
              (SignedBin.order.negation.strict.reversal (SignedBin.Negative W.half) (W.to_b_signed &x)), &above).
    }
    leibniz <- W.maximum.specification in &reversed.
    ipso (modus aequans (SignedBin.order.discreteness (SignedBin.negate (W.to_b_signed &x)) (W.to_b_signed W.Max)),
          &reversed).
  }
  ipso (wrapping.retraction (SignedBin.negate (W.to_b_signed &x)) (conjoin &negated_low, &negated_high)).
Qed.

(* negation.reversal *)
Theorem reversal
  : forall (x : W.T) (y : W.T) .
      ~ (x = W.Min) -> ~ (y = W.Min)
      -> (x < y <-> - y < - x).
Proof.
  intros x y hx hy.
  divide et impera.
  - intro h.
    let proof g := modus aequans (W.order.strict.specification &x &y), &h.
    let proof r :=
      modus aequans (SignedBin.order.negation.strict.reversal (W.to_b_signed &x) (W.to_b_signed &y)), &g.
    leibniz <- (negation.exactness &x &hx), <- (negation.exactness &y &hy) in &r.
    ipso (modus aequans (W.order.strict.specification (- &y) (- &x)), &r).
  - intro h.
    let proof g := modus aequans (W.order.strict.specification (- &y) (- &x)), &h.
    leibniz (negation.exactness &x &hx), (negation.exactness &y &hy) in &g.
    ipso (modus aequans (W.order.strict.specification &x &y),
          (modus aequans (SignedBin.order.negation.strict.reversal (W.to_b_signed &x) (W.to_b_signed &y)), &g)).
Qed.

End negation. (* negation *)

Module increment. (* increment *)

(* Away from [W.Max], the reading is below the greatest, so one more is in
 * range.
 *)
(* increment.exactness *)
Theorem exactness
  : forall (x : W.T) . ~ (x = W.Max) -> W.to_b_signed (x + W.One) = (W.to_b_signed x + 1)%b_signed.
Proof.
  intros x h.
  match (bound.range &x) with | low high end.
  lemma below : (W.to_b_signed x < W.to_b_signed W.Max)%b_signed.
  {
    match &high with | same | smaller end.
    - ex (&h (injectivity &same)) quodlibet.
    - ipso &smaller.
  }
  lemma summed : x + W.One = W.from_b_signed (W.to_b_signed x + 1)%b_signed.
  {
    leibniz (wrapping.summation &x W.One), W.one.specification in |- *.
    quod idem est.
  }
  leibniz &summed in |- *.
  lemma raised_low : (SignedBin.Negative W.half <= W.to_b_signed x + 1)%b_signed.
  {
    ipso (disjoin _, (Comparable.order.mixed.left.transitivity &low
                        (SignedBin.order.increment.extensivity (W.to_b_signed &x)))).
  }
  lemma raised_high : (W.to_b_signed x + 1 <= W.to_b_signed W.Max)%b_signed.
  {
    ipso (modus aequans (SignedBin.order.increment.specification (W.to_b_signed &x) (W.to_b_signed W.Max)), &below).
  }
  ipso (wrapping.retraction (W.to_b_signed &x + 1)%b_signed (conjoin &raised_low, &raised_high)).
Qed.

(* increment.extensivity *)
Theorem extensivity : forall (x : W.T) . ~ (x = W.Max) -> x < x + W.One.
Proof.
  intros x h.
  let proof g := SignedBin.order.increment.extensivity (W.to_b_signed &x).
  leibniz <- (increment.exactness &x &h) in &g.
  ipso (modus aequans (W.order.strict.specification &x (&x + W.One)), &g).
Qed.

(* [x < y] keeps [x] below [W.Max], so [x + 1] is exact and at most [y]. *)
(* increment.specification *)
Theorem specification
  : forall (x : W.T) (y : W.T) . x < y -> x + W.One <= y.
Proof.
  intros x y h.
  let proof g := modus aequans (W.order.strict.specification &x &y), &h.
  lemma below : ~ (x = W.Max).
  {
    simpl (~ _) in |- *.
    intro e.
    leibniz &e in &g.
    match (bound.range &y) with | _ high end.
    ex (SignedBin.order.strict.irreflexivity (W.to_b_signed W.Max)
          (Comparable.order.mixed.right.transitivity &g &high))
      quodlibet.
  }
  match (modus aequans (SignedBin.order.increment.specification (W.to_b_signed &x) (W.to_b_signed &y)), &g)
    with | same | smaller end.
  - lemma e : W.to_b_signed (x + W.One) = W.to_b_signed y.
    {
      leibniz (increment.exactness &x &below) in |- *.
      ipso &same.
    }
    ipso (modus aequans (W.order.specification (&x + W.One) &y), (disjoin (injectivity &e), _)).
  - leibniz <- (increment.exactness &x &below) in &smaller.
    ipso (modus aequans (W.order.specification (&x + W.One) &y),
          (disjoin _, (modus aequans (W.order.strict.specification (&x + W.One) &y), &smaller))).
Qed.

(* increment.sufficiency *)
Theorem sufficiency
  : forall (x : W.T) (y : W.T) .
      ~ (x = W.Max) -> x + W.One <= y -> x < y.
Proof.
  intros x y h k.
  let proof first := increment.extensivity &x &h.
  match (modus aequans (W.order.specification (&x + W.One) &y), &k) with | e | smaller end.
  - leibniz <- &e in |- *.
    ipso &first.
  - let proof g := modus aequans (W.order.strict.specification &x (&x + W.One)), &first.
    let proof l := modus aequans (W.order.strict.specification (&x + W.One) &y), &smaller.
    ipso (modus aequans (W.order.strict.specification &x &y),
          (SignedBin.order.strict.transitivity &g &l)).
Qed.

End increment. (* increment *)

Module decrement. (* decrement *)

(* Away from [W.Min], the reading is above the least, so one less is in range. *)
(* decrement.exactness *)
Theorem exactness
  : forall (x : W.T) . ~ (x = W.Min) -> W.to_b_signed (x - W.One) = (W.to_b_signed x - 1)%b_signed.
Proof.
  intros x h.
  match (bound.range &x) with | low high end.
  lemma above : (SignedBin.Negative W.half < W.to_b_signed x)%b_signed.
  {
    match &low with | same | larger end.
    - lemma e : W.to_b_signed W.Min = W.to_b_signed x.
      {
        leibniz W.minimum.specification in |- *.
        ipso &same.
      }
      ex (&h (symm (injectivity &e))) quodlibet.
    - ipso &larger.
  }
  lemma differenced : x - W.One = W.from_b_signed (W.to_b_signed x - 1)%b_signed.
  {
    leibniz (wrapping.difference &x W.One), W.one.specification in |- *.
    quod idem est.
  }
  leibniz &differenced in |- *.
  lemma lowered_low : (SignedBin.Negative W.half <= W.to_b_signed x - 1)%b_signed.
  {
    let proof least :=
      modus aequans (SignedBin.order.increment.specification (SignedBin.Negative W.half) (W.to_b_signed &x)), &above.
    lemma restored : (SignedBin.Negative W.half + 1 - 1 = SignedBin.Negative W.half)%b_signed.
    {
      leibniz
        (SignedBin.subtraction.specification (SignedBin.Negative W.half + 1)%b_signed 1%b_signed),
        (SignedBin.addition.associativity (SignedBin.Negative W.half) 1%b_signed (SignedBin.negate 1%b_signed)),
        (SignedBin.addition.right.inverse 1%b_signed),
        (SignedBin.addition.right.identity (SignedBin.Negative W.half))
        in |- *.
      quod idem est.
    }
    match &least with | same | smaller end.
    - leibniz <- &same, &restored in |- *.
      ipso (disjoin (refl (SignedBin.Negative W.half)), _).
    - let proof lowered :=
        SignedBin.order.subtraction.left.monotonicity 1%b_signed (SignedBin.Negative W.half + 1)%b_signed (W.to_b_signed &x)
          &smaller.
      leibniz &restored in &lowered.
      ipso (disjoin _, &lowered).
  }
  lemma lowered_high : (W.to_b_signed x - 1 <= W.to_b_signed W.Max)%b_signed.
  {
    ipso (disjoin _, (Comparable.order.mixed.right.transitivity
                        (SignedBin.order.decrement.extensivity (W.to_b_signed &x)) &high)).
  }
  ipso (wrapping.retraction (W.to_b_signed &x - 1)%b_signed (conjoin &lowered_low, &lowered_high)).
Qed.

(* decrement.extensivity *)
Theorem extensivity : forall (x : W.T) . ~ (x = W.Min) -> x - W.One < x.
Proof.
  intros x h.
  let proof g := SignedBin.order.decrement.extensivity (W.to_b_signed &x).
  leibniz <- (decrement.exactness &x &h) in &g.
  ipso (modus aequans (W.order.strict.specification (&x - W.One) &x), &g).
Qed.

End decrement. (* decrement *)

Module order. (* order *)

Module strict. (* order.strict *)

(* order.strict.transitivity *)
Theorem transitivity
  : forall {x : W.T} {y : W.T} {z : W.T} . x < y -> y < z -> x < z.
Proof.
  intros x y z h1 h2.
  let proof g1 := modus aequans (W.order.strict.specification &x &y), &h1.
  let proof g2 := modus aequans (W.order.strict.specification &y &z), &h2.
  ipso (modus aequans (W.order.strict.specification &x &z),
        (SignedBin.order.strict.transitivity &g1 &g2)).
Qed.

End strict. (* order.strict *)

End order. (* order *)

Module comparison. (* comparison *)

(* comparison.specification *)
Theorem specification
  : forall (x : W.T) (y : W.T) .
      (W.compare x y = Comparison.Lt <-> x < y) /\ (W.compare x y = Comparison.Eq <-> x = y).
Proof.
  intros x y.
  leibniz (W.conversion.comparison &x &y) in |- *.
  let proof s := SignedBin.comparison.specification (W.to_b_signed &x) (W.to_b_signed &y).
  match &s with | strict equality end.
  divide et impera.
  - divide et impera.
    + intro c.
      ipso (modus aequans (W.order.strict.specification &x &y), (modus aequans &strict, &c)).
    + intro h.
      ipso (modus aequans &strict, (modus aequans (W.order.strict.specification &x &y), &h)).
  - divide et impera.
    + intro c.
      ipso (injectivity (modus aequans &equality, &c)).
    + intro e.
      ipso (modus aequans &equality, (congru W.to_b_signed, &e)).
Qed.

(* comparison.antisymmetry *)
Theorem antisymmetry
  : forall (x : W.T) (y : W.T) . W.compare x y = Comparison.transpose (W.compare y x).
Proof.
  intros x y.
  leibniz (W.conversion.comparison &x &y), (W.conversion.comparison &y &x) in |- *.
  ipso (SignedBin.comparison.antisymmetry (W.to_b_signed &x) (W.to_b_signed &y)).
Qed.

End comparison. (* comparison *)

End Laws.
