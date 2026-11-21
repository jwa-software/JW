(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

From JW Require Import Core.All.
From JW Require Import Data.Base.Comparison.
From JW Require Import Data.Comparable.
From JW Require Import Data.Machine.Bit.
From JW Require Import Data.Number.Binary.Bin.
From JW Require Import Data.Number.Binary.BinBase.
From JW Require Import Data.Number.Binary.BinWithZero.
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
Parameter Inline to_bin : T -> Bin.
Parameter Inline from_bin : Bin -> T.
Parameter Inline from_bin_with_zero : BinWithZero -> T.
Parameter Inline unsigned_value : T -> BinWithZero.
Parameter Inline sign_bit : T -> Bit.
Parameter Inline add : T -> T -> T.
Parameter Inline sub : T -> T -> T.
Parameter Inline negate : T -> T.
Parameter Inline LessThan : T -> T -> Prop.
Parameter Inline LessOrEqual : T -> T -> Prop.
Parameter Inline add_with_overflow : T -> T -> Product Bit T.
Parameter Inline sub_with_overflow : T -> T -> Product Bit T.
Parameter Inline compare : T -> T -> Comparison.
Parameter Inline half : BinBase.
Parameter Inline modulus : BinBase.
Parameter Inline beyond : BinBase.

Module order. (* order *)

Module strict. (* order.strict *)

Parameter specification
  : forall (x : T) (y : T) . LessThan x y <-> (to_bin x < to_bin y)%b.

End strict. (* order.strict *)

Parameter specification
  : forall (x : T) (y : T) . LessOrEqual x y <-> x = y \/ LessThan x y.

End order. (* order *)

Module conversion. (* conversion *)

Parameter section
  : forall (x : T) . from_bin (to_bin x) = x.
Parameter comparison
  : forall (x : T) (y : T) . compare x y = Bin.compare (to_bin x) (to_bin y).
Parameter addition
  : forall (x : T) (y : T) .
      (pi_1 (add_with_overflow x y))%product = 0%bit
      -> to_bin (add x y) = (to_bin x + to_bin y)%b.
Parameter difference
  : forall (a : BinWithZero) (b : BinWithZero) .
      from_bin (Bin.bin_with_zero_difference a b)
      = add (from_bin_with_zero a) (negate (from_bin_with_zero b)).

Module forward. (* conversion.forward *)

Parameter specification
  : forall (x : T) .
      to_bin x
      = Bin.bin_with_zero_difference (unsigned_value x)
          (BinWithZero.Positive modulus * Bit.to_bin_with_zero (sign_bit x))%bin_with_zero.

End forward. (* conversion.forward *)

Module backward. (* conversion.backward *)

Parameter specification
  : forall (z : Bin) .
      from_bin z
      = add (from_bin_with_zero (Bin.ramp z))
          (negate (from_bin_with_zero (Bin.ramp (Bin.negate z)))).

End backward. (* conversion.backward *)

Module boundedness. (* conversion.boundedness *)

Parameter positive
  : forall (x : T) (p : BinBase) .
      to_bin x = Bin.Positive p
      -> (BinWithZero.Positive p < BinWithZero.Positive half)%bin_with_zero.
Parameter negative
  : forall (x : T) (p : BinBase) .
      to_bin x = Bin.Negative p
      -> (BinWithZero.Positive p <= BinWithZero.Positive half)%bin_with_zero.

End boundedness. (* conversion.boundedness *)

Module retraction. (* conversion.retraction *)

Parameter nonnegative
  : forall (n : BinWithZero) .
      (n < BinWithZero.Positive half)%bin_with_zero
      -> to_bin (from_bin (Bin.from_bin_with_zero n)) = Bin.from_bin_with_zero n.
Parameter negative
  : forall (p : BinBase) .
      (BinWithZero.Positive p <= BinWithZero.Positive half)%bin_with_zero
      -> to_bin (from_bin (Bin.Negative p)) = Bin.Negative p.

End retraction. (* conversion.retraction *)

End conversion. (* conversion *)

Module reinterpretation. (* reinterpretation *)

Parameter boundedness
  : forall (x : T) . (unsigned_value x < BinWithZero.Positive modulus)%bin_with_zero.

Module reduction. (* reinterpretation.reduction *)

Parameter additivity
  : forall (m : BinWithZero) (n : BinWithZero) .
      from_bin_with_zero (m + n)%bin_with_zero
      = add (from_bin_with_zero m) (from_bin_with_zero n).
Parameter zero
  : from_bin_with_zero BinWithZero.Zero = Zero.

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

End flag. (* flag *)

Module minimum. (* minimum *)

Parameter specification
  : to_bin Min = Bin.Negative half.
Parameter negation
  : negate Min = Min.

End minimum. (* minimum *)

Module maximum. (* maximum *)

Parameter specification
  : (to_bin Max + 1 = Bin.Positive half)%b.
Parameter positivity
  : (0 < to_bin Max)%b.

End maximum. (* maximum *)

Module one. (* one *)

Parameter specification
  : to_bin One = 1%b.

End one. (* one *)

Module modulus. (* modulus *)

Parameter specification
  : (Bin.Positive modulus = Bin.Positive half + Bin.Positive half)%b.
Parameter wrapping
  : from_bin (Bin.Positive modulus) = Zero.

End modulus. (* modulus *)

Module beyond. (* beyond *)

Parameter specification
  : (Bin.Positive beyond = Bin.Positive modulus + Bin.Positive half)%b.

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
Local Notation "- x" := (W.negate x)
  (at level 35, right associativity, only parsing)
  : jw_signed_scope.
Local Notation "x < y" := (W.LessThan x y) (only parsing)
  : jw_signed_scope.
Local Notation "x <= y" := (W.LessOrEqual x y) (only parsing)
  : jw_signed_scope.
#[local] Bind Scope jw_signed_scope with W.T.
Local Open Scope jw_signed_scope.

(* A value is fixed by its [Bin] reading. *)
Lemma injectivity : forall {x : W.T} {y : W.T} . W.to_bin x = W.to_bin y -> x = y.
Proof.
  intros x y e.
  leibniz <- (W.conversion.section &x), <- (W.conversion.section &y), &e in |- *.
  quod idem est.
Qed.

(* The least value is at most the greatest. *)
Lemma ordered : (Bin.Negative W.half <= W.to_bin W.Max)%b.
Proof.
  ipso (disjoin _,
        (Bin.order.strict.transitivity
           (Bin.order.sign.negativity W.half) W.maximum.positivity)).
Qed.

Module bound. (* bound *)

(* The bounds of [W.conversion.boundedness.positive] and
 * [W.conversion.boundedness.negative], read in [Bin]'s order.
 *)
(* bound.range *)
Theorem range
  : forall (x : W.T) . (Bin.Negative W.half <= W.to_bin x /\ W.to_bin x <= W.to_bin W.Max)%b.
Proof.
  intro x.
  match (W.to_bin &x) with | p | | p end |- e.
  - let proof b := W.conversion.boundedness.negative &x &p &e.
    divide et impera.
    + match &b with | same | smaller end.
      * lemma facto : W.half = p.
        {
          ipso (symm (congru (fun (n : BinWithZero) .
                                match n with
                                | BinWithZero.Zero       => &p
                                | BinWithZero.Positive q => q
                                end), &same)).
        }
        leibniz &facto in |- *.
        ipso (disjoin (refl (Bin.Negative &p)), _).
      * let proof lifted :=
          modus aequans
            (Bin.order.embedding.preservation
               (BinWithZero.Positive &p) (BinWithZero.Positive W.half)),
            &smaller.
        lemma facto : (Bin.Negative W.half < Bin.Negative p)%b.
        {
          ipso (modus aequans
                  (Bin.order.negation.strict.reversal (Bin.Positive &p) (Bin.Positive W.half)),
                  &lifted).
        }
        ipso (disjoin _, &facto).
    + ipso (disjoin _,
            (Bin.order.strict.transitivity
               (Bin.order.sign.negativity &p) W.maximum.positivity)).
  - divide et impera.
    + ipso (disjoin _, (Bin.order.sign.negativity W.half)).
    + ipso (disjoin _, W.maximum.positivity).
  - let proof b := W.conversion.boundedness.positive &x &p &e.
    divide et impera.
    + ipso (disjoin _,
            (Bin.order.strict.transitivity
               (Bin.order.sign.negativity W.half) (Bin.order.sign.positivity &p))).
    + let proof lifted :=
        modus aequans
          (Bin.order.embedding.preservation
             (BinWithZero.Positive &p) (BinWithZero.Positive W.half)),
          &b.
      lemma facto : (Bin.Positive p < W.to_bin W.Max + 1)%b.
      {
        leibniz W.maximum.specification in |- *.
        ipso &lifted.
      }
      ipso (modus aequans (Bin.order.discreteness (Bin.Positive &p) (W.to_bin W.Max)), &facto).
Qed.

(* bound.lower *)
Theorem lower : forall (x : W.T) . W.Min <= x.
Proof.
  intro x.
  match (bound.range &x) with | low _ end.
  match &low with | same | smaller end.
  - lemma facto : W.to_bin W.Min = W.to_bin x.
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
Theorem clear : forall (x : W.T) . W.sign_bit x = 0%bit -> (0 <= W.to_bin x)%b.
Proof.
  intros x s.
  leibniz (W.conversion.forward.specification &x), &s in |- *.
  lemma scaled : (BinWithZero.Positive W.modulus * Bit.to_bin_with_zero 0 = 0)%bin_with_zero.
  {
    simpl Bit.to_bin_with_zero in |- *.
    simpl in |- *.
    quod idem est.
  }
  leibniz &scaled in |- *.
  lemma facto
    : Bin.bin_with_zero_difference (W.unsigned_value x) 0%bin_with_zero
      = Bin.from_bin_with_zero (W.unsigned_value x).
  {
    match (W.unsigned_value &x) with | | p end; simpl in |- *; quod idem est.
  }
  leibniz &facto in |- *.
  ipso (Bin.order.embedding.nonnegativity (W.unsigned_value &x)).
Qed.

(* A set sign bit takes the modulus from an unsigned value below it. *)
(* sign.set *)
Theorem set : forall (x : W.T) . W.sign_bit x = 1%bit -> (W.to_bin x < 0)%b.
Proof.
  intros x s.
  leibniz (W.conversion.forward.specification &x), &s in |- *.
  lemma whole
    : (BinWithZero.Positive W.modulus * Bit.to_bin_with_zero 1
       = BinWithZero.Positive W.modulus)%bin_with_zero.
  {
    match (BinWithZero.multiplication.identity (BinWithZero.Positive W.modulus)) with | _ r end.
    ipso &r.
  }
  leibniz &whole in |- *.
  lemma split
    : forall (a : BinWithZero) (b : BinWithZero) .
        Bin.bin_with_zero_difference a b
        = (Bin.from_bin_with_zero a + Bin.negate (Bin.from_bin_with_zero b))%b.
  {
    intros a b.
    match &a with | | p end; match &b with | | q end;
      simpl Bin.add in |- *; simpl in |- *; quod idem est.
  }
  leibniz (&split (W.unsigned_value &x) (BinWithZero.Positive W.modulus)) in |- *.
  let proof lifted :=
    modus aequans
      (Bin.order.embedding.preservation (W.unsigned_value &x) (BinWithZero.Positive W.modulus)),
      (W.reinterpretation.boundedness &x).
  let proof shifted :=
    Bin.addition.order.strict.monotonicity
      (Bin.negate (Bin.from_bin_with_zero (BinWithZero.Positive W.modulus))) _ _ &lifted.
  leibniz
    (Bin.addition.commutativity
       (Bin.negate (Bin.from_bin_with_zero (BinWithZero.Positive W.modulus)))
       (Bin.from_bin_with_zero (W.unsigned_value &x))),
    (Bin.addition.left.inverse (Bin.from_bin_with_zero (BinWithZero.Positive W.modulus)))
    in &shifted.
  ipso &shifted.
Qed.

End sign. (* sign *)

Module wrapping. (* wrapping *)

(* [Bin.add] is the difference of the summed positive parts and the summed
 * negative parts, and [from_bin] carries a difference and a sum over; what is
 * left is regrouping the four parts.
 *)
(* wrapping.additivity *)
Theorem additivity
  : forall (a : Bin) (b : Bin) . W.from_bin (a + b)%b = W.from_bin a + W.from_bin b.
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
  simpl Bin.add in |- *.
  leibniz
    (W.conversion.difference
       (Bin.ramp &a + Bin.ramp &b)%bin_with_zero
       (Bin.ramp (Bin.negate &a) + Bin.ramp (Bin.negate &b))%bin_with_zero),
    (W.reinterpretation.reduction.additivity (Bin.ramp &a) (Bin.ramp &b)),
    (W.reinterpretation.reduction.additivity (Bin.ramp (Bin.negate &a)) (Bin.ramp (Bin.negate &b)))
    in |- *.
  leibniz
    (&inverted
       (W.from_bin_with_zero (Bin.ramp (Bin.negate &a)))
       (W.from_bin_with_zero (Bin.ramp (Bin.negate &b))))
    in |- *.
  leibniz
    (W.conversion.backward.specification &a),
    (W.conversion.backward.specification &b)
    in |- *.
  let pa := W.from_bin_with_zero (Bin.ramp &a) in |- *.
  let pb := W.from_bin_with_zero (Bin.ramp &b) in |- *.
  let na := (- W.from_bin_with_zero (Bin.ramp (Bin.negate &a))) in |- *.
  let nb := (- W.from_bin_with_zero (Bin.ramp (Bin.negate &b))) in |- *.
  leibniz
    (W.addition.associativity &pa &pb (&na + &nb)),
    <- (W.addition.associativity &pb &na &nb),
    (W.addition.commutativity &pb &na),
    (W.addition.associativity &na &pb &nb),
    <- (W.addition.associativity &pa &na (&pb + &nb))
    in |- *.
  quod idem est.
Qed.

(* [from_bin a] plus [from_bin (- a)] is [from_bin 0], so the second is the
 * inverse of the first.
 *)
(* wrapping.negation *)
Theorem negation : forall (a : Bin) . W.from_bin (Bin.negate a) = - W.from_bin a.
Proof.
  intro a.
  lemma zero : W.from_bin a + W.from_bin (Bin.negate a) = W.Zero.
  {
    leibniz
      <- (wrapping.additivity &a (Bin.negate &a)),
      (Bin.addition.right.inverse &a),
      (W.conversion.backward.specification 0%b)
      in |- *.
    lemma origin : W.from_bin_with_zero (Bin.ramp 0%b) = W.Zero.
    {
      ipso W.reinterpretation.reduction.zero.
    }
    lemma negated_origin : W.from_bin_with_zero (Bin.ramp (Bin.negate 0%b)) = W.Zero.
    {
      ipso W.reinterpretation.reduction.zero.
    }
    leibniz &origin, &negated_origin in |- *.
    match (W.addition.inverse W.Zero) with | _ right_inverse end.
    ipso &right_inverse.
  }
  match (W.addition.identity (W.from_bin (Bin.negate &a))) with | left_identity _ end.
  match (W.addition.inverse (W.from_bin &a)) with | left_inverse _ end.
  leibniz <- &left_identity, <- &left_inverse in |- *.
  leibniz
    (W.addition.associativity (- W.from_bin &a) (W.from_bin &a) (W.from_bin (Bin.negate &a))),
    &zero
    in |- *.
  match (W.addition.identity (- W.from_bin &a)) with | _ right_identity end.
  ipso &right_identity.
Qed.

(* wrapping.summation *)
Theorem summation
  : forall (x : W.T) (y : W.T) . x + y = W.from_bin (W.to_bin x + W.to_bin y)%b.
Proof.
  intros x y.
  leibniz
    (wrapping.additivity (W.to_bin &x) (W.to_bin &y)),
    (W.conversion.section &x),
    (W.conversion.section &y)
    in |- *.
  quod idem est.
Qed.

(* wrapping.difference *)
Theorem difference
  : forall (x : W.T) (y : W.T) . x - y = W.from_bin (W.to_bin x - W.to_bin y)%b.
Proof.
  intros x y.
  leibniz (W.subtraction.specification &x &y) in |- *.
  simpl Bin.sub in |- *.
  leibniz
    (wrapping.additivity (W.to_bin &x) (Bin.negate (W.to_bin &y))),
    (wrapping.negation (W.to_bin &y)),
    (W.conversion.section &x),
    (W.conversion.section &y)
    in |- *.
  quod idem est.
Qed.

(* [W.conversion.retraction.nonnegative] and [W.conversion.retraction.negative]
 * together, their bounds read in [Bin]'s order.
 *)
(* wrapping.retraction *)
Theorem retraction
  : forall (z : Bin) .
      (Bin.Negative W.half <= z /\ z <= W.to_bin W.Max)%b -> W.to_bin (W.from_bin z) = z.
Proof.
  intros z h.
  match &h with | low high end.
  match &z with | p | | p end.
  - lemma b : (BinWithZero.Positive p <= BinWithZero.Positive W.half)%bin_with_zero.
    {
      match &low with | same | smaller end.
      + lemma facto : W.half = p.
        {
          ipso (congru (fun (v : Bin) .
                          match v with
                          | Bin.Negative q => q
                          | Bin.Zero       => &p
                          | Bin.Positive q => q
                          end), &same).
        }
        leibniz &facto in |- *.
        ipso (disjoin (refl (BinWithZero.Positive &p)), _).
      + let proof reversed :=
          modus aequans
            (Bin.order.negation.strict.reversal (Bin.Positive &p) (Bin.Positive W.half)),
            &smaller.
        ipso (disjoin _,
                (modus aequans
                   (Bin.order.embedding.preservation
                      (BinWithZero.Positive &p) (BinWithZero.Positive W.half)),
                   &reversed)).
    }
    ipso (W.conversion.retraction.negative &p &b).
  - lemma small : (0 < BinWithZero.Positive W.half)%bin_with_zero.
    {
      simpl BinWithZero.LessThan in |- *.
      exists W.half.
      simpl in |- *.
      quod idem est.
    }
    ipso (W.conversion.retraction.nonnegative 0%bin_with_zero &small).
  - lemma small : (BinWithZero.Positive p < BinWithZero.Positive W.half)%bin_with_zero.
    {
      lemma lifted : (Bin.Positive p < Bin.Positive W.half)%b.
      {
        leibniz <- W.maximum.specification in |- *.
        ipso (modus aequans (Bin.order.discreteness (Bin.Positive &p) (W.to_bin W.Max)), &high).
      }
      ipso (modus aequans
              (Bin.order.embedding.preservation
                 (BinWithZero.Positive &p) (BinWithZero.Positive W.half)),
              &lifted).
    }
    ipso (W.conversion.retraction.nonnegative (BinWithZero.Positive &p) &small).
Qed.

(* [from_bin] of the modulus is [Zero], so shifting by the modulus changes
 * nothing that [from_bin] gives, and moves a value just past either end back
 * into range.
 *)
(* wrapping.upper *)
Theorem upper
  : forall (s : Bin) .
      (W.to_bin W.Max < s /\ s < Bin.Positive W.beyond)%b
      -> W.to_bin (W.from_bin s) = (s - Bin.Positive W.modulus)%b.
Proof.
  intros s h.
  match &h with | above below end.
  lemma shifted : W.from_bin s = W.from_bin (s - Bin.Positive W.modulus)%b.
  {
    simpl Bin.sub in |- *.
    leibniz
      (wrapping.additivity &s (Bin.negate (Bin.Positive W.modulus))),
      (wrapping.negation (Bin.Positive W.modulus)),
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
    match (W.addition.identity (W.from_bin &s)) with | _ right_identity end.
    ipso (symm &right_identity).
  }
  (* [half - (half + half)] regrouped. *)
  lemma folded : (Bin.Positive W.half - Bin.Positive W.modulus = Bin.Negative W.half)%b.
  {
    leibniz
      W.modulus.specification,
      (Bin.subtraction.specification (Bin.Positive W.half)
         (Bin.Positive W.half + Bin.Positive W.half)%b),
      (Bin.negation.additivity (Bin.Positive W.half) (Bin.Positive W.half)),
      <- (Bin.addition.associativity (Bin.Positive W.half) (Bin.negate (Bin.Positive W.half))
            (Bin.negate (Bin.Positive W.half))),
      (Bin.addition.right.inverse (Bin.Positive W.half)),
      (Bin.addition.left.identity (Bin.negate (Bin.Positive W.half)))
      in |- *.
    ipso (refl (Bin.Negative W.half)).
  }
  lemma low : (Bin.Negative W.half <= s - Bin.Positive W.modulus)%b.
  {
    let proof least :=
      modus aequans (Bin.order.increment.specification (W.to_bin W.Max) &s), &above.
    leibniz W.maximum.specification in &least.
    match &least with | same | smaller end.
    + leibniz <- &same, &folded in |- *.
      ipso (disjoin (refl (Bin.Negative W.half)), _).
    + let proof lowered :=
        Bin.order.subtraction.left.monotonicity (Bin.Positive W.modulus) (Bin.Positive W.half) &s
          &smaller.
      leibniz &folded in &lowered.
      ipso (disjoin _, &lowered).
  }
  (* [(modulus + half) - modulus] is [half]. *)
  lemma restored : (Bin.Positive W.beyond - Bin.Positive W.modulus = Bin.Positive W.half)%b.
  {
    leibniz
      W.beyond.specification,
      (Bin.addition.commutativity (Bin.Positive W.modulus) (Bin.Positive W.half))
      in |- *.
    ipso (Bin.subtraction.inversion.addition (Bin.Positive W.half) (Bin.Positive W.modulus)).
  }
  lemma high : (s - Bin.Positive W.modulus <= W.to_bin W.Max)%b.
  {
    let proof lowered :=
      Bin.order.subtraction.left.monotonicity (Bin.Positive W.modulus) &s (Bin.Positive W.beyond)
        &below.
    leibniz &restored, <- W.maximum.specification in &lowered.
    ipso (modus aequans
            (Bin.order.discreteness (&s - Bin.Positive W.modulus)%b (W.to_bin W.Max)), &lowered).
  }
  leibniz &shifted in |- *.
  ipso (wrapping.retraction (&s - Bin.Positive W.modulus)%b (conjoin &low, &high)).
Qed.

(* wrapping.lower *)
Theorem lower
  : forall (s : Bin) .
      (s < Bin.Negative W.half /\ Bin.Negative W.beyond < s)%b
      -> W.to_bin (W.from_bin s) = (s + Bin.Positive W.modulus)%b.
Proof.
  intros s h.
  match &h with | below above end.
  lemma shifted : W.from_bin s = W.from_bin (s + Bin.Positive W.modulus)%b.
  {
    leibniz (wrapping.additivity &s (Bin.Positive W.modulus)), W.modulus.wrapping in |- *.
    match (W.addition.identity (W.from_bin &s)) with | _ right_identity end.
    ipso (symm &right_identity).
  }
  (* [- (modulus + half) + modulus] regrouped. *)
  lemma folded
    : (Bin.negate (Bin.Positive W.beyond) + Bin.Positive W.modulus = Bin.Negative W.half)%b.
  {
    leibniz
      W.beyond.specification,
      (Bin.negation.additivity (Bin.Positive W.modulus) (Bin.Positive W.half)),
      (Bin.addition.commutativity (Bin.negate (Bin.Positive W.modulus))
         (Bin.negate (Bin.Positive W.half))),
      (Bin.addition.associativity (Bin.negate (Bin.Positive W.half))
         (Bin.negate (Bin.Positive W.modulus)) (Bin.Positive W.modulus)),
      (Bin.addition.left.inverse (Bin.Positive W.modulus)),
      (Bin.addition.right.identity (Bin.negate (Bin.Positive W.half)))
      in |- *.
    ipso (refl (Bin.Negative W.half)).
  }
  lemma low : (Bin.Negative W.half <= s + Bin.Positive W.modulus)%b.
  {
    let proof raised
      : (Bin.Positive W.modulus + Bin.negate (Bin.Positive W.beyond)
         < Bin.Positive W.modulus + s)%b
      := Bin.addition.order.strict.monotonicity (Bin.Positive W.modulus) (Bin.Negative W.beyond)
           &s &above.
    leibniz
      (Bin.addition.commutativity (Bin.Positive W.modulus) (Bin.negate (Bin.Positive W.beyond))),
      (Bin.addition.commutativity (Bin.Positive W.modulus) &s),
      &folded
      in &raised.
    ipso (disjoin _, &raised).
  }
  (* [- half + (half + half)] regrouped. *)
  lemma unfolded
    : (Bin.negate (Bin.Positive W.half) + Bin.Positive W.modulus = Bin.Positive W.half)%b.
  {
    leibniz
      W.modulus.specification,
      <- (Bin.addition.associativity (Bin.negate (Bin.Positive W.half)) (Bin.Positive W.half)
            (Bin.Positive W.half)),
      (Bin.addition.left.inverse (Bin.Positive W.half)),
      (Bin.addition.left.identity (Bin.Positive W.half))
      in |- *.
    quod idem est.
  }
  lemma high : (s + Bin.Positive W.modulus <= W.to_bin W.Max)%b.
  {
    let proof raised
      : (Bin.Positive W.modulus + s
         < Bin.Positive W.modulus + Bin.negate (Bin.Positive W.half))%b
      := Bin.addition.order.strict.monotonicity (Bin.Positive W.modulus) &s (Bin.Negative W.half)
           &below.
    leibniz
      (Bin.addition.commutativity (Bin.Positive W.modulus) &s),
      (Bin.addition.commutativity (Bin.Positive W.modulus) (Bin.negate (Bin.Positive W.half))),
      &unfolded,
      <- W.maximum.specification
      in &raised.
    ipso (modus aequans
            (Bin.order.discreteness (&s + Bin.Positive W.modulus)%b (W.to_bin W.Max)), &raised).
  }
  leibniz &shifted in |- *.
  ipso (wrapping.retraction (&s + Bin.Positive W.modulus)%b (conjoin &low, &high)).
Qed.

End wrapping. (* wrapping *)

Module overflow. (* overflow *)

Module addition. (* overflow.addition *)

(* Clear flag: the sum is [W.to_bin (W.add x y)], which is in range. Sum in
 * range: [W.add x y] is [W.from_bin] of the [Bin] sum, so its reading is that
 * sum; a set flag would mean two operands of one sign and a result of the
 * other, which that equation rules out.
 *)
(* overflow.addition.specification *)
Theorem specification
  : forall (x : W.T) (y : W.T) .
      (pi_1 (W.add_with_overflow x y))%product = 0%bit
      <-> (Bin.Negative W.half <= W.to_bin x + W.to_bin y
           /\ W.to_bin x + W.to_bin y <= W.to_bin W.Max)%b.
Proof.
  intros x y.
  divide et impera.
  - intro f.
    leibniz <- (W.conversion.addition &x &y &f) in |- *.
    ipso (bound.range (&x + &y)).
  - intro r.
    lemma same : W.to_bin (x + y) = (W.to_bin x + W.to_bin y)%b.
    {
      leibniz (wrapping.summation &x &y) in |- *.
      ipso (wrapping.retraction (W.to_bin &x + W.to_bin &y)%b &r).
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
        let proof widened := Bin.addition.order.monotonicity (W.to_bin &x) 0%b (W.to_bin &y) &cy.
        leibniz (Bin.addition.right.identity (W.to_bin &x)) in &widened.
        let proof nonnegative :=
          @Comparable.order.transitivity _ Bin.compare Bin.LessThan _ 0%b (W.to_bin &x)
            (W.to_bin &x + W.to_bin &y)%b &cx &widened.
        ex (Bin.order.strict.irreflexivity 0%b
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
          Bin.addition.order.mixed.monotonicity (W.to_bin &x) (W.to_bin &y) 0%b 0%b
            (Comparable.order.strict.weakening (W.to_bin &x) 0%b &nx) &ny.
        ex (Bin.order.strict.irreflexivity 0%b
              (Comparable.order.mixed.left.transitivity &nonnegative &negative))
          quodlibet.
      * simpl in &f.
        ex &f quodlibet.
Qed.

(* A set flag puts the [Bin] sum out of range, and the sum of two readings lies
 * between twice the least and twice the greatest, so it is past one end by
 * less than the modulus and [wrapping.upper] or [wrapping.lower] brings it
 * back.
 *)
(* overflow.addition.wrap *)
Theorem wrap
  : forall (x : W.T) (y : W.T) .
      (pi_1 (W.add_with_overflow x y))%product = 1%bit
      -> W.to_bin (x + y) = (W.to_bin x + W.to_bin y - Bin.Positive W.modulus)%b
         \/ W.to_bin (x + y) = (W.to_bin x + W.to_bin y + Bin.Positive W.modulus)%b.
Proof.
  intros x y f.
  lemma outside
    : ~ ((Bin.Negative W.half <= W.to_bin x + W.to_bin y
          /\ W.to_bin x + W.to_bin y <= W.to_bin W.Max)%b).
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
    Bin.addition.order.accumulation (W.to_bin &x) (W.to_bin &y) (W.to_bin W.Max) (W.to_bin W.Max)
      &high_x &high_y.
  let proof bottom :=
    Bin.addition.order.accumulation (Bin.Negative W.half) (Bin.Negative W.half) (W.to_bin &x)
      (W.to_bin &y)
      &low_x &low_y.
  leibniz (wrapping.summation &x &y) in |- *.
  (* [to_bin Max] is below [half], so twice it is below [modulus], which is below
   * [beyond].
   *)
  let proof max_below : (W.to_bin W.Max < W.to_bin W.Max + 1)%b
    := Bin.order.increment.extensivity (W.to_bin W.Max).
  leibniz W.maximum.specification in &max_below.
  lemma max_at_most : (W.to_bin W.Max <= Bin.Positive W.half)%b.
  {
    ipso (disjoin _, &max_below).
  }
  lemma modulus_below : (Bin.Positive W.modulus < Bin.Positive W.beyond)%b.
  {
    simpl Bin.LessThan in |- *.
    exists W.half.
    ipso (symm W.beyond.specification).
  }
  lemma sum_below : (W.to_bin W.Max + W.to_bin W.Max < Bin.Positive W.beyond)%b.
  {
    let proof doubled :=
      Bin.addition.order.mixed.monotonicity (W.to_bin W.Max) (W.to_bin W.Max)
        (Bin.Positive W.half) (Bin.Positive W.half) &max_at_most &max_below.
    leibniz <- W.modulus.specification in &doubled.
    ipso (Bin.order.strict.transitivity &doubled &modulus_below).
  }
  lemma sum_above : (Bin.Negative W.beyond < Bin.Negative W.half + Bin.Negative W.half)%b.
  {
    let proof reversed :=
      modus aequans
        (Bin.order.negation.strict.reversal (Bin.Positive W.modulus) (Bin.Positive W.beyond)),
        &modulus_below.
    leibniz
      W.modulus.specification,
      (Bin.negation.additivity (Bin.Positive W.half) (Bin.Positive W.half))
      in &reversed.
    ipso &reversed.
  }
  match (Comparable.order.strict.trichotomy (W.to_bin W.Max) (W.to_bin &x + W.to_bin &y)%b)
    with | above | rest end.
  - let proof below := Comparable.order.mixed.left.transitivity &top &sum_below.
    ipso (disjoin (wrapping.upper (W.to_bin &x + W.to_bin &y)%b (conjoin &above, &below)), _).
  - match &rest with | same | under end.
    + lemma inside
        : (Bin.Negative W.half <= W.to_bin x + W.to_bin y
           /\ W.to_bin x + W.to_bin y <= W.to_bin W.Max)%b.
      {
        leibniz <- &same in |- *.
        ipso (conjoin ordered, (disjoin (refl (W.to_bin W.Max)), _)).
      }
      ex (&outside &inside) quodlibet.
    + match (Comparable.order.strict.trichotomy (W.to_bin &x + W.to_bin &y)%b (Bin.Negative W.half))
        with | beneath | remainder end.
      * let proof above := Comparable.order.mixed.right.transitivity &sum_above &bottom.
        ipso (disjoin _, (wrapping.lower (W.to_bin &x + W.to_bin &y)%b (conjoin &beneath, &above))).
      * lemma inside
          : (Bin.Negative W.half <= W.to_bin x + W.to_bin y
             /\ W.to_bin x + W.to_bin y <= W.to_bin W.Max)%b.
        {
          lemma low : (Bin.Negative W.half <= W.to_bin x + W.to_bin y)%b.
          {
            match &remainder with | same | over end.
            - leibniz &same in |- *.
              ipso (disjoin (refl (Bin.Negative W.half)), _).
            - ipso (disjoin _, &over).
          }
          ipso (conjoin &low, (disjoin _, &under)).
        }
        ex (&outside &inside) quodlibet.
Qed.

(* Two clear flags make both sums exact, and [Bin]'s addition keeps the order. *)
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
    Bin.addition.order.strict.monotonicity (W.to_bin &x) (W.to_bin &y) (W.to_bin &z) &g.
  leibniz <- (W.conversion.addition &x &y &fy), <- (W.conversion.addition &x &z &fz) in &s.
  ipso (modus aequans (W.order.strict.specification (&x + &y) (&x + &z)), &s).
Qed.

End addition. (* overflow.addition *)

Module subtraction. (* overflow.subtraction *)

(* Difference in range: [W.sub x y] is [W.from_bin] of the [Bin] difference,
 * so it is exact, and a set flag, which needs operands of different signs and
 * a result with the sign of [y], is ruled out by the signs. Difference out of
 * range: it is past one end by less than the modulus, the result wraps to the
 * other sign, and the operands' signs are forced, which sets the flag.
 *)
(* overflow.subtraction.specification *)
Theorem specification
  : forall (x : W.T) (y : W.T) .
      (pi_1 (W.sub_with_overflow x y))%product = 0%bit
      <-> (Bin.Negative W.half <= W.to_bin x - W.to_bin y
           /\ W.to_bin x - W.to_bin y <= W.to_bin W.Max)%b.
Proof.
  intros x y.
  match (bound.range &x) with | low_x high_x end.
  match (bound.range &y) with | low_y high_y end.
  lemma below_y : (Bin.negate (W.to_bin y) <= Bin.Positive W.half)%b.
  {
    ipso (Bin.order.negation.reversal (Bin.Negative W.half) (W.to_bin &y) &low_y).
  }
  let proof above_y := Bin.order.negation.reversal (W.to_bin &y) (W.to_bin W.Max) &high_y.
  (* The ends of the range against [half], [modulus] and [beyond], from
   * [to_bin Max < half], [modulus = half + half] and [beyond = modulus + half].
   *)
  let proof max_below : (W.to_bin W.Max < W.to_bin W.Max + 1)%b
    := Bin.order.increment.extensivity (W.to_bin W.Max).
  leibniz W.maximum.specification in &max_below.
  lemma modulus_below : (Bin.Positive W.modulus < Bin.Positive W.beyond)%b.
  {
    simpl Bin.LessThan in |- *.
    exists W.half.
    ipso (symm W.beyond.specification).
  }
  lemma negated_below : (Bin.Negative W.half < Bin.negate (W.to_bin W.Max))%b.
  {
    ipso (modus aequans
            (Bin.order.negation.strict.reversal (W.to_bin W.Max) (Bin.Positive W.half)),
            &max_below).
  }
  lemma sum_below : (W.to_bin W.Max + Bin.Positive W.half < Bin.Positive W.beyond)%b.
  {
    let proof raised :=
      Bin.addition.order.strict.monotonicity (Bin.Positive W.half) (W.to_bin W.Max)
        (Bin.Positive W.half) &max_below.
    leibniz
      (Bin.addition.commutativity (Bin.Positive W.half) (W.to_bin W.Max)),
      <- W.modulus.specification
      in &raised.
    ipso (Bin.order.strict.transitivity &raised &modulus_below).
  }
  lemma sum_successor
    : ((W.to_bin W.Max + Bin.Positive W.half) + 1 = Bin.Positive W.modulus)%b.
  {
    leibniz
      (Bin.addition.associativity (W.to_bin W.Max) (Bin.Positive W.half) 1%b),
      (Bin.addition.commutativity (Bin.Positive W.half) 1%b),
      <- (Bin.addition.associativity (W.to_bin W.Max) 1%b (Bin.Positive W.half)),
      W.maximum.specification,
      <- W.modulus.specification
      in |- *.
    quod idem est.
  }
  lemma halves_above
    : (Bin.negate (Bin.Positive W.modulus) < Bin.Negative W.half + Bin.negate (W.to_bin W.Max))%b.
  {
    leibniz
      W.modulus.specification,
      (Bin.negation.additivity (Bin.Positive W.half) (Bin.Positive W.half))
      in |- *.
    ipso (Bin.addition.order.strict.monotonicity (Bin.Negative W.half) (Bin.Negative W.half)
            (Bin.negate (W.to_bin W.Max)) &negated_below).
  }
  lemma beyond_above
    : (Bin.Negative W.beyond < Bin.Negative W.half + Bin.negate (W.to_bin W.Max))%b.
  {
    let proof reversed :=
      modus aequans
        (Bin.order.negation.strict.reversal (Bin.Positive W.modulus) (Bin.Positive W.beyond)),
        &modulus_below.
    ipso (Bin.order.strict.transitivity &reversed &halves_above).
  }
  divide et impera.
  - intro f.
    lemma top : (W.to_bin x - W.to_bin y <= W.to_bin W.Max + Bin.Positive W.half)%b.
    {
      ipso (Bin.addition.order.accumulation
              (W.to_bin &x) (Bin.negate (W.to_bin &y)) (W.to_bin W.Max) (Bin.Positive W.half)
              &high_x &below_y).
    }
    lemma bottom
      : (Bin.Negative W.half + Bin.negate (W.to_bin W.Max) <= W.to_bin x - W.to_bin y)%b.
    {
      ipso (Bin.addition.order.accumulation
              (Bin.Negative W.half) (Bin.negate (W.to_bin W.Max)) (W.to_bin &x)
              (Bin.negate (W.to_bin &y)) &low_x &above_y).
    }
    match (Comparable.order.strict.trichotomy (W.to_bin W.Max) (W.to_bin &x - W.to_bin &y)%b)
      with | above | rest end.
    + (* Past the greatest: the result wraps below 0, [x] is nonnegative, [y]
       * negative.
       *)
      let proof below := Comparable.order.mixed.left.transitivity &top &sum_below.
      lemma wrapped
        : W.to_bin (x - y) = (W.to_bin x - W.to_bin y - Bin.Positive W.modulus)%b.
      {
        leibniz (wrapping.difference &x &y) in |- *.
        ipso (wrapping.upper (W.to_bin &x - W.to_bin &y)%b (conjoin &above, &below)).
      }
      lemma negative : (W.to_bin (x - y) < 0)%b.
      {
        let proof under :=
          modus aequans
            (Bin.order.discreteness (W.to_bin &x - W.to_bin &y)%b
               (W.to_bin W.Max + Bin.Positive W.half)%b),
            &top.
        leibniz &sum_successor in &under.
        leibniz &wrapped in |- *.
        let proof lowered :=
          Bin.order.subtraction.left.monotonicity (Bin.Positive W.modulus)
            (W.to_bin &x - W.to_bin &y)%b (Bin.Positive W.modulus) &under.
        leibniz
          (Bin.subtraction.specification (Bin.Positive W.modulus) (Bin.Positive W.modulus)),
          (Bin.addition.right.inverse (Bin.Positive W.modulus))
          in &lowered.
        ipso &lowered.
      }
      match (W.sign_bit (&x - &y)) with | Zero | One end |- sr.
      * ex (Bin.order.strict.irreflexivity 0%b
              (Comparable.order.mixed.left.transitivity
                 (sign.clear (&x - &y) &sr) &negative))
          quodlibet.
      * match (W.sign_bit &x) with | Zero | One end |- sx.
        -- match (W.sign_bit &y) with | Zero | One end |- sy.
           ++ let proof shrunk :=
                Bin.addition.order.monotonicity (W.to_bin &x) (Bin.negate (W.to_bin &y)) 0%b
                  (Bin.order.negation.reversal 0%b (W.to_bin &y) (sign.clear &y &sy)).
              leibniz (Bin.addition.right.identity (W.to_bin &x)) in &shrunk.
              lemma small : (W.to_bin x - W.to_bin y <= W.to_bin W.Max)%b.
              {
                ipso (@Comparable.order.transitivity _ Bin.compare Bin.LessThan _
                        (W.to_bin &x - W.to_bin &y)%b (W.to_bin &x) (W.to_bin W.Max)
                        &shrunk &high_x).
              }
              ex (Bin.order.strict.irreflexivity (W.to_bin W.Max)
                    (Comparable.order.mixed.right.transitivity &above &small))
                quodlibet.
           ++ leibniz (W.flag.subtraction.specification &x &y), &sx, &sy, &sr in &f.
              simpl in &f.
              ex &f quodlibet.
        -- let proof shrunk :=
             Bin.addition.order.mixed.monotonicity
               (Bin.negate (W.to_bin &y)) (W.to_bin &x) (Bin.Positive W.half) 0%b
               &below_y (sign.set &x &sx).
           leibniz
             (Bin.addition.commutativity (Bin.negate (W.to_bin &y)) (W.to_bin &x)),
             (Bin.addition.right.identity (Bin.Positive W.half)),
             <- W.maximum.specification
             in &shrunk.
           lemma small : (W.to_bin x - W.to_bin y <= W.to_bin W.Max)%b.
           {
             ipso (modus aequans
                     (Bin.order.discreteness (W.to_bin &x - W.to_bin &y)%b (W.to_bin W.Max)),
                     &shrunk).
           }
           ex (Bin.order.strict.irreflexivity (W.to_bin W.Max)
                 (Comparable.order.mixed.right.transitivity &above &small))
             quodlibet.
    + match &rest with | same | under end.
      * lemma inside
          : (Bin.Negative W.half <= W.to_bin x - W.to_bin y
             /\ W.to_bin x - W.to_bin y <= W.to_bin W.Max)%b.
        {
          leibniz <- &same in |- *.
          ipso (conjoin ordered, (disjoin (refl (W.to_bin W.Max)), _)).
        }
        ipso &inside.
      * match (Comparable.order.strict.trichotomy (W.to_bin &x - W.to_bin &y)%b
                 (Bin.Negative W.half))
          with | beneath | remainder end.
        -- (* Below the least: the result wraps above 0, [x] is negative, [y]
            * nonnegative.
            *)
           let proof above := Comparable.order.mixed.right.transitivity &beyond_above &bottom.
           lemma wrapped
             : W.to_bin (x - y) = (W.to_bin x - W.to_bin y + Bin.Positive W.modulus)%b.
           {
             leibniz (wrapping.difference &x &y) in |- *.
             ipso (wrapping.lower (W.to_bin &x - W.to_bin &y)%b (conjoin &beneath, &above)).
           }
           lemma nonnegative : (0 <= W.to_bin (x - y))%b.
           {
             let proof over := Comparable.order.mixed.right.transitivity &halves_above &bottom.
             leibniz &wrapped in |- *.
             let proof raised :=
               Bin.addition.order.strict.monotonicity (Bin.Positive W.modulus)
                 (Bin.negate (Bin.Positive W.modulus)) (W.to_bin &x - W.to_bin &y)%b &over.
             leibniz
               (Bin.addition.right.inverse (Bin.Positive W.modulus)),
               (Bin.addition.commutativity (Bin.Positive W.modulus) (W.to_bin &x - W.to_bin &y)%b)
               in &raised.
             ipso (disjoin _, &raised).
           }
           match (W.sign_bit (&x - &y)) with | Zero | One end |- sr.
           ++ match (W.sign_bit &x) with | Zero | One end |- sx.
              ** let proof grown :=
                   Bin.addition.order.accumulation 0%b (Bin.negate (W.to_bin W.Max)) (W.to_bin &x)
                     (Bin.negate (W.to_bin &y)) (sign.clear &x &sx) &above_y.
                 leibniz (Bin.addition.left.identity (Bin.negate (W.to_bin W.Max))) in &grown.
                 lemma large : (Bin.negate (W.to_bin W.Max) <= W.to_bin x - W.to_bin y)%b.
                 {
                   ipso &grown.
                 }
                 ex (Bin.order.strict.irreflexivity (Bin.Negative W.half)
                       (Bin.order.strict.transitivity &negated_below
                          (Comparable.order.mixed.left.transitivity &large &beneath)))
                   quodlibet.
              ** match (W.sign_bit &y) with | Zero | One end |- sy.
                 --- leibniz (W.flag.subtraction.specification &x &y), &sx, &sy, &sr in &f.
                     simpl in &f.
                     ex &f quodlibet.
                 --- lemma positive : (0 < Bin.negate (W.to_bin y))%b.
                     {
                       ipso (modus aequans (Bin.order.negation.strict.reversal (W.to_bin &y) 0%b),
                             (sign.set &y &sy)).
                     }
                     let proof grown :=
                       Bin.addition.order.strict.monotonicity (W.to_bin &x) 0%b
                         (Bin.negate (W.to_bin &y)) &positive.
                     leibniz (Bin.addition.right.identity (W.to_bin &x)) in &grown.
                     lemma large : (Bin.Negative W.half < W.to_bin x - W.to_bin y)%b.
                     {
                       ipso (Comparable.order.mixed.left.transitivity &low_x &grown).
                     }
                     ex (Bin.order.strict.irreflexivity (Bin.Negative W.half)
                           (Bin.order.strict.transitivity &large &beneath))
                       quodlibet.
           ++ ex (Bin.order.strict.irreflexivity 0%b
                   (Comparable.order.mixed.left.transitivity &nonnegative
                      (sign.set (&x - &y) &sr)))
                quodlibet.
        -- lemma inside
             : (Bin.Negative W.half <= W.to_bin x - W.to_bin y
                /\ W.to_bin x - W.to_bin y <= W.to_bin W.Max)%b.
           {
             lemma low : (Bin.Negative W.half <= W.to_bin x - W.to_bin y)%b.
             {
               match &remainder with | same | over end.
               ++ leibniz &same in |- *.
                  ipso (disjoin (refl (Bin.Negative W.half)), _).
               ++ ipso (disjoin _, &over).
             }
             ipso (conjoin &low, (disjoin _, &under)).
           }
           ipso &inside.
  - intro r.
    lemma same : W.to_bin (x - y) = (W.to_bin x - W.to_bin y)%b.
    {
      leibniz (wrapping.difference &x &y) in |- *.
      ipso (wrapping.retraction (W.to_bin &x - W.to_bin &y)%b &r).
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
        lemma positive : (0 < Bin.negate (W.to_bin y))%b.
        {
          ipso (modus aequans (Bin.order.negation.strict.reversal (W.to_bin &y) 0%b),
                (sign.set &y &sy)).
        }
        lemma grown : (0 < W.to_bin x - W.to_bin y)%b.
        {
          ipso (Bin.addition.order.mixed.monotonicity
                  0%b 0%b (W.to_bin &x) (Bin.negate (W.to_bin &y))
                  (sign.clear &x &sx) &positive).
        }
        ex (Bin.order.strict.irreflexivity 0%b (Bin.order.strict.transitivity &grown &negative))
          quodlibet.
      * (* [x] negative, [y] nonnegative, a nonnegative difference. *)
        let proof nonnegative := sign.clear (&x - &y) &sr.
        leibniz &same in &nonnegative.
        let proof shrunk :=
          Bin.addition.order.mixed.monotonicity (Bin.negate (W.to_bin &y)) (W.to_bin &x) 0%b 0%b
            (Bin.order.negation.reversal 0%b (W.to_bin &y) (sign.clear &y &sy)) (sign.set &x &sx).
        leibniz (Bin.addition.commutativity (Bin.negate (W.to_bin &y)) (W.to_bin &x)) in &shrunk.
        lemma negative : (W.to_bin x - W.to_bin y < 0)%b.
        {
          ipso &shrunk.
        }
        ex (Bin.order.strict.irreflexivity 0%b
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
      -> W.to_bin (x - y) = (W.to_bin x - W.to_bin y)%b.
Proof.
  intros x y f.
  leibniz (wrapping.difference &x &y) in |- *.
  ipso (wrapping.retraction (W.to_bin &x - W.to_bin &y)%b
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
    Bin.order.subtraction.left.monotonicity (W.to_bin &x) (W.to_bin &y) (W.to_bin &z) &g.
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
    Bin.order.subtraction.right.antitonicity (W.to_bin &x) (W.to_bin &y) (W.to_bin &z) &g.
  leibniz
    <- (overflow.subtraction.exactness &x &z &fz),
    <- (overflow.subtraction.exactness &x &y &fy)
    in &s.
  ipso (modus aequans (W.order.strict.specification (&x - &z) (&x - &y)), &s).
Qed.

End right. (* overflow.subtraction.right *)

End subtraction. (* overflow.subtraction *)

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
  : forall (x : W.T) . ~ (x = W.Min) -> W.to_bin (- x) = Bin.negate (W.to_bin x).
Proof.
  intros x h.
  match (bound.range &x) with | low high end.
  lemma above : (Bin.Negative W.half < W.to_bin x)%b.
  {
    match &low with | same | larger end.
    - lemma e : W.to_bin W.Min = W.to_bin x.
      {
        leibniz W.minimum.specification in |- *.
        ipso &same.
      }
      ex (&h (symm (injectivity &e))) quodlibet.
    - ipso &larger.
  }
  lemma lifted : - x = W.from_bin (Bin.negate (W.to_bin x)).
  {
    leibniz (wrapping.negation (W.to_bin &x)), (W.conversion.section &x) in |- *.
    quod idem est.
  }
  leibniz &lifted in |- *.
  lemma negated_low : (Bin.Negative W.half <= Bin.negate (W.to_bin x))%b.
  {
    let proof max_below : (W.to_bin W.Max < W.to_bin W.Max + 1)%b
      := Bin.order.increment.extensivity (W.to_bin W.Max).
    leibniz W.maximum.specification in &max_below.
    lemma negated_below : (Bin.Negative W.half < Bin.negate (W.to_bin W.Max))%b.
    {
      ipso (modus aequans
              (Bin.order.negation.strict.reversal (W.to_bin W.Max) (Bin.Positive W.half)),
              &max_below).
    }
    let proof reversed := Bin.order.negation.reversal (W.to_bin &x) (W.to_bin W.Max) &high.
    ipso (disjoin _, (Comparable.order.mixed.right.transitivity &negated_below &reversed)).
  }
  lemma negated_high : (Bin.negate (W.to_bin x) <= W.to_bin W.Max)%b.
  {
    lemma reversed : (Bin.negate (W.to_bin x) < Bin.Positive W.half)%b.
    {
      ipso (modus aequans
              (Bin.order.negation.strict.reversal (Bin.Negative W.half) (W.to_bin &x)), &above).
    }
    leibniz <- W.maximum.specification in &reversed.
    ipso (modus aequans (Bin.order.discreteness (Bin.negate (W.to_bin &x)) (W.to_bin W.Max)),
          &reversed).
  }
  ipso (wrapping.retraction (Bin.negate (W.to_bin &x)) (conjoin &negated_low, &negated_high)).
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
      modus aequans (Bin.order.negation.strict.reversal (W.to_bin &x) (W.to_bin &y)), &g.
    leibniz <- (negation.exactness &x &hx), <- (negation.exactness &y &hy) in &r.
    ipso (modus aequans (W.order.strict.specification (- &y) (- &x)), &r).
  - intro h.
    let proof g := modus aequans (W.order.strict.specification (- &y) (- &x)), &h.
    leibniz (negation.exactness &x &hx), (negation.exactness &y &hy) in &g.
    ipso (modus aequans (W.order.strict.specification &x &y),
          (modus aequans (Bin.order.negation.strict.reversal (W.to_bin &x) (W.to_bin &y)), &g)).
Qed.

End negation. (* negation *)

Module increment. (* increment *)

(* Away from [W.Max], the reading is below the greatest, so one more is in
 * range.
 *)
(* increment.exactness *)
Theorem exactness
  : forall (x : W.T) . ~ (x = W.Max) -> W.to_bin (x + W.One) = (W.to_bin x + 1)%b.
Proof.
  intros x h.
  match (bound.range &x) with | low high end.
  lemma below : (W.to_bin x < W.to_bin W.Max)%b.
  {
    match &high with | same | smaller end.
    - ex (&h (injectivity &same)) quodlibet.
    - ipso &smaller.
  }
  lemma summed : x + W.One = W.from_bin (W.to_bin x + 1)%b.
  {
    leibniz (wrapping.summation &x W.One), W.one.specification in |- *.
    quod idem est.
  }
  leibniz &summed in |- *.
  lemma raised_low : (Bin.Negative W.half <= W.to_bin x + 1)%b.
  {
    ipso (disjoin _, (Comparable.order.mixed.left.transitivity &low
                        (Bin.order.increment.extensivity (W.to_bin &x)))).
  }
  lemma raised_high : (W.to_bin x + 1 <= W.to_bin W.Max)%b.
  {
    ipso (modus aequans (Bin.order.increment.specification (W.to_bin &x) (W.to_bin W.Max)), &below).
  }
  ipso (wrapping.retraction (W.to_bin &x + 1)%b (conjoin &raised_low, &raised_high)).
Qed.

(* increment.extensivity *)
Theorem extensivity : forall (x : W.T) . ~ (x = W.Max) -> x < x + W.One.
Proof.
  intros x h.
  let proof g := Bin.order.increment.extensivity (W.to_bin &x).
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
    ex (Bin.order.strict.irreflexivity (W.to_bin W.Max)
          (Comparable.order.mixed.right.transitivity &g &high))
      quodlibet.
  }
  match (modus aequans (Bin.order.increment.specification (W.to_bin &x) (W.to_bin &y)), &g)
    with | same | smaller end.
  - lemma e : W.to_bin (x + W.One) = W.to_bin y.
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
          (Bin.order.strict.transitivity &g &l)).
Qed.

End increment. (* increment *)

Module decrement. (* decrement *)

(* Away from [W.Min], the reading is above the least, so one less is in range. *)
(* decrement.exactness *)
Theorem exactness
  : forall (x : W.T) . ~ (x = W.Min) -> W.to_bin (x - W.One) = (W.to_bin x - 1)%b.
Proof.
  intros x h.
  match (bound.range &x) with | low high end.
  lemma above : (Bin.Negative W.half < W.to_bin x)%b.
  {
    match &low with | same | larger end.
    - lemma e : W.to_bin W.Min = W.to_bin x.
      {
        leibniz W.minimum.specification in |- *.
        ipso &same.
      }
      ex (&h (symm (injectivity &e))) quodlibet.
    - ipso &larger.
  }
  lemma differenced : x - W.One = W.from_bin (W.to_bin x - 1)%b.
  {
    leibniz (wrapping.difference &x W.One), W.one.specification in |- *.
    quod idem est.
  }
  leibniz &differenced in |- *.
  lemma lowered_low : (Bin.Negative W.half <= W.to_bin x - 1)%b.
  {
    let proof least :=
      modus aequans (Bin.order.increment.specification (Bin.Negative W.half) (W.to_bin &x)), &above.
    lemma restored : (Bin.Negative W.half + 1 - 1 = Bin.Negative W.half)%b.
    {
      leibniz
        (Bin.subtraction.specification (Bin.Negative W.half + 1)%b 1%b),
        (Bin.addition.associativity (Bin.Negative W.half) 1%b (Bin.negate 1%b)),
        (Bin.addition.right.inverse 1%b),
        (Bin.addition.right.identity (Bin.Negative W.half))
        in |- *.
      quod idem est.
    }
    match &least with | same | smaller end.
    - leibniz <- &same, &restored in |- *.
      ipso (disjoin (refl (Bin.Negative W.half)), _).
    - let proof lowered :=
        Bin.order.subtraction.left.monotonicity 1%b (Bin.Negative W.half + 1)%b (W.to_bin &x)
          &smaller.
      leibniz &restored in &lowered.
      ipso (disjoin _, &lowered).
  }
  lemma lowered_high : (W.to_bin x - 1 <= W.to_bin W.Max)%b.
  {
    ipso (disjoin _, (Comparable.order.mixed.right.transitivity
                        (Bin.order.decrement.extensivity (W.to_bin &x)) &high)).
  }
  ipso (wrapping.retraction (W.to_bin &x - 1)%b (conjoin &lowered_low, &lowered_high)).
Qed.

(* decrement.extensivity *)
Theorem extensivity : forall (x : W.T) . ~ (x = W.Min) -> x - W.One < x.
Proof.
  intros x h.
  let proof g := Bin.order.decrement.extensivity (W.to_bin &x).
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
        (Bin.order.strict.transitivity &g1 &g2)).
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
  let proof s := Bin.comparison.specification (W.to_bin &x) (W.to_bin &y).
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
      ipso (modus aequans &equality, (congru W.to_bin, &e)).
Qed.

(* comparison.antisymmetry *)
Theorem antisymmetry
  : forall (x : W.T) (y : W.T) . W.compare x y = Comparison.transpose (W.compare y x).
Proof.
  intros x y.
  leibniz (W.conversion.comparison &x &y), (W.conversion.comparison &y &x) in |- *.
  ipso (Bin.comparison.antisymmetry (W.to_bin &x) (W.to_bin &y)).
Qed.

End comparison. (* comparison *)

End Laws.
