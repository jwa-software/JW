(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

From JW Require Import Core.All.
From JW Require Import Data.Comparable.
From JW Require Import Data.Machine.Bit.
From JW Require Import Data.Number.Binary.BinBase.
From JW Require Import Data.Number.Binary.BinWithZero.
From JW Require Import Data.Product.
From JW Require Import Tactics.Equation.
From JW Require Import Tactics.Modus.
From JW Require Import Tactics.Witness.

(* What an unsigned fixed-width integer provides: its operations, its
 * constants, and facts about them. Each [Parameter] is a field that every
 * width defines or proves, not an axiom. The operations and constants are
 * [Inline]: a width that includes [Laws] gets laws stated with its own
 * operations, such as [UInt8.add], so [leibniz] can rewrite with them.
 *)
Module Type Width.

Parameter Inline T : Type.
Parameter Inline Zero : T.
Parameter Inline One : T.
Parameter Inline Max : T.
Parameter Inline to_bin_with_zero : T -> BinWithZero.
Parameter Inline add : T -> T -> T.
Parameter Inline sub : T -> T -> T.
Parameter Inline LessThan : T -> T -> Prop.
Parameter Inline LessOrEqual : T -> T -> Prop.
Parameter Inline add_with_carry : Bit -> T -> T -> Product Bit T.
Parameter Inline sub_with_borrow : Bit -> T -> T -> Product Bit T.
Parameter Inline modulus : BinBase.

Module order. (* order *)

Module strict. (* order.strict *)

Parameter specification
  : forall (x : T) (y : T) .
      LessThan x y <-> (to_bin_with_zero x < to_bin_with_zero y)%bin_with_zero.

End strict. (* order.strict *)

Parameter specification
  : forall (x : T) (y : T) . LessOrEqual x y <-> x = y \/ LessThan x y.

End order. (* order *)

Module conversion. (* conversion *)

Parameter zero
  : to_bin_with_zero Zero = 0%bin_with_zero.
Parameter one
  : to_bin_with_zero One = 1%bin_with_zero.
Parameter boundedness
  : forall (x : T) . (to_bin_with_zero x < BinWithZero.Positive modulus)%bin_with_zero.
Parameter injectivity
  : forall {x : T} {y : T} . to_bin_with_zero x = to_bin_with_zero y -> x = y.

End conversion. (* conversion *)

Module flag. (* flag *)

Module addition. (* flag.addition *)

Parameter specification
  : forall (x : T) (y : T) .
      (to_bin_with_zero x + to_bin_with_zero y
       = BinWithZero.Positive modulus
           * Bit.to_bin_with_zero (pi_1 (add_with_carry 0 x y))%product
         + to_bin_with_zero (add x y))%bin_with_zero.

End addition. (* flag.addition *)

Module subtraction. (* flag.subtraction *)

Parameter specification
  : forall (x : T) (y : T) .
      (to_bin_with_zero x
         + BinWithZero.Positive modulus
             * Bit.to_bin_with_zero (pi_1 (sub_with_borrow 0 x y))%product
       = to_bin_with_zero y + to_bin_with_zero (sub x y))%bin_with_zero.

End subtraction. (* flag.subtraction *)

End flag. (* flag *)

Module maximum. (* maximum *)

Parameter specification
  : (to_bin_with_zero Max + 1 = BinWithZero.Positive modulus)%bin_with_zero.

End maximum. (* maximum *)

End Width.

(* The laws of the bounds, of the carry and the borrow, and of the successor,
 * for every width.
 *)
Module Laws (W : Width).

(* [only parsing] keeps goals printing the operations by name; the scope is
 * bound to [W.T] here only, so an included law leaves the width's own scope
 * alone.
 *)
Local Notation "x + y" := (W.add x y) (only parsing)
  : jw_unsigned_scope.
Local Notation "x - y" := (W.sub x y) (only parsing)
  : jw_unsigned_scope.
Local Notation "x < y" := (W.LessThan x y) (only parsing)
  : jw_unsigned_scope.
Local Notation "x <= y" := (W.LessOrEqual x y) (only parsing)
  : jw_unsigned_scope.
#[local] Bind Scope jw_unsigned_scope with W.T.
Local Open Scope jw_unsigned_scope.

(* The value keeps the order. *)
Lemma preservation
  : forall (x : W.T) (y : W.T) .
      x <= y -> (W.to_bin_with_zero x <= W.to_bin_with_zero y)%bin_with_zero.
Proof.
  intros x y h.
  match (modus aequans (W.order.specification &x &y), &h) with | e | smaller end.
  - leibniz &e in |- *.
    ipso (disjoin (refl (W.to_bin_with_zero &y)), _).
  - ipso (disjoin _, (modus aequans (W.order.strict.specification &x &y), &smaller)).
Qed.

(* The order of the values is the order of the type. *)
Lemma reflection
  : forall (x : W.T) (y : W.T) .
      (W.to_bin_with_zero x <= W.to_bin_with_zero y)%bin_with_zero -> x <= y.
Proof.
  intros x y h.
  match &h with | e | smaller end.
  - ipso (modus aequans (W.order.specification &x &y),
          (disjoin (W.conversion.injectivity &e), _)).
  - ipso (modus aequans (W.order.specification &x &y),
          (disjoin _, (modus aequans (W.order.strict.specification &x &y), &smaller))).
Qed.

Module bound. (* bound *)

(* A value above [W.Max] would be at least [W.Max + 1], the modulus. *)
(* bound.range *)
Theorem range
  : forall (x : W.T) . (W.to_bin_with_zero x <= W.to_bin_with_zero W.Max)%bin_with_zero.
Proof.
  intro x.
  lemma above : ~ (W.to_bin_with_zero W.Max < W.to_bin_with_zero x)%bin_with_zero.
  {
    simpl (~ _) in |- *.
    intro g.
    let proof s :=
      BinWithZero.order.succession (W.to_bin_with_zero W.Max) (W.to_bin_with_zero &x) &g.
    leibniz W.maximum.specification in &s.
    ex (BinWithZero.order.strict.irreflexivity (BinWithZero.Positive W.modulus)
          (Comparable.order.mixed.left.transitivity &s (W.conversion.boundedness &x)))
      quodlibet.
  }
  ipso (modus aequans
          (Comparable.order.strict.negation
             (W.to_bin_with_zero W.Max) (W.to_bin_with_zero &x)),
          &above).
Qed.

(* bound.lower *)
Theorem lower : forall (x : W.T) . W.Zero <= x.
Proof.
  intro x.
  lemma low : (W.to_bin_with_zero W.Zero <= W.to_bin_with_zero x)%bin_with_zero.
  {
    leibniz W.conversion.zero in |- *.
    match (W.to_bin_with_zero &x) with | | p end.
    - ipso (disjoin (refl 0%bin_with_zero), _).
    - lemma facto : (0 < BinWithZero.Positive p)%bin_with_zero.
      {
        simpl BinWithZero.LessThan in |- *.
        exists &p.
        ipso (refl (BinWithZero.Positive &p)).
      }
      ipso (disjoin _, &facto).
  }
  ipso (reflection W.Zero &x &low).
Qed.

(* bound.upper *)
Theorem upper : forall (x : W.T) . x <= W.Max.
Proof.
  intro x.
  ipso (reflection &x W.Max (bound.range &x)).
Qed.

End bound. (* bound *)

Module overflow. (* overflow *)

Module addition. (* overflow.addition *)

(* A clear carry leaves the sum as it is, below the modulus; a set one takes
 * the modulus away, so the sum was at least the modulus.
 *)
(* overflow.addition.specification *)
Theorem specification
  : forall (x : W.T) (y : W.T) .
      (pi_1 (W.add_with_carry 0 x y))%product = 0%bit
      <-> (W.to_bin_with_zero x + W.to_bin_with_zero y
           < BinWithZero.Positive W.modulus)%bin_with_zero.
Proof.
  intros x y.
  let proof s := W.flag.addition.specification &x &y.
  match ((pi_1 (W.add_with_carry 0 &x &y))%product) with | Zero | One end |- f.
  - let proof t
      : (W.to_bin_with_zero x + W.to_bin_with_zero y = W.to_bin_with_zero (x + y))%bin_with_zero
      := &s.
    divide et impera.
    + intro e.
      leibniz &t in |- *.
      ipso (W.conversion.boundedness (&x + &y)).
    + intro h.
      quod idem est.
  - let proof t
      : (W.to_bin_with_zero x + W.to_bin_with_zero y
         = BinWithZero.Positive W.modulus * BinWithZero.Positive BinBase.One
           + W.to_bin_with_zero (x + y))%bin_with_zero
      := &s.
    match (BinWithZero.multiplication.identity (BinWithZero.Positive W.modulus)) with | _ r end.
    leibniz &r in &t.
    divide et impera.
    + intro e.
      ex &e quodlibet.
    + intro h.
      let proof at_least :=
        BinWithZero.addition.right.order.extensivity
          (W.to_bin_with_zero (&x + &y)) (BinWithZero.Positive W.modulus).
      leibniz
        (BinWithZero.addition.commutativity
           (W.to_bin_with_zero (&x + &y)) (BinWithZero.Positive W.modulus)),
        <- &t
        in &at_least.
      ex (BinWithZero.order.strict.irreflexivity (BinWithZero.Positive W.modulus)
            (Comparable.order.mixed.left.transitivity &at_least &h))
        quodlibet.
Qed.

(* overflow.addition.exactness *)
Theorem exactness
  : forall (x : W.T) (y : W.T) .
      (pi_1 (W.add_with_carry 0 x y))%product = 0%bit
      -> (W.to_bin_with_zero (x + y) = W.to_bin_with_zero x + W.to_bin_with_zero y)%bin_with_zero.
Proof.
  intros x y f.
  let proof s := W.flag.addition.specification &x &y.
  leibniz &f in &s.
  let proof t
    : (W.to_bin_with_zero x + W.to_bin_with_zero y = W.to_bin_with_zero (x + y))%bin_with_zero
    := &s.
  ipso (symm &t).
Qed.

(* Two clear carries make both sums exact, and [BinWithZero]'s addition keeps
 * the order.
 *)
(* overflow.addition.monotonicity *)
Theorem monotonicity
  : forall (x : W.T) (y : W.T) (z : W.T) .
      (pi_1 (W.add_with_carry 0 x y))%product = 0%bit
      -> (pi_1 (W.add_with_carry 0 x z))%product = 0%bit
      -> y < z -> x + y < x + z.
Proof.
  intros x y z fy fz h.
  let proof g := modus aequans (W.order.strict.specification &y &z), &h.
  lemma same : (W.to_bin_with_zero x <= W.to_bin_with_zero x)%bin_with_zero.
  {
    ipso (disjoin (refl (W.to_bin_with_zero &x)), _).
  }
  let proof s :=
    BinWithZero.addition.order.strict.monotonicity
      (W.to_bin_with_zero &x) (W.to_bin_with_zero &y) (W.to_bin_with_zero &x)
      (W.to_bin_with_zero &z) &same &g.
  leibniz <- (overflow.addition.exactness &x &y &fy), <- (overflow.addition.exactness &x &z &fz)
    in &s.
  ipso (modus aequans (W.order.strict.specification (&x + &y) (&x + &z)), &s).
Qed.

End addition. (* overflow.addition *)

Module subtraction. (* overflow.subtraction *)

(* A clear borrow leaves [x] as [y] plus the difference, so [y <= x]; a set
 * one adds the modulus to [x], which [y] and a difference below the modulus
 * cannot reach when [y <= x].
 *)
(* overflow.subtraction.specification *)
Theorem specification
  : forall (x : W.T) (y : W.T) .
      (pi_1 (W.sub_with_borrow 0 x y))%product = 0%bit <-> y <= x.
Proof.
  intros x y.
  let proof s := W.flag.subtraction.specification &x &y.
  match ((pi_1 (W.sub_with_borrow 0 &x &y))%product) with | Zero | One end |- f.
  - let proof t
      : (W.to_bin_with_zero x + 0 = W.to_bin_with_zero y + W.to_bin_with_zero (x - y))%bin_with_zero
      := &s.
    match (BinWithZero.addition.identity (W.to_bin_with_zero &x)) with | _ r end.
    leibniz &r in &t.
    divide et impera.
    + intro e.
      let proof g :=
        BinWithZero.addition.right.order.extensivity
          (W.to_bin_with_zero (&x - &y)) (W.to_bin_with_zero &y).
      leibniz
        (BinWithZero.addition.commutativity
           (W.to_bin_with_zero (&x - &y)) (W.to_bin_with_zero &y)),
        <- &t
        in &g.
      ipso (reflection &y &x &g).
    + intro h.
      quod idem est.
  - let proof t
      : (W.to_bin_with_zero x + BinWithZero.Positive W.modulus * BinWithZero.Positive BinBase.One
         = W.to_bin_with_zero y + W.to_bin_with_zero (x - y))%bin_with_zero
      := &s.
    match (BinWithZero.multiplication.identity (BinWithZero.Positive W.modulus)) with | _ r end.
    leibniz &r in &t.
    divide et impera.
    + intro e.
      ex &e quodlibet.
    + intro h.
      let proof g :=
        BinWithZero.addition.order.strict.monotonicity
          (W.to_bin_with_zero &y) (W.to_bin_with_zero (&x - &y))
          (W.to_bin_with_zero &x) (BinWithZero.Positive W.modulus)
          (preservation &y &x &h) (W.conversion.boundedness (&x - &y)).
      leibniz <- &t in &g.
      ex (BinWithZero.order.strict.irreflexivity
            (W.to_bin_with_zero &x + BinWithZero.Positive W.modulus)%bin_with_zero &g)
        quodlibet.
Qed.

(* overflow.subtraction.exactness *)
Theorem exactness
  : forall (x : W.T) (y : W.T) .
      (pi_1 (W.sub_with_borrow 0 x y))%product = 0%bit
      -> (W.to_bin_with_zero y + W.to_bin_with_zero (x - y) = W.to_bin_with_zero x)%bin_with_zero.
Proof.
  intros x y f.
  let proof s := W.flag.subtraction.specification &x &y.
  leibniz &f in &s.
  let proof t
    : (W.to_bin_with_zero x + 0 = W.to_bin_with_zero y + W.to_bin_with_zero (x - y))%bin_with_zero
    := &s.
  match (BinWithZero.addition.identity (W.to_bin_with_zero &x)) with | _ r end.
  leibniz &r in &t.
  ipso (symm &t).
Qed.

End subtraction. (* overflow.subtraction *)

End overflow. (* overflow *)

Module increment. (* increment *)

(* Away from [W.Max], the value is below the greatest, so one more is below
 * the modulus and the carry is clear.
 *)
(* increment.exactness *)
Theorem exactness
  : forall (x : W.T) .
      ~ (x = W.Max) -> (W.to_bin_with_zero (x + W.One) = W.to_bin_with_zero x + 1)%bin_with_zero.
Proof.
  intros x h.
  match (bound.range &x) with | same | smaller end.
  - ex (&h (W.conversion.injectivity &same)) quodlibet.
  - lemma unit : (1 <= 1)%bin_with_zero.
    {
      ipso (disjoin (refl 1%bin_with_zero), _).
    }
    lemma below
      : (W.to_bin_with_zero x + W.to_bin_with_zero W.One
         < BinWithZero.Positive W.modulus)%bin_with_zero.
    {
      leibniz W.conversion.one in |- *.
      let proof s :=
        BinWithZero.addition.order.strict.monotonicity
          1%bin_with_zero (W.to_bin_with_zero &x) 1%bin_with_zero (W.to_bin_with_zero W.Max)
          &unit &smaller.
      leibniz
        (BinWithZero.addition.commutativity 1%bin_with_zero (W.to_bin_with_zero &x)),
        (BinWithZero.addition.commutativity 1%bin_with_zero (W.to_bin_with_zero W.Max)),
        W.maximum.specification
        in &s.
      ipso &s.
    }
    let proof clear := modus aequans (overflow.addition.specification &x W.One), &below.
    let proof e := overflow.addition.exactness &x W.One &clear.
    leibniz W.conversion.one in &e.
    ipso &e.
Qed.

(* increment.extensivity *)
Theorem extensivity : forall (x : W.T) . ~ (x = W.Max) -> x < x + W.One.
Proof.
  intros x h.
  lemma g : (W.to_bin_with_zero x < W.to_bin_with_zero x + 1)%bin_with_zero.
  {
    simpl BinWithZero.LessThan in |- *.
    exists BinBase.One.
    ipso (refl (W.to_bin_with_zero &x + 1)%bin_with_zero).
  }
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
    ex (BinWithZero.order.strict.irreflexivity (W.to_bin_with_zero W.Max)
          (Comparable.order.mixed.right.transitivity &g (bound.range &y)))
      quodlibet.
  }
  let proof s := BinWithZero.order.succession (W.to_bin_with_zero &x) (W.to_bin_with_zero &y) &g.
  lemma raised : (W.to_bin_with_zero (x + W.One) <= W.to_bin_with_zero y)%bin_with_zero.
  {
    leibniz (increment.exactness &x &below) in |- *.
    ipso &s.
  }
  ipso (reflection (&x + W.One) &y &raised).
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
          (BinWithZero.order.strict.transitivity &g &l)).
Qed.

End increment. (* increment *)

Module decrement. (* decrement *)

(* Away from [W.Zero], the value is at least one, so the borrow is clear and
 * one less, plus one, gives the value back.
 *)
(* decrement.exactness *)
Theorem exactness
  : forall (x : W.T) .
      ~ (x = W.Zero)
      -> (W.to_bin_with_zero (x - W.One) + 1 = W.to_bin_with_zero x)%bin_with_zero.
Proof.
  intros x h.
  let proof low := preservation W.Zero &x (bound.lower &x).
  lemma above : (0 < W.to_bin_with_zero x)%bin_with_zero.
  {
    match &low with | same | larger end.
    - ex (&h (symm (W.conversion.injectivity &same))) quodlibet.
    - leibniz W.conversion.zero in &larger.
      ipso &larger.
  }
  let proof s := BinWithZero.order.succession 0%bin_with_zero (W.to_bin_with_zero &x) &above.
  lemma at_least : (W.to_bin_with_zero W.One <= W.to_bin_with_zero x)%bin_with_zero.
  {
    leibniz W.conversion.one in |- *.
    ipso &s.
  }
  let proof clear :=
    modus aequans (overflow.subtraction.specification &x W.One), (reflection W.One &x &at_least).
  let proof e := overflow.subtraction.exactness &x W.One &clear.
  leibniz
    W.conversion.one,
    (BinWithZero.addition.commutativity 1%bin_with_zero (W.to_bin_with_zero (&x - W.One)))
    in &e.
  ipso &e.
Qed.

(* decrement.extensivity *)
Theorem extensivity : forall (x : W.T) . ~ (x = W.Zero) -> x - W.One < x.
Proof.
  intros x h.
  lemma g
    : (W.to_bin_with_zero (x - W.One) < W.to_bin_with_zero (x - W.One) + 1)%bin_with_zero.
  {
    simpl BinWithZero.LessThan in |- *.
    exists BinBase.One.
    ipso (refl (W.to_bin_with_zero (&x - W.One) + 1)%bin_with_zero).
  }
  leibniz (decrement.exactness &x &h) in &g.
  ipso (modus aequans (W.order.strict.specification (&x - W.One) &x), &g).
Qed.

End decrement. (* decrement *)

End Laws.
