(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

From JW Require Import Core.All.
From JW Require Import Data.Base.Comparison.
From JW Require Import Data.Comparable.
From JW Require Import Data.Machine.Bit.
From JW Require Import Data.Number.Binary.BinBase.
From JW Require Import Data.Number.Binary.Bin0.
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
Parameter Inline to_b0 : T -> Bin0.
Parameter Inline add : T -> T -> T.
Parameter Inline sub : T -> T -> T.
Parameter Inline LessThan : T -> T -> Prop.
Parameter Inline LessOrEqual : T -> T -> Prop.
Parameter Inline add_with_carry : Bit -> T -> T -> Product Bit T.
Parameter Inline sub_with_borrow : Bit -> T -> T -> Product Bit T.
Parameter Inline compare : T -> T -> Comparison.
Parameter Inline mul : T -> T -> T.
Parameter Inline mul_with_overflow : T -> T -> Product Bit T.
Parameter Inline modulus : BinBase.

Module order. (* order *)

Module strict. (* order.strict *)

Parameter specification
  : forall (x : T) (y : T) .
      LessThan x y <-> (to_b0 x < to_b0 y)%b0.

End strict. (* order.strict *)

Parameter specification
  : forall (x : T) (y : T) . LessOrEqual x y <-> x = y \/ LessThan x y.

End order. (* order *)

Module conversion. (* conversion *)

Parameter zero
  : to_b0 Zero = 0%b0.
Parameter one
  : to_b0 One = 1%b0.
Parameter boundedness
  : forall (x : T) . (to_b0 x < Bin0.Positive modulus)%b0.
Parameter injectivity
  : forall {x : T} {y : T} . to_b0 x = to_b0 y -> x = y.
Parameter comparison
  : forall (x : T) (y : T) .
      compare x y = Bin0.compare (to_b0 x) (to_b0 y).
Parameter multiplication
  : forall (x : T) (y : T) .
      (to_b0 (mul x y)
       = (to_b0 x * to_b0 y) %. modulus)%b0.

End conversion. (* conversion *)

Module flag. (* flag *)

Module addition. (* flag.addition *)

Parameter specification
  : forall (x : T) (y : T) .
      (to_b0 x + to_b0 y
       = Bin0.Positive modulus
           * Bit.to_b0 (pi_1 (add_with_carry 0 x y))%product
         + to_b0 (add x y))%b0.

End addition. (* flag.addition *)

Module subtraction. (* flag.subtraction *)

Parameter specification
  : forall (x : T) (y : T) .
      (to_b0 x
         + Bin0.Positive modulus
             * Bit.to_b0 (pi_1 (sub_with_borrow 0 x y))%product
       = to_b0 y + to_b0 (sub x y))%b0.

End subtraction. (* flag.subtraction *)

Module multiplication. (* flag.multiplication *)

Parameter specification
  : forall (x : T) (y : T) .
      mul_with_overflow x y
      = (match Bin0.compare (to_b0 x * to_b0 y)%b0
                 (Bin0.Positive modulus) with
         | Comparison.Lt => 0%bit
         | Comparison.Eq => 1%bit
         | Comparison.Gt => 1%bit
         end,
         mul x y)%product.

End multiplication. (* flag.multiplication *)

End flag. (* flag *)

Module maximum. (* maximum *)

Parameter specification
  : (to_b0 Max + 1 = Bin0.Positive modulus)%b0.

End maximum. (* maximum *)

End Width.

(* The laws of the bounds, of the carry and the borrow, of the successor, of
 * the order and of the comparison, for every width.
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
Local Notation "x * y" := (W.mul x y) (only parsing)
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
      x <= y -> (W.to_b0 x <= W.to_b0 y)%b0.
Proof.
  intros x y h.
  match (modus aequans (W.order.specification &x &y), &h) with | e | smaller end.
  - leibniz &e in |- *.
    ipso (disjoin (refl (W.to_b0 &y)), _).
  - ipso (disjoin _, (modus aequans (W.order.strict.specification &x &y), &smaller)).
Qed.

(* The order of the values is the order of the type. *)
Lemma reflection
  : forall (x : W.T) (y : W.T) .
      (W.to_b0 x <= W.to_b0 y)%b0 -> x <= y.
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
  : forall (x : W.T) . (W.to_b0 x <= W.to_b0 W.Max)%b0.
Proof.
  intro x.
  lemma above : ~ (W.to_b0 W.Max < W.to_b0 x)%b0.
  {
    simpl (~ _) in |- *.
    intro g.
    let proof s :=
      Bin0.order.succession (W.to_b0 W.Max) (W.to_b0 &x) &g.
    leibniz W.maximum.specification in &s.
    ex (Bin0.order.strict.irreflexivity (Bin0.Positive W.modulus)
          (Comparable.order.mixed.left.transitivity &s (W.conversion.boundedness &x)))
      quodlibet.
  }
  ipso (modus aequans
          (Comparable.order.strict.negation
             (W.to_b0 W.Max) (W.to_b0 &x)),
          &above).
Qed.

(* bound.lower *)
Theorem lower : forall (x : W.T) . W.Zero <= x.
Proof.
  intro x.
  lemma low : (W.to_b0 W.Zero <= W.to_b0 x)%b0.
  {
    leibniz W.conversion.zero in |- *.
    match (W.to_b0 &x) with | | p end.
    - ipso (disjoin (refl 0%b0), _).
    - lemma facto : (0 < Bin0.Positive p)%b0.
      {
        simpl Bin0.LessThan in |- *.
        exists &p.
        ipso (refl (Bin0.Positive &p)).
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
      <-> (W.to_b0 x + W.to_b0 y
           < Bin0.Positive W.modulus)%b0.
Proof.
  intros x y.
  let proof s := W.flag.addition.specification &x &y.
  match ((pi_1 (W.add_with_carry 0 &x &y))%product) with | Zero | One end |- f.
  - let proof t
      : (W.to_b0 x + W.to_b0 y = W.to_b0 (x + y))%b0
      := &s.
    divide et impera.
    + intro e.
      leibniz &t in |- *.
      ipso (W.conversion.boundedness (&x + &y)).
    + intro h.
      quod idem est.
  - let proof t
      : (W.to_b0 x + W.to_b0 y
         = Bin0.Positive W.modulus * Bin0.Positive BinBase.One
           + W.to_b0 (x + y))%b0
      := &s.
    match (Bin0.multiplication.identity (Bin0.Positive W.modulus)) with | _ r end.
    leibniz &r in &t.
    divide et impera.
    + intro e.
      ex &e quodlibet.
    + intro h.
      let proof at_least :=
        Bin0.addition.right.order.extensivity
          (W.to_b0 (&x + &y)) (Bin0.Positive W.modulus).
      leibniz
        (Bin0.addition.commutativity
           (W.to_b0 (&x + &y)) (Bin0.Positive W.modulus)),
        <- &t
        in &at_least.
      ex (Bin0.order.strict.irreflexivity (Bin0.Positive W.modulus)
            (Comparable.order.mixed.left.transitivity &at_least &h))
        quodlibet.
Qed.

(* overflow.addition.exactness *)
Theorem exactness
  : forall (x : W.T) (y : W.T) .
      (pi_1 (W.add_with_carry 0 x y))%product = 0%bit
      -> (W.to_b0 (x + y) = W.to_b0 x + W.to_b0 y)%b0.
Proof.
  intros x y f.
  let proof s := W.flag.addition.specification &x &y.
  leibniz &f in &s.
  let proof t
    : (W.to_b0 x + W.to_b0 y = W.to_b0 (x + y))%b0
    := &s.
  ipso (symm &t).
Qed.

(* Two clear carries make both sums exact, and [Bin0]'s addition keeps
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
  lemma same : (W.to_b0 x <= W.to_b0 x)%b0.
  {
    ipso (disjoin (refl (W.to_b0 &x)), _).
  }
  let proof s :=
    Bin0.addition.order.strict.monotonicity
      (W.to_b0 &x) (W.to_b0 &y) (W.to_b0 &x)
      (W.to_b0 &z) &same &g.
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
      : (W.to_b0 x + 0 = W.to_b0 y + W.to_b0 (x - y))%b0
      := &s.
    match (Bin0.addition.identity (W.to_b0 &x)) with | _ r end.
    leibniz &r in &t.
    divide et impera.
    + intro e.
      let proof g :=
        Bin0.addition.right.order.extensivity
          (W.to_b0 (&x - &y)) (W.to_b0 &y).
      leibniz
        (Bin0.addition.commutativity
           (W.to_b0 (&x - &y)) (W.to_b0 &y)),
        <- &t
        in &g.
      ipso (reflection &y &x &g).
    + intro h.
      quod idem est.
  - let proof t
      : (W.to_b0 x + Bin0.Positive W.modulus * Bin0.Positive BinBase.One
         = W.to_b0 y + W.to_b0 (x - y))%b0
      := &s.
    match (Bin0.multiplication.identity (Bin0.Positive W.modulus)) with | _ r end.
    leibniz &r in &t.
    divide et impera.
    + intro e.
      ex &e quodlibet.
    + intro h.
      let proof g :=
        Bin0.addition.order.strict.monotonicity
          (W.to_b0 &y) (W.to_b0 (&x - &y))
          (W.to_b0 &x) (Bin0.Positive W.modulus)
          (preservation &y &x &h) (W.conversion.boundedness (&x - &y)).
      leibniz <- &t in &g.
      ex (Bin0.order.strict.irreflexivity
            (W.to_b0 &x + Bin0.Positive W.modulus)%b0 &g)
        quodlibet.
Qed.

(* overflow.subtraction.exactness *)
Theorem exactness
  : forall (x : W.T) (y : W.T) .
      (pi_1 (W.sub_with_borrow 0 x y))%product = 0%bit
      -> (W.to_b0 y + W.to_b0 (x - y) = W.to_b0 x)%b0.
Proof.
  intros x y f.
  let proof s := W.flag.subtraction.specification &x &y.
  leibniz &f in &s.
  let proof t
    : (W.to_b0 x + 0 = W.to_b0 y + W.to_b0 (x - y))%b0
    := &s.
  match (Bin0.addition.identity (W.to_b0 &x)) with | _ r end.
  leibniz &r in &t.
  ipso (symm &t).
Qed.

End subtraction. (* overflow.subtraction *)

Module multiplication. (* overflow.multiplication *)

(* The flag is clear exactly when [Bin0.compare] puts the product of the
 * values below the modulus.
 *)
(* overflow.multiplication.specification *)
Theorem specification
  : forall (x : W.T) (y : W.T) .
      (pi_1 (W.mul_with_overflow x y))%product = 0%bit
      <-> (W.to_b0 x * W.to_b0 y
           < Bin0.Positive W.modulus)%b0.
Proof.
  intros x y.
  leibniz (W.flag.multiplication.specification &x &y) in |- *.
  let proof s :=
    Bin0.comparison.specification
      (W.to_b0 &x * W.to_b0 &y)%b0
      (Bin0.Positive W.modulus).
  match &s with | strict _ end.
  match (Bin0.compare (W.to_b0 &x * W.to_b0 &y)%b0
           (Bin0.Positive W.modulus))
    with | Lt | Eq | Gt end |- c.
  - divide et impera.
    + intro e.
      ipso (modus aequans &strict, (refl Comparison.Lt)).
    + intro h.
      ipso (refl 0%bit).
  - divide et impera.
    + intro e.
      simpl in &e.
      ex &e quodlibet.
    + intro h.
      let proof l := modus aequans &strict, &h.
      ex &l quodlibet.
  - divide et impera.
    + intro e.
      simpl in &e.
      ex &e quodlibet.
    + intro h.
      let proof l := modus aequans &strict, &h.
      ex &l quodlibet.
Qed.

(* A clear flag puts the product below the modulus, where the remainder leaves
 * it as it is.
 *)
(* overflow.multiplication.exactness *)
Theorem exactness
  : forall (x : W.T) (y : W.T) .
      (pi_1 (W.mul_with_overflow x y))%product = 0%bit
      -> (W.to_b0 (x * y)
          = W.to_b0 x * W.to_b0 y)%b0.
Proof.
  intros x y f.
  let proof h := modus aequans (overflow.multiplication.specification &x &y), &f.
  leibniz
    (W.conversion.multiplication &x &y),
    (Bin0.modulo.identity
       (W.to_b0 &x * W.to_b0 &y)%b0 W.modulus &h)
    in |- *.
  quod idem est.
Qed.

(* Two clear flags make both products exact, and a positive factor keeps the
 * order of [Bin0].
 *)
(* overflow.multiplication.monotonicity *)
Theorem monotonicity
  : forall (x : W.T) (y : W.T) (z : W.T) .
      (pi_1 (W.mul_with_overflow x y))%product = 0%bit
      -> (pi_1 (W.mul_with_overflow x z))%product = 0%bit
      -> W.Zero < x -> y < z -> x * y < x * z.
Proof.
  intros x y z fy fz hx h.
  let proof g := modus aequans (W.order.strict.specification &y &z), &h.
  let proof k := modus aequans (W.order.strict.specification W.Zero &x), &hx.
  leibniz W.conversion.zero in &k.
  let proof s :=
    Bin0.multiplication.left.order.strict.monotonicity
      (W.to_b0 &x) (W.to_b0 &y) (W.to_b0 &z) &k &g.
  leibniz
    <- (overflow.multiplication.exactness &x &y &fy),
    <- (overflow.multiplication.exactness &x &z &fz)
    in &s.
  ipso (modus aequans (W.order.strict.specification (&x * &y) (&x * &z)), &s).
Qed.

End multiplication. (* overflow.multiplication *)

End overflow. (* overflow *)

Module increment. (* increment *)

(* Away from [W.Max], the value is below the greatest, so one more is below
 * the modulus and the carry is clear.
 *)
(* increment.exactness *)
Theorem exactness
  : forall (x : W.T) .
      ~ (x = W.Max) -> (W.to_b0 (x + W.One) = W.to_b0 x + 1)%b0.
Proof.
  intros x h.
  match (bound.range &x) with | same | smaller end.
  - ex (&h (W.conversion.injectivity &same)) quodlibet.
  - lemma unit : (1 <= 1)%b0.
    {
      ipso (disjoin (refl 1%b0), _).
    }
    lemma below
      : (W.to_b0 x + W.to_b0 W.One
         < Bin0.Positive W.modulus)%b0.
    {
      leibniz W.conversion.one in |- *.
      let proof s :=
        Bin0.addition.order.strict.monotonicity
          1%b0 (W.to_b0 &x) 1%b0 (W.to_b0 W.Max)
          &unit &smaller.
      leibniz
        (Bin0.addition.commutativity 1%b0 (W.to_b0 &x)),
        (Bin0.addition.commutativity 1%b0 (W.to_b0 W.Max)),
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
  lemma g : (W.to_b0 x < W.to_b0 x + 1)%b0.
  {
    simpl Bin0.LessThan in |- *.
    exists BinBase.One.
    ipso (refl (W.to_b0 &x + 1)%b0).
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
    ex (Bin0.order.strict.irreflexivity (W.to_b0 W.Max)
          (Comparable.order.mixed.right.transitivity &g (bound.range &y)))
      quodlibet.
  }
  let proof s := Bin0.order.succession (W.to_b0 &x) (W.to_b0 &y) &g.
  lemma raised : (W.to_b0 (x + W.One) <= W.to_b0 y)%b0.
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
          (Bin0.order.strict.transitivity &g &l)).
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
      -> (W.to_b0 (x - W.One) + 1 = W.to_b0 x)%b0.
Proof.
  intros x h.
  let proof low := preservation W.Zero &x (bound.lower &x).
  lemma above : (0 < W.to_b0 x)%b0.
  {
    match &low with | same | larger end.
    - ex (&h (symm (W.conversion.injectivity &same))) quodlibet.
    - leibniz W.conversion.zero in &larger.
      ipso &larger.
  }
  let proof s := Bin0.order.succession 0%b0 (W.to_b0 &x) &above.
  lemma at_least : (W.to_b0 W.One <= W.to_b0 x)%b0.
  {
    leibniz W.conversion.one in |- *.
    ipso &s.
  }
  let proof clear :=
    modus aequans (overflow.subtraction.specification &x W.One), (reflection W.One &x &at_least).
  let proof e := overflow.subtraction.exactness &x W.One &clear.
  leibniz
    W.conversion.one,
    (Bin0.addition.commutativity 1%b0 (W.to_b0 (&x - W.One)))
    in &e.
  ipso &e.
Qed.

(* decrement.extensivity *)
Theorem extensivity : forall (x : W.T) . ~ (x = W.Zero) -> x - W.One < x.
Proof.
  intros x h.
  lemma g
    : (W.to_b0 (x - W.One) < W.to_b0 (x - W.One) + 1)%b0.
  {
    simpl Bin0.LessThan in |- *.
    exists BinBase.One.
    ipso (refl (W.to_b0 (&x - W.One) + 1)%b0).
  }
  leibniz (decrement.exactness &x &h) in &g.
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
        (Bin0.order.strict.transitivity &g1 &g2)).
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
  let proof s :=
    Bin0.comparison.specification (W.to_b0 &x) (W.to_b0 &y).
  match &s with | strict equality end.
  divide et impera.
  - divide et impera.
    + intro c.
      ipso (modus aequans (W.order.strict.specification &x &y), (modus aequans &strict, &c)).
    + intro h.
      ipso (modus aequans &strict, (modus aequans (W.order.strict.specification &x &y), &h)).
  - divide et impera.
    + intro c.
      ipso (W.conversion.injectivity (modus aequans &equality, &c)).
    + intro e.
      ipso (modus aequans &equality, (congru W.to_b0, &e)).
Qed.

(* comparison.antisymmetry *)
Theorem antisymmetry
  : forall (x : W.T) (y : W.T) . W.compare x y = Comparison.transpose (W.compare y x).
Proof.
  intros x y.
  leibniz (W.conversion.comparison &x &y), (W.conversion.comparison &y &x) in |- *.
  ipso (Bin0.comparison.antisymmetry (W.to_b0 &x) (W.to_b0 &y)).
Qed.

End comparison. (* comparison *)

End Laws.
