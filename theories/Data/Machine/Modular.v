(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

From JW Require Import Core.All.
From JW Require Import Data.Number.Binary.BinBase.
From JW Require Import Data.Number.Binary.BinWithZero.
From JW Require Import Tactics.Equation.
From JW Require Import Tactics.Witness.

(* A fixed-width integer whose arithmetic wraps modulo [modulus], read through
 * [to_bin_with_zero], a value below it: its operations, and the facts about
 * that value that every width proves. Each [Parameter] is a field, not an
 * axiom. The operations are [Inline]: a width that includes [Laws] gets laws
 * stated with its own operations, such as [UInt8.add], so [leibniz] can
 * rewrite with them.
 *)
Module Type Width.

Parameter Inline T : Type.
Parameter Inline Zero : T.
Parameter Inline One : T.
Parameter Inline to_bin_with_zero : T -> BinWithZero.
Parameter Inline add : T -> T -> T.
Parameter Inline sub : T -> T -> T.
Parameter Inline negate : T -> T.
Parameter Inline mul : T -> T -> T.
Parameter Inline modulus : BinBase.

Module conversion. (* conversion *)

Parameter zero
  : to_bin_with_zero Zero = 0%bin_with_zero.
Parameter one
  : to_bin_with_zero One = 1%bin_with_zero.
Parameter boundedness
  : forall (x : T) . (to_bin_with_zero x < BinWithZero.Positive modulus)%bin_with_zero.
Parameter injectivity
  : forall {x : T} {y : T} . to_bin_with_zero x = to_bin_with_zero y -> x = y.
Parameter addition
  : forall (x : T) (y : T) .
      (to_bin_with_zero (add x y)
       = (to_bin_with_zero x + to_bin_with_zero y) %. modulus)%bin_with_zero.
Parameter subtraction
  : forall (x : T) (y : T) .
      ((to_bin_with_zero (sub x y) + to_bin_with_zero y) %. modulus
       = to_bin_with_zero x)%bin_with_zero.
Parameter negation
  : forall (x : T) .
      ((to_bin_with_zero (negate x) + to_bin_with_zero x) %. modulus = 0)%bin_with_zero.
Parameter multiplication
  : forall (x : T) (y : T) .
      (to_bin_with_zero (mul x y)
       = (to_bin_with_zero x * to_bin_with_zero y) %. modulus)%bin_with_zero.

End conversion. (* conversion *)

End Width.

(* The laws of addition, subtraction and multiplication, each read through
 * [to_bin_with_zero] modulo [modulus].
 *)
Module Laws (W : Width).

(* [only parsing] keeps goals printing the operations by name; the scope is
 * bound to [W.T] here only, so an included law leaves the width's own scope
 * alone.
 *)
Local Notation "x + y" := (W.add x y) (only parsing)
  : jw_modular_scope.
Local Notation "x - y" := (W.sub x y) (only parsing)
  : jw_modular_scope.
Local Notation "- x" := (W.negate x)
  (at level 35, right associativity, only parsing)
  : jw_modular_scope.
Local Notation "x * y" := (W.mul x y) (only parsing)
  : jw_modular_scope.
#[local] Bind Scope jw_modular_scope with W.T.
Local Open Scope jw_modular_scope.

Module addition. (* addition *)

(* addition.associativity *)
Theorem associativity
  : forall (x : W.T) (y : W.T) (z : W.T) . (x + y) + z = x + (y + z).
Proof.
  intros x y z.
  lemma facto : W.to_bin_with_zero ((&x + &y) + &z) = W.to_bin_with_zero (&x + (&y + &z)).
  {
    leibniz
      (W.conversion.addition (&x + &y) &z),
      (W.conversion.addition &x &y),
      (BinWithZero.modulo.sum.left.absorption
        (W.to_bin_with_zero &x + W.to_bin_with_zero &y)%bin_with_zero (W.to_bin_with_zero &z)
        W.modulus),
      (W.conversion.addition &x (&y + &z)),
      (W.conversion.addition &y &z),
      (BinWithZero.modulo.sum.right.absorption
        (W.to_bin_with_zero &x) (W.to_bin_with_zero &y + W.to_bin_with_zero &z)%bin_with_zero
        W.modulus),
      (BinWithZero.addition.associativity
        (W.to_bin_with_zero &x) (W.to_bin_with_zero &y) (W.to_bin_with_zero &z))
      in |- *.
    quod idem est.
  }
  ipso (W.conversion.injectivity &facto).
Qed.

(* addition.commutativity *)
Theorem commutativity : forall (x : W.T) (y : W.T) . x + y = y + x.
Proof.
  intros x y.
  lemma facto : W.to_bin_with_zero (&x + &y) = W.to_bin_with_zero (&y + &x).
  {
    leibniz
      (W.conversion.addition &x &y),
      (W.conversion.addition &y &x),
      (BinWithZero.addition.commutativity (W.to_bin_with_zero &x) (W.to_bin_with_zero &y))
      in |- *.
    quod idem est.
  }
  ipso (W.conversion.injectivity &facto).
Qed.

(* addition.identity *)
Theorem identity : forall (x : W.T) . (W.Zero + x = x) /\ (x + W.Zero = x).
Proof.
  intros x.
  lemma left : W.Zero + &x = &x.
  {
    lemma facto : W.to_bin_with_zero (W.Zero + &x) = W.to_bin_with_zero &x.
    {
      match (BinWithZero.addition.identity (W.to_bin_with_zero &x)) with | left _ end.
      leibniz
        (W.conversion.addition W.Zero &x),
        W.conversion.zero,
        &left,
        (BinWithZero.modulo.identity
          (W.to_bin_with_zero &x) W.modulus (W.conversion.boundedness &x))
        in |- *.
      quod idem est.
    }
    ipso (W.conversion.injectivity &facto).
  }
  divide et impera.
  - ipso &left.
  - leibniz (addition.commutativity &x W.Zero) in |- *.
    ipso &left.
Qed.

(* addition.inverse *)
Theorem inverse : forall (x : W.T) . (- x + x = W.Zero) /\ (x + - x = W.Zero).
Proof.
  intros x.
  lemma left : - &x + &x = W.Zero.
  {
    lemma facto : W.to_bin_with_zero (- &x + &x) = W.to_bin_with_zero W.Zero.
    {
      leibniz
        (W.conversion.addition (- &x) &x),
        (W.conversion.negation &x),
        W.conversion.zero
        in |- *.
      quod idem est.
    }
    ipso (W.conversion.injectivity &facto).
  }
  divide et impera.
  - ipso &left.
  - leibniz (addition.commutativity &x (- &x)) in |- *.
    ipso &left.
Qed.

Module inversion. (* addition.inversion *)

(* The subtraction ripples a borrow, so this is read through the values
 * modulo [W.modulus], as the other laws are.
 *)
(* addition.inversion.subtraction *)
Theorem subtraction : forall (x : W.T) (y : W.T) . (x - y) + y = x.
Proof.
  intros x y.
  lemma facto : W.to_bin_with_zero ((&x - &y) + &y) = W.to_bin_with_zero &x.
  {
    leibniz (W.conversion.addition (&x - &y) &y) in |- *.
    ipso (W.conversion.subtraction &x &y).
  }
  ipso (W.conversion.injectivity &facto).
Qed.

End inversion. (* addition.inversion *)

End addition. (* addition *)

Module subtraction. (* subtraction *)

(* Adding [- y] to both sides of [addition.inversion.subtraction]. *)
(* subtraction.specification *)
Theorem specification : forall (x : W.T) (y : W.T) . x - y = x + (- y).
Proof.
  intros x y.
  let proof shifted : ((&x - &y) + &y) + (- &y) = &x + (- &y)
    := congru (fun (z : W.T) . z + (- &y)), (addition.inversion.subtraction &x &y).
  match (addition.inverse &y) with | _ r end.
  match (addition.identity (&x - &y)) with | _ i end.
  leibniz (addition.associativity (&x - &y) &y (- &y)), &r, &i in &shifted.
  ipso &shifted.
Qed.

Module inversion. (* subtraction.inversion *)

(* subtraction.inversion.addition *)
Theorem addition : forall (x : W.T) (y : W.T) . (x + y) - y = x.
Proof.
  intros x y.
  match (addition.inverse &y) with | _ r end.
  match (addition.identity &x) with | _ i end.
  leibniz
    (subtraction.specification (&x + &y) &y),
    (addition.associativity &x &y (- &y)),
    &r,
    &i
    in |- *.
  quod idem est.
Qed.

End inversion. (* subtraction.inversion *)

Module right. (* subtraction.right *)

(* subtraction.right.identity *)
Theorem identity : forall (x : W.T) . x - W.Zero = x.
Proof.
  intros x.
  match (addition.identity (&x - W.Zero)) with | _ i end.
  leibniz <- &i in |- *.
  ipso (addition.inversion.subtraction &x W.Zero).
Qed.

End right. (* subtraction.right *)

(* subtraction.annihilation *)
Theorem annihilation : forall (x : W.T) . x - x = W.Zero.
Proof.
  intros x.
  match (addition.inverse &x) with | _ r end.
  leibniz (subtraction.specification &x &x) in |- *.
  ipso &r.
Qed.

End subtraction. (* subtraction *)

Module multiplication. (* multiplication *)

(* multiplication.associativity *)
Theorem associativity
  : forall (x : W.T) (y : W.T) (z : W.T) . (x * y) * z = x * (y * z).
Proof.
  intros x y z.
  lemma facto : W.to_bin_with_zero ((&x * &y) * &z) = W.to_bin_with_zero (&x * (&y * &z)).
  {
    leibniz
      (W.conversion.multiplication (&x * &y) &z),
      (W.conversion.multiplication &x &y),
      (BinWithZero.modulo.product.left.absorption
        (W.to_bin_with_zero &x * W.to_bin_with_zero &y)%bin_with_zero (W.to_bin_with_zero &z)
        W.modulus),
      (W.conversion.multiplication &x (&y * &z)),
      (W.conversion.multiplication &y &z),
      (BinWithZero.modulo.product.right.absorption
        (W.to_bin_with_zero &x) (W.to_bin_with_zero &y * W.to_bin_with_zero &z)%bin_with_zero
        W.modulus),
      (BinWithZero.multiplication.associativity
        (W.to_bin_with_zero &x) (W.to_bin_with_zero &y) (W.to_bin_with_zero &z))
      in |- *.
    quod idem est.
  }
  ipso (W.conversion.injectivity &facto).
Qed.

(* multiplication.commutativity *)
Theorem commutativity : forall (x : W.T) (y : W.T) . x * y = y * x.
Proof.
  intros x y.
  lemma facto : W.to_bin_with_zero (&x * &y) = W.to_bin_with_zero (&y * &x).
  {
    leibniz
      (W.conversion.multiplication &x &y),
      (W.conversion.multiplication &y &x),
      (BinWithZero.multiplication.commutativity (W.to_bin_with_zero &x) (W.to_bin_with_zero &y))
      in |- *.
    quod idem est.
  }
  ipso (W.conversion.injectivity &facto).
Qed.

(* multiplication.identity *)
Theorem identity : forall (x : W.T) . (W.One * x = x) /\ (x * W.One = x).
Proof.
  intros x.
  lemma left : W.One * &x = &x.
  {
    lemma facto : W.to_bin_with_zero (W.One * &x) = W.to_bin_with_zero &x.
    {
      match (BinWithZero.multiplication.identity (W.to_bin_with_zero &x)) with | left _ end.
      leibniz
        (W.conversion.multiplication W.One &x),
        W.conversion.one,
        &left,
        (BinWithZero.modulo.identity
          (W.to_bin_with_zero &x) W.modulus (W.conversion.boundedness &x))
        in |- *.
      quod idem est.
    }
    ipso (W.conversion.injectivity &facto).
  }
  divide et impera.
  - ipso &left.
  - leibniz (multiplication.commutativity &x W.One) in |- *.
    ipso &left.
Qed.

(* multiplication.annihilation *)
Theorem annihilation : forall (x : W.T) . (W.Zero * x = W.Zero) /\ (x * W.Zero = W.Zero).
Proof.
  intros x.
  lemma right : &x * W.Zero = W.Zero.
  {
    lemma facto : W.to_bin_with_zero (&x * W.Zero) = W.to_bin_with_zero W.Zero.
    {
      match (BinWithZero.multiplication.annihilation (W.to_bin_with_zero &x)) with | _ r end.
      lemma positive : (0 < BinWithZero.Positive W.modulus)%bin_with_zero.
      {
        simpl BinWithZero.LessThan in |- *.
        exists W.modulus.
        ipso (refl (BinWithZero.Positive W.modulus)).
      }
      leibniz
        (W.conversion.multiplication &x W.Zero),
        W.conversion.zero,
        &r,
        (BinWithZero.modulo.identity 0%bin_with_zero W.modulus &positive)
        in |- *.
      quod idem est.
    }
    ipso (W.conversion.injectivity &facto).
  }
  divide et impera.
  - leibniz (multiplication.commutativity W.Zero &x) in |- *.
    ipso &right.
  - ipso &right.
Qed.

Module left. (* multiplication.left *)

Module distributivity. (* multiplication.left.distributivity *)

Module over. (* multiplication.left.distributivity.over *)

(* multiplication.left.distributivity.over.addition *)
Theorem addition
  : forall (x : W.T) (y : W.T) (z : W.T) . x * (y + z) = (x * y) + (x * z).
Proof.
  intros x y z.
  lemma facto : W.to_bin_with_zero (&x * (&y + &z)) = W.to_bin_with_zero ((&x * &y) + (&x * &z)).
  {
    match (BinWithZero.multiplication.distributivity.over.addition
            (W.to_bin_with_zero &x) (W.to_bin_with_zero &y) (W.to_bin_with_zero &z))
    with | spread _ end.
    leibniz
      (W.conversion.multiplication &x (&y + &z)),
      (W.conversion.addition &y &z),
      (BinWithZero.modulo.product.right.absorption
        (W.to_bin_with_zero &x) (W.to_bin_with_zero &y + W.to_bin_with_zero &z)%bin_with_zero
        W.modulus),
      &spread,
      (W.conversion.addition (&x * &y) (&x * &z)),
      (W.conversion.multiplication &x &y),
      (W.conversion.multiplication &x &z),
      (BinWithZero.modulo.sum.left.absorption
        (W.to_bin_with_zero &x * W.to_bin_with_zero &y)%bin_with_zero
        ((W.to_bin_with_zero &x * W.to_bin_with_zero &z) %. W.modulus)%bin_with_zero
        W.modulus),
      (BinWithZero.modulo.sum.right.absorption
        (W.to_bin_with_zero &x * W.to_bin_with_zero &y)%bin_with_zero
        (W.to_bin_with_zero &x * W.to_bin_with_zero &z)%bin_with_zero W.modulus)
      in |- *.
    quod idem est.
  }
  ipso (W.conversion.injectivity &facto).
Qed.

End over. (* multiplication.left.distributivity.over *)

End distributivity. (* multiplication.left.distributivity *)

(* [(- x) * y + x * y] is [y * (- x + x)], which is zero, so [(- x) * y] is
 * the inverse of [x * y].
 *)
(* multiplication.left.negation *)
Theorem negation : forall (x : W.T) (y : W.T) . (- x) * y = - (x * y).
Proof.
  intros x y.
  lemma sum : (- &x) * &y + &x * &y = W.Zero.
  {
    leibniz
      (multiplication.commutativity (- &x) &y),
      (multiplication.commutativity &x &y),
      <- (multiplication.left.distributivity.over.addition &y (- &x) &x)
      in |- *.
    match (addition.inverse &x) with | l _ end.
    leibniz &l in |- *.
    match (multiplication.annihilation &y) with | _ r end.
    ipso &r.
  }
  match (addition.identity ((- &x) * &y)) with | _ i end.
  leibniz <- &i in |- *.
  match (addition.inverse (&x * &y)) with | _ r end.
  leibniz <- &r in |- *.
  leibniz <- (addition.associativity ((- &x) * &y) (&x * &y) (- (&x * &y))), &sum in |- *.
  match (addition.identity (- (&x * &y))) with | l _ end.
  ipso &l.
Qed.

End left. (* multiplication.left *)

Module right. (* multiplication.right *)

Module distributivity. (* multiplication.right.distributivity *)

Module over. (* multiplication.right.distributivity.over *)

(* multiplication.right.distributivity.over.addition *)
Theorem addition
  : forall (x : W.T) (y : W.T) (z : W.T) . (y + z) * x = (y * x) + (z * x).
Proof.
  intros x y z.
  leibniz
    (multiplication.commutativity (&y + &z) &x),
    (multiplication.commutativity &y &x),
    (multiplication.commutativity &z &x)
    in |- *.
  ipso (multiplication.left.distributivity.over.addition &x &y &z).
Qed.

End over. (* multiplication.right.distributivity.over *)

End distributivity. (* multiplication.right.distributivity *)

(* multiplication.right.negation *)
Theorem negation : forall (x : W.T) (y : W.T) . x * (- y) = - (x * y).
Proof.
  intros x y.
  leibniz
    (multiplication.commutativity &x (- &y)),
    (multiplication.left.negation &y &x),
    (multiplication.commutativity &y &x)
    in |- *.
  quod idem est.
Qed.

End right. (* multiplication.right *)

Module distributivity. (* multiplication.distributivity *)

Module over. (* multiplication.distributivity.over *)

(* multiplication.distributivity.over.addition *)
Theorem addition
  : forall (x : W.T) (y : W.T) (z : W.T) .
      (x * (y + z) = (x * y) + (x * z)) /\ ((y + z) * x = (y * x) + (z * x)).
Proof.
  intros x y z.
  divide et impera.
  - ipso (multiplication.left.distributivity.over.addition  &x &y &z).
  - ipso (multiplication.right.distributivity.over.addition &x &y &z).
Qed.

End over. (* multiplication.distributivity.over *)

End distributivity. (* multiplication.distributivity *)

End multiplication. (* multiplication *)

End Laws.
