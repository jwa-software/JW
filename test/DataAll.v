(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

From JW Require Import Data.All.

Definition data_all_delivers_some
  : forall (A : Type) (B : Type) (f : A -> B) (a : A) .
      ~ (true = false) -> Option.map f (Some a) = Some (f a)
  := fun (A : Type) (B : Type) (f : A -> B) (a : A) (_ : ~ (true = false)) .
       Identity.reflexivity (Some (f a)).

Definition data_all_delivers_none
  : forall (A : Type) .
      Option.map (fun (a : A) . a) None = None
  := fun (A : Type) .
       Identity.reflexivity None.

Definition data_all_delivers_option_defaulting_retraction
  : forall (A : Type) (d : A) (a : A) . Option.unwrap_or d (Some a) = a
  := @Option.defaulting.retraction.

Definition data_all_delivers_option_defaulting_fallback
  : forall (A : Type) (d : A) . Option.unwrap_or d None = d
  := @Option.defaulting.fallback.

Definition data_all_delivers_option_unwrapping_retraction
  : forall (A : Type) (a : A) (h : ~ (Some a = None)) . Option.unwrap (Some a) h = a
  := @Option.unwrapping.retraction.

Definition data_all_delivers_option_unwrapping_restoration
  : forall (A : Type) (o : Option A) (h : ~ (o = None)) . Some (Option.unwrap o h) = o
  := @Option.unwrapping.restoration.

Definition data_all_delivers_option_unwrapping_irrelevance
  : forall (A : Type) (o : Option A) (h1 : ~ (o = None)) (h2 : ~ (o = None)) .
      Option.unwrap o h1 = Option.unwrap o h2
  := @Option.unwrapping.irrelevance.

Definition data_all_delivers_option_unwrap_or_of_a_value
  : Option.unwrap_or false (Some true) = true
  := Identity.reflexivity true.

Theorem data_all_delivers_some_is_not_none
  : ~ (Some true = None).
Proof.
  simpl (~ _) in |- *.
  intro e.
  ex e quodlibet.
Qed.

Definition data_all_delivers_option_unwrap_of_a_value
  : Option.unwrap (Some true) data_all_delivers_some_is_not_none = true
  := Identity.reflexivity true.

Definition data_all_delivers_product
  : Bool * Bool
  := (true , false)%product.

Definition data_all_delivers_bit
  : forall (b : Bit) . (b ^. b)%bit = 0%bit
  := Bit.sejunction.irreflexivity.

Definition data_all_delivers_first
  : forall (A : Type) (a : A) (b : A) . Product.first (a , b)%product = a
  := fun (A : Type) (a : A) (b : A) . Identity.reflexivity a.

Definition data_all_delivers_projections
  : Bool * Bool
  := (pi_2 (true , false) , pi_1 (true , false))%product.

Definition data_all_delivers_product_functor
  : Bool * Bool
  := Functor.map (fun (b : Bool) . b) (true , false)%product.

Definition data_all_delivers_product_monoid
  : forall (p : Bool * Bool) .
      Product.direct_product Bool.and Bool.or (true , false)%product p = p
      /\ Product.direct_product Bool.and Bool.or p (true , false)%product = p
  := Monoid.identity.

Definition data_all_delivers_coproduct
  : Bool + Bool
  := Coproduct.left true.

Definition data_all_delivers_copair
  : forall (A : Type) (B : Type) (f : A -> Bool) (g : B -> Bool) (b : B) .
      Coproduct.copair f g (Coproduct.right b) = g b
  := fun (A : Type) (B : Type) (f : A -> Bool) (g : B -> Bool) (b : B) .
       Identity.reflexivity (g b).

Definition data_all_delivers_coproduct_functor
  : Bool + Bool
  := Functor.map (fun (b : Bool) . b) (Coproduct.right true).

Definition data_all_delivers_unit
  : forall (u : Unit) . u = Unit.introduction
  := Unit.surjectivity.

Definition data_all_delivers_empty
  : Empty -> Bool
  := Empty.elimination Bool.

Definition data_all_delivers_nat
  : Nat
  := Nat.Successor Nat.One.

Definition data_all_delivers_zero
  : Nat0
  := Nat0.Zero.

Definition data_all_delivers_positive
  : Nat0
  := Nat0.Positive Nat.One.

Definition data_all_delivers_add
  : Nat0
  := Nat0.add (Nat0.Positive (Nat.add Nat.One Nat.One)) Nat0.Zero.

Definition data_all_delivers_instances
  : forall (x : Nat) (y : Nat) (z : Nat) (w : Nat0) .
      Nat.add (Nat.add x y) z = Nat.add x (Nat.add y z)
  := fun (x : Nat) (y : Nat) (z : Nat) (_ : Nat0) .
       Semigroup.associativity x y z.

Definition data_all_delivers_monoid
  : forall (w : Nat0) .
      Nat0.add Nat0.Zero w = w /\ Nat0.add w Nat0.Zero = w
  := Monoid.identity.

Definition data_all_delivers_cancellative
  : forall (x : Nat) (y : Nat) (z : Nat) .
      (Nat.add x y = Nat.add x z -> y = z) /\ (Nat.add x y = Nat.add z y -> x = z)
  := Cancellative.cancellation.

Definition data_all_delivers_cancellative_with_zero
  : forall (x : Nat0) (y : Nat0) (z : Nat0) .
      (Nat0.add x y = Nat0.add x z -> y = z)
      /\ (Nat0.add x y = Nat0.add z y -> x = z)
  := Cancellative.cancellation.

Definition data_all_delivers_nat_operations
  : Nat
  := (Nat.One + Nat.One * Nat.Successor Nat.One)%n.

Definition data_all_delivers_nat0_operations
  : Nat0
  := (Nat0.Zero + Nat0.Positive Nat.One * Nat0.Positive Nat.One)%n0.

Definition data_all_delivers_power
  : Nat
  := Nat.power (Nat.Successor Nat.One) Nat.One.

Definition data_all_delivers_power_notation
  : Nat
  := (Nat.Successor Nat.One ^ Nat.One)%n.

Definition data_all_delivers_nat0_power_notation
  : Nat0
  := (Nat0.Positive Nat.One ^ Nat0.Zero)%n0.

Definition data_all_delivers_sub
  : Option Nat
  := Nat.sub (Nat.Successor Nat.One) Nat.One.

Definition data_all_delivers_mul_monoid
  : forall (n : Nat) . Nat.mul Nat.One n = n /\ Nat.mul n Nat.One = n
  := Monoid.identity.

Definition data_all_delivers_commutative
  : forall (p1 : Nat * Bool) (p2 : Nat * Bool) .
      Product.direct_product Nat.mul Bool.xor p1 p2
      = Product.direct_product Nat.mul Bool.xor p2 p1
  := Commutative.commutativity.

Definition data_all_delivers_functor
  : Option Bool
  := Functor.map (fun (b : Bool) . b) (Some true).

Definition data_all_delivers_bool_operations
  : Bool
  := ((true || false) && (! false ^^ true))%bool.

Definition data_all_delivers_bool_monoids
  : forall (b : Bool) . Bool.and true b = b /\ Bool.and b true = b
  := Monoid.identity.

Definition data_all_delivers_bool_bridge
  : forall (b1 : Bool) (b2 : Bool) .
      Assert (Bool.and b1 b2) <-> Assert b1 /\ Assert b2
  := Assert.conjunction.

Definition data_all_delivers_assert_uniqueness
  : forall (b : Bool) (p : Assert b) (q : Assert b) . p = q
  := Assert.uniqueness.

Definition data_all_delivers_assert_guarding_evaluation
  : forall (X : Type) (b : Bool) (f : Assert b -> X) (p : Assert b) .
      Assert.guard b f = Some (f p)
  := @Assert.guarding.evaluation.

Definition data_all_delivers_assert_guarding_inversion
  : forall (X : Type) (b : Bool) (f : Assert b -> X) (x : X) .
      Assert.guard b f = Some x -> forsome (p : Assert b) . f p = x
  := @Assert.guarding.inversion.

Definition data_all_computes_assert_guard
  : Assert.guard true (fun (_ : Assert true) . false) = Some false
    /\ Assert.guard false (fun (_ : Assert false) . false) = None
  := conjoin (Identity.reflexivity _), (Identity.reflexivity _).

Definition data_all_delivers_list
  : List Bool
  := (List.Cons true List.Nil ++ List.Cons false List.Nil)%list.

Definition data_all_delivers_list_monoid
  : forall (A : Type) (l : List A) .
      (List.Nil ++ l)%list = l /\ (l ++ List.Nil)%list = l
  := fun (A : Type) . Monoid.identity.

Definition data_all_delivers_empty_list
  : List Bool
  := []%list.

Definition data_all_delivers_cons
  : List Bool
  := (true :: false :: [])%list.

Definition data_all_delivers_list_functor
  : List Bool
  := Functor.map (fun (b : Bool) . b) (List.Cons true List.Nil).

Definition data_all_delivers_contains
  : Prop
  := (List.Cons true List.Nil contains_member true)%list.

Definition data_all_delivers_belongs_to
  : Prop
  := (true belongs_to List.Cons true List.Nil)%list.

Definition data_all_delivers_does_not_contain_member
  : Prop
  := (List.Nil does_not_contain_member true)%list.

Definition data_all_delivers_does_not_belong_to
  : Prop
  := (true does_not_belong_to List.Nil)%list.

Definition data_all_delivers_nat_order
  : Prop
  := (Nat.One < Nat.Successor Nat.One)%n.

Definition data_all_delivers_nat0_order
  : Prop
  := (Nat0.Zero <= Nat0.Positive Nat.One)%n0.

Definition data_all_delivers_reversed_order
  : Prop
  := (Nat.Successor Nat.One > Nat.One)%n /\ (Nat0.Positive Nat.One >= Nat0.Zero)%n0.

Definition data_all_delivers_compare
  : Comparison
  := Nat.compare Nat.One (Nat.Successor Nat.One).

Definition data_all_delivers_eq
  : Bool
  := Nat0.eq Nat0.Zero Nat0.Zero.

Definition data_all_delivers_comparable_specifications
  : forall (m : Nat) (n : Nat) .
      (Nat.compare m n = Comparison.Lt <-> Nat.LessThan m n)
    /\ (Nat.compare m n = Comparison.Gt <-> Nat.LessThan n m)
  := fun (m : Nat) (n : Nat) .
       conjoin
         (Comparable.comparison.strict.specification m n),
         (Comparable.comparison.strict.transposition.specification m n).

Definition data_all_delivers_comparable
  : forall (m : Nat) (n : Nat) . Nat.LessThan m n \/ m = n \/ Nat.LessThan n m
  := Comparable.order.strict.trichotomy.

Definition data_all_delivers_comparable_strict_weakening
  : forall (m : Nat) (n : Nat) . Nat.LessThan m n -> Comparable.LessOrEqual Nat.LessThan m n
  := Comparable.order.strict.weakening.

Definition data_all_delivers_comparable_strict_negation
  : forall (m : Nat) (n : Nat) .
      ~ (Nat.LessThan m n) <-> Comparable.LessOrEqual Nat.LessThan n m
  := Comparable.order.strict.negation.

Definition data_all_delivers_comparable_refutation
  : forall (m : Nat) (n : Nat) . Comparable.le Nat.compare m n = false <-> Nat.LessThan n m
  := Comparable.order.refutation.

Definition data_all_delivers_comparable_equality_refutation
  : forall (m : Nat) (n : Nat) . Comparable.eq Nat.compare m n = false <-> ~ (m = n)
  := Comparable.comparison.equality.refutation.

Definition data_all_delivers_comparable_strict_reflection
  : forall (m : Nat) (n : Nat) . Comparable.lt Nat.compare m n = true <-> Nat.LessThan m n
  := Comparable.order.strict.reflection.

Definition data_all_delivers_comparable_strict_refutation
  : forall (m : Nat) (n : Nat) .
      Comparable.lt Nat.compare m n = false <-> Comparable.LessOrEqual Nat.LessThan n m
  := Comparable.order.strict.refutation.

Definition data_all_delivers_comparable_strict_complement
  : forall (m : Nat) (n : Nat) .
      Comparable.lt Nat.compare m n = Bool.negate (Comparable.le Nat.compare n m)
  := Comparable.order.strict.complement.

Definition data_all_computes_comparable_lt
  : Nat0.lt (Nat0.Positive Nat.One) (Nat0.Positive (Nat.Successor Nat.One)) = true
  := Identity.reflexivity _.

Definition data_all_computes_comparable_lt_refusal
  : Nat0.lt Nat0.Zero Nat0.Zero = false
  := Identity.reflexivity _.

Definition data_all_delivers_comparable_mixed_left_transitivity
  : forall (l : Nat) (m : Nat) (n : Nat) .
      Comparable.LessOrEqual Nat.LessThan l m -> Nat.LessThan m n -> Nat.LessThan l n
  := fun (l : Nat) (m : Nat) (n : Nat) . @Comparable.order.mixed.left.transitivity _ _ _ _ l m n.

Definition data_all_delivers_comparable_mixed_right_transitivity
  : forall (l : Nat) (m : Nat) (n : Nat) .
      Nat.LessThan l m -> Comparable.LessOrEqual Nat.LessThan m n -> Nat.LessThan l n
  := fun (l : Nat) (m : Nat) (n : Nat) . @Comparable.order.mixed.right.transitivity _ _ _ _ l m n.

Definition data_all_delivers_comparable_min
  : forall (m : Nat0) (n : Nat0) .
      Nat0.min m n = Nat0.min n m
  := Comparable.minimum.commutativity.

Definition data_all_delivers_total_order
  : forall (m : Nat) (n : Nat) . Nat.LessOrEqual m n \/ Nat.LessOrEqual n m
  := Total.totality.

Definition data_all_delivers_strict_partial_order
  : forall (n : Nat0) . ~ Nat0.LessThan n n
  := Irreflexive.irreflexivity.

Definition data_all_delivers_strict_total_order
  : forall (m : Integer) (n : Integer) .
      Integer.LessThan m n \/ m = n \/ Integer.LessThan n m
  := Trichotomous.trichotomy.

Definition data_all_delivers_max_monoid
  : forall (n : Nat0) .
      Nat0.max Nat0.Zero n = n /\ Nat0.max n Nat0.Zero = n
  := Monoid.identity.

Definition data_all_delivers_nat_max_monoid
  : forall (n : Nat) . Nat.max Nat.One n = n /\ Nat.max n Nat.One = n
  := Monoid.identity.

Definition data_all_delivers_division
  : Nat0 * Nat0
  := (Nat0.divide (Nat0.Positive Nat.One) Nat.One
     , Nat0.modulo (Nat0.Positive Nat.One) Nat.One)%product.

Definition data_all_delivers_nth
  : Option Bool
  := List.nth (List.Cons true List.Nil) Nat0.Zero.

Definition data_all_delivers_split_at
  : List Bool * List Bool
  := List.split_at (Nat0.Positive Nat.One) (List.Cons true (List.Cons false List.Nil)).

Definition data_all_delivers_replicate
  : List Bool
  := List.replicate (Nat0.Positive Nat.One) true.

Definition data_all_delivers_list_sum
  : Nat0
  := Nat0.add (List.sum (List.Cons (Nat0.Positive Nat.One) List.Nil))
                     (List.product List.Nil).

Definition data_all_delivers_count
  : Nat0
  := List.count (fun (b : Bool) . b) (List.Cons true List.Nil).

Definition data_all_delivers_sorting
  : forall (l : List Nat0) .
      List.Sorted Nat0.le (List.insertion_sort Nat0.le l)
  := List.sorting.sortedness
       (fun (m : Nat0) (n : Nat0) .
          Biconditional.backward.elimination
            (Disjunction.congruence
               (Comparable.order.reflection m n) (Comparable.order.reflection n m))
            (Comparable.order.totality m n))
       (fun (a : Nat0) (b : Nat0) (c : Nat0)
            (h1 : Nat0.le a b = true) (h2 : Nat0.le b c = true) .
          Biconditional.backward.elimination
            (Comparable.order.reflection a c)
            (Comparable.order.transitivity a b c
               (Biconditional.forward.elimination (Comparable.order.reflection a b) h1)
               (Biconditional.forward.elimination (Comparable.order.reflection b c) h2))).

Definition data_all_delivers_integer
  : Integer
  := Integer.add (Integer.Negative Nat.One) (Integer.Positive Nat.One).

Definition data_all_delivers_integer_operations
  : Integer
  := (Integer.Zero + Integer.Negative Nat.One * Integer.Positive Nat.One)%z.

Definition data_all_delivers_integer_order
  : Prop
  := (Integer.Negative Nat.One < Integer.Zero)%z /\ (Integer.Positive Nat.One >= Integer.Zero)%z.

Definition data_all_delivers_integer_monoid
  : forall (x : Integer) . Integer.add Integer.Zero x = x /\ Integer.add x Integer.Zero = x
  := Monoid.identity.

Definition data_all_delivers_integer_mul_monoid
  : forall (x : Integer) .
      Integer.mul (Integer.Positive Nat.One) x = x /\ Integer.mul x (Integer.Positive Nat.One) = x
  := Monoid.identity.

Definition data_all_delivers_integer_cancellative
  : forall (x : Integer) (y : Integer) (z : Integer) .
      (Integer.add x y = Integer.add x z -> y = z)
      /\ (Integer.add x y = Integer.add z y -> x = z)
  := Cancellative.cancellation.

Definition data_all_delivers_integer_total_order
  : forall (m : Integer) (n : Integer) . Integer.LessOrEqual m n \/ Integer.LessOrEqual n m
  := Total.totality.

Definition data_all_delivers_integer_embedding
  : Integer
  := Integer.from_nat0 (Nat0.Positive Nat.One).

Definition data_all_delivers_integer_eq
  : Bool
  := Integer.eq (Integer.Negative Nat.One) (Integer.negate (Integer.Positive Nat.One)).

Definition data_all_delivers_range_from_zero
  : List Nat0
  := List.range_from_zero (Nat0.Positive Nat.One).

Definition data_all_delivers_range
  : List Nat0
  := List.range (Nat0.Positive Nat.One) (Nat0.Positive (Nat.Successor Nat.One)).

Definition data_all_delivers_range_inclusive
  : List Nat0
  := List.range_inclusive Nat0.Zero (Nat0.Positive Nat.One).

Definition data_all_delivers_extrema
  : Option Nat0 * Option Nat0
  := (List.maximum_of Nat0.le (List.Cons Nat0.Zero List.Nil)
     , List.minimum_of Nat0.le (List.Cons Nat0.Zero List.Nil))%product.

Definition data_all_delivers_gauss
  : Nat0.mul (Nat0.Positive (Nat.Successor Nat.One))
      (List.sum (List.range_from_zero (Nat0.Positive (Nat.Successor Nat.One))))
    = Nat0.mul (Nat0.Positive Nat.One) (Nat0.Positive (Nat.Successor Nat.One))
  := List.range.from_zero.sum.closed_form Nat.One.

Definition data_all_delivers_divides
  : Prop
  := Nat0.Divides (Nat0.Positive Nat.One) Nat0.Zero.

Definition data_all_delivers_divides_partial_order
  : forall (m : Nat0) (n : Nat0) .
      Nat0.Divides m n -> Nat0.Divides n m -> m = n
  := Antisymmetric.antisymmetry.

Definition data_all_delivers_parity
  : Prop
  := Nat0.Even Nat0.Zero /\ Integer.Odd (Integer.Negative Nat.One).

Definition data_all_delivers_semiring
  : forall (n : Nat0) .
      Nat0.mul Nat0.Zero n = Nat0.Zero
      /\ Nat0.mul n Nat0.Zero = Nat0.Zero
  := Semiring.annihilation.

Definition data_all_delivers_group
  : forall (x : Integer) .
      Integer.add (Integer.negate x) x = Integer.Zero
      /\ Integer.add x (Integer.negate x) = Integer.Zero
  := Group.inverse.

Definition data_all_delivers_ring
  : forall (x : Integer) (y : Integer) (z : Integer) .
      Integer.mul x (Integer.add y z) = Integer.add (Integer.mul x y) (Integer.mul x z)
      /\ Integer.mul (Integer.add y z) x = Integer.add (Integer.mul y x) (Integer.mul z x)
  := Ring.distributivity.

Definition data_all_delivers_boolean_ring
  : forall (b1 : Bool) (b2 : Bool) (b3 : Bool) .
      Bool.and b1 (Bool.xor b2 b3) = Bool.xor (Bool.and b1 b2) (Bool.and b1 b3)
      /\ Bool.and (Bool.xor b2 b3) b1 = Bool.xor (Bool.and b2 b1) (Bool.and b3 b1)
  := Ring.distributivity.

Definition data_all_delivers_mul_cancellative
  : forall (x : Nat) (y : Nat) (z : Nat) .
      (Nat.mul x y = Nat.mul x z -> y = z) /\ (Nat.mul x y = Nat.mul z y -> x = z)
  := Cancellative.cancellation.

Definition data_all_delivers_functor_identity
  : forall (F : Type -> Type) (t : Functor F) (A : Type) (x : F A) .
      Functor.map (fun (a : A) . a) x = x
  := fun (F : Type -> Type) (t : Functor F) . Functor.identity.

Definition data_all_delivers_functor_composition
  : forall (F : Type -> Type) (t : Functor F)
        (A : Type) (B : Type) (C : Type) (f : A -> B) (g : B -> C) (x : F A) .
      Functor.map g (Functor.map f x) = Functor.map (fun (a : A) . g (f a)) x
  := fun (F : Type -> Type) (t : Functor F) . Functor.composition.

Definition data_all_delivers_comparable_transitivity
  : forall (A : Type) (compare : A -> A -> Comparison) (lt : A -> A -> Prop)
        (c : Comparable compare lt) (l : A) (m : A) (n : A) .
      lt l m -> lt m n -> lt l n
  := fun (A : Type) (compare : A -> A -> Comparison) (lt : A -> A -> Prop)
        (c : Comparable compare lt) .
      Comparable.transitivity.

Definition data_all_delivers_comparable_specification
  : forall (A : Type) (compare : A -> A -> Comparison) (lt : A -> A -> Prop)
        (c : Comparable compare lt) (m : A) (n : A) .
      (compare m n = Comparison.Lt <-> lt m n) /\ (compare m n = Comparison.Eq <-> m = n)
  := fun (A : Type) (compare : A -> A -> Comparison) (lt : A -> A -> Prop)
        (c : Comparable compare lt) .
      Comparable.specification.

Definition data_all_delivers_comparable_antisymmetry
  : forall (A : Type) (compare : A -> A -> Comparison) (lt : A -> A -> Prop)
        (c : Comparable compare lt) (m : A) (n : A) .
      compare m n = Comparison.transpose (compare n m)
  := fun (A : Type) (compare : A -> A -> Comparison) (lt : A -> A -> Prop)
        (c : Comparable compare lt) .
      Comparable.antisymmetry.

Definition data_all_delivers_comparable_strict_transposition
  : forall (m : Nat) (n : Nat) .
      Comparable.gt Nat.compare m n = Comparable.lt Nat.compare n m
  := Comparable.order.strict.transposition.

Definition data_all_delivers_comparable_transposition
  : forall (m : Nat) (n : Nat) .
      Comparable.ge Nat.compare m n = Comparable.le Nat.compare n m
  := Comparable.order.transposition.

Definition data_all_computes_comparable_gt
  : Nat0.gt (Nat0.Positive (Nat.Successor Nat.One)) (Nat0.Positive Nat.One) = true
  := Identity.reflexivity _.

Definition data_all_computes_comparable_gt_refusal
  : Nat0.gt Nat0.Zero Nat0.Zero = false
  := Identity.reflexivity _.

Definition data_all_computes_comparable_ge
  : Nat0.ge Nat0.Zero Nat0.Zero = true
  := Identity.reflexivity _.

Definition data_all_computes_comparable_ge_refusal
  : Nat0.ge Nat0.Zero (Nat0.Positive Nat.One) = false
  := Identity.reflexivity _.

Definition data_all_delivers_nat_tests
  : forall (m : Nat) (n : Nat) . Nat.gt m n = Nat.lt n m /\ Nat.ge m n = Nat.le n m
  := fun (m : Nat) (n : Nat) .
       conjoin (Comparable.order.strict.transposition m n), (Comparable.order.transposition m n).

Definition data_all_delivers_nat0_tests
  : forall (m : Nat0) (n : Nat0) . Nat0.gt m n = Nat0.lt n m /\ Nat0.ge m n = Nat0.le n m
  := fun (m : Nat0) (n : Nat0) .
       conjoin (Comparable.order.strict.transposition m n), (Comparable.order.transposition m n).

Definition data_all_delivers_integer_tests
  : forall (m : Integer) (n : Integer) .
      Integer.gt m n = Integer.lt n m /\ Integer.ge m n = Integer.le n m
  := fun (m : Integer) (n : Integer) .
       conjoin (Comparable.order.strict.transposition m n), (Comparable.order.transposition m n).

Definition data_all_delivers_rational_tests
  : forall (m : Rational) (n : Rational) .
      Rational.gt m n = Rational.lt n m /\ Rational.ge m n = Rational.le n m
  := fun (m : Rational) (n : Rational) .
       conjoin (Comparable.order.strict.transposition m n), (Comparable.order.transposition m n).

Definition data_all_delivers_bin_tests
  : forall (m : Bin) (n : Bin) . Bin.gt m n = Bin.lt n m /\ Bin.ge m n = Bin.le n m
  := fun (m : Bin) (n : Bin) .
       conjoin (Comparable.order.strict.transposition m n), (Comparable.order.transposition m n).

Definition data_all_delivers_bin0_tests
  : forall (m : Bin0) (n : Bin0) . Bin0.gt m n = Bin0.lt n m /\ Bin0.ge m n = Bin0.le n m
  := fun (m : Bin0) (n : Bin0) .
       conjoin (Comparable.order.strict.transposition m n), (Comparable.order.transposition m n).

Definition data_all_delivers_signed_bin_tests
  : forall (m : SignedBin) (n : SignedBin) .
      SignedBin.gt m n = SignedBin.lt n m /\ SignedBin.ge m n = SignedBin.le n m
  := fun (m : SignedBin) (n : SignedBin) .
       conjoin (Comparable.order.strict.transposition m n), (Comparable.order.transposition m n).

Definition data_all_delivers_uint8_tests
  : forall (m : UInt8) (n : UInt8) . UInt8.gt m n = UInt8.lt n m /\ UInt8.ge m n = UInt8.le n m
  := fun (m : UInt8) (n : UInt8) .
       conjoin (Comparable.order.strict.transposition m n), (Comparable.order.transposition m n).

Definition data_all_delivers_uint16_tests
  : forall (m : UInt16) (n : UInt16) .
      UInt16.gt m n = UInt16.lt n m /\ UInt16.ge m n = UInt16.le n m
  := fun (m : UInt16) (n : UInt16) .
       conjoin (Comparable.order.strict.transposition m n), (Comparable.order.transposition m n).

Definition data_all_delivers_uint32_tests
  : forall (m : UInt32) (n : UInt32) .
      UInt32.gt m n = UInt32.lt n m /\ UInt32.ge m n = UInt32.le n m
  := fun (m : UInt32) (n : UInt32) .
       conjoin (Comparable.order.strict.transposition m n), (Comparable.order.transposition m n).

Definition data_all_delivers_uint64_tests
  : forall (m : UInt64) (n : UInt64) .
      UInt64.gt m n = UInt64.lt n m /\ UInt64.ge m n = UInt64.le n m
  := fun (m : UInt64) (n : UInt64) .
       conjoin (Comparable.order.strict.transposition m n), (Comparable.order.transposition m n).

Definition data_all_delivers_int8_tests
  : forall (m : Int8) (n : Int8) . Int8.gt m n = Int8.lt n m /\ Int8.ge m n = Int8.le n m
  := fun (m : Int8) (n : Int8) .
       conjoin (Comparable.order.strict.transposition m n), (Comparable.order.transposition m n).

Definition data_all_delivers_int16_tests
  : forall (m : Int16) (n : Int16) . Int16.gt m n = Int16.lt n m /\ Int16.ge m n = Int16.le n m
  := fun (m : Int16) (n : Int16) .
       conjoin (Comparable.order.strict.transposition m n), (Comparable.order.transposition m n).

Definition data_all_delivers_int32_tests
  : forall (m : Int32) (n : Int32) . Int32.gt m n = Int32.lt n m /\ Int32.ge m n = Int32.le n m
  := fun (m : Int32) (n : Int32) .
       conjoin (Comparable.order.strict.transposition m n), (Comparable.order.transposition m n).

Definition data_all_delivers_int64_tests
  : forall (m : Int64) (n : Int64) . Int64.gt m n = Int64.lt n m /\ Int64.ge m n = Int64.le n m
  := fun (m : Int64) (n : Int64) .
       conjoin (Comparable.order.strict.transposition m n), (Comparable.order.transposition m n).

Definition data_all_delivers_ascii_tests
  : forall (m : Ascii) (n : Ascii) . Ascii.gt m n = Ascii.lt n m /\ Ascii.ge m n = Ascii.le n m
  := fun (m : Ascii) (n : Ascii) .
       conjoin (Comparable.order.strict.transposition m n), (Comparable.order.transposition m n).

Definition data_all_delivers_ascii_str_tests
  : forall (m : AsciiStr) (n : AsciiStr) .
      AsciiStr.gt m n = AsciiStr.lt n m /\ AsciiStr.ge m n = AsciiStr.le n m
  := fun (m : AsciiStr) (n : AsciiStr) .
       conjoin (Comparable.order.strict.transposition m n), (Comparable.order.transposition m n).

Definition data_all_delivers_utf8_tests
  : forall (m : Utf8) (n : Utf8) . Utf8.gt m n = Utf8.lt n m /\ Utf8.ge m n = Utf8.le n m
  := fun (m : Utf8) (n : Utf8) .
       conjoin (Comparable.order.strict.transposition m n), (Comparable.order.transposition m n).

Definition data_all_delivers_utf8_str_tests
  : forall (m : Utf8Str) (n : Utf8Str) .
      Utf8Str.gt m n = Utf8Str.lt n m /\ Utf8Str.ge m n = Utf8Str.le n m
  := fun (m : Utf8Str) (n : Utf8Str) .
       conjoin (Comparable.order.strict.transposition m n), (Comparable.order.transposition m n).

Definition data_all_delivers_kleene3_tests
  : forall (m : Kleene3) (n : Kleene3) .
      Kleene3.gt m n = Kleene3.lt n m /\ Kleene3.ge m n = Kleene3.le n m
  := fun (m : Kleene3) (n : Kleene3) .
       conjoin (Comparable.order.strict.transposition m n), (Comparable.order.transposition m n).

Definition data_all_delivers_month_tests
  : forall (m : Month) (n : Month) . Month.gt m n = Month.lt n m /\ Month.ge m n = Month.le n m
  := fun (m : Month) (n : Month) .
       conjoin (Comparable.order.strict.transposition m n), (Comparable.order.transposition m n).

Definition data_all_delivers_date_tests
  : forall (m : Date) (n : Date) . Date.gt m n = Date.lt n m /\ Date.ge m n = Date.le n m
  := fun (m : Date) (n : Date) .
       conjoin (Comparable.order.strict.transposition m n), (Comparable.order.transposition m n).

Definition data_all_delivers_weekday_tests
  : forall (m : Weekday) (n : Weekday) .
      Weekday.gt m n = Weekday.lt n m /\ Weekday.ge m n = Weekday.le n m
  := fun (m : Weekday) (n : Weekday) .
       conjoin (Comparable.order.strict.transposition m n), (Comparable.order.transposition m n).

Definition data_all_delivers_iso_week_date_tests
  : forall (m : IsoWeekDate) (n : IsoWeekDate) .
      IsoWeekDate.gt m n = IsoWeekDate.lt n m /\ IsoWeekDate.ge m n = IsoWeekDate.le n m
  := fun (m : IsoWeekDate) (n : IsoWeekDate) .
       conjoin (Comparable.order.strict.transposition m n), (Comparable.order.transposition m n).

Definition data_all_delivers_rational_eq_min_max
  : forall (m : Rational) (n : Rational) .
      (Rational.eq m n = true <-> m = n)
      /\ Rational.min m n = Rational.min n m /\ Rational.max m n = Rational.max n m
  := fun (m : Rational) (n : Rational) .
       conjoin (Comparable.comparison.equality.reflection m n),
         (conjoin (Comparable.minimum.commutativity m n), (Comparable.maximum.commutativity m n)).

Definition data_all_delivers_kleene3_eq_min_max
  : forall (m : Kleene3) (n : Kleene3) .
      (Kleene3.eq m n = true <-> m = n)
      /\ Kleene3.min m n = Kleene3.min n m /\ Kleene3.max m n = Kleene3.max n m
  := fun (m : Kleene3) (n : Kleene3) .
       conjoin (Comparable.comparison.equality.reflection m n),
         (conjoin (Comparable.minimum.commutativity m n), (Comparable.maximum.commutativity m n)).

Definition data_all_delivers_month_eq_min_max
  : forall (m : Month) (n : Month) .
      (Month.eq m n = true <-> m = n)
      /\ Month.min m n = Month.min n m /\ Month.max m n = Month.max n m
  := fun (m : Month) (n : Month) .
       conjoin (Comparable.comparison.equality.reflection m n),
         (conjoin (Comparable.minimum.commutativity m n), (Comparable.maximum.commutativity m n)).

Definition data_all_delivers_date_eq_min_max
  : forall (m : Date) (n : Date) .
      (Date.eq m n = true <-> m = n)
      /\ Date.min m n = Date.min n m /\ Date.max m n = Date.max n m
  := fun (m : Date) (n : Date) .
       conjoin (Comparable.comparison.equality.reflection m n),
         (conjoin (Comparable.minimum.commutativity m n), (Comparable.maximum.commutativity m n)).

Definition data_all_delivers_weekday_eq_min_max
  : forall (m : Weekday) (n : Weekday) .
      (Weekday.eq m n = true <-> m = n)
      /\ Weekday.min m n = Weekday.min n m /\ Weekday.max m n = Weekday.max n m
  := fun (m : Weekday) (n : Weekday) .
       conjoin (Comparable.comparison.equality.reflection m n),
         (conjoin (Comparable.minimum.commutativity m n), (Comparable.maximum.commutativity m n)).

Definition data_all_delivers_iso_week_date_eq_min_max
  : forall (m : IsoWeekDate) (n : IsoWeekDate) .
      (IsoWeekDate.eq m n = true <-> m = n)
      /\ IsoWeekDate.min m n = IsoWeekDate.min n m
      /\ IsoWeekDate.max m n = IsoWeekDate.max n m
  := fun (m : IsoWeekDate) (n : IsoWeekDate) .
       conjoin (Comparable.comparison.equality.reflection m n),
         (conjoin (Comparable.minimum.commutativity m n), (Comparable.maximum.commutativity m n)).

Definition data_all_delivers_discernible_equivalence_reflection
  : forall (A : Type) (test : A -> A -> Bool) (D : Discernible test) (a : A) (b : A) .
      Discernible.equivalent a b = true <-> a = b
  := fun (A : Type) (test : A -> A -> Bool) (D : Discernible test) .
       Discernible.equivalence.reflection.

Definition data_all_delivers_discernible_equivalence_reflexivity
  : forall (A : Type) (test : A -> A -> Bool) (D : Discernible test) (a : A) .
      Discernible.equivalent a a = true
  := fun (A : Type) (test : A -> A -> Bool) (D : Discernible test) .
       Discernible.equivalence.reflexivity.

Definition data_all_delivers_discernible_equivalence_refutation
  : forall (A : Type) (test : A -> A -> Bool) (D : Discernible test) (a : A) (b : A) .
      Discernible.equivalent a b = false <-> ~ (a = b)
  := fun (A : Type) (test : A -> A -> Bool) (D : Discernible test) .
       Discernible.equivalence.refutation.

Definition data_all_delivers_discernible_equivalence_symmetry
  : forall (A : Type) (test : A -> A -> Bool) (D : Discernible test) (a : A) (b : A) .
      Discernible.equivalent a b = Discernible.equivalent b a
  := fun (A : Type) (test : A -> A -> Bool) (D : Discernible test) .
       Discernible.equivalence.symmetry.

Definition data_all_delivers_discernible_discernment_complement
  : forall (A : Type) (test : A -> A -> Bool) (D : Discernible test) (a : A) (b : A) .
      Discernible.discern a b = Bool.negate (Discernible.equivalent a b)
  := fun (A : Type) (test : A -> A -> Bool) (D : Discernible test) .
       Discernible.discernment.complement.

Definition data_all_delivers_discernible_discernment_reflection
  : forall (A : Type) (test : A -> A -> Bool) (D : Discernible test) (a : A) (b : A) .
      Discernible.discern a b = true <-> ~ (a = b)
  := fun (A : Type) (test : A -> A -> Bool) (D : Discernible test) .
       Discernible.discernment.reflection.

Definition data_all_delivers_discernible_discernment_refutation
  : forall (A : Type) (test : A -> A -> Bool) (D : Discernible test) (a : A) (b : A) .
      Discernible.discern a b = false <-> a = b
  := fun (A : Type) (test : A -> A -> Bool) (D : Discernible test) .
       Discernible.discernment.refutation.

Definition data_all_delivers_bool_conjunction_truth_specification
  : forall (b1 : Bool) (b2 : Bool) . Bool.and b1 b2 = true <-> b1 = true /\ b2 = true
  := Bool.conjunction.truth.specification.

Definition data_all_delivers_list_test_local_reflection
  : forall (A : Type) (tester : A -> A -> Bool) (l : List A) .
      List.All (fun (a : A) . forall (b : A) . tester a b = true <-> a = b) l ->
      forall (m : List A) . List.test tester l m = true <-> l = m
  := @List.test.local.reflection.

Definition data_all_delivers_product_test_local_reflection
  : forall (A : Type) (B : Type)
        (first_tester : A -> A -> Bool) (second_tester : B -> B -> Bool) (p : A * B) .
      (forall (a : A) . first_tester (Product.first p) a = true <-> Product.first p = a) ->
      (forall (b : B) . second_tester (Product.second p) b = true <-> Product.second p = b) ->
      forall (q : A * B) . Product.test first_tester second_tester p q = true <-> p = q
  := @Product.test.local.reflection.

Definition data_all_computes_equivalent_of_two_numbers
  : Nat0.equivalent Nat0.Zero Nat0.Zero = true
  := Identity.reflexivity _.

Definition data_all_computes_discern_of_two_numbers
  : Nat0.discern Nat0.Zero (Nat0.Positive Nat.One) = true
  := Identity.reflexivity _.

Definition data_all_computes_equivalent_with_its_tester
  : Discernible.equivalent (test := Nat0.eq) Nat0.Zero Nat0.Zero = true
  := Identity.reflexivity _.

Definition data_all_computes_equivalent_of_two_lists
  : List.equivalent (true :: false :: [])%list (true :: false :: [])%list = true
  := Identity.reflexivity _.

Definition data_all_computes_discern_of_two_lists_of_lists
  : List.discern ((true :: [])%list :: [])%list ((false :: [])%list :: [])%list = true
  := Identity.reflexivity _.

Definition data_all_computes_equivalent_of_two_pairs
  : Product.equivalent (true, Nat0.Zero)%product (true, Nat0.Zero)%product = true
  := Identity.reflexivity _.

Definition data_all_computes_equivalent_of_two_options
  : Option.equivalent (Some true) None = false
  := Identity.reflexivity _.

Definition data_all_delivers_bool_discernible
  : forall (a : Bool) (b : Bool) .
      (Bool.equivalent a b = true <-> a = b) /\ (Bool.discern a b = true <-> ~ (a = b))
  := fun (a : Bool) (b : Bool) .
       conjoin (Discernible.equivalence.reflection a b), (Discernible.discernment.reflection a b).

Definition data_all_delivers_comparison_discernible
  : forall (a : Comparison) (b : Comparison) .
      (Comparison.equivalent a b = true <-> a = b)
      /\ (Comparison.discern a b = true <-> ~ (a = b))
  := fun (a : Comparison) (b : Comparison) .
       conjoin (Discernible.equivalence.reflection a b), (Discernible.discernment.reflection a b).

Definition data_all_delivers_unit_discernible
  : forall (a : Unit) (b : Unit) .
      (Unit.equivalent a b = true <-> a = b) /\ (Unit.discern a b = true <-> ~ (a = b))
  := fun (a : Unit) (b : Unit) .
       conjoin (Discernible.equivalence.reflection a b), (Discernible.discernment.reflection a b).

Definition data_all_delivers_empty_discernible
  : forall (a : Empty) (b : Empty) .
      (Empty.equivalent a b = true <-> a = b) /\ (Empty.discern a b = true <-> ~ (a = b))
  := fun (a : Empty) (b : Empty) .
       conjoin (Discernible.equivalence.reflection a b), (Discernible.discernment.reflection a b).

Definition data_all_delivers_endian_discernible
  : forall (a : Endian) (b : Endian) .
      (Endian.equivalent a b = true <-> a = b) /\ (Endian.discern a b = true <-> ~ (a = b))
  := fun (a : Endian) (b : Endian) .
       conjoin (Discernible.equivalence.reflection a b), (Discernible.discernment.reflection a b).

Definition data_all_delivers_bit_discernible
  : forall (a : Bit) (b : Bit) .
      (Bit.equivalent a b = true <-> a = b) /\ (Bit.discern a b = true <-> ~ (a = b))
  := fun (a : Bit) (b : Bit) .
       conjoin (Discernible.equivalence.reflection a b), (Discernible.discernment.reflection a b).

Definition data_all_delivers_byte_discernible
  : forall (a : Byte) (b : Byte) .
      (Byte.equivalent a b = true <-> a = b) /\ (Byte.discern a b = true <-> ~ (a = b))
  := fun (a : Byte) (b : Byte) .
       conjoin (Discernible.equivalence.reflection a b), (Discernible.discernment.reflection a b).

Definition data_all_delivers_hword_discernible
  : forall (a : HWord) (b : HWord) .
      (HWord.equivalent a b = true <-> a = b) /\ (HWord.discern a b = true <-> ~ (a = b))
  := fun (a : HWord) (b : HWord) .
       conjoin (Discernible.equivalence.reflection a b), (Discernible.discernment.reflection a b).

Definition data_all_delivers_word_discernible
  : forall (a : Word) (b : Word) .
      (Word.equivalent a b = true <-> a = b) /\ (Word.discern a b = true <-> ~ (a = b))
  := fun (a : Word) (b : Word) .
       conjoin (Discernible.equivalence.reflection a b), (Discernible.discernment.reflection a b).

Definition data_all_delivers_dword_discernible
  : forall (a : DWord) (b : DWord) .
      (DWord.equivalent a b = true <-> a = b) /\ (DWord.discern a b = true <-> ~ (a = b))
  := fun (a : DWord) (b : DWord) .
       conjoin (Discernible.equivalence.reflection a b), (Discernible.discernment.reflection a b).

Definition data_all_delivers_qword_discernible
  : forall (a : QWord) (b : QWord) .
      (QWord.equivalent a b = true <-> a = b) /\ (QWord.discern a b = true <-> ~ (a = b))
  := fun (a : QWord) (b : QWord) .
       conjoin (Discernible.equivalence.reflection a b), (Discernible.discernment.reflection a b).

Definition data_all_delivers_source_byte_discernible
  : forall (a : SourceByte) (b : SourceByte) .
      (SourceByte.equivalent a b = true <-> a = b)
      /\ (SourceByte.discern a b = true <-> ~ (a = b))
  := fun (a : SourceByte) (b : SourceByte) .
       conjoin (Discernible.equivalence.reflection a b), (Discernible.discernment.reflection a b).

Definition data_all_delivers_nat_discernible
  : forall (a : Nat) (b : Nat) .
      (Nat.equivalent a b = true <-> a = b) /\ (Nat.discern a b = true <-> ~ (a = b))
  := fun (a : Nat) (b : Nat) .
       conjoin (Discernible.equivalence.reflection a b), (Discernible.discernment.reflection a b).

Definition data_all_delivers_nat0_discernible
  : forall (a : Nat0) (b : Nat0) .
      (Nat0.equivalent a b = true <-> a = b) /\ (Nat0.discern a b = true <-> ~ (a = b))
  := fun (a : Nat0) (b : Nat0) .
       conjoin (Discernible.equivalence.reflection a b), (Discernible.discernment.reflection a b).

Definition data_all_delivers_integer_discernible
  : forall (a : Integer) (b : Integer) .
      (Integer.equivalent a b = true <-> a = b) /\ (Integer.discern a b = true <-> ~ (a = b))
  := fun (a : Integer) (b : Integer) .
       conjoin (Discernible.equivalence.reflection a b), (Discernible.discernment.reflection a b).

Definition data_all_delivers_rational_discernible
  : forall (a : Rational) (b : Rational) .
      (Rational.equivalent a b = true <-> a = b) /\ (Rational.discern a b = true <-> ~ (a = b))
  := fun (a : Rational) (b : Rational) .
       conjoin (Discernible.equivalence.reflection a b), (Discernible.discernment.reflection a b).

Definition data_all_delivers_bin_discernible
  : forall (a : Bin) (b : Bin) .
      (Bin.equivalent a b = true <-> a = b) /\ (Bin.discern a b = true <-> ~ (a = b))
  := fun (a : Bin) (b : Bin) .
       conjoin (Discernible.equivalence.reflection a b), (Discernible.discernment.reflection a b).

Definition data_all_delivers_bin0_discernible
  : forall (a : Bin0) (b : Bin0) .
      (Bin0.equivalent a b = true <-> a = b) /\ (Bin0.discern a b = true <-> ~ (a = b))
  := fun (a : Bin0) (b : Bin0) .
       conjoin (Discernible.equivalence.reflection a b), (Discernible.discernment.reflection a b).

Definition data_all_delivers_signed_bin_discernible
  : forall (a : SignedBin) (b : SignedBin) .
      (SignedBin.equivalent a b = true <-> a = b) /\ (SignedBin.discern a b = true <-> ~ (a = b))
  := fun (a : SignedBin) (b : SignedBin) .
       conjoin (Discernible.equivalence.reflection a b), (Discernible.discernment.reflection a b).

Definition data_all_delivers_uint8_discernible
  : forall (a : UInt8) (b : UInt8) .
      (UInt8.equivalent a b = true <-> a = b) /\ (UInt8.discern a b = true <-> ~ (a = b))
  := fun (a : UInt8) (b : UInt8) .
       conjoin (Discernible.equivalence.reflection a b), (Discernible.discernment.reflection a b).

Definition data_all_delivers_uint16_discernible
  : forall (a : UInt16) (b : UInt16) .
      (UInt16.equivalent a b = true <-> a = b) /\ (UInt16.discern a b = true <-> ~ (a = b))
  := fun (a : UInt16) (b : UInt16) .
       conjoin (Discernible.equivalence.reflection a b), (Discernible.discernment.reflection a b).

Definition data_all_delivers_uint32_discernible
  : forall (a : UInt32) (b : UInt32) .
      (UInt32.equivalent a b = true <-> a = b) /\ (UInt32.discern a b = true <-> ~ (a = b))
  := fun (a : UInt32) (b : UInt32) .
       conjoin (Discernible.equivalence.reflection a b), (Discernible.discernment.reflection a b).

Definition data_all_delivers_uint64_discernible
  : forall (a : UInt64) (b : UInt64) .
      (UInt64.equivalent a b = true <-> a = b) /\ (UInt64.discern a b = true <-> ~ (a = b))
  := fun (a : UInt64) (b : UInt64) .
       conjoin (Discernible.equivalence.reflection a b), (Discernible.discernment.reflection a b).

Definition data_all_delivers_int8_discernible
  : forall (a : Int8) (b : Int8) .
      (Int8.equivalent a b = true <-> a = b) /\ (Int8.discern a b = true <-> ~ (a = b))
  := fun (a : Int8) (b : Int8) .
       conjoin (Discernible.equivalence.reflection a b), (Discernible.discernment.reflection a b).

Definition data_all_delivers_int16_discernible
  : forall (a : Int16) (b : Int16) .
      (Int16.equivalent a b = true <-> a = b) /\ (Int16.discern a b = true <-> ~ (a = b))
  := fun (a : Int16) (b : Int16) .
       conjoin (Discernible.equivalence.reflection a b), (Discernible.discernment.reflection a b).

Definition data_all_delivers_int32_discernible
  : forall (a : Int32) (b : Int32) .
      (Int32.equivalent a b = true <-> a = b) /\ (Int32.discern a b = true <-> ~ (a = b))
  := fun (a : Int32) (b : Int32) .
       conjoin (Discernible.equivalence.reflection a b), (Discernible.discernment.reflection a b).

Definition data_all_delivers_int64_discernible
  : forall (a : Int64) (b : Int64) .
      (Int64.equivalent a b = true <-> a = b) /\ (Int64.discern a b = true <-> ~ (a = b))
  := fun (a : Int64) (b : Int64) .
       conjoin (Discernible.equivalence.reflection a b), (Discernible.discernment.reflection a b).

Definition data_all_delivers_ascii_discernible
  : forall (a : Ascii) (b : Ascii) .
      (Ascii.equivalent a b = true <-> a = b) /\ (Ascii.discern a b = true <-> ~ (a = b))
  := fun (a : Ascii) (b : Ascii) .
       conjoin (Discernible.equivalence.reflection a b), (Discernible.discernment.reflection a b).

Definition data_all_delivers_ascii_str_discernible
  : forall (a : AsciiStr) (b : AsciiStr) .
      (AsciiStr.equivalent a b = true <-> a = b) /\ (AsciiStr.discern a b = true <-> ~ (a = b))
  := fun (a : AsciiStr) (b : AsciiStr) .
       conjoin (Discernible.equivalence.reflection a b), (Discernible.discernment.reflection a b).

Definition data_all_delivers_utf8_discernible
  : forall (a : Utf8) (b : Utf8) .
      (Utf8.equivalent a b = true <-> a = b) /\ (Utf8.discern a b = true <-> ~ (a = b))
  := fun (a : Utf8) (b : Utf8) .
       conjoin (Discernible.equivalence.reflection a b), (Discernible.discernment.reflection a b).

Definition data_all_delivers_utf8_str_discernible
  : forall (a : Utf8Str) (b : Utf8Str) .
      (Utf8Str.equivalent a b = true <-> a = b) /\ (Utf8Str.discern a b = true <-> ~ (a = b))
  := fun (a : Utf8Str) (b : Utf8Str) .
       conjoin (Discernible.equivalence.reflection a b), (Discernible.discernment.reflection a b).

Definition data_all_delivers_kleene3_discernible
  : forall (a : Kleene3) (b : Kleene3) .
      (Kleene3.equivalent a b = true <-> a = b) /\ (Kleene3.discern a b = true <-> ~ (a = b))
  := fun (a : Kleene3) (b : Kleene3) .
       conjoin (Discernible.equivalence.reflection a b), (Discernible.discernment.reflection a b).

Definition data_all_delivers_month_discernible
  : forall (a : Month) (b : Month) .
      (Month.equivalent a b = true <-> a = b) /\ (Month.discern a b = true <-> ~ (a = b))
  := fun (a : Month) (b : Month) .
       conjoin (Discernible.equivalence.reflection a b), (Discernible.discernment.reflection a b).

Definition data_all_delivers_weekday_discernible
  : forall (a : Weekday) (b : Weekday) .
      (Weekday.equivalent a b = true <-> a = b) /\ (Weekday.discern a b = true <-> ~ (a = b))
  := fun (a : Weekday) (b : Weekday) .
       conjoin (Discernible.equivalence.reflection a b), (Discernible.discernment.reflection a b).

Definition data_all_delivers_date_discernible
  : forall (a : Date) (b : Date) .
      (Date.equivalent a b = true <-> a = b) /\ (Date.discern a b = true <-> ~ (a = b))
  := fun (a : Date) (b : Date) .
       conjoin (Discernible.equivalence.reflection a b), (Discernible.discernment.reflection a b).

Definition data_all_delivers_iso_week_date_discernible
  : forall (a : IsoWeekDate) (b : IsoWeekDate) .
      (IsoWeekDate.equivalent a b = true <-> a = b)
      /\ (IsoWeekDate.discern a b = true <-> ~ (a = b))
  := fun (a : IsoWeekDate) (b : IsoWeekDate) .
       conjoin (Discernible.equivalence.reflection a b), (Discernible.discernment.reflection a b).

Definition data_all_delivers_list_discernible
  : forall (A : Type) (tester : A -> A -> Bool) (D : Discernible tester)
        (a : List A) (b : List A) .
      (List.equivalent a b = true <-> a = b) /\ (List.discern a b = true <-> ~ (a = b))
  := fun (A : Type) (tester : A -> A -> Bool) (D : Discernible tester)
        (a : List A) (b : List A) .
       conjoin (Discernible.equivalence.reflection a b), (Discernible.discernment.reflection a b).

Definition data_all_delivers_non_empty_list_discernible
  : forall (A : Type) (tester : A -> A -> Bool) (D : Discernible tester)
        (a : NonEmptyList A) (b : NonEmptyList A) .
      (NonEmptyList.equivalent a b = true <-> a = b)
      /\ (NonEmptyList.discern a b = true <-> ~ (a = b))
  := fun (A : Type) (tester : A -> A -> Bool) (D : Discernible tester)
        (a : NonEmptyList A) (b : NonEmptyList A) .
       conjoin (Discernible.equivalence.reflection a b), (Discernible.discernment.reflection a b).

Definition data_all_delivers_option_discernible
  : forall (A : Type) (tester : A -> A -> Bool) (D : Discernible tester)
        (a : Option A) (b : Option A) .
      (Option.equivalent a b = true <-> a = b) /\ (Option.discern a b = true <-> ~ (a = b))
  := fun (A : Type) (tester : A -> A -> Bool) (D : Discernible tester)
        (a : Option A) (b : Option A) .
       conjoin (Discernible.equivalence.reflection a b), (Discernible.discernment.reflection a b).

Definition data_all_delivers_binary_tree_discernible
  : forall (A : Type) (tester : A -> A -> Bool) (D : Discernible tester)
        (a : BinaryTree A) (b : BinaryTree A) .
      (BinaryTree.equivalent a b = true <-> a = b)
      /\ (BinaryTree.discern a b = true <-> ~ (a = b))
  := fun (A : Type) (tester : A -> A -> Bool) (D : Discernible tester)
        (a : BinaryTree A) (b : BinaryTree A) .
       conjoin (Discernible.equivalence.reflection a b), (Discernible.discernment.reflection a b).

Definition data_all_delivers_avl_discernible
  : forall (A : Type) (tester : A -> A -> Bool) (D : Discernible tester)
        (a : AVL A) (b : AVL A) .
      (AVL.equivalent a b = true <-> a = b) /\ (AVL.discern a b = true <-> ~ (a = b))
  := fun (A : Type) (tester : A -> A -> Bool) (D : Discernible tester)
        (a : AVL A) (b : AVL A) .
       conjoin (Discernible.equivalence.reflection a b), (Discernible.discernment.reflection a b).

Definition data_all_delivers_sorted_set_discernible
  : forall (A : Type) (cmp : A -> A -> Comparison) (tester : A -> A -> Bool)
        (D : Discernible tester) (a : SortedSet cmp) (b : SortedSet cmp) .
      (SortedSet.equivalent a b = true <-> a = b)
      /\ (SortedSet.discern a b = true <-> ~ (a = b))
  := fun (A : Type) (cmp : A -> A -> Comparison) (tester : A -> A -> Bool)
        (D : Discernible tester) (a : SortedSet cmp) (b : SortedSet cmp) .
       conjoin (Discernible.equivalence.reflection a b), (Discernible.discernment.reflection a b).

Definition data_all_delivers_product_discernible
  : forall (A : Type) (B : Type)
        (first_tester : A -> A -> Bool) (second_tester : B -> B -> Bool)
        (DA : Discernible first_tester) (DB : Discernible second_tester)
        (a : A * B) (b : A * B) .
      (Product.equivalent a b = true <-> a = b) /\ (Product.discern a b = true <-> ~ (a = b))
  := fun (A : Type) (B : Type)
        (first_tester : A -> A -> Bool) (second_tester : B -> B -> Bool)
        (DA : Discernible first_tester) (DB : Discernible second_tester)
        (a : A * B) (b : A * B) .
       conjoin (Discernible.equivalence.reflection a b), (Discernible.discernment.reflection a b).

Definition data_all_delivers_coproduct_discernible
  : forall (A : Type) (B : Type)
        (left_tester : A -> A -> Bool) (right_tester : B -> B -> Bool)
        (DA : Discernible left_tester) (DB : Discernible right_tester)
        (a : Coproduct A B) (b : Coproduct A B) .
      (Coproduct.equivalent a b = true <-> a = b)
      /\ (Coproduct.discern a b = true <-> ~ (a = b))
  := fun (A : Type) (B : Type)
        (left_tester : A -> A -> Bool) (right_tester : B -> B -> Bool)
        (DA : Discernible left_tester) (DB : Discernible right_tester)
        (a : Coproduct A B) (b : Coproduct A B) .
       conjoin (Discernible.equivalence.reflection a b), (Discernible.discernment.reflection a b).

Definition data_all_delivers_numeral_decimal_digits_induction
  : forall (P : Numeral.Decimal.Digits -> Prop) .
      P Numeral.Decimal.Digits.End ->
      (forall (d : Numeral.Decimal.Digits) . P d -> P (Numeral.Decimal.Digits.Zero d)) ->
      (forall (d : Numeral.Decimal.Digits) . P d -> P (Numeral.Decimal.Digits.One d)) ->
      (forall (d : Numeral.Decimal.Digits) . P d -> P (Numeral.Decimal.Digits.Two d)) ->
      (forall (d : Numeral.Decimal.Digits) . P d -> P (Numeral.Decimal.Digits.Three d)) ->
      (forall (d : Numeral.Decimal.Digits) . P d -> P (Numeral.Decimal.Digits.Four d)) ->
      (forall (d : Numeral.Decimal.Digits) . P d -> P (Numeral.Decimal.Digits.Five d)) ->
      (forall (d : Numeral.Decimal.Digits) . P d -> P (Numeral.Decimal.Digits.Six d)) ->
      (forall (d : Numeral.Decimal.Digits) . P d -> P (Numeral.Decimal.Digits.Seven d)) ->
      (forall (d : Numeral.Decimal.Digits) . P d -> P (Numeral.Decimal.Digits.Eight d)) ->
      (forall (d : Numeral.Decimal.Digits) . P d -> P (Numeral.Decimal.Digits.Nine d)) ->
      (forall (d : Numeral.Decimal.Digits) . P d)
  := Numeral.Decimal.Digits.induction.

Definition data_all_delivers_numeral_hexadecimal_digits_test_reflection
  : forall (d1 : Numeral.Hexadecimal.Digits) (d2 : Numeral.Hexadecimal.Digits) .
      Numeral.Hexadecimal.Digits.test d1 d2 = true <-> d1 = d2
  := Numeral.Hexadecimal.Digits.test.reflection.

Definition data_all_computes_numeral_equivalent_of_one_number
  : Numeral.Unsigned.equivalent (Bin0.to_numeral 111%b0) (Bin0.to_numeral 111%b0) = true
  := Identity.reflexivity _.

Definition data_all_computes_numeral_discern_of_two_spellings
  : Numeral.Decimal.Digits.discern
      (Numeral.Decimal.Digits.Zero
        (Numeral.Decimal.Digits.Zero
          (Numeral.Decimal.Digits.Seven Numeral.Decimal.Digits.End)))
      (Numeral.Decimal.Digits.Seven Numeral.Decimal.Digits.End)
    = true
  := Identity.reflexivity _.

Definition data_all_delivers_numeral_decimal_digits_discernible
  : forall (a : Numeral.Decimal.Digits) (b : Numeral.Decimal.Digits) .
      (Numeral.Decimal.Digits.equivalent a b = true <-> a = b)
      /\ (Numeral.Decimal.Digits.discern a b = true <-> ~ (a = b))
  := fun (a : Numeral.Decimal.Digits) (b : Numeral.Decimal.Digits) .
       conjoin (Discernible.equivalence.reflection a b), (Discernible.discernment.reflection a b).

Definition data_all_delivers_numeral_decimal_signed_discernible
  : forall (a : Numeral.Decimal.Signed) (b : Numeral.Decimal.Signed) .
      (Numeral.Decimal.Signed.equivalent a b = true <-> a = b)
      /\ (Numeral.Decimal.Signed.discern a b = true <-> ~ (a = b))
  := fun (a : Numeral.Decimal.Signed) (b : Numeral.Decimal.Signed) .
       conjoin (Discernible.equivalence.reflection a b), (Discernible.discernment.reflection a b).

Definition data_all_delivers_numeral_decimal_fractional_discernible
  : forall (a : Numeral.Decimal.Fractional) (b : Numeral.Decimal.Fractional) .
      (Numeral.Decimal.Fractional.equivalent a b = true <-> a = b)
      /\ (Numeral.Decimal.Fractional.discern a b = true <-> ~ (a = b))
  := fun (a : Numeral.Decimal.Fractional) (b : Numeral.Decimal.Fractional) .
       conjoin (Discernible.equivalence.reflection a b), (Discernible.discernment.reflection a b).

Definition data_all_delivers_numeral_hexadecimal_digits_discernible
  : forall (a : Numeral.Hexadecimal.Digits) (b : Numeral.Hexadecimal.Digits) .
      (Numeral.Hexadecimal.Digits.equivalent a b = true <-> a = b)
      /\ (Numeral.Hexadecimal.Digits.discern a b = true <-> ~ (a = b))
  := fun (a : Numeral.Hexadecimal.Digits) (b : Numeral.Hexadecimal.Digits) .
       conjoin (Discernible.equivalence.reflection a b), (Discernible.discernment.reflection a b).

Definition data_all_delivers_numeral_hexadecimal_signed_discernible
  : forall (a : Numeral.Hexadecimal.Signed) (b : Numeral.Hexadecimal.Signed) .
      (Numeral.Hexadecimal.Signed.equivalent a b = true <-> a = b)
      /\ (Numeral.Hexadecimal.Signed.discern a b = true <-> ~ (a = b))
  := fun (a : Numeral.Hexadecimal.Signed) (b : Numeral.Hexadecimal.Signed) .
       conjoin (Discernible.equivalence.reflection a b), (Discernible.discernment.reflection a b).

Definition data_all_delivers_numeral_hexadecimal_fractional_discernible
  : forall (a : Numeral.Hexadecimal.Fractional) (b : Numeral.Hexadecimal.Fractional) .
      (Numeral.Hexadecimal.Fractional.equivalent a b = true <-> a = b)
      /\ (Numeral.Hexadecimal.Fractional.discern a b = true <-> ~ (a = b))
  := fun (a : Numeral.Hexadecimal.Fractional) (b : Numeral.Hexadecimal.Fractional) .
       conjoin (Discernible.equivalence.reflection a b), (Discernible.discernment.reflection a b).

Definition data_all_delivers_numeral_unsigned_discernible
  : forall (a : Numeral.Unsigned) (b : Numeral.Unsigned) .
      (Numeral.Unsigned.equivalent a b = true <-> a = b)
      /\ (Numeral.Unsigned.discern a b = true <-> ~ (a = b))
  := fun (a : Numeral.Unsigned) (b : Numeral.Unsigned) .
       conjoin (Discernible.equivalence.reflection a b), (Discernible.discernment.reflection a b).

Definition data_all_delivers_numeral_signed_discernible
  : forall (a : Numeral.Signed) (b : Numeral.Signed) .
      (Numeral.Signed.equivalent a b = true <-> a = b)
      /\ (Numeral.Signed.discern a b = true <-> ~ (a = b))
  := fun (a : Numeral.Signed) (b : Numeral.Signed) .
       conjoin (Discernible.equivalence.reflection a b), (Discernible.discernment.reflection a b).

Definition data_all_delivers_numeral_fractional_discernible
  : forall (a : Numeral.Fractional) (b : Numeral.Fractional) .
      (Numeral.Fractional.equivalent a b = true <-> a = b)
      /\ (Numeral.Fractional.discern a b = true <-> ~ (a = b))
  := fun (a : Numeral.Fractional) (b : Numeral.Fractional) .
       conjoin (Discernible.equivalence.reflection a b), (Discernible.discernment.reflection a b).

Definition data_all_delivers_json
  : Json
  := Json.Object
       (("a"%u8,
         Json.Array
           (Json.Null
             :: Json.Boolean true
             :: Json.Number 15%b_decimal (- 1%b0_decimal)%b_signed
             :: Json.String "b"%u8
             :: [])%list)%product
         :: [])%list.

Definition data_all_delivers_json_induction
  : forall (P : Json -> Prop) .
      P Json.Null ->
      (forall (b : Bool) . P (Json.Boolean b)) ->
      (forall (mantissa : SignedBin) (exponent : SignedBin) .
        P (Json.Number mantissa exponent)) ->
      (forall (s : Utf8Str) . P (Json.String s)) ->
      (forall (l : List Json) . List.All P l -> P (Json.Array l)) ->
      (forall (l : List (Utf8Str * Json)) .
        List.All (fun (p : Utf8Str * Json) . P (Product.second p)) l -> P (Json.Object l)) ->
      (forall (j : Json) . P j)
  := Json.induction.

Definition data_all_delivers_json_null_specification
  : forall (j : Json) . Json.is_null j = true <-> j = Json.Null
  := Json.null.specification.

Definition data_all_delivers_json_boolean_injectivity
  : forall (b1 : Bool) (b2 : Bool) . Json.Boolean b1 = Json.Boolean b2 -> b1 = b2
  := @Json.boolean.injectivity.

Definition data_all_delivers_json_boolean_specification
  : forall (j : Json) (b : Bool) . Json.boolean j = Some b <-> j = Json.Boolean b
  := Json.boolean.specification.

Definition data_all_delivers_json_number_injectivity
  : forall (mantissa1 : SignedBin) (exponent1 : SignedBin)
        (mantissa2 : SignedBin) (exponent2 : SignedBin) .
      Json.Number mantissa1 exponent1 = Json.Number mantissa2 exponent2 ->
      mantissa1 = mantissa2 /\ exponent1 = exponent2
  := @Json.number.injectivity.

Definition data_all_delivers_json_number_specification
  : forall (j : Json) (mantissa : SignedBin) (exponent : SignedBin) .
      Json.number j = Some (mantissa, exponent)%product <-> j = Json.Number mantissa exponent
  := Json.number.specification.

Definition data_all_delivers_json_string_injectivity
  : forall (s1 : Utf8Str) (s2 : Utf8Str) . Json.String s1 = Json.String s2 -> s1 = s2
  := @Json.string.injectivity.

Definition data_all_delivers_json_string_specification
  : forall (j : Json) (s : Utf8Str) . Json.string j = Some s <-> j = Json.String s
  := Json.string.specification.

Definition data_all_delivers_json_array_injectivity
  : forall (l1 : List Json) (l2 : List Json) . Json.Array l1 = Json.Array l2 -> l1 = l2
  := @Json.array.injectivity.

Definition data_all_delivers_json_array_specification
  : forall (j : Json) (l : List Json) . Json.array j = Some l <-> j = Json.Array l
  := Json.array.specification.

Definition data_all_delivers_json_object_injectivity
  : forall (l1 : List (Utf8Str * Json)) (l2 : List (Utf8Str * Json)) .
      Json.Object l1 = Json.Object l2 -> l1 = l2
  := @Json.object.injectivity.

Definition data_all_delivers_json_object_specification
  : forall (j : Json) (l : List (Utf8Str * Json)) .
      Json.object j = Some l <-> j = Json.Object l
  := Json.object.specification.

Definition data_all_delivers_json_is_null_of_null
  : Json.is_null Json.Null = true
  := Identity.reflexivity _.

Definition data_all_delivers_json_is_null_of_a_boolean
  : Json.is_null (Json.Boolean false) = false
  := Identity.reflexivity _.

Definition data_all_delivers_json_boolean_of_a_boolean
  : Json.boolean (Json.Boolean true) = Some true
  := Identity.reflexivity _.

Definition data_all_delivers_json_boolean_of_null
  : Json.boolean Json.Null = None
  := Identity.reflexivity _.

Definition data_all_delivers_json_number_of_a_number
  : Json.number (Json.Number 15%b_decimal (- 1%b0_decimal)%b_signed)
    = Some (SignedBin.Positive 15%b_decimal, (- 1%b0_decimal)%b_signed)%product
  := Identity.reflexivity _.

Definition data_all_delivers_json_string_of_a_string
  : Json.string (Json.String "b"%u8) = Some "b"%u8
  := Identity.reflexivity _.

Definition data_all_delivers_json_array_of_an_array
  : Json.array (Json.Array (Json.Null :: [])%list) = Some (Json.Null :: [])%list
  := Identity.reflexivity _.

Definition data_all_delivers_json_array_of_an_object
  : Json.array (Json.Object []%list) = None
  := Identity.reflexivity _.

Definition data_all_delivers_json_object_of_an_object
  : Json.object (Json.Object (("a"%u8, Json.Null)%product :: [])%list)
    = Some (("a"%u8, Json.Null)%product :: [])%list
  := Identity.reflexivity _.
