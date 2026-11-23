(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

From JW Require Import Data.Base.All.

Definition data_base_all_delivers_bool
  : Bool
  := true.

Definition data_base_all_delivers_comparison
  : Comparison
  := Comparison.Eq.

Definition data_base_all_delivers_kleene3
  : Kleene3
  := Kleene3.unknown.

Definition data_base_all_delivers_kleene3_without_excluded_middle
  : (Kleene3.unknown || ! Kleene3.unknown)%k3 = Kleene3.unknown
  := Identity.reflexivity Kleene3.unknown.

Definition data_base_all_delivers_kleene3_without_noncontradiction
  : (Kleene3.unknown && ! Kleene3.unknown)%k3 = Kleene3.unknown
  := Identity.reflexivity Kleene3.unknown.

Definition data_base_all_delivers_kleene3_de_morgan
  : forall (v1 : Kleene3) (v2 : Kleene3) .
      (! (v1 && v2))%k3 = (! v1 || ! v2)%k3
  := Kleene3.negation.de_morgan.conjunction.

Definition data_base_all_delivers_kleene3_from_bool
  : Kleene3.from_bool true = Kleene3.true
  := Identity.reflexivity Kleene3.true.

Definition data_base_all_delivers_kleene3_implication_unknown
  : Kleene3.implies Kleene3.unknown Kleene3.unknown = Kleene3.unknown
  := Identity.reflexivity Kleene3.unknown.

Definition data_base_all_delivers_kleene3_conversion_exclusion
  : forall (b : Bool) . ~ (Kleene3.from_bool b = Kleene3.unknown)
  := Kleene3.conversion.exclusion.

Definition data_base_all_delivers_kleene3_compare
  : Kleene3.compare Kleene3.unknown Kleene3.true = Comparison.Lt
  := Identity.reflexivity Comparison.Lt.

Definition data_base_all_delivers_kleene3_truth_order
  : (Kleene3.false < Kleene3.true)%k3
  := I.

Definition data_base_all_delivers_kleene3_truth_strict_transitivity
  : forall (v1 : Kleene3) (v2 : Kleene3) (v3 : Kleene3) .
      (v1 < v2)%k3 -> (v2 < v3)%k3 -> (v1 < v3)%k3
  := @Kleene3.truth.strict.transitivity.

Definition data_base_all_delivers_kleene3_kleene_condition
  : forall (v1 : Kleene3) (v2 : Kleene3) . (v1 && ! v1 <= v2 || ! v2)%k3
  := Kleene3.negation.kleene.

Definition data_base_all_delivers_kleene3_information_bottom
  : forall (v : Kleene3) . (Kleene3.unknown [= v)%k3
  := Kleene3.information.bottom.

Definition data_base_all_delivers_kleene3_information_incomparability
  : ~ ((Kleene3.true [= Kleene3.false)%k3) /\ ~ ((Kleene3.false [= Kleene3.true)%k3)
  := Kleene3.information.incomparability.

Definition data_base_all_delivers_kleene3_information_monotonicity_conjunction
  : forall (v1 : Kleene3) (v1' : Kleene3) (v2 : Kleene3) (v2' : Kleene3) .
      (v1 [= v1')%k3 -> (v2 [= v2')%k3 -> (v1 && v2 [= v1' && v2')%k3
  := @Kleene3.information.monotonicity.conjunction.

Definition data_base_all_delivers_kleene3_information_monotonicity_implication
  : forall (v1 : Kleene3) (v1' : Kleene3) (v2 : Kleene3) (v2' : Kleene3) .
      (v1 [= v1')%k3 -> (v2 [= v2')%k3 ->
      (Kleene3.implies v1 v2 [= Kleene3.implies v1' v2')%k3
  := @Kleene3.information.monotonicity.implication.

Definition data_base_all_delivers_kleene3_conjunction_truth_specification
  : forall (v1 : Kleene3) (v2 : Kleene3) .
      (v1 && v2)%k3 = Kleene3.true <-> v1 = Kleene3.true /\ v2 = Kleene3.true
  := Kleene3.conjunction.truth.specification.

Definition data_base_all_delivers_kleene3_conjunction_falsity_specification
  : forall (v1 : Kleene3) (v2 : Kleene3) .
      (v1 && v2)%k3 = Kleene3.false <-> v1 = Kleene3.false \/ v2 = Kleene3.false
  := Kleene3.conjunction.falsity.specification.

Definition data_base_all_delivers_kleene3_disjunction_truth_specification
  : forall (v1 : Kleene3) (v2 : Kleene3) .
      (v1 || v2)%k3 = Kleene3.true <-> v1 = Kleene3.true \/ v2 = Kleene3.true
  := Kleene3.disjunction.truth.specification.

Definition data_base_all_delivers_kleene3_disjunction_falsity_specification
  : forall (v1 : Kleene3) (v2 : Kleene3) .
      (v1 || v2)%k3 = Kleene3.false <-> v1 = Kleene3.false /\ v2 = Kleene3.false
  := Kleene3.disjunction.falsity.specification.

Definition data_base_all_delivers_kleene3_negation_truth_specification
  : forall (v : Kleene3) . (! v)%k3 = Kleene3.true <-> v = Kleene3.false
  := Kleene3.negation.truth.specification.

Definition data_base_all_delivers_kleene3_negation_falsity_specification
  : forall (v : Kleene3) . (! v)%k3 = Kleene3.false <-> v = Kleene3.true
  := Kleene3.negation.falsity.specification.

Definition data_base_all_delivers_kleene3_negation_unknown_specification
  : forall (v : Kleene3) . (! v)%k3 = Kleene3.unknown <-> v = Kleene3.unknown
  := Kleene3.negation.unknown.specification.

Definition data_base_all_delivers_kleene3_conversion_truth_specification
  : forall (b : Bool) . Kleene3.from_bool b = Kleene3.true <-> b = true
  := Kleene3.conversion.truth.specification.

Definition data_base_all_delivers_kleene3_conversion_falsity_specification
  : forall (b : Bool) . Kleene3.from_bool b = Kleene3.false <-> b = false
  := Kleene3.conversion.falsity.specification.

Definition data_base_all_delivers_kleene3_conversion_retraction
  : forall (b : Bool) . Kleene3.to_bool (Kleene3.from_bool b) = Option.Some b
  := Kleene3.conversion.retraction.

Definition data_base_all_delivers_kleene3_conversion_inversion
  : forall (v : Kleene3) (b : Bool) .
      Kleene3.to_bool v = Option.Some b <-> v = Kleene3.from_bool b
  := Kleene3.conversion.inversion.

Definition data_base_all_delivers_kleene3_conversion_unknown_specification
  : forall (v : Kleene3) . Kleene3.to_bool v = Option.None <-> v = Kleene3.unknown
  := Kleene3.conversion.unknown.specification.

Definition data_base_all_delivers_kleene3_test_truth_specification
  : forall (v : Kleene3) . Kleene3.is_true v = true <-> v = Kleene3.true
  := Kleene3.test.truth.specification.

Definition data_base_all_delivers_kleene3_test_falsity_specification
  : forall (v : Kleene3) . Kleene3.is_not_false v = false <-> v = Kleene3.false
  := Kleene3.test.falsity.specification.

Definition data_base_all_delivers_kleene3_test_weakening
  : forall (v : Kleene3) . Kleene3.is_true v = true -> Kleene3.is_not_false v = true
  := Kleene3.test.weakening.

Definition data_base_all_delivers_kleene3_test_absorption
  : forall (v : Kleene3) .
      Bool.and (Kleene3.is_not_false v) (Kleene3.is_true v) = Kleene3.is_true v
  := Kleene3.test.absorption.

Definition data_base_all_delivers_kleene3_test_truth_conversion
  : forall (b : Bool) . Kleene3.is_true (Kleene3.from_bool b) = b
  := Kleene3.test.truth.conversion.

Definition data_base_all_delivers_kleene3_test_falsity_conversion
  : forall (b : Bool) . Kleene3.is_not_false (Kleene3.from_bool b) = b
  := Kleene3.test.falsity.conversion.

Definition data_base_all_delivers_kleene3_test_truth_conjunction
  : forall (v1 : Kleene3) (v2 : Kleene3) .
      Kleene3.is_true (v1 && v2)%k3 = Bool.and (Kleene3.is_true v1) (Kleene3.is_true v2)
  := Kleene3.test.truth.conjunction.

Definition data_base_all_delivers_kleene3_test_truth_disjunction
  : forall (v1 : Kleene3) (v2 : Kleene3) .
      Kleene3.is_true (v1 || v2)%k3 = Bool.or (Kleene3.is_true v1) (Kleene3.is_true v2)
  := Kleene3.test.truth.disjunction.

Definition data_base_all_delivers_kleene3_test_falsity_conjunction
  : forall (v1 : Kleene3) (v2 : Kleene3) .
      Kleene3.is_not_false (v1 && v2)%k3
      = Bool.and (Kleene3.is_not_false v1) (Kleene3.is_not_false v2)
  := Kleene3.test.falsity.conjunction.

Definition data_base_all_delivers_kleene3_test_falsity_disjunction
  : forall (v1 : Kleene3) (v2 : Kleene3) .
      Kleene3.is_not_false (v1 || v2)%k3
      = Bool.or (Kleene3.is_not_false v1) (Kleene3.is_not_false v2)
  := Kleene3.test.falsity.disjunction.

Definition data_base_all_delivers_kleene3_test_truth_negation
  : forall (v : Kleene3) .
      Kleene3.is_true (! v)%k3 = Bool.negate (Kleene3.is_not_false v)
  := Kleene3.test.truth.negation.

Definition data_base_all_delivers_kleene3_test_falsity_negation
  : forall (v : Kleene3) .
      Kleene3.is_not_false (! v)%k3 = Bool.negate (Kleene3.is_true v)
  := Kleene3.test.falsity.negation.

Definition data_base_all_computes_kleene3_to_bool_unknown
  : Kleene3.to_bool Kleene3.unknown = Option.None
  := Identity.reflexivity _.

Definition data_base_all_computes_kleene3_is_true_unknown
  : Kleene3.is_true Kleene3.unknown = false
  := Identity.reflexivity _.

Definition data_base_all_computes_kleene3_is_not_false_unknown
  : Kleene3.is_not_false Kleene3.unknown = true
  := Identity.reflexivity _.

Definition data_base_all_delivers_unit
  : Unit
  := Unit.introduction.

Definition data_base_all_delivers_empty
  : forall (A : Type) . Empty -> A
  := fun (A : Type) . Empty.elimination A.
