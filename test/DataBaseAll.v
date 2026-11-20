(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

From jwa Require Import Data.Base.All.

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

Definition data_base_all_delivers_unit
  : Unit
  := Unit.introduction.

Definition data_base_all_delivers_empty
  : forall (A : Type) . Empty -> A
  := fun (A : Type) . Empty.elimination A.
