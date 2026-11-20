(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

From JW Require Import Core.Logic.All.

Definition core_logic_all_delivers
  : forall (A : Prop) (B : Prop) (T : Type) (Q : T -> Prop) .
      A /\ B -> B \/ A -> A _\/_ B -> ~ A -> (A <-> B) -> A -/> B
      -> (forsome t . Q t) -> Falsum -> Verum
  := fun (A : Prop) (B : Prop) (T : Type) (Q : T -> Prop)
         (_ : A /\ B) (_ : B \/ A) (_ : A _\/_ B)
         (_ : ~ A) (_ : A <-> B) (_ : A -/> B)
         (_ : forsome t . Q t)
         (_ : Falsum) . I.
