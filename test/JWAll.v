(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

From JW Require Import All.

Definition jw_all_delivers
  : forall (A : Prop) (T : Type) (o : Option T) .
      A /\ ~ A -> Option.map (fun (t : T) . t) o = o -> Verum
  := fun (A : Prop) (T : Type) (o : Option T)
         (_ : A /\ ~ A) (_ : Option.map (fun (t : T) . t) o = o) . I.
