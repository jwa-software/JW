(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

From JW Require Import Core.All.

Module Endian. (* Endian *)

(* The order in which the bytes of a word are laid out: [Little] puts the
 * least significant byte first, [Big] the most significant.
 *)
Inductive T : Type :=
  | Little : T
  | Big : T.

Abbreviation Endian := T.

End Endian. (* Endian *)

Abbreviation Endian := Endian.T.
