(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

(* [Assumption] holds no module, so this guard checks only that its umbrella
 * loads. No other guard reaches this layer, [JW.All] leaving it out, so this
 * is where an axiom added to it is checked for export.
 *)
From JW Require Import Assumption.All.
