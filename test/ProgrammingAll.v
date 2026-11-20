(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

(* [Programming] holds no module, so this guard checks only that its umbrella
 * loads. It is here so that every umbrella has its own guard, and a module
 * added to the layer brings its entries to this file.
 *)
From jwa Require Import Programming.All.
