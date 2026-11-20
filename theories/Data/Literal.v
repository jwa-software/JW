(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

(* The plugin behind [Number Notation] and [String Notation]: a file declaring
 * either command requires this one, which loads the plugin and so makes the
 * command exist.
 *)
Declare ML Module "rocq-runtime.plugins.number_string_notation".
