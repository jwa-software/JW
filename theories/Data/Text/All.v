(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

(* Umbrella for [JW.Data.Text]: re-exports the text types, so a client imports
 * them with [From JW Require Import Data.Text.All].
 *
 * [SourceByte] is a byte of the source text, the form a string literal
 * arrives in; [Ascii] is a character of one byte, ASCII below 128 and Latin-1
 * above; [AsciiStr] is a string of [Ascii] characters; [Utf8] is a Unicode
 * character, held as its UTF-8 bytes; [Utf8Str] is a string of [Utf8]
 * characters.
 *)
(* The modules below only [Import] [Core.All], so the open scope reaches a
 * client of this umbrella only from here.
 *)
From JW Require Export Core.All.

(* An umbrella exports every type the interfaces under it name: [Byte] for
 * the conversions to and from bytes, [List] and [Option] for those to and
 * from a string literal and a list of characters, [Nat0] for a length,
 * [UInt8] and [UInt32] for a character's code, [Comparison] for a comparison, [Bool]
 * for a character class, [Assert] for the proof a [Utf8] character carries
 * and [Comparable] for the instance an order is.
 *)
From JW Require Export Data.Assert.
From JW Require Export Data.Base.Bool.
From JW Require Export Data.Base.Comparison.
From JW Require Export Data.Collection.List.
From JW Require Export Data.Comparable.
From JW Require Export Data.Machine.Byte.
From JW Require Export Data.Machine.UInt32.
From JW Require Export Data.Machine.UInt8.
From JW Require Export Data.Number.Nat0.
From JW Require Export Data.Option.

From JW Require Export Data.Text.Ascii.
From JW Require Export Data.Text.AsciiStr.
From JW Require Export Data.Text.SourceByte.
From JW Require Export Data.Text.Utf8.
From JW Require Export Data.Text.Utf8Str.
