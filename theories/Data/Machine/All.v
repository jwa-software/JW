(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

(* Umbrella for [JW.Data.Machine]: re-exports the machine units, so a client
 * imports them with [From JW Require Import Data.Machine.All].
 *
 * A machine unit is a value of fixed width, the shape a machine stores and
 * moves. [Bit] is one binary digit, [Byte] eight, [HWord] sixteen, [Word]
 * thirty-two, [DWord] sixty-four, [QWord] a hundred and twenty-eight, [UInt8]
 * a [Byte] read as a number from 0 to 255, [Int8] a [Byte] read in two's
 * complement, from -128 to 127, [UInt16] two [Byte]s read as a number from 0
 * to 65535, [Int16] two [Byte]s read in two's complement, from -32768 to
 * 32767, [UInt32] four [Byte]s read as a number from 0 to 4294967295,
 * [Int32] four [Byte]s read in two's complement, from -2147483648 to
 * 2147483647, [UInt64] eight [Byte]s read as a number from 0 to
 * 18446744073709551615, and [Int64] eight [Byte]s read in two's complement,
 * from -9223372036854775808 to 9223372036854775807.
 *)
(* The modules below only [Import] [Core.All], so the open scope reaches a
 * client of this umbrella only from here.
 *)
From JW Require Export Core.All.

(* An umbrella exports every type the interfaces under it name: [Bool] for
 * [Bit.from_bool] and [Bit.to_bool], [Nat] and [Nat0] for the counts of the
 * shifts and rotations, [BinBase], [BinWithZero] and [Bin] for the values,
 * [Nat0] and [Integer] for the values read in unary, [Product] for the
 * carry, the borrow and the overflow, [Comparison] for [compare], [Numeral]
 * and [Option] for the literals, [List] for the bytes of a word, [Endian]
 * for the order they are laid out in, [Comparable] for the instance each
 * integer's order is.
 *)
From JW Require Export Data.Base.Bool.
From JW Require Export Data.Base.Comparison.
From JW Require Export Data.Collection.List.
From JW Require Export Data.Comparable.
From JW Require Export Data.Number.Binary.Bin.
From JW Require Export Data.Number.Binary.BinBase.
From JW Require Export Data.Number.Binary.BinWithZero.
From JW Require Export Data.Number.Integer.
From JW Require Export Data.Number.Nat.
From JW Require Export Data.Number.Nat0.
From JW Require Export Data.Number.Numeral.
From JW Require Export Data.Option.
From JW Require Export Data.Product.

From JW Require Export Data.Machine.Bit.
From JW Require Export Data.Machine.Byte.
From JW Require Export Data.Machine.DWord.
From JW Require Export Data.Machine.Endian.
From JW Require Export Data.Machine.HWord.
From JW Require Export Data.Machine.Int16.
From JW Require Export Data.Machine.Int32.
From JW Require Export Data.Machine.Int64.
From JW Require Export Data.Machine.Int8.
From JW Require Export Data.Machine.Modular.
From JW Require Export Data.Machine.QWord.
From JW Require Export Data.Machine.Signed.
From JW Require Export Data.Machine.UInt16.
From JW Require Export Data.Machine.UInt32.
From JW Require Export Data.Machine.UInt64.
From JW Require Export Data.Machine.UInt8.
From JW Require Export Data.Machine.Unsigned.
From JW Require Export Data.Machine.Word.
