(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

(* The extraction plugin ships with Rocq in [Corelib], apart from its
 * standard library, so loading it brings in nothing but the command.
 *)
From Corelib Require Extraction.
From JW Require Import Data.All.

(* Each name below is a module, and also the prefix of the abbreviation of
 * the same name inside it, as [Bool.Bool]; extraction warns of the two
 * readings and takes the module, which is the one meant.
 *)
Set Warnings "-extraction-ambiguous-name".

(* The files land beside this one in the build directory, which is where dune
 * looks for them; extraction warns that it chose that directory by default.
 *)
Set Warnings "-extraction-default-directory".

Extraction Language OCaml.

(* Four types become their OCaml counterparts. Each mapping is trusted: the
 * constructors are paired with the OCaml ones by position, in the order the
 * [Inductive] declares them, and nothing checks the pairing. [Option]
 * declares [None] first. A wrong order for [Option], [Product] or [List]
 * fails to compile, the arities differing; for [Bool] it would compile and
 * swap [true] and [false], which [extraction_test.ml] would catch.
 *)
Extract Inductive JW.Data.Base.Bool.Bool.T       => "bool"   [ "true" "false" ].
Extract Inductive JW.Data.Option.Option.T        => "option" [ "None" "Some" ].
Extract Inductive JW.Data.Product.Product.T      => "( * )"  [ "(,)" ].
Extract Inductive JW.Data.Collection.List.List.T => "list"   [ "[]" "(::)" ].

(* Every module of [Data] that computes, into one file [JW.ml]: the proofs
 * are erased, so [SortedSet.T] becomes the [AVL.T] it holds.
 *)
Extraction "JW.ml"
  JW.Data.Base.Bool.Bool
  JW.Data.Base.Comparison.Comparison
  JW.Data.Base.Empty.Empty
  JW.Data.Base.Kleene3.Kleene3
  JW.Data.Base.Unit.Unit
  JW.Data.Calendar.Month.Month
  JW.Data.Calendar.Weekday.Weekday
  JW.Data.Calendar.Gregorian.Date.Date
  JW.Data.Calendar.Gregorian.IsoWeekDate.IsoWeekDate
  JW.Data.Comparable.Comparable
  JW.Data.Coproduct.Coproduct
  JW.Data.Option.Option
  JW.Data.Product.Product
  JW.Data.Number.Nat.Nat
  JW.Data.Number.Nat0.Nat0
  JW.Data.Number.Integer.Integer
  JW.Data.Number.Rational.Rational
  JW.Data.Number.Numeral.Numeral
  JW.Data.Number.Binary.Bin.Bin
  JW.Data.Number.Binary.Bin0.Bin0
  JW.Data.Number.Binary.SignedBin.SignedBin
  JW.Data.Machine.Bit.Bit
  JW.Data.Machine.Byte.Byte
  JW.Data.Machine.Endian.Endian
  JW.Data.Machine.HWord.HWord
  JW.Data.Machine.Word.Word
  JW.Data.Machine.DWord.DWord
  JW.Data.Machine.QWord.QWord
  JW.Data.Machine.UInt8.UInt8
  JW.Data.Machine.UInt16.UInt16
  JW.Data.Machine.UInt32.UInt32
  JW.Data.Machine.UInt64.UInt64
  JW.Data.Machine.Int8.Int8
  JW.Data.Machine.Int16.Int16
  JW.Data.Machine.Int32.Int32
  JW.Data.Machine.Int64.Int64
  JW.Data.Collection.List.List
  JW.Data.Collection.NonEmptyList.NonEmptyList
  JW.Data.Collection.BinaryTree.BinaryTree
  JW.Data.Collection.BST.BST
  JW.Data.Collection.AVL.AVL
  JW.Data.Collection.SortedSet.SortedSet
  JW.Data.Text.SourceByte.SourceByte
  JW.Data.Text.Ascii.Ascii
  JW.Data.Text.AsciiStr.AsciiStr
  JW.Data.Text.Utf8.Utf8
  JW.Data.Text.Utf8Str.Utf8Str.
