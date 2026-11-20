(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

(* The extraction plugin ships with Rocq in [Corelib], apart from its
 * standard library, so loading it brings in nothing but the command.
 *)
From Corelib Require Extraction.
From jwa Require Import Data.All.

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

(* Every module of [Data] that computes, into one file [jwa.ml]: the proofs
 * are erased, so [SortedSet.T] becomes the [AVL.T] it holds.
 *)
Extraction "jwa.ml"
  jwa.Data.Base.Bool.Bool
  jwa.Data.Base.Comparison.Comparison
  jwa.Data.Base.Empty.Empty
  jwa.Data.Base.Kleene3.Kleene3
  jwa.Data.Base.Unit.Unit
  jwa.Data.Comparable.Comparable
  jwa.Data.Coproduct.Coproduct
  jwa.Data.Option.Option
  jwa.Data.Product.Product
  jwa.Data.Number.Nat.Nat
  jwa.Data.Number.Nat0.Nat0
  jwa.Data.Number.Integer.Integer
  jwa.Data.Number.Rational.Rational
  jwa.Data.Number.Numeral.Numeral
  jwa.Data.Number.Binary.BinBase.BinBase
  jwa.Data.Number.Binary.BinWithZero.BinWithZero
  jwa.Data.Number.Binary.Bin.Bin
  jwa.Data.Machine.Bit.Bit
  jwa.Data.Machine.Byte.Byte
  jwa.Data.Machine.Endian.Endian
  jwa.Data.Machine.HWord.HWord
  jwa.Data.Machine.Word.Word
  jwa.Data.Machine.DWord.DWord
  jwa.Data.Machine.QWord.QWord
  jwa.Data.Machine.UInt8.UInt8
  jwa.Data.Machine.UInt16.UInt16
  jwa.Data.Machine.UInt32.UInt32
  jwa.Data.Machine.UInt64.UInt64
  jwa.Data.Machine.Int8.Int8
  jwa.Data.Machine.Int16.Int16
  jwa.Data.Machine.Int32.Int32
  jwa.Data.Machine.Int64.Int64
  jwa.Data.Collection.List.List
  jwa.Data.Collection.NonEmptyList.NonEmptyList
  jwa.Data.Collection.BinaryTree.BinaryTree
  jwa.Data.Collection.BST.BST
  jwa.Data.Collection.AVL.AVL
  jwa.Data.Collection.SortedSet.SortedSet
  jwa.Data.Text.SourceByte.SourceByte
  jwa.Data.Text.Ascii.Ascii
  jwa.Data.Text.AsciiStr.AsciiStr
  jwa.Data.Text.Utf8.Utf8
  jwa.Data.Text.Utf8Str.Utf8Str.
