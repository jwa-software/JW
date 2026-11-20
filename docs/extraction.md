<!--
SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
SPDX-License-Identifier: MIT
-->

# Extraction

A definition proved correct in Rocq can be run outside it. Rocq's extraction turns the definitions into OCaml source, erases every proof, and leaves code that computes what the definitions compute. `extraction/` does this for the library and checks the result on every build.

- **The plugin comes with Rocq.** `From Corelib Require Extraction` loads it; `Corelib` ships with Rocq apart from its standard library, so the library keeps its `-noinit` builds.
- **The library itself is unchanged.** `extraction/` is outside `theories/`, and no theory imports it.
- **The output is generated, never committed.** `make build` writes it under `_build/default/extraction/`, as it writes the `.vo` files.

---

## What is extracted

`extraction/Extract.v` extracts every module of `Data` that computes into one OCaml module, `Jwa`, in `jwa.ml` and `jwa.mli`:

- the base types `Bool`, `Comparison`, `Empty`, `Unit` and `Kleene3`, with `Comparable`, `Coproduct`, `Option` and `Product`;
- the numbers `Nat`, `Nat0`, `Integer`, `Rational`, `Numeral`, `BinBase`, `BinWithZero` and `Bin`;
- the machine units `Bit`, `Byte`, `Endian`, `HWord` to `QWord`, `UInt8` to `UInt64` and `Int8` to `Int64`;
- the collections `List`, `NonEmptyList`, `BinaryTree`, `BST`, `AVL` and `SortedSet`;
- the text types `SourceByte`, `Ascii`, `AsciiStr`, `Utf8` and `Utf8Str`.

`Assert` is a proposition and erases entirely; `Literal` only serves the parsing of literals; `Functor`, `Membership` and `Sized` are classes with no computation of their own.

---

## What the output looks like

- **Each type keeps its module.** `SortedSet.insert` is `Jwa.SortedSet.insert`, `Kleene3.and` is `Jwa.Kleene3.coq_and`, and a type `T` is `coq_T`: the extractor escapes names that OCaml reserves or that would clash, with the prefix `coq_` or `Coq_`.
- **Proofs disappear.** `SortedSet.T` holds a tree and a proof that the tree is valid; in OCaml it is the tree alone, `'a AVL.coq_T`, and `SortedSet.insert` is `AVL.insert`.
- **An instance argument that is a proof disappears with it.** `SortedSet.insert` takes `cmp`, the element and the set; the `Comparable` instance is gone.
- **A case a proof ruled out becomes `assert false`.** `Nat0.divide.nat.safe` divides by a number proved nonzero, and its zero branch, which cannot run, extracts to `assert false`.
- **The types are the library's own.** `Bool` is `Jwa.Bool.coq_T`, with `Coq_true` and `Coq_false`, not OCaml's `bool`; `List` is `Jwa.List.coq_T`, with `Nil` and `Cons`.
- **The numbers are unary.** `Nat` is `One` or `Successor n`, so the number `1000` is a chain of a thousand constructors. Arithmetic on large values is slow, and `Rational` is built on these numbers.

---

## The test

`extraction/extraction_test.ml` runs the extracted code on known values and fails on a wrong one: it builds a `SortedSet` from `1`, `3` and `2` and checks its elements, membership, removal and size, checks that `UInt8.add` wraps `200 + 100` to `44`, and checks two cases of `Kleene3`. OCaml integers go in and come out through conversions to and from the unary numbers.

- **`make build`** extracts the code and compiles it, the library `jwa_extraction` and the test with it.
- **`make test`** runs the test. CI runs it after the build.

---

## What is not there yet

- **No type is mapped to an OCaml one.** Rocq's `Extract Inductive` can make `Bool` OCaml's `bool` or `Nat0` an OCaml integer, but each such mapping is trusted: the extractor takes it on faith, and a wrong one is not caught.
- **The OCaml library is not installed.** `jwa_extraction` has no public name, so an opam installation of `rocq-jwa` leaves it out; only code inside the repository can use it.
