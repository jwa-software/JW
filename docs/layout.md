<!--
SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
SPDX-License-Identifier: MIT
-->

# Layout

The library lives under `theories/`, **one directory per layer**. Each layer:

- is one dune theory under the logical root `JW`: `theories/Data/` is `JW.Data`;
- has an umbrella module `All` that re-exports the whole layer;
- lists `Ltac2` among its dependencies.

---

## The layers

| Layer | Purpose | Depends on |
|:---|:---|:---|
| `JW.Dialect` | The tactic language: Ltac2 with Rocq's tactic syntax hidden, and the tactics that name no definition of the library | -- |
| `JW.Core` | Base definitions, notations, the connectives and equality, the instance hint database and the minimal lemmas everything else shares | Dialect |
| `JW.Tactics` | Tactics that apply the laws of Core: the rules of inference by name, the laws of `=` as terms, witnesses | Dialect, Core |
| `JW.Algebra` | Algebraic structures, from semigroups to rings, and their theory | Dialect, Core |
| `JW.Relation` | Orders, well-founded and equivalence relations | Dialect, Core, Tactics |
| `JW.Data` | Concrete data types: the base types, the machine units, products, coproducts, options, the numbers, lists, text, and the functor class they instantiate | Dialect, Core, Tactics, Algebra, Relation |
| `JW.Assumption` | Axioms: classical principles, extensionality, decidability; the layer holds only its umbrella | Dialect, Core |
| `JW.All` | `From JW Require Import All` brings in every layer except Assumption | every layer but Assumption |

**`Assumption` is the only layer that may introduce axioms**, and no other layer depends on it, so everything else stays axiom-free under `Print Assumptions`, the command its name is taken from. Import it explicitly, with `From JW Require Import Assumption.All`, when a development needs it.

---

## Beside the layers

Two directories sit beside `theories/` and are not part of the library: an opam installation leaves both out.

| Directory | Holds |
|:---|:---|
| `test/` | The theory `jw_test`: one file per umbrella, each importing that umbrella alone, and `TacticsAll.v` for the tactics |
| `extraction/` | `Extract.v`, which extracts the computing modules of `Data` to OCaml, and `extraction_test.ml`, which runs the result; see [Extraction](extraction.md) |

---

## Groups inside a layer

In `Core`, `Relation` and `Data`, whose `dune` files carry `(include_subdirs qualified)`, a subdirectory groups related modules and **becomes a segment of the module path**: `theories/Core/Logic/Conjunction.v` is `JW.Core.Logic.Conjunction`. Each group has its own umbrella, such as `From JW Require Import Core.Logic.All`.

| Group | Holds |
|:---|:---|
| `Core/Logic/` | The connectives, `Verum`, `Falsum`, `forsome` and the syllogisms |
| `Relation/Order/` | The order classes |
| `Data/Base/` | The types built from no other type: `Empty`, `Unit`, `Bool`, `Comparison`, `Kleene3` |
| `Data/Calendar/` | `Month`, the twelve months, and `Weekday`, the seven days of the week, kept with the calendars rather than in `Data/Base/` |
| `Data/Calendar/Gregorian/` | `Date`, a date of the proleptic Gregorian calendar |
| `Data/Collection/` | `List`, `NonEmptyList` and `BinaryTree`, `BST`, the search tree over `BinaryTree`, `AVL`, the balanced search tree, and `SortedSet`, a set held in an AVL tree |
| `Data/Machine/` | The fixed-width units a machine stores: `Bit`, `Byte`, `HWord`, `Word`, `DWord`, `QWord`, the integers `UInt8` to `UInt64` and `Int8` to `Int64`, `Modular`, `Signed` and `Unsigned`, the laws those integers share, and `Endian`, the byte order of a word |
| `Data/Number/` | `Nat`, `Nat0`, `Integer`, `Rational`, and `Numeral`, the digit types a literal is read into |
| `Data/Number/Binary/` | `Bin`, `Bin0`, `SignedBin`, also forwarded by `Data.Number.All` |
| `Data/Text/` | The text types: `SourceByte`, the byte a string literal arrives in, `Ascii` and `AsciiStr`, `Utf8` and `Utf8Str` |
