<!--
SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
SPDX-License-Identifier: MIT
-->

# JW
Library for Rocq

A general-purpose Rocq library in layers, under the logical root `JW`. Import a layer with `From JW Require Import <Layer>.All`, or everything with `From JW Require Import All`.

---

## Requirements

An opam switch holding these packages, all from the default opam repository:

| Package | Version | What it provides |
|:---|:---|:---|
| `rocq-core` | 9.3 | The prover, and Ltac2, the language the tactics are written in |
| `dune` | 3.21 or later | The build |
| `ocaml` | whatever `rocq-core` asks for | The compiler both are built with |

The versions tested are `rocq-core` 9.3.0, `dune` 3.23.1 and `ocaml` 5.4.1. From a fresh opam installation:

```
opam switch create JW ocaml-base-compiler.5.4.1
eval $(opam env --switch=JW)
make deps
make
```

`make deps` installs what `opam/JW.opam` declares into the active switch. Every other `make` target runs its command inside the switch through `opam exec`, so the shell need not have run `opam env` for those.

---

## Building

| Command | What it does | When to use it |
|:---|:---|:---|
| `make` | Compiles every layer to `.vo` under `_build/default/theories/`, the test suite, and the library extracted to OCaml under `_build/default/extraction/`. Silent on success. | After any change to a `.v` or `dune` file. |
| `make test` | Runs the tests that execute: the extracted OCaml on known values. CI runs it after the build. | After `make`, before committing. |
| `opam exec -- dune build theories/Data` | Compiles one layer and the layers it depends on. | Iterating on a single layer. |
| `make opam` | Regenerates `opam/JW.opam` from `dune-project`, rewriting it in place. | After changing a field of `dune-project` that ends up in the opam file: version, depends, synopsis, description, authors, maintainers, license, source, tags. |
| `make fmt-check` | Prints the formatting diff of the `dune` and OCaml files without touching them; CI runs it. The OCaml files need `ocamlformat` 0.30.0, the version `.ocamlformat` pins, which `make deps` does not install. | Before committing, to see what `make fmt` would change. |
| `make fmt` | Reformats the `dune` and OCaml files in place. `.v` files are never touched. | When `make fmt-check` reports a diff you agree with. |
| `opam exec -- dune build @install` | Builds exactly what an opam installation of the package would build. | Before a release, as a self-check. |
| `make clean` | Deletes `_build/`. | When a build result looks stale or inconsistent. |
| `make deps` | Installs the dependencies declared in `opam/JW.opam` into the active switch. | Once, on a new switch. |

---

## No prelude

Every theory is built with `-noinit`, so **Rocq's prelude is never loaded**: a file sees only what it requires by name. The library defines its own notations, connectives, equality and data types, and requires nothing from `Corelib`. Two compiled plugins are used as they are:

- **Ltac2**, the tactic engine, loaded by `theories/Dialect/Ltac.v`;
- **the literal reader** behind `Number Notation` and `String Notation`, loaded by `theories/Data/Literal.v`.

---

## Documentation

- [Usage](docs/usage.md): installing the library and using it in a project of your own.
- [The tactic language](docs/tactic.md): Ltac2 with Rocq's own tactics hidden, and the tactics that take their place.
- [Algebra](docs/algebra.md): the nine classes from `Semigroup` to `Ring`, what each one says, the instances the library declares and how a proof uses them.
- [Relations](docs/relations.md): the properties of a relation from `Reflexive` to `Trichotomous`, `Equivalence`, and `WellFounded` with the recursion that goes down a relation.
- [Order](docs/order.md): the four order classes, and `Comparable`, through which a data type gets its `<`, `<=`, `min` and `max`.
- [Base types](docs/base.md): `Empty`, `Unit`, `Bool`, `Comparison`, and `Kleene3`, the strong three-valued logic of Kleene, with their operations and laws.
- [Numbers](docs/numbers.md): the number types, their conversions, arithmetic and literals.
- [Machine units](docs/machine.md): `Bit`, `Byte`, the words `HWord` to `QWord` with their byte order, and the fixed-width integers `UInt8` to `UInt64` and `Int8` to `Int64`, with their division and the conversions between widths.
- [Text](docs/text.md): the characters `Ascii` and `Utf8`, the strings `AsciiStr` and `Utf8Str`, their order and case, the code points of `Utf8`, indexing and substrings of the strings, and how a string literal is read.
- [Calendar](docs/calendar.md): the months, the weekdays, the proleptic Gregorian `Date` that can only hold a real date, the leap rule, the day number counted from 0001-01-01 and back, the weekday of a date, the order of dates, day, month and year arithmetic, the Unix day, and the ISO 8601 week date.
- [Collections](docs/collections.md): the containers `List`, `NonEmptyList` and `BinaryTree`, their operations and laws, the conversions to `List`, the search tree `BST`, the balanced search tree `AVL`, the set `SortedSet`, and the interfaces `Functor`, `Sized` and `Membership`.
- [Extraction](docs/extraction.md): the library extracted to OCaml, what the extracted code looks like, and the test that runs it.
- [Layout](docs/layout.md): the layers, their directories and what each depends on.

---

## Tests

`test/` is the theory `jw_test`, **not part of the library**: `make` builds it, an opam installation leaves it out.

- **One file per umbrella** (`DataAll.v`, `DataMachineAll.v`, ...), each importing that umbrella alone. An umbrella defines nothing, so only an import in isolation shows whether it forwards everything it should.
- **The laws of `=` are named in full**, as `Identity.reflexivity` and `Identity.transitivity`, not as `refl` and `trans`. Those come from `Tactics.Equation`, which a data umbrella does not forward, and a notation would find the law even where the umbrella fails to.
- **`TacticsAll.v`** checks every form of every tactic, and every refusal with `Fail`.
