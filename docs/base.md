<!--
SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
SPDX-License-Identifier: MIT
-->

# Base types

A base type is built from no other type: every constructor takes no argument, so its values can be listed. `Data/Base/` holds five:

| Type | Values | What it is for |
|:---|:---|:---|
| `Empty` | none | A type that cannot have an element, the unit of `Coproduct` |
| `Unit` | `Unit.introduction` | A type with nothing to say, the unit of `Product` |
| `Bool` | `true`, `false` | A truth value that a function computes |
| `Comparison` | `Comparison.Lt`, `Comparison.Eq`, `Comparison.Gt` | The answer of a three-way comparison |
| `Kleene3` | `Kleene3.true`, `Kleene3.unknown`, `Kleene3.false` | A truth value that may not be known yet |

- **Each type lives in a module of its name.** The carrier is `Bool.T`, written `Bool` on both sides of the module, and the constructors stand behind the namespace: `Comparison.Lt`, `Kleene3.unknown`.
- **Only `Bool` hands its constructors back bare.** `true` and `false` are `Bool.true` and `Bool.false`. Every other constructor is written with its type's prefix, so a bare `true` is the `Bool` one beside `Kleene3.true`.
- **The notations are in a scope of their own.** `Bool` has `jwa_bool_scope` under the key `%bool`, and `Kleene3` has `jwa_kleene3_scope` under `%k3`. Neither is opened: write `(b1 && b2)%bool`, or open the scope.

`From jwa Require Import Data.Base.All` brings the five types and their notations. The laws are written with the type's prefix: `Bool.conjunction.commutativity`.

---

## Empty

- **The problem.** A function sometimes has a case that cannot happen, and its type has to say so. A proposition has `Falsum` for this, and a type needs the same thing.
- **The type.** `Empty` has no constructor, so no value of it can be written. It is to types what `Falsum` is to propositions.
- **From nothing, anything.** `Empty.elimination A e` is a value of any type `A`, from an `e : Empty`. The `match` on `e` has no branch to write.
- **Induction.** `Empty.induction P e` proves `P e` for every `e`, with no case to prove.

---

## Unit

- **The problem.** Some results carry no information, such as an operation that only succeeds or a `Product` with nothing on one side. The type of such a result needs exactly one value.
- **The type.** `Unit` has the one value `Unit.introduction`. It is to types what `Verum` is to propositions.
- **Every value is the one value.** `Unit.surjectivity` states `forall (u : Unit) . u = Unit.introduction`. Rocq does not compute this for an inductive type, so it is a law.

---

## Bool

- **The problem.** A proposition cannot be computed: `n = 3` is a statement, not an answer. A test that a program runs needs a value that it can return and that a `match` can take apart.
- **The type.** `Bool` has `true` and `false`. `Assert` (in `Data.Assert`) reads a `Bool` as a proposition, for the laws that tie a test to its statement.
- **The operations.** `Bool.negate`, `Bool.and`, `Bool.or` and `Bool.xor`, written `!`, `&&`, `||` and `^^` under `%bool`. `!` binds tightest, then `&&`, `^^` and `||`: `(! true || false && true)%bool` is `false`.
- **The laws.** `Bool.negation.involution` and De Morgan both ways, under `Bool.negation.de_morgan`. For each of `conjunction`, `disjunction` and `sejunction`: `associativity`, `commutativity` and `identity`. `Bool.conjunction.distributivity.over.sejunction`, and `Bool.sejunction.irreflexivity`: `(b ^^ b)%bool = false`.
- **Instances.** `Bool_and_monoid`, `Bool_or_monoid` and `Bool_xor_monoid`, each operation `Commutative`, and `Bool_ring`, with `^^` as its sum and `&&` as its product. See [Algebra](algebra.md).

---

## Comparison

- **The problem.** Two `Bool` tests, `<` and `=`, take two runs to order two values, and a search tree or a sort needs all three answers at once.
- **The type.** `Comparison` has `Comparison.Lt`, `Comparison.Eq` and `Comparison.Gt`, read as "the first argument is less than, equal to, or greater than the second". Every `compare` of the library returns one, as [Order](order.md) explains.
- **`transpose` swaps the arguments.** `Comparison.transpose Comparison.Lt` is `Comparison.Gt`, and `Comparison.Eq` stays. `Comparison.transposition.involution` states that two swaps give the first answer back.
- **Induction.** `Comparison.induction P lt eq gt` proves `P c` for every `c` from the three cases.

---

## Kleene3

- **The problem.** A `Bool` must be `true` or `false`. A value that is not known yet has no `Bool` to hold it: the answer of a computation that has not ended, or an SQL field that is `NULL`. A third value is needed, and the connectives must still give an answer when the known arguments decide it.
- **The type.** `Kleene3` has `Kleene3.true`, `Kleene3.unknown` and `Kleene3.false`, in the truth order from the greatest to the least. This is the strong three-valued logic of Kleene, also called K3.
- **The operations.** `Kleene3.negate`, `Kleene3.and` and `Kleene3.or`, written `!`, `&&` and `||` under `%k3`. `!` swaps `true` and `false` and keeps `unknown`. `&&` takes the lesser of its arguments, and `||` the greater:

| `&&` | `true` | `unknown` | `false` |
|:---|:---|:---|:---|
| **`true`** | `true` | `unknown` | `false` |
| **`unknown`** | `unknown` | `unknown` | `false` |
| **`false`** | `false` | `false` | `false` |

| `\|\|` | `true` | `unknown` | `false` |
|:---|:---|:---|:---|
| **`true`** | `true` | `true` | `true` |
| **`unknown`** | `true` | `unknown` | `unknown` |
| **`false`** | `true` | `unknown` | `false` |

- **A known argument can decide.** `(Kleene3.unknown && Kleene3.false)%k3` is `Kleene3.false`, and `(Kleene3.unknown || Kleene3.true)%k3` is `Kleene3.true`, whatever the unknown value turns out to be.
- **The laws.** `Kleene3.negation.involution` and De Morgan both ways, under `Kleene3.negation.de_morgan`. For each of `conjunction` and `disjunction`: `associativity`, `commutativity`, `identity`, `idempotence`, `absorption`, and the distributivity over the other, as `Kleene3.conjunction.distributivity.over.disjunction`.
- **What it does not have.** The excluded middle and the law of contradiction: `(Kleene3.unknown || ! Kleene3.unknown)%k3` and `(Kleene3.unknown && ! Kleene3.unknown)%k3` are both `Kleene3.unknown`. A law that holds for `Bool` holds for `Kleene3` only when it has no such case.
- **Implication.** `Kleene3.implies v1 v2` is `(! v1 || v2)%k3`, so `Kleene3.implies Kleene3.unknown Kleene3.unknown` is `Kleene3.unknown`, not `Kleene3.true`. `Kleene3.implication.contraposition` states `implies v1 v2 = implies (! v2) (! v1)`.
- **From `Bool`.** `Kleene3.from_bool` sends `true` to `Kleene3.true` and `false` to `Kleene3.false`. The laws under `Kleene3.conversion` state that it is injective (`injectivity`), that it never gives `Kleene3.unknown` (`exclusion`), and that it commutes with `negation`, `conjunction`, `disjunction` and `implication`: `Kleene3.from_bool (Bool.and b1 b2) = (Kleene3.from_bool b1 && Kleene3.from_bool b2)%k3`.
- **Instances.** `Kleene3_and_monoid`, with `Kleene3.true` as its identity, and `Kleene3_or_monoid`, with `Kleene3.false`. Both operations are `Commutative`. See [Algebra](algebra.md).
