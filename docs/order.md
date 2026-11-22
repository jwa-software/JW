<!--
SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
SPDX-License-Identifier: MIT
-->

# Order

An order is a relation that says which of two values comes first. `Relation/Order/` names four kinds of order as classes, each built from the properties of [Relations](relations.md), and `Data/Comparable.v` holds the class through which the data types get their orders:

| Class | Holds | An example |
|:---|:---|:---|
| `PartialOrder R` | `Reflexive R`, `Antisymmetric R` and `Transitive R` | "divides" on `Nat0` |
| `TotalOrder R` | `PartialOrder R` and `Total R` | `<=` on `Nat0` |
| `StrictPartialOrder R` | `Irreflexive R` and `Transitive R` | `<` on `Nat0` |
| `StrictTotalOrder R` | `StrictPartialOrder R` and `Trichotomous R` | `<` on `Nat0` |
| `Comparable compare lt` | a function `compare` that decides the strict order `lt` | the order of every number, character and string type |

- **An order comes in two forms.** `<=` admits equal values and `<` does not. The first two classes describe the one form, the next two the other.
- **None of the four adds a law.** Each is a name for properties held together, so each gives the fields of those properties: `Transitive.transitivity`, `Total.totality`.
- **`Comparable` is where the orders of the library come from.** One instance of it gives a type its `<`, its `<=`, and all four order classes.

`From JW Require Import Relation.Order.All` brings the four classes, and `Data.Comparable` the fifth. The examples on this page are in `Nat0`, under the key `%n0`.

---

## PartialOrder

- **The problem.** Some values are comparable and some are not. `2` divides `6`, and neither of `2` and `3` divides the other. A proof about such a relation still chains facts and still closes `x = y` from two bounds; it needs a name for exactly that much.
- **The class.** `PartialOrder R` holds `Reflexive R`, `Antisymmetric R` and `Transitive R`.
- **Instances.** `Nat0_divides_partial_order` for `Nat0.Divides`, and `Kleene3_information_partial_order` for the information order of [`Kleene3`](base.md), where `true` and `false` are not comparable. Every `TotalOrder` holds one as well.
- **In a proof.** `Reflexive.reflexivity n` proves `Nat0.Divides n n`, and `Antisymmetric.antisymmetry m n` takes the two divisibilities and proves `m = n`.
- **What it does not say.** That two values compare. `Nat0.Divides` has no `Total` instance, so a proof by the two cases `x` divides `y` or `y` divides `x` is not available.

---

## TotalOrder

- **The problem.** On numbers, any two values compare: `x <= y`, or `y <= x`. Sorting a list and taking the greater of two values both rest on that, beside the three laws of a partial order.
- **The class.** `TotalOrder R` holds `PartialOrder R` and `Total R`.
- **Instances.** One for the `<=` of every type with a `Comparable` instance, `Nat0` and `AsciiStr` among them.
- **In a proof.** The four properties are each found from the one instance: `Reflexive.reflexivity`, `Antisymmetric.antisymmetry`, `Transitive.transitivity` and `Total.totality`.
- **What it does not say.** Which of the two cases holds. That is a computation, and it is `Comparable`'s.

---

## StrictPartialOrder

- **The problem.** "Before" leaves equal values out: nothing is before itself, and "before" still chains. An order stated in this form needs its own two laws, since `<` is not reflexive.
- **The class.** `StrictPartialOrder R` holds `Irreflexive R` and `Transitive R`.
- **Instances.** One for the `<` of every type with a `Comparable` instance.
- **In a proof.** `Irreflexive.irreflexivity` and `Transitive.transitivity`. Together they give more than each alone: where `x < y` holds, `y < x` does not, as the last section of this page proves once for every strict partial order.
- **What it does not say.** That two different values compare; that is `StrictTotalOrder`.

---

## StrictTotalOrder

- **The problem.** Two numbers stand in one of three ways: `x < y`, `x = y`, or `y < x`. A proof by those three cases needs them to cover every pair.
- **The class.** `StrictTotalOrder R` holds `StrictPartialOrder R` and `Trichotomous R`.
- **Instances.** One for the `<` of every type with a `Comparable` instance.
- **In a proof.** `Trichotomous.trichotomy m n` gives the three cases, beside the two fields of the strict partial order.
- **What it does not say.** Which of the three cases holds; that again is `Comparable`'s.

---

## Comparable

- **The problem.** The four classes above are propositions: they state that two values compare, and compute nothing. A program has to decide: `Nat0.compare 3 5` answers `Comparison.Lt`. The answer and the proposition must agree, or a proof about `<` says nothing about what the program does.
- **The class.** `Comparable compare lt` joins a function `compare : A -> A -> Comparison`, which answers `Comparison.Lt`, `Comparison.Eq` or `Comparison.Gt`, to a relation `lt`. It has three fields: `Comparable.transitivity` of `lt`; `Comparable.specification`, `(compare m n = Comparison.Lt <-> lt m n) /\ (compare m n = Comparison.Eq <-> m = n)`; and `Comparable.antisymmetry`, `compare m n = Comparison.transpose (compare n m)`, the answer turned round when the arguments are.
- **What follows from the three fields.** `Comparable.LessOrEqual lt m n` is `m = n \/ lt m n`. `Comparable.eq`, `Comparable.le` and `Comparable.lt` answer a `Bool`, and `Comparable.min` and `Comparable.max` pick one of two values. A type names them as its own: `Nat0.eq 5 5`, `Nat0.le 3 5` and `Nat0.lt 3 5` are `true`, `Nat0.min 3 5` is `3`, and `Nat0.max 3 5` is `5`.
- **Each test reflects its relation, both ways.** The test's answer `true` is the relation, and `false` its opposite:

| Test | Answers `true` exactly when | Answers `false` exactly when |
|:---|:---|:---|
| `Comparable.eq compare m n` | `m = n` (`Comparable.comparison.equality.reflection`) | `~ (m = n)` (`Comparable.comparison.equality.refutation`) |
| `Comparable.le compare m n` | `Comparable.LessOrEqual lt m n` (`Comparable.order.reflection`) | `lt n m` (`Comparable.order.refutation`) |
| `Comparable.lt compare m n` | `lt m n` (`Comparable.order.strict.reflection`) | `Comparable.LessOrEqual lt n m` (`Comparable.order.strict.refutation`) |

- **The strict test is the complement of the other.** `Comparable.order.strict.complement` states `Comparable.lt compare m n = Bool.negate (Comparable.le compare n m)`. In the laws, a bare `lt` is the order relation the instance decides, so the test is written `Comparable.lt`.
- **Instances.** One per ordered type: `Nat_comparable`, `Nat0.comparable`, `Integer_comparable`, `Rational_comparable` and those of the binary numbers; `UInt8.comparable` to `Int64.comparable`; `Ascii.comparable`, `AsciiStr.comparable`, `Utf8.comparable` and `Utf8Str.comparable`. From any of them the instances `strict_partial_order`, `strict_total_order` and `total_order` give the four order classes, so every property of [Relations](relations.md) is found for that type's `<` and `<=`.
- **In a proof.** A computed answer becomes a proposition through the laws: `Comparable.comparison.strict.specification 3 5` states `Nat0.compare 3 5 = Comparison.Lt <-> 3 < 5`, and the left side holds by computation. `Comparable.order.reflection` does the same for `le` and `<=`, and `Comparable.comparison.equality.reflection` for `eq` and `=`. The laws of `min` and `max` are under `Comparable.minimum` and `Comparable.maximum`: `Comparable.maximum.universality` proves `max m n <= k` from `m <= k` and `n <= k`.
- **Mixing `<` and `<=`.** `Comparable.order.mixed.left.transitivity` gives `l < n` from `l <= m` and `m < n`, and `Comparable.order.mixed.right.transitivity` from `l < m` and `m <= n`; `Comparable.order.strict.weakening` turns `m < n` into `m <= n`, and `Comparable.order.strict.negation` is `~ (m < n) <-> n <= m`. They hold for every instance; the two mixed laws infer their points from the premises.
- **What it does not say.** Anything of an order that is not total. `Nat0.Divides` has no `Comparable` instance: no `compare` could answer for `2` and `3`. And a container gets no instance by itself: `List.compare cmp` compares two lists, and its laws, such as `List.comparison.specification`, take `Comparable cmp lt` as a premise.

---

## Using an order in a proof

A law stated over an order class is proved once and holds of every order of that kind:

```
From JW Require Import Relation.All.
From JW Require Import Data.All.

Theorem asymmetry
  : forall {A : Type} {R : A -> A -> Prop} {S : StrictPartialOrder R} (x : A) (y : A) .
      R x y -> ~ R y x.
Proof.
  intros A R S x y forward.
  simpl (~ _) in |- *.
  intro backward.
  ex (Irreflexive.irreflexivity &x (Transitive.transitivity &x &y &x &forward &backward))
    quodlibet.
Qed.

Definition asymmetry_of_numbers
  : forall (m : Nat0) (n : Nat0) . (m < n -> ~ (n < m))%n0
  := fun (m : Nat0) (n : Nat0) . asymmetry m n.

Definition asymmetry_of_strings
  : forall (s : AsciiStr) (t : AsciiStr) . (s < t -> ~ (t < s))%a
  := fun (s : AsciiStr) (t : AsciiStr) . asymmetry s t.
```

`asymmetry` names no type: from `x < y` and `y < x`, transitivity gives `x < x`, which irreflexivity refuses. `asymmetry_of_numbers` and `asymmetry_of_strings` are that proof at `Nat0` and at `AsciiStr`, the strict partial order of each found through its `Comparable` instance. The library states the same fact for a `Comparable` type as `Comparable.order.strict.asymmetry`.
