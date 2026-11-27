<!--
SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
SPDX-License-Identifier: MIT
-->

# JSON

`Data/Json.v` holds `Json`, a value of JSON as [RFC 8259](https://www.rfc-editor.org/rfc/rfc8259) describes it, and the generator that writes it as JSON text.

---

## The value

| Constructor | Holds | JSON text |
|:---|:---|:---|
| `Json.Null` | nothing | `null` |
| `Json.Boolean b` | a `Bool` | `true`, `false` |
| `Json.Number m x` | a mantissa and an exponent of ten, both `SignedBin` | `15e-1`, `42` |
| `Json.String s` | a `Utf8Str` | `"text"` |
| `Json.Array l` | a `List Json` | `[1,2]` |
| `Json.Object l` | a `List (Utf8Str * Json)`, the members | `{"a":null}` |

- **A number is an exact decimal.** `Json.Number m x` is `m` times ten to the power `x`, so every number the grammar can write is held without loss: `1.5` is `Json.Number 15 (-1)`. One value has many terms: `Json.Number 150 (-2)` is the same number.
- **An object keeps what its text says.** Its members are a list, in their order, and a name may occur twice, as the RFC allows. A lookup by name is left to the client.
- **One accessor per constructor.** `Json.is_null`, `Json.boolean`, `Json.number`, `Json.string`, `Json.array` and `Json.object` answer `Some` of what the constructor holds, or `None`; `number` answers the pair of mantissa and exponent. Each has a `specification` and an `injectivity` law in a topic of its name.
- **Induction reaches inside the lists.** `Json.induction` gives the hypothesis for every element of an array and every value of an object, as `List.All`: `match j with | Null | Boolean b | Number m x | String s | Array l all | Object l all end per Json.induction`.

---

## Equality

`Json` is `Discernible`: `Json.equivalent j k` is `true` exactly when `j = k`, and `Json.discern` is its opposite (see [Order](order.md)). It compares terms, not numbers: `Json.discern` tells `15e-1` from `150e-2`, and an object from the same members in another order.

---

## The generator

RFC 8259 calls a program that writes JSON text a generator.

- **The text of a value.** `Json.to_utf8_str j` is the JSON text of `j`, with no whitespace: `{"a":[null,true,15e-1,"b"]}`.
- **A number** is its mantissa in decimal, a `-` before a negative one, then, when the exponent is not zero, `e` and the exponent: `42`, `-7e3`, `15e-1`.
- **A string** stands between quotation marks. The quotation mark and the reverse solidus are escaped as `\"` and `\\`; the control characters U+0000 to U+001F take the short forms `\b`, `\t`, `\n`, `\f` and `\r` where they have one, and `\u00xx` otherwise. Every other character is written as it is, so text past ASCII stays UTF-8.
- **An array and an object** list their elements and members in order, separated by `,`, a member as its quoted name, `:` and its value.

The text that the generator writes is what a parser of `Json` is to read back.
