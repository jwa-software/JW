<!--
SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
SPDX-License-Identifier: MIT
-->

# Collections

`JW.Data` holds the containers, and the interfaces they share, under `Data/Collection/`:

| Type | What it is | Written as |
|:---|:---|:---|
| `List A` | Any number of elements of type `A`, in order | `(1 :: 2 :: 3 :: [])%list`, `[]%list` (empty) |
| `NonEmptyList A` | One element or more, in order | `(1 :: 2 :: [3])%non_empty_list`, `[1]%non_empty_list` |
| `BinaryTree A` | A leaf, which holds nothing, or a node: one element between two subtrees | `BinaryTree.Node BinaryTree.Leaf 1 BinaryTree.Leaf` |
| `AVL A` | A binary tree that stores at each node the height of the subtree there | `AVL.Node AVL.Leaf 1 AVL.Leaf 1` |
| `SortedSet cmp` | A set of elements in the order `cmp` decides, held in an AVL tree with the proof of its rules | `SortedSet.insert 1 (SortedSet.empty Nat0.compare)` |

`BST` is a module beside them and not a type of its own: it holds the rule that makes a `BinaryTree` a search tree, and the operations that follow that rule.

`From JW Require Import Data.Collection.All` brings the five types, `BST`, the interfaces, and what their operations and laws name: the types `Nat0`, `Nat`, `Bool`, `Option`, `Product` and `Comparison`, the class `Comparable`, and `Assert`, which reads a `Bool` as a proposition. The examples on this page take their numbers in `Nat0` and are written with `jw_list_scope` and `jw_nat0_scope` open.

---

## List

`List` has the ctors `List.Nil` and `List.Cons`, written `[]` and `a :: l`. Its notations live in `jw_list_scope`, under the key `%list`.

- **Building:** `l1 ++ l2` is `List.concat`, and `List.append l a` puts `a` after the last element: `(1 :: 2 :: []) ++ (3 :: [])` and `List.append (1 :: 2 :: []) 3` are both `1 :: 2 :: 3 :: []`. `List.replicate 3 7` is `7 :: 7 :: 7 :: []`.
- **Length and order:** `List.length l`, written `(|| l ||)`, is a `Nat0`, and `List.reverse (1 :: 2 :: 3 :: [])` is `3 :: 2 :: 1 :: []`.
- **Every element at once:** `List.map Nat0.inc (1 :: 2 :: [])` is `2 :: 3 :: []`, `List.filter (Nat0.le 2) (1 :: 2 :: 3 :: [])` keeps `2 :: 3 :: []`, `List.count` counts what `List.filter` keeps, and `List.fold_right Nat0.add 0 (1 :: 2 :: 3 :: [])` is `6`. `List.partition` gives what a test accepts and what it rejects, `List.zip` pairs two lists as far as the shorter one goes, and `List.unzip` splits a list of pairs.
- **The ends return an `Option`**, `None` on the empty list: `List.head`, `List.last`, `List.tail`, `List.initial` (all but the last element) and `List.pop` (the head with the tail). `List.head (5 :: 6 :: 7 :: [])` is `Some 5`, and `List.initial` of the same list is `Some (5 :: 6 :: [])`.
- **Indexing counts from 0.** `List.nth l i` is `Some` of the element at position `i` exactly when `i < (|| l ||)` (`List.indexing.specification`), and `None` from there on: `List.nth (5 :: 6 :: 7 :: []) 1` is `Some 6`.
- **A list splits at a position.** `List.take n l` is the first `n` elements and `List.drop n l` the rest, all of `l` and nothing where `l` is shorter: `List.take 2 (5 :: 6 :: 7 :: [])` is `5 :: 6 :: []`, and `take n l ++ drop n l = l` (`List.splitting.decomposition`).
- **Membership and the quantifiers are propositions.** `List.Contains a l` is written `l contains_member a` or `a belongs_to l`, and its negation `l does_not_contain_member a` or `a does_not_belong_to l`. `List.All P l` and `List.Any P l` state that every element, or some element, satisfies `P`; `List.quantification.all.specification` and `List.quantification.any.specification` state both through membership.
- **Numbers:** `List.sum` and `List.product` fold a `List Nat0`. `List.range 2 5` is `2 :: 3 :: 4 :: []` and `List.range_inclusive 2 5` reaches `5` as well; a range whose `stop` is not past its `start` is empty. `List.range.membership.specification` states `range start stop contains_member i <-> start <= i /\ i < stop`.
- **An order is an argument.** `List.insert`, `List.insertion_sort`, `List.maximum_of` and `List.minimum_of` take a test `le : A -> A -> Bool` that answers whether its first argument may come first, and `List.Sorted le l` states that every element may precede all that follow it. `List.insertion_sort Nat0.le (3 :: 1 :: 2 :: [])` is `1 :: 2 :: 3 :: []`, and `List.maximum_of Nat0.le` of the same list is `Some 3`.
- **The laws of an order take its properties as premises.** For a `le` that is total and transitive, `List.sorting.sortedness` states `Sorted le (insertion_sort le l)`, and `List.maximum.bound` that every element may precede the maximum. `List.sorting.preservation.membership` and `List.sorting.preservation.length` hold of any `le`.
- **Lists are ordered lexicographically.** `List.compare cmp l m` goes by `cmp` on the elements, a proper prefix first: with `Nat0.compare`, `1 :: 2 :: []` comes before `1 :: 3 :: []`, and `1 :: []` before `1 :: 2 :: []`. `List.comparison.specification`, `List.comparison.antisymmetry` and `List.comparison.transitivity` hold for any `cmp` that is `Comparable`.
- **The laws are grouped by operation.** `List.concatenation.associativity` and `List.concatenation.identity` make `++` and `[]` a monoid, the instance `List_concat_monoid`; `List.length.additivity.over.concatenation` states `(|| l1 ++ l2 ||) = (|| l1 ||) + (|| l2 ||)`; `List.reversal.involution` states `reverse (reverse l) = l`; and `mapping`, `filtering`, `membership`, `quantification` and `reversal` each state how their operation meets `++`. A `catamorphism` law states its operation as a `List.fold_right`, as `List.mapping.catamorphism` does for `List.map`.
- **Induction:** `List.induction` is the eliminator, and a proof names its hypothesis in the branch: `match l with | Nil | Cons a (l' by IH) end per List.induction`.

---

## NonEmptyList

`NonEmptyList` has the ctors `NonEmptyList.One` and `NonEmptyList.Cons`, written `[a]` and `a :: x`: a value ends with an element where a list ends with `[]`, so none is empty. Its notations live in `jw_non_empty_list_scope`, under the key `%non_empty_list`.

- **The ends are total.** `NonEmptyList.head` and `NonEmptyList.last` return the element itself, with no `Option`: on `5 :: 6 :: [7]` they are `5` and `7`.
- **The length is a `Nat`**, the number type with no zero: `NonEmptyList.length (5 :: 6 :: [7])` is `3%n`.
- **Operations:** `x ++ y` is `NonEmptyList.concat`, beside `NonEmptyList.reverse`, `NonEmptyList.map` and the membership `NonEmptyList.Contains`, with the notations `List` has. `(1 :: [2]) ++ [3]` is `1 :: 2 :: [3]`.
- **The extrema are total too.** `NonEmptyList.maximum_of` and `NonEmptyList.minimum_of` take a test `le` as `List`'s do and return the element outright: `NonEmptyList.maximum_of Nat0.le (3 :: 1 :: [2])` is `3`.
- **Laws:** `NonEmptyList.concatenation.associativity`, `NonEmptyList.length.additivity.over.concatenation`, `NonEmptyList.membership.distributivity.over.concatenation`, `NonEmptyList.reversal.involution`, `NonEmptyList.mapping.identity` and `NonEmptyList.mapping.composition`; and, for a `le` that is total and transitive, `NonEmptyList.maximum.bound` and `NonEmptyList.minimum.bound`.
- **`NonEmptyList.to_list` gives the same elements as a `List`**, and the `conversion` laws carry each operation to `List`'s: `NonEmptyList.conversion.distributivity.over.concatenation`, `NonEmptyList.conversion.length`, `NonEmptyList.conversion.membership`, and `NonEmptyList.conversion.maximum`, which states `List.maximum_of le (to_list x) = Some (maximum_of le x)`, with `NonEmptyList.conversion.minimum` beside it.
- **Induction:** `match x with | One a | Cons a (x' by IH) end per NonEmptyList.induction`.

---

## BinaryTree

`BinaryTree` has the ctors `BinaryTree.Leaf`, the tree that holds nothing, and `BinaryTree.Node l a r`, the element `a` between the subtrees `l` and `r`. It has no notation. Below, `t` is the tree with `2` at the root, `1` on its left and `3` on its right, `Node (Node Leaf 1 Leaf) 2 (Node Leaf 3 Leaf)` with each ctor under its prefix.

- **`size` counts the elements and `height` the levels.** `BinaryTree.size t` is `3` and `BinaryTree.height t` is `2`; a leaf has `0` for both. `BinaryTree.height.bound` states `height t <= size t`.
- **`to_list` reads the tree in order:** the left subtree, the node's element, the right subtree. `BinaryTree.to_list t` is `1 :: 2 :: 3 :: []`.
- **`map` keeps the shape.** `BinaryTree.map Nat0.inc t` holds `2`, `3` and `4` where `t` holds `1`, `2` and `3`. `BinaryTree.mapping.identity` and `BinaryTree.mapping.composition` are its two laws, and `BinaryTree.mapping.preservation` states that the size and the height stay, and that a member `a` of `t` gives the member `f a` of `map f t`.
- **`mirror` exchanges the two subtrees of every node.** `BinaryTree.mirror t` lists as `3 :: 2 :: 1 :: []`. `BinaryTree.mirroring.involution` states `mirror (mirror t) = t`, and `BinaryTree.mirroring.preservation` that the size, the height and the members stay.
- **Membership and the quantifiers are propositions:** `BinaryTree.Contains a t`, `BinaryTree.All P t` and `BinaryTree.Any P t`, each read in the order of `to_list`. `BinaryTree.quantification.all.specification` and `BinaryTree.quantification.any.specification` state both quantifiers through membership, and `BinaryTree.quantification.all.monotonicity` carries `All` from a property to a weaker one.
- **`all` is the `Bool` test of `All`.** `BinaryTree.all (Nat0.le 1) t` is `true`, and `BinaryTree.all (Nat0.le 2) t` is `false`, since `1` fails it. `BinaryTree.quantification.all.reflection` states `Assert (all p t) <-> All (fun a . Assert (p a)) t`.
- **The `conversion` laws carry each operation to `List`'s.** `BinaryTree.conversion.size` states `(|| to_list t ||) = size t`; `BinaryTree.conversion.mapping` and `BinaryTree.conversion.mirroring` state that `to_list` turns `map` into `List.map` and `mirror` into `List.reverse`; `BinaryTree.conversion.membership`, `BinaryTree.conversion.all` and `BinaryTree.conversion.any` state `Contains`, `All` and `Any` through `List`'s. Along them a statement about a tree moves to the list of its elements, and a `List` law comes back.
- **Two trees may hold the same elements and differ.** `Node Leaf 1 (Node Leaf 2 Leaf)` and `Node (Node Leaf 1 Leaf) 2 Leaf` both list as `1 :: 2 :: []` and are two values, so a statement about what a tree holds goes through `to_list` or `Contains`, not through `=`.
- **Induction has one hypothesis per subtree:** `match t with | Leaf | Node (l by IHl) a (r by IHr) end per BinaryTree.induction`.

---

## BST

A search tree is a `BinaryTree` whose elements stand in order: at every node, the left subtree holds what is below the node's element, and the right subtree what is above it. `BST` adds no type. It holds that rule as the proposition `BST.Ordered`, and the operations `BST.contains`, `BST.insert` and `BST.remove`, which follow it. Below, `t` is the tree with `5` at the root, `2` on its left and `8` on its right, and the comparison is `Nat0.compare`.

- **The rule is a proposition.** `BST.Ordered lt t` states, for every node, that each element of its left subtree is below its element and each element of its right subtree above it. `BinaryTree.Leaf` is ordered, and so is `t`, which lists as `2 :: 5 :: 8 :: []`.
- **A search follows one path.** `BST.contains cmp a t` compares `a` with the element of a node and goes to one subtree, never to both: `BST.contains Nat0.compare 8 t` is `true`, and `BST.contains Nat0.compare 3 t` is `false`. `BST.search.specification` states that on an ordered tree the answer is the tree's membership, `contains cmp a t = true <-> BinaryTree.Contains a t`.
- **`insert` puts an element at its place.** `BST.insert Nat0.compare 3 t` puts `3` on the right of `2`, and the tree then lists as `2 :: 3 :: 5 :: 8 :: []`. An element the tree already holds is not added again: `BST.insert Nat0.compare 5 t` is `t`. `BST.insertion.membership` states `Contains b (insert cmp a t) <-> b = a \/ Contains b t`, and `BST.insertion.preservation` that an ordered tree stays ordered.
- **A tree built by `insert` is ordered.** It starts from `BinaryTree.Leaf` and every step keeps the rule: `5`, `8` and `3` inserted into a leaf, in that order, list as `3 :: 5 :: 8 :: []`.
- **`remove` takes an element out.** `BST.remove Nat0.compare 5 t` puts `8`, the smallest element of the right subtree, at the root, and the tree then lists as `2 :: 8 :: []`; removing an element the tree does not hold changes nothing. `BST.removal.membership` states, for an ordered tree, `Contains b (remove cmp a t) <-> Contains b t /\ ~ (b = a)`, and `BST.removal.preservation` that the tree stays ordered.
- **`remove` is built from two operations.** `BST.pop_minimum t` answers with the smallest element and the tree that is left, `Some` of the pair of `2` and the rest for `t`, and with `None` on a leaf; its laws are under `BST.extraction`. `BST.join l r` makes one tree of two where `l` lies wholly below `r`; its laws are under `BST.joining`.
- **The comparison is an argument.** `contains`, `insert` and `remove` take `cmp`, as `List.compare` does, and their laws take `Comparable cmp lt` as a premise: `BST.search.specification Nat0.comparable` is the law at `Nat0`. The laws that read only the transitivity of `lt`, `BST.extraction.minimality` and `BST.joining.preservation`, take that alone.
- **`is_ordered` is the `Bool` test of the rule.** `BST.is_ordered Nat0.compare t` is `true`, and `BST.is_ordered Nat0.compare (BinaryTree.mirror t)` is `false`. For a `cmp` that is `Comparable cmp lt`, `BST.order.reflection` states `Assert (is_ordered cmp t) <-> Ordered lt t`.
- **The type does not hold the rule.** A `BinaryTree` put together by hand need not be ordered, and on such a tree the laws say nothing: each one that needs the rule has `BST.Ordered lt t` as a premise. `BinaryTree.mirror` does not keep the rule either: `BST.contains Nat0.compare 8 (BinaryTree.mirror t)` is `false`.
- **The tree is not balanced.** `1`, `2` and `3` inserted in that order make a chain of height `3`, where `t`, with three elements too, has height `2`. A search in a chain may go through every element. `AVL`, below, keeps its trees balanced.

---

## AVL

An AVL tree is a search tree that keeps the heights of every node's two subtrees within one of each other, so that a path from the root stays short. `AVL` is a type of its own: each node stores the height of the subtree there, which a plain `BinaryTree` has no place for. Below, the comparison is `Nat0.compare`, and `t` is the tree that `1`, `2` and `3` make when inserted into `AVL.Leaf` in that order: `Node (Node Leaf 1 Leaf 1) 2 (Node Leaf 3 Leaf 1) 2`, each ctor under its prefix.

- **A node stores its height, last.** `AVL.Node l a r h` holds the left subtree `l`, the element `a`, the right subtree `r` and the height `h`. `AVL.height t` reads it in one step, `2` for `t`, and `AVL.node l a r` builds a node with the right height. `AVL.to_tree` drops the heights and gives the `BinaryTree`, so `BinaryTree.to_list (AVL.to_tree t)` is `1 :: 2 :: 3 :: []`.
- **Three rules are propositions.** `AVL.Measured t` states that every stored height is one above the higher of the heights its two subtrees store; `AVL.measurement.specification` turns it into `height t = BinaryTree.height (to_tree t)`. `AVL.Balanced t` states that at every node the heights of the two subtrees are equal or one apart. `AVL.Ordered lt t` is `BST.Ordered lt (to_tree t)`.
- **`insert` rebalances on the way back up.** Where a subtree has grown two above its sibling, `AVL.balance` turns the node with `AVL.rotate.right` or `AVL.rotate.left`, a single or a double rotation. `t` comes from one single rotation, and `3`, `1` and `2` inserted in that order give the same tree from one double rotation. `1` to `7` inserted in order make a tree of height `3`, where `BST.insert` makes a chain of height `7`.
- **A search follows one path.** `AVL.contains Nat0.compare 3 t` is `true`, and `AVL.contains Nat0.compare 4 t` is `false`. `AVL.search.specification` states that on an ordered tree the answer is the membership of `to_tree t`.
- **`pop` takes the first element in order.** `AVL.pop t` is `Some` of the pair of `1` and the tree of `2` and `3`, and `None` on a leaf; on an ordered tree the first element is the smallest, by `AVL.extraction.minimality`. `AVL.join l r` makes one tree of two where `l` lies wholly below `r`: the first element of `r` goes between them, and the node is rebalanced.
- **`remove` rebalances as well.** `AVL.remove Nat0.compare 2 t` puts `3` at the root, over `1`. `1` to `7` inserted in order, then `1`, `3` and `2` removed, leave `4 :: 5 :: 6 :: 7 :: []` at height `3`: the last removal turns the root with a left rotation.
- **Each operation keeps each rule.** Under `insertion`, `extraction`, `joining` and `removal`, a `preservation` law states for each rule that the result keeps it: `AVL.insertion.preservation.balance` states `Measured t -> Balanced t -> Balanced (insert cmp a t)`, beside `.measurement` and `.order`. The `membership` laws state what the result holds, as `BST`'s do, through `to_tree`.
- **The height changes by one level at most.** `AVL.insertion.growth` states that `insert` leaves the height as it was or one higher, and `AVL.removal.shrinkage` and `AVL.extraction.shrinkage` that `remove` and `pop` leave it as it was or one lower.
- **The size follows the path of `contains`.** `contains`, `insert` and `remove` take the same path down, so the size laws need no rule: `AVL.insertion.size.growth` states that `insert cmp a t` has one element more than `t` when `contains cmp a t = false`, and `AVL.insertion.size.invariance` as many when it is `true`; `AVL.removal.size.shrinkage` and `AVL.removal.size.invariance` state the same of `remove`. The sizes are counted on `to_tree`, with `BinaryTree.size`.
- **The comparison is an argument.** `contains`, `insert` and `remove` take `cmp`, and their laws take `Comparable cmp lt` as a premise. The laws that read only the transitivity of `lt`, those of the rotations, of `balance`, of `pop` and of `join`, take that alone.
- **`is_valid` tests the three rules at once.** `AVL.is_measured`, `AVL.is_balanced` and `AVL.is_ordered` test one rule each as a `Bool`, and `AVL.is_valid` joins them. The `reflection` laws under `measurement`, `equilibrium`, `order` and `validity` state each test as its rule: `AVL.validity.reflection` states `Assert (is_valid cmp t) <-> Measured t /\ Balanced t /\ Ordered lt t` for a `Comparable cmp lt`. `AVL.is_valid Nat0.compare t` is `true`, and `AVL.is_measured (AVL.Node AVL.Leaf 1 AVL.Leaf 7)` is `false`.
- **The type does not hold the rules.** A tree put together by hand may store a wrong height, or be unbalanced or unordered, and on such a tree the laws say nothing: each one that needs a rule has it as a premise. A tree built from `AVL.Leaf` by `insert` and `remove` keeps all three. `SortedSet`, below, carries their proof with the tree.
- **Induction has one hypothesis per subtree:** `match t with | Leaf | Node (l by IHl) a (r by IHr) h end per AVL.induction`.

---

## SortedSet

A sorted set holds an AVL tree together with the proof that the tree passes `AVL.is_valid cmp`, so every value is measured, balanced and ordered, and its laws need none of those premises. The type is `SortedSet cmp`, one type for each comparison: `SortedSet Nat0.compare` is a set of numbers. Below, `s` is `SortedSet.insert 2 (SortedSet.insert 3 (SortedSet.insert 1 (SortedSet.empty Nat0.compare)))`.

- **The proof is a `Bool` check under `Assert`.** `SortedSet.introduction t p` takes the tree `t` and a proof `p` of `Assert (AVL.is_valid cmp t)`, and `SortedSet.to_avl` gives the tree back. Any two proofs of `Assert b` are equal (`Assert.uniqueness`), so `SortedSet.conversion.injectivity` states that two sets with the same tree are the same set: `SortedSet.insert 1` applied twice to `SortedSet.empty Nat0.compare` is `SortedSet.insert 1` applied once.
- **`insert` and `remove` take the order as an instance.** Keeping the tree ordered needs `cmp` to decide a strict order, so both take `Comparable cmp lt`, which instance search finds: `SortedSet.insert 3 s` finds `Nat0.comparable`. `empty`, `contains`, `to_list` and `size` take none.
- **The laws state plain facts.** `SortedSet.insertion.membership` states `contains b (insert a s) = true <-> b = a \/ contains b s = true`, `SortedSet.removal.membership` states `contains b (remove a s) = true <-> contains b s = true /\ ~ (b = a)`, and `SortedSet.emptiness` states `contains a (empty cmp) = false`.
- **The elements read in order.** `SortedSet.to_list s` is `1 :: 2 :: 3 :: []`, `SortedSet.contains 3 s` is `true` and `SortedSet.contains 4 s` is `false`. Removing `2` leaves `1 :: 3 :: []`, of `SortedSet.size` `2`, and `SortedSet.conversion.size` states `(|| to_list s ||) = size s`.
- **The size counts each element once.** `SortedSet.insertion.size.growth` states that `insert a s` has one element more when `contains a s = false`, and `SortedSet.insertion.size.invariance` that it has as many when `contains a s = true`: `SortedSet.size (SortedSet.insert 2 s)` is `3`. `SortedSet.removal.size.shrinkage` and `SortedSet.removal.size.invariance` state the same of `remove`, one element fewer or as many.

---

## Interfaces

Each interface is a class over a container `F : Type -> Type`, and `List`, `NonEmptyList` and `BinaryTree` each have an instance of all three; `AVL` and `SortedSet` have none, and reach `BinaryTree`'s through `AVL.to_tree`, a set after `SortedSet.to_avl`. `Functor` has a section of its own after this one.

| Class | What it holds | `List` | `NonEmptyList` | `BinaryTree` |
|:---|:---|:---|:---|:---|
| `Functor` | `Functor.map`, with the laws `Functor.identity` and `Functor.composition` | `List.map` | `NonEmptyList.map` | `BinaryTree.map` |
| `Sized` | `Sized.cardinality`, a `Nat0` | `List.length` | `NonEmptyList.length`, as a `Nat0` | `BinaryTree.size` |
| `Membership` | `Membership.Contains`, a proposition | `List.Contains` | `NonEmptyList.Contains` | `BinaryTree.Contains` |

- **One name serves every container.** `Sized.cardinality (1 :: 2 :: 3 :: [])` and `Sized.cardinality t` are both `3`, and `Functor.map Nat0.inc` maps a list or a tree.
- **`Sized` derives emptiness.** `Sized.is_empty` and `Sized.is_not_empty` answer a `Bool`, and `Sized.emptiness.reflection` states `Assert (is_empty x) <-> cardinality x = Nat0.Zero`.
- **`Sized` and `Membership` state no law.** A count alone, or a relation alone, constrains nothing; a law that relates one of them to another operation is the container's own, as `List.length.additivity.over.concatenation` is.

---

## Functor

- **The problem.** One change is applied to every element of a container, whatever the container: add one to each number of a list, of a tree, of an `Option`. Each type has a `map` of its own. A function or a proof written once for all of them needs one name for it, and the laws that make "apply to every element" mean the same everywhere.
- **The class.** `Functor F`, for a container `F : Type -> Type`, has the operation `Functor.map : (A -> B) -> F A -> F B` and two laws. `Functor.identity` is `map (fun a . a) x = x`: a `map` that changes no element changes nothing. `Functor.composition` is `map g (map f x) = map (fun a . g (f a)) x`: two passes are one pass that makes both changes.
- **Instances.** `List_functor`, `NonEmptyList_functor` and `BinaryTree_functor`. `Option_functor`, under which `Functor.map Nat0.inc (Some 1)` is `Some 2` and `None` stays `None`. `Product_functor` and `Coproduct_functor`, which map the second component of a pair and the right side of a coproduct.
- **In a proof.** `Functor.map Nat0.inc` maps a list, a tree or an `Option`, the instance found from its argument. `Functor.composition A B C f g x` is the second law for whichever container `x` is in, so a statement proved from it holds of all six.
- **What it does not say.** How many elements there are, or in which order. That `map` keeps the length of a list, or the size of a tree, is each container's own law: `List.mapping.preservation.length`, `BinaryTree.mapping.preservation.size`.
