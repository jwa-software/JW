(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

From JW Require Import Core.All.
From JW Require Import Data.Assert.
From JW Require Import Data.Base.Bool.
From JW Require Import Data.Base.Comparison.
From JW Require Import Data.Collection.AVL.
From JW Require Import Data.Collection.BinaryTree.
From JW Require Import Data.Collection.List.
From JW Require Import Data.Comparable.
From JW Require Import Data.Number.Nat0.
From JW Require Import Tactics.Equation.
From JW Require Import Tactics.Modus.

(* A set of elements kept in the order [cmp] decides: an AVL tree together
 * with the proof that it passes [AVL.is_valid], so that every value of the
 * type is measured, balanced and ordered, and no law needs those premises.
 *)
Module SortedSet. (* SortedSet *)

(* The proof is a [Bool] check under [Assert], whose proofs are all equal,
 * so two sets with the same tree are the same set.
 *)
Inductive T {A : Type} (cmp : A -> A -> Comparison) : Type :=
  | introduction : forall (t : AVL A) . Assert (AVL.is_valid cmp t) -> T cmp.

(* [A] and [cmp] are read off the tree and the proof. *)
Arguments introduction {A} {cmp} t p.

Abbreviation SortedSet := T.

(* The tree inside. *)
(* [forall {A : Type} {cmp : A -> A -> Comparison} . SortedSet cmp -> AVL A] *)
Definition to_avl := fun {A : Type} {cmp : A -> A -> Comparison} (s : SortedSet cmp) .
  match s with
  | SortedSet.introduction t _ => t
  end.

(* The set with no element. The check computes to [true] on a leaf, so
 * [Verum]'s proof [I] is its proof.
 *)
(* [forall {A : Type} . (A -> A -> Comparison) -> SortedSet cmp] *)
Definition empty := fun {A : Type} (cmp : A -> A -> Comparison) .
  @SortedSet.introduction A cmp AVL.Leaf I.

(* [AVL.insert], with the proof rebuilt from the three [preservation] laws
 * of [AVL.insertion]. Keeping the order needs [cmp] to decide a strict
 * order, so [insert] takes that fact as an instance.
 *)
(* [forall {A : Type} {cmp : A -> A -> Comparison} {lt : A -> A -> Prop} .
 *   Comparable cmp lt -> A -> SortedSet cmp -> SortedSet cmp]
 *)
Definition insert
  := fun {A : Type} {cmp : A -> A -> Comparison} {lt : A -> A -> Prop}
       {C : Comparable cmp lt} (a : A) (s : SortedSet cmp) .
  match s with
  | SortedSet.introduction t p =>
      SortedSet.introduction
        (AVL.insert cmp a t)
        (Biconditional.backward.elimination
          (AVL.validity.reflection C (AVL.insert cmp a t))
          (match Biconditional.forward.elimination (AVL.validity.reflection C t) p with
           | Conjunction.introduction m (Conjunction.introduction b o) =>
               conjoin (AVL.insertion.preservation.measurement cmp a t m),
                 (conjoin (AVL.insertion.preservation.balance cmp a t m b),
                   (AVL.insertion.preservation.order C a t o))
           end))
  end.

(* [AVL.remove], with the proof rebuilt from the three [preservation] laws
 * of [AVL.removal]; it takes the fact that [cmp] decides a strict order as
 * [insert] does.
 *)
(* [forall {A : Type} {cmp : A -> A -> Comparison} {lt : A -> A -> Prop} .
 *   Comparable cmp lt -> A -> SortedSet cmp -> SortedSet cmp]
 *)
Definition remove
  := fun {A : Type} {cmp : A -> A -> Comparison} {lt : A -> A -> Prop}
       {C : Comparable cmp lt} (a : A) (s : SortedSet cmp) .
  match s with
  | SortedSet.introduction t p =>
      SortedSet.introduction
        (AVL.remove cmp a t)
        (Biconditional.backward.elimination
          (AVL.validity.reflection C (AVL.remove cmp a t))
          (match Biconditional.forward.elimination (AVL.validity.reflection C t) p with
           | Conjunction.introduction m (Conjunction.introduction b o) =>
               conjoin (AVL.removal.preservation.measurement cmp a t m),
                 (conjoin (AVL.removal.preservation.balance cmp a t m b),
                   (AVL.removal.preservation.order C a t o))
           end))
  end.

(* The search of [AVL.contains] on the tree inside; it needs no proof. *)
(* [forall {A : Type} {cmp : A -> A -> Comparison} . A -> SortedSet cmp -> Bool] *)
Definition contains := fun {A : Type} {cmp : A -> A -> Comparison} (a : A) (s : SortedSet cmp) .
  AVL.contains cmp a (to_avl s).

(* The elements in order. *)
(* [forall {A : Type} {cmp : A -> A -> Comparison} . SortedSet cmp -> List A] *)
Definition to_list := fun {A : Type} {cmp : A -> A -> Comparison} (s : SortedSet cmp) .
  BinaryTree.to_list (AVL.to_tree (to_avl s)).

(* The number of elements. *)
(* [forall {A : Type} {cmp : A -> A -> Comparison} . SortedSet cmp -> Nat0] *)
Definition size := fun {A : Type} {cmp : A -> A -> Comparison} (s : SortedSet cmp) .
  BinaryTree.size (AVL.to_tree (to_avl s)).

Module conversion. (* conversion *)

(* conversion.injectivity *)
Theorem injectivity
  : forall {A : Type} {cmp : A -> A -> Comparison} (s1 : SortedSet cmp) (s2 : SortedSet cmp) .
      to_avl s1 = to_avl s2 -> s1 = s2.
Proof.
  intros A cmp s1 s2.
  match &s1 with | introduction t1 p1 end.
  match &s2 with | introduction t2 p2 end.
  simpl to_avl in |- *.
  intro e.
  extro &p2.
  match &e with end.
  intro p2.
  ipso (congru (SortedSet.introduction &t1), (Assert.uniqueness _ &p1 &p2)).
Qed.

(* conversion.size *)
Theorem size
  : forall {A : Type} {cmp : A -> A -> Comparison} (s : SortedSet cmp) .
      (|| to_list s ||)%list = size s.
Proof.
  intros A cmp s.
  match &s with | introduction t p end.
  ipso (BinaryTree.conversion.size (AVL.to_tree &t)).
Qed.

End conversion. (* conversion *)

(* emptiness *)
Theorem emptiness
  : forall {A : Type} (cmp : A -> A -> Comparison) (a : A) . contains a (empty cmp) = false.
Proof.
  intros A cmp a.
  simpl contains, to_avl, empty in |- *.
  simpl in |- *.
  quod idem est.
Qed.

Module insertion. (* insertion *)

(* The search on the tree after [AVL.insert] answers the tree's membership,
 * since the tree is still ordered; the membership law of [AVL.insert] then
 * carries it back to a search on the tree before.
 *)
(* insertion.membership *)
Theorem membership
  : forall {A : Type} {cmp : A -> A -> Comparison} {lt : A -> A -> Prop}
      {C : Comparable cmp lt} (a : A) (b : A) (s : SortedSet cmp) .
      contains b (insert a s) = true <-> b = a \/ contains b s = true.
Proof.
  intros A cmp lt C a b s.
  match &s with | introduction t p end.
  let proof parts := Biconditional.forward.elimination (AVL.validity.reflection &C &t) &p.
  match &parts with | m rest end.
  match &rest with | bt o end.
  let proof o' := AVL.insertion.preservation.order &C &a &t &o.
  let proof after := AVL.search.specification &C &b (AVL.insert &cmp &a &t) &o'.
  let proof added := AVL.insertion.membership &C &a &b &t.
  let proof before := AVL.search.specification &C &b &t &o.
  lemma shown
    : AVL.contains &cmp &b (AVL.insert &cmp &a &t) = true
      <-> &b = &a \/ AVL.contains &cmp &b &t = true.
  {
    divide et impera.
    - intro h.
      modus aequans &after, &h |- h1.
      modus aequans &added, &h1 |- h2.
      match &h2 with | e | inside end.
      + ipso (disjoin &e, _).
      + ipso (disjoin _, (modus aequans &before, &inside)).
    - intro h.
      match &h with | e | found end.
      + modus aequans &added, (disjoin &e, _) |- h1.
        ipso (modus aequans &after, &h1).
      + modus aequans &before, &found |- inside.
        modus aequans &added, (disjoin _, &inside) |- h1.
        ipso (modus aequans &after, &h1).
  }
  ipso &shown.
Qed.

Module size. (* insertion.size *)

(* insertion.size.growth *)
Theorem growth
  : forall {A : Type} {cmp : A -> A -> Comparison} {lt : A -> A -> Prop}
      {C : Comparable cmp lt} (a : A) (s : SortedSet cmp) .
      contains a s = false -> size (insert a s) = (++ (size s))%n0.
Proof.
  intros A cmp lt C a s.
  match &s with | introduction t p end.
  simpl contains, size, insert, to_avl in |- *.
  ipso (AVL.insertion.size.growth &cmp &a &t).
Qed.

(* insertion.size.invariance *)
Theorem invariance
  : forall {A : Type} {cmp : A -> A -> Comparison} {lt : A -> A -> Prop}
      {C : Comparable cmp lt} (a : A) (s : SortedSet cmp) .
      contains a s = true -> size (insert a s) = size s.
Proof.
  intros A cmp lt C a s.
  match &s with | introduction t p end.
  simpl contains, size, insert, to_avl in |- *.
  ipso (AVL.insertion.size.invariance &cmp &a &t).
Qed.

End size. (* insertion.size *)

End insertion. (* insertion *)

Module removal. (* removal *)

(* The search on the tree after [AVL.remove] answers the tree's membership,
 * since the tree is still ordered; the membership law of [AVL.remove] then
 * carries it back to a search on the tree before.
 *)
(* removal.membership *)
Theorem membership
  : forall {A : Type} {cmp : A -> A -> Comparison} {lt : A -> A -> Prop}
      {C : Comparable cmp lt} (a : A) (b : A) (s : SortedSet cmp) .
      contains b (remove a s) = true <-> contains b s = true /\ ~ (b = a).
Proof.
  intros A cmp lt C a b s.
  match &s with | introduction t p end.
  let proof parts := Biconditional.forward.elimination (AVL.validity.reflection &C &t) &p.
  match &parts with | m rest end.
  match &rest with | bt o end.
  let proof o' := AVL.removal.preservation.order &C &a &t &o.
  let proof after := AVL.search.specification &C &b (AVL.remove &cmp &a &t) &o'.
  let proof removed := AVL.removal.membership &C &a &b &t &o.
  let proof before := AVL.search.specification &C &b &t &o.
  lemma shown
    : AVL.contains &cmp &b (AVL.remove &cmp &a &t) = true
      <-> AVL.contains &cmp &b &t = true /\ ~ (&b = &a).
  {
    divide et impera.
    - intro h.
      modus aequans &after, &h |- h1.
      modus aequans &removed, &h1 |- h2.
      match &h2 with | inside differs end.
      ipso (conjoin (modus aequans &before, &inside), &differs).
    - intro h.
      match &h with | found differs end.
      modus aequans &before, &found |- inside.
      modus aequans &removed, (conjoin &inside, &differs) |- h1.
      ipso (modus aequans &after, &h1).
  }
  ipso &shown.
Qed.

Module size. (* removal.size *)

(* removal.size.shrinkage *)
Theorem shrinkage
  : forall {A : Type} {cmp : A -> A -> Comparison} {lt : A -> A -> Prop}
      {C : Comparable cmp lt} (a : A) (s : SortedSet cmp) .
      contains a s = true -> (++ (size (remove a s)))%n0 = size s.
Proof.
  intros A cmp lt C a s.
  match &s with | introduction t p end.
  simpl contains, size, remove, to_avl in |- *.
  ipso (AVL.removal.size.shrinkage &cmp &a &t).
Qed.

(* removal.size.invariance *)
Theorem invariance
  : forall {A : Type} {cmp : A -> A -> Comparison} {lt : A -> A -> Prop}
      {C : Comparable cmp lt} (a : A) (s : SortedSet cmp) .
      contains a s = false -> size (remove a s) = size s.
Proof.
  intros A cmp lt C a s.
  match &s with | introduction t p end.
  simpl contains, size, remove, to_avl in |- *.
  ipso (AVL.removal.size.invariance &cmp &a &t).
Qed.

End size. (* removal.size *)

End removal. (* removal *)

End SortedSet. (* SortedSet *)

Abbreviation SortedSet := SortedSet.T.
