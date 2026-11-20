(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

From jwa Require Import Core.All.
From jwa Require Import Data.Assert.
From jwa Require Import Data.Base.Bool.
From jwa Require Import Data.Base.Comparison.
From jwa Require Import Data.Collection.BST.
From jwa Require Import Data.Collection.BinaryTree.
From jwa Require Import Data.Collection.List.
From jwa Require Import Data.Comparable.
From jwa Require Import Data.Number.Nat0.
From jwa Require Import Data.Option.
From jwa Require Import Data.Product.
From jwa Require Import Dialect.ExFalso.
From jwa Require Import Tactics.Equation.
From jwa Require Import Tactics.Modus.

(* An AVL tree is a binary tree that stores at each node the height of the
 * subtree there, and keeps the heights of every node's two subtrees within
 * one of each other, so that a path from the root is short.
 *)
Module AVL. (* AVL *)

(* A node holds its left subtree, its element, its right subtree, and last
 * the height of the subtree it roots.
 *)
Inductive T (A : Type) : Type :=
  | Leaf : T A
  | Node : T A -> A -> T A -> Nat0 -> T A.

(* [A] is inferred from the element or, for [Leaf], from the expected type;
 * a use that has neither needs [@Leaf A].
 *)
Arguments Leaf {A}.
Arguments Node {A} l a r h.

Abbreviation AVL := T.

(* [Nat0]'s scope is opened for the [++] of the heights. *)
Local Open Scope jwa_nat0_scope.

(* The eliminator that [match ... per] takes, written out. Each hypothesis
 * stands right after the subtree it is about.
 *)
Definition induction
  : forall (A : Type) (P : AVL A -> Prop) .
      P Leaf ->
      (forall (l : AVL A) . P l ->
        forall (a : A) (r : AVL A) . P r -> forall (h : Nat0) . P (Node l a r h)) ->
      (forall (t : AVL A) . P t)
  := fun (A : Type) (P : AVL A -> Prop) (base : P Leaf)
      (step : forall (l : AVL A) . P l ->
        forall (a : A) (r : AVL A) . P r -> forall (h : Nat0) . P (Node l a r h)) .
      fix go (t : AVL A) : P t :=
        match t with
        | Leaf         => base
        | Node l a r h => step l (go l) a r (go r) h
        end.

(* The stored height, read in one step; a leaf has height zero. *)
(* [forall {A : Type} . AVL A -> Nat0] *)
Definition height := fun {A : Type} (t : AVL A) .
  match t with
  | AVL.Leaf         => Nat0.Zero
  | AVL.Node _ _ _ h => h
  end.

(* A node over [l] and [r] whose stored height is one above the higher of
 * the two.
 *)
(* [forall {A : Type} . AVL A -> A -> AVL A -> AVL A] *)
Definition node := fun {A : Type} (l : AVL A) (a : A) (r : AVL A) .
  AVL.Node l a r (++ (Nat0.max (height l) (height r))).

(* The same tree without its heights. *)
(* [forall {A : Type} . AVL A -> BinaryTree A] *)
Fixpoint to_tree {A : Type} (t : AVL A) : BinaryTree A :=
  match t with
  | AVL.Leaf         => BinaryTree.Leaf
  | AVL.Node l a r _ => BinaryTree.Node (to_tree l) a (to_tree r)
  end.

(* Every stored height is right: at each node, one above the higher of the
 * heights its two subtrees store. A tree built by hand may store any number,
 * so this is a proposition about a tree, not a property of the type; with
 * it, the stored height is the height of [to_tree], by
 * [measurement.specification].
 *)
(* [forall {A : Type} . AVL A -> Prop] *)
Fixpoint Measured {A : Type} (t : AVL A) : Prop :=
  match t with
  | AVL.Leaf         => Verum
  | AVL.Node l _ r h => h = ++ (Nat0.max (height l) (height r)) /\ Measured l /\ Measured r
  end.

(* At each node the heights of the two subtrees are equal or one apart. Each
 * case is an equation, so that a proof meets no inequality.
 *)
(* [forall {A : Type} . AVL A -> Prop] *)
Fixpoint Balanced {A : Type} (t : AVL A) : Prop :=
  match t with
  | AVL.Leaf         => Verum
  | AVL.Node l _ r _ =>
      (height l = height r \/ height l = ++ (height r) \/ height r = ++ (height l))
      /\ Balanced l
      /\ Balanced r
  end.

(* The order of a search tree, read on the tree without its heights: at
 * every node the left subtree holds what is below the node's element, and
 * the right subtree what is above it.
 *)
(* [forall {A : Type} . (A -> A -> Prop) -> AVL A -> Prop] *)
Definition Ordered := fun {A : Type} (lt : A -> A -> Prop) (t : AVL A) .
  BST.Ordered lt (to_tree t).

(* The test that a tree is [Measured], answered as a [Bool]. *)
(* [forall {A : Type} . AVL A -> Bool] *)
Fixpoint is_measured {A : Type} (t : AVL A) : Bool :=
  match t with
  | AVL.Leaf         => true
  | AVL.Node l _ r h =>
      Bool.and
        (Nat0.eq h (++ (Nat0.max (height l) (height r))))
        (Bool.and (is_measured l) (is_measured r))
  end.

(* The test that a tree is [Balanced], answered as a [Bool]. *)
(* [forall {A : Type} . AVL A -> Bool] *)
Fixpoint is_balanced {A : Type} (t : AVL A) : Bool :=
  match t with
  | AVL.Leaf         => true
  | AVL.Node l _ r _ =>
      Bool.and
        (Bool.or
          (Nat0.eq (height l) (height r))
          (Bool.or (Nat0.eq (height l) (++ (height r))) (Nat0.eq (height r) (++ (height l)))))
        (Bool.and (is_balanced l) (is_balanced r))
  end.

(* The test that a tree is ordered by [cmp], read on the tree without its
 * heights.
 *)
(* [forall {A : Type} . (A -> A -> Comparison) -> AVL A -> Bool] *)
Definition is_ordered := fun {A : Type} (cmp : A -> A -> Comparison) (t : AVL A) .
  BST.is_ordered cmp (to_tree t).

(* The three tests at once: a tree that passes is one that [insert] and
 * [remove] keep in shape.
 *)
(* [forall {A : Type} . (A -> A -> Comparison) -> AVL A -> Bool] *)
Definition is_valid := fun {A : Type} (cmp : A -> A -> Comparison) (t : AVL A) .
  Bool.and (is_measured t) (Bool.and (is_balanced t) (is_ordered cmp t)).

Module rotate. (* rotate *)

(* A node whose left subtree stands two above its right one, rebuilt one
 * level lower on the left. Where the left subtree's own right subtree is the
 * higher, its root comes up to the top: a double rotation. Otherwise the
 * left subtree's root does: a single one.
 *)
(* [forall {A : Type} . AVL A -> A -> AVL A -> AVL A] *)
Definition right := fun {A : Type} (l : AVL A) (a : A) (r : AVL A) .
  match l with
  | AVL.Leaf           => node l a r
  | AVL.Node ll b lr _ =>
      match Nat0.eq (height lr) (++ (height ll)) with
      | true  =>
          match lr with
          | AVL.Leaf             => node l a r
          | AVL.Node lrl c lrr _ => node (node ll b lrl) c (node lrr a r)
          end
      | false => node ll b (node lr a r)
      end
  end.

(* The mirror of [rotate.right], for a right subtree two above the left. *)
(* [forall {A : Type} . AVL A -> A -> AVL A -> AVL A] *)
Definition left := fun {A : Type} (l : AVL A) (a : A) (r : AVL A) .
  match r with
  | AVL.Leaf           => node l a r
  | AVL.Node rl b rr _ =>
      match Nat0.eq (height rl) (++ (height rr)) with
      | true  =>
          match rl with
          | AVL.Leaf             => node l a r
          | AVL.Node rll c rlr _ => node (node l a rll) c (node rlr b rr)
          end
      | false => node (node l a rl) b rr
      end
  end.

End rotate. (* rotate *)

(* A node over [l] and [r] whose heights may be two apart: the higher side is
 * rotated down, and otherwise the node is built as it stands.
 *)
(* [forall {A : Type} . AVL A -> A -> AVL A -> AVL A] *)
Definition balance := fun {A : Type} (l : AVL A) (a : A) (r : AVL A) .
  match Nat0.eq (height l) (++ (++ (height r))) with
  | true  => rotate.right l a r
  | false =>
      match Nat0.eq (height r) (++ (++ (height l))) with
      | true  => rotate.left l a r
      | false => node l a r
      end
  end.

(* [cmp a b] picks one subtree at each node, so the search follows one path
 * from the root down. Its answer is the tree's membership only where the
 * tree is [Ordered].
 *)
(* [forall {A : Type} . (A -> A -> Comparison) -> A -> AVL A -> Bool] *)
Fixpoint contains {A : Type} (cmp : A -> A -> Comparison) (a : A) (t : AVL A) : Bool :=
  match t with
  | AVL.Leaf         => false
  | AVL.Node l b r _ =>
      match cmp a b with
      | Comparison.Lt => contains cmp a l
      | Comparison.Eq => true
      | Comparison.Gt => contains cmp a r
      end
  end.

(* [insert] walks the path that the comparison picks, puts [a] at the leaf
 * it ends on, and rebalances each node on the way back up. An element the
 * tree already holds is not added again.
 *)
(* [forall {A : Type} . (A -> A -> Comparison) -> A -> AVL A -> AVL A] *)
Fixpoint insert {A : Type} (cmp : A -> A -> Comparison) (a : A) (t : AVL A) : AVL A :=
  match t with
  | AVL.Leaf         => node AVL.Leaf a AVL.Leaf
  | AVL.Node l b r h =>
      match cmp a b with
      | Comparison.Lt => balance (insert cmp a l) b r
      | Comparison.Eq => AVL.Node l b r h
      | Comparison.Gt => balance l b (insert cmp a r)
      end
  end.

(* The first element in order, the leftmost one, paired with the tree that
 * is left, each node on the way back up rebalanced; [None] on a leaf. On an
 * [Ordered] tree the first element is the smallest, by
 * [extraction.minimality].
 *)
(* [forall {A : Type} . AVL A -> Option (Product A (AVL A))] *)
Fixpoint pop {A : Type} (t : AVL A) : Option (Product A (AVL A)) :=
  match t with
  | AVL.Leaf         => None
  | AVL.Node l a r _ =>
      match pop l with
      | None                             => Some (Product.introduction a r)
      | Some (Product.introduction m l') => Some (Product.introduction m (balance l' a r))
      end
  end.

(* One tree out of two, for an [l] that lies wholly below [r]: the smallest
 * element of [r] becomes the root, the one element that may stand between
 * the two.
 *)
(* [forall {A : Type} . AVL A -> AVL A -> AVL A] *)
Definition join := fun {A : Type} (l : AVL A) (r : AVL A) .
  match pop r with
  | None                             => l
  | Some (Product.introduction m r') => balance l m r'
  end.

(* [remove] walks the path that the comparison picks. Where it finds [a],
 * the node goes and its two subtrees are joined; each node on the way back
 * up is rebalanced.
 *)
(* [forall {A : Type} . (A -> A -> Comparison) -> A -> AVL A -> AVL A] *)
Fixpoint remove {A : Type} (cmp : A -> A -> Comparison) (a : A) (t : AVL A) : AVL A :=
  match t with
  | AVL.Leaf         => AVL.Leaf
  | AVL.Node l b r _ =>
      match cmp a b with
      | Comparison.Lt => balance (remove cmp a l) b r
      | Comparison.Eq => join l r
      | Comparison.Gt => balance l b (remove cmp a r)
      end
  end.

Module construction. (* construction *)

(* construction.measurement *)
Theorem measurement
  : forall {A : Type} (l : AVL A) (a : A) (r : AVL A) .
      Measured l -> Measured r -> Measured (node l a r).
Proof.
  intros A l a r ml mr.
  simpl node in |- *.
  simpl in |- *.
  ipso (conjoin (Identity.reflexivity _), (conjoin &ml, &mr)).
Qed.

End construction. (* construction *)

Module measurement. (* measurement *)

(* measurement.specification *)
Theorem specification
  : forall {A : Type} (t : AVL A) . Measured t -> height t = BinaryTree.height (to_tree t).
Proof.
  intros A t.
  match &t with | Leaf | Node (l by IHl) a (r by IHr) h end per AVL.induction.
  - intro m.
    simpl in |- *.
    quod idem est.
  - intro m.
    let proof m0 := simpl &m.
    match &m0 with | e m' end.
    match &m' with | ml mr end.
    modus ponens &IHl, &ml |- el.
    modus ponens &IHr, &mr |- er.
    simpl in |- *.
    leibniz &e, &el, &er in |- *.
    quod idem est.
Qed.

(* measurement.reflection *)
Theorem reflection
  : forall {A : Type} (t : AVL A) . Assert (is_measured t) <-> Measured t.
Proof.
  intros A t.
  match &t with | Leaf | Node (l by IHl) a (r by IHr) h end per AVL.induction.
  - simpl in |- *.
    ipso (Biconditional.reflexivity _).
  - simpl in |- *.
    let proof q
      := Biconditional.transitivity
           (Assert.specification (Nat0.eq &h (++ (Nat0.max (height &l) (height &r)))))
           (Comparable.comparison.equality.reflection
             &h (++ (Nat0.max (height &l) (height &r)))).
    divide et impera.
    + intro w.
      modus aequans (Assert.conjunction _ _), &w |- w1.
      match &w1 with | he w2 end.
      modus aequans (Assert.conjunction _ _), &w2 |- w3.
      match &w3 with | ml mr end.
      ipso
        (conjoin (modus aequans &q, &he),
          (conjoin (modus aequans &IHl, &ml), (modus aequans &IHr, &mr))).
    + intro w.
      match &w with | e w2 end.
      match &w2 with | ml mr end.
      modus aequans &q, &e |- he.
      modus aequans &IHl, &ml |- il.
      modus aequans &IHr, &mr |- ir.
      modus aequans (Assert.conjunction _ _), (conjoin &il, &ir) |- w3.
      ipso (modus aequans (Assert.conjunction _ _), (conjoin &he, &w3)).
Qed.

End measurement. (* measurement *)

(* The laws of the rule [Balanced], under a noun of their own: [balance]
 * and [balancing] are the operation and its laws.
 *)
Module equilibrium. (* equilibrium *)

(* equilibrium.reflection *)
Theorem reflection
  : forall {A : Type} (t : AVL A) . Assert (is_balanced t) <-> Balanced t.
Proof.
  intros A t.
  lemma equation
    : forall (m : Nat0) (n : Nat0) . Assert (Nat0.eq m n) <-> m = n.
  {
    intros m n.
    ipso
      (Biconditional.transitivity
        (Assert.specification (Nat0.eq &m &n))
        (Comparable.comparison.equality.reflection &m &n)).
  }
  match &t with | Leaf | Node (l by IHl) a (r by IHr) h end per AVL.induction.
  - simpl in |- *.
    ipso (Biconditional.reflexivity _).
  - simpl in |- *.
    lemma rel
      : Assert
          (Bool.or
            (Nat0.eq (height &l) (height &r))
            (Bool.or
              (Nat0.eq (height &l) (++ (height &r)))
              (Nat0.eq (height &r) (++ (height &l)))))
        <-> height &l = height &r
          \/ height &l = ++ (height &r)
          \/ height &r = ++ (height &l).
    {
      let proof d1
        := Assert.disjunction
             (Nat0.eq (height &l) (height &r))
             (Bool.or
               (Nat0.eq (height &l) (++ (height &r)))
               (Nat0.eq (height &r) (++ (height &l)))).
      let proof d2
        := Assert.disjunction
             (Nat0.eq (height &l) (++ (height &r)))
             (Nat0.eq (height &r) (++ (height &l))).
      divide et impera.
      - intro w.
        modus aequans &d1, &w |- w1.
        match &w1 with | e | w2 end.
        + ipso (disjoin (modus aequans (&equation _ _), &e), _).
        + modus aequans &d2, &w2 |- w3.
          match &w3 with | e | e end.
          * ipso (disjoin _, (disjoin (modus aequans (&equation _ _), &e), _)).
          * ipso (disjoin _, (disjoin _, (modus aequans (&equation _ _), &e))).
      - intro w.
        match &w with | e | w2 end.
        + modus aequans (&equation (height &l) (height &r)), &e |- t.
          modus aequans &d1, (disjoin &t, _) |- done.
          ipso &done.
        + match &w2 with | e | e end.
          * modus aequans (&equation (height &l) (++ (height &r))), &e |- t.
            modus aequans &d2, (disjoin &t, _) |- t'.
            modus aequans &d1, (disjoin _, &t') |- done.
            ipso &done.
          * modus aequans (&equation (height &r) (++ (height &l))), &e |- t.
            modus aequans &d2, (disjoin _, &t) |- t'.
            modus aequans &d1, (disjoin _, &t') |- done.
            ipso &done.
    }
    divide et impera.
    + intro w.
      modus aequans (Assert.conjunction _ _), &w |- w1.
      match &w1 with | hr w2 end.
      modus aequans (Assert.conjunction _ _), &w2 |- w3.
      match &w3 with | bl br end.
      ipso
        (conjoin (modus aequans &rel, &hr),
          (conjoin (modus aequans &IHl, &bl), (modus aequans &IHr, &br))).
    + intro w.
      match &w with | e w2 end.
      match &w2 with | bl br end.
      modus aequans &rel, &e |- hr.
      modus aequans &IHl, &bl |- il.
      modus aequans &IHr, &br |- ir.
      modus aequans (Assert.conjunction _ _), (conjoin &il, &ir) |- w3.
      ipso (modus aequans (Assert.conjunction _ _), (conjoin &hr, &w3)).
Qed.

End equilibrium. (* equilibrium *)

Module order. (* order *)

(* order.reflection *)
Theorem reflection
  : forall {A : Type} {cmp : A -> A -> Comparison} {lt : A -> A -> Prop} .
      Comparable cmp lt ->
      forall (t : AVL A) . Assert (is_ordered cmp t) <-> Ordered lt t.
Proof.
  intros A cmp lt C t.
  ipso (BST.order.reflection &C (to_tree &t)).
Qed.

End order. (* order *)

Module validity. (* validity *)

(* validity.reflection *)
Theorem reflection
  : forall {A : Type} {cmp : A -> A -> Comparison} {lt : A -> A -> Prop} .
      Comparable cmp lt ->
      forall (t : AVL A) .
        Assert (is_valid cmp t) <-> Measured t /\ Balanced t /\ Ordered lt t.
Proof.
  intros A cmp lt C t.
  let proof qm := measurement.reflection &t.
  let proof qb := equilibrium.reflection &t.
  let proof qo := order.reflection &C &t.
  simpl is_valid in |- *.
  divide et impera.
  - intro w.
    modus aequans (Assert.conjunction _ _), &w |- w1.
    match &w1 with | m w2 end.
    modus aequans (Assert.conjunction _ _), &w2 |- w3.
    match &w3 with | b o end.
    ipso
      (conjoin (modus aequans &qm, &m),
        (conjoin (modus aequans &qb, &b), (modus aequans &qo, &o))).
  - intro w.
    match &w with | m w2 end.
    match &w2 with | b o end.
    modus aequans &qm, &m |- am.
    modus aequans &qb, &b |- ab.
    modus aequans &qo, &o |- ao.
    modus aequans (Assert.conjunction _ _), (conjoin &ab, &ao) |- w3.
    ipso (modus aequans (Assert.conjunction _ _), (conjoin &am, &w3)).
Qed.

End validity. (* validity *)

Module search. (* search *)

(* search.specification *)
Theorem specification
  : forall {A : Type} {cmp : A -> A -> Comparison} {lt : A -> A -> Prop} .
      Comparable cmp lt ->
      forall (a : A) (t : AVL A) .
        Ordered lt t -> (contains cmp a t = true <-> BinaryTree.Contains a (to_tree t)).
Proof.
  intros A cmp lt C a t.
  lemma same : contains &cmp &a &t = BST.contains &cmp &a (to_tree &t).
  {
    match &t with | Leaf | Node (l by IHl) b (r by IHr) h end per AVL.induction.
    - simpl in |- *.
      quod idem est.
    - simpl in |- *.
      match (&cmp &a &b) with | | | end |- c.
      + ipso &IHl.
      + quod idem est.
      + ipso &IHr.
  }
  intro o.
  leibniz &same in |- *.
  ipso (BST.search.specification &C &a (to_tree &t) &o).
Qed.

End search. (* search *)

Module rotation. (* rotation *)

Module right. (* rotation.right *)

(* A rotation keeps the elements in their order from left to right, so the
 * two lists [BinaryTree.to_list] reads are the same; [membership] and [size]
 * both go through them.
 *)
(* rotation.right.sequence *)
Lemma sequence
  : forall {A : Type} (l : AVL A) (a : A) (r : AVL A) .
      BinaryTree.to_list (to_tree (rotate.right l a r))
      = BinaryTree.to_list (to_tree (node l a r)).
Proof.
  intros A l a r.
  simpl rotate.right in |- *.
  match &l with | Leaf | Node ll c lr hl end.
  - simpl in |- *.
    quod idem est.
  - match (Nat0.eq (height &lr) (++ (height &ll))) with | | end |- t.
    + match &lr with | Leaf | Node lrl d lrr hlr end.
      * simpl in |- *.
        quod idem est.
      * simpl node in |- *.
        simpl in |- *.
        leibniz
          (List.concatenation.associativity
            (BinaryTree.to_list (to_tree &ll))
            (List.Cons &c (BinaryTree.to_list (to_tree &lrl)))
            (List.Cons &d
              (List.concat
                (BinaryTree.to_list (to_tree &lrr))
                (List.Cons &a (BinaryTree.to_list (to_tree &r))))))
          in |- *.
        leibniz
          (List.concatenation.associativity
            (BinaryTree.to_list (to_tree &ll))
            (List.Cons &c
              (List.concat
                (BinaryTree.to_list (to_tree &lrl))
                (List.Cons &d (BinaryTree.to_list (to_tree &lrr)))))
            (List.Cons &a (BinaryTree.to_list (to_tree &r))))
          in |- *.
        simpl in |- *.
        leibniz
          (List.concatenation.associativity
            (BinaryTree.to_list (to_tree &lrl))
            (List.Cons &d (BinaryTree.to_list (to_tree &lrr)))
            (List.Cons &a (BinaryTree.to_list (to_tree &r))))
          in |- *.
        simpl in |- *.
        quod idem est.
    + simpl node in |- *.
      simpl in |- *.
      leibniz
        (List.concatenation.associativity
          (BinaryTree.to_list (to_tree &ll))
          (List.Cons &c (BinaryTree.to_list (to_tree &lr)))
          (List.Cons &a (BinaryTree.to_list (to_tree &r))))
        in |- *.
      simpl in |- *.
      quod idem est.
Qed.

(* rotation.right.membership *)
Theorem membership
  : forall {A : Type} (l : AVL A) (a : A) (r : AVL A) (b : A) .
      BinaryTree.Contains b (to_tree (rotate.right l a r))
      <-> BinaryTree.Contains b (to_tree (node l a r)).
Proof.
  intros A l a r b.
  let proof here := BinaryTree.conversion.membership &b (to_tree (rotate.right &l &a &r)).
  let proof there := BinaryTree.conversion.membership &b (to_tree (node &l &a &r)).
  leibniz (rotation.right.sequence &l &a &r) in &here.
  ipso (Biconditional.transitivity &here (Biconditional.symmetry &there)).
Qed.

(* rotation.right.size *)
Theorem size
  : forall {A : Type} (l : AVL A) (a : A) (r : AVL A) .
      BinaryTree.size (to_tree (rotate.right l a r)) = BinaryTree.size (to_tree (node l a r)).
Proof.
  intros A l a r.
  leibniz
    <- (BinaryTree.conversion.size (to_tree (rotate.right &l &a &r))),
    <- (BinaryTree.conversion.size (to_tree (node &l &a &r)))
    in |- *.
  leibniz (rotation.right.sequence &l &a &r) in |- *.
  quod idem est.
Qed.

(* A subtree that moves to a new parent is below or above it by
 * transitivity, through the element it was compared with before.
 *)
(* rotation.right.order *)
Theorem order
  : forall {A : Type} {lt : A -> A -> Prop} .
      (forall (x : A) (y : A) (z : A) . lt x y -> lt y z -> lt x z) ->
      forall (l : AVL A) (a : A) (r : AVL A) .
        Ordered lt (node l a r) -> Ordered lt (rotate.right l a r).
Proof.
  intros A lt tr l a r o.
  simpl Ordered, node in &o.
  simpl Ordered, rotate.right in |- *.
  let proof o0 := simpl &o.
  match &o0 with | below o1 end.
  match &o1 with | above o2 end.
  match &o2 with | ordl ordr end.
  match &l with | Leaf | Node ll c lr hl end.
  - ipso &o.
  - simpl in &below.
    match &below with | bll b1 end.
    match &b1 with | ca blr end.
    simpl in &ordl.
    match &ordl with | cll c1 end.
    match &c1 with | clr c2 end.
    match &c2 with | oll olr end.
    match (Nat0.eq (height &lr) (++ (height &ll))) with | | end |- t.
    + match &lr with | Leaf | Node lrl d lrr hlr end.
      * ipso &o.
      * simpl in &blr.
        match &blr with | blrl b2 end.
        match &b2 with | da blrr end.
        simpl in &clr.
        match &clr with | clrl c3 end.
        match &c3 with | cd clrr end.
        simpl in &olr.
        match &olr with | dlrl d1 end.
        match &d1 with | dlrr d2 end.
        match &d2 with | olrl olrr end.
        let proof dll
          := BinaryTree.quantification.all.monotonicity
               (fun (x : &A) (h : &lt x &c) . &tr x &c &d h &cd) &cll.
        let proof dr
          := BinaryTree.quantification.all.monotonicity
               (fun (x : &A) (h : &lt &a x) . &tr &d &a x &da h) &above.
        simpl node in |- *.
        simpl in |- *.
        ipso
          (conjoin (conjoin &dll, (conjoin &cd, &dlrl)),
            (conjoin (conjoin &dlrr, (conjoin &da, &dr)),
              (conjoin (conjoin &cll, (conjoin &clrl, (conjoin &oll, &olrl))),
                (conjoin &blrr, (conjoin &above, (conjoin &olrr, &ordr)))))).
    + let proof cr
        := BinaryTree.quantification.all.monotonicity
             (fun (x : &A) (h : &lt &a x) . &tr &c &a x &ca h) &above.
      simpl node in |- *.
      simpl in |- *.
      ipso
        (conjoin &cll,
          (conjoin (conjoin &clr, (conjoin &ca, &cr)),
            (conjoin &oll, (conjoin &blr, (conjoin &above, (conjoin &olr, &ordr)))))).
Qed.

(* rotation.right.measurement *)
Theorem measurement
  : forall {A : Type} (l : AVL A) (a : A) (r : AVL A) .
      Measured l -> Measured r -> Measured (rotate.right l a r).
Proof.
  intros A l a r ml mr.
  simpl rotate.right in |- *.
  match &l with | Leaf | Node ll b lr hl end.
  - ipso (construction.measurement _ _ _ &ml &mr).
  - let proof ml0 := simpl &ml.
    match &ml0 with | _ ml' end.
    match &ml' with | mll mlr end.
    match (Nat0.eq (height &lr) (++ (height &ll))) with | | end |- t.
    + match &lr with | Leaf | Node lrl c lrr hlr end.
      * ipso (construction.measurement _ _ _ &ml &mr).
      * let proof mlr0 := simpl &mlr.
        match &mlr0 with | _ mlr' end.
        match &mlr' with | mlrl mlrr end.
        ipso
          (construction.measurement _ _ _
            (construction.measurement _ _ _ &mll &mlrl)
            (construction.measurement _ _ _ &mlrr &mr)).
    + ipso (construction.measurement _ _ _ &mll (construction.measurement _ _ _ &mlr &mr)).
Qed.

(* Each case of [Balanced l] fixes the heights of [l]'s subtrees in terms of
 * [height r]; every height of the result is then rewritten into one number,
 * and each balance condition closes as an equation of that number.
 *)
(* rotation.right.balance *)
Theorem balance
  : forall {A : Type} (l : AVL A) (a : A) (r : AVL A) .
      Measured l -> Balanced l -> Balanced r ->
      height l = ++ (++ (height r)) -> Balanced (rotate.right l a r).
Proof.
  intros A l a r ml bl br h.
  match &l with | Leaf | Node ll b lr hl end.
  - simpl in &h.
    ex (Nat0.order.strict.distinction (Nat0.increment.order.positivity _) &h) quodlibet.
  - let proof ml0 := simpl &ml.
    match &ml0 with | hm ml' end.
    match &ml' with | mll mlr end.
    let proof bl0 := simpl &bl.
    match &bl0 with | rel bl' end.
    match &bl' with | bll blr end.
    simpl in &h.
    leibniz &hm in &h.
    let proof mx := Nat0.increment.injectivity &h.
    simpl rotate.right in |- *.
    match &rel with | e | rel' end.
    (* The subtrees of [l] are equally high: a single rotation. *)
    + leibniz <- &e in &mx.
      leibniz (Comparable.maximum.idempotence (height &ll)) in &mx.
      match (Nat0.eq (height &lr) (++ (height &ll))) with | | end |- t.
      * modus aequans
          (Comparable.comparison.equality.reflection (height &lr) (++ (height &ll))), &t
          |- e'.
        leibniz <- &e in &e'.
        ex (Nat0.order.strict.distinction (Nat0.increment.order.extensivity _) &e') quodlibet.
      * simpl node in |- *.
        simpl in |- *.
        leibniz <- &e in |- *.
        leibniz &mx in |- *.
        leibniz
          (modus aequans
            (Comparable.maximum.specification (++ (height &r)) (height &r)),
            (disjoin _, (Nat0.increment.order.extensivity (height &r))))
          in |- *.
        ipso
          (conjoin (disjoin _, (disjoin _, (Identity.reflexivity _))),
            (conjoin &bll,
              (conjoin (disjoin _, (disjoin (Identity.reflexivity _), _)), (conjoin &blr, &br)))).
    + match &rel' with | e | e end.
      (* The left subtree of [l] is the higher: a single rotation. *)
      * leibniz &e in &mx.
        leibniz
          (modus aequans
            (Comparable.maximum.specification (++ (height &lr)) (height &lr)),
            (disjoin _, (Nat0.increment.order.extensivity (height &lr))))
          in &mx.
        let proof mx2 := Nat0.increment.injectivity &mx.
        match (Nat0.eq (height &lr) (++ (height &ll))) with | | end |- t.
        -- modus aequans
             (Comparable.comparison.equality.reflection (height &lr) (++ (height &ll))), &t
             |- e'.
           leibniz &e in &e'.
           ex
             (Nat0.order.strict.distinction
               (Nat0.order.strict.transitivity
                 (Nat0.increment.order.extensivity _) (Nat0.increment.order.extensivity _))
               &e')
             quodlibet.
        -- simpl node in |- *.
           simpl in |- *.
           leibniz &e in |- *.
           leibniz &mx2 in |- *.
           leibniz (Comparable.maximum.idempotence (height &r)) in |- *.
           ipso
             (conjoin (disjoin (Identity.reflexivity _), _),
               (conjoin &bll,
                 (conjoin (disjoin (Identity.reflexivity _), _), (conjoin &blr, &br)))).
      (* The right subtree of [l] is the higher: a double rotation. *)
      * leibniz &e in &mx.
        leibniz (Comparable.maximum.commutativity (height &ll) (++ (height &ll))) in &mx.
        leibniz
          (modus aequans
            (Comparable.maximum.specification (++ (height &ll)) (height &ll)),
            (disjoin _, (Nat0.increment.order.extensivity (height &ll))))
          in &mx.
        let proof mx2 := Nat0.increment.injectivity &mx.
        match (Nat0.eq (height &lr) (++ (height &ll))) with | | end |- t.
        -- match &lr with | Leaf | Node lrl c lrr hlr end.
           ++ simpl in &e.
              ex (Nat0.order.strict.distinction (Nat0.increment.order.positivity _) &e) quodlibet.
           ++ let proof mlr0 := simpl &mlr.
              match &mlr0 with | hm2 mlr' end.
              match &mlr' with | mlrl mlrr end.
              let proof blr0 := simpl &blr.
              match &blr0 with | rel2 blr' end.
              match &blr' with | blrl blrr end.
              simpl in &e.
              leibniz &hm2 in &e.
              let proof mx3 := Nat0.increment.injectivity &e.
              simpl node in |- *.
              simpl in |- *.
              match &rel2 with | e3 | rel3 end.
              ** leibniz <- &e3 in &mx3.
                 leibniz (Comparable.maximum.idempotence (height &lrl)) in &mx3.
                 leibniz <- &e3 in |- *.
                 leibniz &mx3 in |- *.
                 leibniz &mx2 in |- *.
                 leibniz (Comparable.maximum.idempotence (height &r)) in |- *.
                 ipso
                   (conjoin (disjoin (Identity.reflexivity _), _),
                     (conjoin
                       (conjoin (disjoin (Identity.reflexivity _), _), (conjoin &bll, &blrl)),
                       (conjoin (disjoin (Identity.reflexivity _), _), (conjoin &blrr, &br)))).
              ** match &rel3 with | e3 | e3 end.
                 --- leibniz &e3 in &mx3.
                     leibniz
                       (modus aequans
                         (Comparable.maximum.specification (++ (height &lrr)) (height &lrr)),
                         (disjoin _, (Nat0.increment.order.extensivity (height &lrr))))
                       in &mx3.
                     trans (symm &mx2), (symm &mx3) |- hr.
                     leibniz &e3 in |- *.
                     leibniz (symm &mx3) in |- *.
                     leibniz &hr in |- *.
                     leibniz (Comparable.maximum.idempotence (++ (height &lrr))) in |- *.
                     leibniz
                       (Comparable.maximum.commutativity (height &lrr) (++ (height &lrr)))
                       in |- *.
                     leibniz
                       (modus aequans
                         (Comparable.maximum.specification (++ (height &lrr)) (height &lrr)),
                         (disjoin _, (Nat0.increment.order.extensivity (height &lrr))))
                       in |- *.
                     ipso
                       (conjoin (disjoin (Identity.reflexivity _), _),
                         (conjoin
                           (conjoin (disjoin (Identity.reflexivity _), _), (conjoin &bll, &blrl)),
                           (conjoin (disjoin _, (disjoin _, (Identity.reflexivity _))),
                             (conjoin &blrr, &br)))).
                 --- leibniz &e3 in &mx3.
                     leibniz
                       (Comparable.maximum.commutativity (height &lrl) (++ (height &lrl)))
                       in &mx3.
                     leibniz
                       (modus aequans
                         (Comparable.maximum.specification (++ (height &lrl)) (height &lrl)),
                         (disjoin _, (Nat0.increment.order.extensivity (height &lrl))))
                       in &mx3.
                     trans (symm &mx2), (symm &mx3) |- hr.
                     leibniz &e3 in |- *.
                     leibniz (symm &mx3) in |- *.
                     leibniz &hr in |- *.
                     leibniz
                       (modus aequans
                         (Comparable.maximum.specification (++ (height &lrl)) (height &lrl)),
                         (disjoin _, (Nat0.increment.order.extensivity (height &lrl))))
                       in |- *.
                     leibniz (Comparable.maximum.idempotence (++ (height &lrl))) in |- *.
                     ipso
                       (conjoin (disjoin (Identity.reflexivity _), _),
                         (conjoin
                           (conjoin (disjoin _, (disjoin (Identity.reflexivity _), _)),
                             (conjoin &bll, &blrl)),
                           (conjoin (disjoin (Identity.reflexivity _), _), (conjoin &blrr, &br)))).
        -- modus aequans
             (Comparable.comparison.equality.reflection (height &lr) (++ (height &ll))), &e
             |- t'.
           leibniz &t' in &t.
           ex &t quodlibet.
Qed.

(* The result is as high as [l], or one higher when the two subtrees of [l]
 * were equally high.
 *)
(* rotation.right.growth *)
Theorem growth
  : forall {A : Type} (l : AVL A) (a : A) (r : AVL A) .
      Measured l -> Balanced l -> height l = ++ (++ (height r)) ->
      height (rotate.right l a r) = height l \/ height (rotate.right l a r) = ++ (height l).
Proof.
  intros A l a r ml bl h.
  match &l with | Leaf | Node ll b lr hl end.
  - simpl in &h.
    ex (Nat0.order.strict.distinction (Nat0.increment.order.positivity _) &h) quodlibet.
  - let proof ml0 := simpl &ml.
    match &ml0 with | hm ml' end.
    match &ml' with | mll mlr end.
    let proof bl0 := simpl &bl.
    match &bl0 with | rel bl' end.
    match &bl' with | bll blr end.
    simpl in &h.
    leibniz &hm in &h.
    let proof mx := Nat0.increment.injectivity &h.
    simpl rotate.right in |- *.
    match &rel with | e | rel' end.
    + leibniz <- &e in &mx.
      leibniz (Comparable.maximum.idempotence (height &ll)) in &mx.
      match (Nat0.eq (height &lr) (++ (height &ll))) with | | end |- t.
      * modus aequans
          (Comparable.comparison.equality.reflection (height &lr) (++ (height &ll))), &t
          |- e'.
        leibniz <- &e in &e'.
        ex (Nat0.order.strict.distinction (Nat0.increment.order.extensivity _) &e') quodlibet.
      * simpl node in |- *.
        leibniz &hm in |- *.
        simpl in |- *.
        leibniz <- &e in |- *.
        leibniz &mx in |- *.
        leibniz
          (modus aequans
            (Comparable.maximum.specification (++ (height &r)) (height &r)),
            (disjoin _, (Nat0.increment.order.extensivity (height &r))))
          in |- *.
        leibniz (Comparable.maximum.idempotence (++ (height &r))) in |- *.
        leibniz (Comparable.maximum.commutativity (++ (height &r)) (++ (++ (height &r)))) in |- *.
        leibniz
          (modus aequans
            (Comparable.maximum.specification (++ (++ (height &r))) (++ (height &r))),
            (disjoin _, (Nat0.increment.order.extensivity (++ (height &r)))))
          in |- *.
        ipso (disjoin _, (Identity.reflexivity _)).
    + match &rel' with | e | e end.
      * leibniz &e in &mx.
        leibniz
          (modus aequans
            (Comparable.maximum.specification (++ (height &lr)) (height &lr)),
            (disjoin _, (Nat0.increment.order.extensivity (height &lr))))
          in &mx.
        let proof mx2 := Nat0.increment.injectivity &mx.
        match (Nat0.eq (height &lr) (++ (height &ll))) with | | end |- t.
        -- modus aequans
             (Comparable.comparison.equality.reflection (height &lr) (++ (height &ll))), &t
             |- e'.
           leibniz &e in &e'.
           ex
             (Nat0.order.strict.distinction
               (Nat0.order.strict.transitivity
                 (Nat0.increment.order.extensivity _) (Nat0.increment.order.extensivity _))
               &e')
             quodlibet.
        -- simpl node in |- *.
           leibniz &hm in |- *.
           simpl in |- *.
           leibniz &e in |- *.
           leibniz &mx2 in |- *.
           leibniz (Comparable.maximum.idempotence (height &r)) in |- *.
           leibniz (Comparable.maximum.idempotence (++ (height &r))) in |- *.
           leibniz
             (modus aequans
               (Comparable.maximum.specification (++ (height &r)) (height &r)),
               (disjoin _, (Nat0.increment.order.extensivity (height &r))))
             in |- *.
           ipso (disjoin (Identity.reflexivity _), _).
      * leibniz &e in &mx.
        leibniz (Comparable.maximum.commutativity (height &ll) (++ (height &ll))) in &mx.
        leibniz
          (modus aequans
            (Comparable.maximum.specification (++ (height &ll)) (height &ll)),
            (disjoin _, (Nat0.increment.order.extensivity (height &ll))))
          in &mx.
        let proof mx2 := Nat0.increment.injectivity &mx.
        match (Nat0.eq (height &lr) (++ (height &ll))) with | | end |- t.
        -- match &lr with | Leaf | Node lrl c lrr hlr end.
           ++ simpl in &e.
              ex (Nat0.order.strict.distinction (Nat0.increment.order.positivity _) &e) quodlibet.
           ++ let proof mlr0 := simpl &mlr.
              match &mlr0 with | hm2 mlr' end.
              let proof blr0 := simpl &blr.
              match &blr0 with | rel2 blr' end.
              simpl in &e.
              simpl node in |- *.
              leibniz &hm in |- *.
              simpl in |- *.
              leibniz &e in |- *.
              leibniz (Comparable.maximum.commutativity (height &ll) (++ (height &ll))) in |- *.
              leibniz
                (modus aequans
                  (Comparable.maximum.specification (++ (height &ll)) (height &ll)),
                  (disjoin _, (Nat0.increment.order.extensivity (height &ll))))
                in |- *.
              leibniz &hm2 in &e.
              let proof mx3 := Nat0.increment.injectivity &e.
              match &rel2 with | e3 | rel3 end.
              ** leibniz <- &e3 in &mx3.
                 leibniz (Comparable.maximum.idempotence (height &lrl)) in &mx3.
                 leibniz <- &e3 in |- *.
                 leibniz &mx3 in |- *.
                 leibniz &mx2 in |- *.
                 leibniz (Comparable.maximum.idempotence (height &r)) in |- *.
                 leibniz (Comparable.maximum.idempotence (++ (height &r))) in |- *.
                 ipso (disjoin (Identity.reflexivity _), _).
              ** match &rel3 with | e3 | e3 end.
                 --- leibniz &e3 in &mx3.
                     leibniz
                       (modus aequans
                         (Comparable.maximum.specification (++ (height &lrr)) (height &lrr)),
                         (disjoin _, (Nat0.increment.order.extensivity (height &lrr))))
                       in &mx3.
                     trans (symm &mx2), (symm &mx3) |- hr.
                     leibniz &e3 in |- *.
                     leibniz (symm &mx3) in |- *.
                     leibniz &hr in |- *.
                     leibniz (Comparable.maximum.idempotence (++ (height &lrr))) in |- *.
                     leibniz
                       (Comparable.maximum.commutativity (height &lrr) (++ (height &lrr)))
                       in |- *.
                     leibniz
                       (modus aequans
                         (Comparable.maximum.specification (++ (height &lrr)) (height &lrr)),
                         (disjoin _, (Nat0.increment.order.extensivity (height &lrr))))
                       in |- *.
                     leibniz (Comparable.maximum.idempotence (++ (++ (height &lrr)))) in |- *.
                     ipso (disjoin (Identity.reflexivity _), _).
                 --- leibniz &e3 in &mx3.
                     leibniz
                       (Comparable.maximum.commutativity (height &lrl) (++ (height &lrl)))
                       in &mx3.
                     leibniz
                       (modus aequans
                         (Comparable.maximum.specification (++ (height &lrl)) (height &lrl)),
                         (disjoin _, (Nat0.increment.order.extensivity (height &lrl))))
                       in &mx3.
                     trans (symm &mx2), (symm &mx3) |- hr.
                     leibniz &e3 in |- *.
                     leibniz (symm &mx3) in |- *.
                     leibniz &hr in |- *.
                     leibniz
                       (modus aequans
                         (Comparable.maximum.specification (++ (height &lrl)) (height &lrl)),
                         (disjoin _, (Nat0.increment.order.extensivity (height &lrl))))
                       in |- *.
                     leibniz (Comparable.maximum.idempotence (++ (height &lrl))) in |- *.
                     leibniz (Comparable.maximum.idempotence (++ (++ (height &lrl)))) in |- *.
                     ipso (disjoin (Identity.reflexivity _), _).
        -- modus aequans
             (Comparable.comparison.equality.reflection (height &lr) (++ (height &ll))), &e
             |- t'.
           leibniz &t' in &t.
           ex &t quodlibet.
Qed.

End right. (* rotation.right *)

Module left. (* rotation.left *)

(* rotation.left.sequence *)
Lemma sequence
  : forall {A : Type} (l : AVL A) (a : A) (r : AVL A) .
      BinaryTree.to_list (to_tree (rotate.left l a r))
      = BinaryTree.to_list (to_tree (node l a r)).
Proof.
  intros A l a r.
  simpl rotate.left in |- *.
  match &r with | Leaf | Node rl c rr hr end.
  - simpl in |- *.
    quod idem est.
  - match (Nat0.eq (height &rl) (++ (height &rr))) with | | end |- t.
    + match &rl with | Leaf | Node rll d rlr hrl end.
      * simpl in |- *.
        quod idem est.
      * simpl node in |- *.
        simpl in |- *.
        leibniz
          (List.concatenation.associativity
            (BinaryTree.to_list (to_tree &l))
            (List.Cons &a (BinaryTree.to_list (to_tree &rll)))
            (List.Cons &d
              (List.concat
                (BinaryTree.to_list (to_tree &rlr))
                (List.Cons &c (BinaryTree.to_list (to_tree &rr))))))
          in |- *.
        leibniz
          (List.concatenation.associativity
            (BinaryTree.to_list (to_tree &rll))
            (List.Cons &d (BinaryTree.to_list (to_tree &rlr)))
            (List.Cons &c (BinaryTree.to_list (to_tree &rr))))
          in |- *.
        simpl in |- *.
        quod idem est.
    + simpl node in |- *.
      simpl in |- *.
      leibniz
        (List.concatenation.associativity
          (BinaryTree.to_list (to_tree &l))
          (List.Cons &a (BinaryTree.to_list (to_tree &rl)))
          (List.Cons &c (BinaryTree.to_list (to_tree &rr))))
        in |- *.
      simpl in |- *.
      quod idem est.
Qed.

(* rotation.left.membership *)
Theorem membership
  : forall {A : Type} (l : AVL A) (a : A) (r : AVL A) (b : A) .
      BinaryTree.Contains b (to_tree (rotate.left l a r))
      <-> BinaryTree.Contains b (to_tree (node l a r)).
Proof.
  intros A l a r b.
  let proof here := BinaryTree.conversion.membership &b (to_tree (rotate.left &l &a &r)).
  let proof there := BinaryTree.conversion.membership &b (to_tree (node &l &a &r)).
  leibniz (rotation.left.sequence &l &a &r) in &here.
  ipso (Biconditional.transitivity &here (Biconditional.symmetry &there)).
Qed.

(* rotation.left.size *)
Theorem size
  : forall {A : Type} (l : AVL A) (a : A) (r : AVL A) .
      BinaryTree.size (to_tree (rotate.left l a r)) = BinaryTree.size (to_tree (node l a r)).
Proof.
  intros A l a r.
  leibniz
    <- (BinaryTree.conversion.size (to_tree (rotate.left &l &a &r))),
    <- (BinaryTree.conversion.size (to_tree (node &l &a &r)))
    in |- *.
  leibniz (rotation.left.sequence &l &a &r) in |- *.
  quod idem est.
Qed.

(* rotation.left.order *)
Theorem order
  : forall {A : Type} {lt : A -> A -> Prop} .
      (forall (x : A) (y : A) (z : A) . lt x y -> lt y z -> lt x z) ->
      forall (l : AVL A) (a : A) (r : AVL A) .
        Ordered lt (node l a r) -> Ordered lt (rotate.left l a r).
Proof.
  intros A lt tr l a r o.
  simpl Ordered, node in &o.
  simpl Ordered, rotate.left in |- *.
  let proof o0 := simpl &o.
  match &o0 with | below o1 end.
  match &o1 with | above o2 end.
  match &o2 with | ordl ordr end.
  match &r with | Leaf | Node rl c rr hr end.
  - ipso &o.
  - simpl in &above.
    match &above with | arl a1 end.
    match &a1 with | ac arr end.
    simpl in &ordr.
    match &ordr with | crl c1 end.
    match &c1 with | crr c2 end.
    match &c2 with | orl orr end.
    match (Nat0.eq (height &rl) (++ (height &rr))) with | | end |- t.
    + match &rl with | Leaf | Node rll d rlr hrl end.
      * ipso &o.
      * simpl in &arl.
        match &arl with | arll a2 end.
        match &a2 with | ad arlr end.
        simpl in &crl.
        match &crl with | crll c3 end.
        match &c3 with | dc crlr end.
        simpl in &orl.
        match &orl with | drll d1 end.
        match &d1 with | drlr d2 end.
        match &d2 with | orll orlr end.
        let proof dl
          := BinaryTree.quantification.all.monotonicity
               (fun (x : &A) (h : &lt x &a) . &tr x &a &d h &ad) &below.
        let proof drr
          := BinaryTree.quantification.all.monotonicity
               (fun (x : &A) (h : &lt &c x) . &tr &d &c x &dc h) &crr.
        simpl node in |- *.
        simpl in |- *.
        ipso
          (conjoin (conjoin &dl, (conjoin &ad, &drll)),
            (conjoin (conjoin &drlr, (conjoin &dc, &drr)),
              (conjoin (conjoin &below, (conjoin &arll, (conjoin &ordl, &orll))),
                (conjoin &crlr, (conjoin &crr, (conjoin &orlr, &orr)))))).
    + let proof cl
        := BinaryTree.quantification.all.monotonicity
             (fun (x : &A) (h : &lt x &a) . &tr x &a &c h &ac) &below.
      simpl node in |- *.
      simpl in |- *.
      ipso
        (conjoin (conjoin &cl, (conjoin &ac, &crl)),
          (conjoin &crr,
            (conjoin (conjoin &below, (conjoin &arl, (conjoin &ordl, &orl))), &orr))).
Qed.

(* rotation.left.measurement *)
Theorem measurement
  : forall {A : Type} (l : AVL A) (a : A) (r : AVL A) .
      Measured l -> Measured r -> Measured (rotate.left l a r).
Proof.
  intros A l a r ml mr.
  simpl rotate.left in |- *.
  match &r with | Leaf | Node rl b rr hr end.
  - ipso (construction.measurement _ _ _ &ml &mr).
  - let proof mr0 := simpl &mr.
    match &mr0 with | _ mr' end.
    match &mr' with | mrl mrr end.
    match (Nat0.eq (height &rl) (++ (height &rr))) with | | end |- t.
    + match &rl with | Leaf | Node rll c rlr hrl end.
      * ipso (construction.measurement _ _ _ &ml &mr).
      * let proof mrl0 := simpl &mrl.
        match &mrl0 with | _ mrl' end.
        match &mrl' with | mrll mrlr end.
        ipso
          (construction.measurement _ _ _
            (construction.measurement _ _ _ &ml &mrll)
            (construction.measurement _ _ _ &mrlr &mrr)).
    + ipso (construction.measurement _ _ _ (construction.measurement _ _ _ &ml &mrl) &mrr).
Qed.

(* rotation.left.balance *)
Theorem balance
  : forall {A : Type} (l : AVL A) (a : A) (r : AVL A) .
      Measured r -> Balanced l -> Balanced r ->
      height r = ++ (++ (height l)) -> Balanced (rotate.left l a r).
Proof.
  intros A l a r mr bl br h.
  match &r with | Leaf | Node rl b rr hr end.
  - simpl in &h.
    ex (Nat0.order.strict.distinction (Nat0.increment.order.positivity _) &h) quodlibet.
  - let proof mr0 := simpl &mr.
    match &mr0 with | hm mr' end.
    match &mr' with | mrl mrr end.
    let proof br0 := simpl &br.
    match &br0 with | rel br' end.
    match &br' with | brl brr end.
    simpl in &h.
    leibniz &hm in &h.
    let proof mx := Nat0.increment.injectivity &h.
    simpl rotate.left in |- *.
    match &rel with | e | rel' end.
    (* The subtrees of [r] are equally high: a single rotation. *)
    + leibniz &e in &mx.
      leibniz (Comparable.maximum.idempotence (height &rr)) in &mx.
      match (Nat0.eq (height &rl) (++ (height &rr))) with | | end |- t.
      * modus aequans
          (Comparable.comparison.equality.reflection (height &rl) (++ (height &rr))), &t
          |- e'.
        leibniz &e in &e'.
        ex (Nat0.order.strict.distinction (Nat0.increment.order.extensivity _) &e') quodlibet.
      * simpl node in |- *.
        simpl in |- *.
        leibniz &e in |- *.
        leibniz &mx in |- *.
        leibniz (Comparable.maximum.commutativity (height &l) (++ (height &l))) in |- *.
        leibniz
          (modus aequans
            (Comparable.maximum.specification (++ (height &l)) (height &l)),
            (disjoin _, (Nat0.increment.order.extensivity (height &l))))
          in |- *.
        ipso
          (conjoin (disjoin _, (disjoin (Identity.reflexivity _), _)),
            (conjoin
              (conjoin (disjoin _, (disjoin _, (Identity.reflexivity _))), (conjoin &bl, &brl)),
              &brr)).
    + match &rel' with | e | e end.
      (* The left subtree of [r] is the higher: a double rotation. *)
      * leibniz &e in &mx.
        leibniz
          (modus aequans
            (Comparable.maximum.specification (++ (height &rr)) (height &rr)),
            (disjoin _, (Nat0.increment.order.extensivity (height &rr))))
          in &mx.
        let proof mx2 := Nat0.increment.injectivity &mx.
        match (Nat0.eq (height &rl) (++ (height &rr))) with | | end |- t.
        -- match &rl with | Leaf | Node rll c rlr hrl end.
           ++ simpl in &e.
              ex (Nat0.order.strict.distinction (Nat0.increment.order.positivity _) &e) quodlibet.
           ++ let proof mrl0 := simpl &mrl.
              match &mrl0 with | hm2 mrl' end.
              match &mrl' with | mrll mrlr end.
              let proof brl0 := simpl &brl.
              match &brl0 with | rel2 brl' end.
              match &brl' with | brll brlr end.
              simpl in &e.
              leibniz &hm2 in &e.
              let proof mx3 := Nat0.increment.injectivity &e.
              simpl node in |- *.
              simpl in |- *.
              match &rel2 with | e3 | rel3 end.
              ** leibniz <- &e3 in &mx3.
                 leibniz (Comparable.maximum.idempotence (height &rll)) in &mx3.
                 leibniz <- &e3 in |- *.
                 leibniz &mx3 in |- *.
                 leibniz &mx2 in |- *.
                 leibniz (Comparable.maximum.idempotence (height &l)) in |- *.
                 ipso
                   (conjoin (disjoin (Identity.reflexivity _), _),
                     (conjoin
                       (conjoin (disjoin (Identity.reflexivity _), _), (conjoin &bl, &brll)),
                       (conjoin (disjoin (Identity.reflexivity _), _), (conjoin &brlr, &brr)))).
              ** match &rel3 with | e3 | e3 end.
                 --- leibniz &e3 in &mx3.
                     leibniz
                       (modus aequans
                         (Comparable.maximum.specification (++ (height &rlr)) (height &rlr)),
                         (disjoin _, (Nat0.increment.order.extensivity (height &rlr))))
                       in &mx3.
                     trans (symm &mx2), (symm &mx3) |- hx.
                     leibniz &e3 in |- *.
                     leibniz (symm &mx3) in |- *.
                     leibniz &hx in |- *.
                     leibniz (Comparable.maximum.idempotence (++ (height &rlr))) in |- *.
                     leibniz
                       (Comparable.maximum.commutativity (height &rlr) (++ (height &rlr)))
                       in |- *.
                     leibniz
                       (modus aequans
                         (Comparable.maximum.specification (++ (height &rlr)) (height &rlr)),
                         (disjoin _, (Nat0.increment.order.extensivity (height &rlr))))
                       in |- *.
                     ipso
                       (conjoin (disjoin (Identity.reflexivity _), _),
                         (conjoin
                           (conjoin (disjoin (Identity.reflexivity _), _), (conjoin &bl, &brll)),
                           (conjoin (disjoin _, (disjoin _, (Identity.reflexivity _))),
                             (conjoin &brlr, &brr)))).
                 --- leibniz &e3 in &mx3.
                     leibniz
                       (Comparable.maximum.commutativity (height &rll) (++ (height &rll)))
                       in &mx3.
                     leibniz
                       (modus aequans
                         (Comparable.maximum.specification (++ (height &rll)) (height &rll)),
                         (disjoin _, (Nat0.increment.order.extensivity (height &rll))))
                       in &mx3.
                     trans (symm &mx2), (symm &mx3) |- hx.
                     leibniz &e3 in |- *.
                     leibniz (symm &mx3) in |- *.
                     leibniz &hx in |- *.
                     leibniz
                       (modus aequans
                         (Comparable.maximum.specification (++ (height &rll)) (height &rll)),
                         (disjoin _, (Nat0.increment.order.extensivity (height &rll))))
                       in |- *.
                     leibniz (Comparable.maximum.idempotence (++ (height &rll))) in |- *.
                     ipso
                       (conjoin (disjoin (Identity.reflexivity _), _),
                         (conjoin
                           (conjoin (disjoin _, (disjoin (Identity.reflexivity _), _)),
                             (conjoin &bl, &brll)),
                           (conjoin (disjoin (Identity.reflexivity _), _), (conjoin &brlr, &brr)))).
        -- modus aequans
             (Comparable.comparison.equality.reflection (height &rl) (++ (height &rr))), &e
             |- t'.
           leibniz &t' in &t.
           ex &t quodlibet.
      (* The right subtree of [r] is the higher: a single rotation. *)
      * leibniz &e in &mx.
        leibniz (Comparable.maximum.commutativity (height &rl) (++ (height &rl))) in &mx.
        leibniz
          (modus aequans
            (Comparable.maximum.specification (++ (height &rl)) (height &rl)),
            (disjoin _, (Nat0.increment.order.extensivity (height &rl))))
          in &mx.
        let proof mx2 := Nat0.increment.injectivity &mx.
        match (Nat0.eq (height &rl) (++ (height &rr))) with | | end |- t.
        -- modus aequans
             (Comparable.comparison.equality.reflection (height &rl) (++ (height &rr))), &t
             |- e'.
           leibniz &e in &e'.
           ex
             (Nat0.order.strict.distinction
               (Nat0.order.strict.transitivity
                 (Nat0.increment.order.extensivity _) (Nat0.increment.order.extensivity _))
               &e')
             quodlibet.
        -- simpl node in |- *.
           simpl in |- *.
           leibniz &e in |- *.
           leibniz &mx2 in |- *.
           leibniz (Comparable.maximum.idempotence (height &l)) in |- *.
           ipso
             (conjoin (disjoin (Identity.reflexivity _), _),
               (conjoin
                 (conjoin (disjoin (Identity.reflexivity _), _), (conjoin &bl, &brl)),
                 &brr)).
Qed.

(* rotation.left.growth *)
Theorem growth
  : forall {A : Type} (l : AVL A) (a : A) (r : AVL A) .
      Measured r -> Balanced r -> height r = ++ (++ (height l)) ->
      height (rotate.left l a r) = height r \/ height (rotate.left l a r) = ++ (height r).
Proof.
  intros A l a r mr br h.
  match &r with | Leaf | Node rl b rr hr end.
  - simpl in &h.
    ex (Nat0.order.strict.distinction (Nat0.increment.order.positivity _) &h) quodlibet.
  - let proof mr0 := simpl &mr.
    match &mr0 with | hm mr' end.
    match &mr' with | mrl mrr end.
    let proof br0 := simpl &br.
    match &br0 with | rel br' end.
    match &br' with | brl brr end.
    simpl in &h.
    leibniz &hm in &h.
    let proof mx := Nat0.increment.injectivity &h.
    simpl rotate.left in |- *.
    match &rel with | e | rel' end.
    + leibniz &e in &mx.
      leibniz (Comparable.maximum.idempotence (height &rr)) in &mx.
      match (Nat0.eq (height &rl) (++ (height &rr))) with | | end |- t.
      * modus aequans
          (Comparable.comparison.equality.reflection (height &rl) (++ (height &rr))), &t
          |- e'.
        leibniz &e in &e'.
        ex (Nat0.order.strict.distinction (Nat0.increment.order.extensivity _) &e') quodlibet.
      * simpl node in |- *.
        leibniz &hm in |- *.
        simpl in |- *.
        leibniz &e in |- *.
        leibniz &mx in |- *.
        leibniz (Comparable.maximum.commutativity (height &l) (++ (height &l))) in |- *.
        leibniz
          (modus aequans
            (Comparable.maximum.specification (++ (height &l)) (height &l)),
            (disjoin _, (Nat0.increment.order.extensivity (height &l))))
          in |- *.
        leibniz (Comparable.maximum.idempotence (++ (height &l))) in |- *.
        leibniz
          (modus aequans
            (Comparable.maximum.specification (++ (++ (height &l))) (++ (height &l))),
            (disjoin _, (Nat0.increment.order.extensivity (++ (height &l)))))
          in |- *.
        ipso (disjoin _, (Identity.reflexivity _)).
    + match &rel' with | e | e end.
      * leibniz &e in &mx.
        leibniz
          (modus aequans
            (Comparable.maximum.specification (++ (height &rr)) (height &rr)),
            (disjoin _, (Nat0.increment.order.extensivity (height &rr))))
          in &mx.
        let proof mx2 := Nat0.increment.injectivity &mx.
        match (Nat0.eq (height &rl) (++ (height &rr))) with | | end |- t.
        -- match &rl with | Leaf | Node rll c rlr hrl end.
           ++ simpl in &e.
              ex (Nat0.order.strict.distinction (Nat0.increment.order.positivity _) &e) quodlibet.
           ++ let proof mrl0 := simpl &mrl.
              match &mrl0 with | hm2 mrl' end.
              let proof brl0 := simpl &brl.
              match &brl0 with | rel2 brl' end.
              simpl in &e.
              simpl node in |- *.
              leibniz &hm in |- *.
              simpl in |- *.
              leibniz &e in |- *.
              leibniz
                (modus aequans
                  (Comparable.maximum.specification (++ (height &rr)) (height &rr)),
                  (disjoin _, (Nat0.increment.order.extensivity (height &rr))))
                in |- *.
              leibniz &hm2 in &e.
              let proof mx3 := Nat0.increment.injectivity &e.
              match &rel2 with | e3 | rel3 end.
              ** leibniz <- &e3 in &mx3.
                 leibniz (Comparable.maximum.idempotence (height &rll)) in &mx3.
                 leibniz <- &e3 in |- *.
                 leibniz &mx3 in |- *.
                 leibniz &mx2 in |- *.
                 leibniz (Comparable.maximum.idempotence (height &l)) in |- *.
                 leibniz (Comparable.maximum.idempotence (++ (height &l))) in |- *.
                 ipso (disjoin (Identity.reflexivity _), _).
              ** match &rel3 with | e3 | e3 end.
                 --- leibniz &e3 in &mx3.
                     leibniz
                       (modus aequans
                         (Comparable.maximum.specification (++ (height &rlr)) (height &rlr)),
                         (disjoin _, (Nat0.increment.order.extensivity (height &rlr))))
                       in &mx3.
                     trans (symm &mx2), (symm &mx3) |- hx.
                     leibniz &e3 in |- *.
                     leibniz (symm &mx3) in |- *.
                     leibniz &hx in |- *.
                     leibniz (Comparable.maximum.idempotence (++ (height &rlr))) in |- *.
                     leibniz
                       (Comparable.maximum.commutativity (height &rlr) (++ (height &rlr)))
                       in |- *.
                     leibniz
                       (modus aequans
                         (Comparable.maximum.specification (++ (height &rlr)) (height &rlr)),
                         (disjoin _, (Nat0.increment.order.extensivity (height &rlr))))
                       in |- *.
                     leibniz (Comparable.maximum.idempotence (++ (++ (height &rlr)))) in |- *.
                     ipso (disjoin (Identity.reflexivity _), _).
                 --- leibniz &e3 in &mx3.
                     leibniz
                       (Comparable.maximum.commutativity (height &rll) (++ (height &rll)))
                       in &mx3.
                     leibniz
                       (modus aequans
                         (Comparable.maximum.specification (++ (height &rll)) (height &rll)),
                         (disjoin _, (Nat0.increment.order.extensivity (height &rll))))
                       in &mx3.
                     trans (symm &mx2), (symm &mx3) |- hx.
                     leibniz &e3 in |- *.
                     leibniz (symm &mx3) in |- *.
                     leibniz &hx in |- *.
                     leibniz
                       (modus aequans
                         (Comparable.maximum.specification (++ (height &rll)) (height &rll)),
                         (disjoin _, (Nat0.increment.order.extensivity (height &rll))))
                       in |- *.
                     leibniz (Comparable.maximum.idempotence (++ (height &rll))) in |- *.
                     leibniz (Comparable.maximum.idempotence (++ (++ (height &rll)))) in |- *.
                     ipso (disjoin (Identity.reflexivity _), _).
        -- modus aequans
             (Comparable.comparison.equality.reflection (height &rl) (++ (height &rr))), &e
             |- t'.
           leibniz &t' in &t.
           ex &t quodlibet.
      * leibniz &e in &mx.
        leibniz (Comparable.maximum.commutativity (height &rl) (++ (height &rl))) in &mx.
        leibniz
          (modus aequans
            (Comparable.maximum.specification (++ (height &rl)) (height &rl)),
            (disjoin _, (Nat0.increment.order.extensivity (height &rl))))
          in &mx.
        let proof mx2 := Nat0.increment.injectivity &mx.
        match (Nat0.eq (height &rl) (++ (height &rr))) with | | end |- t.
        -- modus aequans
             (Comparable.comparison.equality.reflection (height &rl) (++ (height &rr))), &t
             |- e'.
           leibniz &e in &e'.
           ex
             (Nat0.order.strict.distinction
               (Nat0.order.strict.transitivity
                 (Nat0.increment.order.extensivity _) (Nat0.increment.order.extensivity _))
               &e')
             quodlibet.
        -- simpl node in |- *.
           leibniz &hm in |- *.
           simpl in |- *.
           leibniz &e in |- *.
           leibniz &mx2 in |- *.
           leibniz (Comparable.maximum.idempotence (height &l)) in |- *.
           leibniz (Comparable.maximum.idempotence (++ (height &l))) in |- *.
           leibniz (Comparable.maximum.commutativity (height &l) (++ (height &l))) in |- *.
           leibniz
             (modus aequans
               (Comparable.maximum.specification (++ (height &l)) (height &l)),
               (disjoin _, (Nat0.increment.order.extensivity (height &l))))
             in |- *.
           ipso (disjoin (Identity.reflexivity _), _).
Qed.

End left. (* rotation.left *)

End rotation. (* rotation *)

Module balancing. (* balancing *)

(* balancing.measurement *)
Theorem measurement
  : forall {A : Type} (l : AVL A) (a : A) (r : AVL A) .
      Measured l -> Measured r -> Measured (balance l a r).
Proof.
  intros A l a r ml mr.
  simpl balance in |- *.
  match (Nat0.eq (height &l) (++ (++ (height &r)))) with | | end |- t1.
  - ipso (rotation.right.measurement &l &a &r &ml &mr).
  - match (Nat0.eq (height &r) (++ (++ (height &l)))) with | | end |- t2.
    + ipso (rotation.left.measurement &l &a &r &ml &mr).
    + ipso (construction.measurement &l &a &r &ml &mr).
Qed.

(* The heights of [l] and [r] may be up to two apart, as they are just
 * after one of them grew or shrank by one.
 *)
(* balancing.balance *)
Theorem balance
  : forall {A : Type} (l : AVL A) (a : A) (r : AVL A) .
      Measured l -> Measured r -> Balanced l -> Balanced r ->
      height l = height r
        \/ height l = ++ (height r)
        \/ height r = ++ (height l)
        \/ height l = ++ (++ (height r))
        \/ height r = ++ (++ (height l)) ->
      Balanced (balance l a r).
Proof.
  intros A l a r ml mr bl br near.
  simpl balance in |- *.
  match (Nat0.eq (height &l) (++ (++ (height &r)))) with | | end |- t1.
  - modus aequans
      (Comparable.comparison.equality.reflection (height &l) (++ (++ (height &r)))), &t1
      |- e.
    ipso (rotation.right.balance &l &a &r &ml &bl &br &e).
  - match (Nat0.eq (height &r) (++ (++ (height &l)))) with | | end |- t2.
    + modus aequans
        (Comparable.comparison.equality.reflection (height &r) (++ (++ (height &l)))), &t2
        |- e.
      ipso (rotation.left.balance &l &a &r &mr &bl &br &e).
    + lemma rel
      : height &l = height &r \/ height &l = ++ (height &r) \/ height &r = ++ (height &l).
      {
        match &near with | e | n1 end.
        - ipso (disjoin &e, _).
        - match &n1 with | e | n2 end.
          + ipso (disjoin _, (disjoin &e, _)).
          + match &n2 with | e | n3 end.
            * ipso (disjoin _, (disjoin _, &e)).
            * match &n3 with | e | e end.
              -- modus aequans
                   (Comparable.comparison.equality.reflection
                     (height &l) (++ (++ (height &r)))),
                   &e
                   |- t.
                 leibniz &t in &t1.
                 ex &t1 quodlibet.
              -- modus aequans
                   (Comparable.comparison.equality.reflection
                     (height &r) (++ (++ (height &l)))),
                   &e
                   |- t.
                 leibniz &t in &t2.
                 ex &t2 quodlibet.
      }
      simpl node in |- *.
      simpl in |- *.
      ipso (conjoin &rel, (conjoin &bl, &br)).
Qed.

(* balancing.membership *)
Theorem membership
  : forall {A : Type} (l : AVL A) (a : A) (r : AVL A) (b : A) .
      BinaryTree.Contains b (to_tree (AVL.balance l a r))
      <-> BinaryTree.Contains b (to_tree (node l a r)).
Proof.
  intros A l a r b.
  simpl AVL.balance in |- *.
  match (Nat0.eq (height &l) (++ (++ (height &r)))) with | | end |- t1.
  - ipso (rotation.right.membership &l &a &r &b).
  - match (Nat0.eq (height &r) (++ (++ (height &l)))) with | | end |- t2.
    + ipso (rotation.left.membership &l &a &r &b).
    + ipso (Biconditional.reflexivity _).
Qed.

(* balancing.order *)
Theorem order
  : forall {A : Type} {lt : A -> A -> Prop} .
      (forall (x : A) (y : A) (z : A) . lt x y -> lt y z -> lt x z) ->
      forall (l : AVL A) (a : A) (r : AVL A) .
        Ordered lt (node l a r) -> Ordered lt (AVL.balance l a r).
Proof.
  intros A lt tr l a r o.
  simpl AVL.balance in |- *.
  match (Nat0.eq (height &l) (++ (++ (height &r)))) with | | end |- t1.
  - ipso (rotation.right.order &tr &l &a &r &o).
  - match (Nat0.eq (height &r) (++ (++ (height &l)))) with | | end |- t2.
    + ipso (rotation.left.order &tr &l &a &r &o).
    + ipso &o.
Qed.

(* balancing.size *)
Theorem size
  : forall {A : Type} (l : AVL A) (a : A) (r : AVL A) .
      BinaryTree.size (to_tree (AVL.balance l a r)) = BinaryTree.size (to_tree (node l a r)).
Proof.
  intros A l a r.
  simpl AVL.balance in |- *.
  match (Nat0.eq (height &l) (++ (++ (height &r)))) with | | end |- t1.
  - ipso (rotation.right.size &l &a &r).
  - match (Nat0.eq (height &r) (++ (++ (height &l)))) with | | end |- t2.
    + ipso (rotation.left.size &l &a &r).
    + quod idem est.
Qed.

Module shrinkage. (* balancing.shrinkage *)

(* [h] is the height the left subtree had before it lost one level or none,
 * and [l] is what it became: the result is as high as a node over the old
 * subtree and [r], or one lower.
 *)
(* balancing.shrinkage.left *)
Lemma left
  : forall {A : Type} (l : AVL A) (a : A) (r : AVL A) (h : Nat0) .
      Measured r -> Balanced r ->
      h = height r \/ h = ++ (height r) \/ height r = ++ h ->
      height l = h \/ ++ (height l) = h ->
      height (AVL.balance l a r) = ++ (Nat0.max h (height r))
      \/ ++ (height (AVL.balance l a r)) = ++ (Nat0.max h (height r)).
Proof.
  intros A l a r h mr br rel g.
  simpl AVL.balance in |- *.
  match (Nat0.eq (height &l) (++ (++ (height &r)))) with | | end |- t1.
  - modus aequans
      (Comparable.comparison.equality.reflection (height &l) (++ (++ (height &r)))), &t1
      |- e1.
    match &rel with | q | rel' end.
    + match &g with | k | k end.
      * leibniz &k, &q in &e1.
        ex
          (Nat0.order.strict.distinction
            (Nat0.order.strict.transitivity
              (Nat0.increment.order.extensivity _) (Nat0.increment.order.extensivity _))
            &e1)
          quodlibet.
      * trans (symm &q), (symm &k) |- rx.
        leibniz &rx in &e1.
        ex
          (Nat0.order.strict.distinction
            (Nat0.order.strict.transitivity
              (Nat0.increment.order.extensivity _)
              (Nat0.order.strict.transitivity
                (Nat0.increment.order.extensivity _) (Nat0.increment.order.extensivity _)))
            &e1)
          quodlibet.
    + match &rel' with | q | q end.
      * match &g with | k | k end.
        -- leibniz &k, &q in &e1.
           let proof e1' := Nat0.increment.injectivity &e1.
           ex (Nat0.order.strict.distinction (Nat0.increment.order.extensivity _) &e1') quodlibet.
        -- let proof xr := Nat0.increment.injectivity (trans &k, &q).
           leibniz &xr in &e1.
           ex
             (Nat0.order.strict.distinction
               (Nat0.order.strict.transitivity
                 (Nat0.increment.order.extensivity _) (Nat0.increment.order.extensivity _))
               &e1)
             quodlibet.
      * match &g with | k | k end.
        -- leibniz &k, &q in &e1.
           ex
             (Nat0.order.strict.distinction
               (Nat0.order.strict.transitivity
                 (Nat0.increment.order.extensivity _)
                 (Nat0.order.strict.transitivity
                   (Nat0.increment.order.extensivity _) (Nat0.increment.order.extensivity _)))
               &e1)
             quodlibet.
        -- leibniz (symm &k) in &q.
           leibniz &q in &e1.
           ex
             (Nat0.order.strict.distinction
               (Nat0.order.strict.transitivity
                 (Nat0.increment.order.extensivity _)
                 (Nat0.order.strict.transitivity
                   (Nat0.increment.order.extensivity _)
                   (Nat0.order.strict.transitivity
                     (Nat0.increment.order.extensivity _) (Nat0.increment.order.extensivity _))))
               &e1)
             quodlibet.
  - match (Nat0.eq (height &r) (++ (++ (height &l)))) with | | end |- t2.
    + modus aequans
        (Comparable.comparison.equality.reflection (height &r) (++ (++ (height &l)))), &t2
        |- e2.
      match &rel with | q | rel' end.
      * match &g with | k | k end.
        -- leibniz &k, &q in &e2.
           ex
             (Nat0.order.strict.distinction
               (Nat0.order.strict.transitivity
                 (Nat0.increment.order.extensivity _) (Nat0.increment.order.extensivity _))
               &e2)
             quodlibet.
        -- trans (symm &q), (symm &k) |- rx.
           leibniz &rx in &e2.
           let proof e2' := Nat0.increment.injectivity &e2.
           ex (Nat0.order.strict.distinction (Nat0.increment.order.extensivity _) &e2') quodlibet.
      * match &rel' with | q | q end.
        -- match &g with | k | k end.
           ++ leibniz &k, &q in &e2.
              ex
                (Nat0.order.strict.distinction
                  (Nat0.order.strict.transitivity
                    (Nat0.increment.order.extensivity _)
                    (Nat0.order.strict.transitivity
                      (Nat0.increment.order.extensivity _) (Nat0.increment.order.extensivity _)))
                  &e2)
                quodlibet.
           ++ let proof xr := Nat0.increment.injectivity (trans &k, &q).
              leibniz &xr in &e2.
              ex
                (Nat0.order.strict.distinction
                  (Nat0.order.strict.transitivity
                    (Nat0.increment.order.extensivity _) (Nat0.increment.order.extensivity _))
                  &e2)
                quodlibet.
        -- match &g with | k | k end.
           ++ leibniz &k, &q in &e2.
              let proof e2' := Nat0.increment.injectivity &e2.
              ex
                (Nat0.order.strict.distinction (Nat0.increment.order.extensivity _) &e2')
                quodlibet.
           (* The right subtree is now two above the left: a rotation. *)
           ++ let proof gr := rotation.left.growth &l &a &r &mr &br &e2.
              leibniz &q in |- *.
              leibniz (Comparable.maximum.commutativity &h (++ &h)) in |- *.
              leibniz
                (modus aequans
                  (Comparable.maximum.specification (++ &h) &h),
                  (disjoin _, (Nat0.increment.order.extensivity &h)))
                in |- *.
              leibniz &q in &gr.
              match &gr with | u | u end.
              ** ipso (disjoin _, (congru Nat0.inc, &u)).
              ** ipso (disjoin &u, _).
    + simpl node in |- *.
      simpl in |- *.
      match &rel with | q | rel' end.
      * match &g with | k | k end.
        -- leibniz &k in |- *.
           ipso (disjoin (Identity.reflexivity _), _).
        -- trans (symm &q), (symm &k) |- rx.
           leibniz &q in |- *.
           leibniz &rx in |- *.
           leibniz (Comparable.maximum.commutativity (height &l) (++ (height &l))) in |- *.
           leibniz
             (modus aequans
               (Comparable.maximum.specification (++ (height &l)) (height &l)),
               (disjoin _, (Nat0.increment.order.extensivity (height &l))))
             in |- *.
           leibniz (Comparable.maximum.idempotence (++ (height &l))) in |- *.
           ipso (disjoin (Identity.reflexivity _), _).
      * match &rel' with | q | q end.
        -- match &g with | k | k end.
           ++ leibniz &k in |- *.
              ipso (disjoin (Identity.reflexivity _), _).
           ++ let proof xr := Nat0.increment.injectivity (trans &k, &q).
              leibniz &xr, &q in |- *.
              leibniz (Comparable.maximum.idempotence (height &r)) in |- *.
              leibniz
                (modus aequans
                  (Comparable.maximum.specification (++ (height &r)) (height &r)),
                  (disjoin _, (Nat0.increment.order.extensivity (height &r))))
                in |- *.
              ipso (disjoin _, (Identity.reflexivity _)).
        -- match &g with | k | k end.
           ++ leibniz &k in |- *.
              ipso (disjoin (Identity.reflexivity _), _).
           ++ leibniz (symm &k) in &q.
              modus aequans
                (Comparable.comparison.equality.reflection (height &r) (++ (++ (height &l)))),
                &q
                |- t.
              leibniz &t in &t2.
              ex &t2 quodlibet.
Qed.

(* The mirror of [balancing.shrinkage.left], for the right subtree. *)
(* balancing.shrinkage.right *)
Lemma right
  : forall {A : Type} (l : AVL A) (a : A) (r : AVL A) (h : Nat0) .
      Measured l -> Balanced l ->
      height l = h \/ height l = ++ h \/ h = ++ (height l) ->
      height r = h \/ ++ (height r) = h ->
      height (AVL.balance l a r) = ++ (Nat0.max (height l) h)
      \/ ++ (height (AVL.balance l a r)) = ++ (Nat0.max (height l) h).
Proof.
  intros A l a r h ml bl rel g.
  simpl AVL.balance in |- *.
  match (Nat0.eq (height &l) (++ (++ (height &r)))) with | | end |- t1.
  - modus aequans
      (Comparable.comparison.equality.reflection (height &l) (++ (++ (height &r)))), &t1
      |- e1.
    match &rel with | q | rel' end.
    + match &g with | k | k end.
      * leibniz &k in &e1.
        leibniz <- &q in &e1.
        ex
          (Nat0.order.strict.distinction
            (Nat0.order.strict.transitivity
              (Nat0.increment.order.extensivity _) (Nat0.increment.order.extensivity _))
            &e1)
          quodlibet.
      * trans &q, (symm &k) |- ly.
        leibniz &ly in &e1.
        let proof e1' := Nat0.increment.injectivity &e1.
        ex (Nat0.order.strict.distinction (Nat0.increment.order.extensivity _) &e1') quodlibet.
    + match &rel' with | q | q end.
      * match &g with | k | k end.
        -- leibniz &k, &q in &e1.
           let proof e1' := Nat0.increment.injectivity &e1.
           ex (Nat0.order.strict.distinction (Nat0.increment.order.extensivity _) &e1') quodlibet.
        (* The left subtree is now two above the right: a rotation. *)
        -- let proof gr := rotation.right.growth &l &a &r &ml &bl &e1.
           leibniz &q in |- *.
           leibniz
             (modus aequans
               (Comparable.maximum.specification (++ &h) &h),
               (disjoin _, (Nat0.increment.order.extensivity &h)))
             in |- *.
           leibniz &q in &gr.
           match &gr with | u | u end.
           ++ ipso (disjoin _, (congru Nat0.inc, &u)).
           ++ ipso (disjoin &u, _).
      * match &g with | k | k end.
        -- leibniz &k, &q in &e1.
           ex
             (Nat0.order.strict.distinction
               (Nat0.order.strict.transitivity
                 (Nat0.increment.order.extensivity _)
                 (Nat0.order.strict.transitivity
                   (Nat0.increment.order.extensivity _) (Nat0.increment.order.extensivity _)))
               &e1)
             quodlibet.
        -- let proof yl := Nat0.increment.injectivity (trans &k, &q).
           leibniz &yl in &e1.
           ex
             (Nat0.order.strict.distinction
               (Nat0.order.strict.transitivity
                 (Nat0.increment.order.extensivity _) (Nat0.increment.order.extensivity _))
               &e1)
             quodlibet.
  - match (Nat0.eq (height &r) (++ (++ (height &l)))) with | | end |- t2.
    + modus aequans
        (Comparable.comparison.equality.reflection (height &r) (++ (++ (height &l)))), &t2
        |- e2.
      match &rel with | q | rel' end.
      * match &g with | k | k end.
        -- leibniz &k in &e2.
           leibniz <- &q in &e2.
           ex
             (Nat0.order.strict.distinction
               (Nat0.order.strict.transitivity
                 (Nat0.increment.order.extensivity _) (Nat0.increment.order.extensivity _))
               &e2)
             quodlibet.
        -- trans &q, (symm &k) |- ly.
           leibniz &ly in &e2.
           ex
             (Nat0.order.strict.distinction
               (Nat0.order.strict.transitivity
                 (Nat0.increment.order.extensivity _)
                 (Nat0.order.strict.transitivity
                   (Nat0.increment.order.extensivity _) (Nat0.increment.order.extensivity _)))
               &e2)
             quodlibet.
      * match &rel' with | q | q end.
        -- match &g with | k | k end.
           ++ leibniz &k, &q in &e2.
              ex
                (Nat0.order.strict.distinction
                  (Nat0.order.strict.transitivity
                    (Nat0.increment.order.extensivity _)
                    (Nat0.order.strict.transitivity
                      (Nat0.increment.order.extensivity _) (Nat0.increment.order.extensivity _)))
                  &e2)
                quodlibet.
           ++ leibniz (symm &k) in &q.
              modus aequans
                (Comparable.comparison.equality.reflection (height &l) (++ (++ (height &r)))),
                &q
                |- t.
              leibniz &t in &t1.
              ex &t1 quodlibet.
        -- match &g with | k | k end.
           ++ leibniz &k, &q in &e2.
              let proof e2' := Nat0.increment.injectivity &e2.
              ex
                (Nat0.order.strict.distinction (Nat0.increment.order.extensivity _) &e2')
                quodlibet.
           ++ let proof yl := Nat0.increment.injectivity (trans &k, &q).
              leibniz &yl in &e2.
              ex
                (Nat0.order.strict.distinction
                  (Nat0.order.strict.transitivity
                    (Nat0.increment.order.extensivity _) (Nat0.increment.order.extensivity _))
                  &e2)
                quodlibet.
    + simpl node in |- *.
      simpl in |- *.
      match &rel with | q | rel' end.
      * match &g with | k | k end.
        -- leibniz &k in |- *.
           ipso (disjoin (Identity.reflexivity _), _).
        -- trans &q, (symm &k) |- ly.
           leibniz (symm &k) in |- *.
           leibniz &ly in |- *.
           leibniz
             (modus aequans
               (Comparable.maximum.specification (++ (height &r)) (height &r)),
               (disjoin _, (Nat0.increment.order.extensivity (height &r))))
             in |- *.
           leibniz (Comparable.maximum.idempotence (++ (height &r))) in |- *.
           ipso (disjoin (Identity.reflexivity _), _).
      * match &rel' with | q | q end.
        -- match &g with | k | k end.
           ++ leibniz &k in |- *.
              ipso (disjoin (Identity.reflexivity _), _).
           ++ leibniz (symm &k) in &q.
              modus aequans
                (Comparable.comparison.equality.reflection (height &l) (++ (++ (height &r)))),
                &q
                |- t.
              leibniz &t in &t1.
              ex &t1 quodlibet.
        -- match &g with | k | k end.
           ++ leibniz &k in |- *.
              ipso (disjoin (Identity.reflexivity _), _).
           ++ let proof yl := Nat0.increment.injectivity (trans &k, &q).
              leibniz &yl in |- *.
              leibniz &q in |- *.
              leibniz (Comparable.maximum.idempotence (height &l)) in |- *.
              leibniz (Comparable.maximum.commutativity (height &l) (++ (height &l))) in |- *.
              leibniz
                (modus aequans
                  (Comparable.maximum.specification (++ (height &l)) (height &l)),
                  (disjoin _, (Nat0.increment.order.extensivity (height &l))))
                in |- *.
              ipso (disjoin _, (Identity.reflexivity _)).
Qed.

End shrinkage. (* balancing.shrinkage *)

End balancing. (* balancing *)

Module insertion. (* insertion *)

(* This law asks for no ordered tree: [insert] adds [a] and loses nothing
 * on any tree.
 *)
(* insertion.membership *)
Theorem membership
  : forall {A : Type} {cmp : A -> A -> Comparison} {lt : A -> A -> Prop} .
      Comparable cmp lt ->
      forall (a : A) (b : A) (t : AVL A) .
        BinaryTree.Contains b (to_tree (insert cmp a t))
        <-> b = a \/ BinaryTree.Contains b (to_tree t).
Proof.
  intros A cmp lt C a b t.
  match &t with | Leaf | Node (l by IHl) c (r by IHr) n end per AVL.induction.
  - simpl in |- *.
    divide et impera.
    + intro h.
      match &h with | f | h' end.
      * ex &f quodlibet.
      * match &h' with | e | f end.
        -- ipso (disjoin &e, _).
        -- ex &f quodlibet.
    + intro h.
      match &h with | e | f end.
      * ipso (disjoin _, (disjoin &e, _)).
      * ex &f quodlibet.
  - simpl in |- *.
    match (&cmp &a &c) with | | | end |- k.
    + let proof bm := balancing.membership (insert &cmp &a &l) &c &r &b.
      simpl node in &bm.
      simpl in &bm.
      lemma shift
        : (BinaryTree.Contains &b (to_tree (insert &cmp &a &l))
            \/ &b = &c
            \/ BinaryTree.Contains &b (to_tree &r))
          <-> &b = &a
            \/ BinaryTree.Contains &b (to_tree &l)
            \/ &b = &c
            \/ BinaryTree.Contains &b (to_tree &r).
      {
        divide et impera.
        - intro h.
          match &h with | m | rest end.
          + modus aequans &IHl, &m |- found.
            match &found with | e | m' end.
            * ipso (disjoin &e, _).
            * ipso (disjoin _, (disjoin &m', _)).
          + ipso (disjoin _, (disjoin _, &rest)).
        - intro h.
          match &h with | e | h' end.
          + modus aequans &IHl, (disjoin &e, _) |- m.
            ipso (disjoin &m, _).
          + match &h' with | m | rest end.
            * modus aequans &IHl, (disjoin _, &m) |- m'.
              ipso (disjoin &m', _).
            * ipso (disjoin _, &rest).
      }
      ipso (Biconditional.transitivity &bm &shift).
    (* [a] is [c], already in the tree: [b = a] is [b = c]. *)
    + modus aequans (Comparable.comparison.equality.specification &a &c), &k |- ac.
      simpl in |- *.
      divide et impera.
      * intro h.
        ipso (disjoin _, &h).
      * intro h.
        match &h with | e | present end.
        -- trans &e, &ac |- bc.
           ipso (disjoin _, (disjoin &bc, _)).
        -- ipso &present.
    + let proof bm := balancing.membership &l &c (insert &cmp &a &r) &b.
      simpl node in &bm.
      simpl in &bm.
      lemma shift
        : (BinaryTree.Contains &b (to_tree &l)
            \/ &b = &c
            \/ BinaryTree.Contains &b (to_tree (insert &cmp &a &r)))
          <-> &b = &a
            \/ BinaryTree.Contains &b (to_tree &l)
            \/ &b = &c
            \/ BinaryTree.Contains &b (to_tree &r).
      {
        divide et impera.
        - intro h.
          match &h with | m | h' end.
          + ipso (disjoin _, (disjoin &m, _)).
          + match &h' with | e | m end.
            * ipso (disjoin _, (disjoin _, (disjoin &e, _))).
            * modus aequans &IHr, &m |- found.
              match &found with | e | m' end.
              -- ipso (disjoin &e, _).
              -- ipso (disjoin _, (disjoin _, (disjoin _, &m'))).
        - intro h.
          match &h with | e | h1 end.
          + modus aequans &IHr, (disjoin &e, _) |- m.
            ipso (disjoin _, (disjoin _, &m)).
          + match &h1 with | m | h2 end.
            * ipso (disjoin &m, _).
            * match &h2 with | e | m end.
              -- ipso (disjoin _, (disjoin &e, _)).
              -- modus aequans &IHr, (disjoin _, &m) |- m'.
                 ipso (disjoin _, (disjoin _, &m')).
      }
      ipso (Biconditional.transitivity &bm &shift).
Qed.

Module preservation. (* insertion.preservation *)

(* insertion.preservation.measurement *)
Theorem measurement
  : forall {A : Type} (cmp : A -> A -> Comparison) (a : A) (t : AVL A) .
      Measured t -> Measured (insert cmp a t).
Proof.
  intros A cmp a t.
  match &t with | Leaf | Node (l by IHl) b (r by IHr) h end per AVL.induction.
  - intro m.
    ipso (construction.measurement AVL.Leaf &a AVL.Leaf I I).
  - intro m.
    let proof m0 := simpl &m.
    match &m0 with | _ m' end.
    match &m' with | ml mr end.
    simpl in |- *.
    match (&cmp &a &b) with | | | end |- c.
    + modus ponens &IHl, &ml |- ml'.
      ipso (balancing.measurement (insert &cmp &a &l) &b &r &ml' &mr).
    + ipso &m.
    + modus ponens &IHr, &mr |- mr'.
      ipso (balancing.measurement &l &b (insert &cmp &a &r) &ml &mr').
Qed.

(* insertion.preservation.order *)
Theorem order
  : forall {A : Type} {cmp : A -> A -> Comparison} {lt : A -> A -> Prop} .
      Comparable cmp lt ->
      forall (a : A) (t : AVL A) . Ordered lt t -> Ordered lt (insert cmp a t).
Proof.
  intros A cmp lt C a t.
  match &t with | Leaf | Node (l by IHl) b (r by IHr) h end per AVL.induction.
  - intro o.
    simpl Ordered in |- *.
    simpl in |- *.
    ipso (conjoin I, (conjoin I, (conjoin I, I))).
  - intro o.
    simpl Ordered in &o.
    let proof o0 := simpl &o.
    match &o0 with | below o1 end.
    match &o1 with | above o2 end.
    match &o2 with | ordl ordr end.
    simpl Ordered in |- *.
    simpl in |- *.
    match (&cmp &a &b) with | | | end |- c.
    (* [a] goes into the left subtree, and is below [b] as all of it is. *)
    + modus aequans (Comparable.comparison.strict.specification &a &b), &c |- ab.
      modus ponens &IHl, &ordl |- kept.
      lemma each
        : forall (x : &A) . BinaryTree.Contains x (to_tree (insert &cmp &a &l)) -> &lt x &b.
      {
        intros x m.
        modus aequans (insertion.membership &C &a &x &l), &m |- w.
        match &w with | e | m' end.
        - leibniz &e in |- *.
          ipso &ab.
        - modus aequans
            (BinaryTree.quantification.all.specification (fun (y : &A) . &lt y &b) (to_tree &l)),
            &below
            |- under.
          ipso (&under &x &m').
      }
      modus aequans
        (BinaryTree.quantification.all.specification
          (fun (y : &A) . &lt y &b) (to_tree (insert &cmp &a &l))),
        &each
        |- inserted.
      lemma on : Ordered &lt (node (insert &cmp &a &l) &b &r).
      {
        simpl Ordered, node in |- *.
        simpl in |- *.
        ipso (conjoin &inserted, (conjoin &above, (conjoin &kept, &ordr))).
      }
      ipso
        (balancing.order
          (fun (x : &A) (y : &A) (z : &A) . Comparable.transitivity x y z)
          (insert &cmp &a &l) &b &r &on).
    + ipso &o.
    (* [a] goes into the right subtree, and is above [b] as all of it is. *)
    + modus aequans
        (Comparable.comparison.strict.transposition.specification &a &b), &c |- ba.
      modus ponens &IHr, &ordr |- kept.
      lemma each
        : forall (x : &A) . BinaryTree.Contains x (to_tree (insert &cmp &a &r)) -> &lt &b x.
      {
        intros x m.
        modus aequans (insertion.membership &C &a &x &r), &m |- w.
        match &w with | e | m' end.
        - leibniz &e in |- *.
          ipso &ba.
        - modus aequans
            (BinaryTree.quantification.all.specification (fun (y : &A) . &lt &b y) (to_tree &r)),
            &above
            |- over.
          ipso (&over &x &m').
      }
      modus aequans
        (BinaryTree.quantification.all.specification
          (fun (y : &A) . &lt &b y) (to_tree (insert &cmp &a &r))),
        &each
        |- inserted.
      lemma on : Ordered &lt (node &l &b (insert &cmp &a &r)).
      {
        simpl Ordered, node in |- *.
        simpl in |- *.
        ipso (conjoin &below, (conjoin &inserted, (conjoin &ordl, &kept))).
      }
      ipso
        (balancing.order
          (fun (x : &A) (y : &A) (z : &A) . Comparable.transitivity x y z)
          &l &b (insert &cmp &a &r) &on).
Qed.

(* The balance of [insert cmp a t] and its height are proved by one
 * induction: [balance] needs the subtree it receives to be at most two
 * apart from its sibling, which is what the height bound says, and the
 * height bound reads the rotation laws, which need that subtree balanced.
 *)
(* insertion.preservation.invariance *)
Lemma invariance
  : forall {A : Type} (cmp : A -> A -> Comparison) (a : A) (t : AVL A) .
      Measured t -> Balanced t ->
        Balanced (insert cmp a t)
        /\ (height (insert cmp a t) = height t \/ height (insert cmp a t) = ++ (height t)).
Proof.
  intros A cmp a t.
  match &t with | Leaf | Node (l by IHl) b (r by IHr) h end per AVL.induction.
  - intros m bt.
    simpl in |- *.
    ipso
      (conjoin
        (conjoin (disjoin (Identity.reflexivity _), _), (conjoin I, I)),
        (disjoin _, (Identity.reflexivity _))).
  - intros m bt.
    let proof m0 := simpl &m.
    match &m0 with | e m' end.
    match &m' with | ml mr end.
    let proof b0 := simpl &bt.
    match &b0 with | rel b' end.
    match &b' with | bl br end.
    simpl in |- *.
    match (&cmp &a &b) with | | | end |- c.
    (* [a] goes into the left subtree. *)
    + modus ponens &IHl, &ml |- IHl'.
      modus ponens &IHl', &bl |- ih.
      match &ih with | bl' g end.
      let proof ml' := insertion.preservation.measurement &cmp &a &l &ml.
      lemma near
        : height (insert &cmp &a &l) = height &r
          \/ height (insert &cmp &a &l) = ++ (height &r)
          \/ height &r = ++ (height (insert &cmp &a &l))
          \/ height (insert &cmp &a &l) = ++ (++ (height &r))
          \/ height &r = ++ (++ (height (insert &cmp &a &l))).
      {
        match &rel with | q | rel' end.
        - match &g with | k | k end.
          + ipso (disjoin (trans &k, &q), _).
          + leibniz &q in &k.
            ipso (disjoin _, (disjoin &k, _)).
        - match &rel' with | q | q end.
          + match &g with | k | k end.
            * ipso (disjoin _, (disjoin (trans &k, &q), _)).
            * leibniz &q in &k.
              ipso (disjoin _, (disjoin _, (disjoin _, (disjoin &k, _)))).
          + match &g with | k | k end.
            * leibniz <- &k in &q.
              ipso (disjoin _, (disjoin _, (disjoin &q, _))).
            * ipso (disjoin (trans &k, (symm &q)), _).
      }
      divide et impera.
      * ipso (balancing.balance (insert &cmp &a &l) &b &r &ml' &mr &bl' &br &near).
      * leibniz &e in |- *.
        simpl balance in |- *.
        match (Nat0.eq (height (insert &cmp &a &l)) (++ (++ (height &r)))) with | | end |- t1.
        -- modus aequans
             (Comparable.comparison.equality.reflection
               (height (insert &cmp &a &l)) (++ (++ (height &r)))),
             &t1
             |- e1.
           match &rel with | q | rel' end.
           ++ match &g with | k | k end.
              ** leibniz &k, &q in &e1.
                 ex
                   (Nat0.order.strict.distinction
                     (Nat0.order.strict.transitivity
                       (Nat0.increment.order.extensivity _) (Nat0.increment.order.extensivity _))
                     &e1)
                   quodlibet.
              ** leibniz &k in &e1.
                 let proof e1' := Nat0.increment.injectivity &e1.
                 leibniz &q in &e1'.
                 ex (Nat0.order.strict.distinction (Nat0.increment.order.extensivity _) &e1')
                   quodlibet.
           ++ match &rel' with | q | q end.
              ** match &g with | k | k end.
                 --- leibniz &k, &q in &e1.
                     let proof e1' := Nat0.increment.injectivity &e1.
                     ex (Nat0.order.strict.distinction (Nat0.increment.order.extensivity _) &e1')
                       quodlibet.
                 --- leibniz &q in |- *.
                     leibniz
                       (modus aequans
                         (Comparable.maximum.specification (++ (height &r)) (height &r)),
                         (disjoin _, (Nat0.increment.order.extensivity (height &r))))
                       in |- *.
                     leibniz <- &e1 in |- *.
                     ipso (rotation.right.growth (insert &cmp &a &l) &b &r &ml' &bl' &e1).
              ** match &g with | k | k end.
                 --- leibniz &k, &q in &e1.
                     ex
                       (Nat0.order.strict.distinction
                         (Nat0.order.strict.transitivity
                           (Nat0.increment.order.extensivity _)
                           (Nat0.order.strict.transitivity
                             (Nat0.increment.order.extensivity _)
                             (Nat0.increment.order.extensivity _)))
                         &e1)
                       quodlibet.
                 --- leibniz &k in &e1.
                     let proof e1' := Nat0.increment.injectivity &e1.
                     leibniz &q in &e1'.
                     ex
                       (Nat0.order.strict.distinction
                         (Nat0.order.strict.transitivity
                           (Nat0.increment.order.extensivity _)
                           (Nat0.increment.order.extensivity _))
                         &e1')
                       quodlibet.
        -- match (Nat0.eq (height &r) (++ (++ (height (insert &cmp &a &l))))) with | | end |- t2.
           ++ modus aequans
                (Comparable.comparison.equality.reflection
                  (height &r) (++ (++ (height (insert &cmp &a &l))))),
                &t2
                |- e2.
              match &rel with | q | rel' end.
              ** match &g with | k | k end.
                 --- leibniz &k, &q in &e2.
                     ex
                       (Nat0.order.strict.distinction
                         (Nat0.order.strict.transitivity
                           (Nat0.increment.order.extensivity _)
                           (Nat0.increment.order.extensivity _))
                         &e2)
                       quodlibet.
                 --- leibniz &k, &q in &e2.
                     ex
                       (Nat0.order.strict.distinction
                         (Nat0.order.strict.transitivity
                           (Nat0.increment.order.extensivity _)
                           (Nat0.order.strict.transitivity
                             (Nat0.increment.order.extensivity _)
                             (Nat0.increment.order.extensivity _)))
                         &e2)
                       quodlibet.
              ** match &rel' with | q | q end.
                 --- match &g with | k | k end.
                     +++ leibniz &k, &q in &e2.
                         ex
                           (Nat0.order.strict.distinction
                             (Nat0.order.strict.transitivity
                               (Nat0.increment.order.extensivity _)
                               (Nat0.order.strict.transitivity
                                 (Nat0.increment.order.extensivity _)
                                 (Nat0.increment.order.extensivity _)))
                             &e2)
                           quodlibet.
                     +++ leibniz &q in &k.
                         modus aequans
                           (Comparable.comparison.equality.reflection
                             (height (insert &cmp &a &l)) (++ (++ (height &r)))),
                           &k
                           |- t.
                         leibniz &t in &t1.
                         ex &t1 quodlibet.
                 --- match &g with | k | k end.
                     +++ leibniz &k, &q in &e2.
                         let proof e2' := Nat0.increment.injectivity &e2.
                         ex
                           (Nat0.order.strict.distinction
                             (Nat0.increment.order.extensivity _) &e2')
                           quodlibet.
                     +++ leibniz &k, &q in &e2.
                         let proof e2' := Nat0.increment.injectivity &e2.
                         ex
                           (Nat0.order.strict.distinction
                             (Nat0.order.strict.transitivity
                               (Nat0.increment.order.extensivity _)
                               (Nat0.increment.order.extensivity _))
                             &e2')
                           quodlibet.
           ++ simpl node in |- *.
              simpl in |- *.
              match &rel with | q | rel' end.
              ** match &g with | k | k end.
                 --- leibniz &k in |- *.
                     ipso (disjoin (Identity.reflexivity _), _).
                 --- leibniz &k in |- *.
                     leibniz &q in |- *.
                     leibniz
                       (modus aequans
                         (Comparable.maximum.specification (++ (height &r)) (height &r)),
                         (disjoin _, (Nat0.increment.order.extensivity (height &r))))
                       in |- *.
                     leibniz (Comparable.maximum.idempotence (height &r)) in |- *.
                     ipso (disjoin _, (Identity.reflexivity _)).
              ** match &rel' with | q | q end.
                 --- match &g with | k | k end.
                     +++ leibniz &k in |- *.
                         ipso (disjoin (Identity.reflexivity _), _).
                     +++ leibniz &q in &k.
                         modus aequans
                           (Comparable.comparison.equality.reflection
                             (height (insert &cmp &a &l)) (++ (++ (height &r)))),
                           &k
                           |- t.
                         leibniz &t in &t1.
                         ex &t1 quodlibet.
                 --- match &g with | k | k end.
                     +++ leibniz &k in |- *.
                         ipso (disjoin (Identity.reflexivity _), _).
                     +++ leibniz &k in |- *.
                         leibniz &q in |- *.
                         leibniz (Comparable.maximum.idempotence (++ (height &l))) in |- *.
                         leibniz
                           (Comparable.maximum.commutativity (height &l) (++ (height &l)))
                           in |- *.
                         leibniz
                           (modus aequans
                             (Comparable.maximum.specification (++ (height &l)) (height &l)),
                             (disjoin _, (Nat0.increment.order.extensivity (height &l))))
                           in |- *.
                         ipso (disjoin (Identity.reflexivity _), _).
    (* [a] is [b], already in the tree: nothing changes. *)
    + simpl in |- *.
      ipso (conjoin &bt, (disjoin (Identity.reflexivity _), _)).
    (* [a] goes into the right subtree. *)
    + modus ponens &IHr, &mr |- IHr'.
      modus ponens &IHr', &br |- ih.
      match &ih with | br' g end.
      let proof mr' := insertion.preservation.measurement &cmp &a &r &mr.
      lemma near
        : height &l = height (insert &cmp &a &r)
          \/ height &l = ++ (height (insert &cmp &a &r))
          \/ height (insert &cmp &a &r) = ++ (height &l)
          \/ height &l = ++ (++ (height (insert &cmp &a &r)))
          \/ height (insert &cmp &a &r) = ++ (++ (height &l)).
      {
        match &rel with | q | rel' end.
        - match &g with | k | k end.
          + ipso (disjoin (trans &q, (symm &k)), _).
          + leibniz <- &q in &k.
            ipso (disjoin _, (disjoin _, (disjoin &k, _))).
        - match &rel' with | q | q end.
          + match &g with | k | k end.
            * leibniz <- &k in &q.
              ipso (disjoin _, (disjoin &q, _)).
            * ipso (disjoin (trans &q, (symm &k)), _).
          + match &g with | k | k end.
            * ipso (disjoin _, (disjoin _, (disjoin (trans &k, &q), _))).
            * leibniz &q in &k.
              ipso (disjoin _, (disjoin _, (disjoin _, (disjoin _, &k)))).
      }
      divide et impera.
      * ipso (balancing.balance &l &b (insert &cmp &a &r) &ml &mr' &bl &br' &near).
      * leibniz &e in |- *.
        simpl balance in |- *.
        match (Nat0.eq (height &l) (++ (++ (height (insert &cmp &a &r))))) with | | end |- t1.
        -- modus aequans
             (Comparable.comparison.equality.reflection
               (height &l) (++ (++ (height (insert &cmp &a &r))))),
             &t1
             |- e1.
           match &rel with | q | rel' end.
           ++ match &g with | k | k end.
              ** leibniz &k in &e1.
                 leibniz <- &q in &e1.
                 ex
                   (Nat0.order.strict.distinction
                     (Nat0.order.strict.transitivity
                       (Nat0.increment.order.extensivity _) (Nat0.increment.order.extensivity _))
                     &e1)
                   quodlibet.
              ** leibniz &k in &e1.
                 leibniz <- &q in &e1.
                 ex
                   (Nat0.order.strict.distinction
                     (Nat0.order.strict.transitivity
                       (Nat0.increment.order.extensivity _)
                       (Nat0.order.strict.transitivity
                         (Nat0.increment.order.extensivity _)
                         (Nat0.increment.order.extensivity _)))
                     &e1)
                   quodlibet.
           ++ match &rel' with | q | q end.
              ** match &g with | k | k end.
                 --- leibniz &k, &q in &e1.
                     let proof e1' := Nat0.increment.injectivity &e1.
                     ex (Nat0.order.strict.distinction (Nat0.increment.order.extensivity _) &e1')
                       quodlibet.
                 --- leibniz &k, &q in &e1.
                     let proof e1' := Nat0.increment.injectivity &e1.
                     ex
                       (Nat0.order.strict.distinction
                         (Nat0.order.strict.transitivity
                           (Nat0.increment.order.extensivity _)
                           (Nat0.increment.order.extensivity _))
                         &e1')
                       quodlibet.
              ** match &g with | k | k end.
                 --- leibniz &k, &q in &e1.
                     ex
                       (Nat0.order.strict.distinction
                         (Nat0.order.strict.transitivity
                           (Nat0.increment.order.extensivity _)
                           (Nat0.order.strict.transitivity
                             (Nat0.increment.order.extensivity _)
                             (Nat0.increment.order.extensivity _)))
                         &e1)
                       quodlibet.
                 --- leibniz &k, &q in &e1.
                     ex
                       (Nat0.order.strict.distinction
                         (Nat0.order.strict.transitivity
                           (Nat0.increment.order.extensivity _)
                           (Nat0.order.strict.transitivity
                             (Nat0.increment.order.extensivity _)
                             (Nat0.order.strict.transitivity
                               (Nat0.increment.order.extensivity _)
                               (Nat0.increment.order.extensivity _))))
                         &e1)
                       quodlibet.
        -- match (Nat0.eq (height (insert &cmp &a &r)) (++ (++ (height &l)))) with | | end |- t2.
           ++ modus aequans
                (Comparable.comparison.equality.reflection
                  (height (insert &cmp &a &r)) (++ (++ (height &l)))),
                &t2
                |- e2.
              match &rel with | q | rel' end.
              ** match &g with | k | k end.
                 --- leibniz &k in &e2.
                     leibniz <- &q in &e2.
                     ex
                       (Nat0.order.strict.distinction
                         (Nat0.order.strict.transitivity
                           (Nat0.increment.order.extensivity _)
                           (Nat0.increment.order.extensivity _))
                         &e2)
                       quodlibet.
                 --- leibniz &k in &e2.
                     let proof e2' := Nat0.increment.injectivity &e2.
                     leibniz <- &q in &e2'.
                     ex (Nat0.order.strict.distinction (Nat0.increment.order.extensivity _) &e2')
                       quodlibet.
              ** match &rel' with | q | q end.
                 --- match &g with | k | k end.
                     +++ leibniz &k in &e2.
                         leibniz &q in &e2.
                         ex
                           (Nat0.order.strict.distinction
                             (Nat0.order.strict.transitivity
                               (Nat0.increment.order.extensivity _)
                               (Nat0.order.strict.transitivity
                                 (Nat0.increment.order.extensivity _)
                                 (Nat0.increment.order.extensivity _)))
                             &e2)
                           quodlibet.
                     +++ leibniz &k in &e2.
                         let proof e2' := Nat0.increment.injectivity &e2.
                         leibniz &q in &e2'.
                         ex
                           (Nat0.order.strict.distinction
                             (Nat0.order.strict.transitivity
                               (Nat0.increment.order.extensivity _)
                               (Nat0.increment.order.extensivity _))
                             &e2')
                           quodlibet.
                 --- match &g with | k | k end.
                     +++ leibniz &k in &e2.
                         leibniz &q in &e2.
                         let proof e2' := Nat0.increment.injectivity &e2.
                         ex
                           (Nat0.order.strict.distinction
                             (Nat0.increment.order.extensivity _) &e2')
                           quodlibet.
                     +++ leibniz &q in |- *.
                         leibniz
                           (Comparable.maximum.commutativity (height &l) (++ (height &l)))
                           in |- *.
                         leibniz
                           (modus aequans
                             (Comparable.maximum.specification (++ (height &l)) (height &l)),
                             (disjoin _, (Nat0.increment.order.extensivity (height &l))))
                           in |- *.
                         leibniz <- &e2 in |- *.
                         ipso (rotation.left.growth &l &b (insert &cmp &a &r) &mr' &br' &e2).
           ++ simpl node in |- *.
              simpl in |- *.
              match &rel with | q | rel' end.
              ** match &g with | k | k end.
                 --- leibniz &k in |- *.
                     ipso (disjoin (Identity.reflexivity _), _).
                 --- leibniz &k in |- *.
                     leibniz &q in |- *.
                     leibniz
                       (Comparable.maximum.commutativity (height &r) (++ (height &r)))
                       in |- *.
                     leibniz
                       (modus aequans
                         (Comparable.maximum.specification (++ (height &r)) (height &r)),
                         (disjoin _, (Nat0.increment.order.extensivity (height &r))))
                       in |- *.
                     leibniz (Comparable.maximum.idempotence (height &r)) in |- *.
                     ipso (disjoin _, (Identity.reflexivity _)).
              ** match &rel' with | q | q end.
                 --- match &g with | k | k end.
                     +++ leibniz &k in |- *.
                         ipso (disjoin (Identity.reflexivity _), _).
                     +++ leibniz &k in |- *.
                         leibniz &q in |- *.
                         leibniz (Comparable.maximum.idempotence (++ (height &r))) in |- *.
                         leibniz
                           (modus aequans
                             (Comparable.maximum.specification (++ (height &r)) (height &r)),
                             (disjoin _, (Nat0.increment.order.extensivity (height &r))))
                           in |- *.
                         ipso (disjoin (Identity.reflexivity _), _).
                 --- match &g with | k | k end.
                     +++ leibniz &k in |- *.
                         ipso (disjoin (Identity.reflexivity _), _).
                     +++ leibniz &q in &k.
                         modus aequans
                           (Comparable.comparison.equality.reflection
                             (height (insert &cmp &a &r)) (++ (++ (height &l)))),
                           &k
                           |- t.
                         leibniz &t in &t2.
                         ex &t2 quodlibet.
Qed.

(* insertion.preservation.balance *)
Theorem balance
  : forall {A : Type} (cmp : A -> A -> Comparison) (a : A) (t : AVL A) .
      Measured t -> Balanced t -> Balanced (insert cmp a t).
Proof.
  intros A cmp a t m bt.
  match (insertion.preservation.invariance &cmp &a &t &m &bt) with | kept _ end.
  ipso &kept.
Qed.

End preservation. (* insertion.preservation *)

(* insertion.growth *)
Theorem growth
  : forall {A : Type} (cmp : A -> A -> Comparison) (a : A) (t : AVL A) .
      Measured t -> Balanced t ->
      height (insert cmp a t) = height t \/ height (insert cmp a t) = ++ (height t).
Proof.
  intros A cmp a t m bt.
  match (insertion.preservation.invariance &cmp &a &t &m &bt) with | _ grown end.
  ipso &grown.
Qed.

(* [contains] and [insert] walk the same path, so the size laws read the
 * tree's shape alone and ask for no ordered tree.
 *)
Module size. (* insertion.size *)

(* insertion.size.growth *)
Theorem growth
  : forall {A : Type} (cmp : A -> A -> Comparison) (a : A) (t : AVL A) .
      contains cmp a t = false ->
      BinaryTree.size (to_tree (insert cmp a t)) = ++ (BinaryTree.size (to_tree t)).
Proof.
  intros A cmp a t.
  match &t with | Leaf | Node (l by IHl) b (r by IHr) n end per AVL.induction.
  - intro e.
    simpl in |- *.
    quod idem est.
  - intro e.
    simpl in &e.
    simpl in |- *.
    match (&cmp &a &b) with | | | end |- c.
    + leibniz (balancing.size (insert &cmp &a &l) &b &r) in |- *.
      simpl node in |- *.
      simpl in |- *.
      leibniz (&IHl &e) in |- *.
      leibniz (Nat0.increment.specification (BinaryTree.size (to_tree &l))) in |- *.
      leibniz
        (Nat0.addition.associativity
          1 (BinaryTree.size (to_tree &l)) (BinaryTree.size (to_tree &r)))
        in |- *.
      leibniz
        <- (Nat0.increment.specification
             (BinaryTree.size (to_tree &l) + BinaryTree.size (to_tree &r)))
        in |- *.
      quod idem est.
    + ex &e quodlibet.
    + leibniz (balancing.size &l &b (insert &cmp &a &r)) in |- *.
      simpl node in |- *.
      simpl in |- *.
      leibniz (&IHr &e) in |- *.
      leibniz (Nat0.increment.specification (BinaryTree.size (to_tree &r))) in |- *.
      leibniz
        (Nat0.addition.left.commutativity
          (BinaryTree.size (to_tree &l)) 1 (BinaryTree.size (to_tree &r)))
        in |- *.
      leibniz
        <- (Nat0.increment.specification
             (BinaryTree.size (to_tree &l) + BinaryTree.size (to_tree &r)))
        in |- *.
      quod idem est.
Qed.

(* insertion.size.invariance *)
Theorem invariance
  : forall {A : Type} (cmp : A -> A -> Comparison) (a : A) (t : AVL A) .
      contains cmp a t = true ->
      BinaryTree.size (to_tree (insert cmp a t)) = BinaryTree.size (to_tree t).
Proof.
  intros A cmp a t.
  match &t with | Leaf | Node (l by IHl) b (r by IHr) n end per AVL.induction.
  - intro e.
    simpl in &e.
    ex &e quodlibet.
  - intro e.
    simpl in &e.
    simpl in |- *.
    match (&cmp &a &b) with | | | end |- c.
    + leibniz (balancing.size (insert &cmp &a &l) &b &r) in |- *.
      simpl node in |- *.
      simpl in |- *.
      leibniz (&IHl &e) in |- *.
      quod idem est.
    + simpl in |- *.
      quod idem est.
    + leibniz (balancing.size &l &b (insert &cmp &a &r)) in |- *.
      simpl node in |- *.
      simpl in |- *.
      leibniz (&IHr &e) in |- *.
      quod idem est.
Qed.

End size. (* insertion.size *)

End insertion. (* insertion *)

Module extraction. (* extraction *)

Module absence. (* extraction.absence *)

(* extraction.absence.specification *)
Theorem specification
  : forall {A : Type} (t : AVL A) . pop t = None <-> t = AVL.Leaf.
Proof.
  intros A t.
  divide et impera.
  - match &t with | Leaf | Node l a r h end.
    + intro e.
      quod idem est.
    + simpl in |- *.
      match (pop &l) with | None | Some p end |- found.
      * intro e.
        ex &e quodlibet.
      * match &p with | m l' end.
        intro e.
        ex &e quodlibet.
  - intro e.
    leibniz &e in |- *.
    simpl in |- *.
    quod idem est.
Qed.

End absence. (* extraction.absence *)

(* This law asks for no ordered tree: on any tree, the element taken out
 * and the tree that is left hold what the tree held.
 *)
(* extraction.membership *)
Theorem membership
  : forall {A : Type} (t : AVL A) (m : A) (rest : AVL A) .
      pop t = Some (Product.introduction m rest) ->
      forall (b : A) .
        BinaryTree.Contains b (to_tree t) <-> b = m \/ BinaryTree.Contains b (to_tree rest).
Proof.
  intros A t.
  match &t with | Leaf | Node (l by IHl) a (r by IHr) n end per AVL.induction.
  - intros m rest e b.
    simpl in &e.
    ex &e quodlibet.
  - intros m rest.
    simpl in |- *.
    match (pop &l) with | None | Some p end |- found.
    + intros e b.
      modus aequans (extraction.absence.specification &l), &found |- empty.
      match (Product.introduction.injectivity (Option.some.injectivity &e)) with | am rr end.
      leibniz &empty in |- *.
      leibniz <- &am, <- &rr in |- *.
      simpl in |- *.
      divide et impera.
      * intro h.
        match &h with | f | h' end.
        -- ex &f quodlibet.
        -- ipso &h'.
      * intro h.
        ipso (disjoin _, &h).
    + match &p with | m' l' end.
      intros e b.
      match (Product.introduction.injectivity (Option.some.injectivity &e)) with | mm nr end.
      leibniz <- &mm, <- &nr in |- *.
      let proof bm := balancing.membership &l' &a &r &b.
      simpl node in &bm.
      simpl in &bm.
      let proof spec
        := &IHl &m' &l' (Identity.reflexivity (Some (Product.introduction &m' &l'))) &b.
      divide et impera.
      * intro h.
        match &h with | inside | others end.
        -- modus aequans &spec, &inside |- d.
           match &d with | least | kept end.
           ++ ipso (disjoin &least, _).
           ++ modus aequans &bm, (disjoin &kept, _) |- now.
              ipso (disjoin _, &now).
        -- modus aequans &bm, (disjoin _, &others) |- now.
           ipso (disjoin _, &now).
      * intro h.
        match &h with | least | h' end.
        -- modus aequans &spec, (disjoin &least, _) |- inside.
           ipso (disjoin &inside, _).
        -- modus aequans &bm, &h' |- h''.
           match &h'' with | kept | others end.
           ++ modus aequans &spec, (disjoin _, &kept) |- inside.
              ipso (disjoin &inside, _).
           ++ ipso (disjoin _, &others).
Qed.

(* Transitivity is the one property of [lt] this law reads, so it takes
 * that alone and no comparison.
 *)
(* extraction.minimality *)
Theorem minimality
  : forall {A : Type} {lt : A -> A -> Prop} .
      (forall (x : A) (y : A) (z : A) . lt x y -> lt y z -> lt x z) ->
      forall (t : AVL A) (m : A) (rest : AVL A) .
        Ordered lt t -> pop t = Some (Product.introduction m rest) ->
        BinaryTree.All (fun (b : A) . lt m b) (to_tree rest).
Proof.
  intros A lt transitive t.
  match &t with | Leaf | Node (l by IHl) a (r by IHr) h end per AVL.induction.
  - intros m rest o e.
    simpl in &e.
    ex &e quodlibet.
  - intros m rest o.
    simpl Ordered in &o.
    simpl in &o.
    match &o with | below o1 end.
    match &o1 with | above o2 end.
    match &o2 with | lower upper end.
    simpl in |- *.
    match (pop &l) with | None | Some p end |- found.
    + intro e.
      match (Product.introduction.injectivity (Option.some.injectivity &e)) with | am rr end.
      leibniz <- &am, <- &rr in |- *.
      ipso &above.
    (* The element taken out is in the left subtree, so it is below [a],
     * and through [a] below all of the right subtree.
     *)
    + match &p with | m' l' end.
      intro e.
      match (Product.introduction.injectivity (Option.some.injectivity &e)) with | mm nr end.
      leibniz <- &mm, <- &nr in |- *.
      let proof smaller
        := &IHl &m' &l' &lower (Identity.reflexivity (Some (Product.introduction &m' &l'))).
      lemma inside : BinaryTree.Contains &m' (to_tree &l).
      {
        modus aequans
          (extraction.membership &l &m' &l' &found &m'), (disjoin (Identity.reflexivity &m'), _)
          |- member.
        ipso &member.
      }
      modus aequans
        (BinaryTree.quantification.all.specification (fun (b : &A) . &lt b &a) (to_tree &l)),
        &below
        |- each.
      let proof ma : &lt &m' &a := &each &m' &inside.
      lemma beyond : BinaryTree.All (fun (b : &A) . &lt &m' b) (to_tree &r).
      {
        ipso
          (BinaryTree.quantification.all.monotonicity
            (fun (b : &A) (ab : &lt &a b) . &transitive &m' &a b &ma ab) &above).
      }
      lemma whole : BinaryTree.All (fun (b : &A) . &lt &m' b) (to_tree (node &l' &a &r)).
      {
        simpl node in |- *.
        simpl in |- *.
        ipso (conjoin &smaller, (conjoin &ma, &beyond)).
      }
      modus aequans
        (BinaryTree.quantification.all.specification
          (fun (b : &A) . &lt &m' b) (to_tree (node &l' &a &r))),
        &whole
        |- every.
      lemma moved
        : forall (x : &A) . BinaryTree.Contains x (to_tree (balance &l' &a &r)) -> &lt &m' x.
      {
        intros x member.
        modus aequans (balancing.membership &l' &a &r &x), &member |- there.
        ipso (&every &x &there).
      }
      modus aequans
        (BinaryTree.quantification.all.specification
          (fun (b : &A) . &lt &m' b) (to_tree (balance &l' &a &r))),
        &moved
        |- done.
      ipso &done.
Qed.

Module preservation. (* extraction.preservation *)

(* What is left of the left subtree was in it, so it is still below [a]. *)
(* extraction.preservation.order *)
Theorem order
  : forall {A : Type} {lt : A -> A -> Prop} .
      (forall (x : A) (y : A) (z : A) . lt x y -> lt y z -> lt x z) ->
      forall (t : AVL A) (m : A) (rest : AVL A) .
        Ordered lt t -> pop t = Some (Product.introduction m rest) -> Ordered lt rest.
Proof.
  intros A lt transitive t.
  match &t with | Leaf | Node (l by IHl) a (r by IHr) h end per AVL.induction.
  - intros m rest o e.
    simpl in &e.
    ex &e quodlibet.
  - intros m rest o.
    simpl Ordered in &o.
    simpl in &o.
    match &o with | below o1 end.
    match &o1 with | above o2 end.
    match &o2 with | lower upper end.
    simpl in |- *.
    match (pop &l) with | None | Some p end |- found.
    + intro e.
      match (Product.introduction.injectivity (Option.some.injectivity &e)) with | am rr end.
      leibniz <- &rr in |- *.
      ipso &upper.
    + match &p with | m' l' end.
      intro e.
      match (Product.introduction.injectivity (Option.some.injectivity &e)) with | mm nr end.
      leibniz <- &nr in |- *.
      let proof kept
        := &IHl &m' &l' &lower (Identity.reflexivity (Some (Product.introduction &m' &l'))).
      modus aequans
        (BinaryTree.quantification.all.specification (fun (b : &A) . &lt b &a) (to_tree &l)),
        &below
        |- each.
      lemma every : forall (x : &A) . BinaryTree.Contains x (to_tree &l') -> &lt x &a.
      {
        intros x member.
        modus aequans (extraction.membership &l &m' &l' &found &x), (disjoin _, &member)
          |- inside.
        ipso (&each &x &inside).
      }
      modus aequans
        (BinaryTree.quantification.all.specification (fun (b : &A) . &lt b &a) (to_tree &l')),
        &every
        |- smaller.
      lemma on : Ordered &lt (node &l' &a &r).
      {
        simpl Ordered, node in |- *.
        simpl in |- *.
        ipso (conjoin &smaller, (conjoin &above, (conjoin &kept, &upper))).
      }
      ipso (balancing.order &transitive &l' &a &r &on).
Qed.

(* extraction.preservation.measurement *)
Theorem measurement
  : forall {A : Type} (t : AVL A) (m : A) (rest : AVL A) .
      Measured t -> pop t = Some (Product.introduction m rest) -> Measured rest.
Proof.
  intros A t.
  match &t with | Leaf | Node (l by IHl) a (r by IHr) h end per AVL.induction.
  - intros m rest mt e.
    simpl in &e.
    ex &e quodlibet.
  - intros m rest mt.
    let proof m0 := simpl &mt.
    match &m0 with | _ m' end.
    match &m' with | ml mr end.
    simpl in |- *.
    match (pop &l) with | None | Some p end |- found.
    + intro e.
      match (Product.introduction.injectivity (Option.some.injectivity &e)) with | am rr end.
      leibniz <- &rr in |- *.
      ipso &mr.
    + match &p with | m'' l' end.
      intro e.
      match (Product.introduction.injectivity (Option.some.injectivity &e)) with | mm nr end.
      leibniz <- &nr in |- *.
      let proof ml'
        := &IHl &m'' &l' &ml (Identity.reflexivity (Some (Product.introduction &m'' &l'))).
      ipso (balancing.measurement &l' &a &r &ml' &mr).
Qed.

(* The balance of what [pop] leaves and its height are proved by one
 * induction, as for [insert]: the height bound keeps the two subtrees of
 * each rebuilt node within [balance]'s reach.
 *)
(* extraction.preservation.invariance *)
Lemma invariance
  : forall {A : Type} (t : AVL A) (m : A) (rest : AVL A) .
      Measured t -> Balanced t -> pop t = Some (Product.introduction m rest) ->
      Balanced rest /\ (height rest = height t \/ ++ (height rest) = height t).
Proof.
  intros A t.
  match &t with | Leaf | Node (l by IHl) a (r by IHr) h end per AVL.induction.
  - intros m rest mt bt e.
    simpl in &e.
    ex &e quodlibet.
  - intros m rest mt bt.
    let proof m0 := simpl &mt.
    match &m0 with | e m' end.
    match &m' with | ml mr end.
    let proof b0 := simpl &bt.
    match &b0 with | rel b' end.
    match &b' with | bl br end.
    simpl in |- *.
    match (pop &l) with | None | Some p end |- found.
    + intro e'.
      modus aequans (extraction.absence.specification &l), &found |- empty.
      match (Product.introduction.injectivity (Option.some.injectivity &e')) with | am rr end.
      leibniz <- &rr in |- *.
      divide et impera.
      * ipso &br.
      * leibniz &e in |- *.
        leibniz &empty in |- *.
        let proof z : height (@AVL.Leaf &A) = Nat0.Zero := Identity.reflexivity _.
        leibniz &z in |- *.
        leibniz (Nat0.maximum.left.identity (height &r)) in |- *.
        ipso (disjoin _, (Identity.reflexivity _)).
    + match &p with | m'' l' end.
      intro e'.
      match (Product.introduction.injectivity (Option.some.injectivity &e')) with | mm nr end.
      leibniz <- &nr in |- *.
      let proof ml' := extraction.preservation.measurement &l &m'' &l' &ml &found.
      let proof ih
        := &IHl &m'' &l' &ml &bl (Identity.reflexivity (Some (Product.introduction &m'' &l'))).
      match &ih with | bl' g end.
      lemma near
        : height &l' = height &r
          \/ height &l' = ++ (height &r)
          \/ height &r = ++ (height &l')
          \/ height &l' = ++ (++ (height &r))
          \/ height &r = ++ (++ (height &l')).
      {
        match &rel with | q | rel' end.
        - match &g with | k | k end.
          + ipso (disjoin (trans &k, &q), _).
          + ipso (disjoin _, (disjoin _, (disjoin (symm (trans &k, &q)), _))).
        - match &rel' with | q | q end.
          + match &g with | k | k end.
            * ipso (disjoin _, (disjoin (trans &k, &q), _)).
            * ipso (disjoin (Nat0.increment.injectivity (trans &k, &q)), _).
          + match &g with | k | k end.
            * leibniz <- &k in &q.
              ipso (disjoin _, (disjoin _, (disjoin &q, _))).
            * leibniz (symm &k) in &q.
              ipso (disjoin _, (disjoin _, (disjoin _, (disjoin _, &q)))).
      }
      divide et impera.
      * ipso (balancing.balance &l' &a &r &ml' &mr &bl' &br &near).
      * leibniz &e in |- *.
        ipso (balancing.shrinkage.left &l' &a &r (height &l) &mr &br &rel &g).
Qed.

(* extraction.preservation.balance *)
Theorem balance
  : forall {A : Type} (t : AVL A) (m : A) (rest : AVL A) .
      Measured t -> Balanced t -> pop t = Some (Product.introduction m rest) ->
      Balanced rest.
Proof.
  intros A t m rest mt bt e.
  match (extraction.preservation.invariance &t &m &rest &mt &bt &e) with | kept _ end.
  ipso &kept.
Qed.

End preservation. (* extraction.preservation *)

(* extraction.shrinkage *)
Theorem shrinkage
  : forall {A : Type} (t : AVL A) (m : A) (rest : AVL A) .
      Measured t -> Balanced t -> pop t = Some (Product.introduction m rest) ->
      height rest = height t \/ ++ (height rest) = height t.
Proof.
  intros A t m rest mt bt e.
  match (extraction.preservation.invariance &t &m &rest &mt &bt &e) with | _ shrunk end.
  ipso &shrunk.
Qed.

(* extraction.size *)
Theorem size
  : forall {A : Type} (t : AVL A) (m : A) (rest : AVL A) .
      pop t = Some (Product.introduction m rest) ->
      ++ (BinaryTree.size (to_tree rest)) = BinaryTree.size (to_tree t).
Proof.
  intros A t.
  match &t with | Leaf | Node (l by IHl) a (r by IHr) n end per AVL.induction.
  - intros m rest e.
    simpl in &e.
    ex &e quodlibet.
  - intros m rest.
    simpl in |- *.
    match (pop &l) with | None | Some p end |- found.
    + intro e.
      modus aequans (extraction.absence.specification &l), &found |- empty.
      match (Product.introduction.injectivity (Option.some.injectivity &e)) with | am rr end.
      leibniz &empty, <- &rr in |- *.
      simpl in |- *.
      quod idem est.
    + match &p with | m' l' end.
      intro e.
      match (Product.introduction.injectivity (Option.some.injectivity &e)) with | mm nr end.
      let proof spec
        := &IHl &m' &l' (Identity.reflexivity (Some (Product.introduction &m' &l'))).
      leibniz <- &nr, (balancing.size &l' &a &r) in |- *.
      simpl node in |- *.
      simpl in |- *.
      leibniz <- &spec in |- *.
      leibniz (Nat0.increment.specification (BinaryTree.size (to_tree &l'))) in |- *.
      leibniz
        (Nat0.addition.associativity
          1 (BinaryTree.size (to_tree &l')) (BinaryTree.size (to_tree &r)))
        in |- *.
      leibniz
        <- (Nat0.increment.specification
             (BinaryTree.size (to_tree &l') + BinaryTree.size (to_tree &r)))
        in |- *.
      quod idem est.
Qed.

End extraction. (* extraction *)

Module joining. (* joining *)

(* joining.membership *)
Theorem membership
  : forall {A : Type} (l : AVL A) (r : AVL A) (b : A) .
      BinaryTree.Contains b (to_tree (join l r))
      <-> BinaryTree.Contains b (to_tree l) \/ BinaryTree.Contains b (to_tree r).
Proof.
  intros A l r b.
  simpl join in |- *.
  match (pop &r) with | None | Some p end |- found.
  - modus aequans (extraction.absence.specification &r), &found |- empty.
    leibniz &empty in |- *.
    simpl in |- *.
    divide et impera.
    + intro h.
      ipso (disjoin &h, _).
    + intro h.
      match &h with | m | f end.
      * ipso &m.
      * ex &f quodlibet.
  - match &p with | m r' end.
    let proof bm := balancing.membership &l &m &r' &b.
    simpl node in &bm.
    simpl in &bm.
    let proof spec := extraction.membership &r &m &r' &found &b.
    divide et impera.
    + intro h.
      modus aequans &bm, &h |- h'.
      match &h' with | inside | rest end.
      * ipso (disjoin &inside, _).
      * ipso (disjoin _, (modus aequans &spec, &rest)).
    + intro h.
      match &h with | inside | beyond end.
      * modus aequans &bm, (disjoin &inside, _) |- now.
        ipso &now.
      * modus aequans &spec, &beyond |- rest.
        modus aequans &bm, (disjoin _, &rest) |- now.
        ipso &now.
Qed.

(* joining.size *)
Theorem size
  : forall {A : Type} (l : AVL A) (r : AVL A) .
      BinaryTree.size (to_tree (join l r))
      = BinaryTree.size (to_tree l) + BinaryTree.size (to_tree r).
Proof.
  intros A l r.
  simpl join in |- *.
  match (pop &r) with | None | Some p end |- found.
  - modus aequans (extraction.absence.specification &r), &found |- empty.
    leibniz &empty in |- *.
    simpl in |- *.
    match (Nat0.addition.identity (BinaryTree.size (to_tree &l))) with | _ ri end.
    leibniz &ri in |- *.
    quod idem est.
  - match &p with | m r' end.
    let proof spec := extraction.size &r &m &r' &found.
    leibniz (balancing.size &l &m &r') in |- *.
    simpl node in |- *.
    simpl in |- *.
    leibniz <- &spec in |- *.
    leibniz (Nat0.increment.specification (BinaryTree.size (to_tree &r'))) in |- *.
    leibniz
      (Nat0.addition.left.commutativity
        (BinaryTree.size (to_tree &l)) 1 (BinaryTree.size (to_tree &r')))
      in |- *.
    leibniz
      <- (Nat0.increment.specification
           (BinaryTree.size (to_tree &l) + BinaryTree.size (to_tree &r')))
      in |- *.
    quod idem est.
Qed.

Module preservation. (* joining.preservation *)

(* [b] stands between the two trees: every element of [l] is below it, and
 * every element of [r] above it.
 *)
(* joining.preservation.order *)
Theorem order
  : forall {A : Type} {lt : A -> A -> Prop} .
      (forall (x : A) (y : A) (z : A) . lt x y -> lt y z -> lt x z) ->
      forall (b : A) (l : AVL A) (r : AVL A) .
        BinaryTree.All (fun (x : A) . lt x b) (to_tree l) ->
        BinaryTree.All (fun (x : A) . lt b x) (to_tree r) ->
        Ordered lt l -> Ordered lt r -> Ordered lt (join l r).
Proof.
  intros A lt transitive b l r below above lower upper.
  simpl join in |- *.
  match (pop &r) with | None | Some p end |- found.
  - ipso &lower.
  - match &p with | m r' end.
    lemma inside : BinaryTree.Contains &m (to_tree &r).
    {
      modus aequans
        (extraction.membership &r &m &r' &found &m), (disjoin (Identity.reflexivity &m), _)
        |- member.
      ipso &member.
    }
    modus aequans
      (BinaryTree.quantification.all.specification (fun (x : &A) . &lt &b x) (to_tree &r)),
      &above
      |- each.
    let proof bm : &lt &b &m := &each &m &inside.
    lemma smaller : BinaryTree.All (fun (x : &A) . &lt x &m) (to_tree &l).
    {
      ipso
        (BinaryTree.quantification.all.monotonicity
          (fun (x : &A) (xb : &lt x &b) . &transitive x &b &m xb &bm) &below).
    }
    let proof larger := extraction.minimality &transitive &r &m &r' &upper &found.
    let proof kept := extraction.preservation.order &transitive &r &m &r' &upper &found.
    lemma on : Ordered &lt (node &l &m &r').
    {
      simpl Ordered, node in |- *.
      simpl in |- *.
      ipso (conjoin &smaller, (conjoin &larger, (conjoin &lower, &kept))).
    }
    ipso (balancing.order &transitive &l &m &r' &on).
Qed.

(* joining.preservation.measurement *)
Theorem measurement
  : forall {A : Type} (l : AVL A) (r : AVL A) .
      Measured l -> Measured r -> Measured (join l r).
Proof.
  intros A l r ml mr.
  simpl join in |- *.
  match (pop &r) with | None | Some p end |- found.
  - ipso &ml.
  - match &p with | m r' end.
    ipso
      (balancing.measurement &l &m &r'
        &ml (extraction.preservation.measurement &r &m &r' &mr &found)).
Qed.

(* The two trees are within one level of each other, as the subtrees of a
 * balanced node are.
 *)
(* joining.preservation.balance *)
Theorem balance
  : forall {A : Type} (l : AVL A) (r : AVL A) .
      Measured l -> Measured r -> Balanced l -> Balanced r ->
      height l = height r \/ height l = ++ (height r) \/ height r = ++ (height l) ->
      Balanced (join l r).
Proof.
  intros A l r ml mr bl br rel.
  simpl join in |- *.
  match (pop &r) with | None | Some p end |- found.
  - ipso &bl.
  - match &p with | m r' end.
    let proof mr' := extraction.preservation.measurement &r &m &r' &mr &found.
    let proof inv := extraction.preservation.invariance &r &m &r' &mr &br &found.
    match &inv with | br' g end.
    lemma near
      : height &l = height &r'
        \/ height &l = ++ (height &r')
        \/ height &r' = ++ (height &l)
        \/ height &l = ++ (++ (height &r'))
        \/ height &r' = ++ (++ (height &l)).
    {
      match &rel with | q | rel' end.
      - match &g with | k | k end.
        + ipso (disjoin (trans &q, (symm &k)), _).
        + ipso (disjoin _, (disjoin (trans &q, (symm &k)), _)).
      - match &rel' with | q | q end.
        + match &g with | k | k end.
          * leibniz <- &k in &q.
            ipso (disjoin _, (disjoin &q, _)).
          * leibniz (symm &k) in &q.
            ipso (disjoin _, (disjoin _, (disjoin _, (disjoin &q, _)))).
        + match &g with | k | k end.
          * ipso (disjoin _, (disjoin _, (disjoin (trans &k, &q), _))).
          * ipso (disjoin (symm (Nat0.increment.injectivity (trans &k, &q))), _).
    }
    ipso (balancing.balance &l &m &r' &ml &mr' &bl &br' &near).
Qed.

End preservation. (* joining.preservation *)

End joining. (* joining *)

Module removal. (* removal *)

(* removal.membership *)
Theorem membership
  : forall {A : Type} {cmp : A -> A -> Comparison} {lt : A -> A -> Prop} .
      Comparable cmp lt ->
      forall (a : A) (b : A) (t : AVL A) .
        Ordered lt t ->
        (BinaryTree.Contains b (to_tree (remove cmp a t))
          <-> BinaryTree.Contains b (to_tree t) /\ ~ (b = a)).
Proof.
  intros A cmp lt C a b t.
  match &t with | Leaf | Node (l by IHl) c (r by IHr) n end per AVL.induction.
  - intro o.
    simpl in |- *.
    divide et impera.
    + intro f.
      ex &f quodlibet.
    + intro h.
      match &h with | f differs end.
      ex &f quodlibet.
  - intro o.
    simpl Ordered in &o.
    simpl in &o.
    match &o with | below o1 end.
    match &o1 with | above o2 end.
    match &o2 with | lower upper end.
    modus ponens &IHl, &lower |- left.
    modus ponens &IHr, &upper |- right.
    modus aequans
      (BinaryTree.quantification.all.specification (fun (x : &A) . &lt x &c) (to_tree &l)),
      &below
      |- under.
    modus aequans
      (BinaryTree.quantification.all.specification (fun (x : &A) . &lt &c x) (to_tree &r)),
      &above
      |- over.
    simpl in |- *.
    match (&cmp &a &c) with | | | end |- k.
    (* [a] is below [c]: it is removed from the left subtree. *)
    + modus aequans (Comparable.comparison.strict.specification &a &c), &k |- ac.
      let proof bm := balancing.membership (remove &cmp &a &l) &c &r &b.
      simpl node in &bm.
      simpl in &bm.
      lemma shift
        : (BinaryTree.Contains &b (to_tree (remove &cmp &a &l))
            \/ &b = &c
            \/ BinaryTree.Contains &b (to_tree &r))
          <-> (BinaryTree.Contains &b (to_tree &l)
                \/ &b = &c
                \/ BinaryTree.Contains &b (to_tree &r))
              /\ ~ (&b = &a).
      {
        divide et impera.
        - intro h.
          match &h with | m | h' end.
          + modus aequans &left, &m |- both.
            match &both with | inside differs end.
            ipso (conjoin (disjoin &inside, _), &differs).
          + match &h' with | e | m end.
            * lemma differs : ~ (&b = &a).
              {
                simpl (~ _) in |- *.
                intro ba.
                leibniz <- &ba in &ac.
                leibniz &e in &ac.
                ex (Comparable.order.strict.irreflexivity &c &ac) quodlibet.
              }
              ipso (conjoin (disjoin _, (disjoin &e, _)), &differs).
            * lemma differs : ~ (&b = &a).
              {
                simpl (~ _) in |- *.
                intro ba.
                let proof cb : &lt &c &b := &over &b &m.
                leibniz &ba in &cb.
                ex (Comparable.order.strict.asymmetry &a &c &ac &cb) quodlibet.
              }
              ipso (conjoin (disjoin _, (disjoin _, &m)), &differs).
        - intro h.
          match &h with | present differs end.
          match &present with | m | rest end.
          + modus aequans &left, (conjoin &m, &differs) |- kept.
            ipso (disjoin &kept, _).
          + ipso (disjoin _, &rest).
      }
      ipso (Biconditional.transitivity &bm &shift).
    (* [a] is [c]: the node goes, and its two subtrees are joined. *)
    + modus aequans (Comparable.comparison.equality.specification &a &c), &k |- ac.
      let proof joined := joining.membership &l &r &b.
      divide et impera.
      * intro h.
        modus aequans &joined, &h |- either.
        match &either with | m | m end.
        -- lemma differs : ~ (&b = &a).
           {
             simpl (~ _) in |- *.
             intro ba.
             let proof bc : &lt &b &c := &under &b &m.
             leibniz &ba in &bc.
             leibniz &ac in &bc.
             ex (Comparable.order.strict.irreflexivity &c &bc) quodlibet.
           }
           ipso (conjoin (disjoin &m, _), &differs).
        -- lemma differs : ~ (&b = &a).
           {
             simpl (~ _) in |- *.
             intro ba.
             let proof cb : &lt &c &b := &over &b &m.
             leibniz &ba in &cb.
             leibniz &ac in &cb.
             ex (Comparable.order.strict.irreflexivity &c &cb) quodlibet.
           }
           ipso (conjoin (disjoin _, (disjoin _, &m)), &differs).
      * intro h.
        match &h with | present differs end.
        match &present with | m | rest end.
        -- ipso (modus aequans &joined, (disjoin &m, _)).
        -- match &rest with | e | m end.
           ++ trans &e, (symm &ac) |- ba.
              ex (&differs &ba) quodlibet.
           ++ ipso (modus aequans &joined, (disjoin _, &m)).
    (* [a] is above [c]: it is removed from the right subtree. *)
    + modus aequans
        (Comparable.comparison.strict.transposition.specification &a &c), &k |- ca.
      let proof bm := balancing.membership &l &c (remove &cmp &a &r) &b.
      simpl node in &bm.
      simpl in &bm.
      lemma shift
        : (BinaryTree.Contains &b (to_tree &l)
            \/ &b = &c
            \/ BinaryTree.Contains &b (to_tree (remove &cmp &a &r)))
          <-> (BinaryTree.Contains &b (to_tree &l)
                \/ &b = &c
                \/ BinaryTree.Contains &b (to_tree &r))
              /\ ~ (&b = &a).
      {
        divide et impera.
        - intro h.
          match &h with | m | h' end.
          + lemma differs : ~ (&b = &a).
            {
              simpl (~ _) in |- *.
              intro ba.
              let proof bc : &lt &b &c := &under &b &m.
              leibniz &ba in &bc.
              ex (Comparable.order.strict.asymmetry &a &c &bc &ca) quodlibet.
            }
            ipso (conjoin (disjoin &m, _), &differs).
          + match &h' with | e | m end.
            * lemma differs : ~ (&b = &a).
              {
                simpl (~ _) in |- *.
                intro ba.
                leibniz <- &ba in &ca.
                leibniz &e in &ca.
                ex (Comparable.order.strict.irreflexivity &c &ca) quodlibet.
              }
              ipso (conjoin (disjoin _, (disjoin &e, _)), &differs).
            * modus aequans &right, &m |- both.
              match &both with | inside differs end.
              ipso (conjoin (disjoin _, (disjoin _, &inside)), &differs).
        - intro h.
          match &h with | present differs end.
          match &present with | m | rest end.
          + ipso (disjoin &m, _).
          + match &rest with | e | m end.
            * ipso (disjoin _, (disjoin &e, _)).
            * modus aequans &right, (conjoin &m, &differs) |- kept.
              ipso (disjoin _, (disjoin _, &kept)).
      }
      ipso (Biconditional.transitivity &bm &shift).
Qed.

Module preservation. (* removal.preservation *)

(* removal.preservation.order *)
Theorem order
  : forall {A : Type} {cmp : A -> A -> Comparison} {lt : A -> A -> Prop} .
      Comparable cmp lt ->
      forall (a : A) (t : AVL A) . Ordered lt t -> Ordered lt (remove cmp a t).
Proof.
  intros A cmp lt C a t.
  match &t with | Leaf | Node (l by IHl) c (r by IHr) n end per AVL.induction.
  - intro o.
    ipso I.
  - intro o.
    simpl Ordered in &o.
    let proof o0 := simpl &o.
    match &o0 with | below o1 end.
    match &o1 with | above o2 end.
    match &o2 with | lower upper end.
    simpl in |- *.
    match (&cmp &a &c) with | | | end |- k.
    (* What is left of the left subtree was in it, so it is still below [c]. *)
    + modus ponens &IHl, &lower |- kept.
      modus aequans
        (BinaryTree.quantification.all.specification (fun (x : &A) . &lt x &c) (to_tree &l)),
        &below
        |- under.
      lemma every
        : forall (x : &A) . BinaryTree.Contains x (to_tree (remove &cmp &a &l)) -> &lt x &c.
      {
        intros x member.
        modus aequans (removal.membership &C &a &x &l &lower), &member |- both.
        match &both with | inside differs end.
        ipso (&under &x &inside).
      }
      modus aequans
        (BinaryTree.quantification.all.specification
          (fun (x : &A) . &lt x &c) (to_tree (remove &cmp &a &l))),
        &every
        |- smaller.
      lemma on : Ordered &lt (node (remove &cmp &a &l) &c &r).
      {
        simpl Ordered, node in |- *.
        simpl in |- *.
        ipso (conjoin &smaller, (conjoin &above, (conjoin &kept, &upper))).
      }
      ipso
        (balancing.order
          (fun (x : &A) (y : &A) (z : &A) . Comparable.transitivity x y z)
          (remove &cmp &a &l) &c &r &on).
    + ipso
        (joining.preservation.order
          (fun (x : &A) (y : &A) (z : &A) . Comparable.transitivity x y z)
          &c &l &r &below &above &lower &upper).
    (* What is left of the right subtree was in it, so it is still above [c]. *)
    + modus ponens &IHr, &upper |- kept.
      modus aequans
        (BinaryTree.quantification.all.specification (fun (x : &A) . &lt &c x) (to_tree &r)),
        &above
        |- over.
      lemma every
        : forall (x : &A) . BinaryTree.Contains x (to_tree (remove &cmp &a &r)) -> &lt &c x.
      {
        intros x member.
        modus aequans (removal.membership &C &a &x &r &upper), &member |- both.
        match &both with | inside differs end.
        ipso (&over &x &inside).
      }
      modus aequans
        (BinaryTree.quantification.all.specification
          (fun (x : &A) . &lt &c x) (to_tree (remove &cmp &a &r))),
        &every
        |- larger.
      lemma on : Ordered &lt (node &l &c (remove &cmp &a &r)).
      {
        simpl Ordered, node in |- *.
        simpl in |- *.
        ipso (conjoin &below, (conjoin &larger, (conjoin &lower, &kept))).
      }
      ipso
        (balancing.order
          (fun (x : &A) (y : &A) (z : &A) . Comparable.transitivity x y z)
          &l &c (remove &cmp &a &r) &on).
Qed.

(* removal.preservation.measurement *)
Theorem measurement
  : forall {A : Type} (cmp : A -> A -> Comparison) (a : A) (t : AVL A) .
      Measured t -> Measured (remove cmp a t).
Proof.
  intros A cmp a t.
  match &t with | Leaf | Node (l by IHl) c (r by IHr) n end per AVL.induction.
  - intro m.
    ipso I.
  - intro m.
    let proof m0 := simpl &m.
    match &m0 with | _ m' end.
    match &m' with | ml mr end.
    simpl in |- *.
    match (&cmp &a &c) with | | | end |- k.
    + modus ponens &IHl, &ml |- ml'.
      ipso (balancing.measurement (remove &cmp &a &l) &c &r &ml' &mr).
    + ipso (joining.preservation.measurement &l &r &ml &mr).
    + modus ponens &IHr, &mr |- mr'.
      ipso (balancing.measurement &l &c (remove &cmp &a &r) &ml &mr').
Qed.

(* The balance of [remove cmp a t] and its height are proved by one
 * induction, as for [insert]: the height bound keeps the two subtrees of
 * each rebuilt node within [balance]'s reach.
 *)
(* removal.preservation.invariance *)
Lemma invariance
  : forall {A : Type} (cmp : A -> A -> Comparison) (a : A) (t : AVL A) .
      Measured t -> Balanced t ->
        Balanced (remove cmp a t)
        /\ (height (remove cmp a t) = height t \/ ++ (height (remove cmp a t)) = height t).
Proof.
  intros A cmp a t.
  match &t with | Leaf | Node (l by IHl) c (r by IHr) h end per AVL.induction.
  - intros mt bt.
    ipso (conjoin I, (disjoin (Identity.reflexivity _), _)).
  - intros mt bt.
    let proof m0 := simpl &mt.
    match &m0 with | e m' end.
    match &m' with | ml mr end.
    let proof b0 := simpl &bt.
    match &b0 with | rel b' end.
    match &b' with | bl br end.
    simpl in |- *.
    match (&cmp &a &c) with | | | end |- k.
    (* [a] is removed from the left subtree. *)
    + modus ponens &IHl, &ml |- IHl'.
      modus ponens &IHl', &bl |- ih.
      match &ih with | bl' g end.
      let proof ml' := removal.preservation.measurement &cmp &a &l &ml.
      lemma near
        : height (remove &cmp &a &l) = height &r
          \/ height (remove &cmp &a &l) = ++ (height &r)
          \/ height &r = ++ (height (remove &cmp &a &l))
          \/ height (remove &cmp &a &l) = ++ (++ (height &r))
          \/ height &r = ++ (++ (height (remove &cmp &a &l))).
      {
        match &rel with | q | rel' end.
        - match &g with | k' | k' end.
          + ipso (disjoin (trans &k', &q), _).
          + ipso (disjoin _, (disjoin _, (disjoin (symm (trans &k', &q)), _))).
        - match &rel' with | q | q end.
          + match &g with | k' | k' end.
            * ipso (disjoin _, (disjoin (trans &k', &q), _)).
            * ipso (disjoin (Nat0.increment.injectivity (trans &k', &q)), _).
          + match &g with | k' | k' end.
            * leibniz <- &k' in &q.
              ipso (disjoin _, (disjoin _, (disjoin &q, _))).
            * leibniz (symm &k') in &q.
              ipso (disjoin _, (disjoin _, (disjoin _, (disjoin _, &q)))).
      }
      divide et impera.
      * ipso (balancing.balance (remove &cmp &a &l) &c &r &ml' &mr &bl' &br &near).
      * leibniz &e in |- *.
        ipso (balancing.shrinkage.left (remove &cmp &a &l) &c &r (height &l) &mr &br &rel &g).
    (* [a] is [c]: the node goes, and its two subtrees are joined. *)
    + divide et impera.
      * ipso (joining.preservation.balance &l &r &ml &mr &bl &br &rel).
      * leibniz &e in |- *.
        simpl join in |- *.
        match (pop &r) with | None | Some p end |- found.
        -- modus aequans (extraction.absence.specification &r), &found |- empty.
           leibniz &empty in |- *.
           let proof z : height (@AVL.Leaf &A) = Nat0.Zero := Identity.reflexivity _.
           leibniz &z in |- *.
           leibniz (Nat0.maximum.right.identity (height &l)) in |- *.
           ipso (disjoin _, (Identity.reflexivity _)).
        -- match &p with | m r' end.
           let proof inv := extraction.preservation.invariance &r &m &r' &mr &br &found.
           match &inv with | br' g end.
           ipso (balancing.shrinkage.right &l &m &r' (height &r) &ml &bl &rel &g).
    (* [a] is removed from the right subtree. *)
    + modus ponens &IHr, &mr |- IHr'.
      modus ponens &IHr', &br |- ih.
      match &ih with | br' g end.
      let proof mr' := removal.preservation.measurement &cmp &a &r &mr.
      lemma near
        : height &l = height (remove &cmp &a &r)
          \/ height &l = ++ (height (remove &cmp &a &r))
          \/ height (remove &cmp &a &r) = ++ (height &l)
          \/ height &l = ++ (++ (height (remove &cmp &a &r)))
          \/ height (remove &cmp &a &r) = ++ (++ (height &l)).
      {
        match &rel with | q | rel' end.
        - match &g with | k' | k' end.
          + ipso (disjoin (trans &q, (symm &k')), _).
          + ipso (disjoin _, (disjoin (trans &q, (symm &k')), _)).
        - match &rel' with | q | q end.
          + match &g with | k' | k' end.
            * leibniz <- &k' in &q.
              ipso (disjoin _, (disjoin &q, _)).
            * leibniz (symm &k') in &q.
              ipso (disjoin _, (disjoin _, (disjoin _, (disjoin &q, _)))).
          + match &g with | k' | k' end.
            * ipso (disjoin _, (disjoin _, (disjoin (trans &k', &q), _))).
            * ipso (disjoin (symm (Nat0.increment.injectivity (trans &k', &q))), _).
      }
      divide et impera.
      * ipso (balancing.balance &l &c (remove &cmp &a &r) &ml &mr' &bl &br' &near).
      * leibniz &e in |- *.
        ipso (balancing.shrinkage.right &l &c (remove &cmp &a &r) (height &r) &ml &bl &rel &g).
Qed.

(* removal.preservation.balance *)
Theorem balance
  : forall {A : Type} (cmp : A -> A -> Comparison) (a : A) (t : AVL A) .
      Measured t -> Balanced t -> Balanced (remove cmp a t).
Proof.
  intros A cmp a t m bt.
  match (removal.preservation.invariance &cmp &a &t &m &bt) with | kept _ end.
  ipso &kept.
Qed.

End preservation. (* removal.preservation *)

(* removal.shrinkage *)
Theorem shrinkage
  : forall {A : Type} (cmp : A -> A -> Comparison) (a : A) (t : AVL A) .
      Measured t -> Balanced t ->
      height (remove cmp a t) = height t \/ ++ (height (remove cmp a t)) = height t.
Proof.
  intros A cmp a t m bt.
  match (removal.preservation.invariance &cmp &a &t &m &bt) with | _ shrunk end.
  ipso &shrunk.
Qed.

(* [contains] and [remove] walk the same path, so the size laws read the
 * tree's shape alone and ask for no ordered tree.
 *)
Module size. (* removal.size *)

(* removal.size.shrinkage *)
Theorem shrinkage
  : forall {A : Type} (cmp : A -> A -> Comparison) (a : A) (t : AVL A) .
      contains cmp a t = true ->
      ++ (BinaryTree.size (to_tree (remove cmp a t))) = BinaryTree.size (to_tree t).
Proof.
  intros A cmp a t.
  match &t with | Leaf | Node (l by IHl) b (r by IHr) n end per AVL.induction.
  - intro e.
    simpl in &e.
    ex &e quodlibet.
  - intro e.
    simpl in &e.
    simpl in |- *.
    match (&cmp &a &b) with | | | end |- c.
    + leibniz (balancing.size (remove &cmp &a &l) &b &r) in |- *.
      simpl node in |- *.
      simpl in |- *.
      leibniz <- (&IHl &e) in |- *.
      leibniz (Nat0.increment.specification (BinaryTree.size (to_tree (remove &cmp &a &l))))
        in |- *.
      leibniz
        (Nat0.addition.associativity
          1 (BinaryTree.size (to_tree (remove &cmp &a &l))) (BinaryTree.size (to_tree &r)))
        in |- *.
      leibniz
        <- (Nat0.increment.specification
             (BinaryTree.size (to_tree (remove &cmp &a &l)) + BinaryTree.size (to_tree &r)))
        in |- *.
      quod idem est.
    + leibniz (joining.size &l &r) in |- *.
      quod idem est.
    + leibniz (balancing.size &l &b (remove &cmp &a &r)) in |- *.
      simpl node in |- *.
      simpl in |- *.
      leibniz <- (&IHr &e) in |- *.
      leibniz (Nat0.increment.specification (BinaryTree.size (to_tree (remove &cmp &a &r))))
        in |- *.
      leibniz
        (Nat0.addition.left.commutativity
          (BinaryTree.size (to_tree &l)) 1 (BinaryTree.size (to_tree (remove &cmp &a &r))))
        in |- *.
      leibniz
        <- (Nat0.increment.specification
             (BinaryTree.size (to_tree &l) + BinaryTree.size (to_tree (remove &cmp &a &r))))
        in |- *.
      quod idem est.
Qed.

(* removal.size.invariance *)
Theorem invariance
  : forall {A : Type} (cmp : A -> A -> Comparison) (a : A) (t : AVL A) .
      contains cmp a t = false ->
      BinaryTree.size (to_tree (remove cmp a t)) = BinaryTree.size (to_tree t).
Proof.
  intros A cmp a t.
  match &t with | Leaf | Node (l by IHl) b (r by IHr) n end per AVL.induction.
  - intro e.
    simpl in |- *.
    quod idem est.
  - intro e.
    simpl in &e.
    simpl in |- *.
    match (&cmp &a &b) with | | | end |- c.
    + leibniz (balancing.size (remove &cmp &a &l) &b &r) in |- *.
      simpl node in |- *.
      simpl in |- *.
      leibniz (&IHl &e) in |- *.
      quod idem est.
    + ex &e quodlibet.
    + leibniz (balancing.size &l &b (remove &cmp &a &r)) in |- *.
      simpl node in |- *.
      simpl in |- *.
      leibniz (&IHr &e) in |- *.
      quod idem est.
Qed.

End size. (* removal.size *)

End removal. (* removal *)

End AVL. (* AVL *)

Abbreviation AVL := AVL.T.
