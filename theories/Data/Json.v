(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

From JW Require Import Core.All.
From JW Require Import Data.Base.Bool.
From JW Require Import Data.Collection.List.
From JW Require Import Data.Number.Binary.SignedBin.
From JW Require Import Data.Option.
From JW Require Import Data.Product.
From JW Require Import Data.Text.Utf8Str.
From JW Require Import Tactics.Equation.

Local Unset Elimination Schemes.

Module Json. (* Json *)

(* A JSON value. A number [Number m x] is the exact decimal [m] times ten
 * to the power [x], so one value has several terms. An object lists its
 * members in order and may repeat a name.
 *)
Inductive T : Type :=
  | Null    : T
  | Boolean : Bool -> T
  | Number  : SignedBin -> SignedBin -> T
  | String  : Utf8Str -> T
  | Array   : List T -> T
  | Object  : List (Utf8Str * T) -> T.

Abbreviation Json := T.

Local Open Scope jw_list_scope.

(* The eliminator that [match ... per] takes, written out. An array's step
 * takes [P] of every element and an object's step [P] of every member's
 * value, each as one [List.All] stated right after the list.
 *)
Definition induction
  : forall (P : Json -> Prop) .
      P Json.Null ->
      (forall (b : Bool) . P (Json.Boolean b)) ->
      (forall (mantissa : SignedBin) (exponent : SignedBin) .
        P (Json.Number mantissa exponent)) ->
      (forall (s : Utf8Str) . P (Json.String s)) ->
      (forall (l : List Json) . List.All P l -> P (Json.Array l)) ->
      (forall (l : List (Utf8Str * Json)) .
        List.All (fun (p : Utf8Str * Json) . P (Product.second p)) l -> P (Json.Object l)) ->
      (forall (j : Json) . P j)
  := fun (P : Json -> Prop) (null : P Json.Null)
      (boolean : forall (b : Bool) . P (Json.Boolean b))
      (number : forall (mantissa : SignedBin) (exponent : SignedBin) .
        P (Json.Number mantissa exponent))
      (string : forall (s : Utf8Str) . P (Json.String s))
      (array : forall (l : List Json) . List.All P l -> P (Json.Array l))
      (object : forall (l : List (Utf8Str * Json)) .
        List.All (fun (p : Utf8Str * Json) . P (Product.second p)) l -> P (Json.Object l)) .
      fix go (j : Json) : P j :=
        match j with
        | Json.Null                     => null
        | Json.Boolean b                => boolean b
        | Json.Number mantissa exponent => number mantissa exponent
        | Json.String s                 => string s
        | Json.Array l                  =>
            array l
              ((fix all (l : List Json) : List.All P l :=
                  match l with
                  | []      => I
                  | a :: l' => Conjunction.introduction (go a) (all l')
                  end) l)
        | Json.Object l                 =>
            object l
              ((fix all (l : List (Utf8Str * Json))
                  : List.All (fun (p : Utf8Str * Json) . P (Product.second p)) l :=
                  match l with
                  | []      => I
                  | p :: l' =>
                      Conjunction.introduction
                        (match p as q return P (Product.second q) with
                         | Product.introduction _ v => go v
                         end)
                        (all l')
                  end) l)
        end.

(* [Json -> Bool] *)
Definition is_null := fun (j : Json) .
  match j with
  | Json.Null => true
  | _         => false
  end.

(* [Json -> Option Bool] *)
Definition boolean := fun (j : Json) .
  match j with
  | Json.Boolean b => Some b
  | _              => None
  end.

(* The mantissa first, the exponent of ten second. *)
(* [Json -> Option (SignedBin * SignedBin)] *)
Definition number := fun (j : Json) .
  match j with
  | Json.Number mantissa exponent => Some (mantissa, exponent)%product
  | _                             => None
  end.

(* [Json -> Option Utf8Str] *)
Definition string := fun (j : Json) .
  match j with
  | Json.String s => Some s
  | _             => None
  end.

(* [Json -> Option (List Json)] *)
Definition array := fun (j : Json) .
  match j with
  | Json.Array l => Some l
  | _            => None
  end.

(* [Json -> Option (List (Utf8Str * Json))] *)
Definition object := fun (j : Json) .
  match j with
  | Json.Object l => Some l
  | _             => None
  end.

Module null. (* null *)

(* null.specification *)
Theorem specification
  : forall (j : Json) . is_null j = true <-> j = Json.Null.
Proof.
  intro j.
  divide et impera.
  - intro e.
    match &j with | | b | mantissa exponent | s | l | l end.
    + quod idem est.
    + simpl in &e.
      ex &e quodlibet.
    + simpl in &e.
      ex &e quodlibet.
    + simpl in &e.
      ex &e quodlibet.
    + simpl in &e.
      ex &e quodlibet.
    + simpl in &e.
      ex &e quodlibet.
  - intro e.
    leibniz &e in |- *.
    simpl in |- *.
    quod idem est.
Qed.

End null. (* null *)

Module boolean. (* boolean *)

(* boolean.injectivity *)
Theorem injectivity
  : forall {b1 : Bool} {b2 : Bool} . Json.Boolean b1 = Json.Boolean b2 -> b1 = b2.
Proof.
  intros b1 b2 e.
  congru boolean, e |- e'.
  simpl in e'.
  ipso (Option.some.injectivity e').
Qed.

(* boolean.specification *)
Theorem specification
  : forall (j : Json) (b : Bool) . boolean j = Some b <-> j = Json.Boolean b.
Proof.
  intros j b.
  divide et impera.
  - intro e.
    match &j with | | b' | mantissa exponent | s | l | l end.
    + simpl in &e.
      ex &e quodlibet.
    + simpl in &e.
      leibniz (Option.some.injectivity &e) in |- *.
      quod idem est.
    + simpl in &e.
      ex &e quodlibet.
    + simpl in &e.
      ex &e quodlibet.
    + simpl in &e.
      ex &e quodlibet.
    + simpl in &e.
      ex &e quodlibet.
  - intro e.
    leibniz &e in |- *.
    simpl in |- *.
    quod idem est.
Qed.

End boolean. (* boolean *)

Module number. (* number *)

(* number.injectivity *)
Theorem injectivity
  : forall {mantissa1 : SignedBin} {exponent1 : SignedBin}
      {mantissa2 : SignedBin} {exponent2 : SignedBin} .
      Json.Number mantissa1 exponent1 = Json.Number mantissa2 exponent2
      -> mantissa1 = mantissa2 /\ exponent1 = exponent2.
Proof.
  intros mantissa1 exponent1 mantissa2 exponent2 e.
  congru number, e |- e'.
  simpl in e'.
  ipso (Product.introduction.injectivity (Option.some.injectivity e')).
Qed.

(* number.specification *)
Theorem specification
  : forall (j : Json) (mantissa : SignedBin) (exponent : SignedBin) .
      number j = Some (mantissa, exponent)%product <-> j = Json.Number mantissa exponent.
Proof.
  intros j mantissa exponent.
  divide et impera.
  - intro e.
    match &j with | | b | mantissa' exponent' | s | l | l end.
    + simpl in &e.
      ex &e quodlibet.
    + simpl in &e.
      ex &e quodlibet.
    + simpl in &e.
      match (Product.introduction.injectivity (Option.some.injectivity &e)) with
      | em ex
      end.
      leibniz &em, &ex in |- *.
      quod idem est.
    + simpl in &e.
      ex &e quodlibet.
    + simpl in &e.
      ex &e quodlibet.
    + simpl in &e.
      ex &e quodlibet.
  - intro e.
    leibniz &e in |- *.
    simpl in |- *.
    quod idem est.
Qed.

End number. (* number *)

Module string. (* string *)

(* string.injectivity *)
Theorem injectivity
  : forall {s1 : Utf8Str} {s2 : Utf8Str} . Json.String s1 = Json.String s2 -> s1 = s2.
Proof.
  intros s1 s2 e.
  congru string, e |- e'.
  simpl in e'.
  ipso (Option.some.injectivity e').
Qed.

(* string.specification *)
Theorem specification
  : forall (j : Json) (s : Utf8Str) . string j = Some s <-> j = Json.String s.
Proof.
  intros j s.
  divide et impera.
  - intro e.
    match &j with | | b | mantissa exponent | s' | l | l end.
    + simpl in &e.
      ex &e quodlibet.
    + simpl in &e.
      ex &e quodlibet.
    + simpl in &e.
      ex &e quodlibet.
    + simpl in &e.
      leibniz (Option.some.injectivity &e) in |- *.
      quod idem est.
    + simpl in &e.
      ex &e quodlibet.
    + simpl in &e.
      ex &e quodlibet.
  - intro e.
    leibniz &e in |- *.
    simpl in |- *.
    quod idem est.
Qed.

End string. (* string *)

Module array. (* array *)

(* array.injectivity *)
Theorem injectivity
  : forall {l1 : List Json} {l2 : List Json} . Json.Array l1 = Json.Array l2 -> l1 = l2.
Proof.
  intros l1 l2 e.
  congru array, e |- e'.
  simpl in e'.
  ipso (Option.some.injectivity e').
Qed.

(* array.specification *)
Theorem specification
  : forall (j : Json) (l : List Json) . array j = Some l <-> j = Json.Array l.
Proof.
  intros j l.
  divide et impera.
  - intro e.
    match &j with | | b | mantissa exponent | s | l' | l' end.
    + simpl in &e.
      ex &e quodlibet.
    + simpl in &e.
      ex &e quodlibet.
    + simpl in &e.
      ex &e quodlibet.
    + simpl in &e.
      ex &e quodlibet.
    + simpl in &e.
      leibniz (Option.some.injectivity &e) in |- *.
      quod idem est.
    + simpl in &e.
      ex &e quodlibet.
  - intro e.
    leibniz &e in |- *.
    simpl in |- *.
    quod idem est.
Qed.

End array. (* array *)

Module object. (* object *)

(* object.injectivity *)
Theorem injectivity
  : forall {l1 : List (Utf8Str * Json)} {l2 : List (Utf8Str * Json)} .
      Json.Object l1 = Json.Object l2 -> l1 = l2.
Proof.
  intros l1 l2 e.
  congru object, e |- e'.
  simpl in e'.
  ipso (Option.some.injectivity e').
Qed.

(* object.specification *)
Theorem specification
  : forall (j : Json) (l : List (Utf8Str * Json)) . object j = Some l <-> j = Json.Object l.
Proof.
  intros j l.
  divide et impera.
  - intro e.
    match &j with | | b | mantissa exponent | s | l' | l' end.
    + simpl in &e.
      ex &e quodlibet.
    + simpl in &e.
      ex &e quodlibet.
    + simpl in &e.
      ex &e quodlibet.
    + simpl in &e.
      ex &e quodlibet.
    + simpl in &e.
      ex &e quodlibet.
    + simpl in &e.
      leibniz (Option.some.injectivity &e) in |- *.
      quod idem est.
  - intro e.
    leibniz &e in |- *.
    simpl in |- *.
    quod idem est.
Qed.

End object. (* object *)

End Json. (* Json *)

Abbreviation Json := Json.T.
