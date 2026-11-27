(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

From JW Require Import Core.All.
From JW Require Import Data.Base.Bool.
From JW Require Import Data.Collection.List.
From JW Require Import Data.Comparable.
From JW Require Import Data.Discernible.
From JW Require Import Data.Machine.Bit.
From JW Require Import Data.Machine.Byte.
From JW Require Import Data.Number.Binary.Bin.
From JW Require Import Data.Number.Binary.SignedBin.
From JW Require Import Data.Option.
From JW Require Import Data.Product.
From JW Require Import Data.Text.Utf8.
From JW Require Import Data.Text.Utf8Str.
From JW Require Import Tactics.Equation.
From JW Require Import Tactics.Modus.

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

(* The same term, not the same value: a number in two forms differs from
 * itself, and so does an object from the same members in another order.
 *)
(* [Json -> Json -> Bool] *)
Fixpoint test (j : Json) (k : Json) : Bool :=
  match j, k with
  | Json.Null,         Json.Null         => true
  | Json.Boolean b1,   Json.Boolean b2   => Bool.test b1 b2
  | Json.Number m1 x1, Json.Number m2 x2 => (SignedBin.eq m1 m2 && SignedBin.eq x1 x2)%bool
  | Json.String s1,    Json.String s2    => Utf8Str.eq s1 s2
  | Json.Array l1,     Json.Array l2     => List.test test l1 l2
  | Json.Object l1,    Json.Object l2    => List.test (Product.test Utf8Str.eq test) l1 l2
  | _,                 _                 => false
  end.

(* [Json -> Json -> Bool] *)
Abbreviation equivalent := Discernible.equivalent.

(* [Json -> Json -> Bool] *)
Abbreviation discern := Discernible.discern.

(* A character is matched by its byte, so the bits are written as such. *)
Local Open Scope jw_bit_scope.

(* [s] between quotation marks, each character escaped as RFC 8259 asks: the
 * quotation mark, the reverse solidus and the control characters U+0000 to
 * U+001F, the five that have a short form by it and the others as [\u00xx].
 *)
(* [Utf8Str -> Utf8Str] *)
Definition quote := fun (s : Utf8Str) .
  ("""" ++
   List.fold_right
     (fun (c : Utf8) (rest : Utf8Str) .
       (match c with
        | Utf8.OneByte (Byte.introduction 0 0 1 0 0 0 1 0) _ => "\"""
        | Utf8.OneByte (Byte.introduction 0 1 0 1 1 1 0 0) _ => "\\"
        | Utf8.OneByte (Byte.introduction 0 0 0 0 1 0 0 0) _ => "\b"
        | Utf8.OneByte (Byte.introduction 0 0 0 0 1 0 0 1) _ => "\t"
        | Utf8.OneByte (Byte.introduction 0 0 0 0 1 0 1 0) _ => "\n"
        | Utf8.OneByte (Byte.introduction 0 0 0 0 1 1 0 0) _ => "\f"
        | Utf8.OneByte (Byte.introduction 0 0 0 0 1 1 0 1) _ => "\r"
        | Utf8.OneByte (Byte.introduction 0 0 0 0 0 0 0 0) _ => "\u0000"
        | Utf8.OneByte (Byte.introduction 0 0 0 0 0 0 0 1) _ => "\u0001"
        | Utf8.OneByte (Byte.introduction 0 0 0 0 0 0 1 0) _ => "\u0002"
        | Utf8.OneByte (Byte.introduction 0 0 0 0 0 0 1 1) _ => "\u0003"
        | Utf8.OneByte (Byte.introduction 0 0 0 0 0 1 0 0) _ => "\u0004"
        | Utf8.OneByte (Byte.introduction 0 0 0 0 0 1 0 1) _ => "\u0005"
        | Utf8.OneByte (Byte.introduction 0 0 0 0 0 1 1 0) _ => "\u0006"
        | Utf8.OneByte (Byte.introduction 0 0 0 0 0 1 1 1) _ => "\u0007"
        | Utf8.OneByte (Byte.introduction 0 0 0 0 1 0 1 1) _ => "\u000b"
        | Utf8.OneByte (Byte.introduction 0 0 0 0 1 1 1 0) _ => "\u000e"
        | Utf8.OneByte (Byte.introduction 0 0 0 0 1 1 1 1) _ => "\u000f"
        | Utf8.OneByte (Byte.introduction 0 0 0 1 0 0 0 0) _ => "\u0010"
        | Utf8.OneByte (Byte.introduction 0 0 0 1 0 0 0 1) _ => "\u0011"
        | Utf8.OneByte (Byte.introduction 0 0 0 1 0 0 1 0) _ => "\u0012"
        | Utf8.OneByte (Byte.introduction 0 0 0 1 0 0 1 1) _ => "\u0013"
        | Utf8.OneByte (Byte.introduction 0 0 0 1 0 1 0 0) _ => "\u0014"
        | Utf8.OneByte (Byte.introduction 0 0 0 1 0 1 0 1) _ => "\u0015"
        | Utf8.OneByte (Byte.introduction 0 0 0 1 0 1 1 0) _ => "\u0016"
        | Utf8.OneByte (Byte.introduction 0 0 0 1 0 1 1 1) _ => "\u0017"
        | Utf8.OneByte (Byte.introduction 0 0 0 1 1 0 0 0) _ => "\u0018"
        | Utf8.OneByte (Byte.introduction 0 0 0 1 1 0 0 1) _ => "\u0019"
        | Utf8.OneByte (Byte.introduction 0 0 0 1 1 0 1 0) _ => "\u001a"
        | Utf8.OneByte (Byte.introduction 0 0 0 1 1 0 1 1) _ => "\u001b"
        | Utf8.OneByte (Byte.introduction 0 0 0 1 1 1 0 0) _ => "\u001c"
        | Utf8.OneByte (Byte.introduction 0 0 0 1 1 1 0 1) _ => "\u001d"
        | Utf8.OneByte (Byte.introduction 0 0 0 1 1 1 1 0) _ => "\u001e"
        | Utf8.OneByte (Byte.introduction 0 0 0 1 1 1 1 1) _ => "\u001f"
        | _ => Utf8Str.from_list (c :: [])%list
        end) ++ rest)
     Utf8Str.empty
     (Utf8Str.to_list s)
   ++ """")%u8.

(* The JSON text of [j], with no whitespace: an array's elements and an
 * object's members in their order, a number as its mantissa followed, when
 * the exponent is not zero, by [e] and the exponent.
 *)
(* [Json -> Utf8Str] *)
Fixpoint to_utf8_str (j : Json) : Utf8Str :=
  let signed := fun (n : SignedBin) .
    match n with
    | SignedBin.Negative p => ("-" ++ Utf8Str.from_decimal (Bin.to_decimal p))%u8
    | SignedBin.Zero       => "0"%u8
    | SignedBin.Positive p => Utf8Str.from_decimal (Bin.to_decimal p)
    end in
  match j with
  | Json.Null           => "null"%u8
  | Json.Boolean b      =>
      match b with
      | true  => "true"%u8
      | false => "false"%u8
      end
  | Json.Number m x     =>
      match x with
      | SignedBin.Zero => signed m
      | _              => (signed m ++ "e" ++ signed x)%u8
      end
  | Json.String s       => quote s
  | Json.Array []       => "[]"%u8
  | Json.Array (a :: l) =>
      ("[" ++ to_utf8_str a ++
       (fix others (l : List Json) : Utf8Str :=
          match l with
          | []      => "]"%u8
          | b :: l' => ("," ++ to_utf8_str b ++ others l')%u8
          end) l)%u8
  | Json.Object []       => "{}"%u8
  | Json.Object (p :: l) =>
      ("{" ++
       match p with
       | Product.introduction n v => (quote n ++ ":" ++ to_utf8_str v)%u8
       end ++
       (fix others (l : List (Utf8Str * Json)) : Utf8Str :=
          match l with
          | []      => "}"%u8
          | q :: l' =>
              ("," ++
               match q with
               | Product.introduction n v => (quote n ++ ":" ++ to_utf8_str v)%u8
               end ++
               others l')%u8
          end) l)%u8
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

Module test. (* test *)

(* test.reflection *)
Theorem reflection
  : forall (j : Json) (k : Json) . test j k = true <-> j = k.
Proof.
  intro j.
  match &j with
  | Null | Boolean b | Number mantissa exponent | String s | Array l all | Object l all
  end per Json.induction.
  - intro k.
    match &k with | | b' | mantissa' exponent' | s' | l' | l' end; simpl in |- *.
    + divide et impera; intro e; quod idem est.
    + divide et impera; intro e; ex &e quodlibet.
    + divide et impera; intro e; ex &e quodlibet.
    + divide et impera; intro e; ex &e quodlibet.
    + divide et impera; intro e; ex &e quodlibet.
    + divide et impera; intro e; ex &e quodlibet.
  - intro k.
    match &k with | | b' | mantissa' exponent' | s' | l' | l' end; simpl in |- *.
    + divide et impera; intro e; ex &e quodlibet.
    + let proof rb := Bool.test.reflection &b &b'.
      divide et impera.
      * intro e.
        leibniz (modus aequans &rb, &e) in |- *.
        quod idem est.
      * intro e.
        ipso (modus aequans &rb, (boolean.injectivity &e)).
    + divide et impera; intro e; ex &e quodlibet.
    + divide et impera; intro e; ex &e quodlibet.
    + divide et impera; intro e; ex &e quodlibet.
    + divide et impera; intro e; ex &e quodlibet.
  - intro k.
    match &k with | | b' | mantissa' exponent' | s' | l' | l' end; simpl in |- *.
    + divide et impera; intro e; ex &e quodlibet.
    + divide et impera; intro e; ex &e quodlibet.
    + let proof rm : SignedBin.eq &mantissa &mantissa' = true <-> &mantissa = &mantissa'
        := Comparable.comparison.equality.reflection &mantissa &mantissa'.
      let proof rx : SignedBin.eq &exponent &exponent' = true <-> &exponent = &exponent'
        := Comparable.comparison.equality.reflection &exponent &exponent'.
      match (SignedBin.eq &mantissa &mantissa') with | | end.
      * simpl in |- *.
        let proof em := modus aequans &rm, (Identity.reflexivity true).
        divide et impera.
        -- intro e.
           let proof ee := modus aequans &rx, &e.
           leibniz &em, &ee in |- *.
           quod idem est.
        -- intro e.
           match (number.injectivity &e) with | _ ee end.
           ipso (modus aequans &rx, &ee).
      * simpl in |- *.
        divide et impera.
        -- intro e.
           ex &e quodlibet.
        -- intro e.
           match (number.injectivity &e) with | em _ end.
           let proof t := modus aequans &rm, &em.
           ex &t quodlibet.
    + divide et impera; intro e; ex &e quodlibet.
    + divide et impera; intro e; ex &e quodlibet.
    + divide et impera; intro e; ex &e quodlibet.
  - intro k.
    match &k with | | b' | mantissa' exponent' | s' | l' | l' end; simpl in |- *.
    + divide et impera; intro e; ex &e quodlibet.
    + divide et impera; intro e; ex &e quodlibet.
    + divide et impera; intro e; ex &e quodlibet.
    + let proof rs : Utf8Str.eq &s &s' = true <-> &s = &s'
        := Comparable.comparison.equality.reflection &s &s'.
      divide et impera.
      * intro e.
        leibniz (modus aequans &rs, &e) in |- *.
        quod idem est.
      * intro e.
        ipso (modus aequans &rs, (string.injectivity &e)).
    + divide et impera; intro e; ex &e quodlibet.
    + divide et impera; intro e; ex &e quodlibet.
  - intro k.
    match &k with | | b' | mantissa' exponent' | s' | l' | l' end; simpl in |- *.
    + divide et impera; intro e; ex &e quodlibet.
    + divide et impera; intro e; ex &e quodlibet.
    + divide et impera; intro e; ex &e quodlibet.
    + divide et impera; intro e; ex &e quodlibet.
    + let proof r := List.test.local.reflection test &l &all &l'.
      divide et impera.
      * intro e.
        leibniz (modus aequans &r, &e) in |- *.
        quod idem est.
      * intro e.
        ipso (modus aequans &r, (array.injectivity &e)).
    + divide et impera; intro e; ex &e quodlibet.
  - intro k.
    match &k with | | b' | mantissa' exponent' | s' | l' | l' end; simpl in |- *.
    + divide et impera; intro e; ex &e quodlibet.
    + divide et impera; intro e; ex &e quodlibet.
    + divide et impera; intro e; ex &e quodlibet.
    + divide et impera; intro e; ex &e quodlibet.
    + divide et impera; intro e; ex &e quodlibet.
    + lemma members
        : List.All
            (fun (p : Utf8Str * Json) .
              forall (q : Utf8Str * Json) . Product.test Utf8Str.eq test p q = true <-> p = q)
            &l.
      {
        ipso
          (List.quantification.all.monotonicity
            (fun (p : Utf8Str * Json)
                (h : forall (k : Json) .
                       test (Product.second p) k = true <-> Product.second p = k) .
              Product.test.local.reflection Utf8Str.eq test p
                (fun (n : Utf8Str) .
                  Comparable.comparison.equality.reflection (Product.first p) n)
                h)
            &all).
      }
      let proof r
        := List.test.local.reflection (Product.test Utf8Str.eq test) &l &members &l'.
      divide et impera.
      * intro e.
        leibniz (modus aequans &r, &e) in |- *.
        quod idem est.
      * intro e.
        ipso (modus aequans &r, (object.injectivity &e)).
Qed.

End test. (* test *)

Instance discernible
  : Discernible test :=
  {| Discernible.reflection := test.reflection |}.

End Json. (* Json *)

Abbreviation Json := Json.T.

Existing Instance Json.discernible.
