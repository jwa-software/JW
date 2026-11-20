(* SPDX-FileCopyrightText: Junzhe Wang <research@junzhewang.de>
 * SPDX-License-Identifier: MIT
 *)

open JW

(* The extracted numbers are unary, so OCaml integers go in and come out
   through these conversions. *)
let rec nat0 k = if k = 0 then Nat0.Zero else Nat0.inc (nat0 (k - 1))

let rec int_of_nat = function
  | Nat.One -> 1
  | Nat.Successor n -> 1 + int_of_nat n
;;

let int_of_nat0 = function
  | Nat0.Zero -> 0
  | Nat0.Positive p -> int_of_nat p
;;

(* [JW] has a [List] module of its own, which [open JW] puts in front of
   OCaml's. *)
let ints l = Stdlib.List.map int_of_nat0 l
let check name ok = if not ok then failwith ("extraction test failed: " ^ name)

let () =
  let cmp = Nat0.compare in
  let s =
    SortedSet.insert
      cmp
      (nat0 2)
      (SortedSet.insert
         cmp
         (nat0 3)
         (SortedSet.insert cmp (nat0 1) (SortedSet.empty cmp)))
  in
  check "SortedSet.to_list" (ints (SortedSet.to_list cmp s) = [ 1; 2; 3 ]);
  check "SortedSet.contains" (SortedSet.contains cmp (nat0 2) s);
  check "SortedSet.contains, absent" (not (SortedSet.contains cmp (nat0 4) s));
  let t = SortedSet.remove cmp (nat0 2) s in
  check "SortedSet.remove" (ints (SortedSet.to_list cmp t) = [ 1; 3 ]);
  check "SortedSet.size" (int_of_nat0 (SortedSet.size cmp t) = 2);
  let sum = UInt8.add (UInt8.from_nat0 (nat0 200)) (UInt8.from_nat0 (nat0 100)) in
  check "UInt8.add" (int_of_nat0 (UInt8.to_nat0 sum) = 44);
  check
    "Kleene3.and"
    (Kleene3.coq_and Kleene3.Coq_unknown Kleene3.Coq_false = Kleene3.Coq_false);
  check
    "Kleene3.or"
    (Kleene3.coq_or Kleene3.Coq_unknown Kleene3.Coq_true = Kleene3.Coq_true);
  check "bool" (Bool.coq_and true false = false && Bool.coq_or false true = true);
  check
    "option"
    (int_of_nat0 (Option.unwrap_or (nat0 0) (Some (nat0 5))) = 5
     && int_of_nat0 (Option.unwrap_or (nat0 7) None) = 7);
  check "product" (int_of_nat0 (Product.first (nat0 1, nat0 2)) = 1);
  check "product, second" (int_of_nat0 (Product.second (nat0 1, nat0 2)) = 2);
  check "list" (ints (List.concat [ nat0 1 ] [ nat0 2; nat0 3 ]) = [ 1; 2; 3 ])
;;
