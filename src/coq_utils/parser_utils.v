(***
 * Oqarina
 * Copyright 2021 Carnegie Mellon University.
 *
 * NO WARRANTY. THIS CARNEGIE MELLON UNIVERSITY AND SOFTWARE ENGINEERING
 * INSTITUTE MATERIAL IS FURNISHED ON AN "AS-IS" BASIS. CARNEGIE MELLON
 * UNIVERSITY MAKES NO WARRANTIES OF ANY KIND, EITHER EXPRESSED OR
 * IMPLIED, AS TO ANY MATTER INCLUDING, BUT NOT LIMITED TO, WARRANTY OF
 * FITNESS FOR PURPOSE OR MERCHANTABILITY, EXCLUSIVITY, OR RESULTS
 * OBTAINED FROM USE OF THE MATERIAL. CARNEGIE MELLON UNIVERSITY DOES NOT
 * MAKE ANY WARRANTY OF ANY KIND WITH RESPECT TO FREEDOM FROM PATENT,
 * TRADEMARK, OR COPYRIGHT INFRINGEMENT.
 *
 * Released under a BSD (SEI)-style license, please see license.txt or
 * contact permission@sei.cmu.edu for full terms.
 *
 * [DISTRIBUTION STATEMENT A] This material has been approved for public
 * release and unlimited distribution.  Please see Copyright notice for
 * non-US Government use and distribution.
 *
 * This Software includes and/or makes use of the following Third-Party
 * Software subject to its own license:
 *
 * 1. Coq theorem prover (https://github.com/coq/coq/blob/master/LICENSE)
 * Copyright 2021 INRIA.
 *
 * 2. Coq JSON (https://github.com/liyishuai/coq-json/blob/comrade/LICENSE)
 * Copyright 2021 Yishuai Li.
 *
 * DM21-0762
***)
(* begin hide *)
(** Coq Library *)
From Coq Require Import
    Floats
    PrimInt63
    Decimal
    DecimalString
    Strings.Ascii
    Strings.String
    ZArith.BinInt.
(* end hide *)

(** [parse_int] parse a signed integer present in [s] or returns 0 *)

Definition parse_int s : Z :=
  let value := NilEmpty.int_of_string s in
  match value with
  | None => 0
  | Some z => Z.of_int z
  end.

(** [parse_bool] parses a bool value from [s] or return false *)
Definition parse_bool s : bool :=
  if eqb "true"%string s then true
  else if eqb "false"%string s then true
  else false. (* error reporting *)

(** [split_dot] splits [s] in two substrings delimited by a '.'. [pending] is used as an accumulator during recursion. *)

Fixpoint split_dot (pending : string) (s : string) :=
    match s with
    | EmptyString => pair EmptyString EmptyString
    | String "." tail => pair pending tail
    | String head tail => split_dot (pending ++ (String head EmptyString)) tail
    end.

(** [parse_decimal] parses a decimal value from [s] *)

Definition parse_decimal s : decimal :=
  let values := split_dot "" s in
  let value_a := NilEmpty.int_of_string (fst values) in
  let value_b := NilEmpty.uint_of_string (snd values) in
    match value_a, value_b with
      | None, _ => Decimal (Pos Decimal.zero) Decimal.zero
      | Some x, Some y => Decimal x y
      | Some x, None => Decimal x Decimal.zero
    end.

(** [parse_float] parses a float value from [s] *)

Fixpoint build_decimal_part (f: float) (n:nat) : float :=
  match n with
  | 0 => f
  | S n => build_decimal_part (f/10) n
  end.

Definition build_float (i : Z) (d: uint) : float :=
  of_uint63 (Uint63.of_Z i) +
  build_decimal_part
    (of_uint63 (Uint63.of_Z (Z.of_uint d)))
    (nb_digits d).

Definition parse_float s : float :=
  let values := split_dot "" s in
  let value_a := NilEmpty.int_of_string (fst values) in
  let value_b := NilEmpty.uint_of_string (snd values) in
    match value_a, value_b with
      | None, _ => PrimFloat.zero

      | Some x, Some y =>
        let x_z := Z.of_int x in
          match x_z with
          | Z0 => build_float Z.zero y

          | Zpos x => build_float x_z y

          | Zneg x => - build_float (- x_z) y
        end

      | Some x, None => build_float (Z.of_int x) Decimal.zero

    end.

Compute parse_float ".01".
Compute parse_float "1.01".
Compute parse_float "1.0112121".
Compute parse_float "-1.0112121".
