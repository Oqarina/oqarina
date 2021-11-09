(* begin hide *)
(** Coq Library *)
From Coq Require Import
    Decimal
    DecimalString
    Strings.Ascii
    Strings.String
    ZArith.BinInt.
(* end hide *)

(** [parse_int] parse a signed integer present in [s] or returns 0*)

Definition parse_int s : Z :=
  let value := NilEmpty.int_of_string s in
  match value with
  | None => 0
  | Some z => Z.of_int z
  end.
(** [parse_bool] parses a bool value from [s] or return false *)
Definition parse_bool s : bool :=
  if eqb "true" s then true
  else if eqb "false" s then true
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
