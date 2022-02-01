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

(** Hand-written lexer for AADL.

Note: this file is based on the `coq-minicalc` example from the Menhir distribution.
Original author is Pierre Letouzey, 2019. The code was released under the CC0 licence.

*)

Require Import BinNat Ascii String.
Require Import List.
Import ListNotations. (* from List *)

Require Import Oqarina.AADL.atin_frontend.atin_parser.
Import MenhirLibParser.Inter.

Open Scope char_scope.
Open Scope bool_scope.

(** No such thing as an empty buffer, instead we use
    an infinite stream of EOF *)

CoFixpoint TheEnd : buffer := Buf_cons (EOF tt) TheEnd.

Fixpoint ntail n s :=
  match n, s with
  | 0, _ => s
  | _, EmptyString => s
  | S n, String _ s => ntail n s
  end.

(** Comparison on characters *)

Definition ascii_eqb c c' := (N_of_ascii c =? N_of_ascii c')%N.
Definition ascii_leb c c' := (N_of_ascii c <=? N_of_ascii c')%N.

Infix "<=?" := ascii_leb : char_scope.

Definition is_digit c := (("0" <=? c) && (c <=? "9"))%char.

Definition is_alpha c :=
  ((("a" <=? c) && (c <=? "z")) ||
   (("A" <=? c) && (c <=? "Z")) ||
   (c =? "_"))%char.

Fixpoint identsize s :=
  match s with
  | EmptyString => 0
  | String c s =>
    if is_alpha c || is_digit c then S (identsize s)
    else 0
  end.

Fixpoint readnum acc s :=
  match s with
  | String "0" s => readnum (acc*10) s
  | String "1" s => readnum (acc*10+1) s
  | String "2" s => readnum (acc*10+2) s
  | String "3" s => readnum (acc*10+3) s
  | String "4" s => readnum (acc*10+4) s
  | String "5" s => readnum (acc*10+5) s
  | String "6" s => readnum (acc*10+6) s
  | String "7" s => readnum (acc*10+7) s
  | String "8" s => readnum (acc*10+8) s
  | String "9" s => readnum (acc*10+9) s
  | _ => (acc,s)
  end.

Fixpoint which_keyword (s : string) (kw : list string) :=
  match kw with
  | nil => (0, EmptyString)
  | h :: t => if prefix h s then (String.length h, h) else which_keyword s t
  end.

Fixpoint is_keyword (s : string) (kw : list string) :=
  match kw with
  | nil => false
  | h :: t => if prefix h s then true else is_keyword s t
  end.

(** As a general warning, the lexer relies on the order of declaration and will return the first entity that matches.
Double check the order below to avoid ambiguity.

Also, ids with a space, e.g. "virtual bus", won't be lex'd correctly.
*)

Definition AADL_Component_Category : list string := [
  "abstract"%string ; "bus"%string ; "data"%string ;
	"device"%string ; "memory"%string ; "processor"%string ; "process"%string ; "subprogram"%string ;
	"subprogram group"%string ; "system"%string ; "thread group"%string ;
	"thread"%string ; "virtual bus"%string ; "virtual processor"%string
].

Definition AADL_Direction_Type : list string := [
  "in"%string ; "out"%string ; "in out"%string
].

Definition AADL_Feature_Category : list string := [
  "dataPort"%string ; "eventPort"%string ; "eventDataPort"%string ; "parameter"%string ;
  "busAccess"%string ; "dataAccess"%string ; "subprogramAccess"%string ; "subprogramGroupAccess"%string ;
  "featureGroup"%string ; "abstractFeature"%string
].

Fixpoint lex_string_cpt n s :=
  match n with
  | 0 => None
  | S n =>
    match s with
    | EmptyString => Some TheEnd
    | String c s' =>
      match c with
      | " " => lex_string_cpt n s'
      | "009" => lex_string_cpt n s' (* \t *)
      | "010" => lex_string_cpt n s' (* \n *)
      | "013" => lex_string_cpt n s' (* \r *)
      | "{" => option_map (Buf_cons (LEFT_BRACE tt)) (lex_string_cpt n s')
      | "}" => option_map (Buf_cons (RIGHT_BRACE tt)) (lex_string_cpt n s')
  (*    | "(" => option_map (Buf_cons (LPAREN tt)) (lex_string_cpt n s')
      | ")" => option_map (Buf_cons (RPAREN tt)) (lex_string_cpt n s')
      | "+" => option_map (Buf_cons (ADD tt)) (lex_string_cpt n s')
      | "-" => option_map (Buf_cons (SUB tt)) (lex_string_cpt n s')
      | "*" => option_map (Buf_cons (MUL tt)) (lex_string_cpt n s')
      | "/" => option_map (Buf_cons (DIV tt)) (lex_string_cpt n s')
    *)
      | _ =>
        if is_digit c then
          let (m,s) := readnum 0 s in
          option_map (Buf_cons (NUM m)) (lex_string_cpt n s)

        else if is_keyword s AADL_Direction_Type then
          let (l, kw) := which_keyword s AADL_Direction_Type in
              option_map (Buf_cons (DIRECTION_TYPE kw)) (lex_string_cpt n (ntail l s))

        else if is_keyword s AADL_Feature_Category then
          let (l, kw) := which_keyword s AADL_Feature_Category in
            option_map (Buf_cons (FEATURE_CATEGORY kw)) (lex_string_cpt n (ntail l s))

        else if is_keyword s AADL_Component_Category then
          let (l, kw) := which_keyword s AADL_Component_Category in
            option_map (Buf_cons (COMPONENT_CATEGORY kw)) (lex_string_cpt n (ntail l s))

        else if prefix "::" s then
          option_map (Buf_cons (COLONx2 tt)) (lex_string_cpt n (ntail 2 s))

        else if prefix ":" s then
          option_map (Buf_cons (COLON tt)) (lex_string_cpt n (ntail 1 s))

        else if prefix "." s then
          option_map (Buf_cons (DOT tt)) (lex_string_cpt n (ntail 1 s))

        else if is_alpha c then
          let k := identsize s in
          let id := substring 0 k s in
          let s := ntail k s in
          option_map (Buf_cons (ID id)) (lex_string_cpt n s)

        else None
      end
    end
  end.

Definition lex_string (s:string) := lex_string_cpt (String.length s) s.
