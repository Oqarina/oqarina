
(** Hand-written lexer for natural numbers, idents, parens and + - * / *)

Require Import BinNat Ascii String.
Require Import Oqarina.parsers.Parser.
Import MenhirLibParser.Inter.
Open Scope char_scope.
Open Scope bool_scope.
Require Import List.
Import ListNotations. (* from List *)
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

Definition AADL_Component_Category : list string := [
  "abstract"%string ; "bus"%string ; "data"%string ;
	"device"%string ; "memory"%string ; "process"%string ; "processor"%string ; "subprogram"%string ;
	"subprogram group"%string ; "system"%string ; "thread group"%string ;
	"thread"%string ; "virtual bus"%string ; "virtual processor"%string
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

        else if is_keyword s AADL_Component_Category then
          let (l, kw) := which_keyword s AADL_Component_Category in
            option_map (Buf_cons (COMPONENT_CATEGORY kw)) (lex_string_cpt n (ntail l s))

        else if prefix "::" s then
          option_map (Buf_cons (COLONx2 tt)) (lex_string_cpt n (ntail 2 s))

        else if prefix ":" s then
          option_map (Buf_cons (COLON tt)) (lex_string_cpt n (ntail 1 s))

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
