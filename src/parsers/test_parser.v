Require Import List String PeanoNat.

Require Import Oqarina.parsers.Parser.
Require Import Oqarina.parsers.Lexer.
Import MenhirLibParser.Inter.
Open Scope string_scope.

(** Lexer + Parser for little arithmetic expressions *)

Definition string2expr s :=
  match option_map (Parser.main 50) (Lexer.lex_string s) with
  | Some (Parsed_pr f _) => Some f
  | _ => None
  end.

Definition example := "xx".
Compute (Lexer.lex_string example).
Compute (string2expr example).

Definition example2 := "xx:yy".
Compute (Lexer.lex_string example2).
Compute (string2expr example2).

Definition example3 := "xx::yy".
Compute (Lexer.lex_string example3).
Compute (string2expr example3).

Definition example4 := "xx::yy::qq::aa::aa".
Compute (Lexer.lex_string example4).
Compute (string2expr example4).