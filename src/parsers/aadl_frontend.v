Require Import List String.

Require Import Oqarina.parsers.aadl_parser.
Require Import Oqarina.parsers.aadl_lexer.
Import MenhirLibParser.Inter.
Open Scope string_scope.

Definition string2aadl s :=
  match option_map (aadl_parser.main 500) (aadl_lexer.lex_string s) with
  | Some (Parsed_pr f _) => Some f
  | _ => None
  end.