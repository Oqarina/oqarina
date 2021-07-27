Require Import List String.

Require Import Oqarina.AADL.atin_frontend.atin_lexer.
Require Import Oqarina.AADL.atin_frontend.atin_parser.
Import MenhirLibParser.Inter.
Open Scope string_scope.

Definition string2aadl s :=
  match option_map (atin_parser.main 500) (atin_lexer.lex_string s) with
  | Some (Parsed_pr f _) => Some f
  | _ => None
  end.