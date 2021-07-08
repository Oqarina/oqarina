Require Import List String PeanoNat.

Require Import Oqarina.parsers.Parser.
Require Import Oqarina.parsers.Lexer.
Import MenhirLibParser.Inter.
Open Scope string_scope.

Definition string2expr s :=
  match option_map (Parser.main 500) (Lexer.lex_string s) with
  | Some (Parsed_pr f _) => Some f
  | _ => None
  end.


Definition example := "system xx : aa::bb { system yy : zog::zog }".
Compute (Lexer.lex_string example).
Compute (string2expr example).
