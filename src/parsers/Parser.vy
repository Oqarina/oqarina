(* Grammar the AADL Textual Instance Notation *)

%{
Require Import List.
Import ListNotations. (* from List *)
Require Import Oqarina.core.identifiers.

%}

%token EOF     (* EOF *)
%token COLON   (* ':' *)
%token COLONx2 (* '::' *)

%token<nat> NUM
%token<string> ID

%start<list identifier> main
%type<list identifier> p_main
%type<list identifier> p_idlist

%%

main: p_main EOF       { $1 }

p_main :
| p_idlist { $1 }

p_idlist:
| ID { [ Id $1 ] }
| ID COLONx2 p_idlist { [ Id $1 ] ++ $3}
