(* Grammar the AADL Textual Instance Notation

See https://github.com/osate/osate2/blob/master/core/org.osate.aadl2.instance.textual/src/org/osate/aadl2/instance/textual/Instance.xtext

*)

%{
Require Import List.
Import ListNotations. (* from List *)
Require Import Oqarina.core.identifiers.

Module AST.
Inductive elt :=
    | COMPONENT_CATEGORY : identifier -> elt
    | ID : list identifier -> elt
with
node :=
    | ROOT_SYSTEM : elt -> elt -> elt -> node
.
End AST.

%}

%token EOF     (* EOF *)
%token COLON   (* ':' *)
%token COLONx2 (* '::' *)

%token<nat> NUM
%token<string> ID
%token<string> COMPONENT_CATEGORY

%start<AST.node> main
%type<AST.node> p_main
%type<AST.node> p_root_system
%type<AST.elt> p_component_category
%type<AST.elt> p_id
%type<AST.elt> p_idlist
%type<list identifier> p_idlist_inner

%%

main: p_main EOF       { $1 }

p_main :
| p_root_system { $1 }


p_root_system:
| p_component_category p_id COLON p_idlist { AST.ROOT_SYSTEM $1 $2 $4 }

p_component_category:
| COMPONENT_CATEGORY { AST.COMPONENT_CATEGORY (Id $1) }

p_id:
| ID { AST.ID [ Id $1 ] }

p_idlist:
| ID p_idlist_inner { AST.ID ([ Id $1 ] ++ $2) }

p_idlist_inner:
| COLONx2 ID { [Id $2] }
| COLONx2 ID  p_idlist_inner { [ Id $2 ] ++ $3}
