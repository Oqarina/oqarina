(* Grammar the AADL Textual Instance Notation

See https://github.com/osate/osate2/blob/master/core/org.osate.aadl2.instance.textual/src/org/osate/aadl2/instance/textual/Instance.xtext

*)

%{
Require Import List.
Import ListNotations. (* from List *)
Require Import Oqarina.core.identifiers.

Module AST.

    Inductive ComponentCategory_ast :=
        | COMPONENT_CATEGORY : identifier -> ComponentCategory_ast.

    Inductive ID_ast :=
        | ID : list identifier -> ID_ast.

    Inductive ComponentInstance_ast :=
        | COMPONENT_INSTANCE : ComponentCategory_ast -> ID_ast -> ID_ast -> ComponentInstance_ast.

    Inductive node :=
        | ROOT_SYSTEM : ComponentCategory_ast -> ID_ast -> ID_ast -> ComponentInstance_ast -> node.


End AST.

%}

%token EOF         (* EOF *)
%token COLON       (* ':' *)
%token COLONx2     (* '::' *)
%token LEFT_BRACE  (* { *)
%token RIGHT_BRACE (* } *)

%token<nat> NUM
%token<string> ID
%token<string> COMPONENT_CATEGORY

%start<AST.node> main
%type<AST.node> p_main
%type<AST.node> p_SystemInstance
%type<AST.ComponentInstance_ast> p_subclause_element
%type<AST.ComponentInstance_ast> p_ComponentInstance
%type<AST.ComponentCategory_ast> p_component_category
%type<AST.ID_ast> p_id
%type<AST.ID_ast> p_idlist
%type<list identifier> p_idlist_inner

%%

main: p_main EOF       { $1 }

p_main :
| p_SystemInstance { $1 }



(*
SystemInstance returns instance::SystemInstance:
	category=ComponentCategory name=ID ':' componentImplementation=[aadl2::ComponentImplementation|ImplRef] '{' (
		featureInstance+=FeatureInstance |
		componentInstance+=ComponentInstance |
		connectionInstance+=ConnectionInstance |
		flowSpecification+=FlowSpecificationInstance |
		endToEndFlow+=EndToEndFlowInstance |
		modeInstance+=ModeInstance |
		modeTransitionInstance+=ModeTransitionInstance |
		systemOperationMode+=SystemOperationMode |
		ownedPropertyAssociation+=PropertyAssociationInstance
	)* '}'
;

*)

p_SystemInstance :
| p_component_category p_id COLON p_idlist LEFT_BRACE p_subclause_element RIGHT_BRACE { AST.ROOT_SYSTEM $1 $2 $4 $6 }

p_subclause_element :
| p_ComponentInstance { $1 }

p_ComponentInstance:
| p_component_category p_id COLON p_idlist  { AST.COMPONENT_INSTANCE $1 $2 $4 }

p_component_category:
| COMPONENT_CATEGORY { AST.COMPONENT_CATEGORY (Id $1) }

(* The following is largely incomplete *)

p_id:
| ID { AST.ID [ Id $1 ] }

p_idlist:
| ID p_idlist_inner { AST.ID ([ Id $1 ] ++ $2) }

p_idlist_inner:
| COLONx2 ID { [Id $2] }
| COLONx2 ID  p_idlist_inner { [ Id $2 ] ++ $3}
