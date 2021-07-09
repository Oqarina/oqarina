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

    Inductive DirectionType_ast :=
        | DIRECTION_TYPE : identifier -> DirectionType_ast.

    Inductive FeatureCategory_ast :=
        | FEATURE_CATEGORY : identifier -> FeatureCategory_ast.

    Inductive ID_ast :=
        | ID : list identifier -> ID_ast.

    Inductive ComponentInstance_ast :=
        | COMPONENT_INSTANCE : ComponentCategory_ast -> ID_ast -> ID_ast -> list Subclause_ast -> ComponentInstance_ast
	with FeatureInstance_ast :=
		| FEATURE_INSTANCE : DirectionType_ast -> FeatureCategory_ast  -> ID_ast -> ID_ast -> FeatureInstance_ast
	with Subclause_ast :=
		| COMPONENT : ComponentInstance_ast -> Subclause_ast
		| FEATURE : FeatureInstance_ast -> Subclause_ast.

    Inductive node :=
        | ROOT_SYSTEM : ComponentCategory_ast -> ID_ast -> ID_ast -> list Subclause_ast -> node.


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
%token<string> DIRECTION_TYPE
%token<string> FEATURE_CATEGORY

%start<AST.node> main
%type<AST.node> p_main
%type<AST.node> p_SystemInstance

%type<list AST.Subclause_ast> p_subclause_list
%type<list AST.Subclause_ast> p_subclause_list_inner
%type<AST.Subclause_ast> p_subclause_element

%type<AST.ComponentInstance_ast> p_ComponentInstance
%type<AST.FeatureInstance_ast> p_FeatureInstance

%type<AST.ComponentCategory_ast> p_ComponentCategory
%type<AST.DirectionType_ast> p_DirectionType
%type<AST.FeatureCategory_ast> p_FeatureCategory

%type<AST.ID_ast> p_id
%type<AST.ID_ast> p_idlist
%type<list identifier> p_idlist_inner

%%

main: p_main EOF       { $1 }

p_main :
| p_SystemInstance { $1 }

(* We introduced the concept of subclause to factor out the parsing of the following

		'{' (
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

For the moment, we support only componentInstance and featureInstance.

*)

p_subclause_list:
| LEFT_BRACE p_subclause_list_inner { $2 }

p_subclause_list_inner:
| RIGHT_BRACE { [ ] }
| p_subclause_element p_subclause_list_inner { $1 :: $2 }

p_subclause_element :
| p_ComponentInstance { AST.COMPONENT $1 }
| p_FeatureInstance { AST.FEATURE $1 }

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
| p_ComponentCategory p_id COLON p_idlist p_subclause_list { AST.ROOT_SYSTEM $1 $2 $4 $5 }

(*

	ComponentInstance returns instance::ComponentInstance:
		category=ComponentCategory classifier=[aadl2::ComponentClassifier|ClassifierRef]? name=ID ('[' index+=Long ']')*
		('in' 'modes' '(' inMode+=[instance::ModeInstance] (',' inMode+=[instance::ModeInstance])*')')?
		':' subcomponent=[aadl2::Subcomponent|DeclarativeRef] ('{' (
			featureInstance+=FeatureInstance |
			componentInstance+=ComponentInstance |
			connectionInstance+=ConnectionInstance |
			flowSpecification+=FlowSpecificationInstance |
			endToEndFlow+=EndToEndFlowInstance |
			modeInstance+=ModeInstance |
			modeTransitionInstance+=ModeTransitionInstance |
			ownedPropertyAssociation+=PropertyAssociationInstance
		)* '}')?
	;

*)

p_ComponentInstance:
| p_ComponentCategory p_id COLON p_idlist p_subclause_list  { AST.COMPONENT_INSTANCE $1 $2 $4 $5 }

(*

	ComponentCategory returns aadl2::ComponentCategory: 'abstract' | 'bus'| 'data'
		| 'device' | 'memory' | 'process' | 'processor' | 'subprogram'
		| 'subprogram' 'group' | 'system' | 'thread' 'group'
		| 'thread' | 'virtual' 'bus' | 'virtual' 'processor';

*)

p_ComponentCategory:
| COMPONENT_CATEGORY { AST.COMPONENT_CATEGORY (Id $1) }

(*

	FeatureInstance returns instance::FeatureInstance:
		direction=DirectionType category=FeatureCategory name=ID ('[' index=Long ']')? ':' feature=[aadl2::Feature|DeclarativeRef] ('{' (
			featureInstance+=FeatureInstance |
			ownedPropertyAssociation+=PropertyAssociationInstance
		)* '}')?
	;

*)

p_FeatureInstance:
| p_DirectionType p_FeatureCategory p_id COLON p_idlist { AST.FEATURE_INSTANCE $1 $2 $3 $5 }

(*

	DirectionType returns aadl2::DirectionType:
		'in' | 'out' | 'in' 'out'
	;
*)

p_DirectionType:
| DIRECTION_TYPE { AST.DIRECTION_TYPE (Id $1) }

(*
	FeatureCategory returns instance::FeatureCategory:
		'dataPort' | 'eventPort' | 'eventDataPort' | 'parameter' |
		'busAccess' | 'dataAccess'| 'subprogramAccess' | 'subprogramGroupAccess' |
		'featureGroup' | 'abstractFeature'
	;
*)

p_FeatureCategory:
| FEATURE_CATEGORY { AST.FEATURE_CATEGORY(Id $1) }

(* The following is largely incomplete *)

p_id:
| ID { AST.ID [ Id $1 ] }

p_idlist:
| ID p_idlist_inner { AST.ID ([ Id $1 ] ++ $2) }

p_idlist_inner:
| COLONx2 ID { [Id $2] }
| COLONx2 ID  p_idlist_inner { [ Id $2 ] ++ $3}
