%{

From Coq Require Import List.
Import ListNotations.

%}

%token <int> INT
%token <string> STRING
%token <string> ID
%token <string> COMPONENT_CATEGORY
%token <string> FEATURE_CATEGORY
%token <string> CONNECTION_KIND

%token LPAREN
%token RPAREN
%token LEFT_BRACE
%token RIGHT_BRACE
%token LEFT_BRACK
%token RIGHT_BRACK
%token COLON
%token COLONx2
%token COMMA
%token DOT
%token POUND
%token FWD_ARROW
%token BIDI_ARROW

%token EOF

%token IN
%token OUT
%token MODES
%token TRANSITION
%token TRANSITIONS

%token COMPLETE
%token PARENT
%token CONNECTION


%start main
%type <Aadl.aadl_ast_root option> main
%type <Aadl.id option> opt_id_sfx
%type <[`Transition of int | `ID of Aadl.id]> transition_num_or_id
%type <Aadl.id> id
%type <Aadl.feature_instance> featureInstance
%type <Aadl.component_instance> componentInstance
%type <Aadl.system_instance> systemInstance
%type <Aadl.connection_instance> connectionInstance
%type <Aadl.instance_ref> instance_ref
%type <Aadl.connection_reference> connectionReference
%%

idPrefix:
  | id = id; COLONx2 { [id] }
  | pfx = idPrefix; id = id; COLONx2 { id :: pfx }

opt_id_sfx:
  | (* empty *) { None }
  | DOT; id = id { Some id }

bracketed_int:
  LEFT_BRACK; i=int; RIGHT_BRACK  { i }

bracketed_int_opt:
    x = bracketed_int  { Some x }
  | (* empty *)  { None }

bracketed_int_star:
    (* empty *) { [] }
  | x = bracketed_int; xs = bracketed_int_star  { x :: xs }

classifierRef:
  pfx = idPrefix; id = id; sfx = opt_id_sfx
  { `ClassifierRef (List.rev pfx, id, sfx) }

(*
optional_index:
  LEFT_BRACK; i=int; RIGHT_BRACK { Some i }
  | (*empty*) { None }
*)

in_modes:  (* TODO! *)
  IN MODES LPAREN RPAREN { }

in_modes_opt:
  x = in_modes { Some x }
  | (* empty *) { None }

systemInstance:
  category=componentCategory; name=id; COLON; component_impl=classifierRef;
  braced_list=braced_subitem_list
  { {
    Aadl.sys_category = category;
    sys_name = name;
    component_impl = component_impl;
    braced_subitems = braced_list;
  } }

componentInstance:
  category=componentCategory; classifier=classifierRef; name=id; index=bracketed_int_star
  in_modes_opt
  COLON subcomponent=declarativeRef
  braced_list=braced_subitem_list_opt
  { {Aadl.category=category; classifier_ref=classifier; id=name; indexes=index; subcomponent=subcomponent; braced_subitems=braced_list} }

featureInstance:
  direction=direction_type; category=FEATURE_CATEGORY; name=ID; index=bracketed_int_opt
  COLON feature=declarativeRef
  braced_list=braced_subitem_list_opt
  { {Aadl.direction=direction; category=category; name=name; index=index; feature=feature; braced_subitems=braced_list} }

bidi:
    FWD_ARROW  { "->" }
  | BIDI_ARROW { "<->" }

bidi_opt:
    x=bidi  { Some x }
  | (* empty *)  { None }

COMPLETE_opt:
    x=COMPLETE  { Some x }
  | (* empty *)  { None }

connectionInstance:
  complete=COMPLETE_opt; kind=CONNECTION_KIND; name=STRING;
  COLON;
  source=instance_ref; bidi=bidi_opt; destination=instance_ref;
  (* (IN MODES LPAREN separated_list(COMMA, system_operation_mod) RPAREN)? *)
  braced_list=braced_subitem_list
  {
  {
    Aadl.complete = (match complete with  Some x -> true  |  None -> false);
    kind; name; source;
    bidirectional = bidi;
    destination;
    in_system_operation_mode = None;
    in_mode_transition = None;
    braced_subitems = braced_list;
  }
  }

connectionReference:
  source=instance_ref; FWD_ARROW; destination=instance_ref;
  COLON
  connection=declarativeRef; IN; context=instance_ref
  {
  {Aadl.source; destination; connection; context}
  }

componentCategory:
  cat = COMPONENT_CATEGORY { `ComponentCategory cat }

braced_subitem:
  | componentInstance { `ComponentInstance $1 }
  | featureInstance { `FeatureInstance $1 }
  | connectionInstance { `ConnectionInstance $1 }
  | connectionReference { `ConnectionReference $1 }

braced_subitem_list:
  LEFT_BRACE braced_subitem_list_inner { $2 }

braced_subitem_list_inner:
  RIGHT_BRACE {[]}
  | braced_subitem_list braced_subitem_list_inner { $1 :: $2 }

braced_subitem_list_opt:
    x = braced_subitem_list  { Some x }
 | (* empty *)  { None }

main:
  v = systemInstance EOF { Some (`AADL_ast_root v) }

transition_num_or_id:
  | TRANSITION POUND i=int { `Transition i }
  | id=id { `ID id }

direction_type:
  | IN { `In }
  | OUT { `Out }
  | dt=direction_type; OUT {
    match dt with
      `In -> `InOut
      | _ -> raise (Aadl.SyntaxError ("Expected 'in' before 'out'."))
  }

declarativeRef:
  pfx=idPrefix id=id sfx=opt_id_sfx COLON x=transition_num_or_id
  { `DeclarativeRef ((pfx, id, sfx), x) }

(*
id_bracketed_ints:
  id=id int_list=bracketed_int*
  { (id, int_list) }
*)
connection_num:
  CONNECTION POUND i=int
  { i }

instance_ref_subpart:
    CONNECTION POUND i=int
    { ([], Some i) }
 (* | head=id_bracketed_ints; DOT; remainder=instance_ref_subpart
    { match remainder with
      (tail, cnum) -> (head :: tail, cnum)}
 | head=id_bracketed_ints
    {([head], None)}
*)
instance_ref:
    PARENT { `InstanceRefParent }
  | x=instance_ref_subpart
    { `InstanceRef x }

id:
  id = ID { `Id id };

int:
  i = INT { i };
