(***
 * Oqarina
 * Copyright 2021 Carnegie Mellon University.
 *
 * NO WARRANTY. THIS CARNEGIE MELLON UNIVERSITY AND SOFTWARE ENGINEERING
 * INSTITUTE MATERIAL IS FURNISHED ON AN "AS-IS" BASIS. CARNEGIE MELLON
 * UNIVERSITY MAKES NO WARRANTIES OF ANY KIND, EITHER EXPRESSED OR
 * IMPLIED, AS TO ANY MATTER INCLUDING, BUT NOT LIMITED TO, WARRANTY OF
 * FITNESS FOR PURPOSE OR MERCHANTABILITY, EXCLUSIVITY, OR RESULTS
 * OBTAINED FROM USE OF THE MATERIAL. CARNEGIE MELLON UNIVERSITY DOES NOT
 * MAKE ANY WARRANTY OF ANY KIND WITH RESPECT TO FREEDOM FROM PATENT,
 * TRADEMARK, OR COPYRIGHT INFRINGEMENT.
 *
 * Released under a BSD (SEI)-style license, please see license.txt or
 * contact permission@sei.cmu.edu for full terms.
 *
 * [DISTRIBUTION STATEMENT A] This material has been approved for public
 * release and unlimited distribution.  Please see Copyright notice for
 * non-US Government use and distribution.
 *
 * This Software includes and/or makes use of the following Third-Party
 * Software subject to its own license:
 *
 * 1. Coq theorem prover (https://github.com/coq/coq/blob/master/LICENSE)
 * Copyright 2021 INRIA.
 *
 * 2. Coq JSON (https://github.com/liyishuai/coq-json/blob/comrade/LICENSE)
 * Copyright 2021 Yishuai Li.
 *
 * DM21-0762
***)
(*| .. coq:: none |*)

(* Coq Library *)
Require Import List.
Import ListNotations. (* from List *)

(* Oqarina library *)
Require Import Oqarina.AADL.Kernel.all.
Require Import Oqarina.core.all.
(*| .. coq:: |*)
Section Error_Flows.

Definition Error_Type_Set := option nat. (* XXX placeholder *)

Inductive Error_Direction := | inErr | outErr.

(* From E.7.1

error_propagation ::=
    error_propagation_point :
     ( in | out ) propagation error_type_set ;

error_containment ::=
    error_propagation_point :
      not ( in | out ) propagation error_type_set ;

error_propagation_point ::=
  feature_reference | binding_reference
  | propagation_point_identifier

feature_reference ::=
    ( { feature_group_identifier . }*  feature_identifier )
    | access

binding_reference ::=
    processor | memory | connection | binding | bindings

*)

Inductive Binding_Reference :=
| processor | memory | connection | binding | bindings.

Inductive Error_Propagation_Point :=
| frpp (* feature_reference *):
   fq_name -> Error_Propagation_Point
(* access XXX *)
| brpp (* binding_reference *):
    Binding_Reference -> Error_Propagation_Point
.

Record Error_Propagation := {
    ep : Error_Propagation_Point ;
    ep_dir : Error_Direction ;
    ep_error_type_set : Error_Type_Set ;
}.

Record Error_Containement := {
    ec : Error_Propagation_Point ;
    ex_dir : Error_Direction ;
    ec_error_type_set : Error_Type_Set ;
}.

(*| This captures the BNF from section E.7.2

error_flow ::=
  error_source | error_sink | error_path

error_source ::=
  defining_error_source_identifier :
    error source  ( outgoing_error_propagation_point | all )
   [ effect_error_type_set ] [ when fault_source ] [ if fault_condition ] ;

error_sink ::=
  defining_error_sink_identifier :
    error sink ( incoming_error_propagation_point | all ) [ error_type_set ] ;

error_path ::=
  defining_error_path_identifier :
    error path
      ( incoming_error_propagation_point | all ) [ error_type_set ] ->
      ( outgoing_error_propagation_point | all )
        [ target_error_type_instance ] ;

fault_source ::=
  ( error_behavior_state [ error_type_set ])
  | error_type_set | failure_mode_description

fault_condition ::= string_literal;

|*)

Inductive Error_Flow :=
| error_source : identifier -> Error_Propagation_Point -> Error_Type_Set -> Error_Flow
| error_sink : identifier -> Error_Propagation_Point -> Error_Type_Set -> Error_Flow
| error_path : identifier -> Error_Propagation_Point -> Error_Type_Set
                -> Error_Propagation_Point -> Error_Flow
.

(* From E.7

error_propagations ::=
    error propagations
     { error_propagation | error_containment }*
     [ flows
        { error_flow }+ ]
    end propagations;

*)

Record Error_Propagations := {
    propagations  : list Error_Propagation ;
    containements : list Error_Containement;
    flows         : list Error_Flow ;
}.

End Error_Flows.

Section Error_Behavior_State_Machine.

(* From E.8

error_behavior_event ::=
  error_event | recover_event | repair_event

error_event ::=
  defining_error_behavior_event_identifier : error event
    [ error_type_set ]
    [ if error_event_condition ] ;

error_event_condition ::= string_literal

recover_event ::=
  defining_error_behavior_event_identifier : recover event
    [ when recover_event_initiators ]
    [ if error_event_condition ] ;

event_initiators ::=
  ( initiator_reference { , initiator_reference }* )

initiator_reference ::=
  mode_transition_reference | port_reference | self_event_reference

repair_event ::=
  defining_error_behavior_event_identifier : repair event
    [ when repair_event_initiation initiator ] ;


*)

Inductive Error_Behavior_Event :=
    | error_event: identifier -> Error_Type_Set (* -> error_event_condition *)
        -> Error_Behavior_Event
    | recover_event : identifier -> Error_Behavior_Event (* XXX *)
    | repair_event :  identifier -> Error_Behavior_Event (* XXX *)
.

(*

error_behavior_state ::=
  defining_error_behavior_state_identifier : [ initial ] state
    [ error_type_set ] ;


*)

Definition Error_Behavior_State : Type := prod identifier bool.

(*

error_behavior_transition ::=
    [ defining_error_transition_identifier : ]
    error_source_state –[ error_condition ]->
     ( error_transition_target | error_transition_branch ) ;

error_source_state ::=
    all | ( source_error_state_identifier  [ source_error_type_set ] )

error_transition_target ::=
    ( target_error_state_identifier [ target_error_type_instance ] )
    | same state

error_transition_branch ::=
    ( error_transition_target with branch_probability
     { , error_transition_target with branch_probability }* )

In the following, we do not model "all" or "same state", we assume these get expanded during instantiation.
*)

Definition Error_Source_State : Type := identifier.

Definition Error_Transition_Target : Type := identifier.

Inductive Error_Behavior_Transition :=
    ebt : identifier -> Error_Source_State -> option identifier  (* XXX *)
    -> Error_Transition_Target -> Error_Behavior_Transition.

(*

error_behavior_state_machine ::=
  error behavior defining_state_machine_identifier
    [ use types error_type_library_list ; ]
    [ use transformations error_type_transformation_set_reference ; ]
    [ events { error_behavior_event }+ ]
    [ states { error_behavior_state }+ ]
    [ transitions { error_behavior_transition }+ ]
    [ properties { error_behavior_state_machine_emv2_contained_property_association }+ ]
  end behavior ;

*)

Record Error_Behavior_State_Machine := {
    events : list Error_Behavior_Event;
    states : list Error_Behavior_State;
    transitions : list Error_Behavior_Transition ;
}.

Definition nil_Error_Behavior_State_Machine := {|
    events := [] ; states := [] ; transitions := [];
|}.

End Error_Behavior_State_Machine.

Section Component_Error_Behavior.

(* From E.10

component_error_behavior ::=
    component error behavior
      [ use transformations error_type_transformation_set_reference ; ]
      [ events { error_behavior_event }+ ]
      [ transitions { component_specific_error_behavior_transition }+ ]
      [ propagations { outgoing_propagation_condition }+ ]
      [ detections { error_detection }+ ]
      [ mode mappings { error_state_to_mode_mapping }+ ]
    end component;

outgoing_propagation_condition ::=
  [ defining_outgoing_propagation_identifier : ]
  ( error_source_state | all )
  -[ [ error_condition ] ]->
  propagation_target ;

propagation_target ::=
    ( error_propagation_point | all )
    [ propagated_target_error_type_instance | { noerror } ]

error_detection ::=
  [ defining_error_detection_identifier : ]
  ( error_source_state | all )
    -[ [ error_condition ] ]->
    error_detection_effect ;

error_detection_effect ::=
    ( outgoing_port_reference | internal_event_reference ) !
    [ ( error_code_value ) ]

*)

Definition Propagation_Target : Type := Error_Propagation_Point.

Inductive Outgoing_Propagation_Condition :=
    opc: identifier -> Error_Source_State (* XXX Error_Condition *) -> Propagation_Target -> Outgoing_Propagation_Condition.

Record Component_Error_Behavior := {
    ceb_events : list Error_Behavior_Event ;
    ceb_transitions : list Error_Behavior_Transition ;
    ceb_propagations : list Outgoing_Propagation_Condition ;
}.

Definition nil_Component_Error_Behavior := {|
    ceb_events := [] ;
    ceb_transitions := [] ;
    ceb_propagations := [] ;
|}.

End Component_Error_Behavior.

Section EMV2.

(* From E.4

error_model_component_constructs ::=
    [ use types error_type_library_list ; ]
    [ use type equivalence error_type_mappings_reference ; ]
    [ use mappings error_type_mappings_reference ; ]
    [ use behavior error_behavior_state_machine_reference ; ]
    [ error_propagations ]
    [ component_error_behavior ]
    [ composite_error_behavior ]
    [ connection_error_behavior ]
    [ propagation_paths ]
    [ EMV2_properties_section ]
*)

Record EMV2 := {
    use_behavior : Error_Behavior_State_Machine ;
    error_propagations : Error_Propagations;
    component_error_behavior : Component_Error_Behavior ;
}.
End EMV2.

Module EMV2_Notations.

Declare Scope emv2_scope.
Notation "'in_propagation:' point error_type_set" :=
    ({| ep := frpp (parse_fq_name point) ;
        ep_dir := inErr ;
        ep_error_type_set := error_type_set;
    |})
    (at level 10, point at next level, error_type_set at next level)
    : emv2_scope.

Notation "'out_propagation:'  point error_type_set" :=
    ({| ep := frpp (parse_fq_name point) ;
        ep_dir := outErr ;
        ep_error_type_set := error_type_set;
    |})
    (at level 10, point at next level, error_type_set at next level)
    : emv2_scope.

Notation "'error_path:' id src error_type_set dest" :=
    ( error_path (Id id)
    (frpp (parse_fq_name src)) error_type_set
    (frpp (parse_fq_name dest))
   ) (at level 10, id at next level, src at next level, error_type_set at next level, dest at next level) : emv2_scope.

Notation "'error_source:' id point error_type_set " :=
    ( error_source (Id id)
    (frpp (parse_fq_name point)) error_type_set (* XXX *)
   ) (at level 10, id at next level, point at next level, error_type_set at next level) : emv2_scope.

Notation "'error_sink:' id point error_type_set " :=
    ( error_sink (Id id)
    (frpp (parse_fq_name point)) error_type_set
   ) (at level 10, id at next level, point at next level, error_type_set at next level) : emv2_scope.

Notation "'error_event:' id error_type_set " :=
    (error_event (Id id) error_type_set)
    (at level 10, id at next level, error_type_set at next level) : emv2_scope.

Notation "'state:' id" := (Id id, false)
    (at level 10) : emv2_scope.

Notation "'transition:' id src '-[' cond ']->' dst" :=
    (ebt (Id id) (Id src) cond (Id dst))
    (at level 10, id at next level, src at next level, dst at next level).

Notation "'initial_state:' id" := (Id id, true)
    (at level 10) : emv2_scope.

End EMV2_Notations.

Section EMV2_Examples.

Import EMV2_Notations.
Open Scope emv2_scope.

(*| This example illustrates how to use error propagations |*)

Example emv2_test_1 : EMV2 := {|
    use_behavior := nil_Error_Behavior_State_Machine;

    error_propagations := {|
        propagations :=
        [
            out_propagation: "foo.outF" None;
            in_propagation:  "foo.inF" None;
            in_propagation:  "foo.inF2" None;
            out_propagation: "foo.outF2" None
        ];
        containements := [];
        flows :=
        [
            error_path: "ep1" "foo.inF" None "foo.outF" ;
            error_sink: "es1" "foo.inF2" None ;
            error_source: "es2" "foo.outF2" None
        ];
    |};
    component_error_behavior := nil_Component_Error_Behavior ;
|}.

Example EMV2_FailStop : Error_Behavior_State_Machine := {|
    events := [
        error_event: "Failure" None
    ];

    states := [
        initial_state: "Operational" ;
        state: "FailStop"
    ];

    transitions := [
        transition: "FailureTransition"
            "Operational" -[ (Some (Id "Failure")) ]-> "FailStop"
    ]
|}.
Print Error_Behavior_State_Machine.
Print Component_Error_Behavior.

Example emv2_test_2 : EMV2 := {|
    use_behavior :=  EMV2_FailStop;

    error_propagations := {|
        propagations :=
        [
            out_propagation: "foo.outF" None
        ];
        containements := [];
        flows :=
        [
            error_source: "es2" "foo.outF" None
        ];
    |};
    component_error_behavior := nil_Component_Error_Behavior ;

|}.

End EMV2_Examples.
