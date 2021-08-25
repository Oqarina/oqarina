(** %\chapter{AADL instance model JSON parser}\label{chap::aadl_json}% *)

(**
This module introduces a JSON-based parser for Oqarina. It maps a JSON file produced by Ocarina to an Oqarina instance model.

This implementation relies on the `coq-json` library for parsing a JSON file, producing an AST. Then the [Map_JSON] function maps this AST onto a valid AADL instance file. Because of Coq typing rules, we can only build a valid instance model, albeit incomplete.
*)

(* begin hide *)
(** Coq Library *)
From JSON Require Import
    Lexer
    Printer.
Import
    List
    ListNotations.

(** Oqarina library *)
From Oqarina Require Import
    Kernel.all
    core.identifiers.
(* end hide *)
Require Import Coq.Strings.String.

(** * Helper functions *)

Definition get_string_from_json (s : string) (j : json) :=
  match get_string s j with
  | Some s' => s'
  | _ => ""
  end.

(** - [get_identifier] extracts a string object from a JSON object *)
Definition get_identifier (j : json) :=
  match get_string "identifier" j with
  | Some s => Id s
  | _ => empty_identifier
  end.

(** - [get_json_list] turns a JSON__Array object into a list *)

Definition get_json_list (j : json) :=
  match get_list (fun x => Some x) j with
  | Some l => l
  | None => []
  end.

(** * Mapping helper functions *)

(** These functions map various elements of a JSON AST to their AADL counterpart. *)

Definition Map_JSON_To_ComponentCategory (cat : json) :=
  match cat with
  | JSON__String "system" => system
  | JSON__String "abstract" => abstract
  | JSON__String "bus" => bus
  | JSON__String "data" => data
	| JSON__String "device" => device
  | JSON__String "memory" => memory
  | JSON__String "processor" => processor
  | JSON__String "process" => process
  | JSON__String "subprogram" => subprogram
  | JSON__String "subprogram group" => subprogramGroup
  | JSON__String "thread group" => threadGroup
	| JSON__String "thread" => thread
  | JSON__String "virtual bus" => virtualBus
  | JSON__String "virtual processor" => virtualProcessor
  | _ => null
  end.

Definition Map_JSON_To_Feature_Direction (j : json) :=
  match j with
    | JSON__Object [("kind", JSON__String "out")] => outF
    | JSON__Object [("kind", JSON__String "in")] => inF
    | JSON__Object [("kind", JSON__String "inout")] => inoutF
    | _ => nullDirection
  end.

Definition Map_JSON_To_Feature_Category (j : json) :=
  match j with
    | JSON__Object [("kind", JSON__String "data")] => dataPort
    | JSON__Object [("kind", JSON__String "event")] => eventPort
    | JSON__Object [("kind", JSON__String "event_data")] => eventDataPort
    | JSON__Object [("kind", JSON__String "feature")] => abstractFeature
    | _ => invalid
  end.

Definition get_subcomponents (j : json) :=
  let s := get_json "component" (get_json "subcomponents" j) in
  match s with
  | JSON__Object f => [ s ]
  | JSON__Array l => get_json_list s
  | _ => []
  end.

Definition get_features (j : json) : list json :=
  let f := get_json "feature" (get_json "features" j) in
  match f with
  | JSON__Object o => [ f ]
  | JSON__Array l => get_json_list f
  | _ => []
  end.

Definition get_properties (j : json) : list json :=
  let f := get_json "property" (get_json "properties" j) in
  match f with
  | JSON__Object o => [ f ]
  | JSON__Array l => get_json_list f
  | _ => []
  end.

Fixpoint parse_uint' acc s :=
  match s with
  | String "0" s => parse_uint' (acc*10) s
  | String "1" s => parse_uint' (acc*10+1) s
  | String "2" s => parse_uint' (acc*10+2) s
  | String "3" s => parse_uint' (acc*10+3) s
  | String "4" s => parse_uint' (acc*10+4) s
  | String "5" s => parse_uint' (acc*10+5) s
  | String "6" s => parse_uint' (acc*10+6) s
  | String "7" s => parse_uint' (acc*10+7) s
  | String "8" s => parse_uint' (acc*10+8) s
  | String "9" s => parse_uint' (acc*10+9) s
  | _ => (acc,s)
  end.

Definition parse_uint (s : string) :=
  let (n, s) := parse_uint' 0 s in n.

Definition parse_int s :=
  match s with
  | EmptyString => 0 (* XXX should report error*)
  | String a s' =>
    if Ascii.eqb a "-" then - (parse_uint s')
    else (parse_uint s)
  end.

Definition parse_bool s :=
  if eqb "true" s then true
  else if eqb "false" s then true
  else false. (* error reporting *)

Definition Map_JSON_To_Property_Value_Abstract (j2 : json) (f : json -> property_value ): property_value :=
  match j2 with
  | JSON__Object j3 => f j2
  | JSON__Array j3 => PV_List (map (fun x => f x) j3)
  | _ => PV_Bool false
  end.

Fixpoint Map_JSON_To_Property_Value (j : json) : property_value :=
  match j with
  | JSON__Object [("boolean", j2)] =>
    Map_JSON_To_Property_Value_Abstract j2
      (fun x => PV_Bool (parse_bool (get_string_from_json "value" x)))

  | JSON__Object [("string", j2)] =>
    Map_JSON_To_Property_Value_Abstract j2
      (fun x => PV_String (get_string_from_json "value" x))

  | JSON__Object [("integer", j2)] =>
    Map_JSON_To_Property_Value_Abstract j2
      (fun x => PV_Int (parse_int (get_string_from_json "value" x)))

  | JSON__Object [("integer_unit", j2)] =>
    Map_JSON_To_Property_Value_Abstract j2
      (fun x => PV_IntU (parse_int (get_string_from_json "value" x))
                (PV_Unit (Id (get_string_from_json "unit" x))))

  | JSON__Object [("enumeration", j2)] =>
    Map_JSON_To_Property_Value_Abstract j2
      (fun x => PV_Enum (Id (get_string_from_json "value" x)))

  | JSON__Object [("integer_range", j2)] =>
    Map_JSON_To_Property_Value_Abstract j2
      (fun x => PV_IntRange (PV_Int (parse_int (get_string_from_json "value_low" x)))
                    (PV_Int (parse_int (get_string_from_json "value_high" x))))

  | JSON__Object [("integer_range_unit", j2)] =>
    Map_JSON_To_Property_Value_Abstract j2
      (fun x => PV_IntRange (PV_IntU (parse_int (get_string_from_json "value_low" x))
                            (PV_Unit (Id (get_string_from_json "unit_low" x))))
                            (PV_IntU (parse_int (get_string_from_json "value_high" x))
                            (PV_Unit (Id (get_string_from_json "unit_high" x)))))

  | JSON__Object [("list", j2)] =>
    Map_JSON_To_Property_Value j2

(* The following are not handled yet, To be continued

  | PV_Real (r : REAL)
  | PV_RealU (r : REAL) (unit : property_value)
  | PV_RealRange (min max : property_value)
  | PV_IntRangeD (min max : property_value) (delta : property_value)
  | PV_RealRangeD (min max : property_value) (delta : property_value)
  | PV_PropertyRef (qname : ps_qname) (* ref to property or constant *)
  | PV_Classifier (* TBD *)
  | PV_ModelRef (path : list identifier)
  | PV_Record (fields : list field_value)
  | PV_Computed (function : string)
*)


    | _  => PV_Bool false
  end.

Fixpoint Map_JSON_To_Property_Association (j : list json) :=
  match j with
      | (JSON__Object o) :: t =>
        {| P := PSQN (get_string_from_json "name" (JSON__Object o)) "";
          PV := (Map_JSON_To_Property_Value (get_json "property_value" (JSON__Object o))) |}
        :: Map_JSON_To_Property_Association  t
      | _ => [  ]
  end.

Fixpoint Map_JSON_To_Component' (fuel : nat) (c : list json) : list component :=
  match fuel with
  | 0%nat => nil
  | S m =>
    match c with
    | (JSON__Object f) :: t =>
       ( Component (get_identifier (JSON__Object f))
                   (Map_JSON_To_ComponentCategory (get_json "category" (JSON__Object f)))
                   empty_fqname (* classifier *)
                   (Map_JSON_To_Feature' m (get_features (JSON__Object f))) (* features *)
                   (Map_JSON_To_Component' m (get_subcomponents (JSON__Object f))) (* subcomponents *)
                   (Map_JSON_To_Property_Association (get_properties (JSON__Object f)))(* properties *)
                   nil (* connections *)
       )
      :: (Map_JSON_To_Component' m t)
    | _ => []
    end
  end
with Map_JSON_To_Feature' (fuel : nat) (j : list json) :=
  match fuel with
  | 0%nat => nil
  | S m =>
    match j with
      | (JSON__Object o) :: t =>
        ( Feature (get_identifier (JSON__Object o)) (* identifier *)
                (Map_JSON_To_Feature_Direction (get_json "direction" (JSON__Object o))) (* directionType *)
                (Map_JSON_To_Feature_Category (get_json "type" (JSON__Object o))) (* feature category *)
                (hd nil_component (Map_JSON_To_Component' m [get_json "component" (get_json "corresponding_instance" (JSON__Object o))]))
                nil (* properties *)
        )
        :: Map_JSON_To_Feature' m t
      | _ => [  ]
      end
  end.

Definition Map_JSON_To_Component (c : list json) : list component :=
  Map_JSON_To_Component' 10 c. (* XXX should us a better value. The fuel value is the "depth of the model" *)

Definition Map_JSON_Root_To_Component (AST : option string + json) :=
  match AST with
    | inr (JSON__Object l) =>
    let aadl_xml := get_json "aadl_xml" (JSON__Object l) in
    let comps := get_json "components" aadl_xml in
      inr (Map_JSON_To_Component ([get_json "component" comps]))
    | inr _ =>  inl (Some "Invalid JSON Object")
    | inl x => inl x
  end.

Definition Map_JSON_String_To_Component (s : string) :=
    Map_JSON_Root_To_Component (from_string s).

Definition test_properties := "
{""aadl_xml"": {""components"": {""component"": {""category"": ""system"", ""features"": {}, ""subcomponents"": {""component"": {""category"": ""device"", ""features"": {}, ""subcomponents"": {}, ""identifier"": ""subcomp_subdevice"", ""properties"": {}, ""classifier"": ""subdevice.impl""}}, ""identifier"": ""main.impl"", ""properties"": {""property"": [{""name"": ""Test_Properties::a_record_property"", ""property_value"": {""record"": {""record_field"": [{""integer"": {""value"": ""10""}, ""name"": ""an_integer_field""}, {""name"": ""a_string_field"", ""string"": {""value"": ""test string""}}, {""real_range"": {""value_low"": ""5.0"", ""value_high"": ""10.0""}, ""name"": ""a_real_range_field""}]}}}, {""name"": ""Test_Properties::an_enumeration_property"", ""property_value"": {""enumeration"": {""value"": ""enum2""}}}, {""name"": ""Test_Properties::a_classifier_property"", ""property_value"": {""classifier"": {""value"": ""subdevice""}}}, {""name"": ""Test_Properties::a_reference_property"", ""property_value"": {""reference"": {""value"": ""subcomp_subdevice""}}}, {""name"": ""Test_Properties::a_list_of_list_property"", ""property_value"": {""list"": {""list"": [{""integer"": [{""value"": ""1""}, {""value"": ""2""}]}, {""integer"": [{""value"": ""3""}, {""value"": ""4""}]}]}}}, {""name"": ""Test_Properties::a_boolean_property"", ""property_value"": {""boolean"": {""value"": ""true""}}}, {""name"": ""Test_Properties::a_string_property"", ""property_value"": {""string"": {""value"": ""test string""}}}, {""name"": ""Test_Properties::a_real_range_property"", ""property_value"": {""real_range"": {""value_low"": ""5.0"", ""value_high"": ""10.0""}}}, {""name"": ""Test_Properties::a_real_unit_property"", ""property_value"": {""real_unit"": {""unit"": ""ns"", ""value"": ""10.0""}}}, {""name"": ""Test_Properties::a_negative_real_property"", ""property_value"": {""real"": {""value"": ""-10.0""}}}, {""name"": ""Test_Properties::a_real_property"", ""property_value"": {""real"": {""value"": ""10.0""}}}, {""name"": ""Test_Properties::an_integer_range_property"", ""property_value"": {""integer_range"": {""value_low"": ""5"", ""value_high"": ""10""}}}, {""name"": ""Test_Properties::an_integer_unit_property"", ""property_value"": {""integer_unit"": {""unit"": ""ms"", ""value"": ""10""}}}, {""name"": ""Test_Properties::a_negative_integer_property"", ""property_value"": {""integer"": {""value"": ""-10""}}}, {""name"": ""Test_Properties::an_integer_property"", ""property_value"": {""integer"": {""value"": ""10""}}}]}, ""classifier"": ""main.impl""}}, ""root_system"": ""main.impl""}}

".

Compute from_string test_properties.
Compute Map_JSON_String_To_Component test_properties.


Compute Map_JSON_String_To_Component "XXX".

Definition rma_test := "
{""aadl_xml"": {""components"": {""component"": {""category"": ""system"", ""features"": {}, ""subcomponents"": {""component"": [{""category"": ""process"", ""features"": {}, ""subcomponents"": {""component"": [{""category"": ""thread"", ""features"": {}, ""subcomponents"": {}, ""identifier"": ""Task1"", ""properties"": {""property"": [{""name"": ""Deadline"", ""property_value"": {""integer_unit"": {""unit"": ""ms"", ""value"": ""1000""}}}, {""name"": ""Compute_Execution_time"", ""property_value"": {""integer_range_unit"": {""value_low"": ""0"", ""value_high"": ""3"", ""unit_high"": ""ms"", ""unit_low"": ""ms""}}}, {""name"": ""Period"", ""property_value"": {""integer_unit"": {""unit"": ""ms"", ""value"": ""1000""}}}, {""name"": ""Priority"", ""property_value"": {""integer"": {""value"": ""1""}}}, {""name"": ""Dispatch_Protocol"", ""property_value"": {""enumeration"": {""value"": ""Periodic""}}}]}, ""classifier"": ""Task.impl_1""}, {""category"": ""thread"", ""features"": {}, ""subcomponents"": {}, ""identifier"": ""Task2"", ""properties"": {""property"": [{""name"": ""Deadline"", ""property_value"": {""integer_unit"": {""unit"": ""ms"", ""value"": ""500""}}}, {""name"": ""Compute_Execution_time"", ""property_value"": {""integer_range_unit"": {""value_low"": ""0"", ""value_high"": ""5"", ""unit_high"": ""ms"", ""unit_low"": ""ms""}}}, {""name"": ""Period"", ""property_value"": {""integer_unit"": {""unit"": ""ms"", ""value"": ""500""}}}, {""name"": ""Priority"", ""property_value"": {""integer"": {""value"": ""2""}}}, {""name"": ""Dispatch_Protocol"", ""property_value"": {""enumeration"": {""value"": ""Periodic""}}}]}, ""classifier"": ""Task.impl_2""}]}, ""identifier"": ""node_a"", ""properties"": {""property"": {""name"": ""Actual_Processor_Binding"", ""property_value"": {""list"": {""reference"": {""value"": ""cpu""}}}}}, ""classifier"": ""node_a.impl""}, {""category"": ""processor"", ""features"": {}, ""subcomponents"": {}, ""identifier"": ""cpu"", ""properties"": {""property"": [{""name"": ""Scheduling_Protocol"", ""property_value"": {""list"": {""enumeration"": {""value"": ""POSIX_1003_HIGHEST_PRIORITY_FIRST_PROTOCOL""}}}}, {""name"": ""Processor_properties::Max_Prio_First"", ""property_value"": {""enumeration"": {""value"": ""high""}}}, {""name"": ""Scheduling_Protocol"", ""property_value"": {""list"": {""enumeration"": {""value"": ""POSIX_1003_HIGHEST_PRIORITY_FIRST_PROTOCOL""}}}}, {""name"": ""Deployment::Execution_Platform"", ""property_value"": {""enumeration"": {""value"": ""Native""}}}]}, ""classifier"": ""cpu.impl""}]}, ""identifier"": ""rma.impl"", ""properties"": {}, ""classifier"": ""rma.impl""}}, ""root_system"": ""rma.impl""}}".

Compute Map_JSON_String_To_Component rma_test.