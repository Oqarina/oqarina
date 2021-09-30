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

From Coq Require Import
    String.

(** Oqarina library *)
From Oqarina Require Import
    AADL.json_frontend.json_frontend
    AADL.instance.all.

(** * Tests *)

(** These examples have been generated using Ocarina https://github.com/openaadl/ocarina. They test the conversion from JSON to AADL, and the capability to prove automatically that the resulting model is well-formed. *)

(** ** Testing properties

This example test the correct parsing of several property types.

*)

Definition test_properties_JSON : string := "{""aadl_xml"": {""components"": {""component"": {""category"": ""system"", ""features"": {}, ""subcomponents"": {""component"": {""category"": ""device"", ""features"": {}, ""subcomponents"": {}, ""identifier"": ""subcomp_subdevice"", ""properties"": {}, ""classifier"": ""subdevice.impl""}}, ""identifier"": ""main.impl"", ""properties"": {""property"": [{""name"": ""Test_Properties::a_record_property"", ""property_value"": {""record"": {""record_field"": [{""integer"": {""value"": ""10""}, ""name"": ""an_integer_field""}, {""name"": ""a_string_field"", ""string"": {""value"": ""test string""}}, {""real_range"": {""value_low"": ""5.0"", ""value_high"": ""10.0""}, ""name"": ""a_real_range_field""}]}}}, {""name"": ""Test_Properties::an_enumeration_property"", ""property_value"": {""enumeration"": {""value"": ""enum2""}}}, {""name"": ""Test_Properties::a_classifier_property"", ""property_value"": {""classifier"": {""value"": ""subdevice""}}}, {""name"": ""Test_Properties::a_reference_property"", ""property_value"": {""reference"": {""value"": ""subcomp_subdevice""}}}, {""name"": ""Test_Properties::a_list_of_list_property"", ""property_value"": {""list"": {""list"": [{""integer"": [{""value"": ""1""}, {""value"": ""2""}]}, {""integer"": [{""value"": ""3""}, {""value"": ""4""}]}]}}}, {""name"": ""Test_Properties::a_boolean_property"", ""property_value"": {""boolean"": {""value"": ""true""}}}, {""name"": ""Test_Properties::a_string_property"", ""property_value"": {""string"": {""value"": ""test string""}}}, {""name"": ""Test_Properties::a_real_range_property"", ""property_value"": {""real_range"": {""value_low"": ""5.0"", ""value_high"": ""10.0""}}}, {""name"": ""Test_Properties::a_real_unit_property"", ""property_value"": {""real_unit"": {""unit"": ""ns"", ""value"": ""10.0""}}}, {""name"": ""Test_Properties::a_negative_real_property"", ""property_value"": {""real"": {""value"": ""-10.0""}}}, {""name"": ""Test_Properties::a_real_property"", ""property_value"": {""real"": {""value"": ""10.0""}}}, {""name"": ""Test_Properties::an_integer_range_property"", ""property_value"": {""integer_range"": {""value_low"": ""5"", ""value_high"": ""10""}}}, {""name"": ""Test_Properties::an_integer_unit_property"", ""property_value"": {""integer_unit"": {""unit"": ""ms"", ""value"": ""10""}}}, {""name"": ""Test_Properties::a_negative_integer_property"", ""property_value"": {""integer"": {""value"": ""-10""}}}, {""name"": ""Test_Properties::an_integer_property"", ""property_value"": {""integer"": {""value"": ""10""}}}]}, ""classifier"": ""main.impl""}}, ""root_system"": ""main.impl""}}".

Definition test_properties_AADL := Map_JSON_String_To_Component test_properties_JSON.

Definition f := Get_Instance test_properties_AADL.

(** Note: this example cannot be well-formed: it relies on property definitions that are not standard, and not encoded in Coq. *)

(** ** Car example, from https://github.com/OpenAADL/AADLib/tree/master/examples/car *)

Definition car : string := "{""aadl_xml"": {""components"": {""component"": {""category"": ""system"", ""features"": {}, ""subcomponents"": {""component"": [{""category"": ""process"", ""features"": {""feature"": [{""direction"": {""kind"": ""out""}, ""identifier"": ""M1_Out"", ""type"": {""kind"": ""event_data""}, ""corresponding_instance"": {""component"": {""category"": ""data"", ""features"": {}, ""subcomponents"": {}, ""identifier"": ""M1"", ""properties"": {}, ""classifier"": ""M1""}}}, {""direction"": {""kind"": ""in""}, ""identifier"": ""M2_In"", ""type"": {""kind"": ""event_data""}, ""corresponding_instance"": {""component"": {""category"": ""data"", ""features"": {}, ""subcomponents"": {}, ""identifier"": ""M2"", ""properties"": {}, ""classifier"": ""M2""}}}]}, ""subcomponents"": {}, ""identifier"": ""Process_A"", ""properties"": {""property"": {""name"": ""Actual_Processor_Binding"", ""property_value"": {""list"": {""reference"": {""value"": ""CPU_A""}}}}}, ""classifier"": ""PA""}, {""category"": ""processor"", ""features"": {}, ""subcomponents"": {}, ""identifier"": ""CPU_A"", ""properties"": {}, ""classifier"": ""CPU.A""}, {""category"": ""process"", ""features"": {""feature"": [{""direction"": {""kind"": ""in""}, ""identifier"": ""M1_In"", ""type"": {""kind"": ""event_data""}, ""corresponding_instance"": {""component"": {""category"": ""data"", ""features"": {}, ""subcomponents"": {}, ""identifier"": ""M1"", ""properties"": {}, ""classifier"": ""M1""}}}, {""direction"": {""kind"": ""out""}, ""identifier"": ""M2_Out"", ""type"": {""kind"": ""event_data""}, ""corresponding_instance"": {""component"": {""category"": ""data"", ""features"": {}, ""subcomponents"": {}, ""identifier"": ""M2"", ""properties"": {}, ""classifier"": ""M2""}}}, {""direction"": {""kind"": ""out""}, ""identifier"": ""M3_Out"", ""type"": {""kind"": ""event_data""}, ""corresponding_instance"": {""component"": {""category"": ""data"", ""features"": {}, ""subcomponents"": {}, ""identifier"": ""M3"", ""properties"": {}, ""classifier"": ""M3""}}}]}, ""subcomponents"": {}, ""identifier"": ""Process_B"", ""properties"": {""property"": {""name"": ""Actual_Processor_Binding"", ""property_value"": {""list"": {""reference"": {""value"": ""CPU_B""}}}}}, ""classifier"": ""PB""}, {""category"": ""processor"", ""features"": {}, ""subcomponents"": {}, ""identifier"": ""CPU_B"", ""properties"": {}, ""classifier"": ""CPU.B""}, {""category"": ""process"", ""features"": {""feature"": {""direction"": {""kind"": ""in""}, ""identifier"": ""M3_In"", ""type"": {""kind"": ""event_data""}, ""corresponding_instance"": {""component"": {""category"": ""data"", ""features"": {}, ""subcomponents"": {}, ""identifier"": ""M3"", ""properties"": {}, ""classifier"": ""M3""}}}}, ""subcomponents"": {}, ""identifier"": ""Process_C"", ""properties"": {""property"": {""name"": ""Actual_Processor_Binding"", ""property_value"": {""list"": {""reference"": {""value"": ""CPU_C""}}}}}, ""classifier"": ""PC""}, {""category"": ""processor"", ""features"": {}, ""subcomponents"": {}, ""identifier"": ""CPU_C"", ""properties"": {""property"": {""name"": ""Scheduling_Protocol"", ""property_value"": {""list"": {""enumeration"": {""value"": ""POSIX_1003_HIGHEST_PRIORITY_FIRST_PROTOCOL""}}}}}, ""classifier"": ""CPU.C""}, {""category"": ""bus"", ""features"": {}, ""subcomponents"": {}, ""identifier"": ""CAN"", ""properties"": {""property"": {""name"": ""Bus_Properties::Available_Bandwidth"", ""property_value"": {""list"": {""number"": [{""unit"": ""KBytesps"", ""value"": ""20""}, {""unit"": ""KBytesps"", ""value"": ""100""}, {""unit"": ""KBytesps"", ""value"": ""500""}, {""unit"": ""MBytesps"", ""value"": ""1""}]}}}}, ""classifier"": ""CAN""}]}, ""connections"": {""connection"": [{""src"": {""component"": ""Process_A"", ""feature"": ""m1_out""}, ""dst"": {""component"": ""Process_B"", ""feature"": ""m1_in""}, ""type"": ""port_connection"", ""name"": ""C1"", ""properties"": {""property"": {""name"": ""Actual_Connection_Binding"", ""property_value"": {""list"": {""reference"": {""value"": ""CAN""}}}}}}, {""src"": {""component"": ""Process_B"", ""feature"": ""m2_out""}, ""dst"": {""component"": ""Process_A"", ""feature"": ""m2_in""}, ""type"": ""port_connection"", ""name"": ""C2"", ""properties"": {""property"": {""name"": ""Actual_Connection_Binding"", ""property_value"": {""list"": {""reference"": {""value"": ""CAN""}}}}}}, {""src"": {""component"": ""Process_B"", ""feature"": ""m3_out""}, ""dst"": {""component"": ""Process_C"", ""feature"": ""m3_in""}, ""type"": ""port_connection"", ""name"": ""C3"", ""properties"": {""property"": {""name"": ""Actual_Connection_Binding"", ""property_value"": {""list"": {""reference"": {""value"": ""CAN""}}}}}}]}, ""identifier"": ""Car.impl"", ""properties"": {}, ""classifier"": ""Car.impl""}}, ""root_system"": ""Car.impl""}}".

Definition car_AADL := Map_JSON_String_To_Component car.

Lemma car_AADL_OK : Is_AADL_Instance (Get_Instance car_AADL) /\
                    Well_Formed_Component_Instance (Get_Instance car_AADL).
Proof.
  split.
  - prove_Is_AADL_Instance.
  - prove_Well_Formed_Component_Instance.
Qed.

(** ** RMA example from https://github.com/OpenAADL/AADLib/tree/master/examples/rma *)

Definition rma_test_JSON : string := "{""aadl_xml"": {""components"": {""component"": {""category"": ""system"", ""features"": {}, ""subcomponents"": {""component"": [{""category"": ""process"", ""features"": {}, ""subcomponents"": {""component"": [{""category"": ""thread"", ""features"": {}, ""subcomponents"": {}, ""identifier"": ""Task1"", ""properties"": {""property"": [{""name"": ""Deadline"", ""property_value"": {""integer_unit"": {""unit"": ""ms"", ""value"": ""1000""}}}, {""name"": ""Compute_Execution_time"", ""property_value"": {""integer_range_unit"": {""value_low"": ""0"", ""value_high"": ""3"", ""unit_high"": ""ms"", ""unit_low"": ""ms""}}}, {""name"": ""Period"", ""property_value"": {""integer_unit"": {""unit"": ""ms"", ""value"": ""1000""}}}, {""name"": ""Priority"", ""property_value"": {""integer"": {""value"": ""1""}}}, {""name"": ""Dispatch_Protocol"", ""property_value"": {""enumeration"": {""value"": ""Periodic""}}}]}, ""classifier"": ""Task.impl_1""}, {""category"": ""thread"", ""features"": {}, ""subcomponents"": {}, ""identifier"": ""Task2"", ""properties"": {""property"": [{""name"": ""Deadline"", ""property_value"": {""integer_unit"": {""unit"": ""ms"", ""value"": ""500""}}}, {""name"": ""Compute_Execution_time"", ""property_value"": {""integer_range_unit"": {""value_low"": ""0"", ""value_high"": ""5"", ""unit_high"": ""ms"", ""unit_low"": ""ms""}}}, {""name"": ""Period"", ""property_value"": {""integer_unit"": {""unit"": ""ms"", ""value"": ""500""}}}, {""name"": ""Priority"", ""property_value"": {""integer"": {""value"": ""2""}}}, {""name"": ""Dispatch_Protocol"", ""property_value"": {""enumeration"": {""value"": ""Periodic""}}}]}, ""classifier"": ""Task.impl_2""}]}, ""identifier"": ""node_a"", ""properties"": {""property"": {""name"": ""Actual_Processor_Binding"", ""property_value"": {""list"": {""reference"": {""value"": ""cpu""}}}}}, ""classifier"": ""node_a.impl""}, {""category"": ""processor"", ""features"": {}, ""subcomponents"": {}, ""identifier"": ""cpu"", ""properties"": {""property"": [{""name"": ""Scheduling_Protocol"", ""property_value"": {""list"": {""enumeration"": {""value"": ""POSIX_1003_HIGHEST_PRIORITY_FIRST_PROTOCOL""}}}}, {""name"": ""Processor_properties::Max_Prio_First"", ""property_value"": {""enumeration"": {""value"": ""high""}}}, {""name"": ""Scheduling_Protocol"", ""property_value"": {""list"": {""enumeration"": {""value"": ""POSIX_1003_HIGHEST_PRIORITY_FIRST_PROTOCOL""}}}}, {""name"": ""Deployment::Execution_Platform"", ""property_value"": {""enumeration"": {""value"": ""Native""}}}]}, ""classifier"": ""cpu.impl""}]}, ""identifier"": ""rma.impl"", ""properties"": {}, ""classifier"": ""rma.impl""}}, ""root_system"": ""rma.impl""}}".

Definition rma_test_AADL := Map_JSON_String_To_Component rma_test_JSON.

Lemma rma_test_AADL_OK : Well_Formed_Component_Instance (Get_Instance rma_test_AADL).
Proof.
  prove_Well_Formed_Component_Instance.
Qed.
