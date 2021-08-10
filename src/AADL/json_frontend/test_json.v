From Coq Require Import
    List.
Import ListNotations.

(** Oqarina library *)
From Oqarina Require Import
    coq_utils.utils
    Kernel.all
    core.identifiers
    AADL.json_frontend.json_frontend
    AADL.instance.all.
(** Tests *)

Definition car := "{""aadl_xml"": {""components"": {""component"": {""category"": ""system"", ""features"": {}, ""subcomponents"": {""component"": [{""category"": ""process"", ""features"": {""feature"": [{""direction"": {""kind"": ""out""}, ""identifier"": ""M1_Out"", ""type"": {""kind"": ""event_data""}, ""corresponding_instance"": {""component"": {""category"": ""data"", ""features"": {}, ""subcomponents"": {}, ""identifier"": ""M1"", ""properties"": {}, ""classifier"": ""M1""}}}, {""direction"": {""kind"": ""in""}, ""identifier"": ""M2_In"", ""type"": {""kind"": ""event_data""}, ""corresponding_instance"": {""component"": {""category"": ""data"", ""features"": {}, ""subcomponents"": {}, ""identifier"": ""M2"", ""properties"": {}, ""classifier"": ""M2""}}}]}, ""subcomponents"": {}, ""identifier"": ""Process_A"", ""properties"": {""property"": {""name"": ""Actual_Processor_Binding"", ""property_value"": {""list"": {""reference"": {""value"": ""CPU_A""}}}}}, ""classifier"": ""PA""}, {""category"": ""processor"", ""features"": {}, ""subcomponents"": {}, ""identifier"": ""CPU_A"", ""properties"": {}, ""classifier"": ""CPU.A""}, {""category"": ""process"", ""features"": {""feature"": [{""direction"": {""kind"": ""in""}, ""identifier"": ""M1_In"", ""type"": {""kind"": ""event_data""}, ""corresponding_instance"": {""component"": {""category"": ""data"", ""features"": {}, ""subcomponents"": {}, ""identifier"": ""M1"", ""properties"": {}, ""classifier"": ""M1""}}}, {""direction"": {""kind"": ""out""}, ""identifier"": ""M2_Out"", ""type"": {""kind"": ""event_data""}, ""corresponding_instance"": {""component"": {""category"": ""data"", ""features"": {}, ""subcomponents"": {}, ""identifier"": ""M2"", ""properties"": {}, ""classifier"": ""M2""}}}, {""direction"": {""kind"": ""out""}, ""identifier"": ""M3_Out"", ""type"": {""kind"": ""event_data""}, ""corresponding_instance"": {""component"": {""category"": ""data"", ""features"": {}, ""subcomponents"": {}, ""identifier"": ""M3"", ""properties"": {}, ""classifier"": ""M3""}}}]}, ""subcomponents"": {}, ""identifier"": ""Process_B"", ""properties"": {""property"": {""name"": ""Actual_Processor_Binding"", ""property_value"": {""list"": {""reference"": {""value"": ""CPU_B""}}}}}, ""classifier"": ""PB""}, {""category"": ""processor"", ""features"": {}, ""subcomponents"": {}, ""identifier"": ""CPU_B"", ""properties"": {}, ""classifier"": ""CPU.B""}, {""category"": ""process"", ""features"": {""feature"": {""direction"": {""kind"": ""in""}, ""identifier"": ""M3_In"", ""type"": {""kind"": ""event_data""}, ""corresponding_instance"": {""component"": {""category"": ""data"", ""features"": {}, ""subcomponents"": {}, ""identifier"": ""M3"", ""properties"": {}, ""classifier"": ""M3""}}}}, ""subcomponents"": {}, ""identifier"": ""Process_C"", ""properties"": {""property"": {""name"": ""Actual_Processor_Binding"", ""property_value"": {""list"": {""reference"": {""value"": ""CPU_C""}}}}}, ""classifier"": ""PC""}, {""category"": ""processor"", ""features"": {}, ""subcomponents"": {}, ""identifier"": ""CPU_C"", ""properties"": {""property"": {""name"": ""Scheduling_Protocol"", ""property_value"": {""list"": {""enumeration"": {""value"": ""POSIX_1003_HIGHEST_PRIORITY_FIRST_PROTOCOL""}}}}}, ""classifier"": ""CPU.C""}, {""category"": ""bus"", ""features"": {}, ""subcomponents"": {}, ""identifier"": ""CAN"", ""properties"": {""property"": {""name"": ""Bus_Properties::Available_Bandwidth"", ""property_value"": {""list"": {""number"": [{""unit"": ""KBytesps"", ""value"": ""20""}, {""unit"": ""KBytesps"", ""value"": ""100""}, {""unit"": ""KBytesps"", ""value"": ""500""}, {""unit"": ""MBytesps"", ""value"": ""1""}]}}}}, ""classifier"": ""CAN""}]}, ""connections"": {""connection"": [{""src"": {""component"": ""Process_A"", ""feature"": ""m1_out""}, ""dst"": {""component"": ""Process_B"", ""feature"": ""m1_in""}, ""type"": ""port_connection"", ""name"": ""C1"", ""properties"": {""property"": {""name"": ""Actual_Connection_Binding"", ""property_value"": {""list"": {""reference"": {""value"": ""CAN""}}}}}}, {""src"": {""component"": ""Process_B"", ""feature"": ""m2_out""}, ""dst"": {""component"": ""Process_A"", ""feature"": ""m2_in""}, ""type"": ""port_connection"", ""name"": ""C2"", ""properties"": {""property"": {""name"": ""Actual_Connection_Binding"", ""property_value"": {""list"": {""reference"": {""value"": ""CAN""}}}}}}, {""src"": {""component"": ""Process_B"", ""feature"": ""m3_out""}, ""dst"": {""component"": ""Process_C"", ""feature"": ""m3_in""}, ""type"": ""port_connection"", ""name"": ""C3"", ""properties"": {""property"": {""name"": ""Actual_Connection_Binding"", ""property_value"": {""list"": {""reference"": {""value"": ""CAN""}}}}}}]}, ""identifier"": ""Car.impl"", ""properties"": {}, ""classifier"": ""Car.impl""}}, ""root_system"": ""Car.impl""}}".

Definition Car_AADL := Component (Id "Car.impl") system (FQN [] (Id "") None) []
[Component (Id "Process_A") process (FQN [] (Id "") None)
   [Feature (Id "M1_Out") outF eventDataPort
      (Component (Id "M1") data (FQN [] (Id "") None) [] [] [] [])
      [];
   Feature (Id "M2_In") inF eventDataPort
     (Component (Id "M2") data (FQN [] (Id "") None) [] [] [] [])
     []] [] [] [];
Component (Id "CPU_A") processor (FQN [] (Id "") None) [] [] [] [];
Component (Id "Process_B") process (FQN [] (Id "") None)
  [Feature (Id "M1_In") inF eventDataPort
     (Component (Id "M1") data (FQN [] (Id "") None) [] [] [] [])
     [];
  Feature (Id "M2_Out") outF eventDataPort
    (Component (Id "M2") data (FQN [] (Id "") None) [] [] [] []) [];
  Feature (Id "M3_Out") outF eventDataPort
    (Component (Id "M3") data (FQN [] (Id "") None) [] [] [] []) []]
  [] [] [];
Component (Id "CPU_B") processor (FQN [] (Id "") None) [] [] [] [];
Component (Id "Process_C") process (FQN [] (Id "") None)
  [Feature (Id "M3_In") inF eventDataPort
     (Component (Id "M3") data (FQN [] (Id "") None) [] [] [] [])
     []] [] [] [];
Component (Id "CPU_C") processor (FQN [] (Id "") None) [] [] [] [];
Component (Id "CAN") bus (FQN [] (Id "") None) [] [] [] []] [] [].

Definition f := Oracle (Is_AADL_Instance_dec Car_AADL).
Compute f.

(* XXX the following is disabled. The Lemma can be proved but requires 10 sec.

Lemma car_OK : Map_JSON_String_To_Component car = Car_AADL.
Proof.
  trivial.
Qed.
*)
