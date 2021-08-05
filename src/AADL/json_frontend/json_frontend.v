From JSON Require Import
    Lexer
    Printer.

From Oqarina Require Import
    Kernel.all
    core.identifiers.
Import
  List
  ListNotations.

Definition get_identifier (i : string) (j : json) :=
  match get_string i j with
  | Some s => Id s
  | _ => empty_identifier
  end.

Definition Map_ComponentCategory (cat : json) :=
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

Definition Map_Feature_Direction (j : json) :=
  match j with
    | JSON__Object [("kind", JSON__String "out")] => outF
    | JSON__Object [("kind", JSON__String "in")] => inF
    | JSON__Object [("kind", JSON__String "inout")] => inoutF
    | _ => nullDirection
  end.

Definition Map_Feature_Category (j : json) :=
  match j with
    | JSON__Object [("kind", JSON__String "data")] => dataPort
    | JSON__Object [("kind", JSON__String "event")] => eventPort
    | JSON__Object [("kind", JSON__String "event_data")] => eventDataPort
    | JSON__Object [("kind", JSON__String "feature")] => abstractFeature
    | _ => invalid
  end.

Definition id_map (i : json) : option json :=
  Some i.

Definition get_json_list (j : json) :=
  match get_list id_map j with
  | Some l => l
  | None => []
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

Fixpoint Map_Component (fuel : nat) (c : list json) : list component :=
  match fuel with
  | 0%nat => nil
  | S m =>
    match c with
    | (JSON__Object f) :: t =>
       ( Component (get_identifier "identifier" (JSON__Object f))
                   (Map_ComponentCategory (get_json "category" (JSON__Object f)))
                   empty_fqname (* classifier *)
                   (Map_Feature m (get_features (JSON__Object f))) (* features *)
                   (Map_Component m (get_subcomponents (JSON__Object f))) (* subcomponents *)
                   nil (* properties *)
                   nil (* connections *)
       )
      :: (Map_Component m t)
    | _ => []
    end
  end
with Map_Feature (fuel : nat) (j : list json) :=
  match fuel with
  | 0%nat => nil
  | S m =>
    match j with
      | (JSON__Object o) :: t =>
        ( Feature (get_identifier "identifier" (JSON__Object o)) (* identifier *)
                (Map_Feature_Direction (get_json "direction" (JSON__Object o))) (* directionType *)
                (Map_Feature_Category (get_json "type" (JSON__Object o))) (* feature category *)
                (hd nil_component (Map_Component m [get_json "component" (get_json "corresponding_instance" (JSON__Object o))]))
                nil (* properties *)
        )
        :: Map_Feature m t
      | _ => [  ]
      end
  end.

Definition Map_JSON (AST : option string + json) :=
  match AST with
    | inr (JSON__Object l) =>
    let aadl_xml := get_json "aadl_xml" (JSON__Object l) in
    let comps := get_json "components" aadl_xml in
      Map_Component 10 ([get_json "component" comps])
    | _ =>  []
  end.

(*

Definition pc := from_string "{""aadl_xml"": {""components"": {""component"": {""category"": ""system"", ""features"": {}, ""subcomponents"": {""component"": [{""category"": ""process"", ""features"": {""feature"": {""direction"": {""kind"": ""out""}, ""identifier"": ""Alpha"", ""type"": {""kind"": ""data""}, ""corresponding_instance"": {""component"": {""category"": ""data"", ""features"": {}, ""subcomponents"": {}, ""identifier"": ""Alpha_Type"", ""properties"": {""property"": {""name"": ""Data_Model::Data_Representation"", ""property_value"": {""enumeration"": {""value"": ""Integer""}}}}, ""classifier"": ""Alpha_Type""}}}}, ""subcomponents"": {""component"": {""category"": ""thread"", ""features"": {""feature"": {""direction"": {""kind"": ""out""}, ""identifier"": ""Data_Source"", ""type"": {""kind"": ""event_data""}, ""corresponding_instance"": {""component"": {""category"": ""data"", ""features"": {}, ""subcomponents"": {}, ""identifier"": ""Alpha_Type"", ""properties"": {""property"": {""name"": ""Data_Model::Data_Representation"", ""property_value"": {""enumeration"": {""value"": ""Integer""}}}}, ""classifier"": ""Alpha_Type""}}}}, ""subcomponents"": {}, ""connections"": {""connection"": {""src"": {""component"": ""P_Spg"", ""feature"": ""data_source""}, ""dst"": {""feature"": ""Data_Source""}, ""type"": ""parameter"", ""name"": ""Z1"", ""properties"": {}}}, ""identifier"": ""Producer"", ""properties"": {""property"": [{""name"": ""Period"", ""property_value"": {""number"": {""unit"": ""ms"", ""value"": ""500""}}}, {""name"": ""Priority"", ""property_value"": {""number"": {""value"": ""1""}}}, {""name"": ""Compute_Execution_Time"", ""property_value"": {""range"": {""value_low"": ""1"", ""value_high"": ""10"", ""unit"": ""ms""}}}, {""name"": ""Dispatch_Protocol"", ""property_value"": {""enumeration"": {""value"": ""Periodic""}}}]}, ""classifier"": ""P.Impl""}}, ""connections"": {""connection"": {""src"": {""component"": ""Producer"", ""feature"": ""data_source""}, ""dst"": {""feature"": ""Alpha""}, ""type"": ""port_connection"", ""name"": ""Z3"", ""properties"": {}}}, ""identifier"": ""pr_A"", ""properties"": {""property"": {""name"": ""Actual_Processor_Binding"", ""property_value"": {""list"": {""reference"": {""value"": ""CPU_A""}}}}}, ""classifier"": ""A.Impl""}, {""category"": ""processor"", ""features"": {}, ""subcomponents"": {}, ""identifier"": ""CPU_A"", ""properties"": {""property"": {""name"": ""Deployment::Execution_Platform"", ""property_value"": {""enumeration"": {""value"": ""Native""}}}}, ""classifier"": ""the_processor""}, {""category"": ""device"", ""features"": {""feature"": {""direction"": {""kind"": ""none""}, ""identifier"": ""Eth"", ""type"": {""kind"": ""access""}, ""corresponding_instance"": {""component"": {""category"": ""bus"", ""features"": {}, ""subcomponents"": {}, ""identifier"": ""Ethernet.impl"", ""properties"": {""property"": {""name"": ""Bus_Properties::Available_Bandwidth"", ""property_value"": {""list"": {""number"": [{""unit"": ""MBytesps"", ""value"": ""10""}, {""unit"": ""MBytesps"", ""value"": ""100""}, {""unit"": ""GBytesps"", ""value"": ""1""}]}}}}, ""classifier"": ""Ethernet.impl""}}}}, ""subcomponents"": {}, ""identifier"": ""Eth1"", ""properties"": {""property"": [{""name"": ""Actual_Processor_Binding"", ""property_value"": {""list"": {""reference"": {""value"": ""CPU_A""}}}}, {""name"": ""Deployment::Location"", ""property_value"": {""string"": {""value"": ""ip 127.0.0.1 1233""}}}, {""name"": ""Initialize_Entrypoint"", ""property_value"": {""classifier"": {""value"": ""PolyORB_HI_Ada_BSD_Socket_Initialize""}}}, {""name"": ""Device_Driver"", ""property_value"": {""classifier"": {""value"": ""BSD_Sockets_Driver.POHI_Ada""}}}, {""name"": ""Deployment::Driver_Name"", ""property_value"": {""string"": {""value"": ""sockets""}}}]}, ""classifier"": ""Native_Sockets.POHI_ADA""}, {""category"": ""process"", ""features"": {""feature"": {""direction"": {""kind"": ""in""}, ""identifier"": ""Beta"", ""type"": {""kind"": ""data""}, ""corresponding_instance"": {""component"": {""category"": ""data"", ""features"": {}, ""subcomponents"": {}, ""identifier"": ""Alpha_Type"", ""properties"": {""property"": {""name"": ""Data_Model::Data_Representation"", ""property_value"": {""enumeration"": {""value"": ""Integer""}}}}, ""classifier"": ""Alpha_Type""}}}}, ""subcomponents"": {""component"": {""category"": ""thread"", ""features"": {""feature"": {""direction"": {""kind"": ""in""}, ""identifier"": ""Data_Sink"", ""type"": {""kind"": ""event_data""}, ""corresponding_instance"": {""component"": {""category"": ""data"", ""features"": {}, ""subcomponents"": {}, ""identifier"": ""Alpha_Type"", ""properties"": {""property"": {""name"": ""Data_Model::Data_Representation"", ""property_value"": {""enumeration"": {""value"": ""Integer""}}}}, ""classifier"": ""Alpha_Type""}}}}, ""subcomponents"": {}, ""connections"": {""connection"": {""src"": {""feature"": ""Data_Sink""}, ""dst"": {""component"": ""Q_Spg"", ""feature"": ""data_sink""}, ""type"": ""parameter"", ""name"": ""Z2"", ""properties"": {}}}, ""identifier"": ""Consumer"", ""properties"": {""property"": [{""name"": ""Period"", ""property_value"": {""number"": {""unit"": ""ms"", ""value"": ""10""}}}, {""name"": ""Priority"", ""property_value"": {""number"": {""value"": ""2""}}}, {""name"": ""Compute_Execution_Time"", ""property_value"": {""range"": {""value_low"": ""1"", ""value_high"": ""20"", ""unit"": ""ms""}}}, {""name"": ""Dispatch_Protocol"", ""property_value"": {""enumeration"": {""value"": ""Sporadic""}}}]}, ""classifier"": ""Q.Impl""}}, ""connections"": {""connection"": {""src"": {""feature"": ""Beta""}, ""dst"": {""component"": ""Consumer"", ""feature"": ""data_sink""}, ""type"": ""port_connection"", ""name"": ""Z4"", ""properties"": {}}}, ""identifier"": ""pr_B"", ""properties"": {""property"": [{""name"": ""Actual_Processor_Binding"", ""property_value"": {""list"": {""reference"": {""value"": ""CPU_B""}}}}, {""name"": ""Deployment::port_number"", ""property_value"": {""number"": {""value"": ""4002""}}}]}, ""classifier"": ""B.Impl""}, {""category"": ""processor"", ""features"": {}, ""subcomponents"": {}, ""identifier"": ""CPU_B"", ""properties"": {""property"": {""name"": ""Deployment::Execution_Platform"", ""property_value"": {""enumeration"": {""value"": ""Native""}}}}, ""classifier"": ""the_processor""}, {""category"": ""device"", ""features"": {""feature"": {""direction"": {""kind"": ""none""}, ""identifier"": ""Eth"", ""type"": {""kind"": ""access""}, ""corresponding_instance"": {""component"": {""category"": ""bus"", ""features"": {}, ""subcomponents"": {}, ""identifier"": ""Ethernet.impl"", ""properties"": {""property"": {""name"": ""Bus_Properties::Available_Bandwidth"", ""property_value"": {""list"": {""number"": [{""unit"": ""MBytesps"", ""value"": ""10""}, {""unit"": ""MBytesps"", ""value"": ""100""}, {""unit"": ""GBytesps"", ""value"": ""1""}]}}}}, ""classifier"": ""Ethernet.impl""}}}}, ""subcomponents"": {}, ""identifier"": ""Eth2"", ""properties"": {""property"": [{""name"": ""Actual_Processor_Binding"", ""property_value"": {""list"": {""reference"": {""value"": ""CPU_B""}}}}, {""name"": ""Deployment::Location"", ""property_value"": {""string"": {""value"": ""ip 127.0.0.1 1234""}}}, {""name"": ""Initialize_Entrypoint"", ""property_value"": {""classifier"": {""value"": ""PolyORB_HI_Ada_BSD_Socket_Initialize""}}}, {""name"": ""Device_Driver"", ""property_value"": {""classifier"": {""value"": ""BSD_Sockets_Driver.POHI_Ada""}}}, {""name"": ""Deployment::Driver_Name"", ""property_value"": {""string"": {""value"": ""sockets""}}}]}, ""classifier"": ""Native_Sockets.POHI_ADA""}, {""category"": ""bus"", ""features"": {}, ""subcomponents"": {}, ""identifier"": ""the_bus"", ""properties"": {""property"": {""name"": ""Bus_Properties::Available_Bandwidth"", ""property_value"": {""list"": {""number"": [{""unit"": ""MBytesps"", ""value"": ""10""}, {""unit"": ""MBytesps"", ""value"": ""100""}, {""unit"": ""GBytesps"", ""value"": ""1""}]}}}}, ""classifier"": ""Ethernet.impl""}]}, ""connections"": {""connection"": [{""src"": {""feature"": ""the_bus""}, ""dst"": {""component"": ""Eth1"", ""feature"": ""eth""}, ""type"": ""access_bus"", ""name"": ""Z5"", ""properties"": {}}, {""src"": {""feature"": ""the_bus""}, ""dst"": {""component"": ""Eth2"", ""feature"": ""eth""}, ""type"": ""access_bus"", ""name"": ""Z5b"", ""properties"": {}}, {""src"": {""component"": ""pr_A"", ""feature"": ""alpha""}, ""dst"": {""component"": ""pr_B"", ""feature"": ""beta""}, ""type"": ""port_connection"", ""name"": ""Z6"", ""properties"": {""property"": {""name"": ""Actual_Connection_Binding"", ""property_value"": {""list"": {""reference"": {""value"": ""the_bus""}}}}}}]}, ""identifier"": ""PC_Simple.Native"", ""properties"": {}, ""classifier"": ""PC_Simple.Native""}}, ""root_system"": ""PC_Simple.Native""}}".

Definition pc2 := from_string "{""aadl_xml"": {""components"": {""component"": {""category"": ""system"", ""features"": {}, ""subcomponents"": {""component"": [{""category"": ""process"", ""features"": {""feature"": {""direction"": {""kind"": ""out""}, ""identifier"": ""Alpha"", ""type"": {""kind"": ""data""}, ""corresponding_instance"": {""component"": {""category"": ""data"", ""features"": {}, ""subcomponents"": {}, ""identifier"": ""Alpha_Type"", ""properties"": {}, ""classifier"": ""Alpha_Type""}}}}, ""subcomponents"": {}, ""identifier"": ""pr_A"", ""properties"": {}, ""classifier"": ""A""}, {""category"": ""process"", ""features"": {""feature"": {""direction"": {""kind"": ""in""}, ""identifier"": ""Beta"", ""type"": {""kind"": ""data""}, ""corresponding_instance"": {""component"": {""category"": ""data"", ""features"": {}, ""subcomponents"": {}, ""identifier"": ""Alpha_Type"", ""properties"": {}, ""classifier"": ""Alpha_Type""}}}}, ""subcomponents"": {}, ""identifier"": ""pr_B"", ""properties"": {}, ""classifier"": ""B""}]}, ""connections"": {""connection"": {""src"": {""component"": ""pr_A"", ""feature"": ""alpha""}, ""dst"": {""component"": ""pr_B"", ""feature"": ""beta""}, ""type"": ""port_connection"", ""name"": ""Z6"", ""properties"": {}}}, ""identifier"": ""PC_Simple.Native"", ""properties"": {}, ""classifier"": ""PC_Simple.Native""}}, ""root_system"": ""PC_Simple.Native""}}".

Definition car := from_string "{""aadl_xml"": {""components"": {""component"": {""category"": ""system"", ""features"": {}, ""subcomponents"": {""component"": [{""category"": ""process"", ""features"": {""feature"": [{""direction"": {""kind"": ""out""}, ""identifier"": ""M1_Out"", ""type"": {""kind"": ""event_data""}, ""corresponding_instance"": {""component"": {""category"": ""data"", ""features"": {}, ""subcomponents"": {}, ""identifier"": ""M1"", ""properties"": {}, ""classifier"": ""M1""}}}, {""direction"": {""kind"": ""in""}, ""identifier"": ""M2_In"", ""type"": {""kind"": ""event_data""}, ""corresponding_instance"": {""component"": {""category"": ""data"", ""features"": {}, ""subcomponents"": {}, ""identifier"": ""M2"", ""properties"": {}, ""classifier"": ""M2""}}}]}, ""subcomponents"": {}, ""identifier"": ""Process_A"", ""properties"": {""property"": {""name"": ""Actual_Processor_Binding"", ""property_value"": {""list"": {""reference"": {""value"": ""CPU_A""}}}}}, ""classifier"": ""PA""}, {""category"": ""processor"", ""features"": {}, ""subcomponents"": {}, ""identifier"": ""CPU_A"", ""properties"": {}, ""classifier"": ""CPU.A""}, {""category"": ""process"", ""features"": {""feature"": [{""direction"": {""kind"": ""in""}, ""identifier"": ""M1_In"", ""type"": {""kind"": ""event_data""}, ""corresponding_instance"": {""component"": {""category"": ""data"", ""features"": {}, ""subcomponents"": {}, ""identifier"": ""M1"", ""properties"": {}, ""classifier"": ""M1""}}}, {""direction"": {""kind"": ""out""}, ""identifier"": ""M2_Out"", ""type"": {""kind"": ""event_data""}, ""corresponding_instance"": {""component"": {""category"": ""data"", ""features"": {}, ""subcomponents"": {}, ""identifier"": ""M2"", ""properties"": {}, ""classifier"": ""M2""}}}, {""direction"": {""kind"": ""out""}, ""identifier"": ""M3_Out"", ""type"": {""kind"": ""event_data""}, ""corresponding_instance"": {""component"": {""category"": ""data"", ""features"": {}, ""subcomponents"": {}, ""identifier"": ""M3"", ""properties"": {}, ""classifier"": ""M3""}}}]}, ""subcomponents"": {}, ""identifier"": ""Process_B"", ""properties"": {""property"": {""name"": ""Actual_Processor_Binding"", ""property_value"": {""list"": {""reference"": {""value"": ""CPU_B""}}}}}, ""classifier"": ""PB""}, {""category"": ""processor"", ""features"": {}, ""subcomponents"": {}, ""identifier"": ""CPU_B"", ""properties"": {}, ""classifier"": ""CPU.B""}, {""category"": ""process"", ""features"": {""feature"": {""direction"": {""kind"": ""in""}, ""identifier"": ""M3_In"", ""type"": {""kind"": ""event_data""}, ""corresponding_instance"": {""component"": {""category"": ""data"", ""features"": {}, ""subcomponents"": {}, ""identifier"": ""M3"", ""properties"": {}, ""classifier"": ""M3""}}}}, ""subcomponents"": {}, ""identifier"": ""Process_C"", ""properties"": {""property"": {""name"": ""Actual_Processor_Binding"", ""property_value"": {""list"": {""reference"": {""value"": ""CPU_C""}}}}}, ""classifier"": ""PC""}, {""category"": ""processor"", ""features"": {}, ""subcomponents"": {}, ""identifier"": ""CPU_C"", ""properties"": {""property"": {""name"": ""Scheduling_Protocol"", ""property_value"": {""list"": {""enumeration"": {""value"": ""POSIX_1003_HIGHEST_PRIORITY_FIRST_PROTOCOL""}}}}}, ""classifier"": ""CPU.C""}, {""category"": ""bus"", ""features"": {}, ""subcomponents"": {}, ""identifier"": ""CAN"", ""properties"": {""property"": {""name"": ""Bus_Properties::Available_Bandwidth"", ""property_value"": {""list"": {""number"": [{""unit"": ""KBytesps"", ""value"": ""20""}, {""unit"": ""KBytesps"", ""value"": ""100""}, {""unit"": ""KBytesps"", ""value"": ""500""}, {""unit"": ""MBytesps"", ""value"": ""1""}]}}}}, ""classifier"": ""CAN""}]}, ""connections"": {""connection"": [{""src"": {""component"": ""Process_A"", ""feature"": ""m1_out""}, ""dst"": {""component"": ""Process_B"", ""feature"": ""m1_in""}, ""type"": ""port_connection"", ""name"": ""C1"", ""properties"": {""property"": {""name"": ""Actual_Connection_Binding"", ""property_value"": {""list"": {""reference"": {""value"": ""CAN""}}}}}}, {""src"": {""component"": ""Process_B"", ""feature"": ""m2_out""}, ""dst"": {""component"": ""Process_A"", ""feature"": ""m2_in""}, ""type"": ""port_connection"", ""name"": ""C2"", ""properties"": {""property"": {""name"": ""Actual_Connection_Binding"", ""property_value"": {""list"": {""reference"": {""value"": ""CAN""}}}}}}, {""src"": {""component"": ""Process_B"", ""feature"": ""m3_out""}, ""dst"": {""component"": ""Process_C"", ""feature"": ""m3_in""}, ""type"": ""port_connection"", ""name"": ""C3"", ""properties"": {""property"": {""name"": ""Actual_Connection_Binding"", ""property_value"": {""list"": {""reference"": {""value"": ""CAN""}}}}}}]}, ""identifier"": ""Car.impl"", ""properties"": {}, ""classifier"": ""Car.impl""}}, ""root_system"": ""Car.impl""}}".

Compute pc.
Compute Map_JSON pc.
Compute Map_JSON pc2.
Compute Map_JSON car.
Compute car.

Definition Map_JSON_ (AST : option string + json) :=
  match AST with
    | inr (JSON__Object l) =>
    let aadl_xml := get_json "aadl_xml" (JSON__Object l) in
    let comps := get_json "components" aadl_xml in
    let comp :=  get_json "component" comps in
      (*get_json "features"*) comp
    | _ =>  JSON__Null
  end.



Definition plop :=
  JSON__Object
  [("category", JSON__String "process");
  ("features",
  JSON__Object
    [("feature",
     JSON__Object
       [("direction",
        JSON__Object [("kind", JSON__String "in")]);
       ("identifier", JSON__String "M3_In");
       ("type",
       JSON__Object
         [("kind", JSON__String "event_data")]);
       ("corresponding_instance",
       JSON__Object
         [("component",
          JSON__Object
            [("category", JSON__String "data");
            ("features", JSON__Object []);
            ("subcomponents", JSON__Object []);
            ("identifier", JSON__String "M3");
            ("properties", JSON__Object []);
            ("classifier", JSON__String "M3")])])])])
  ].

Compute Map_Component 10 [plop].

*)