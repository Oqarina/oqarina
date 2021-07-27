Require Import List String.

Require Import Oqarina.AADL.atin_frontend.atin_lexer.
Require Import Oqarina.AADL.atin_frontend.atin_parser.
Require Import Oqarina.AADL.atin_frontend.atin_frontend.

Open Scope string_scope.

Require Import Oqarina.core.identifiers.
Require Import Oqarina.AADL.Kernel.all.

Definition example := "system s_impl_Instance : test_1::s.impl {
	system test_1::sc sc1 : test_1::s.impl:sc1 {}
}".

Definition AST := string2aadl example.
Compute AST.

Definition Map_ComponentCategory (cat : AST.ComponentCategory_ast) :=
  match cat with
  | AST.COMPONENT_CATEGORY (Id "system") => system
  | AST.COMPONENT_CATEGORY (Id "abstract") => abstract
  | AST.COMPONENT_CATEGORY (Id "bus") => bus
  | AST.COMPONENT_CATEGORY (Id "data") => data
	| AST.COMPONENT_CATEGORY (Id "device") => device
  | AST.COMPONENT_CATEGORY (Id "memory") => memory
  | AST.COMPONENT_CATEGORY (Id "processor") => processor
  | AST.COMPONENT_CATEGORY (Id "process") => process
  | AST.COMPONENT_CATEGORY (Id "subprogram") => subprogram
  | AST.COMPONENT_CATEGORY (Id "subprogram group") => subprogramGroup
  | AST.COMPONENT_CATEGORY (Id "thread group") => threadGroup
	| AST.COMPONENT_CATEGORY (Id "thread") => thread
  | AST.COMPONENT_CATEGORY (Id "virtual bus") => virtualBus
  | AST.COMPONENT_CATEGORY (Id "virtual processor") => virtualProcessor
  | _ => null
  end.

Definition Map_DirectionType (dir : AST.DirectionType_ast) :=
  match dir with
  | AST.DIRECTION_TYPE (Id "in") => inF
  | AST.DIRECTION_TYPE (Id "out") => outF
  | AST.DIRECTION_TYPE (Id "inout") => inoutF
  | AST.DIRECTION_TYPE _ => nullDirection
end.

Definition Map_FeatureCategory (cat : AST.FeatureCategory_ast) :=
  match cat with
  | AST.FEATURE_CATEGORY (Id "dataPort") => dataPort
  | AST.FEATURE_CATEGORY (Id "eventPort") => eventPort
  | AST.FEATURE_CATEGORY (Id "eventDataPort") => eventDataPort
  | AST.FEATURE_CATEGORY (Id "parameter") => parameter
  | AST.FEATURE_CATEGORY (Id "busAccess") => busAccess
  | AST.FEATURE_CATEGORY (Id "dataAccess") => dataAccess
  | AST.FEATURE_CATEGORY (Id "subprogramAccess") => subprogramAccess
  | AST.FEATURE_CATEGORY (Id "subprogramGroupAccess") => subprogramGroupAccess
  | AST.FEATURE_CATEGORY (Id "featureGroup") => featureGroup
  | AST.FEATURE_CATEGORY (Id "abstractFeature") => abstractFeature
  | _ =>invalid
  end.

Definition Map_AST_ID (AST_Id : AST.ID_ast) :=
  match AST_Id with
  | AST.ID ( h :: _ ) => h
  | _ => empty_identifier
  end.

Definition Map_ImplRef (AST_ImplRef : AST.ImplRef_ast) :=
  match AST_ImplRef with
  | AST.IMPL_REF (AST.ID idl) type_id impl_id => FQN idl type_id (Some impl_id)
  end.

Definition Map_ClassifierRef (AST_ClassifierRef : AST.ClassifierRef_ast) :=
  match AST_ClassifierRef with
  | AST.CLASSIFIER_REF (AST.ID idl) type_id => FQN idl type_id None
  end.

Definition Map_DeclarativeRef (AST_DeclarativeRef : AST.DeclarativeRef_ast) :=
    match AST_DeclarativeRef with
      | AST.DECLARATIVE_REF (AST.ID idl) type_id impl_id  => FQN idl type_id (Some impl_id)
    end.

Fixpoint Map_Feature_Subclause (l : list AST.Subclause_ast) :=
  match l with
    | (AST.FEATURE h ) :: t =>
      let Map_Feature_Instance (a : AST.FeatureInstance_ast) :=
      match a with
        | AST.FEATURE_INSTANCE dir cat id declarativeref
          => Feature (Map_AST_ID id)
                     (Map_DirectionType dir)
                     (Map_FeatureCategory cat)
                     nil_component
                     nil
        end in
          Map_Feature_Instance h :: Map_Feature_Subclause t
      | _ :: t => Map_Feature_Subclause t
      | nil => nil
  end.

(** Here we use n as "fuel" for the function because of the mutually recursive types*)
Fixpoint Map_Component_Subclause (n : nat) (l : list AST.Subclause_ast) :=
  match n with
  | 0 => nil
  | S m =>
    match l with
      | (AST.COMPONENT h ) :: t =>
        let Map_Component_Instance (a : AST.ComponentInstance_ast) :=
        match a with
          | AST.COMPONENT_INSTANCE cat classifierref (AST.ID (id :: _)) declarativeref subclauses
            => Component id
                        (Map_ComponentCategory cat)
                        (Map_DeclarativeRef declarativeref)
                        (Map_Feature_Subclause subclauses)
                        (Map_Component_Subclause m subclauses)
                        nil
                        nil
          | _ => nil_component
        end in
          Map_Component_Instance h :: Map_Component_Subclause m t
      | _ :: t => Map_Component_Subclause m t
      | nil => nil
    end
  end.

Definition Map_Root_System (AST : option AST.node) :=
  match AST with
    | Some (AST.ROOT_SYSTEM cat id impl_ref subclauses) =>
      Component (Map_AST_ID id)
                (Map_ComponentCategory cat)
                (Map_ImplRef impl_ref)
                (Map_Feature_Subclause subclauses)
                (Map_Component_Subclause 10 subclauses)
                nil
                nil
    | _ => nil_component
  end.

Compute Map_Root_System AST.

(**
TBD:
- Buses::Ethernet::Ethernet.impl extends Buses::Ethernet::Generic_Ethernet:Eth
but this information is lost in the instance notation below!

*)
Definition example2 :=
  "system PING_Native_Instance : PING_Package::PING.Native {
    bus Buses::Ethernet::Ethernet.impl the_bus : PING_Package::PING.Native:the_bus {
    }
    device Native_Sockets::Native_Sockets.POHI_ADA Eth1 : PING_Package::PING.Native:Eth1 {
      in busAccess Eth : Buses::Ethernet::Generic_Ethernet:Eth
    }
    device Native_Sockets::Native_Sockets.POHI_ADA Eth2 : PING_Package::PING.Native:Eth2 {
      in busAccess Eth : Buses::Ethernet::Generic_Ethernet:Eth
    }
    process PING_Package::A.Impl Node_A : PING_Package::PING.Native:Node_A {
      out eventDataPort Out_Port : PING_Package::A:Out_Port
      thread Software::P.Impl Pinger : PING_Package::A.Impl:Pinger {
        out eventDataPort Data_Source : Software::P:Data_Source
      }
    }
    process PING_Package::B.Impl Node_B : PING_Package::PING.Native:Node_B {
      in eventDataPort In_Port : PING_Package::B:In_Port
      thread Software::Q.Impl Ping_Me : PING_Package::B.Impl:Ping_Me {
        in eventDataPort Data_Sink : Software::Q:Data_Sink
      }
    }
    processor PING_Package::the_processor CPU_A : PING_Package::PING.Native:CPU_A {
    }
    processor PING_Package::the_processor CPU_B : PING_Package::PING.Native:CPU_B {
    }
  }".

Definition AST2 := string2aadl example2.
Compute Map_Root_System AST2.
