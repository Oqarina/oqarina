(* begin hide *)
(** Coq Library *)
Require Import List.
Import ListNotations. (* from List *)
Require Import Coq.Lists.ListDec.
Require Import Coq.ZArith.ZArith.

(** Oqarina library *)
Require Import Oqarina.core.all.
Require Import Oqarina.coq_utils.utils.
Require Import Oqarina.AADL.Kernel.all.
Require Import Oqarina.AADL.property_sets.aadl_project.
(* end hide *)

(** %\N \texttt{communication\_properties}% as Coq/AADL property_types. *)

Definition Deployment_Properties_PS :=
    PropertySet (Id "Deployment_Properties") [

    (* 	Actual_Processor_Binding: inherit list of reference (processor, virtual processor, system, device, abstract)
		applies to (thread, thread group, process, system, virtual processor, device);*)

    "Actual_Processor_Binding" :prop PT_Reference
      => None applies [CompCat thread ; CompCat threadGroup ; CompCat process ; CompCat system ;
                       CompCat virtualProcessor ; CompCat device] ;

    (* 	Scheduling_Protocol: inherit list of Supported_Scheduling_Protocols
		applies to (virtual processor, processor, system);*)

    "Scheduling_Protocol" :prop PT_TypeRef (PSQN "AADL_Project" "Supported_Scheduling_Protocols")
        => None applies [ CompCat virtualProcessor; CompCat processor ; CompCat system ]

    ].

Lemma Deployment_Properties_PS_Valid :
  typecheck_property_sets [AADL_Project_PS ; Deployment_Properties_PS] = true.
Proof.
  trivial.
Qed.
