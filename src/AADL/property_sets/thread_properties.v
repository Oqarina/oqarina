(** %\section{\texttt{Thread\_Properties}} %*)

(* begin hide *)
(** Coq Library *)
Require Import List.
Import ListNotations. (* from List *)
Require Import Coq.ZArith.ZArith.

(** Oqarina library *)
Require Import Oqarina.core.all.
Require Import Oqarina.AADL.Kernel.all.
Require Import Oqarina.AADL.property_sets.aadl_project.
(* end hide *)

(** %\N \texttt{thread\_properties}% as Coq/AADL property_types. *)

Definition Thread_Properties_PS :=
    PropertySet (Id "Thread_Properties") [

    (* Dispatch_Protocol: Supported_Dispatch_Protocols
        applies to (thread, device, virtual processor); *)

    "Dispatch_Protocol" :prop PT_TypeRef (PSQN "AADL_Project" "Supported_Dispatch_Protocols")
        => None applies [ CompCat thread ; CompCat device ; CompCat virtualProcessor ];

    (* Dispatch_Able: aadlboolean applies to (thread); *)

    "Dispatch_Able" :prop aadlboolean => None applies [ CompCat thread ];

    (* Priority: inherit aadlinteger
        applies to (thread, thread group, process, system, device, data); *)

    "Priority" :prop aadlinteger
      => None
      applies [ CompCat thread ; CompCat threadGroup ; CompCat process ;
      CompCat system ; CompCat device ; CompCat data];

    (* Urgency: aadlinteger 0 .. Max_Urgency
      applies to (port, subprogram); *)
    (* XXX how to resolve Max_Urgency? *)

    "Urgency" :prop PT_Number aadlinteger (Some (C_IntRange (IRC 0 42))) None => None applies [];

    (* Dequeue_Protocol: enumeration (OneItem, MultipleItems, AllItems) => OneItem
		  applies to (event port, event data port); *)

    "Dequeue_Protocol" :prop PT_Enumeration [
        Id "OneItem"; Id "MultipleItems"; Id "AllItems" ]
        => (Some (PV_Enum (Id "OneItem")))
        applies [ FeatureCat eventPort ; FeatureCat eventDataPort ];

    (* Dequeued_Items: aadlinteger
		   applies to (event port, event data port); *)

    "Dequeued_Items" :prop aadlinteger
       => None applies [ FeatureCat eventPort ; FeatureCat eventDataPort ]

].

Lemma Thread_Properties_PS_Valid :
  typecheck_property_sets [AADL_Project_PS ; Thread_Properties_PS] = true.
Proof.
  trivial.
Qed.

(** %
  \begin{definition}[Priority (AADLv2.2 \S XXX]
 TBD
  \end{definition}
% *)

Definition Priority_Name := PSQN "Thread_Properties" "Priority".

Definition Is_Priority (pa : property_association) :=
  Is_Property_Name Priority_Name pa.

Definition Map_Priority (pa : list property_association) : Z :=
  Map_PV_Int_List pa (PV_Int 0%Z) Is_Priority.

(** %
  \begin{definition}[Urgency (AADLv2.2 \S XXX]
 TBD
  \end{definition}
% *)

Definition Urgency_Name := PSQN "Thread_Properties" "Urgency".

Definition Is_Urgency (pa : property_association) :=
  Is_Property_Name Urgency_Name pa.

Definition Map_Urgency (pa : list property_association) : Z :=
  Map_PV_Int_List pa (PV_Int 0%Z) Is_Urgency.

(**
%
  \begin{definition}[Dispatch\_Protocol (AADLv2.2 \S 5.4.2 (34)\index{Dispatch\_Protocol (AADL)}]
  The \texttt{Dispatch\_Protocol} property of a thread determines the characteristics of dispatch requests to the thread.
  \end{definition}
% *)

Definition Dispatch_Protocol_Name := PSQN "Thread_Properties" "Dispatch_Protocol".

Definition Is_Scheduling_Protocol (pa : property_association) :=
    Is_Property_Name Dispatch_Protocol_Name pa.

Inductive Dispatch_Protocol :=
  Unspecified_Dispatch_Protocol | Periodic | Sporadic | Aperiodic | Background | Timed | Hybrid.

Scheme Equality for Dispatch_Protocol.

Definition Map_Scheduling_Protocol_pv (pa : property_association) : Dispatch_Protocol :=
  match pa.(PV) with
    | (PV_Enum (Id "Periodic")) => Periodic
    | (PV_Enum (Id "Sporadic")) => Sporadic
    | (PV_Enum (Id "Aperiodic")) => Aperiodic
    | (PV_Enum (Id "Background")) => Background
    | (PV_Enum (Id "Timed")) => Timed
    | (PV_Enum (Id "Hybrid")) => Hybrid
    | _ => Unspecified_Dispatch_Protocol
  end.

Definition Map_Scheduling_Protocol (pa : list property_association) : Dispatch_Protocol :=
  match filter Is_Scheduling_Protocol pa with
  | nil => Unspecified_Dispatch_Protocol
  | v :: _ => Map_Scheduling_Protocol_pv v
  end.

(** %
  \begin{definition}[Overflow\_Handling\_Protocol (AADLv2.2 \S XXX]
 TBD
  \end{definition}
% *)

Definition Dequeue_Protocol_Name := PSQN "Thread_Properties" "Dequeue_Protocol".

Definition Is_Dequeue_Protocol (pa : property_association) :=
  Is_Property_Name Dequeue_Protocol_Name pa.

Inductive Dequeue_Protocol :=
  Unspecified_Dequeue_Protocol | OneItem | MultipleItems | AllItems.

Scheme Equality for Dequeue_Protocol.

Definition Map_Dequeue_Protocol_pv (pv : property_value) : Dequeue_Protocol :=
  match pv with
    | (PV_Enum (Id "OneItem")) => OneItem
    | (PV_Enum (Id "MultipleItems")) => MultipleItems
    | (PV_Enum (Id "AllItems")) => AllItems
    | _ => Unspecified_Dequeue_Protocol
  end.

Definition Map_Dequeue_Protocol (pa : list property_association) :=
  match filter Is_Dequeue_Protocol pa with
  | nil =>
    let pv := resolve_default_value [Thread_Properties_PS] Dequeue_Protocol_Name in
    match pv with
      | None => Unspecified_Dequeue_Protocol (* should never be executed *)
      | Some pv_ => Map_Dequeue_Protocol_pv pv_
    end
  | v :: _ => Map_Dequeue_Protocol_pv v.(PV)
  end.

(** %
  \begin{definition}[Dequeued\_Items (AADLv2.2 \S XXX]
 TBD
  \end{definition}
% *)

Definition Dequeued_Items_Name := PSQN "Thread_Properties" "Dequeued_Items".

Definition Is_Dequeued_Items (pa : property_association) :=
  Is_Property_Name Dequeued_Items_Name pa.

Definition Map_Dequeued_Items (pa : list property_association) : Z :=
  Map_PV_Int_List pa (PV_Int 0%Z) Is_Dequeued_Items.

(** %
  \begin{definition}[Dispatch\_Able (AADLv2.2 \S XXX]
 TBD
  \end{definition}
% *)

Definition Dispatch_Able_Name := PSQN "Thread_Properties" "Dispatch_Able".

Definition Is_Dispatch_Able (pa : property_association) :=
  Is_Property_Name Dispatch_Able_Name pa.

Definition Map_Dispatch_Able (pa : list property_association) :=
  Map_PV_Bool_List pa (PV_Bool true) Is_Dequeued_Items.
