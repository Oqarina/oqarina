(** %\section{\texttt{Thread\_Properties}} %*)

(* begin hide *)
(** Coq Library *)
Require Import List.
Import ListNotations. (* from List *)
Require Import Coq.ZArith.ZArith.

(** Oqarina library *)
Require Import Oqarina.core.identifiers.
Require Import Oqarina.properties.all.
Require Import Oqarina.property_sets.aadl_aadl_project.
Require Import Oqarina.aadl_categories.
(* end hide *)

(** ** %\texttt{thread\_properties}% as Coq/AADL property_types *)

Definition Thread_Properties_PS :=
    PropertySet (Id "Thread_Properties") [

    (* Dispatch_Protocol: Supported_Dispatch_Protocols
        applies to (thread, device, virtual processor); *)

    "Dispatch_Protocol" :prop PT_TypeRef (PSQN "AADL_Project" "Supported_Dispatch_Protocols")
        => None applies [ thread ; device ; virtualProcessor ];

    (* Priority: inherit aadlinteger
        applies to (thread, thread group, process, system, device, data); *)

    "Priority" :prop aadlinteger
      => None
      applies [ thread ; threadGroup ; process ; system ; device ; data];

    (* Urgency: aadlinteger 0 .. Max_Urgency
      applies to (port, subprogram); *)
    (* XXX how to resolve Max_Urgency? *)

    "Urgency" :prop PT_Number aadlinteger (Some (C_IntRange (IRC 0 42))) None => None applies [];

    (* Dequeue_Protocol: enumeration (OneItem, MultipleItems, AllItems) => OneItem
		  applies to (event port, event data port); *)

    "Dequeue_Protocol" :prop PT_Enumeration [
        Id "OneItem"; Id "MultipleItems"; Id "AllItems" ]
        => (Some (PV_Enum (Id "OneItem"))) applies [];

    (* Dequeued_Items: aadlinteger
		   applies to (event port, event data port);*)

    "Dequeued_Items" :prop aadlinteger
       => None applies [ ]

].

(** %
  \begin{definition}[Priority (AADLv2.2 \S XXX]
 TBD
  \end{definition}
% *)

Definition Priority_Name := PSQN "thread_properties" "priority".

Definition Is_Priority (pa : property_association) :=
  Is_Property_Name Priority_Name pa.

Definition Map_Priority (pa : list property_association) : Z :=
  Map_PV_Int_List pa 0%Z Is_Priority.

(** %
  \begin{definition}[Urgency (AADLv2.2 \S XXX]
 TBD
  \end{definition}
% *)

Definition Urgency_Name := PSQN "thread_properties" "urgency".

Definition Is_Urgency (pa : property_association) :=
  Is_Property_Name Urgency_Name pa.

Definition Map_Urgency (pa : list property_association) : Z :=
  Map_PV_Int_List pa 0%Z Is_Urgency.

(**
%
  \begin{definition}[Dispatch\_Protocol (AADLv2.2 \S 5.4.2 (34)\index{Dispatch\_Protocol (AADL)}]
  The \texttt{Dispatch\_Protocol} property of a thread determines the characteristics of dispatch requests to the thread.
  \end{definition}
% *)

Definition Dispatch_Protocol_Name := PSQN "thread_properties" "dispatch_protocol".

Definition Is_Scheduling_Protocol (pa : property_association) :=
    Is_Property_Name Dispatch_Protocol_Name pa.

(** ** %\texttt{thread\_properties}% as Coq native types *)

(** %\paragraph{}
  \begin{definition}[Dispatch\_Protocol (Coq)]
  TBD
  \end{definition}
%
*)

Inductive Dispatch_Protocol :=
  Dispatch_Protocol_Unspecified | Periodic | Sporadic | Aperiodic | Background | Timed | Hybrid.

Scheme Equality for Dispatch_Protocol.

Definition Map_Scheduling_Protocol_pv (pa : property_association) : Dispatch_Protocol :=
  match pa.(PV) with
    | (PV_Enum (Id "periodic")) => Periodic
    | (PV_Enum (Id "sporadic")) => Sporadic
    | (PV_Enum (Id "aperiodic")) => Aperiodic
    | (PV_Enum (Id "background")) => Background
    | (PV_Enum (Id "timed")) => Timed
    | (PV_Enum (Id "Hybrid")) => Hybrid
    | _ => Dispatch_Protocol_Unspecified
  end.

Definition Map_Scheduling_Protocol (pa : list property_association) : Dispatch_Protocol :=
  match filter Is_Scheduling_Protocol pa with
  | nil => Dispatch_Protocol_Unspecified
  | v :: _ => Map_Scheduling_Protocol_pv v
  end.

(** %
  \begin{definition}[Overflow\_Handling\_Protocol (AADLv2.2 \S XXX]
 TBD
  \end{definition}
% *)

Definition Dequeue_Protocol_Name := PSQN "thread_properties" "dequeue_protocol".

Definition Is_Dequeue_Protocol (pa : property_association) :=
  Is_Property_Name Dequeue_Protocol_Name pa.

Inductive Dequeue_Protocol :=
Dequeue_Protocol_Unspecified | OneItem | MultipleItems | AllItems.

Definition Map_Dequeue_Protocol_pv (pa : property_association) : Dequeue_Protocol :=
  match pa.(PV) with
    | (PV_Enum (Id "oneitem")) => OneItem
    | (PV_Enum (Id "multipleitems")) => MultipleItems
    | (PV_Enum (Id "allitems")) => AllItems
    | _ => OneItem
  end.

Definition Map_Dequeue_Protocol (pa : list property_association) :=
  match filter Is_Dequeue_Protocol pa with
  | nil => OneItem
  | v :: _ => Map_Dequeue_Protocol_pv v
  end.

(** %
  \begin{definition}[Dequeued\_Items (AADLv2.2 \S XXX]
 TBD
  \end{definition}
% *)

Definition Dequeued_Items_Name := PSQN "thread_properties" "dequeued_items".

Definition Is_Dequeued_Items (pa : property_association) :=
  Is_Property_Name Dequeued_Items_Name pa.

Definition Map_Dequeued_Items (pa : list property_association) : Z :=
  Map_PV_Int_List pa 0%Z Is_Dequeued_Items.
