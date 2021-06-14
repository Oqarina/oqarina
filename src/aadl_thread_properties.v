(** %\section{\texttt{Thread\_Properties}} %*)

(* begin hide *)
(** Coq Library *)
Require Import List.
Import ListNotations. (* from List *)

(** AADL library *)
Require Import Oqarina.core.identifiers.
Require Import Oqarina.properties.properties.
Require Import Oqarina.properties.typecheck.
Require Import Coq.ZArith.ZArith.
Require Import Oqarina.aadl_aadl_project.
(* end hide *)

(** ** %\texttt{thread\_properties}% as Coq/AADL property_types *)

Definition Thread_Properties_PS :=
    PropertySet (Id "Thread_Properties") [

    (* Dispatch_Protocol: Supported_Dispatch_Protocols
        applies to (thread, device, virtual processor); *)

    "Dispatch_Protocol" :prop PT_TypeRef (PSQN "AADL_Project" "Supported_Dispatch_Protocols")
        => None applies [];

    (* Priority: inherit aadlinteger
        applies to (thread, thread group, process, system, device, data); *)

    "Priority" :prop aadlinteger => None applies []
  ].

(*
%\paragraph{} \begin{definition}[Period (\S XXX]
 TBD
  \end{definition}% *)

Definition Period_Name := PSQN "timing_properties" "period".

Definition Is_Period (pa : property_association) :=
  Is_Property_Name Period_Name pa.

(** %
  \begin{definition}[Priority (AADLv2.2 \S XXX]
 TBD
  \end{definition}
% *)

Definition Priority_Name := PSQN "thread_properties" "priority".

Definition Is_Priority (pa : property_association) :=
  Is_Property_Name Priority_Name pa.

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
    Unspecified | Periodic | Sporadic | Aperiodic | Background | Timed | Hybrid.

Scheme Equality for Dispatch_Protocol.

Definition Map_Scheduling_Protocol_pv (pa : property_association) : Dispatch_Protocol :=
  match pa.(PV) with
    | (PV_Enum (Id "periodic")) => Periodic
    | (PV_Enum (Id "sporadic")) => Sporadic
    | (PV_Enum (Id "aperiodic")) => Aperiodic
    | (PV_Enum (Id "background")) => Background
    | (PV_Enum (Id "timed")) => Timed
    | (PV_Enum (Id "Hybrid")) => Hybrid
    | _ => Unspecified
  end.

Definition Map_Scheduling_Protocol (pa : list property_association) : Dispatch_Protocol :=
  match filter Is_Scheduling_Protocol pa with
  | nil => Unspecified
  | v :: _ => Map_Scheduling_Protocol_pv v
  end.

(**

%
  \begin{definition}[Period (Coq)]
  TBD
  \end{definition}
% *)

Definition Map_Period_pv (pa : property_association) : Z :=
  match pa.(PV) with
    | PV_Int i => i
    | _ => 0
  end.

Definition Map_Period (pa : list property_association) : Z :=
    match filter Is_Period pa with
    | nil => 0
    | v :: _ => Map_Period_pv v
    end.

(**

%
  \begin{definition}[Priority (Coq)]
  TBD
  \end{definition}
%

*)

Definition Map_Priority_pv (pa : property_association) : Z :=
  match pa.(PV) with
    | PV_Int i => i
    | _ => 0
  end.

Definition Map_Priority (pa : list property_association) : Z :=
    match filter Is_Priority pa with
    | nil => 0
    | v :: _ => Map_Priority_pv v
    end.
