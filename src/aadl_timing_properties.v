(** %\chapter{\texttt{AADL\_Project}} %*)

(** Loose mapping of aadl_project.aadl to define common types, units, etc. *)

Require Import Coq.Lists.List.
Import ListNotations.

Require Import Oqarina.core.identifiers.
Require Import Oqarina.core.time.
Require Import Oqarina.properties.properties.

Require Import Oqarina.aadl_aadl_project.

Definition Timing_Properties_PS :=
    PropertySet (Id "Timing_Properties") [

    (* Time: type aadlinteger 0 ps .. Max_Time units Time_Units; *)

    "Time" :prop PT_Number aadlinteger None (Some (PT_TypeRef (PSQN "AADL_Project_PS" "Time_Units"))) => None
       applies [];

    (* Period: inherit Time
       applies to (thread, thread group, process, system, device, virtual processor);
    *)

    "Period" :prop PT_TypeRef (PSQN "Timing_Properties" "Time")
        => None applies []
  ].

