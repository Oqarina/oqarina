(** %\chapter{\texttt{Timing\_Properties}} %*)

(** Loose mapping of aadl_project.aadl to define common types, units, etc. *)

(* begin hide *)
(** Coq Library *)
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.

(** Oqarina library *)
Require Import Oqarina.core.identifiers.
Require Import Oqarina.core.time.
Require Import Oqarina.properties.properties.
Require Import Oqarina.property_sets.aadl_aadl_project.
Require Import Oqarina.aadl_categories.
(* end hide *)

(** ** %\texttt{timing\_properties}% as Coq/AADL property_types *)

Definition Timing_Properties_PS :=
    PropertySet (Id "Timing_Properties") [

    (* Time: type aadlinteger 0 ps .. Max_Time units Time_Units; *)

    "Time" :prop PT_Number aadlinteger None (Some (PT_TypeRef (PSQN "AADL_Project_PS" "Time_Units")))
      => None applies [];

    (* Deadline: inherit Time => Period
		   applies to (thread, thread group, process, system, device, virtual processor);
    *)

    "Deadline" :prop PT_TypeRef (PSQN "Timing_Properties" "Time")
        => None applies [ thread ; threadGroup ; process ; system ; device ; virtualProcessor];

    (* Period: inherit Time
       applies to (thread, thread group, process, system, device, virtual processor);
    *)

    "Period" :prop PT_TypeRef (PSQN "Timing_Properties" "Time")
        => None applies [ thread ; threadGroup ; process ; system ; device ; virtualProcessor]
  ].

(*
%\paragraph{} \begin{definition}[Period (\S XXX]
 TBD
  \end{definition}% *)

Definition Period_Name := PSQN "timing_properties" "period".

Definition Is_Period (pa : property_association) :=
  Is_Property_Name Period_Name pa.

(*
%\paragraph{} \begin{definition}[Deadline (\S XXX]
 TBD
  \end{definition}% *)

  Definition Deadline_Name := PSQN "timing_properties" "deadline".

  Definition Is_Deadline (pa : property_association) :=
    Is_Property_Name Deadline_Name pa.

(**

%
  \begin{definition}[Period (Coq)]
  TBD
  \end{definition}
% *)

Definition Map_Period (pa : list property_association) : Z :=
  Map_PV_Int_List pa Is_Period.

(**

%
  \begin{definition}[Deadline (Coq)]
  TBD
  \end{definition}
% *)

Definition Map_Deadline (pa : list property_association) : Z :=
  Map_PV_Int_List pa Is_Deadline.
