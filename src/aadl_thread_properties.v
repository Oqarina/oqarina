(** %\section{\texttt{Thread\_Properties}} %*)

(* begin hide *)
(** Coq Library *)
Require Import List.
Import ListNotations. (* from List *)

(** Oqarina library *)
Require Import Oqarina.core.identifiers.
Require Import Oqarina.aadl.
Require Import Oqarina.aadl_aadl_project.
(* end hide *)

(** ** %\texttt{thread\_properties}% as Coq/AADL property_types

%\paragraph{} \begin{definition}[Period (\S XXX]
 TBD
  \end{definition}% *)

Definition Period_Name := Id "period".

Definition Period : property_type :=
  Property_Type (Id "period")  [ thread ] aadlinteger_t. (* XXX should use a unit !*)

Definition Is_Period (v : property_value) : bool :=
    Is_Property_Name Period_Name v.

(** %
  \begin{definition}[Priority (AADLv2.2 \S XXX]
 TBD
  \end{definition}
% *)

Definition Priority_Name := Id "priority".

Definition Priority : property_type :=
  Property_Type Priority_Name [ thread ] aadlinteger_t.

Definition Is_Priority (v : property_value) : bool :=
  Is_Property_Name Priority_Name v.

(**
%
  \begin{definition}[Dispatch\_Protocol (AADLv2.2 \S 5.4.2 (34)\index{Dispatch\_Protocol (AADL)}]
  The \texttt{Dispatch\_Protocol} property of a thread determines the characteristics of dispatch requests to the thread.
  \end{definition}
% *)

Definition Scheduling_Protocol_Name := Id "scheduling_protocol".

Definition Scheduling_Protocol : property_type :=
  Property_Type Scheduling_Protocol_Name [ thread ]
  (aadlenum_t [ (Id "periodic") ; (Id "sporadic") ; (Id "aperiodic") ;
                (Id "background") ; (Id "timed") ; (Id "hybrid") ] ).

Definition Is_Scheduling_Protocol (v : property_value) : bool :=
    Is_Property_Name Scheduling_Protocol_Name v.

(** ** %\texttt{thread\_properties}% as Coq native types


*)

(** %\paragraph{}
  \begin{definition}[Dispatch\_Protocol (Coq)]
  TBD
  \end{definition}
%

*)

Inductive Dispatch_Protocol :=
    Unspecified | Periodic | Sporadic | Aperiodic | Background | Timed | Hybrid.

Scheme Equality for Dispatch_Protocol.

Definition Map_Scheduling_Protocol_pv (pv : property_value) : Dispatch_Protocol :=
  match Get_Base_Value pv with
    | (aadlenum (Id "periodic")) => Periodic
    | (aadlenum (Id "sporadic")) => Sporadic
    | (aadlenum (Id "aperiodic")) => Aperiodic
    | (aadlenum (Id "background")) => Background
    | (aadlenum (Id "timed")) => Timed
    | (aadlenum (Id "Hybrid")) => Hybrid
    | _ => Unspecified
  end.

Definition Map_Scheduling_Protocol (pv : list property_value) : Dispatch_Protocol :=
  match filter Is_Scheduling_Protocol pv with
  | nil => Unspecified
  | v :: _ => Map_Scheduling_Protocol_pv v
  end.

(**

%
  \begin{definition}[Period (Coq)]
  TBD
  \end{definition}
%

*)

Definition Map_Period_pv (pv : property_value) : nat :=
  match Get_Base_Value pv with
    | aadlinteger int => int
    | _ => 0
  end.



Definition Map_Period (pv : list property_value) : nat :=
    match filter Is_Period pv with
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

Definition Map_Priority_pv (pv : property_value) : nat :=
  match Get_Base_Value pv with
    | aadlinteger int => int
    | _ => 0
  end.

Definition Map_Priority (pv : list property_value) : AADL_Time :=
    match filter Is_Priority pv with
    | nil => 0
    | v :: _ => Map_Priority_pv v
    end.
