(***
 * Oqarina
 * Copyright 2021 Carnegie Mellon University.
 *
 * NO WARRANTY. THIS CARNEGIE MELLON UNIVERSITY AND SOFTWARE ENGINEERING
 * INSTITUTE MATERIAL IS FURNISHED ON AN "AS-IS" BASIS. CARNEGIE MELLON
 * UNIVERSITY MAKES NO WARRANTIES OF ANY KIND, EITHER EXPRESSED OR
 * IMPLIED, AS TO ANY MATTER INCLUDING, BUT NOT LIMITED TO, WARRANTY OF
 * FITNESS FOR PURPOSE OR MERCHANTABILITY, EXCLUSIVITY, OR RESULTS
 * OBTAINED FROM USE OF THE MATERIAL. CARNEGIE MELLON UNIVERSITY DOES NOT
 * MAKE ANY WARRANTY OF ANY KIND WITH RESPECT TO FREEDOM FROM PATENT,
 * TRADEMARK, OR COPYRIGHT INFRINGEMENT.
 *
 * Released under a BSD (SEI)-style license, please see license.txt or
 * contact permission@sei.cmu.edu for full terms.
 *
 * [DISTRIBUTION STATEMENT A] This material has been approved for public
 * release and unlimited distribution.  Please see Copyright notice for
 * non-US Government use and distribution.
 *
 * This Software includes and/or makes use of the following Third-Party
 * Software subject to its own license:
 *
 * 1. Coq theorem prover (https://github.com/coq/coq/blob/master/LICENSE)
 * Copyright 2021 INRIA.
 *
 * 2. Coq JSON (https://github.com/liyishuai/coq-json/blob/comrade/LICENSE)
 * Copyright 2021 Yishuai Li.
 *
 * DM21-0762
***)
(* begin hide *)
Require Import Coq.Init.Datatypes.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations. (* from List *)

Require Import Oqarina.core.all.
Import NaturalTime.
Require Import Oqarina.AADL.property_sets.all.
Require Import Oqarina.formalisms.devs_classic.
Require Import Oqarina.formalisms.devs_coupled.
Require Import Oqarina.coq_utils.all.
Require Import Oqarina.formalisms.lts.
Set Implicit Arguments.
(* end hide *)

(**
%\chapter{AADL System Category}\label{sec::aadl_system}%

%\N% The %\texttt{system}% component category denotes an assembly of interacting application software, execution platform, and sub-systems as sub-components. Systems may be hierarchically nested%\footnote{Note: the following is inspired from AADLv2.2 \S 13.3. We heavily simplified it to the bare minimal level of information. We also corrected some of this description to better reflect the modular nature of AADL instance hierarchy and remove redundant information that belongs to the description of other component categories.}%.

* System behavioral semantics

** Informal definition

%\N% In the following, we start by presenting the expected behavior of any system component catefory (figure%~\ref{fig:aadl_system_beh}%).

%
\tikzset{elliptic state/.style={draw,ellipse}, -Triangle, node distance=2cm}

\begin{figure}[!h]
\centering
\begin{tikzpicture}
\node[elliptic state, very thick] (s0) {system offline};
\node[elliptic state, below=1cm of s0] (s1) {system starting};
\node[elliptic state, right=1cm of s1] (s2) {system stoping};
\node[elliptic state, below of=s1] (s3) {system operational};
\draw (s0) edge[bend left, right] node{\textbf{start(system)}} (s1);
\draw (s1) edge[bend left, left] node{\textbf{abort(system)}} (s0);
\draw (s1) edge[, right] node{\textbf{started(system)}} (s3);
\draw (s3) -| node[below]{\textbf{stop(system)}} (s2);
\draw (s2) |- node[above]{\textbf{stopped(system)}} (s0);
\draw (s3) -| ++(-4,2) node[left]{\textbf{abort(system)}} |- (s0);

\end{tikzpicture}
\caption{AADL \texttt{system} automata behavior} \label{fig:aadl_system_beh}
\end{figure}
%

%\N% This automata semantics can also be described as follows:

- %\textit{"system offline"}% is the system initial state.

- On system startup the system instance transitions from %\textit{"system offline"}% to %\textit{"system starting"}% through the action %\textbf{start(system)}%

- When in state %\textit{"system starting"}%, the system perform the initialization of the system subcomponents. In case of an error during this step, the system goes back to %\textit{"system offline"}% through the the %\textbf{abort(system)}% action. When all subsystems have been successfully initialized, the system moves to the state %\textit{"system operational"}% through the %\textbf{started(system)}% action.

- When in state %\textit{"system operational"}%, the system is under operation, the system and its subcomponents execute their nominal behavior. In case of an error during the execution, the system goes back to %\textit{"system offline"}% through the %\textbf{abort(system)}% action.

- Upon completion of its execution, a system may perform a graceful shutdowm (%\textbf{stop(system)}% action) and moves to the state %\textit{"system stoping"}%. When all subsystems are successfully stoped, the system moves to the state %\textit{"system offline"}% through the %\textbf{stopped(system)}% action.

*)

(** *** Coq mechanization

%\N% The following provides a Coq mechanization of the previous automata using the actor formalism. *)


(** [X_system] represents the set of actions that a system may perform, as per the hybrid automata defined in AADLv2.2 \S 13.3. *)

Inductive X_system : Set :=
    start_system | abort_system | started_system | stop_system | stopped_system.

(** [Y_system] is the internal state of a system, for the moment empty *)

Definition Y_system : Type := unit.

Definition Synchronization_Message_Type_system :=
    Synchronization_Message_Type X_system Y_system.

(** [system_S] represents the labels of the state of the system DEVS. *)

Inductive S_system : Set :=
    system_offline | system_starting |
    system_operational | system_stoping.
Scheme Equality for S_system.

Definition Q_system : Type := Q S_system.

Definition Q_init_system := {| st := system_offline ; e := 0 |}.

Definition δint_system (s : S_system) : S_system := s.

Definition δext_system (s : Q_system) (x : X_system) : S_system :=
    match s.(st), x with
        (* capture the transitions of the automata *)
        | system_offline, start_system => system_starting
        | system_starting, started_system => system_operational
        | system_operational, stop_system => system_stoping
        | system_stoping, stopped_system =>  system_offline
        | system_starting, abort_system => system_offline
        | system_operational, abort_system => system_offline
        (* any other configuration is invalid *)
        | _, _ => s.(st)
        end.

Definition Y_output_system : Type := Y_output Y_system.

Definition λ_system (s : S_system) : Y_output_system :=
    no_output Y_system.

Definition ta_system (s : S_system) : Time := 1.

Definition system_DEVS_type : Type :=
    DEVS_Atomic_Model S_system X_system Y_system.

Definition system_DEVS : system_DEVS_type := {|
    devs_atomic_id := Id "AADL_system" ;
    Q_init := Q_init_system;

    ta := ta_system;
    δint := δint_system;
    λ  := λ_system;
    δext := δext_system;
|}.

Definition system_DEVS_Simulator_Type : Type :=
    DEVS_Simulator S_system X_system Y_system.

Definition System_Initial := Instantiate_DEVS_Simulator
    (Id "System") system_DEVS.

Definition System_Coordinator :=
    Iniitialize_DEVS_Root_Coordinator System_Initial.

Definition SC_Step1 := DEVS_Simulation_Step System_Coordinator None.
Compute Print_DEVS_State SC_Step1.

Lemma SC_Step1_OK :
    Print_DEVS_State SC_Step1 =  dbg 0 1 system_offline [].
Proof. trivial. Qed.

(* We inject the start_system event, the system moves to the system_starting state *)

Definition m_start_system : Synchronization_Message_Type_system  :=
    xs Y_system Parent Parent 1 start_system.

Definition SC_Step2 := DEVS_Simulation_Step SC_Step1 (Some m_start_system).
Compute Print_DEVS_State SC_Step2.

Lemma SC_Step2_OK :
    Print_DEVS_State SC_Step2 =  dbg 1 2 system_starting [].
Proof. trivial. Qed.

(* XXX from this, who is sending system started?
most certainly it is an internal event after all subcomponents have finished
*)

Definition SC_Step3 := DEVS_Simulation_Step SC_Step2 None.
Compute Print_DEVS_State SC_Step3.
