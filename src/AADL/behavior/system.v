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
Require Import Coq.Lists.ListSet.

Require Import Oqarina.core.all.
Import NaturalTime.
Require Import Oqarina.coq_utils.all.
Require Import Oqarina.formalisms.DEVS.parallel.all.
Require Import Oqarina.formalisms.all.

Require Import Oqarina.AADL.Kernel.all.
Import AADL_Notations.
Require Import Oqarina.AADL.property_sets.all.

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

%\N% The following provides a Coq mechanization of the previous automata using the DEVS formalism. *)

(** [X_system] represents the set of actions that a system may perform, as per the hybrid automata defined in AADLv2.2 \S 13.3. *)

Inductive X_system : Set :=
    start_system | abort_system | started_system | stop_system | stopped_system.

(** [Y_system] XXX *)

Definition Y_system : Type := X_system.

Definition Synchronization_Message_Type_system :=
    Synchronization_Message_Type X_system Y_system.

(** [system_S] represents the labels of the state of the system DEVS. *)

Inductive S_system : Set :=
    system_offline | system_starting |
    system_operational | system_stoping.

Definition Q_system : Type := Q S_system.

Definition Q_init_system := {| st := system_offline ; e := 0 |}.

Definition δint_system (s : S_system) : S_system := s.

Definition δext_system (s : Q_system) (x : list X_system) : S_system :=
    match s.(st), hd_error x with
        (* capture the transitions of the automata *)
        | system_offline, Some start_system => system_starting
        | system_starting,  Some started_system => system_operational
        | system_operational,  Some stop_system => system_stoping
        | system_stoping,  Some stopped_system =>  system_offline
        | system_starting,  Some abort_system => system_offline
        | system_operational,  Some abort_system => system_offline
        (* any other configuration is invalid *)
        | _, _ => s.(st)
        end.

Definition δcon_system  := Build_Default_δcon δint_system δext_system.

Definition Y_output_system : Type := Y_output Y_system.

Definition λ_system (s : S_system) : list Y_output_system :=
    match s with
    | system_starting => [ y start_system ]
    | system_operational => [ y started_system ]
    | _ => [ y abort_system ] (*[ no_output Y_system ]*)
    end.

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
    δcon := δcon_system;
|}.

Definition system_DEVS_Simulator_Type : Type :=
    DEVS_Simulator S_system X_system Y_system.

Definition System_Initial := Instantiate_DEVS_Simulator
    (Id "System") system_DEVS.

(* Translate DEVS to a LTS *)

Definition System_LTS := LTS_Of_DEVS (System_Initial).

Example System_LTS_1 :=
    step_lts (Init System_LTS) (i X_system Y_system 0).

Lemma System_LTS_1_OK :
    Print_DEVS_Simulator System_LTS_1 =  dbg 0 1 system_offline [].
Proof. trivial. Qed.

Example System_LTS_2 :=
    step_lts System_LTS_1 (xs Y_system Parent Parent 1 [ start_system ]).

Lemma System_LTS_2_OK :
    Print_DEVS_Simulator System_LTS_2 =  dbg 1 2 system_starting [].
Proof. trivial. Qed.

(* Map a complete system hierarchy to a DEVS *)

(* Map a system component and system subcomponents into a list of DEVS system *)

Definition Map_AADL_System_DEVS_System (c : component) :=
    map (fun s => Instantiate_DEVS_Simulator (s->id) system_DEVS)
     (Unfold c).

(* Let's map a system hierarchy into a coupled DEVS ! *)

Definition Z_Function_system : Z_Function_internal X_system Y_system :=
    fun (id id2 : identifier) (yi : Y_output Y_system)  =>
    match yi with
    | y x => [ x ]
    | no_output _ => [  ]
    end.

Definition Z_Function_in_system : Z_Function_in X_system :=
    fun (id : identifier) (x : list X_system) => x.

Definition Z_Function_out_system : Z_Function_out Y_system :=
    fun (id : identifier) (y : Y_output Y_system) => y.

(* For a list of components, we define the map of influenced
components as follows:
-  A influences B if B is a subcomponent of A
- others XXX TBD e.g. modes, EMV2 state machine, etc.
*)

Fixpoint Build_Influenced' (lc : list component) :=
    match lc with
    | [] => empty_list_identifiers_map
    | h :: t =>  (h->id) !-> Components_Identifiers (h->subcomps) ;
                 (Build_Influenced' t)
    end.

(* For a component hierarchy, we build the *)

Definition Build_Influenced (c : component) :=
    (Id "_self") !-> [c->id] ;
    Build_Influenced' (Unfold c). (* add I_self as the root !*)

Definition Map_AADL_Root_System_to_Coupled_DEVS (c : component) := {|
    devs_coupled_model_id := c->id ;
    D := Map_AADL_System_DEVS_System c ;
    Z_in := Z_Function_in_system;
    Z_out := Z_Function_out_system ;
    Z_f := Z_Function_system ;
    I := Build_Influenced c ;
|}.

Definition Map_AADL_Root_to_DEVS (c : component) :=
    Instantiate_DEVS_Simulator (Id "root")
    (Map_DEVS_Coupled_Model
    (Map_AADL_Root_System_to_Coupled_DEVS c)).
