(**
%\section{AADL System Category}\label{sec::aadl_system}%

%\N% The %\texttt{system}% component category denotes an assembly of interacting application software, execution platform, and sub-systems as sub-components. Systems may be hierarchically nested%\footnote{Note: the following is inspired from AADLv2.2 \S 13.3. We heavily simplified it to the bare minimal level of information. We also corrected some of this description to better reflect the modular nature of AADL instance hierarchy and remove redundant information that belongs to the description of other component categories.}%.

** System behavioral semantics

*** Informal definition

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

(* begin hide *)
Require Import Coq.Init.Datatypes.

Require Import pautomata.
Require Import actor.
Require Import time.
Import NaturalTime.
Require Import aadl_aadl_project.
Require Import utils.
Set Implicit Arguments.
(* end hide *)

(** *** Coq mechanization

    The following provides a Coq mechanization of the previous automata using p-Automata. *)

(** We use Coq unit as a system has no variable attached to is *)

Definition system_var : Type := unit.

(** The informal definition provides a direct path to the definition of    states, actions and transitions.
*)

Inductive system_states : Set :=
    system_offline | system_starting | system_operational | system_stoping.

Scheme Equality for system_states.

Inductive system_actions : Set :=
    start_system | abort_system | started_system | stop_system | stopped_system.

Definition system_transitions
    (a : system_actions) (t : Time)
    (l1 : system_states) (v1 : system_var)
    (l2 : system_states) (v2 : system_var) : Prop :=
    match a, t, l1, v1, l2, v2 with
    (* capture the transitions of the automata *)
    | start_system, _, system_offline, _, system_starting, _ => True
    | started_system, _, system_starting, _, system_operational, _ => True
    | stop_system, _, system_operational, _, system_stoping, _ => True
    | stopped_system, _, system_stoping, _, system_offline, _ => True
    | abort_system, _, system_starting, _, system_offline, _ => True
    | abort_system, _, system_operational, _, system_offline, _ => True
    (* any other configuration is invalid *)
    | _, _, _, _, _, _   => False
    end.

(** An AADL system is an hybrid category, there is no invariant
    attached to it. *)

Definition system_invariants
     (l : system_states) (t : Time) (v : system_var) : Prop :=
    match l, t, v with
    | _, _,_ => True
    end.

Module System_Automata <: Pautomata.
    Definition Var := system_var.
    Definition Loc := system_states.
    Definition Act := system_actions.
    Definition Inv := system_invariants.
    Definition Trans := system_transitions.
End System_Automata.

Record System_State_Variable : Type := mkSystemStateVariable {
    current_state : system_states;
    system_time : AADL_Time;
}.

Definition System_Initial_State : System_State_Variable := {|
    current_state := system_offline;
    system_time := 0;
|}.

Definition start_system_pre (ssv : System_State_Variable)  :=
    system_states_beq ssv.(current_state) system_offline.

Definition start_system_op (ssv : System_State_Variable) :=
    if start_system_pre ssv then
        {| current_state := system_starting; system_time := 0; |}
    else
        ssv.

Example s := start_system_op  System_Initial_State .
Compute s.

(***********

*)

Definition system_Fire (s : system_states) (a : system_actions) : unit := tt.

Definition system_Post_Fire
    (s : system_states)
    (a : system_actions) : system_states :=
    match s, a with
    (* capture the transitions of the automata *)
    | system_offline, start_system => system_starting
    | system_starting, started_system => system_operational
    | system_operational, stop_system => system_stoping
    | system_stoping, stopped_system=> system_offline
    | system_starting, abort_system => system_offline
    | system_operational, abort_system => system_offline
    (* any other configuration is invalid *)
    | _, _ => s
    end.

Definition system_Deadline
    (s : system_states)  (i : system_actions) : Time :=
    0.

Definition system_Time_Update
    (s : system_states)  (i : system_actions) (t : Time) : system_states :=
    s.

(*Definition System_Actor : Actor system_states system_actions unit := {|
    Initial_State := system_offline;
    Fire := system_Fire;
    Post_Fire := system_Post_Fire;
    Deadline := system_Deadline;
    Time_Update := system_Time_Update;
|}.
*)



