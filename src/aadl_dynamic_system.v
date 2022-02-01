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
Require Import Oqarina.coq_utils.all.
Require Import Oqarina.formalisms.lts.
Set Implicit Arguments.
(* end hide *)
(** %\chapter{AADL Systems} %*)
Section Actors.

    (* We revise the definition of actors as follows: intuitively, an actor is an automata-like ADT. It is defined by a state and a collection of operations that operate on this state. We define the following:
    - [L] a set of labels that represent the different phases of the execution of the actor;
    - [A] denote the actions that the actor may perform;
    - [I] represents the internal state of an actor, i.e. any memory the actor needs.

    An actor relies on an definition of time, inherited from [Time] formalization. *)

    Variable L : Type. (* State labels *)
    Variable A : Type. (* Actions *)
    Variable I : Type. (* private state *)

    (** An [Actor_Action] denotes an action that can be executed. We distinguish between discrete ([Dis]) and timed ([Temp]) actions. *)

    Inductive Actor_Action :=
        | Dis : A -> Actor_Action
        | Temp : A -> Time -> Actor_Action
        | Step : Actor_Action. (* trigger internal behavior *)

    Definition Connection := list nat.

    (** First, we define [Actor_State] as a placeholder to store the current state of an actor. An [Actor_State] is a tuple that holds [Current_State] which is is the curent state label (i.e. position in the underlying automata), along with a clock variable, the state of inputs and outputs variable and an internal state. [Actor_State] represents the mutable part of an actor definition. *)

    Inductive Actor_State : Type := {
        (* State information *)
        Current_State : L;
        Clock_Variable : Time;
        Inputs : list Actor_Action;
        Outputs : list Actor_Action;
        Internal : I;
    }.

    (** Then, we define [Actor] as the immutable part of an actor definition. An [Actor] gathers the definition of initial state of an actor, and the definitions of the various operations on a state. *)
    Inductive Actor : Type := {

        (* Mutable state variable *)
        Act_State : Actor_State;

        (* Mapping functions *)
        Prefire : Actor_State -> list Actor_State -> Actor_State;
        Fire : Actor_State -> Actor_State;
        Post_Fire : Actor_State -> Actor_State;
        Deadline : L  -> Time;
        Time_Update : L -> L;
    }.

    (** ** Operations on [Actor_State] *)

    (** - [Set_Initial_Actor_State] configures the initial state of an actor. *)

    Definition Set_Initial_Actor_State (Initial_State : L) (Internal : I) : Actor_State := {|
        Current_State := Initial_State ;
        Clock_Variable := 0;
        Inputs := nil;
        Outputs := nil;
        Internal := Internal;
    |}.

    (** - [Set_State] sets the [Current_State] of an Actor *)

    Definition Set_State (ast : Actor_State) (l : L) : Actor_State := {|
        Current_State := l;
        Clock_Variable := ast.(Clock_Variable);
        Inputs := ast.(Inputs);
        Outputs := ast.(Outputs);
        Internal := ast.(Internal);
    |}.

    (** - [Peek_Input] returns one input, without dequeuing it. *)

    Definition Peek_Input (ast : Actor_State) : option Actor_Action :=
        hd_error ast.(Inputs).

    (** - [Dequeue_Input] removes one input from an Actor. *)

    Definition Dequeue_Input (ast : Actor_State) : Actor_State := {|
        Current_State := ast.(Current_State);
        Clock_Variable := ast.(Clock_Variable);
        Inputs := tl ast.(Inputs);
        Outputs := ast.(Outputs);
        Internal := ast.(Internal);
    |}.

    (** - [Set_Input] adds a list of inputs to an Actor. *)
    (* XXX should we keep a list here ... *)
    Definition Set_Input (ast : Actor_State) (i : list Actor_Action) : Actor_State := {|
        Current_State := ast.(Current_State);
        Clock_Variable := ast.(Clock_Variable);
        Inputs := Coq.Lists.List.concat [ast.(Inputs) ; i] ;
        Outputs := ast.(Outputs);
        Internal := ast.(Internal);
    |}.

    (** - [Set_Output] adds a list of outputs to an Actor. *)

    Definition Set_Output (ast : Actor_State) (i : list Actor_Action) : Actor_State := {|
        Current_State := ast.(Current_State);
        Clock_Variable := ast.(Clock_Variable);
        Inputs := ast.(Inputs);
        Outputs := Coq.Lists.List.concat [ast.(Outputs) ; i] ;
        Internal := ast.(Internal);
    |}.

    (** - [Peek_Output] returns one input, without dequeuing it. *)

    Definition Peek_Output (ast : Actor_State) : option Actor_Action :=
        hd_error ast.(Outputs).

    (** - [Dequeue_Output] removes one input from an Actor. *)

    Definition Dequeue_Output (ast : Actor_State) : Actor_State := {|
        Current_State := ast.(Current_State);
        Clock_Variable := ast.(Clock_Variable);
        Inputs := ast.(Inputs);
        Outputs := tl ast.(Outputs);
        Internal := ast.(Internal);
    |}.

    (** - [Set_Internal] sets the internal state of an Actor *)

    Definition Set_Internal (ast : Actor_State) (i : I) : Actor_State := {|
        Current_State := ast.(Current_State);
        Clock_Variable := ast.(Clock_Variable);
        Inputs := ast.(Inputs);
        Outputs := tl ast.(Outputs);
        Internal := i;
    |}.

    (** ** Operations on [Actor] *)

    Definition Set_Act_State (a : Actor) (ast : Actor_State) : Actor := {|
        Act_State := ast;
        Prefire := a.(Prefire);
        Fire := a.(Fire);
        Post_Fire := a.(Post_Fire);
        Deadline := a.(Deadline);
        Time_Update := a.(Time_Update);
    |}.

    Definition Actor_Set_Input (a : Actor) (i : list Actor_Action) : Actor :=
        Set_Act_State a (Set_Input a.(Act_State) i).

    Definition Actor_Dequeue_Output (a : Actor) : Actor :=
        Set_Act_State a (Dequeue_Output a.(Act_State)).

    (** An actor my perform untimed or timed action. we first define each concept separately, then we build a common action type: [Actor_Action]. Each action runs the actors functions defined in [a] on [ast] and returns an updated actor state. *)

    Definition Untimed_Action (actor : Actor) (ast : Actor_State) : Actor_State :=
        (Post_Fire actor) ((Fire actor) ast).

    Definition Timed_Action (actor : Actor) (ast : Actor_State) : Actor_State :=
        let action := Peek_Input ast in
        match action with
        | Some (Temp _ dt) => if dt <=? (Deadline actor) (Current_State ast) then {|
                            Clock_Variable := (Clock_Variable ast) + dt;
                            Current_State := (Time_Update actor) (Current_State ast);
                            Inputs := ast.(Inputs);
                            Outputs := ast.(Outputs);
                            Internal := ast.(Internal);
                        |}
                        else
                            ast
        | _ => ast
        end.

    (** - [Actor_Step] executes one step, executing the action [act]. This function returns an updated [Actor_State]. XXX merge discrete actions and timed ones *)

    Definition Actor_Step (a : Actor) (l : list Actor_State) : Actor :=
        let a' := Set_Act_State a (Prefire a a.(Act_State) l) in
        let act := Peek_Input a'.(Act_State) in
            match act with
                | Some (Dis _) => Set_Act_State a' (Untimed_Action a' a'.(Act_State))
                | Some (Temp _ _) => Set_Act_State a' (Timed_Action a' a'.(Act_State))
                | _ => a'
            end.

    (** - [Actor_Broadcast] broadcast one outpot from a to all elements of [l]. Note this function does not dequeue element from a.  *)

    Definition Actor_Broadcast (a : Actor) (l : list Actor) :=
        let act := Peek_Output a.(Act_State) in
        match act with
            | Some act' => map (fun x => Actor_Set_Input a [act']) l
            | None => l
        end.

    (** - [Actor_Transfer_Output] copy one output from [src] to [dest]. Note this function does not dequeue element from [src].   *)

    Definition Actor_Transfer_Output (src : Actor) (dest : Actor) :=
        let act := Peek_Output src.(Act_State) in
        match act with
            | Some act' => Actor_Set_Input dest [act']
            | None => dest
        end.

    (** - [LTS_Of] builds a labelled transition system (LTS) out of an actor. *)
(*
    Definition LTS_Of (a : Actor) (act : Actor_Action) (Initial_State : L) (Internal : I) : LTS_struct := {|
        States := Actor;
        Init := Set_Act_State a (Set_Initial_Actor_State Initial_State Internal);
        Actions := Actor_Action;
        Step := fun actor act => Actor_Step (Actor_Set_Input actor [act]) [] (* XXX *);
    |}.
*)
End Actors.

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

(** [system_L] represents the labels of the state of the system hybrid automata. *)

Inductive system_L : Set :=
    system_offline | system_starting | system_operational | system_stoping.
Scheme Equality for system_L.

(** [system_A] represents the set of actions that a system may perform, as per the hybrid automata defined in AADLv2.2 \S 13.3. *)

Inductive system_A : Set :=
    start_system | abort_system | started_system | stop_system | stopped_system.

(** [system_I] is the internal state of a system, for the moment empty *)

Definition system_I : Type := unit.

Definition system_actions : Type := Actor_Action system_A.

Definition System_Actor_Type : Type := Actor system_L system_A system_I .

(** From these definition, we can build the various elements of a AADL system actor. *)

Definition system_state : Type := Actor_State system_L system_A system_I.

(** [System_Initial_State] is the default initial state of all system instances. *)

Definition System_Initial_State : system_state :=
    Set_Initial_Actor_State  system_A system_offline tt.

Definition system_Prefire (s : system_state) (deps: list system_state) : system_state  := (* internal event queued *)
    match s.(Current_State) with
        | system_starting => (* XXX *)
            match deps with
            | [ ] => (Set_Input s [Dis started_system])
            | _ => if andbl (map (fun x => system_L_beq system_operational (Current_State x)) deps) then (Set_Input s [Dis started_system]) else s
            end
        | _ => s
    end.

Definition system_executions (s : system_state) (a : system_actions) : system_state :=
    match a with
    | Dis a' =>
        match s.(Current_State), a' with
            (* capture the transitions of the automata *)
            | system_offline, start_system => (Set_Output s [a])

            (* any other configuration is invalid *)
            | _, _ => s
            end
    | _ => s
    end.

Definition system_Fire (s : system_state) : system_state :=
    let a : option system_actions := Peek_Input s in
        match a with
        | Some a' => system_executions s a' (* XXX *)
        | None => s
        end.

Definition system_transitions (s : system_state) (a : system_actions) : system_state :=
    match a with
    | Dis a' =>
        match s.(Current_State), a' with
            (* capture the transitions of the automata *)
            | system_offline, start_system => (Set_State s system_starting)
            | system_starting, started_system => (Set_State s system_operational)
            | system_operational, stop_system => (Set_State s system_stoping)
            | system_stoping, stopped_system => (Set_State s system_offline)
            | system_starting, abort_system => (Set_State s system_offline)
            | system_operational, abort_system => (Set_State s system_offline)
            (* any other configuration is invalid *)
            | _, _ => s
            end
    | _ => s
    end.

Definition system_Postfire (s : system_state) : system_state :=
    let a : option system_actions := Peek_Input s in
    let s' := Dequeue_Input s in
        match a with
        | Some a' => system_transitions s' a' (* XXX *)
        | None => s
        end.

Definition system_Deadline (s : system_L)  : Time :=
    0%nat.

Definition system_Time_Update
    (s : system_L) : system_L :=
    s.

Definition System_Actor : System_Actor_Type := {|
    Act_State := System_Initial_State;

    Prefire := system_Prefire;
    Fire := system_Fire;
    Post_Fire := system_Postfire;
    Deadline := system_Deadline;
    Time_Update := system_Time_Update;
|}.

(* Check that the initial value is correct *)

Definition system_step0 := Actor_Step System_Actor [].
Lemma system_step0_OK : Act_State system_step0 =
{| Current_State := system_offline; Clock_Variable := 0%nat; Inputs := [];
   Outputs := []; Internal := tt; |}.
Proof.
    trivial.
Qed.

(* We inject the start_system event, the system moves to the system_starting state *)

Definition system_step1 := Actor_Set_Input System_Actor [Dis start_system].
Definition system_step1' := Actor_Step system_step1 [].
Lemma system_step1_OK : Act_State (system_step1') =
{| Current_State := system_starting; Clock_Variable := 0%nat; Inputs := [];
   Outputs := [(Dis start_system)]; Internal := tt; |}.
Proof.
    trivial.
Qed.

(* Since there is no subcomponents, the next state is system_operational *)

Definition system_step2 := Actor_Step system_step1' [].
Lemma system_step2_OK : Act_State (system_step2) =
{| Current_State := system_operational; Clock_Variable := 0%nat; Inputs := [];
   Outputs := [(Dis start_system)]; Internal := tt; |}.
Proof.
    trivial.
Qed.

(** We now define a tree of [System_Actor] as an actor *)

Section Tree.

    (** We define a basic tree structure with a map-like operator *)

    Inductive tree (X : Type): Type :=
    | empty : tree X
    | branch : identifier -> X -> list (tree X) -> tree X.

    (** [map_tree] applies [f] recursively on [t] to produce a new tree. *)

    Fixpoint map_tree (T : Type) (X : Type) (f : T -> X) (t : tree T) : tree X :=
        match t with
        | empty _ => empty X
        | branch i a b => branch i (f a) (map (fun x => map_tree f x) b)
        end.

    Definition map_root (T : Type) (f : T -> T) (t : tree T) :=
        match t with
            | empty _ => empty T
            | branch i a b => branch i (f a) b
        end.

    (** [apply_tree_id] applies [f] on node [I] *)

    Fixpoint apply_tree_id (T : Type) (I : identifier) (f : T -> T) (t : tree T) :=
        match t with
            | empty _ => empty T
            | branch i a b => if (identifier_beq i I) then branch i (f a) (map (fun x => apply_tree_id I f x) b) else branch i a (map (fun x => apply_tree_id I f x) b)
        end.

    (** [apply_tree] applies [f] on all nodes of [t] *)

    Fixpoint apply_tree (T : Type) (f : T -> list (tree T) -> T) (t : tree T) :=
        match t with
            | empty _ => empty T
            | branch i a b => branch i (f a b) (map (fun x => apply_tree f x) b)
        end.

    Fixpoint apply_tree_b (T : Type) (f : T -> list (tree T) -> bool) (t : tree T) :=
        match t with
            | empty _ => true
            | branch i a b => andb (f a b) (andbl (map (fun x => apply_tree_b f x) b))
        end.

    Fixpoint apply_tree2 (T : Type) (f : T -> T -> T) (arg : option T) (t : tree T) :=
        match t with
            | empty _ => empty T
            | branch i a b =>
                match arg with
                | None => branch i a (map (fun x => apply_tree2 f (Some a) x) b)
                | Some a' => branch i (f a' a) (map (fun x => apply_tree2 f (Some a) x) b)
                end
        end.

End Tree.

Definition System_Actor_Tree : Type := tree System_Actor_Type.
Definition Empty_System_Actor_Tree : System_Actor_Tree := empty System_Actor_Type.

(** [Show_States] returns the actor states of the nodes of a System_Actor_Tree *)

Definition Show_States (t : System_Actor_Tree) :=
    map_tree  (fun x => Current_State (Act_State x)) t.

Definition Show_States' (t : System_Actor_Tree) :=
    map_tree  (fun x => Act_State x) t.

Definition System_Actor_Tree_state : Type := Actor_State system_L system_A System_Actor_Tree.

Definition System_Actor_Tree_initial_state : System_Actor_Tree_state :=
    Set_Initial_Actor_State system_A system_offline Empty_System_Actor_Tree.

Definition System_Actor_Tree_Prefire
    (ast : System_Actor_Tree_state) (deps : list System_Actor_Tree_state):= ast.

(** Executes all actors from [ast] *)

Definition System_Actor_Tree_Micro_Step_exec (ast : System_Actor_Tree_state) : System_Actor_Tree_state :=
    Set_Internal ast (map_tree (fun x => Actor_Step x []) (Internal ast)).

(** Propagate outputs down the hierarchy *)

Definition System_Actor_Tree_Micro_Step_comm (ast : System_Actor_Tree_state) :=
    let ast1 := Set_Internal ast (apply_tree2 (fun x y => Actor_Transfer_Output x y)
        None (Internal ast)) in
        Set_Internal ast (map_tree (fun x => Actor_Dequeue_Output x) (Internal ast1)).

Definition System_Actor_Tree_Fire
    (ast : System_Actor_Tree_state) : System_Actor_Tree_state :=

    (* We pass the first event from the Actor_Tree down to the root Actor for further processing. *)

    let event := Peek_Input ast in (* should dequeue when all sub actors converged XXX *)
    match event with
    | Some evt => let tree := map_root (fun x => Actor_Set_Input x [evt]) (Internal ast) in
                  let ast' := Set_Internal ast tree in
                  let ast1 := System_Actor_Tree_Micro_Step_exec ast' in
                  System_Actor_Tree_Micro_Step_comm ast1

    | None => ast
    end.

Definition System_Actor_Tree_Post_Fire
    (ast : System_Actor_Tree_state) : System_Actor_Tree_state := ast.

Definition System_Actor_Tree_Deadline
    (s : system_L)  : Time := 0%nat.

Definition System_Actor_Tree_Time_Update (s : system_L) := s.

Definition System_Actor_Tree_Type : Type :=
    Actor system_L system_A System_Actor_Tree.

Definition System_Actor_Tree_Actor : System_Actor_Tree_Type := {|
    Act_State := System_Actor_Tree_initial_state ;

    Prefire := System_Actor_Tree_Prefire;
    Fire := System_Actor_Tree_Fire;
    Post_Fire := System_Actor_Tree_Post_Fire;
    Deadline := System_Actor_Tree_Deadline;
    Time_Update := System_Actor_Tree_Time_Update;
|}.

Definition Instantiate_System_Actor_Tree_Actor (t : System_Actor_Tree ) :=
    Set_Act_State System_Actor_Tree_Actor
    (Set_Internal System_Actor_Tree_Actor.(Act_State) t).

(** A toy [System_Actor_Tree]

System_Actor "root"
   |- System Actor "s1"
        |- System_Actor "s2"
   |- System_Actor "s3"

*)

Definition root_system :=
    branch (Id "root") System_Actor
    [ branch (Id "s1") System_Actor
        [ branch (Id "s2") System_Actor [empty System_Actor_Type]] ;
      branch  (Id "s3")  System_Actor [empty System_Actor_Type]].

(** First. we instantiate a System_Actor_Tree  actor with [root_system], then we iterate *)

Definition root_system_Actor := Instantiate_System_Actor_Tree_Actor root_system.

(** [Actor_Step] performs no action, there is no input in [root_system_Actor] *)

Definition root_system_step0 := Actor_Step root_system_Actor []. (* XXX *)
Lemma step0_OK : root_system_step0 = root_system_Actor.
Proof.
    trivial.
Qed.

(** We inject one even in the root system, the first step will *)


Fixpoint Iterate (T : Type) (n : nat) (f : T -> T) (x : T) :=
    match n with
    | 0 => x
    | S n' => Iterate n' f (f x)
    end.

Definition root_system_step1 := Actor_Set_Input root_system_step0 [Dis start_system].
Compute Show_States (Internal (Act_State root_system_step1)).

Definition root_system_stepn := Iterate 1 (fun x => Actor_Step x []) root_system_step1.
Compute Show_States (Internal (Act_State root_system_stepn)).


Definition root_system_step2 := Actor_Step root_system_step1 [].
Compute Show_States (Internal (Act_State root_system_step2)).

Definition root_system_step3 := Actor_Step root_system_step2 [].
Compute Show_States (Internal (Act_State root_system_step3)).

Definition root_system_step4 := Actor_Step root_system_step3 [].
Compute Show_States (Internal (Act_State root_system_step4)).

Definition root_system_step5 := Actor_Step root_system_step4 [].
Compute Show_States (Internal (Act_State root_system_step5)).

Definition root_system_step6 := Actor_Step root_system_step5 [].
Compute Show_States (Internal (Act_State root_system_step6)).


Inductive AADL_Actor :=
| Sys_Actor : System_Actor_Type -> AADL_Actor.
