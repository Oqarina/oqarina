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
(** %\chapter{Actor Component Model}\label{chap::actor}%

The following captures the Actor component model as described in the Ptolemy toolset and presented in %\cite{tripakisModularFormalSemantics2013,leeHeterogeneousActorModeling2011}%. This model has been extended to decouple actions of a component from input/output communication.  *)

(* begin hide *)
(** Coq Library *)
Require Import Coq.Lists.List.
Import ListNotations. (* from List *)
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Init.Datatypes.
Require Import Coq.Program.Basics.

(** Oqarina library *)
Require Import Oqarina.core.time.
Import NaturalTime.
Require Import Oqarina.formalisms.lts.
Require Import Oqarina.coq_utils.utils.

Set Implicit Arguments.

Section Actor_Definition.
(* end hide *)

    (** * Definition of an actor

    %
    In Ptolemy, an Actor~\cite{tripakisModularFormalSemantics2013,leeHeterogeneousActorModeling2011} is defined as a tuple $A = (I,O,S,s_0,F,P,D,T)$ where $I$ is a set of input variables, $O$ is a set of output variables, $S$ is a set of state variables, $s_0 \in S$ is the initial state, and $Fire$, $Post\_Fire$, $Deadline$, and $Time\_Update$ are total functions that controls the execution of an actor. This model fits the regular model of computations-driven CPS. However, inputs and outputs are base numeric types only. This does not sufficiently capture the life-cycle of an actor. Indeed, one need to initialize a component, change its mode of operation in addition to performing computation.%

    This model has been recently revisited to define the Reactor model  %\cite{lohstrohLinguaFrancaDeterministic2021}%. Reactors provide a clearer separation between input/outputs and actions. Yet, this model has a couple of abstraction limits. The most important one at this stage is the absence of an explicit Director that synchronizes components for different MoCs. This limitation stems from the targeted domain of reactive systems.

    Hence, we revise the definition of actors as follows: intuitively, an actor is an automata-like ADT. It is defined by a state and a collection of operations that operate on this state. We define the following:
    - [L] a set of labels that represent the different phases of the execution of the actor;
    - [A] denote the actions that the actor may perform;
    - [V] are the values the actor may receive or send;
    - [I] represents the internal state of an actor, i.e. any memory the actor needs.

    An actor relies on an definition of time, inherited from [Time] formalization.

    *)

    Variable L : Type. (* State labels *)
    Variable A : Type. (* Actions *)
    Variable V : Type. (* Values *)
    Variable I : Type. (* private state *)

    (** First, we define [Actor_State] as a placeholder to store the current state of an acort. An [Actor_State] is a tuple that holds [Current_State] which is is the curent state label (i.e. position in the underlying automata). [Actor_State] represents the mutable part of an actor definition. *)

    Record Actor_State : Type := {
        Current_State : L;
        Clock_Variable : Time;
        Inputs : list V;
        Outputs : list V;
        Internal : I;
    }.

    (** Then, we define [Actor] as the immutable part of an actor definition. An [Actor] gathers the definition of initial state of an actor, and the definitions of the various operations on a state. *)

    Record Actor: Type := {
        (* Immutable state variable *)
        Initial_State : L;

        (* Mapping functions *)
        Fire : Actor_State -> A -> Actor_State;
        Post_Fire : Actor_State -> A -> Actor_State;
        Deadline : L -> A -> Time;
        Time_Update : L -> A -> Time -> L;
    }.
    (** * Operations on an actor.

    We provide three accessors for manipulating inputs, outpurs and setting the initial state of an actor. *)

    (** - [Fetch_Output] removes one output from an Actor. *)

    Definition Fetch_Output (ast : Actor_State) := {|
        Current_State := ast.(Current_State);
        Clock_Variable := ast.(Clock_Variable);
        Inputs := ast.(Inputs);
        Outputs := tl ast.(Outputs);
        Internal := ast.(Internal);
    |}.

    (** - [Set_Input] adds one input to an Actor. *)

    Definition Set_Input (ast : Actor_State) (i : list V) := {|
        Current_State := ast.(Current_State);
        Clock_Variable := ast.(Clock_Variable);
        Inputs := concat [ast.(Inputs) ; i] ;
        Outputs := ast.(Outputs);
        Internal := ast.(Internal);
    |}.

    (** - [Set_Output] adds one output to an Actor. *)

    Definition Set_Output (ast : Actor_State) (i : list V) := {|
        Current_State := ast.(Current_State);
        Clock_Variable := ast.(Clock_Variable);
        Inputs := ast.(Inputs);
        Outputs := concat [ast.(Outputs) ; i] ;
        Internal := ast.(Internal);
    |}.

    (** - [Set_Initial_Actor_State] configures the initial state of an actor. *)

    Definition Set_Initial_Actor_State (A : Actor) (Internal : I): Actor_State := {|
        Current_State := Initial_State A;
        Clock_Variable := 0;
        Inputs := nil;
        Outputs := nil;
        Internal := Internal;
    |}.

    (** * Actions on an actor. *)

    (** An actor my perform untimed or timed action. we first define each concept separately, then we build a common action type: [Actor_Action]. Each action runs the actors functions defined in [a] on [ast] and returns an updated actor state. *)

    Definition Untimed_Action (actor : Actor) (ast : Actor_State) (action : A) : Actor_State :=
    let step1 := (Fire actor) ast action in
        (Post_Fire actor) step1 action.

    Definition Untimed_Actions (actor : Actor) (ast : Actor_State) (actions : list A) :=
        fold_left (fun x y => Untimed_Action actor x y) actions ast.

    Definition Timed_Action (actor : Actor) (ast : Actor_State) (action : A) (dt : Time) :
        Actor_State :=
        if dt <=? (Deadline actor) (Current_State ast) action then {|
                Clock_Variable := (Clock_Variable ast) + dt;
                Current_State := (Time_Update actor) (Current_State ast) action dt;
                Inputs := ast.(Inputs);
                Outputs := ast.(Outputs);
                Internal := ast.(Internal);
            |}
        else
            ast.

    Inductive Actor_Action :=
        | Dis : list A -> Actor_Action
        | Temp : A -> Time -> Actor_Action.

    (** - [Actor_Step] executes one step, executing the action [act]. This function returns an updated [Actor_State].*)

    Set Asymmetric Patterns.
    Definition Actor_Step (a : Actor) (ast : Actor_State) (act: Actor_Action) :
        Actor_State :=
            match act with
                | Dis action => Untimed_Actions a ast action
                | Temp action t => Timed_Action a ast action t
                end.
    Unset Asymmetric Patterns.

    (** - [LTS_Of] builds a labelled transition system (LTS) out of an actor. *)

    Definition LTS_Of (a : Actor) (Internal : I) : LTS_struct := {|
        States := Actor_State;
        Init := Set_Initial_Actor_State a Internal;
        Actions := Actor_Action;
        Steps := fun ast act => Actor_Step a ast act;
    |}.

    (** * Definition of an actor diagram *)

    Definition Connection := list nat.

    (** An [Actor_Diagram] is a graph of connected actors. An actor diagram has a step function, and additional helper functions to set inputs, fetch outputs and transfer data between actors. *)

    Record Actor_Diagram := mkActor_Diagram {
        Actors : list (Actor * Actor_State);
        Connections : list Connection;
    }.
(*
    Definition Set_Initial_States (l : list Actor) : list (Actor_State) :=
        map Set_Initial_Actor_State l.
*)
    Definition Build_Actor_Diagram
        (actors : list Actor)
        (initial_states : list Actor_State)
        (cnx : list Connection) := {|
            Actors := combine actors initial_states;
            Connections := cnx;
        |}.

    Definition Actor_Diagram_Step
            (diag : Actor_Diagram)
            (action : Actor_Action)
            (id : nat) :=
        {|
            Actors := list_alter id diag.(Actors)
                (fun x => pair (fst x) (Actor_Step (fst x) (snd x) action));
            Connections := diag.(Connections);
        |}.

    Definition Get_States (diag : Actor_Diagram) :=
        map snd (Actors diag).

    Definition Actor_Diagram_Reset_Output
            (diag : Actor_Diagram)
            (id : nat)
        := {|
            Actors := list_alter id diag.(Actors)
                (fun x => pair (fst x) (Fetch_Output (snd x)));
            Connections := diag.(Connections);
        |}.

    Definition Actor_Diagram_Set_Input
        (diag : Actor_Diagram)
        (i : list V)
        (id : nat)
        := {|
            Actors := list_alter id diag.(Actors)
                (fun x => pair (fst x) (Set_Input (snd x) i));
            Connections := diag.(Connections);
        |}.

    Fixpoint Actor_Diagram_Set_Input_list
        (diag : Actor_Diagram)
        (i : list V)
        (ids : list nat) :=
        match ids with
            | nil => diag
            | h :: t => Actor_Diagram_Set_Input_list
                    (Actor_Diagram_Set_Input diag i h) i t
        end.

    Definition Get_Outputs (diag : Actor_Diagram) (id : nat) :=
        nth id (map (fun x => x.(Outputs)) (Get_States diag)) nil.

    Definition Propagate_Outputs (diag : Actor_Diagram) (id : nat) : Actor_Diagram :=
        let value := Get_Outputs diag id in
        let destinations := nth id diag.(Connections) (nil) in
            Actor_Diagram_Set_Input_list diag value destinations.

End Actor_Definition.

(** * Example *)

(** In this example, we build a producer/consummer system made of two actors, and a diagram. *)

Section Actor_Example.

    Inductive some_states := dummy.
    Definition some_types := nat.

    (** ** Definition of [producer_Actor] *)

    Definition producer_labels := some_states.
    Inductive producer_actions := step.
    Definition producer_V := some_types.
    Definition producer_internal := unit.
    Definition producer_state : Type := Actor_State producer_labels producer_V producer_internal.

    Definition producer_Fire (ast : producer_state) (action : producer_actions) :=
        Set_Output ast [42].

    Definition producer_Post_Fire (ast : producer_state) (action : producer_actions) := ast.

    Definition producer_Deadline (s : producer_labels) (action : producer_actions)  : Time := 0.

    Definition producer_Time_Update
        (s : producer_labels) (action : producer_actions) (t : Time) : producer_labels := s.

    Definition producer_Actor : Actor producer_labels producer_actions producer_V producer_internal := {|
        (* Immutable state variable *)
        Initial_State := dummy;

        (* Mapping function *)
        Fire := producer_Fire;
        Post_Fire := producer_Post_Fire;
        Deadline := producer_Deadline;
        Time_Update := producer_Time_Update;
    |}.

    Definition producer_initial_state := Set_Initial_Actor_State producer_Actor tt.

    (** ** Definition of [consumer_Actor] *)

    Definition consumer_labels := some_states.
    Definition consumer_actions := producer_actions.
    Definition consumer_V := producer_V.
    Definition consumer_internal := unit.

    Definition consumer_state : Type := Actor_State consumer_labels consumer_V consumer_internal.
    Definition consumer_Fire
        (ast : consumer_state) (action : consumer_actions) :=
    match ast.(Inputs) with
        | h :: t => {|
            Current_State := ast.(Current_State);
            Clock_Variable := ast.(Clock_Variable);
            Inputs := t;
            Outputs := ast.(Outputs) ;
            Internal := ast.(Internal);
            |}
        | [] => ast
    end.

    Definition consumer_Post_Fire
        (ast : consumer_state) (action : consumer_actions) := ast.

    Definition consumer_Deadline (s : consumer_labels)  (action : consumer_actions) : Time := 0.

    Definition consumer_Time_Update
        (s : consumer_labels)  (action : consumer_actions) (t : Time) : consumer_labels := s.

    Definition consumer_Actor : Actor consumer_labels consumer_actions consumer_V consumer_internal  := {|
        (* Immutable state variable *)
        Initial_State := dummy;

        (* Mapping function *)
        Fire := consumer_Fire;
        Post_Fire := consumer_Post_Fire;
        Deadline := consumer_Deadline;
        Time_Update := consumer_Time_Update;
    |}.
    Definition consumer_initial_state := Set_Initial_Actor_State consumer_Actor tt.
    (** ** Definition of the [prodcons_Diagram] *)

    (** - Initial Actor diagram for the producer/consumer model *)

    Definition prodcons_Diagram_step0 :=
        Build_Actor_Diagram [producer_Actor ; consumer_Actor] [producer_initial_state ; consumer_initial_state] [ [ 1 ] ; []].
        Compute Get_States prodcons_Diagram_step0.
    Lemma step0_OK : Get_States prodcons_Diagram_step0 =
        [{| Current_State := dummy; Clock_Variable := 0; Inputs := []; Outputs := []; Internal := tt;|};
        {| Current_State := dummy; Clock_Variable := 0; Inputs := []; Outputs := []; Internal := tt; |}].
    Proof.
        trivial.
    Qed.
Print prodcons_Diagram_step0.
    (** - Set an input on the producer node *)

    Definition prodcons_Diagram_step1 :=
        Actor_Diagram_Set_Input prodcons_Diagram_step0 ([ 1 ]) 0.
    Lemma step1_OK : Get_States prodcons_Diagram_step1 =
        [{| Current_State := dummy; Clock_Variable := 0; Inputs := [1]; Outputs := [];Internal := tt; |};
        {| Current_State := dummy; Clock_Variable := 0; Inputs := []; Outputs := [];Internal := tt;  |}].
    Proof.
        trivial.
    Qed.

    (** - Producer node computes, setting its output. _Note: we resume from step0 as step1 does not make sense from an application perspecive_.  *)

    Definition prodcons_Diagram_step2 :=
        Actor_Diagram_Step prodcons_Diagram_step0 (Dis [ step ]) 0.
    Lemma step2_OK : Get_States prodcons_Diagram_step2 =
        [{| Current_State := dummy; Clock_Variable := 0; Inputs := []; Outputs := [42];Internal := tt;  |};
        {| Current_State := dummy; Clock_Variable := 0; Inputs := []; Outputs := [];Internal := tt;  |}].
    Proof.
        trivial.
    Qed.

    (** - the output is propagated to the consumer *)

    Definition prodcons_Diagram_step3 := Propagate_Outputs prodcons_Diagram_step2 0.
    Lemma step3_OK : Get_States prodcons_Diagram_step3 =
        [{| Current_State := dummy; Clock_Variable := 0; Inputs := []; Outputs := [42];Internal := tt;  |};
        {| Current_State := dummy; Clock_Variable := 0; Inputs := [42]; Outputs := [];Internal := tt;  |}].
    Proof.
        trivial.
    Qed.

    (** - the output is deleted from the producer *)

    Definition prodcons_Diagram_step4 :=
        Actor_Diagram_Reset_Output prodcons_Diagram_step3 0.
    Lemma step4_OK : Get_States prodcons_Diagram_step4 =
        [{| Current_State := dummy; Clock_Variable := 0; Inputs := []; Outputs := [];Internal := tt;  |};
        {| Current_State := dummy; Clock_Variable := 0; Inputs := [42]; Outputs := [];Internal := tt;  |}].
    Proof.
        trivial.
    Qed.

    (** - the consumer computes its reaction*)

    Definition prodcons_Diagram_step5 :=
        Actor_Diagram_Step prodcons_Diagram_step4 (Dis [ step ]) 1.
    Lemma step5_OK : Get_States prodcons_Diagram_step5 =
        [{| Current_State := dummy; Clock_Variable := 0; Inputs := []; Outputs := [];Internal := tt;  |};
        {| Current_State := dummy; Clock_Variable := 0; Inputs := []; Outputs := [];Internal := tt;  |}].
    Proof.
        trivial.
    Qed.

    (** ** Definition of [director_Actor] *)

    Inductive director_labels := step0 | step1 | step2  | step3 | step4 | step5.
    Inductive director_actions := director_step.
    Definition director_V := nat.
    Definition director_outputs := nat.

    Definition director_internal := Actor_Diagram producer_labels producer_actions producer_V
    producer_internal.

    Definition director_state : Type := Actor_State director_labels director_V director_internal.

    Definition director_Fire
        (ast : director_state) (action : director_actions)  :=
        let local_internal := match ast.(Current_State) with
            | step0 => Actor_Diagram_Step ast.(Internal) (Dis [ step ]) 0
            | step1 => Propagate_Outputs ast.(Internal) 0
            | step2 => Actor_Diagram_Reset_Output ast.(Internal) 0
            | step3 => Actor_Diagram_Step ast.(Internal) (Dis [ step ]) 1
            | _ => ast.(Internal)

        end in {|
            Clock_Variable := (Clock_Variable ast);
            Current_State := ast.(Current_State);
            Inputs := ast.(Inputs);
            Outputs := ast.(Outputs);
            Internal := local_internal ;
        |}.
    Definition rotata_director_labels (d : director_labels ) :=
        match d with
            | step0 => step1
            | step1 => step2
            | step2 => step3
            | step3 => step4
            | step4 => step5
            | step5 => step0
        end.

    Definition director_Post_Fire
    (ast : director_state) (action : director_actions) :=
        {|
            Clock_Variable := (Clock_Variable ast);
            Current_State := rotata_director_labels ast.(Current_State);
            Inputs := ast.(Inputs);
            Outputs := ast.(Outputs);
            Internal := ast.(Internal);
    |}.

    Definition director_Deadline (s : director_labels)  (action : director_actions) : Time := 0.

    Definition director_Time_Update
        (s : director_labels)  (action : director_actions) (t : Time) := s.

    Definition director_Actor : Actor director_labels director_actions director_V director_internal := {|
        (* Immutable state variable *)
        Initial_State := step0;

        (* Mapping function *)
        Fire := director_Fire;
        Post_Fire := director_Post_Fire;
        Deadline := director_Deadline;
        Time_Update := director_Time_Update;
    |}.

    Definition da_initial_state :=
        Set_Initial_Actor_State director_Actor prodcons_Diagram_step0.
    Compute (Current_State da_initial_state).

    (*  Definition Actor_Step (a : Actor) (ast : Actor_State) (act: Actor_Action) :*)
    Definition da_step1 := Actor_Step director_Actor da_initial_state (Dis [director_step]).
    Compute (Get_States (Internal da_step1)).
    Compute (Current_State da_step1).

    Definition da_step2 := Actor_Step director_Actor da_step1 (Dis [director_step]).
    Compute (Get_States (Internal da_step2)).
    Compute (Current_State da_step2).

    Definition da_step3 := Actor_Step director_Actor da_step2 (Dis [director_step]).
    Compute (Get_States (Internal da_step3)).
    Compute (Current_State da_step3).

    Definition da_step4 := Actor_Step director_Actor da_step3 (Dis [director_step]).
    Compute (Get_States (Internal da_step4)).
    Compute (Current_State da_step4).

    Definition da_step5 := Actor_Step director_Actor da_step4 (Dis [director_step]).
    Compute (Get_States (Internal da_step5)).
    Compute (Current_State da_step5).

End Actor_Example.




