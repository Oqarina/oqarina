(** %\chapter{Actor Component Model}\label{chap::actor}%

The following captures the Actor component model as described in the Ptolemy toolset and presented in %\cite{tripakisModularFormalSemantics2013,leeHeterogeneousActorModeling2011}%. *)

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

    % \begin{definition}[Actor (Ptolemy)]
    An Actor is a tuple $A = (I,O,S,s_0,F,P,D,T)$ where $I$ is a set of input variables, $O$ is a set of output variables, $S$ is a set of state variables, $s_0 \in S$ is the initial state, and $Fire$, $Post\_Fire$, $Deadline$, and $Time_Update$ are total functions with the following types that controls the execution of an actor.

    \end{definition}% *)

    Variable St : Type. (* States *)
    Variable V : Type.  (* Values *)

    Record Actor: Type := {
        (* Immutable state variable *)
        Initial_State : St;

        (* Mapping functions *)
        Fire : St -> V -> list V;
        Post_Fire : St -> V -> St;
        Deadline : St -> V -> Time;
        Time_Update : St -> V -> Time -> St;
    }.

    Record Actor_State : Type := {
        Current_State : St;
        Clock_Variable : Time;
        Inputs : list V;
        Outputs : list V;
    }.

    (** * Operations on an actor.

    We provide three accessors for manipulating inputs, outpurs and setting the initial state of an actor. *)

    (** - [Fetch_Output] removes one output from an Actor. *)

    Definition Fetch_Output (ast : Actor_State) := {|
        Current_State := ast.(Current_State);
        Clock_Variable := ast.(Clock_Variable);
        Inputs := ast.(Inputs);
        Outputs := tl ast.(Outputs);
    |}.

    (** - [Set_Input] adds one input to an Actor. *)

    Definition Set_Input (ast : Actor_State) (i : list V) := {|
        Current_State := ast.(Current_State);
        Clock_Variable := ast.(Clock_Variable);
        Inputs := concat [ast.(Inputs) ; i] ;
        Outputs := ast.(Outputs);
    |}.

    (** - [Set_Initial_Actor_State] configures the initial state of an actor. *)

    Definition Set_Initial_Actor_State (A : Actor) : Actor_State := {|
        Current_State := Initial_State A;
        Clock_Variable := 0;
        Inputs := nil;
        Outputs := nil;
    |}.

    (** * Actions on an actor. *)

    (** An actor my perform untimed or timed action. we first define each concept separately, then we build a common action type: [Actor_Action]. Each action runs the actors functions defined in [a] on [ast] and returns an updated actor state. *)

    Definition Untimed_Action (a : Actor) (ast : Actor_State) (i : V) : Actor_State := {|
        Current_State := (Post_Fire a) (Current_State ast) i;
        Clock_Variable := (Clock_Variable ast);
        Inputs := tail ast.(Inputs);
        Outputs := concat [((Fire a) (Current_State ast) i) ; (Outputs ast)];
    |}.

    Definition Untimed_Actions (a : Actor) (ast : Actor_State) (i : list V) :=
        fold_left (fun x y => Untimed_Action a x y) i ast.

    Definition Timed_Action (a : Actor) (ast : Actor_State) (i : V) (dt : Time) :
        Actor_State :=
        if dt <=? (Deadline a) (Current_State ast) i then {|
                Clock_Variable := (Clock_Variable ast) + dt;
                Current_State := (Time_Update a) (Current_State ast) i dt;
                Inputs := ast.(Inputs);
                Outputs := (Outputs ast)
            |}
        else
            ast.

    Inductive Actor_Action :=
        | Dis : list V -> Actor_Action
        | Temp : V -> Time -> Actor_Action.

(** - [Actor_Step] executes one step, executing the action [act]. This function returns an updated [Actor_State].*)

    Set Asymmetric Patterns.
    Definition Actor_Step (a : Actor) (ast : Actor_State) (act: Actor_Action) :
        Actor_State :=
            match act with
                | Dis i => Untimed_Actions a ast i
                | Temp i t => Timed_Action a ast i t
                end.
    Unset Asymmetric Patterns.

(** - [LTS_Of] builds a labelled transition system (LTS) out of an actor. *)

    Definition LTS_Of (a : Actor) : LTS_struct := {|
        States := Actor_State;
        Init := Set_Initial_Actor_State a;
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

    Definition Set_Initial_States (l : list Actor) : list (Actor_State) :=
        map Set_Initial_Actor_State l.

    Definition Build_Actor_Diagram
        (actors : list Actor)
        (cnx : list Connection) := {|
            Actors := combine actors (Set_Initial_States actors);
            Connections := cnx;
        |}.

    Definition Actor_Diagram_Step
        (diag : Actor_Diagram)
        (action : Actor_Action)
        (id : nat) := {|
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

(** In this examplem we define a dummy actor made of two states, A and B and three actions DoA, DoB and Nothing.
*)

Inductive some_states := dummy.
Definition some_types := nat.
Definition a_value : some_types := 42.

Definition producer_states := some_states.
Definition producer_inputs := some_types.
Definition producer_outputs  := some_types.

Definition producer_Fire
    (s : producer_states) (i : producer_inputs) : list producer_outputs := [ a_value ].

Definition producer_Post_Fire
    (s : producer_states)  (i : producer_inputs) : producer_states := dummy.

Definition producer_Deadline (s : producer_states)  (i : producer_inputs) : Time := 0.

Definition producer_Time_Update
    (s : producer_states)  (i : producer_inputs) (t : Time) : producer_states := s.

Definition producer_Actor : Actor producer_states producer_inputs := {|
    (* Immutable state variable *)
    Initial_State := dummy;

    (* Mapping function *)
    Fire := producer_Fire;
    Post_Fire := producer_Post_Fire;
    Deadline := producer_Deadline;
    Time_Update := producer_Time_Update;
|}.

Definition consumer_states := some_states.
Definition consumer_inputs := nat.
Definition consumer_outputs := nat.

Definition consumer_Fire
    (s : consumer_states) (i : consumer_inputs) : list consumer_outputs := [ ].

Definition consumer_Post_Fire
    (s : consumer_states)  (i : consumer_inputs) : consumer_states := dummy.

Definition consumer_Deadline (s : consumer_states)  (i : consumer_inputs) : Time := 0.

Definition consumer_Time_Update
    (s : consumer_states)  (i : consumer_inputs) (t : Time) : consumer_states := s.

Definition consumer_Actor : Actor consumer_states consumer_inputs := {|
    (* Immutable state variable *)
    Initial_State := dummy;

    (* Mapping function *)
    Fire := consumer_Fire;
    Post_Fire := consumer_Post_Fire;
    Deadline := consumer_Deadline;
    Time_Update := consumer_Time_Update;
|}.

Definition prod := producer_Actor.
Definition cons := consumer_Actor.

Definition prodcons_Diagram := Build_Actor_Diagram [prod ; cons] [ [ 1 ] ; []].
Compute (Get_States prodcons_Diagram).

Compute Get_States (Actor_Diagram_Step prodcons_Diagram (Dis [ 1 ]) 0).

Definition prodcons_Diagram_step0 := Actor_Diagram_Set_Input prodcons_Diagram ([ 1 ]) 0.
Compute Get_States prodcons_Diagram_step0.
Definition prodcons_Diagram_step1 := Actor_Diagram_Step prodcons_Diagram_step0 (Dis [ 1 ]) 0.
Compute Get_States prodcons_Diagram_step1.
Definition prodcons_Diagram_step2 := Actor_Diagram_Reset_Output prodcons_Diagram_step1 0.
Compute Get_States prodcons_Diagram_step2.

Definition coin St V (a : Actor_Diagram St V) (i : V) (id : nat) :=
    compose (fun x : Actor_Diagram St V => Actor_Diagram_Step x (Dis [ i ]) id)
            (fun x : Actor_Diagram St V => Actor_Diagram_Set_Input x ([  ]) id)
        a.


Definition coin2 St V (a : Actor_Diagram St V) (i : V) (id : nat) :=
    let micro_step1 := Actor_Diagram_Set_Input a ([  ]) id in
        Actor_Diagram_Step micro_step1 (Dis [ i ]) id.



Definition prodcons_Diagram_step1bis := coin prodcons_Diagram 42 0.
Compute Get_States prodcons_Diagram_step1bis.

Definition prodcons_Diagram_step1ter := coin2 prodcons_Diagram 42 0.
Compute Get_States prodcons_Diagram_step1ter.

Definition prodcons_Diagram_step2bis := Propagate_Outputs prodcons_Diagram_step1bis 0.
Compute Get_States prodcons_Diagram_step2bis.
Definition prodcons_Diagram_step3bis := Actor_Diagram_Reset_Output prodcons_Diagram_step2bis 0.
Compute Get_States prodcons_Diagram_step3bis.

Print Actor_Diagram_Step.

Definition prodcons_Diagram_step4 := coin2 prodcons_Diagram_step3bis 1 1.
Compute Get_States prodcons_Diagram_step4.
