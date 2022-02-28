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

(*|

************
Classic DEVS
************

In this section, we provide a mechanization of the DEVS formalism. We first define the various data types forming the Classic DEVS formalism, then the simulation algorithms for atomic and coupled DEVS models. We follow the conventions from :math:`\cite{vantendelooIntroductionClassicDEVS2018}`.

|*)

(*| .. coq:: none |*)
Require Import Coq.Init.Datatypes.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations. (* from List *)
Import IfNotations.
Require Import Coq.Lists.ListSet.

Require Import Oqarina.core.all.
Import NaturalTime.
Require Import Oqarina.coq_utils.all.
Require Import Oqarina.formalisms.lts.

#[local] Open Scope bool_scope.
Set Implicit Arguments.

Section DEVS.
(*| .. coq:: |*)
(*|

====================
Definition of a DEVS
====================

DEVS or Discrete Event System Specification is a modular and hierarchical formalism for modeling and simulating systems described by discrete state transitions, continuous states described by differential equations, or a combination of both to build hybrid systems.

Atomic DEVS model
=================

An atomic DEVS model is defined as a 7-tuple :math:`<X,Y,S,s_{0},ta,\delta _{ext},\delta _{int},\lambda >` where

* X is the set of input events;
* Y is the set of output events;
* S is the set of states;
* :math:`s_{0}\in S` is the initial state;
* :math:`ta:S\rightarrow \mathbb {T} ^{\infty }` is the time advance function;
* :math:`\delta _{ext}:Q\times X\rightarrow S` is the external transition function which defines how an input event changes a state of the system. We define :math:`Q=\{(s,t_{e})|s\in S,t_{e}\in ({\mathbb {T}}\cap [0,ta(s)])\}` as the total state of a system, with s the current state of the system and :math:`t_{e}` the elapsed time since the last event;
* :math:`\delta _{{int}}:S\rightarrow S` is the internal transition function which defines how a state of the system changes internally, for instance when the elapsed time reaches to the lifetime of the state;
* :math:`\lambda :S\rightarrow Y^{\phi }` is the output function where :math:`Y^{\phi }=Y\cup \{\phi \}` and :math:`\phi \not \in Y` is a silent event or an unobserved event. This function defines how a state of the system generates an output event (e.g. when the elapsed time reaches to the lifetime of the state).

The Coq type :coq:`DEVS_Atomic_Model` is the specification of an atomic DEVS model, defined by its total state and the four mapping functions defining its behavior.

Note, to ease model manipulation, each DEVS atomic model is given an identifier that can serve to represent either its type (in the case of a model) or its instance (in the case of a simulator).

|*)

Variable S : Type.                  (* State Set (S) *)
Variable X : Type.                  (* Input Set (X) *)
Variable Y : Type.                  (* Output Set (Y) *)

Inductive Y_output := | y : Y -> Y_output | no_output.
Record Q := { st : S ; e : Time }.   (* Total state of the system *)

(* XXX move *)

Class Generic_Model A : Type := {
    get_id : A -> identifier ;   (* Id *) }.

Record DEVS_Atomic_Model : Type := {
    devs_atomic_id : identifier ;
    Q_init : Q ;        (* Initial state *)
    ta : S -> Time ;    (* Time advance *)
    δint : S -> S;      (* Internal Transition *)
    λ : S -> Y_output;  (* Output Function *)
    δext : Q -> X -> S; (* External Transition *) }.


Instance DEVS_Atomic_Model' : Generic_Model DEVS_Atomic_Model := {
    get_id := devs_atomic_id
}.

Definition sigma (d : DEVS_Atomic_Model) (q : Q): Time :=
    d.(ta) q.(st) - q.(e).

Definition Set_Q_Init (d : DEVS_Atomic_Model) (q : Q) := {|
    devs_atomic_id := d.(devs_atomic_id);
    Q_init := q;
    ta := d.(ta);
    δint := d.(δint);
    λ := d.(λ);
    δext := d.(δext);
|}.

(*|

====================
Simulation of a DEVS
====================

Simulation algorithms for DEVS models produce the sequence of states of the system during its lifecycle. A DEVS simulator is an instance of a DEVS model, that is a DEVS model combined with the current state of the DEVS, the queue of incoming events and clock variables.

Synchronization message
=======================

:coq:`Synchronization_Message_Type` defines the various messages exchanged during a simulation: a DEVS model may be react to incoming events: initialization, time step, input event. A DEVS model may produce events or report all computations are done. Generally speaking, events are sent from one DEVS model to another. |*)

Inductive Destination_Type :=
    | Parent
    | Dest : identifier -> Destination_Type
    | From : identifier -> Destination_Type.

Inductive Synchronization_Message_Type :=
    (* initialization of the simulation *)
    | i : Time -> Synchronization_Message_Type
    (* transition in the model*)
    | step : Time -> Synchronization_Message_Type
    (* input event for the model *)
    | xs : Destination_Type (* from *) -> Destination_Type (* to *)
        -> Time -> X -> Synchronization_Message_Type
    (* output event from the model *)
    | ys : Destination_Type (* from *) -> Destination_Type (* to *)
        -> Time -> Y_output -> Synchronization_Message_Type
    (* computation finished for a model *)
    | done: Destination_Type (* from *) -> Destination_Type (* to *)
        ->  Time -> Synchronization_Message_Type .

Definition Set_From
    (m: Synchronization_Message_Type) (from: identifier) :=
    match m with
    | i _ => m
    | step _ => m
    | xs _ to t x => xs (From from) to t x
    | ys _ to t yo => ys (From from) to t yo
    | done _ to t => done (From from) to t
    end.

(*| The :coq:`λ` function of a DEVS may send an output. :coq:`DEVS_Add_Output` ensures that we only add valid y messages, i.e. messages different from :coq:`no_output`. |*)

Definition DEVS_Add_Output
    (l1 l2: list Synchronization_Message_Type) :=
    let filter_output (l : list Synchronization_Message_Type) :=
        filter (fun x => match x with | ys _ _ _ no_output => false
                                        | _ => true end) l in
    (filter_output l1) ++ l2.

Fixpoint Has_Done (l : list Synchronization_Message_Type) :
    option Synchronization_Message_Type :=
    match l with
    | [] => None
    | h :: t => match h with
                | done _ _ _ => Some h (* XXX Parent ?*)
                | _ => Has_Done t
                end
    end.

(*|
DEVS Simulator
==============

A :coq:`DEVS_Simulator` is an instance of a :coq:`DEVS_Atomic_Model`, i.e.the specification of an atomic DEVS with the various state variables defining its state. We provide two helper functions to initialize a DEVS simulator with default values inherited from the DEVS model, and a function to reset the outputs. |*)

Record DEVS_Simulator : Type := {
    devs_simulator_id : identifier ;
    tla : Time; (* simulation time of last transition *)
    tn : Time;  (* simulation time of next transition *)
    cs : Q;     (* current state of the atomic model *)
    outputs : list Synchronization_Message_Type; (* outgoing event *)
    d : DEVS_Atomic_Model;
}.

Instance DEVS_Simulator' : Generic_Model DEVS_Simulator := {
    get_id := devs_simulator_id
}.

Definition Instantiate_DEVS_Simulator (i : identifier) (d : DEVS_Atomic_Model) :=
    Build_DEVS_Simulator i 0 0 (Build_Q d.(Q_init).(st) 0) [] d.

Definition DEVS_Reset_Outputs (s : DEVS_Simulator) :=
    Build_DEVS_Simulator (get_id s) s.(tla) s.(tn) s.(cs) nil s.(d).

(*|

DEVS Simulation Algortihm #1
----------------------------

Now that we have defined the concept of an atomic DEVS model, we present the simulation of an atomic DEVS.

First, we define :coq:`DEVS_Simulation_Microstep` that represents one computational step. The following implements Algorithm 4 from :math:`\cite{vantendelooIntroductionClassicDEVS2018}`. |*)

Definition DEVS_Simulation_microStep
    (s : DEVS_Simulator)
    (m : Synchronization_Message_Type) : DEVS_Simulator :=
    match m with
    | i t => (* if receive (i, from,t) message then *)
        let tla' := t in (* tl ← t - e *)
        let tn' := tla' + s.(d).(ta) (st s.(cs)) in (* tn ← tl + ta(s) *)
        let outputs' :=
            DEVS_Add_Output [done (From empty_identifier) Parent tn']
            s.(outputs) in (* send (done, self, tn) to parent *)
        Build_DEVS_Simulator (get_id s) tla' tn' s.(cs) outputs' s.(d)

    | step t =>
        if t =? s.(tn) then (* if t = tn then *)
            let tla' := t in (* tl ← t *)
            let te' := t - tla' in (* e ← t - tl *)
            let y := s.(d).(λ) s.(cs).(st) in (* y ← λ(s) *)
            let cs' := s.(d).(δint) s.(cs).(st) in (* s ← δint(s) *)
            let tn' := tla' + s.(d).(ta) cs' in (* tn ← tl + ta(s)*)
            let outputs' := DEVS_Add_Output
            (* send(y, self, t) to parent *)
            (* send(done, self, tn) to parent *)
                    [ done (From empty_identifier) Parent tn' ;
                      ys (From empty_identifier) Parent tn' y ]
                     s.(outputs) in
            Build_DEVS_Simulator (get_id s) tla' tn' (Build_Q cs' te') outputs' s.(d)
        else s

    | xs _ _ t x' =>
        if (s.(tla) <=? t) && (t <=? s.(tn)) (* if tl ≤ t ≤ tn *)
        then
            let tla' := t in (* tl ← t *)
            let te' := t - s.(tla) in (* e ← t - tl *)
            let cs' := (* s ← δext((s,e),x) *)
                s.(d).(δext) s.(cs) x' in
            let tn' := tla' + s.(d).(ta) cs'  in (* tn ← tl + ta(s)*)
            let outputs' := DEVS_Add_Output
            (* send(done, self, tn) to parent *)
                [done (From empty_identifier) Parent tn']
                s.(outputs) in
            Build_DEVS_Simulator (get_id s) tla' tn' (Build_Q cs' te') outputs' s.(d)

        else s (* XXX must address synchronization errors *)

    | _ => s
    end.

(*| From this definition, one can derive a LTS structure. |*)

Definition LTS_Of_DEVS (ds : DEVS_Simulator) : LTS_struct := {|
    States := DEVS_Simulator;
    Actions := Synchronization_Message_Type ;
    Init := Instantiate_DEVS_Simulator (get_id ds) ds.(d);
    Step := fun ds m => DEVS_Simulation_microStep ds m;
    |}.

(*|

Root coordinator
----------------

From the defintiion of a micro step, we can now define the notion of a coordinator that will execute micro steps as required to reach a convergence situation in the simulation model.

Note: The following implements Algorithm 5 from :math:`\cite{vantendelooIntroductionClassicDEVS2018}`. |*)

Inductive Root_Coordinator_State :=
    Init_Coordinator | Step_Coordinator.

(*| We define an abstract DEVS_Root_Coordinator, as we will need to coordinate either a coupled model (see below) or an atomic one. |*)

Record DEVS_Root_Coordinator_a (state_t : Type) :=
    Build_DEVS_Root_Coordinator {
    status : bool; (* error status of the coordinator *)
    cstime : Time; (* simulation time *)
    cstate: Root_Coordinator_State;
    astate: state_t; (* XXX some form of polymorphism,
                        check this is really useful *)
    event_queue : list Synchronization_Message_Type;
}.

Definition Iniitialize_DEVS_Root_Coordinator (s : DEVS_Simulator) :=
    Build_DEVS_Root_Coordinator true 0 Init_Coordinator s [].

(*| :coq:`DEVS_Fetch_Input` returns a pair with the first dequeued message and an updated :coq:`DEVS_Root_Coordinator_a` |*)

Definition DEVS_Fetch_Input
    (t : Type) (r : DEVS_Root_Coordinator_a t) :=
    (hd_error r.(event_queue),
        Build_DEVS_Root_Coordinator
        r.(status) r.(cstime) r.(cstate)
        r.(astate) (tl r.(event_queue))).

(*| We define :coq:`DEVS_Root_Coordinqtor` as a specific instance of a DEVS
Root Coordinator with a unique DEVS_Simulator as subcomponent. |*)

Definition DEVS_Root_Coordinator :=
    DEVS_Root_Coordinator_a DEVS_Simulator.

(*| :coq:`DEVS_Propage_Output` propagates output from :coq:`s` output queue to
:coq:`r` event queue. |*)

Definition DEVS_Propagate_Output
    (r : DEVS_Root_Coordinator) (s : DEVS_Simulator) :=
    Build_DEVS_Root_Coordinator
        r.(status) r.(cstime) r.(cstate) (DEVS_Reset_Outputs s)
        (List.concat [r.(event_queue) ; s.(outputs) ]).

(*| :coq:`DEVS_Wait_For_Done` executes :coq:`DEVS_Simulation_microStep` until the  :coq:`Done` message is received or the :coq:`fuel` is 0. |*)

Fixpoint DEVS_Wait_For_Done
    (r : DEVS_Root_Coordinator)
    (m : Synchronization_Message_Type)
    (fuel : nat)
:=
    match fuel with
    | 0 => (false, 0, r)
    | Datatypes.S n =>
        (* Run microstep *)
        let astate' := DEVS_Simulation_microStep r.(astate) m in
        (* Propagate outputs from the DEVS instance to its coordinator *)
        let r' := DEVS_Propagate_Output r astate' in
        (* Check for the Done message *)
        let has_done := Has_Done r'.(event_queue) in
        (* Reset message queue *)
        let r'' :=  Build_DEVS_Root_Coordinator
            r'.(status) r'.(cstime) r'.(cstate) r'.(astate)
            nil in
        match has_done with
        | Some (done _ _ tn) => (true, tn, r'')
        | _ => DEVS_Wait_For_Done r'' m n
        end
end.

(*| :coq:`DEVS_Simulation_Step` runs one step of the DEVS, i.e. runs computations until the Done message is received. |*)

Definition DEVS_Simulation_Step (r : DEVS_Root_Coordinator) ( m : option Synchronization_Message_Type)
: DEVS_Root_Coordinator
:=
    let '(status', cstime', r') :=
        match r.(cstate) with
            | Init_Coordinator =>
                DEVS_Wait_For_Done r (i 0) 10
            | Step_Coordinator =>
                match m with
                | None => DEVS_Wait_For_Done r (step r.(cstime)) 10
                | Some m' => DEVS_Wait_For_Done r m' 10
        end end in
    Build_DEVS_Root_Coordinator status' cstime' Step_Coordinator
        r'.(astate) r'.(event_queue).

Inductive DEVS_Simulator_Debug : Type :=
    dbg : Time -> Time -> S ->
        list Synchronization_Message_Type -> DEVS_Simulator_Debug.

Definition Get_S (db : DEVS_Simulator_Debug) :=
    match db with
    | dbg _ _ s _ => s
    end.

Definition Print_DEVS_Simulator (s : DEVS_Simulator) :=
    dbg s.(tla) s.(tn) s.(cs).(st) s.(outputs).

Definition Print_DEVS_State (r : DEVS_Root_Coordinator) :=
    Print_DEVS_Simulator r.(astate).

(*| .. coq:: none |*)
End DEVS.
