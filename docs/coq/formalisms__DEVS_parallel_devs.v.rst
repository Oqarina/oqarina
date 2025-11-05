.. coq::


.. coq:: none

   Require Import Coq.Init.Datatypes.
   Require Import Coq.ZArith.ZArith.
   Require Import Coq.Lists.List.
   Import ListNotations. (* from List *)
   Require Import Coq.Lists.ListSet.

   Require Import Oqarina.core.all.
   Require Import Oqarina.coq_utils.all.
   Require Import Oqarina.CoqExt.all.

   Require Import Oqarina.formalisms.lts.

   #[local] Open Scope bool_scope.
   Set Implicit Arguments.

*************
Parallel DEVS
*************

.. coq:: none

   Section DEVS.

Atomic PDEVS model
==================

See Zeigler section 6.3 for details

An atomic parallel DEVS model is defined as a 8-tuple :math:`<X,Y,S,s_{0},ta,\delta _{ext},\delta _{int},\delta _{con},\lambda >` where

* X is the set of input events;
* Y is the set of output events;
* S is the set of states;
* :math:`s_{0}\in S` is the initial state;
* :math:`ta:S\rightarrow \mathbb {T} ^{\infty }` is the time advance function;
* :math:`\delta _{ext}:Q\times X^b\rightarrow S` is the external transition function which defines how a bag of input events changes a state of the system. We define :math:`Q=\{(s,t_{e})|s\in S,t_{e}\in ({\mathbb {T}}\cap [0,ta(s)])\}` as the total state of a system, with s the current state of the system and :math:`t_{e}` the elapsed time since the last event;
* :math:`\delta _{con}:S\times X^{b}\rightarrow` the confluent transition function, with :math:`\delta _{con}(s,\emptyset )=\delta _{int}(s)`
* :math:`\delta _{{int}}:S\rightarrow S` is the internal transition function which defines how a state of the system changes internally, for instance when the elapsed time reaches to the lifetime of the state;
* :math:`\lambda :S\rightarrow Y^{\phi }` is the output function where :math:`Y^{\phi }=Y\cup \{\phi \}` and :math:`\phi \not \in Y` is a silent event or an unobserved event. This function defines how a state of the system generates an output event (e.g. when the elapsed time reaches to the lifetime of the state).

The Coq type :coq:`DEVS_Atomic_Model` is the specification of an atomic DEVS model, defined by its total state and the four mapping functions defining its behavior.

Note, to ease model manipulation, each DEVS atomic model is given an identifier that can serve to represent either its type (in the case of a model) or its instance (in the case of a simulator).

.. coq::

   Variable Time : Type.
   Context `{Time_i : TimeClass Time }.
   Context `{Time_ops : TimeOperations Time }.
   Import Time_Notations.

   Variable S : Type.                  (* State Set (S) *)
   Variable X : Type.                  (* Input Set (X) *)
   Variable Y : Type.                  (* Output Set (Y) *)

   Inductive Y_output := | y : Y -> Y_output | no_output.
   Record Q := { st : S ; e : Time }.   (* Total state of the system *)

   (* Note: the original definition relies on a bag of X. We opted for a simple list for the moment, it is unclear whether we are interested by the multiplicity of items (that we can rebuild in any case) or even we need a bag here. *)

   Record DEVS_Atomic_Model : Type := {
       devs_atomic_id : identifier ;
       Q_init : Q ;        (* Initial state *)
       ta : S -> Time ;    (* Time advance *)
       δint : S -> S;      (* Internal Transition *)
       λ : S -> list Y_output;  (* Output Function *)
       δext : Q -> list X -> S; (* External Transition *)
       δcon : S -> list X -> S; (* Confluent Transition *)
   }.

   Definition Build_Default_δcon'
       (δint : S -> S) (δext : Q -> list X -> S) :=
       (fun (s : S) (x : list X)  =>
           δext (Build_Q (δint s) Zero) x).

   Definition Build_Default_δcon
       (δint : S -> S) (δext : Q -> list X -> S) :=
       (fun (s : S) (x : list X)  =>
           δint (δext (Build_Q s Zero) x)).

   Instance DEVS_Atomic_Model_id : Element_id DEVS_Atomic_Model := {
       get_id := devs_atomic_id
   }.

   Definition sigma (d : DEVS_Atomic_Model) (q : Q): Time :=
       ((d.(ta) q.(st)) - q.(e))%time.

   Definition Set_Q_Init (d : DEVS_Atomic_Model) (q : Q) := {|
       devs_atomic_id := d.(devs_atomic_id);
       Q_init := q;
       ta := d.(ta);
       δint := d.(δint);
       λ := d.(λ);
       δext := d.(δext);
       δcon := d.(δcon);
   |}.

====================
Simulation of a DEVS
====================

Simulation algorithms for DEVS models produce the sequence of states of the system during its lifecycle. A DEVS simulator is an instance of a DEVS model, that is a DEVS model combined with the current state of the DEVS, the queue of incoming events and clock variables.

Synchronization message
=======================

:coq:`Synchronization_Message_Type` defines the various messages exchanged during a simulation: a DEVS model may be react to incoming events: initialization, time step, input event. A DEVS model may produce events or report all computations are done. Generally speaking, events are sent from one DEVS model to another.

.. coq::

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
           -> Time -> list X -> Synchronization_Message_Type
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

   Definition Get_From (m : Synchronization_Message_Type) :=
       match m with
       | xs (From id) _ _ _ => id
       | ys (From id) _ _ _ => id
       | _ => empty_identifier
       end.

   Definition Get_Dest (m : Synchronization_Message_Type) :=
       match m with
       | xs _ (Dest id) _ _ => id
       | ys _ (Dest id) _ _ => id
       | _ => empty_identifier
       end.

The :coq:`λ` function of a DEVS may send an output. :coq:`DEVS_Add_Output` ensures that we only add valid y messages, i.e. messages different from :coq:`no_output`.

.. coq::

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

DEVS Simulator
==============

A :coq:`DEVS_Simulator` is an instance of a :coq:`DEVS_Atomic_Model`, i.e., the specification of an atomic DEVS with the various state variables defining its state. We provide two helper functions to initialize a DEVS simulator with default values inherited from the DEVS model, and a function to reset the outputs.

.. coq::

   Record DEVS_Simulator : Type := {
       devs_simulator_id : identifier ;
       tla : Time; (* simulation time of last transition *)
       tn : Time;  (* simulation time of next transition *)
       cs : Q;     (* current state of the atomic model *)
       outputs : list Synchronization_Message_Type; (* outgoing event *)
       d : DEVS_Atomic_Model;
   }.

   Instance DEVS_Simulator_Id : Element_id DEVS_Simulator := {
       get_id := devs_simulator_id
   }.

   Definition get_devs_simulator_ids (l : list DEVS_Simulator) :=
       map (fun x => get_id x) l.

   Definition Instantiate_DEVS_Simulator
       (i : identifier) (d : DEVS_Atomic_Model) :=
       Build_DEVS_Simulator i Zero Zero (Build_Q d.(Q_init).(st) Zero) [] d.

   Definition DEVS_Reset_Outputs (s : DEVS_Simulator) :=
       Build_DEVS_Simulator (get_id s) s.(tla) s.(tn) s.(cs) nil s.(d).

   Definition DEVS_Filter_Out_Done (s : DEVS_Simulator) :=
       let outputs' :=
       filter (fun x => match x with | done _ _ _ => false
       | _ => true end) s.(outputs) in
       Build_DEVS_Simulator
           (get_id s) s.(tla) s.(tn) s.(cs) outputs' s.(d).

DEVS Simulation Algortihm #1
----------------------------

Now that we have defined the concept of an atomic DEVS model, we present the simulation of an atomic DEVS.

First, we define :coq:`DEVS_Simulation_Microstep` that represents one computational step. The following implements Algorithm 15 in section 14.4 from Zeigler's book.

.. coq::

   Definition DEVS_Simulation_microStep
       (s : DEVS_Simulator)
       (m : Synchronization_Message_Type)
       : DEVS_Simulator
   :=
       match m with
       | i t => (* if receive (i, from,t) message then *)
           let tla' := t in (* tl ← t - e *)
           let tn' := (tla' + s.(d).(ta) (st s.(cs)))%time in (* tn ← tl + ta(s)*)
           let outputs' :=
               DEVS_Add_Output [done (From s.(devs_simulator_id)) Parent tn']
               s.(outputs) in (* send (done, self, tn) to parent *)
           Build_DEVS_Simulator (get_id s) tla' tn' s.(cs) outputs' s.(d)

       | step t =>
           if (t ==b s.(tn))%time then (* if t = tn then *)
               let y := s.(d).(λ) s.(cs).(st) in (* y ← λ(s) *)
               let outputs' := DEVS_Add_Output
               (* send(y, self, t) to parent *)
               (* send(done, self, tn) to parent *) (* correct from *)
                   ([ done (From s.(devs_simulator_id)) Parent s.(tn) ] ++
                     map
                       (fun a => ys
                           (From s.(devs_simulator_id)) Parent s.(tn) a) y)
                        s.(outputs)
               in
                   Build_DEVS_Simulator
                       (get_id s) s.(tla) s.(tn) s.(cs) outputs' s.(d)

         else s

       | xs _ _ t x' => (* XXX check semantics, should we check that t >= tla *)
           let tla' := t in (* tl ← t *)

           let cs' : S :=
               if ((is_nil x') && (t ==b s.(tn))) then
                   s.(d).(δint) s.(cs).(st)

               else if (t ==b s.(tn)) then
                   s.(d).(δcon) s.(cs).(st) x'

               else if ( (preorder_decb s.(tla) t) && (preorder_decb t s.(tn)) ) then
                   s.(d).(δext) s.(cs) x'

               else  (* XXX must address synchronization errors *)
                   s.(cs).(st) in

           let tn' := (tla' + s.(d).(ta) cs')%time in (* tn ← tl + ta(s) *)

           let te' :=
               if ( (negb (is_nil x')) &&
                   (preorder_decb s.(tla) t) &&
                   (preorder_decb t s.(tn))  ) then
                   (t - s.(tla))%time  (* e ← t - tl *)
               else Zero in

           let outputs' := DEVS_Add_Output
               (* send(done, self, tn) to parent *)
                   [done (From s.(devs_simulator_id)) Parent tn']
                   s.(outputs) in
           Build_DEVS_Simulator
                   (get_id s) tla' tn' (Build_Q cs' te') outputs' s.(d)

       | _ => s

   end.

From this definition, one can derive a LTS structure from a DEVS instance, i.e. a :coq:`DEVS_Simulator`. A DEVS is a LTS whose states are the states of the the DEVS simulator, actions are defined by :coq:`Synchronization_Message_Type` and the step function is one step of the DEVS simulation algorithm.

.. coq::

   Definition LTS_Of_DEVS (ds : DEVS_Simulator) : LTS_struct := {|
       States := DEVS_Simulator;
       Actions := Synchronization_Message_Type ;
       Init := Instantiate_DEVS_Simulator (get_id ds) ds.(d);
       Step := fun ds m =>
                   let ds' := DEVS_Simulation_microStep ds m in
                   DEVS_Filter_Out_Done ds';
       |}.

   Inductive DEVS_Simulator_Debug : Type :=
       dbg : Time -> Time -> S ->
           list Synchronization_Message_Type -> DEVS_Simulator_Debug.

   Definition Get_S (db : DEVS_Simulator_Debug) :=
       match db with
       | dbg _ _ s _ => s
       end.

   Definition Print_DEVS_Simulator (s : DEVS_Simulator) :=
       dbg s.(tla) s.(tn) s.(cs).(st) s.(outputs).

   Definition DEVS_Simulator_state (s : DEVS_Simulator) :=
       s.(cs).(st).

   Definition DEVS_Simulator_outputs (s : DEVS_Simulator) :=
       s.(outputs).

   Definition DEVS_Simulator_tla (s : DEVS_Simulator) :=
       s.(tla).

   Definition DEVS_Simulator_tn (s : DEVS_Simulator) :=
       s.(tn).

   Definition DEVS_Simulator_model (s : DEVS_Simulator) :=
       s.(d).

.. coq:: none

   End DEVS.
