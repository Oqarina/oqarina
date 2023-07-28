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
AADL Systems
============

.. coq:: none |*)
Require Import Coq.Init.Datatypes.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations. (* from List *)
Require Import Coq.Lists.ListSet.
Open Scope bool_scope.

Require Import Oqarina.core.all.
Require Import Oqarina.CoqExt.all.
Require Import Oqarina.coq_utils.all.
Require Import Oqarina.formalisms.DEVS.parallel.all.
Require Import Oqarina.formalisms.all.


Definition Time := nat.

Set Implicit Arguments.
(*| .. coq::  |*)

(*|
The system component category denotes an assembly of interacting application software, execution platform, and sub-systems as sub-components. Systems may be hierarchically nested.

System behavioral semantics
---------------------------

In the following, we start by presenting the behavior of any instance of a system component.

.. figure:: /../_static/aadl_system.png
    :width: 600px
    :align: center

This automata semantics can also be described as follows:

- :code:`system offline` is the system initial state.

- On system startup the system instance transitions from :code:`system offline` to :code:`system starting` through the action :code:`start(system)`

- When in state :code:`system starting`, the system perform the initialization of the system subcomponents. In case of an error during this step, the system goes back to :code:`system offline` through the the :code:`abort(system)` action. When all subsystems have been successfully initialized, the system moves to the state :code:`system operational` through the :code:`started(system)` action.

- When in state :code:`system operational`, the system is under operation, the system and its subcomponents execute their nominal behavior. In case of an error during the execution, the system goes back to :code:`system offline` through the :code:`abort(system)` action.

- Upon completion of its execution, a system may perform a graceful shutdowm (:code:`stop(system)` action) and moves to the state :code:`system stoping`. When all subsystems are successfully stoped, the system moves to the state :code:`system offline` through the :code:`stopped(system)` action.

We propose two semantics:

* a reduction semantics, that defines relations between pairs of state and events

* a semantics based on the DEVS formalism.

We show that they are equivalent.

|*)

(*|
States and events
-----------------

We first define the states and events of the system component category.

* :coq:`X_system` represents the set of incoming events that a system may rect to, as per the hybrid automata defined in AADLv2.2 \S 13.3. |*)

Inductive X_system : Set :=
    start_system | abort_system | started_system
    | stop_system | stopped_system.

Definition Y_system : Type := X_system.

(*| :coq:`system_S` represents the labels of the state of the system DEVS. |*)

Inductive S_system : Set :=
    system_offline | system_starting |
    system_operational | system_stoping.

(*|
Reduction semantics
-------------------

In this section, we provide the set of rules that define the semantics of the previous automata. The state machine is define as a relation that maps a pair :coq:`S_system * X_system` to :coq:`S_system`. |*)


Inductive system_red : S_system * X_system -> S_system -> Prop :=
    | red_system_offline:
        system_red (system_offline, start_system) system_starting

    | red_system_starting:
        system_red (system_starting, started_system) system_operational

    | red_system_operational:
        system_red (system_operational, stop_system) system_stoping

    | red_system_stoping:
        system_red (system_stoping, stopped_system)  system_offline

    | red_system_abort_1:
        system_red (system_starting, abort_system) system_offline

    | red_system_abort_2:
        system_red (system_operational, abort_system) system_offline
    .

(*| This set of rules is deterministic. |*)

Lemma red_determ:
    forall sx s', system_red sx s' ->
        forall s'', system_red sx s'' ->
        s' = s''.
Proof.
    induction 1 ; intros; inversion H ; reflexivity.
Qed.


(*|
DEVS models for the system category
-----------------------------------

The definition of the DEVS component follows the same logic. We build from the previous definitions

* :coq:`Synchronization_Message_Type_system` that synchronizes DEVS components,

|*)

Definition Synchronization_Message_Type_system :=
    Synchronization_Message_Type X_system Y_system.

(*| * :coq:`Q_system` which is the total state of the component |*)

Definition Q_system : Type := Q Time S_system.

Definition Q_init_system := {| st := system_offline ; e := 0 |}.

(*| * The transition functions |*)

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

Definition ta_system (s : S_system) : Time := 1. (* replace with infinity *)

(*| * :coq:`system_DEVS` is the consolidated data type that aggregates all definitions. |*)

Definition system_DEVS_type : Type :=
    DEVS_Atomic_Model Time S_system X_system Y_system.

Definition system_DEVS : system_DEVS_type := {|
    devs_atomic_id := Id "AADL_system" ;
    Q_init := Q_init_system;

    ta := ta_system;
    δint := δint_system;
    λ  := λ_system;
    δext := δext_system;
    δcon := δcon_system;
|}.

(*| * and :coq:`system_DEVS_Simulator` the associated DEVS simulator. |*)

Definition system_DEVS_Simulator_Type : Type :=
    DEVS_Simulator Time S_system X_system Y_system.

Definition system_DEVS_Simulator := Instantiate_DEVS_Simulator
    (Id "System") system_DEVS.

(*| * :coq:`system_DEVS_LTS` is the canonical LTS built from a DEVS simulator.|*)

Definition system_DEVS_LTS := LTS_Of_DEVS (system_DEVS_Simulator).

(*|
Correctness of the DEVS semantics
---------------------------------

|*)

(*|
In the following, we show that the LTS derived from a DEVS is both sound and complete with respect to the reduction semantics we have defined. We also demonstrate that it is live.

First, we define the notion of :coq:`Firable_system_DEVS_LTS`: Let assume a state of a LTS instanciated from a DEVS that represents an AADL System component category (1).  Let assume this state is valid, i.e., no outputs (2). We assume the state is :coq:`st` (3) and assume the DEVS component receives an event at time :coq:`n` that is compatible with DEVS firing semantics.

|*)

Definition Firable_system_DEVS_LTS
    (S: S_system)
    (s: States system_DEVS_LTS)
    (n: Time)
:=
    DEVS_Simulator_model s = system_DEVS /\ (* 1 *)
    DEVS_Simulator_state s = S /\ (* 3 *)
    DEVS_Simulator_outputs s = [] /\ (* 2 *)
    (DEVS_Simulator_tla s) b<= (DEVS_Simulator_tn s) = true /\ (* 4 *)
    (DEVS_Simulator_tla s) b<= n = true /\
    n b<= (DEVS_Simulator_tn s) = true .


(*| The tactics :coq:`prove_LTS_DEVS_clean_hyp` and :coq:`prove_LTS_DEVS_clean_hyp2` helps reducing hypothesis that uses :coq:`Firable_system_DEVS_LTS`.

|*)

(*|.. coq:: none |*)
Ltac prove_LTS_DEVS_clean_hyp :=
    intros s ;
    match goal with
        | [ H : States system_DEVS_LTS |- _ ] =>
            let H2 := fresh "H" in
                destruct H eqn:H2
        end ;
    match goal with
        | [ H : Q Time S_system |- _ ] => destruct H
    end ;
    intros s' x st0 n H_firable H_step_lts
    ;
    match goal with
        | [ H : Firable_system_DEVS_LTS ?st ?s ?n |- _ ] =>
            unfold Firable_system_DEVS_LTS in H ; simpl in H  ;
            inversion H as [Hd [Hs [Houtputs [H_tla_tn [H_tla_n H_n]]]]] ;
            compute in Hs ; rewrite Hd, Houtputs in * ; simpl in * ;
            generalize H_step_lts ;
            simpl
    end.

(* This tactic intros and cleans hypotheses of the form

    forall (s s': States system_DEVS_LTS) (x : X_system) st st2 n,
    Firable_system_DEVS_LTS st s n -> [...]
*)

Ltac prove_LTS_DEVS_clean_hyp_2 :=
    intros s ;
    match goal with
        | [ H : States system_DEVS_LTS |- _ ] =>
            let H2 := fresh "H" in
                destruct H eqn:H2
        end ;
    match goal with
        | [ H : Q Time S_system |- _ ] => destruct H
    end ;
    intros s' x st0 st2 n H_firable H_red H_step_lts
    ;
    match goal with
        | [ H : Firable_system_DEVS_LTS ?st ?s ?n |- _ ] =>
            unfold Firable_system_DEVS_LTS in H ; simpl in H  ;
            inversion H as [Hd [Hs [Houtputs [H_tla_tn [H_tla_n H_n]]]]] ;
            compute in Hs ; rewrite Hd, Houtputs in * ; simpl in * ;
            generalize H_step_lts ;
            simpl ; clear H_firable
    end.

(*|.. coq:: |*)

(*|

* Soundness:

Then either the next state computed by :coq:`step_lts` matches the reduction semantics (case of a valid message) or the next state is the same (case of an out of band message).

|*)

Ltac prove_system_red :=
    match goal with
    (* Typical case: we are given an exact system_red_* rule *)
    | [ |-  system_red (system_offline, start_system) system_starting \/ _ ]
        => left; apply red_system_offline

    | [ |- system_red (system_starting, abort_system) system_offline \/ _ ]
        => left ; apply red_system_abort_1

    | [ |- system_red (system_starting, started_system) system_operational \/ _ ]
        => left ; apply red_system_starting

    | [ |- system_red (system_operational, abort_system) system_offline \/ _ ]
        => left ; apply red_system_abort_2

    | [ |- system_red (system_operational, stop_system) system_stoping \/ _ ]
        => left ; apply red_system_operational

    | [ |- system_red (system_stoping, stopped_system) system_offline \/ _ ]
        => left ; apply red_system_stoping

    (* an alternative is that right is an exact egality statement *)
    | [ |- _ \/ ?x = ?x ] => right ; reflexivity

    | [ |- _ ] => idtac
    end.

Lemma LTS_DEVS_sound:
    forall (s s': States system_DEVS_LTS) (x : X_system) st n,

    Firable_system_DEVS_LTS st s n ->

    (step_lts s (xs Y_system Parent Parent (n) [ x ])) = s' ->
        system_red (DEVS_Simulator_state s, x) (DEVS_Simulator_state s')
        \/ (DEVS_Simulator_state s) = (DEVS_Simulator_state s').
Proof.
    (* First, we clean hypotheses *)
    prove_LTS_DEVS_clean_hyp.

    replace (tla b<= n) with true in * ;
    replace (n b<= tn) with true in *.

    (* We perform an induction on all states and message types.
       We discriminate on the value of n to simplify all expressions,
       and conclude. *)
    induction st, x ; destruct (n ==b tn) ;
    compute ; intros H_s' ; rewrite <- H_s'.

    all: prove_system_red.
Qed.

(*|
* Completeness:

Let assume a state of a LTS instanciated from a DEVS that represents an AADL System component category (1).  Let assume this state is valid, i.e., no outputs (2). We assume the state is :coq:`st` (3) and assume the DEVS component receives an event at time :coq:`n` that is compatible with DEVS firing semantics. Then if state :coq:`st` reduces to state :coq:`st2` then the corresponding LTS state also reduces to a LTS state whose state is :coq:`st2`.

|*)


Lemma LTS_DEVS_complete:
    forall (s s': States system_DEVS_LTS) (x : X_system) st st2 n,

    Firable_system_DEVS_LTS st s n ->

    system_red (st, x) (st2) ->
        step_lts s (xs Y_system Parent Parent (n) [ x ]) = s' ->
        DEVS_Simulator_state s' = st2.

Proof.

    (* This proof follows the same pattern as the previous one *)
    (* First, we clean hypotheses *)
    prove_LTS_DEVS_clean_hyp_2.

    (* From there, we can perform an induction over st and compute all
      solutions directly. *)

    induction st0 ;
        inversion H_red ;
        destruct (n ==b tn) ;
        replace (tla b<= n) with true ;
        replace (n b<= tn) with true ;
        simpl ;
        rewrite Hs ; intros H_s' ; rewrite <- H_s'; trivial.
Qed.

(*|
* Liveness: we show that a LTS instanciated from a DEVS that represents an AADL System component category is live. That is, as long as the DEVS is firable, there exists a transition that can be activated. This proof is by induction on the state :coq:`S_system`.

This proof procedes in two steps. First, we prove a collection of lemmas :coq:`red_system_DEVS_<state>` that shows that how a system DEVS may move from one state to another. Then, we show the general liveness theorem. It is a specific instance of the general :coq:`red_system_DEVS` definition.

The proof of :coq:`red_system_DEVS_<state>` relies on the tactic :coq:`prove_red_system_DEVS `. It simply reduces all termes to basic computations that can be simplified.
|*)

Ltac prove_red_system_DEVS :=
    (* First, we clean hypotheses *)
    prove_LTS_DEVS_clean_hyp ;
    intros ; subst ;
    (* We propagate the value of all inequalities *)
    repeat match goal with
    | [ H : ?X b<= ?Y = true |-  ?G ] =>
        replace (X b<= Y) with true in * ; clear H
    end ;
    simpl;
    (* We destruct basic cases "?X ==b ?Y]" *)
    match goal with
    | [ H: _ |- context[?X ==b ?Y] ] =>
        destruct (X ==b Y)
    end ;
    simpl; discriminate.

Definition red_system_DEVS (x' : X_system) st' : Prop :=
    forall (s s': States system_DEVS_LTS) x st n,
        Firable_system_DEVS_LTS st s n ->
        st = st' ->
        x = x'  ->
        step_lts s (xs Y_system Parent Parent (n) [ x ]) = s' ->
        DEVS_Simulator_state s' <> st.

Lemma red_system_DEVS_system_offline:
    red_system_DEVS start_system system_offline.
Proof.
    prove_red_system_DEVS.
Qed.

Lemma red_system_DEVS_system_starting:
    red_system_DEVS started_system system_starting.
Proof.
    prove_red_system_DEVS.
Qed.

Lemma red_system_DEVS_system_operational:
    red_system_DEVS stop_system system_operational.
Proof.
    prove_red_system_DEVS.
Qed.

Lemma red_system_DEVS_system_stoping:
    red_system_DEVS stopped_system system_stoping.
Proof.
    prove_red_system_DEVS.
Qed.

Lemma system_DEVS_LTS_live :
    forall (S: S_system) (s1: States system_DEVS_LTS) n,
        Firable_system_DEVS_LTS S s1 n ->
        (exists t (s2:States system_DEVS_LTS),
            Transitions system_DEVS_LTS s1 t s2 ->
            DEVS_Simulator_state s2 <> S).
Proof.
    intros S s1 n H.
    induction S.

    - (* S = system_offline *)
      exists (xs Y_system Parent Parent (n) [start_system]).
      exists ((step_lts s1 (xs Y_system Parent Parent (n) [start_system]))).
      eapply red_system_DEVS_system_offline ; auto.

    - (* S = system_starting *)
      exists (xs Y_system Parent Parent (n) [started_system]).
      exists ((step_lts s1 (xs Y_system Parent Parent (n) [started_system]))).
      eapply red_system_DEVS_system_starting ; auto.

    - (* S = system_operational *)
      exists (xs Y_system Parent Parent (n) [stop_system]).
      exists ((step_lts s1 (xs Y_system Parent Parent (n) [stop_system]))).
      eapply red_system_DEVS_system_operational ; auto.

    - (* S = system_stoping *)
      exists (xs Y_system Parent Parent (n) [stopped_system]).
      exists ((step_lts s1 (xs Y_system Parent Parent (n) [stopped_system]))).
      eapply red_system_DEVS_system_stoping ; auto.
Qed.

(*|
Mapping a system hierarchy to a DEVS
-------------------------------------
|*)

(*|
* Map a system component and system subcomponents into a list of DEVS system |*)

Require Import Oqarina.AADL.Kernel.all.
Import AADL_Notations.
Require Import Oqarina.AADL.property_sets.all.

Definition Map_AADL_System_DEVS_System (c : component) :=
    map (fun s => Instantiate_DEVS_Simulator (s->id) system_DEVS)
     (Unfold c).

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

(*| For a list of components, we define the map of influenced
components as follows:
-  A influences B if B is a subcomponent of A
- others XXX TBD e.g. modes, EMV2 state machine, etc.
|*)

Fixpoint Build_Influenced' (lc : list component) :=
    match lc with
    | [] => empty_list_identifiers_map
    | h :: t =>  (h->id) !-> Components_Identifiers (h->subcomps) ;
                 (Build_Influenced' t)
    end.

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
