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
AADL Threads
============

.. coq:: none
|*)

(** Coq Library *)
Require Import List.
Import ListNotations. (* from List *)
Require Import Coq.Bool.Bool.
Require Import Coq.Bool.Sumbool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.ZArith.ZArith.
Import IfNotations.

(** Oqarina library *)
Require Import Oqarina.coq_utils.all.

Require Import Oqarina.core.all.
Import NaturalTime.
Require Import Oqarina.AADL.Kernel.all.
Require Import Oqarina.AADL.property_sets.all.

Require Import Oqarina.AADL.declarative.all.
Require Import Oqarina.AADL.instance.all.
Require Import Oqarina.AADL.behavior.port_variable.

Require Import Oqarina.formalisms.DEVS.parallel.all.
Require Import Oqarina.formalisms.all.

Import AADL_Notations.
Open Scope aadl_scope.

Open Scope nat_scope.

(*|
Thread State Variable
---------------------

Each AADL thread is associated to a state variable that stores the relevant parameters relative to is dispatch and scheduling by the underlying executive.

.. coq:: none
|*)

Section Thread_State_Variable.

(*|
:coq:`Build_Dispatch_Trigger` returns the list of triggering features
|*)

Definition Build_Dispatch_Trigger (l : list feature) :=
  filter Is_Triggering_Feature l.
  (* XXX should use also property Dispatch\_Trigger *)

Inductive thread_state := Not_Activated | Idle | Ready | Running.

(*|
:coq:`thread_state_variable` defines the general state variable that stores
the current state of a thread. Its is made of a static part that is derived
from the AADL model, and a dynamic part that is the current state used in the simulation. It is associated with a constructor :coq:`mk_thread_state_variable` and a well-formedness predicate.
|*)

Record thread_state_variable : Type := {
  (* static configuration parameters derived from AADL thread component *)
  dispatch_protocol : Dispatch_Protocol;
  period : Time;
  deadline : AADL_Time;
  priority : Z;
  dispatch_able : bool;
  wcet : Time;

  (* dynamic status *)
  clock : Time; (* clock with reset for evaluating dispatch *)
  cet : Time;   (* execution time clock *)
  delta_cet : Time ;
  current_state : thread_state;
  next_dispatch_time : Time;
  input_ports : list port_variable;
  output_ports : list port_variable;
  dispatch_trigger : list feature;
}.

(*|
* :coq:`mk_thread_state_variable` maps an AADL component to a :coq:`thread_state_variable`.
|*)

Definition mk_thread_state_variable (t : component) : thread_state_variable := {|
  dispatch_protocol := Map_Dispatch_Protocol (t->properties);
  period := (Z.to_nat (Map_Period (t->properties))) ;
  priority := Map_Priority (t->properties);
  deadline := Map_Deadline (t->properties);
  dispatch_able := Map_Dispatch_Able (t->properties);
  wcet := Z.to_nat (snd (Map_Compute_Execution_Time (t->properties)));

  clock := Zero;
  cet := Zero;
  delta_cet := Zero;
  next_dispatch_time := Zero;
  current_state := Not_Activated;
  input_ports := Build_Input_Port_Variables (t->features);
  output_ports := Build_Output_Port_Variables (t->features);
  dispatch_trigger := Build_Dispatch_Trigger (t->features);
|}.

(*|
:coq:`Compute_Entrypoint` defines the compute entrypoint of a thread.
|*)

Definition Compute_Entry_Point := thread_state_variable -> thread_state_variable.

Definition Default_Compute_Entry_Point : Compute_Entry_Point :=
  (fun x => x).

(*|
.. coq:: none
|*)

  Definition thread_state_variable_wf (t : thread_state_variable) :=
    t.(dispatch_protocol) <> Unspecified_Dispatch_Protocol /\
    port_variable_list_wf t.(input_ports) /\
    port_variable_list_wf t.(output_ports)
    .

  Lemma thread_state_variable_wf_dec : forall t : thread_state_variable,
    dec_sumbool (thread_state_variable_wf t).
  Proof.
    intros.
    unfold thread_state_variable_wf.
    repeat apply dec_sumbool_and.
    - destruct (Dispatch_Protocol_eq_dec (dispatch_protocol t) Unspecified_Dispatch_Protocol).
      * subst. auto.
      * subst. auto.
    - apply port_variable_list_wf_dec.
    - apply port_variable_list_wf_dec.
  Qed.

(*|
.. coq:: none
|*)

End Thread_State_Variable.

Ltac prove_thread_state_variable_wf :=
  repeat match goal with
    | |- thread_state_variable_wf _ => compute; repeat split; auto
    | |- ( _ = Unspecified_Dispatch_Protocol -> False) => discriminate
    | |- ( _ = Unspecified_Overflow_Handling_Protocol -> False) => discriminate
    | |- ( _ = Unspecified_Dequeue_Protocol -> False) => discriminate
    | |- NoDup  _  => apply NoDup_cons ; auto
    | |- NoDup nil => apply NoDup_nil
  end.

(*|
Thread Dispatching
------------------

This section captures the content of %\S 5.4.2 of \cite{as2-cArchitectureAnalysisDesign2017}%. Ultimately, we want to provide a definition of the :coq:`Enabled` function that controls the dispatch of a thread. The definition of this function relies on the state of some of its triggering features. In the following, we use directly the concept of thread state variable and port variables to define :coq:`Enabled` .

.. coq:: none
|*)

Section AADL_Dispatching.

(*|
Intermediate Predicates
^^^^^^^^^^^^^^^^^^^^^^^

All AADL dispatch protocols review the state of triggering features and the current clock. We build the :coq:`Thread_Has_Activated_Triggering_Feature` predicate as a conjunction of more basic predicates, in :coq:`Prop`, and demonstrate their decidability.

First, we check whether the feature is activated, :coq:`Is_Feature_Activated`, then whether it is in the dispatch trigger, in :coq:`Feature_In_Dispatch_Trigger`.
|*)

Definition Is_Feature_Activated (p : port_variable) :=
  ~ PortQueue.Is_Empty p.(outer_variable).

(*|
.. coq:: none
|*)

Lemma Is_Feature_Activated_dec :
  forall (p : port_variable),
    { Is_Feature_Activated p } + { ~ Is_Feature_Activated p }.
Proof.
  prove_dec.
Defined.

(*||*)

Definition Feature_In_Dispatch_Trigger (p : port_variable) (d : list feature) :=
  In p.(port) d.

(*|
.. coq:: none
|*)

Definition Feature_In_Dispatch_Trigger_dec :
  forall (p : port_variable) (d : list feature),
    dec_sumbool (Feature_In_Dispatch_Trigger p d).
Proof.
  prove_dec.
Defined.

(*|
From that point, we can build :coq:`Thread_Has_Activated_Triggering_Feature` that is true iff. the thread has at least one activated triggering feature that is also in the dispatch trigger.
|*)

Definition Is_Activated_Triggering_Feature (p : port_variable)  (d : list feature) :=
  Is_Feature_Activated p /\ Feature_In_Dispatch_Trigger p d.

(*|
.. coq:: none
|*)

Lemma Is_Activated_Triggering_Feature_dec:
  forall (p : port_variable)  (d : list feature),
    dec_sumbool (Is_Activated_Triggering_Feature p d).
Proof.
  generalize Is_Feature_Activated_dec.
  prove_dec.
Defined.

Definition Is_Activated_Triggering_Feature_b (p : port_variable)  (d : list feature) :=
  if Is_Activated_Triggering_Feature_dec p d is (left _) then true else false.

(*||*)

Definition Has_Activated_Triggering_Feature
  (l : list port_variable) (d : list feature)
:=
  All_Or (fun x => (Is_Activated_Triggering_Feature x d)) l.

(*|
.. coq:: none
|*)

Lemma Has_Activated_Triggering_Feature_dec :
  forall (l : list port_variable) (d : list feature),
    { Has_Activated_Triggering_Feature l d } + { ~ Has_Activated_Triggering_Feature l d }.
Proof.
  intros.
  unfold Has_Activated_Triggering_Feature.
  induction l.
  - auto.
  - unfold All_Or. apply dec_sumbool_or.
    * apply Is_Activated_Triggering_Feature_dec.
    * apply IHl.
Defined.

(*||*)

Definition Thread_Has_Activated_Triggering_Feature
  (th : thread_state_variable)
  :=
  Has_Activated_Triggering_Feature th.(input_ports) th.(dispatch_trigger).

(*|
.. coq:: none
|*)

  Lemma Thread_Has_Activated_Triggering_Feature_dec :
    forall (th : thread_state_variable),
      { Thread_Has_Activated_Triggering_Feature th } +
      { ~ Thread_Has_Activated_Triggering_Feature th }.
  Proof.
    generalize Has_Activated_Triggering_Feature_dec.
    prove_dec.
  Defined.

(*|
Definition of :coq:`Enabled`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^

From the previous definitions, we can now define the :coq:`Enabled` function that returns :coq:`true` when a thread is dispatched.

A thread can be enable if it is "dispatchable". Then, we define basic predicates for each dispatch protocol.
|*)

Definition Thread_Dispatchable (th : thread_state_variable) :=
  (th.(dispatch_able) = true).

(*|
.. coq:: none
|*)

Lemma Thread_Dispatchable_dec:
  forall (th : thread_state_variable),
    { Thread_Dispatchable th } + { ~  Thread_Dispatchable th }.
Proof.
  prove_dec.
Defined.

(*||*)

Definition Periodic_Enabled (th : thread_state_variable) :=
  (Thread_Dispatchable th) /\ (th.(clock) mod th.(period) = 0).

(*|
.. coq:: none
|*)

Lemma Periodic_Enabled_dec:
  forall (th : thread_state_variable),
   { Periodic_Enabled th } + { ~ Periodic_Enabled th }.
Proof.
  prove_dec.
  apply PeanoNat.Nat.eq_dec.
Defined.

(*||*)

Definition Aperiodic_Enabled (th : thread_state_variable) :=
  (Thread_Dispatchable th) /\
    (Thread_Has_Activated_Triggering_Feature th).

(*|
.. coq:: none
|*)

Lemma Aperiodic_Enabled_dec:
  forall (th : thread_state_variable),
   { Aperiodic_Enabled th } + { ~ Aperiodic_Enabled th  }.
Proof.
  prove_dec.
  apply Thread_Has_Activated_Triggering_Feature_dec.
Defined.

(*||*)

Definition Sporadic_Enabled (th : thread_state_variable) :=
  (Thread_Dispatchable th) /\
    th.(next_dispatch_time) <= th.(clock) /\
   (* th.(period) <= th.(clock) /\ *)
    Thread_Has_Activated_Triggering_Feature th.

(*|
.. coq:: none
|*)

Lemma Sporadic_Enabled_dec:
  forall (th : thread_state_variable),
    { Sporadic_Enabled th } + { ~ Sporadic_Enabled th }.
Proof.
  generalize Thread_Has_Activated_Triggering_Feature_dec.
  generalize Compare_dec.le_dec.
  prove_dec.
Defined.

(*||*)

Definition Timed_Enabled (th : thread_state_variable) :=
  (Thread_Dispatchable th) /\
  ((th.(period) = th.(clock)) \/
  Thread_Has_Activated_Triggering_Feature th).

(*|
.. coq:: none
|*)

Lemma Timed_Enabled_dec:
  forall (th : thread_state_variable),
  { Timed_Enabled th } + { ~ Timed_Enabled th }.
Proof.
  prove_dec.
  apply PeanoNat.Nat.eq_dec.
  apply Thread_Has_Activated_Triggering_Feature_dec.
Defined.

(*||*)

Definition Hybrid_Enabled (th : thread_state_variable) :=
  (Thread_Dispatchable th) /\ (th.(period) = th.(clock)) /\
  Thread_Has_Activated_Triggering_Feature th.

(*|
.. coq:: none
|*)

Lemma Hybrid_Enabled_dec:
  forall (th : thread_state_variable),
    { Hybrid_Enabled th } + { ~ Hybrid_Enabled th }.
Proof.
  prove_dec.
  apply PeanoNat.Nat.eq_dec.
  apply Thread_Has_Activated_Triggering_Feature_dec.
Defined.

(*||*)

Definition Background_Enabled (th : thread_state_variable) :=
  (Thread_Dispatchable th).

(*|
.. coq:: none
|*)

Lemma Background_Enabled_dec:
  forall (th : thread_state_variable),
  { Background_Enabled th } + { ~ Background_Enabled th }.
Proof.
  prove_dec.
Defined.

(*|
Then we define the :coq:`Enabled` predicate
|*)

Definition Enabled (th : thread_state_variable) :=
  match th.(dispatch_protocol) with
  | Periodic => Periodic_Enabled th
  | Sporadic => Sporadic_Enabled th
  | Aperiodic => Aperiodic_Enabled th
  | Timed => Timed_Enabled th
  | Hybrid => Hybrid_Enabled th
  | Background => Background_Enabled th
  | Unspecified_Dispatch_Protocol => False
  end.

(*|
.. coq:: none
|*)

Lemma Enabled_dec: forall (th : thread_state_variable),
  dec_sumbool (Enabled th).
Proof.
  generalize Periodic_Enabled_dec.
  generalize Sporadic_Enabled_dec.
  generalize Aperiodic_Enabled_dec.
  generalize Background_Enabled_dec.
  generalize Timed_Enabled_dec.
  generalize Hybrid_Enabled_dec.
  prove_dec.
Defined.

(*||*)

  (** :coq:`Enabled_oracle` return a :coq:`bool` as a witness, for debugging purposes. *)

  Definition Enabled_oracle (th : thread_state_variable) :=
    if Enabled_dec th is (left _) then true else false.

(*|
.. coq:: none
|*)

End AADL_Dispatching.

(*|
Ports Queue Processing
----------------------

The following is a first cut at formalizing ports from %\S 8.3%. We capture the definition of :coq:`Frozen` for ports. First, we build ATF, the list of Activated Triggering Features.

- :coq:`Activated_Triggering_Features` returns the list of Activated Triggering Features.
|*)

Definition Activated_Triggering_Features'  (l : list port_variable) (d : list feature) :=
  filter (fun x => Is_Activated_Triggering_Feature_b x d) l.

Definition Activated_Triggering_Features (th : thread_state_variable) :=
  Activated_Triggering_Features' th.(input_ports) th.(dispatch_trigger).

(*|
Then, we can define the :coq:`Get_Elected_Triggering_Feature` that returns the elected features among Activated Triggering Features.
|*)

Definition Get_Elected_Triggering_Feature (th : thread_state_variable) :=
  Get_Port_Variable_With_Max_Urgency Invalid_Port_Variable
      (Activated_Triggering_Features th).

(*|
:coq:`Current_Valid_IO_Time_Spec` returns the current IO_Time_Spec for the considered port variable. A port variable can be associated with a list of IO_Time_Spec. The current IO_Time_Spec denotes the IO_Time_Spec that is current to the thread state. %\change{This version is highly simplified. We should define this in the standard first}%
|*)

Definition Current_Valid_IO_Time_Spec
  (p : port_variable)
  (th : thread_state_variable)
:=
  hd Unspecified_IO_Time_Spec (projectionIO_Time_Spec p.(port_input_times)).

(*|
The definition of the :coq:`Frozen` predicate relies on the previous definitions. A port variable is frozen based on the current thread state, the port IO_Time_Spec, etc.
|*)

Definition Dispatch_Frozen (p : port_variable) (th : thread_state_variable) :=
   (p = Get_Elected_Triggering_Feature  th) \/
       ~ (Feature_In_Dispatch_Trigger p th.(dispatch_trigger)).

(*|
.. coq:: none
|*)

Lemma Dispatch_Frozen_dec:
  forall p th, { Dispatch_Frozen p th } + { ~ Dispatch_Frozen p th }.
Proof.
  generalize port_variable_eq_dec.
  prove_dec.
Defined.

(*||*)

Definition Frozen (p : port_variable) (th : thread_state_variable) : Prop :=
  match Current_Valid_IO_Time_Spec p th with
  | Dispatch => Dispatch_Frozen p th
  | NoIo => False
  | Start _ => False
  | Completion _ => False
  | Unspecified_IO_Time_Spec => False
  end.

Lemma Frozen_dec: forall p th,  { Frozen p th } + { ~ Frozen p th }.
Proof.
  generalize Dispatch_Frozen_dec.
  prove_dec.
Defined.

Fixpoint Freeze_Port_Variables
  (l : list port_variable)
  (th : thread_state_variable)
:=
  match l with
  | [] => []
  | h :: t => match Frozen_dec h th with
              | left _ => Receive_Input__ h :: Freeze_Port_Variables t th
              | right _ => h :: Freeze_Port_Variables t th
              end
end.

Definition Frozen_Ports' (th : thread_state_variable): list port_variable :=
  filter_dec port_variable_wf port_variable_wf_dec th.(input_ports).

(*|
Runtime support for threads -- Private API
-------------------------------------------

.. coq:: none
|*)

Section Thread_RTS.

(*|
A collection of runtime services is provided. A runtime service manipulates the thread state and its port variables.

:coq:`advance_time` increments the clock of the thread state variable.
|*)

Definition advance_time (th : thread_state_variable) (t : Time) (n : Time) := {|
  (* Generic part *)
  dispatch_protocol := th.(dispatch_protocol);
  period := th.(period);
  deadline := th.(deadline);
  priority := th.(priority);
  dispatch_able := th.(dispatch_able);
  wcet := th.(wcet);

  input_ports := th.(input_ports);
  output_ports := th.(output_ports);
  dispatch_trigger := th.(dispatch_trigger);
  current_state := th.(current_state);
  next_dispatch_time := th.(next_dispatch_time);

  (* advance_time *)
  clock := t;
  delta_cet := n;
  cet := th.(cet);
|}.

Definition freeze_thread_ports (th : thread_state_variable)  := {|
  (* Generic part *)
  dispatch_protocol := th.(dispatch_protocol);
  period := th.(period);
  deadline := th.(deadline);
  priority := th.(priority);
  dispatch_able := th.(dispatch_able);
  wcet := th.(wcet);

  clock := th.(clock);
  delta_cet := th.(delta_cet);
  cet := th.(cet);

  output_ports := th.(output_ports);
  dispatch_trigger := th.(dispatch_trigger);
  current_state := th.(current_state);
  next_dispatch_time := th.(next_dispatch_time);

  (* freeze_ports *)
  input_ports := Freeze_Port_Variables th.(input_ports) th;
|}.

Definition reset_thread_ports (th : thread_state_variable)  := {|
  (* Generic part *)
  dispatch_protocol := th.(dispatch_protocol);
  period := th.(period);
  deadline := th.(deadline);
  priority := th.(priority);
  dispatch_able := th.(dispatch_able);
  wcet := th.(wcet);

  clock := th.(clock);
  delta_cet := th.(delta_cet);
  cet := th.(cet);

  output_ports := th.(output_ports);
  dispatch_trigger := th.(dispatch_trigger);
  current_state := th.(current_state);
  next_dispatch_time := th.(next_dispatch_time);

  (* reset_thread_ports *)
  input_ports := map Reset_Port_Variable th.(input_ports) ;
|}.

Definition compute_during (th : thread_state_variable) (t : Time) := {|
  (* Generic part *)
  dispatch_protocol := th.(dispatch_protocol);
  period := th.(period);
  deadline := th.(deadline);
  priority := th.(priority);
  dispatch_able := th.(dispatch_able);
  wcet := th.(wcet);

  input_ports := th.(input_ports);
  output_ports := th.(output_ports);
  dispatch_trigger := th.(dispatch_trigger);
  current_state := th.(current_state);
  next_dispatch_time := th.(next_dispatch_time);

  (* compute_during *)
  clock := th.(clock) + t;
  cet := th.(cet) + t;
  delta_cet := t;
|}.

(*|
:coq:`store_in` stores a value in an outer\_port of an AADL thread.
|*)

Definition store_in
  (t : thread_state_variable) (name : identifier) (value : bool) := {|
  (* Generic part *)
  dispatch_protocol := t.(dispatch_protocol);
  period := t.(period);
  deadline := t.(deadline);
  priority := t.(priority);
  dispatch_able := t.(dispatch_able);
  wcet := t.(wcet);

  clock := t.(clock);
  cet := t.(cet);
  delta_cet := t.(delta_cet);
  output_ports := t.(output_ports);
  dispatch_trigger := t.(dispatch_trigger);
  current_state := t.(current_state);
  next_dispatch_time := t.(next_dispatch_time);

  (* store_in *)
  input_ports := Store t.(input_ports) name (t.(clock), value);
|}.

(*|
XXX
|*)

Definition eval_enabled_thread_state (t : thread_state_variable) :=
let is_enabled := Enabled_oracle t in {|
(* Generic part *)
  dispatch_protocol := t.(dispatch_protocol);
  period := t.(period);
  deadline := t.(deadline);
  priority := t.(priority);
  dispatch_able := t.(dispatch_able);
  wcet := t.(wcet);

  clock := t.(clock); (* XXX should reset the clock if enabled *)
  cet := t.(cet);
  delta_cet := t.(delta_cet);
  output_ports := t.(output_ports);
  dispatch_trigger := t.(dispatch_trigger);
  input_ports := t.(input_ports);

  (* eval_enabled_thread_state *)
  current_state := if is_enabled then Ready else t.(current_state);
  next_dispatch_time :=
    if is_enabled then
      match t.(dispatch_protocol) with
      | Periodic => t.(clock) + t.(period)
      | Sporadic => t.(clock) + t.(period)
      | _ => t.(clock)
      end
    else t.(next_dispatch_time);
|}.

Definition nop (t : thread_state_variable) := {|
  (* Generic part *)
  dispatch_protocol := t.(dispatch_protocol);
  period := t.(period);
  deadline := t.(deadline);
  priority := t.(priority);
  dispatch_able := t.(dispatch_able);
  wcet := t.(wcet);

  current_state := t.(current_state);
  clock := t.(clock);
  cet := t.(cet);
  output_ports := t.(output_ports);
  dispatch_trigger := t.(dispatch_trigger);
  input_ports := t.(input_ports);
  next_dispatch_time := t.(next_dispatch_time);

  (* set_running *)
  delta_cet := 0;
|}.

Definition set_running (t : thread_state_variable) := {|
  (* Generic part *)
  dispatch_protocol := t.(dispatch_protocol);
  period := t.(period);
  deadline := t.(deadline);
  priority := t.(priority);
  dispatch_able := t.(dispatch_able);
  wcet := t.(wcet);

  clock := t.(clock);
  cet := t.(cet);
  delta_cet := t.(delta_cet);
  output_ports := t.(output_ports);
  dispatch_trigger := t.(dispatch_trigger);
  input_ports := t.(input_ports);
  next_dispatch_time := t.(next_dispatch_time);

  (* set_running *)
  current_state := Running;
|}.

Definition set_Idle (t : thread_state_variable) := {|
  (* Generic part *)
  dispatch_protocol := t.(dispatch_protocol);
  period := t.(period);
  deadline := t.(deadline);
  priority := t.(priority);
  dispatch_able := t.(dispatch_able);
  wcet := t.(wcet);

  clock := t.(clock);
  delta_cet := t.(delta_cet);
  output_ports := t.(output_ports);
  dispatch_trigger := t.(dispatch_trigger);
  input_ports := t.(input_ports);
  next_dispatch_time := t.(next_dispatch_time);

  (* set_Idle *)
  current_state := Idle;
  cet := 0;
|}.

(*|
Runtime support for threads -- AADL RTS
---------------------------------------

The definition of the RTS relies on the port functions presented in XXX.

* :coq:`Await_Dispatch`
|*)

Definition await_dispatch (t : thread_state_variable) := {|
  (* Generic part *)
  dispatch_protocol := t.(dispatch_protocol);
  period := t.(period);
  deadline := t.(deadline);
  priority := t.(priority);
  dispatch_able := t.(dispatch_able);
  wcet := t.(wcet);

  clock := t.(clock);
  output_ports := t.(output_ports);
  dispatch_trigger := t.(dispatch_trigger);
  input_ports := t.(input_ports);
  next_dispatch_time := t.(next_dispatch_time);

  (* await_dispatch *)
  current_state := Idle;

  cet := 0;
  delta_cet := 0;
|}.

(*|
* :coq:`Get_Count`
|*)

Definition get_count (t : thread_state_variable) (name : identifier) :=
  Get_Count t.(input_ports) name.

(*|
* :coq:`Put_Value`
|*)

Definition put_value
  (t : thread_state_variable) (name : identifier) (value : bool) := {|
  (* Generic part *)
  dispatch_protocol := t.(dispatch_protocol);
  period := t.(period);
  deadline := t.(deadline);
  priority := t.(priority);
  dispatch_able := t.(dispatch_able);
  wcet := t.(wcet);

  clock := t.(clock);
  cet := t.(cet);
  delta_cet := t.(delta_cet);
  input_ports := t.(input_ports);
  dispatch_trigger := t.(dispatch_trigger);
  current_state := t.(current_state);
  next_dispatch_time := t.(next_dispatch_time);

  (* put_value *)
  output_ports := Store t.(output_ports) name (t.(clock), value);
|}.

(*|
* :coq:`Send_Output`
|*)

Definition send_output (t : thread_state_variable) (name : identifier) := {|
  (* Generic part *)
  dispatch_protocol := t.(dispatch_protocol);
  period := t.(period);
  deadline := t.(deadline);
  priority := t.(priority);
  dispatch_able := t.(dispatch_able);
  wcet := t.(wcet);

  clock := t.(clock);
  cet := t.(cet);
  delta_cet := t.(delta_cet);
  input_ports := t.(input_ports);
  dispatch_trigger := t.(dispatch_trigger);
  current_state := t.(current_state);
  next_dispatch_time := t.(next_dispatch_time);

  (* send_output *)
  output_ports := Send_Output t.(output_ports) name;
|}.

(*|
* :coq:`Get_Value`
|*)

Definition get_value (t : thread_state_variable) (name : identifier) :=
  Get_Value t.(input_ports) name.

(*|
* :coq:`Next_Value`
|*)

Definition next_value
  (t : thread_state_variable) (name : identifier) (value : bool) := {|
  (* Generic part *)
  dispatch_protocol := t.(dispatch_protocol);
  period := t.(period);
  deadline := t.(deadline);
  priority := t.(priority);
  dispatch_able := t.(dispatch_able);
  wcet := t.(wcet);

  clock := t.(clock);
  cet := t.(cet);
  delta_cet := t.(delta_cet);
  output_ports := t.(output_ports);
  dispatch_trigger := t.(dispatch_trigger);
  current_state := t.(current_state);
  next_dispatch_time := t.(next_dispatch_time);

  (* next_value *)
  input_ports := Next_Value t.(input_ports) name;
|}.

(*|
* :coq:`Receive_Input`
|*)

Definition receive_input (t : thread_state_variable) (name : identifier) := {|
  (* Generic part *)
  dispatch_protocol := t.(dispatch_protocol);
  period := t.(period);
  deadline := t.(deadline);
  priority := t.(priority);
  dispatch_able := t.(dispatch_able);
  wcet := t.(wcet);

  clock := t.(clock);
  cet := t.(cet);
  delta_cet := t.(delta_cet);
  output_ports := t.(output_ports);
  dispatch_trigger := t.(dispatch_trigger);
  current_state := t.(current_state);
  next_dispatch_time := t.(next_dispatch_time);

  (* receive_input *)
  input_ports := Receive_Input t.(input_ports) name;
|}.

(*|
.. coq:: none
|*)

End Thread_RTS.

(*|
Examples
--------

A Periodic Thread
^^^^^^^^^^^^^^^^^

In this example, we first build a periodic AADL :coq:`Component`, we then map it to a :coq:`thread_state_variable` and perform some steps on it.
|*)

Example A_Periodic_Thread :=
    thread: "a_periodic_thread" ->| "pack::a_thread_classifier.impl"
        extends: None
        features: nil
        subcomponents: nil
        connections: nil
        properties: [
            property: Priority_Name ==>| PV_Int 42 ;
            property: Dispatch_Protocol_Name ==>| PV_Enum (Id "Periodic") ;
            property: Period_Name ==>| PV_IntU 500 (PV_Unit (Id "ms")) ;
            property: Compute_Execution_Time_Name ==>|
                PV_IntRange (PV_IntU 0 (PV_Unit (Id "ms")))
                            (PV_IntU 100 (PV_Unit (Id "ms")))
        ].

(*|
This component is well-formed
|*)

Lemma A_Periodic_Thread_wf : Well_Formed_Component_Instance A_Periodic_Thread.
Proof.
  prove_Well_Formed_Component_Instance.
Qed.

Definition A_Periodic_Thread_State_ := set_Idle (mk_thread_state_variable (A_Periodic_Thread)).

Check A_Periodic_Thread_State_.

Lemma A_Periodic_Thread_State_valid : thread_state_variable_wf A_Periodic_Thread_State_ .
Proof.
  prove_thread_state_variable_wf.
Qed.

(** - "activate" the thread *)

Definition A_Periodic_Thread_State :=
  eval_enabled_thread_state A_Periodic_Thread_State_.

(** - At t = 0, the periodic thread is enabled *)

Lemma Periodic_t0_enabled : A_Periodic_Thread_State.(current_state) = Ready.
Proof.
  compute.
  trivial.
Qed.

(** - "do something" *)

Definition A_Periodic_Thread_State' := advance_time A_Periodic_Thread_State 2 0.
Definition A_Periodic_Thread_State'' := await_dispatch A_Periodic_Thread_State'.

(** - At t = 2, the periodic thread is not enabled *)

Lemma Periodic_t2_not_enabled :
  A_Periodic_Thread_State''.(current_state) = Idle.
Proof.
  trivial.
Qed.

(*|
A Sporadic Thread
^^^^^^^^^^^^^^^^^

In this example, we consider a sporadic thread with one input event port.
|*)

Example A_Sporadic_Thread :=
thread: "a_periodic_thread" ->| "pack::a_thread_classifier.impl"
    extends: None
    features: [
      feature: in_event "a_feature"
    ]
    subcomponents: nil
    connections: nil
    properties: [
        property: Priority_Name ==>| PV_Int 42 ;
        property: Dispatch_Protocol_Name ==>| PV_Enum (Id "Sporadic") ;
        property: Period_Name ==>| PV_IntU 500 (PV_Unit (Id "ms")) ;
        property: Compute_Execution_Time_Name ==>|
            PV_IntRange (PV_IntU 0 (PV_Unit (Id "ms")))
                        (PV_IntU 100 (PV_Unit (Id "ms")))
    ].

(*|
This component is well-formed
|*)

Lemma A_Sporadic_Thread_wf : Well_Formed_Component_Instance A_Sporadic_Thread.
Proof.
  prove_Well_Formed_Component_Instance.
Qed.

(*|
We can continue and build a corresponding thread state variable, add an event, avance time and check whether the thread is enabled.
|*)

Definition A_Sporadic_Thread_State_ := set_Idle (mk_thread_state_variable (A_Sporadic_Thread)).

Lemma A_Sporadic_Thread_State_valid : thread_state_variable_wf A_Sporadic_Thread_State_.
Proof.
  prove_thread_state_variable_wf.
Qed.

Definition A_Sporadic_Thread_State := eval_enabled_thread_state A_Sporadic_Thread_State_.

(*|
Initially, the sporadic thread is not enabled
|*)

Lemma Sporadic_tO_not_enabled :
  Enabled_oracle (A_Sporadic_Thread_State) = false.
Proof. trivial. Qed.

(*|
Inject two events. Because of the DropOldest policy used, with a queue size of 1, we loose the first event
|*)

Definition A_Sporadic_Thread_State' :=
  store_in A_Sporadic_Thread_State (Id "a_feature") false.
Definition A_Sporadic_Thread_State'' :=
  store_in A_Sporadic_Thread_State' (Id "a_feature") true.

(** - The thread is not enabled yet *)

Lemma Sporatic_tO_not_enabled' :
  A_Sporadic_Thread_State''.(current_state) = Idle.
Proof. trivial. Qed.

(** - We advance time *)
Definition th_ := advance_time A_Sporadic_Thread_State'' 500 0.
Definition th := eval_enabled_thread_state th_.

(** - The thread is enabled, and we can check frozen port *)

Lemma Sporadic_t500_enabled : th.(current_state) = Ready.
Proof. trivial. Qed.

Lemma ETF:
  Get_Port_Variable_Name (Get_Elected_Triggering_Feature (th)) = Id "a_feature".
Proof. trivial. Qed.

Compute Frozen_Ports' th.

(* - At this stage, we have not called receive_input, no event available *)

Lemma get_count_1 : get_count th (Id "a_feature") = 0%nat.
Proof. trivial. Qed.

(* - Calling receive input *)

Definition th_rec := receive_input th (Id "a_feature").

Lemma get_count_2 : get_count th_rec (Id "a_feature") = 1%nat.
Proof. trivial. Qed.

Lemma get_value_1 : get_value th_rec (Id "a_feature") = (0,true).
Proof. trivial. Qed.

(*|
AADL thread as a P-DEVS
-----------------------

Let us turn this thread into a P-DEVS.

* :coq:`X_thread` is the set of incoming messages the P-DEVS reacts to.
|*)

Inductive X_thread : Set :=
| thread_step
| eval_enabled  (clock: Time)
| run_thread (clock : Time) (duration : Time)
| store_message (clock : Time) (port_name : identifier) (value : bool)
| time_advance (clock : Time)
.

Definition Y_thread : Type := X_thread.

Definition Synchronization_Message_Type_thread :=
    Synchronization_Message_Type X_thread Y_thread.

(*|
* :coq:`S_thread` is the state variable of the P-DEVS. It is the cross-product of a label denoting the state and the actual state varoable. XXX thread_state_variable also has the Ready/Idle/Run state, is this redundant ?
|*)

Inductive S_thread_labels : Set :=
    | performing_thread_activation
    | suspended_awaiting_dispatch
    | performing_thread_computation .

Record S_thread := {
  thread_l : S_thread_labels ;
  thread_st : thread_state_variable ;
  thread_ce : Compute_Entry_Point;
  }.

Definition Update_S_thread
  (s : S_thread)
  (label : S_thread_labels)
  (tsv : thread_state_variable)
:=
 {| thread_l := label ; thread_st := tsv; thread_ce := s.(thread_ce) |} .

Definition Q_thread : Type := Q S_thread.

Definition Q_init_thread
  (tsv : thread_state_variable)
  (tce : Compute_Entry_Point)
  : Q_thread :=
  {| st := {| thread_l := performing_thread_activation ;
              thread_st := tsv;
              thread_ce := tce ;
              |} ;
    e := Zero |}.

Definition Update_Q
  (q : Q_thread)
  (label : S_thread_labels)
  (tsv : thread_state_variable)
:=
  {| st := Update_S_thread q.(st) label tsv ; e := q.(e) |}.

(*|
* :coq:`δint_thread` updates the internal state of the thread

  - (1) if the thread is Idle, we evaluate its enabled function using eval_enabled_thread_state. If the thread is Ready, we enter the performing thread conputation

  - (2) if the thread is Running, and if its compute execution time is equal to its WCET, the thread becomes suspended (external AADL state) and Idle .

  - Otherwise, we keep the existing state
|*)

Definition δint_thread (s : S_thread) : S_thread :=
  match s.(thread_st).(current_state) with

    | Not_Activated  => s

    | Idle => (* (1) *)
      let state' := eval_enabled_thread_state s.(thread_st) in
        match state'.(current_state) with
        | Ready =>
          let state'' := freeze_thread_ports state' in
            Update_S_thread s performing_thread_computation state''

        | _ =>  s
        end

    | Running => (* (2) *)
    (* XXX must split compute_entrypoint into parts: await/fetch/execute/write
all atomic except execute

    *)
      let state := s.(thread_ce) s.(thread_st) in

      if state.(wcet) <=? state.(cet) then
      let state' := reset_thread_ports state in
        {| thread_l := suspended_awaiting_dispatch ;
           thread_st := set_Idle state' ;
           thread_ce := s.(thread_ce) |}

      else
        {| thread_l := performing_thread_computation;
           thread_st := state;
           thread_ce := s.(thread_ce) |}

    | Ready  => s
  end.

(*|
* :coq:`δext_thread` take into account incoming messages to update
the thread state.
|*)

Definition δext_thread (q : Q_thread) (x : list X_thread) : S_thread :=
  match q.(st).(thread_l), hd_error x with

    | performing_thread_activation, Some thread_step =>
      let state' := await_dispatch q.(st).(thread_st) in
        {| thread_l  := suspended_awaiting_dispatch ;
          thread_st := state' ;
          thread_ce := q.(st).(thread_ce) |}

    | suspended_awaiting_dispatch, Some (eval_enabled c) =>
      let state' := advance_time q.(st).(thread_st) c 0 in
        {| thread_l := q.(st).(thread_l) ;
          thread_st := state' ;
          thread_ce := q.(st).(thread_ce) |}

    |  _, Some (time_advance c) =>
      let state' := advance_time q.(st).(thread_st) c 0 in
        {| thread_l := q.(st).(thread_l) ;
          thread_st := state' ;
          thread_ce := q.(st).(thread_ce) |}

    | performing_thread_computation, Some (run_thread c n) =>
      let state := set_running q.(st).(thread_st) in
      let state' := advance_time state c n in
        {| thread_l := performing_thread_computation ;
          thread_st := state' ;
          thread_ce := q.(st).(thread_ce) |}

    | _, Some (store_message c p m) =>
      let state' := store_in q.(st).(thread_st) p m in
        {| thread_l :=  q.(st).(thread_l);
           thread_st := state' ;
           thread_ce := q.(st).(thread_ce) |}

    | _, _ =>
    let state' := nop q.(st).(thread_st) in
      {| thread_l :=  q.(st).(thread_l);
        thread_st := state' ;
        thread_ce := q.(st).(thread_ce) |}

end.

Definition δcon_thread  := Build_Default_δcon δint_thread δext_thread.

Definition Y_output_thread : Type := Y_output Y_thread.

Definition λ_thread (s : S_thread) : list Y_output_thread :=
  match s with
    | _ => [ no_output Y_thread ]
  end.

Definition ta_thread (s : S_thread) : Time :=
  match s.(thread_l) with
    | performing_thread_activation => Zero

    | suspended_awaiting_dispatch =>
      match s.(thread_st).(dispatch_protocol) with
        | Periodic =>
          s.(thread_st).(next_dispatch_time) + s.(thread_st).(delta_cet)
          - s.(thread_st).(clock)

        | Sporadic => s.(thread_st).(delta_cet)

        | _ => Zero
      end

    (* XXX if periodic, OK, if sporadic, should be 0*)

    | performing_thread_computation => s.(thread_st).(delta_cet)
  end.

Definition thread_DEVS_type : Type :=
    DEVS_Atomic_Model S_thread X_thread Y_thread.

Definition thread_DEVS_Simulator_Type : Type :=
    DEVS_Simulator S_thread X_thread Y_thread.

Definition thread_DEVS
  (t : component)
  (ce : Compute_Entry_Point)
  : thread_DEVS_type := {|
  devs_atomic_id := t->id ;
  Q_init := Q_init_thread (mk_thread_state_variable t) ce;

  ta := ta_thread;
  δint := δint_thread;
  λ  := λ_thread;
  δext := δext_thread;
  δcon := δcon_thread;
|}.

Definition thread_Initial
  (t : component)
  (ce : Compute_Entry_Point)
:=
  Instantiate_DEVS_Simulator (t->id) (thread_DEVS t ce).

(*|
Periodic thread test
^^^^^^^^^^^^^^^^^^^^

Translate DEVS to a LTS
|*)

Definition Periodic_Compute_Entry_Point : Compute_Entry_Point :=
  fun x : thread_state_variable =>
    compute_during x x.(delta_cet).

Definition A_Periodic_initial :=
  thread_Initial A_Periodic_Thread Periodic_Compute_Entry_Point.

Definition thread_LTS := LTS_Of_DEVS (A_Periodic_initial).

Example thread_LTS_0 := Init thread_LTS.

(*|
* Step#0: we confirm the correct initialization of a thread
|*)

Lemma thread_LTS_0_OK :
    Print_DEVS_Simulator thread_LTS_0 =
    dbg Zero Zero
    {|
      thread_l := performing_thread_activation;
      thread_st :=
        {|
          dispatch_protocol := Periodic;
          period := 500;
          deadline := 0%Z;
          priority := 42;
          dispatch_able := true;
          wcet := 100;
          clock := 0;
          cet := 0;
          delta_cet := 0;
          current_state := Not_Activated;
          next_dispatch_time := 0;
          input_ports := [];
          output_ports := [];
          dispatch_trigger := []
        |};
        thread_ce := Periodic_Compute_Entry_Point;
    |} [].
Proof. trivial. Qed.

(*|
* Step#1: We perform a :coq:`thread_step` to activate the thread. Because of the activation time allows the thread to be dispatched, the thread directly enters the :coq:`performing_thread_computation` state. This is expected because of the confluence function that executes first the external transition, then the internal one.
|*)

Example thread_LTS_1 :=
  step_lts thread_LTS_0
    (xs Y_thread Parent Parent Zero [ thread_step ]).

Lemma thread_LTS_1_OK :
    Print_DEVS_Simulator thread_LTS_1 =
    dbg Zero Zero
    {|
      thread_l := performing_thread_computation;
      thread_st :=
        {|
          dispatch_protocol := Periodic;
          period := 500;
          deadline := 0%Z;
          priority := 42;
          dispatch_able := true;
          wcet := 100;
          clock := 0;
          cet := 0;
          delta_cet := 0;
          current_state := Ready;
          next_dispatch_time := 500;
          input_ports := [];
          output_ports := [];
          dispatch_trigger := []
        |};
        thread_ce := Periodic_Compute_Entry_Point;
    |} [].
Proof. trivial. Qed.

(*|
* Step#2: we "run" the thread for 50 ms
|*)

Example thread_LTS_2 :=
    step_lts thread_LTS_1
    (xs Y_thread Parent Parent Zero [ run_thread 0 50 ]).

Lemma thread_LTS_2_OK :
    Print_DEVS_Simulator thread_LTS_2 =
    dbg 0 50
    {|
      thread_l := performing_thread_computation;
      thread_st :=
        {|
          dispatch_protocol := Periodic;
          period := 500;
          deadline := 0%Z;
          priority := 42;
          dispatch_able := true;
          wcet := 100;
          clock := 50;
          cet := 50;
          delta_cet := 50;
          current_state := Running;
          next_dispatch_time := 500;
          input_ports := [];
          output_ports := [];
          dispatch_trigger := []
        |};
        thread_ce := Periodic_Compute_Entry_Point;
    |} [].
Proof. trivial. Qed.

(*|
* Step#3: we "run" the thread for another 50 ms to see it being completed and go back to :coq:`suspended_awaiting_dispatch` state.
|*)

Example thread_LTS_3 :=
    step_lts thread_LTS_2 (xs Y_thread Parent Parent 50%nat [ run_thread 50 50%nat ]).

Lemma thread_LTS_3_OK :
    Print_DEVS_Simulator thread_LTS_3 =
    dbg 50%nat 500%nat
    {|
      thread_l := suspended_awaiting_dispatch;
      thread_st :=
        {|
          dispatch_protocol := Periodic;
          period := 500;
          deadline := 0%Z;
          priority := 42;
          dispatch_able := true;
          wcet := 100;
          clock := 100; (* XXX *)
          cet := 0;
          delta_cet := 50;
          current_state := Idle;
          next_dispatch_time := 500;
          input_ports := [];
          output_ports := [];
          dispatch_trigger := []
        |};
        thread_ce := Periodic_Compute_Entry_Point;
    |} [].
Proof. trivial. Qed.

Example thread_LTS_4 :=
    step_lts thread_LTS_3
    (xs Y_thread Parent Parent 500 [ eval_enabled 500 ]).

Lemma thread_LTS_4_OK :
    Print_DEVS_Simulator thread_LTS_4 =
    dbg 500 500
    {|
      thread_l := performing_thread_computation;
      thread_st :=
             {|
               dispatch_protocol := Periodic;
               period := 500;
               deadline := 0%Z;
               priority := 42;
               dispatch_able := true;
               wcet := 100;
               clock := 500;
               cet := 0;
               delta_cet := 0;
               current_state := Ready;
               next_dispatch_time := 1000;
               input_ports := [];
               output_ports := [];
               dispatch_trigger := []
             |};
        thread_ce := Periodic_Compute_Entry_Point;
    |} [].
Proof. trivial. Qed.

Example thread_LTS_5 :=
    step_lts thread_LTS_4 (xs Y_thread Parent Parent 500 [ run_thread 500 100%nat ]).

Lemma thread_LTS_5_OK :
    Print_DEVS_Simulator thread_LTS_5 =
    dbg 500 1000
         {|
           thread_l := suspended_awaiting_dispatch;
           thread_st :=
             {|
               dispatch_protocol := Periodic;
               period := 500;
               deadline := 0%Z;
               priority := 42;
               dispatch_able := true;
               wcet := 100;
               clock := 600;
               cet := 0;
               delta_cet := 100;
               current_state := Idle;
               next_dispatch_time := 1000;
               input_ports := [];
               output_ports := [];
               dispatch_trigger := []
             |};
          thread_ce := Periodic_Compute_Entry_Point;
          |} [].
Proof. trivial. Qed.

(*|
Sporadic thread test
^^^^^^^^^^^^^^^^^^^^

Translate DEVS to a LTS
|*)

Definition Sporadic_Compute_Entry_Point : Compute_Entry_Point :=
  fun x : thread_state_variable =>
    compute_during x x.(delta_cet).

Definition A_Sporadic_initial :=
  thread_Initial A_Sporadic_Thread Sporadic_Compute_Entry_Point.

Definition S_thread_LTS := LTS_Of_DEVS (A_Sporadic_initial).

Example S_thread_LTS_0 := Init S_thread_LTS.

(*|
* Step#0: we confirm the correct initialization of a thread
|*)

Compute Print_DEVS_Simulator S_thread_LTS_0.
Lemma S_thread_LTS_0_OK :
    Print_DEVS_Simulator S_thread_LTS_0 =
    dbg Zero Zero
    {|
      thread_l := performing_thread_activation;
      thread_st :=
        {|
          dispatch_protocol := Sporadic;
          period := 500;
          deadline := 0%Z;
          priority := 42;
          dispatch_able := true;
          wcet := 100;
          clock := 0;
          cet := 0;
          delta_cet := 0;
          current_state := Not_Activated;
          next_dispatch_time := 0;
          input_ports :=
          [{|
             port :=
               Feature (Id "a_feature") inF eventPort
                 (Component (Id "") null (FQN [] (Id "") None) None [] []
                    [] []) [];
             is_data := false;
             inner_variable := [];
             outer_variable := [];
             port_input_times := Input_Time [Dispatch];
             urgency := 0;
             size := 1;
             overflow_handling_protocol := DropOldest;
             dequeue_protocol := OneItem;
             dequeued_items := 0
           |}];
          output_ports := [];
          dispatch_trigger :=
          [Feature (Id "a_feature") inF eventPort
             (Component (Id "") null (FQN [] (Id "") None) None [] [] [] [])
             []]
        |};
        thread_ce := Periodic_Compute_Entry_Point;
    |} [].
Proof. trivial. Qed.

(*|
* Step#1: We perform a :coq:`thread_step` to activate the thread. XXX
|*)

Example S_thread_LTS_1 :=
  step_lts S_thread_LTS_0
    (xs Y_thread Parent Parent Zero [ thread_step ]).

Compute Print_DEVS_Simulator S_thread_LTS_1.

Lemma S_thread_LTS_1_OK :
    Print_DEVS_Simulator S_thread_LTS_1 =
    dbg 0 0
         {|
           thread_l := suspended_awaiting_dispatch;
           thread_st :=
             {|
               dispatch_protocol := Sporadic;
               period := 500;
               deadline := 0%Z;
               priority := 42;
               dispatch_able := true;
               wcet := 100;
               clock := 0;
               cet := 0;
               delta_cet := 0;
               current_state := Idle;
               next_dispatch_time := 0;
               input_ports :=
                 [{|
                    port :=
                      Feature (Id "a_feature") inF eventPort
                        (Component (Id "") null (FQN [] (Id "") None) None [] []
                           [] []) [];
                    is_data := false;
                    inner_variable := [];
                    outer_variable := [];
                    port_input_times := Input_Time [Dispatch];
                    urgency := 0;
                    size := 1;
                    overflow_handling_protocol := DropOldest;
                    dequeue_protocol := OneItem;
                    dequeued_items := 0
                  |}];
               output_ports := [];
               dispatch_trigger :=
                 [Feature (Id "a_feature") inF eventPort
                    (Component (Id "") null (FQN [] (Id "") None) None [] [] [] [])
                    []]
             |};
             thread_ce := Periodic_Compute_Entry_Point;
             |} [].
Proof. trivial. Qed.

(*|
* Step#2: We send an event to the sporadic thread, the thread is immediatly dispatched.
|*)

Example S_thread_LTS_2 :=
  step_lts S_thread_LTS_1
    (xs Y_thread Parent Parent 0 [ store_message 0 (Id "a_feature") false ]).

Compute Print_DEVS_Simulator S_thread_LTS_2.

Lemma S_thread_LTS_2_OK :
    Print_DEVS_Simulator S_thread_LTS_2 =
    dbg 0 0
    {|
      thread_l := performing_thread_computation;
      thread_st :=
        {|
          dispatch_protocol := Sporadic;
          period := 500;
          deadline := 0%Z;
          priority := 42;
          dispatch_able := true;
          wcet := 100;
          clock := 0;
          cet := 0;
          delta_cet := 0;
          current_state := Ready;
          next_dispatch_time := 500;
          input_ports :=
            [{|
               port :=
                 Feature (Id "a_feature") inF eventPort
                   (Component (Id "") null (FQN [] (Id "") None) None [] []
                      [] []) [];
               is_data := false;
               inner_variable := [(0, false)];
               outer_variable := [];
               port_input_times := Input_Time [Dispatch];
               urgency := 0;
               size := 1;
               overflow_handling_protocol := DropOldest;
               dequeue_protocol := OneItem;
               dequeued_items := 0
             |}];
          output_ports := [];
          dispatch_trigger :=
            [Feature (Id "a_feature") inF eventPort
               (Component (Id "") null (FQN [] (Id "") None) None [] [] [] [])
               []]
        |};
        thread_ce := Periodic_Compute_Entry_Point;
        |} [].
Proof. trivial. Qed.

(*|
* Step#3: We execute the thread for 100 time units. The thread goes to the :coq:`suspended_awaiting_dispatch` state.
|*)

Example S_thread_LTS_3 :=
  step_lts S_thread_LTS_2
    (xs Y_thread Parent Parent 0  [ run_thread 0 100%nat ]).

Compute Print_DEVS_Simulator S_thread_LTS_3.

Lemma S_thread_LTS_3_OK :
    Print_DEVS_Simulator S_thread_LTS_3 =
    dbg 0 100
    {|
      thread_l := suspended_awaiting_dispatch;
      thread_st :=
        {|
          dispatch_protocol := Sporadic;
          period := 500;
          deadline := 0%Z;
          priority := 42;
          dispatch_able := true;
          wcet := 100;
          clock := 100;
          cet := 0;
          delta_cet := 100;
          current_state := Idle;
          next_dispatch_time := 500;
          input_ports :=
            [{|
               port :=
                 Feature (Id "a_feature") inF eventPort
                   (Component (Id "") null (FQN [] (Id "") None) None [] []
                      [] []) [];
               is_data := false;
               inner_variable := [];
               outer_variable := [];
               port_input_times := Input_Time [Dispatch];
               urgency := 0;
               size := 1;
               overflow_handling_protocol := DropOldest;
               dequeue_protocol := OneItem;
               dequeued_items := 0
             |}];
          output_ports := [];
          dispatch_trigger :=
            [Feature (Id "a_feature") inF eventPort
               (Component (Id "") null (FQN [] (Id "") None) None [] [] [] [])
               []]
        |};
        thread_ce := Periodic_Compute_Entry_Point;
        |} [].
Proof. trivial. Qed.

(*|
* Step#4: We just step .
|*)

Example S_thread_LTS_4 :=
  step_lts S_thread_LTS_3
    (xs Y_thread Parent Parent 100 [ thread_step  ]).

Compute Print_DEVS_Simulator S_thread_LTS_4.

Lemma S_thread_LTS_4_OK :
    Print_DEVS_Simulator S_thread_LTS_4 =
    dbg 100 100
         {|
           thread_l := suspended_awaiting_dispatch;
           thread_st :=
             {|
               dispatch_protocol := Sporadic;
               period := 500;
               deadline := 0%Z;
               priority := 42;
               dispatch_able := true;
               wcet := 100;
               clock := 100;
               cet := 0;
               delta_cet := 0;
               current_state := Idle;
               next_dispatch_time := 500;
               input_ports :=
                 [{|
                    port :=
                      Feature (Id "a_feature") inF eventPort
                        (Component (Id "") null (FQN [] (Id "") None) None [] []
                           [] []) [];
                    is_data := false;
                    inner_variable := [];
                    outer_variable := [];
                    port_input_times := Input_Time [Dispatch];
                    urgency := 0;
                    size := 1;
                    overflow_handling_protocol := DropOldest;
                    dequeue_protocol := OneItem;
                    dequeued_items := 0
                  |}];
               output_ports := [];
               dispatch_trigger :=
                 [Feature (Id "a_feature") inF eventPort
                    (Component (Id "") null (FQN [] (Id "") None) None [] [] [] [])
                    []]
             |};
             thread_ce := Periodic_Compute_Entry_Point;
             |} [].
Proof. trivial. Qed.
