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
AADL Port variables
===================
|*)

(*| .. coq:: none |*)
(** Coq Library *)
Require Import List.
Import ListNotations. (* from List *)
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.BinInt.

(** Oqarina library *)
Require Import Oqarina.coq_utils.all.
Require Import Oqarina.core.all.
Import NaturalTime.
Require Import Oqarina.AADL.Kernel.all.
Require Import Oqarina.AADL.property_sets.all.

Local Open Scope Z_scope.
(*| .. coq:: |*)

(*|
Port Variable
-------------

  *A port variable captures the feature of a component as a runtime entity.
  Port variables are accessed through runtime services (AADLv2.2 (8.2))*.

Port variable maps AADL features to runtime level entities. We define the concept of port variable and use it to capture further the dynamic semantics of AADL threads. A port variable is modeled by a Coq record. We define the concept of invalid port variable and a constructor for this record, along withe well-formedness rule and decidability result. Then, we define two set of runtime services: one set derived from the AADL standard, another used to build a simulation environment to synchronize all components.

|*)

(*| The root of a port variable is a port queue, with typical FIFO semantics. This is captured in an external formalization in :coq:`ListQueue`. |*)

Module PortVal.
  Definition V := prod Time bool.
  Definition Invalid_Value := (1978%nat, true).
End PortVal.

Module PortQueue := ListQueue PortVal.

Definition Port_Queue : Type := PortQueue.queue.

(*| .. coq:: none |*)
Lemma Port_Queue_dec : forall x y : Port_Queue, {x=y}+{x<>y}.
Proof.
  repeat decide equality.
Qed.
(*| .. coq:: |*)

(*| .. coq:: none |*)
Section Port_Variable.
(*| .. coq:: |*)

(*| A :coq:`port_variable` is made of two collections of elements. First, static configuration parameters derive from the corresponding AADL feature: a reference to an AADL feature, a queue that stores incoming events or calls, :coq:`port_input_times` that indicates when a feature can be frozen, and an urgency value to discriminate among activated triggering features. Other elements configures the port queue: urgency, size, etc. Then, two states variables exist to represent the two port queues used to represent a port variable. |*)

Record port_variable : Type := {
  (* static configuration parameters *)
  port : feature;
  is_data : bool;
  port_input_times : input_time;
  urgency : Z;
  size : Z;
  overflow_handling_protocol : Overflow_Handling_Protocol;
  dequeue_protocol : Dequeue_Protocol;
  dequeued_items : Z;

  (* state *)
  inner_variable : Port_Queue;
  outer_variable : Port_Queue;
}.

(*| .. coq:: none |*)
Lemma port_variable_eq_dec : forall x y : port_variable, {x=y}+{x<>y}.
Proof.
  repeat decide equality.
Defined.
(*| .. coq:: |*)

(*| A port variable is well-formed iff its configuration parameters are well-formed. This property is decidable. |*)

Definition port_variable_wf (p : port_variable) :=
  (* XXX p.(f) well formed *)
  input_time_wf p.(port_input_times) /\
  p.(overflow_handling_protocol) <>
    Unspecified_Overflow_Handling_Protocol /\
  p.(dequeue_protocol) <> Unspecified_Dequeue_Protocol.

(*| .. coq:: none |*)
Definition port_variable_wf_dec : forall p : port_variable,
  { port_variable_wf p } + { ~ port_variable_wf p }.
Proof.
  generalize IO_Time_Spec_eq_dec.
  generalize Overflow_Handling_Protocol_eq_dec.
  generalize Dequeue_Protocol_eq_dec.
  prove_dec.
Defined.

Definition port_variable_list_wf (l : list port_variable) :=
  All port_variable_wf l.

Definition port_variable_list_wf_dec : forall p : list port_variable,
  dec_sumbool (port_variable_list_wf p).
Proof.
  generalize port_variable_wf_dec.
  prove_dec.
Qed.
(*| .. coq:: |*)

(*| * :coq:`mkPortVariable` maps an AADL feature to a :coq:`port_variable`. The port variable is initialized with an empty queue. |*)

Definition mkPortVariable (f : feature) := {|
  port := f;
  is_data := Is_Data_Portb f;
  port_input_times := Map_Input_Time (projectionFeatureProperties f);
  urgency := Map_Urgency (projectionFeatureProperties f);
  size := Map_Queue_Size (projectionFeatureProperties f);
  overflow_handling_protocol :=
    Map_Overflow_Handling_Protocol (projectionFeatureProperties f);
  dequeue_protocol := Map_Dequeue_Protocol (projectionFeatureProperties f);
  dequeued_items := Map_Dequeued_Items (projectionFeatureProperties f);

  inner_variable := [];
  outer_variable := [];
|}.

(*| * :coq:`Invalid_Port_Variable` is |*)

Definition Invalid_Port_Variable := mkPortVariable Invalid_Feature.

(*| :coq:`Build_Input_Port_Variables` (resp. :coq:`Build_Output_Port_Variables`) is a utility function that builds port variables from input (resp. output) features. AADL inout features are also considered. *)

Definition Build_Input_Port_Variables (l : list feature) :=
  map mkPortVariable (Get_Input_Features l).

Definition Build_Output_Port_Variables (l : list feature) :=
  map mkPortVariable (Get_Output_Features l).

Definition Update_Inner_Variable (p : port_variable) (v : Port_Queue): port_variable := {|
  port := p.(port);
  is_data := p.(is_data);
  inner_variable := v;
  outer_variable := [];
  port_input_times := p.(port_input_times);
  urgency := p.(urgency);
  size := p.(size);
  overflow_handling_protocol := p.(overflow_handling_protocol);
  dequeue_protocol := p.(dequeue_protocol);
  dequeued_items := p.(dequeued_items);
|}.

Definition Update_Outer_Variable (p : port_variable) (v : Port_Queue): port_variable := {|
  port := p.(port);
  is_data := p.(is_data);
  inner_variable := [];
  outer_variable := v;
  port_input_times := p.(port_input_times);
  urgency := p.(urgency);
  size := p.(size);
  overflow_handling_protocol := p.(overflow_handling_protocol);
  dequeue_protocol := p.(dequeue_protocol);
  dequeued_items := p.(dequeued_items);
|}.

Definition Reset_Port_Variable (p : port_variable) : port_variable := {|
  port := p.(port);
  is_data := p.(is_data);
  inner_variable := []; (* XXX enough ?*)
  outer_variable := p.(outer_variable);
  port_input_times := p.(port_input_times);
  urgency := p.(urgency);
  size := p.(size);
  overflow_handling_protocol := p.(overflow_handling_protocol);
  dequeue_protocol := p.(dequeue_protocol);
  dequeued_items := p.(dequeued_items);
|}.

Definition Get_Port_Variable_By_Name (l : list port_variable) (name : identifier) :=
  find (fun x => identifier_beq (projectionFeatureIdentifier x.(port)) name) l.

Definition Get_Port_Variable_Name (p : port_variable) :=
  projectionFeatureIdentifier p.(port).

(*| - :coq:`Get_Port_Variable_With_Max_Urgency` returns the port variable with the maximum urgency, see %\S 8.3 (32) \change{We should also address the FIFO for ports with same urgency .. }% |*)

Fixpoint Get_Port_Variable_With_Max_Urgency
  (p : port_variable) (l : list port_variable) : port_variable :=
    match l with
    | nil => p
    | h :: t => if p.(urgency) <=? h.(urgency)
      then Get_Port_Variable_With_Max_Urgency h t
      else Get_Port_Variable_With_Max_Urgency p t
      (* note we take h in all cases, this is to address the case where the
        first argument is :coq:`Invalid_Port_Variable` *)
    end.

(*| .. coq:: none |*)
End Port_Variable.
(*| .. coq:: |*)

(*|
Runtime services
----------------
|*)

(*| .. coq:: none |*)
Section Port_Variable_RTS.
(*| .. coq:: |*)
(** %\begin{definition}[store\_in [port variable](Coq)]
TBD
  \end{definition} %*)

Definition Store_DropNewest
  (p : port_variable) (name : identifier) (value : PortVal.V)
:=
  if Z.of_nat (PortQueue.count p.(outer_variable)) <? p.(size) then
    Update_Outer_Variable p (PortQueue.enq p.(outer_variable) value)
  else
    p.

Definition Store_DropOldest
  (p : port_variable) (name : identifier) (value : PortVal.V)
:=
  if Z.of_nat (PortQueue.count p.(outer_variable)) <? p.(size) then
    Update_Outer_Variable p (PortQueue.enq p.(outer_variable) value)
  else
    let q := PortQueue.deq p.(outer_variable) in
    Update_Outer_Variable p (PortQueue.enq q value).

Definition Store_
  (p : port_variable) (name : identifier) (value : PortVal.V)
:=
  if identifier_beq (projectionFeatureIdentifier p.(port)) name then
    match p.(overflow_handling_protocol) with
    | DropNewest => Store_DropNewest p name value
    | DropOldest => Store_DropOldest p name value
    | Error => p
    | Overflow_Handling_Protocol_Unspecified => p
    end
  else
    p.

Definition Store
  (l : list port_variable) (name : identifier) (value : PortVal.V)
:=
  map (fun x => Store_ x name value) l.

(** %\begin{definition}[get\_count [port variable](Coq)]
TBD XXX this is wrong, get\_count is changed when we do a next\_value
  \end{definition} %*)

Definition Get_Count (l : list port_variable) (name : identifier) :=
  let pv := Get_Port_Variable_By_Name l name in
    match pv with
      | None => 0%nat
      | Some p => PortQueue.count p.(inner_variable)
    end.

(** %\begin{definition}[get\_value [port variable](Coq)]
TBD
  \end{definition} %*)

Definition Get_Value (l : list port_variable) (name : identifier) :=
  let pv := Get_Port_Variable_By_Name l name in
    match pv with
      | None => PortQueue.Invalid_Value
      | Some p => PortQueue.peek p.(inner_variable)
    end.

(** %\begin{definition}[next\_value [port variable](Coq)]
TBD
  \end{definition} %*)

Definition Next_Value_ (p : port_variable) (name : identifier) :=
  if identifier_beq (projectionFeatureIdentifier p.(port)) name
    && negb p.(is_data)
  then
    Update_Inner_Variable p (PortQueue.deq p.(inner_variable))
  else
    p.

Definition Next_Value (l : list port_variable) (name : identifier) :=
  map (fun x => Next_Value_ x name) l.

(** %\begin{definition}[receive\_input [port variable](Coq)]
TBD
  \end{definition} %*)

(* XXX add timestamp *)

Definition Receive_Input_OneItem (p : port_variable) :=
  let v := PortQueue.peek p.(outer_variable) in
    {|
    port := p.(port);
    is_data := p.(is_data);
    inner_variable := PortQueue.enq p.(inner_variable) v;
    outer_variable := PortQueue.deq p.(outer_variable);
    port_input_times := p.(port_input_times);
    urgency := p.(urgency);
    size := p.(size);
    overflow_handling_protocol := p.(overflow_handling_protocol);
    dequeue_protocol := p.(dequeue_protocol);
    dequeued_items := p.(dequeued_items);
|}.

Definition Receive_Input_AllItems (p : port_variable):= {|
  port := p.(port);
  is_data := p.(is_data);
  inner_variable := p.(outer_variable);
  outer_variable := [];
  port_input_times := p.(port_input_times);
  urgency := p.(urgency);
  size := p.(size);
  overflow_handling_protocol := p.(overflow_handling_protocol);
  dequeue_protocol := p.(dequeue_protocol);
  dequeued_items := p.(dequeued_items);
|}.

Definition Receive_Input__ (p : port_variable) :=
  match p.(dequeue_protocol) with
  | OneItem => Receive_Input_OneItem p
  | AllItems => Receive_Input_AllItems p
  | _ => Receive_Input_OneItem p
  end.

Definition Receive_Input_ (p : port_variable) (name : identifier) :=
  if identifier_beq (projectionFeatureIdentifier p.(port)) name then
    Receive_Input__ p
  else
    p.

Definition Receive_Input (l : list port_variable) (name : identifier) :=
  map (fun x => Receive_Input_ x name) l.

(** %\begin{definition}[send\_output [port variable](Coq)]
TBD
  \end{definition} %*)

Definition Send_Output_ (p : port_variable) (name : identifier) :=
  if identifier_beq (projectionFeatureIdentifier p.(port)) name
  then {|
    port := p.(port);
    is_data := p.(is_data);
    inner_variable := [];
    outer_variable := p.(inner_variable);
    port_input_times := p.(port_input_times);
    urgency := p.(urgency);
    size := p.(size);
    overflow_handling_protocol := p.(overflow_handling_protocol);
    dequeue_protocol := p.(dequeue_protocol);
    dequeued_items := p.(dequeued_items);
  |}
  else
    p.

  Definition Send_Output (l : list port_variable) (name : identifier) :=
    map (fun x => Send_Output_ x name) l.

(*| .. coq:: none |*)
End Port_Variable_RTS.
(*| .. coq:: |*)
