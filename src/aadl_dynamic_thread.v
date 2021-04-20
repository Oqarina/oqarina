(** %\section{Threads} %*)

(* begin hide *)
(** Coq Library *)
Require Import List.
Import ListNotations. (* from List *)
Require Import Coq.Bool.Bool.
Require Import Coq.Bool.Sumbool.
Require Import Coq.Arith.PeanoNat.

(** AADL library *)
Require Import identifiers.
Require Import aadl.
Require Import time.
Require Import queue.
Require Import utils.
Require Import aadl_declarative.
Require Import aadl_thread_properties.
Require Import aadl_communication_properties.
Require Import aadl_aadl_project.
Require Import aadl_feature_helper.

(* end hide *)

(** ** Port Variable *)

(**
Port variable maps AADL features to runtime level entities. Since we use Coq to define the dynamic semantics of AADL, it is also reasonnable to define the concept of port variable and use it to capture further the dynamic semantics of AADL threads.

 %\paragraph{}\define{Port Variable (AADLv2.2 \S 8.2)}{Port Variable (AADL)}{A port variable captures the feature at runtime. It implements runtime services to interact with the feature.}%

A port variable is captured using a Coq record. We define the concept of invalid port variable and a constructor for this record.
*)

Definition Port_Queue : Type := ListQueue.queue.


(* begin hide *)
Section Port_Variable.
(* end hide *)

  Record port_variable : Type := {
    port : feature;
    variable : Port_Queue;
    port_input_times : input_time;
    urgency : nat;
  }.

  Lemma port_variable_eq_dec : forall x y : port_variable, {x=y}+{x<>y}.
  Proof.
    decide equality.
    apply PeanoNat.Nat.eq_dec.
    apply input_time_eq_dec.
    apply list_eq_dec; apply PeanoNat.Nat.eq_dec.
    apply feature_eq_dec.
  Qed.

  Definition mkPortVariable (f : feature) := {|
    port := f;
    variable := [];
    port_input_times := Input_Time [ Default_IO_Time_Spec ]; (* XXX default value to change*)
    urgency := 0;
  |}.

  Definition Invalid_Port_Variable := mkPortVariable Invalid_Feature.

  Definition Update_Variable (p : port_variable) (v : Port_Queue): port_variable := {|
    port := p.(port);
    variable := v;
    port_input_times := p.( port_input_times);
    urgency := p.(urgency);
  |}.

(** [Build_Input_Port_Variables] (resp. [Build_Output_Port_Variables]) is a utility functions that builds port variables from input (resp. output) features. \change{what about inout?} *)

  Definition Build_Input_Port_Variables (l : list feature) :=
    map mkPortVariable (Get_Input_Features l).

  Definition Build_Output_Port_Variables (l : list feature) :=
    map mkPortVariable (Get_Output_Features l).

(* begin hide *)
End Port_Variable.
(* end hide *)

(** ** Thread State Variable *)

(** Each AADL thread is associated to a state variable that stores the relevant parameters relative to is dispatch and scheduling by the underlying executive. *)

(* begin hide*)
Section Thread_State_Variable.
(* end hide *)
(** [Build_Dispatch_Trigger] returns the list of triggering features *)

  Definition Build_Dispatch_Trigger (l : list feature) :=
    filter Is_Triggering_Feature l. (* %\change{should use also property Dispatch\_Trigger}% *)

(** %\begin{definition}[Thread State (Coq)]
TBD
  \end{definition} %*)

  Record thread_state_variable : Type := {
    dispatch_protocol : Dispatch_Protocol;
    period : AADL_Time;
  (*  deadline : AADL_Time;
    wcet : AADL_Time; *)
    priority : nat;
    clock : AADL_Time;
    input_ports : list port_variable;
    output_ports : list port_variable;
    dispatch_trigger : list feature;
  }.

  Definition mk_thread_state_variable (t : component) : thread_state_variable := {|
    dispatch_protocol := Map_Scheduling_Protocol (t->properties);
    period := Map_Period (t->properties);
    priority := Map_Priority (t->properties);
    clock := 0;
    input_ports := Build_Input_Port_Variables (t->features);
    output_ports := Build_Output_Port_Variables (t->features);
    dispatch_trigger := Build_Dispatch_Trigger (t->features);
  |}.

(* begin hide *)
End Thread_State_Variable.
(* end hide*)

(** ** Thread Dispatching

This section captures the content of %\S 5.4.2 of  \cite{as2-cArchitectureAnalysisDesign2017}%. Ultimately, we want to provide a definition of the [Enabled] function that controls the dispatch of a thread. The definition of this function relies on the state of some of its triggering features. In the following, we use directly the concept of thread state variable and port variables to define the [Enabled] function. *)

(* begin hide *)
Section AADL_Dispatching.
(* end hide *)

(** *** Intermediate Predicates

Most dispatch protocols review the state of triggering features. We build the [Thread_Has_Activated_Triggering_Feature] predicate as a conjunction of more basic predicates, either in [Prop] or [bool]. First, we check whether the feature is activated, [Is_Feature_Activiated], then whether it is in the dispatch trigger, in [Feature_In_Dispatch_Trigger]. *)

  Definition Is_Feature_Activated_b (p : port_variable) :=
    negb (ListQueue.is_empty p.(variable)).

  Definition Is_Feature_Activated (p : port_variable) :=
    p.(variable) <> nil.

  Definition Feature_In_Dispatch_Trigger (p : port_variable) (d : list feature) :=
    In p.(port) d.

  Fixpoint Feature_In_Dispatch_Trigger_b (p : port_variable) (d : list feature) :=
    match d with
    | nil => false
    | h :: t => (eqb feature_eq_dec (p.(port)) h) || Feature_In_Dispatch_Trigger_b p t
    end.

  Definition Has_Activated_Triggering_Feature
    (l : list port_variable) (d : list feature) : Prop :=
    exists p, In p l -> Is_Feature_Activated p  /\ Feature_In_Dispatch_Trigger p d.

  Definition Is_Activated_Triggering_Feature_b (p : port_variable) (d : list feature) :=
    Is_Feature_Activated_b p && Feature_In_Dispatch_Trigger_b p d.

  Fixpoint Has_Activated_Triggering_Feature_b (l : list port_variable) (d : list feature) :=
    match l with
    | nil => false
    | h :: t => (Is_Activated_Triggering_Feature_b h d ) ||
                (Has_Activated_Triggering_Feature_b t d)
    end.

  Definition Thread_Has_Activated_Triggering_Feature (th : thread_state_variable) :=
    Has_Activated_Triggering_Feature_b th.(input_ports) th.(dispatch_trigger).

(** *** Definition of [Enabled]

From the previous definitions, we can now define the [Enabled] function that returns [true] when a thread is dispatched.  *)

  Definition Periodic_Enabled (th : thread_state_variable) :=
    (th.(clock) mod th.(period)) =? 0.

  Definition Aperiodic_Enabled (th : thread_state_variable) :=
    Thread_Has_Activated_Triggering_Feature th.

  Definition Sporadic_Enabled (th : thread_state_variable) :=
    (th.(period) <=? th.(clock)) &&
     Thread_Has_Activated_Triggering_Feature th.

  Definition Timed_Enabled (th : thread_state_variable) :=
    (th.(period) =? th.(clock)) ||
    Thread_Has_Activated_Triggering_Feature th.

  Definition Hybrid_Enabled (th : thread_state_variable) :=
    (th.(period) =? th.(clock)) ||
    Thread_Has_Activated_Triggering_Feature th.

  Definition Background_Enabled (th : thread_state_variable) :=
    true.

  Definition Enabled (th : thread_state_variable) :=
    match th.(dispatch_protocol) with
    | Periodic => Periodic_Enabled th
    | Sporadic => Sporadic_Enabled th
    | Aperiodic => Aperiodic_Enabled th
    | Timed => Timed_Enabled th
    | Hybrid => Hybrid_Enabled th
    | Background => Background_Enabled th
    | Unspecified => false
    end.

(* begin hide *)
End AADL_Dispatching.
(* end hide *)

(** ** Ports Queue Processing *)

(**  The following is a first cut at formalizing ports from %\S 8.3%. We capture the definition of [Frozen] for ports. *)

(** [Activated_Triggering_Features] returns the list of all Activated_Trigger_Features *)

Definition Activated_Triggering_Features (th : thread_state_variable): list port_variable :=
  filter (fun l => Is_Activated_Triggering_Feature_b l th.(dispatch_trigger))
     th.(input_ports).

(** see %\S 8.3 (32)% XXX We should also address the FIFO for ports with same urgency .. *)

Fixpoint Get_Port_Variable_With_Max_Urgency (p : port_variable) (l : list port_variable) :=
  match l with
  | nil => p
  | h :: t => if p.(urgency) <=? h.(urgency) then
      Get_Port_Variable_With_Max_Urgency h t else
      Get_Port_Variable_With_Max_Urgency p t
    (* note we take h in all cases, this is to address the case where the
       first argument is [Invalid_Feature] *)
  end.

(** From that, we can define the [Get_Elected_Triggering_Feature] that returns the elected features among Triggering Features that have been activated. XXX must define this concept in the standard. *)

Definition Get_Elected_Triggering_Feature (th : thread_state_variable) : port_variable :=
  Get_Port_Variable_With_Max_Urgency Invalid_Port_Variable
      (Activated_Triggering_Features th).

(** Not even sure this is enough. For the moment, a port is frozen iff. the corresponding Input_Time is dispatch. We also make the assumption this is the only one IO_Time_Spec given, probably too strong ...*)

Definition Frozen (p : port_variable) (th : thread_state_variable) :=
match (hd Default_IO_Time_Spec (projectionIO_Time_Spec p.(port_input_times))) with
| Dispatch => (p = Get_Elected_Triggering_Feature  th) \/
              ~ (Feature_In_Dispatch_Trigger p th.(dispatch_trigger))
| NoIo => False
| Start _ => False
| Completion _ => False
end.

(** ** Runtime support for threads *)

(* begin hide *)
Section Thread_RTS.
(* end hide *)

(** A collection of runtime services is provided. A runtime service manipulates the thread state and its assocoated port variable *)

(** %\define{Advance time (Coq)}{advance\_time (Coq)}
{TBD}
   %*)

  Definition advance_time (t : thread_state_variable) (tt : AADL_Time): thread_state_variable := {|
    dispatch_protocol := t.(dispatch_protocol);
    period := t.(period);
    priority := t.(priority);
    clock := t.(clock) + tt;
    input_ports := t.(input_ports);
    output_ports := t.(output_ports);
    dispatch_trigger := t.(dispatch_trigger);
  |}.

(** %\begin{definition}[store\_in (Coq)]
TBD
  \end{definition} %*)

  Definition Store_In_ (p : port_variable) (name : identifier) (value : nat) :=
    if identifier_beq (projectionFeatureIdentifier p.(port)) name then
      Update_Variable p (ListQueue.enq p.(variable) value)
    else
      p.

  Fixpoint Store_In (l : list port_variable) (name : identifier) (value : nat) :=
    match l with
    | nil => l
    | h :: t => Store_In_ h name value :: Store_In t name value
    end.

  Definition store_in (t : thread_state_variable) (name : identifier) (value : nat) : thread_state_variable := {|
    dispatch_protocol := t.(dispatch_protocol);
    period := t.(period);
    priority := t.(priority);
    clock := t.(clock);
    input_ports := Store_In t.(input_ports) name value;
    output_ports := t.(output_ports);
    dispatch_trigger := t.(dispatch_trigger);
  |}.

(* begin hide *)
End Thread_RTS.
(* end hide *)

(** ** Examples *)

(** *** A Periodic Thread *)

Definition Periodic_Dispatch :=
  Property_Value Scheduling_Protocol (aadlenum (Ident "periodic")).

Definition A_Priority_Value :=
    Property_Value Priority (aadlinteger 42).

Definition A_Period :=
    Property_Value Period (aadlinteger 3).

Definition A_Periodic_Thread := Component
  (Ident "a_periodic_thread")
  (thread)
  (Ident "a_periodic_thread_classifier")
  nil
  nil
  [A_Priority_Value ; Periodic_Dispatch ; A_Period ] nil.

Eval compute in mk_thread_state_variable (A_Periodic_Thread).

Definition A_Periodic_Thread_State := mk_thread_state_variable (A_Periodic_Thread).

Eval compute in Enabled (A_Periodic_Thread_State).

Definition A_Periodic_Thread_State' := advance_time A_Periodic_Thread_State 4.

Eval compute in Enabled (A_Periodic_Thread_State').

(** *** A Sporadic Thread*)

Definition Sporadic_Dispatch :=
  Property_Value Scheduling_Protocol (aadlenum (Ident "sporadic")).

Definition An_Input_Feature :=
  Feature (Ident "a_feature") inF eventPort nil_component nil.

Definition A_Sporadic_Thread := Component
  (Ident "a_sporadic_thread")
  (thread)
  (Ident "a_sporadic_thread_classifier")
  [ An_Input_Feature ]
  nil
  [A_Priority_Value ; Sporadic_Dispatch ; A_Period ]
  nil.

(** We can continue a build a sporadic thread, add an event, avancd time and check it is enabled *)

Eval compute in mk_thread_state_variable (A_Sporadic_Thread).

Definition A_Sporadic_Thread_State := mk_thread_state_variable (A_Sporadic_Thread).

Eval compute in Enabled (A_Sporadic_Thread_State).

Definition A_Sporadic_Thread_State' := store_in A_Sporadic_Thread_State (Ident "a_feature") 42.
Compute A_Sporadic_Thread_State'.

Eval compute in Enabled (A_Sporadic_Thread_State').

Eval compute in Enabled (advance_time A_Sporadic_Thread_State' 32).

Compute advance_time A_Sporadic_Thread_State' 32.

Definition th := advance_time A_Sporadic_Thread_State' 32.

Eval compute in Get_Elected_Triggering_Feature (th).
