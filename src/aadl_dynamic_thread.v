(** %\section{Threads} %*)

(* begin hide *)
(** Coq Library *)
Require Import List.
Import ListNotations. (* from List *)
Require Import Coq.Bool.Bool.
Require Import Coq.Bool.Sumbool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Bool.Bool.

(** AADL library *)
Require Import utils.
(*Require Import hlist. *)
Require Import identifiers.
Require Import aadl.
Require Import time.
Require Import queue.
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

A port variable is captured using a Coq record. We define the concept of invalid port variable and a constructor for this record, along with the well-formedness rule and decidability result.
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
    apply list_eq_dec; apply bool_dec.
    apply feature_eq_dec.
  Defined.

  Definition mkPortVariable (f : feature) := {|
    port := f;
    variable := [];
    port_input_times := Input_Time [ Default_IO_Time_Spec ]; (* XXX default value to change*)
    urgency := 0;
  |}.

  Definition port_variable_wf (p : port_variable) :=
    input_time_wf p.(port_input_times).

  Definition port_variable_wf_dec : forall p : port_variable,
    dec_sumbool (port_variable_wf p).
  Proof.
    intros.
    unfold port_variable_wf.
    destruct port_input_times.
    apply input_time_wf_dec.
  Defined.

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

Most dispatch protocols review the state of triggering features. We build the [Thread_Has_Activated_Triggering_Feature] predicate as a conjunction of more basic predicates,  in [Prop], and demonstrate their decidability.

First, we check whether the feature is activated, [Is_Feature_Activiated], then whether it is in the dispatch trigger, in [Feature_In_Dispatch_Trigger]. *)

  Definition Is_Feature_Activated (p : port_variable) :=
    ~ ListQueue.Is_Empty p.(variable).

  Lemma Is_Feature_Activated_dec :
    forall (p : port_variable), dec_sumbool (Is_Feature_Activated p).
  Proof.
    intros.
    unfold dec_sumbool.
    unfold Is_Feature_Activated.
    apply dec_sumbool_not.
    apply ListQueue.Is_Empty_dec.
  Defined.

  Definition Feature_In_Dispatch_Trigger (p : port_variable) (d : list feature) :=
    In p.(port) d.

  Definition Feature_In_Dispatch_Trigger_dec :
    forall (p : port_variable) (d : list feature),
      dec_sumbool (Feature_In_Dispatch_Trigger p d).
  Proof.
    unfold Feature_In_Dispatch_Trigger.
    unfold dec_sumbool.
    intros.
    apply In_dec.
    apply feature_eq_dec.
  Defined.

  (** From that point, we can build [Thread_Has_Activated_Triggering_Feature] that is true iff. the thread has at least one activated triggering feature (predicate [Is_Activated_Triggering_Feature]). *)

  Definition Is_Activated_Triggering_Feature (p : port_variable)  (d : list feature) :=
    Is_Feature_Activated p /\ Feature_In_Dispatch_Trigger p d.

  Lemma Is_Activated_Triggering_Feature_dec:
    forall (p : port_variable)  (d : list feature),
      dec_sumbool (Is_Activated_Triggering_Feature p d).
  Proof.
    intros.
    unfold Is_Activated_Triggering_Feature.
    apply dec_sumbool_and.
    apply Is_Feature_Activated_dec.
    apply Feature_In_Dispatch_Trigger_dec.
  Defined.

  Fixpoint Has_Activated_Triggering_Feature (l : list port_variable) (d : list feature) :=
    match l with
      | nil => False
      | h :: t => Is_Activated_Triggering_Feature h d \/
                  Has_Activated_Triggering_Feature t d
    end.

  Lemma Has_Activated_Triggering_Feature_dec :
    forall (l : list port_variable) (d : list feature),
      dec_sumbool (Has_Activated_Triggering_Feature l d).
  Proof.
    intros.
    unfold dec_sumbool.
    unfold Has_Activated_Triggering_Feature.
    induction l.
    - auto.
    - apply dec_sumbool_or.
      * apply Is_Activated_Triggering_Feature_dec.
      * apply IHl.
  Defined.

  Definition Thread_Has_Activated_Triggering_Feature (th : thread_state_variable) :=
    Has_Activated_Triggering_Feature
      th.(input_ports) th.(dispatch_trigger).

  Lemma Thread_Has_Activated_Triggering_Feature_dec :
    forall (th : thread_state_variable),
      dec_sumbool (Thread_Has_Activated_Triggering_Feature th).
  Proof.
    unfold dec_sumbool.
    unfold Thread_Has_Activated_Triggering_Feature.
    unfold Has_Activated_Triggering_Feature.
    intros.
    apply Has_Activated_Triggering_Feature_dec.
  Defined.

(** *** Definition of [Enabled]

From the previous definitions, we can now define the [Enabled] function that returns [true] when a thread is dispatched.  *)

  Definition Periodic_Enabled (th : thread_state_variable) :=
    th.(clock) mod th.(period) = 0.

  Lemma Periodic_Enabled_dec:
    forall (th : thread_state_variable), dec_sumbool (Periodic_Enabled th).
  Proof.
    unfold dec_sumbool.
    unfold Periodic_Enabled.
    intros.
    apply PeanoNat.Nat.eq_dec.
  Defined.

  Definition Aperiodic_Enabled (th : thread_state_variable) :=
    Thread_Has_Activated_Triggering_Feature th.

  Lemma Aperiodic_Enabled_dec:
    forall (th : thread_state_variable), dec_sumbool (Aperiodic_Enabled th).
  Proof.
    unfold dec_sumbool.
    unfold Aperiodic_Enabled.
    intros.
    apply Thread_Has_Activated_Triggering_Feature_dec.
  Defined.

  Definition Sporadic_Enabled (th : thread_state_variable) :=
    th.(period) <= th.(clock) /\
     Thread_Has_Activated_Triggering_Feature th.

  Lemma Sporadic_Enabled_dec:
    forall (th : thread_state_variable), dec_sumbool (Sporadic_Enabled th).
  Proof.
    unfold dec_sumbool.
    unfold Sporadic_Enabled.
    intros.
    apply dec_sumbool_and.
    apply le_dec. (* {period th <= clock th} + {~ period th <= clock th} *)
    apply Thread_Has_Activated_Triggering_Feature_dec.
  Defined.

  Definition Timed_Enabled (th : thread_state_variable) :=
    (th.(period) = th.(clock)) \/
    Thread_Has_Activated_Triggering_Feature th.

  Lemma Timed_Enabled_dec:
    forall (th : thread_state_variable), dec_sumbool (Timed_Enabled th).
  Proof.
    unfold dec_sumbool.
    unfold Timed_Enabled.
    intros.
    apply dec_sumbool_or.
    apply PeanoNat.Nat.eq_dec.
    apply Thread_Has_Activated_Triggering_Feature_dec.
  Defined.

  Definition Hybrid_Enabled (th : thread_state_variable) :=
    (th.(period) = th.(clock)) /\
    Thread_Has_Activated_Triggering_Feature th.

  Lemma Hybrid_Enabled_dec:
    forall (th : thread_state_variable), dec_sumbool (Hybrid_Enabled th).
  Proof.
    unfold dec_sumbool.
    unfold Hybrid_Enabled.
    intros.
    apply dec_sumbool_and.
    apply PeanoNat.Nat.eq_dec.
    apply Thread_Has_Activated_Triggering_Feature_dec.
  Defined.

  Definition Background_Enabled (th : thread_state_variable) :=
    True.

  Lemma Background_Enabled_dec:
    forall (th : thread_state_variable), dec_sumbool (Background_Enabled th).
  Proof.
    unfold dec_sumbool.
    unfold Background_Enabled.
    auto.
  Defined.

  Definition Enabled (th : thread_state_variable) :=
    match th.(dispatch_protocol) with
    | Periodic => Periodic_Enabled th
    | Sporadic => Sporadic_Enabled th
    | Aperiodic => Aperiodic_Enabled th
    | Timed => Timed_Enabled th
    | Hybrid => Hybrid_Enabled th
    | Background => Background_Enabled th
    | Unspecified => False
    end.

  Lemma Enabled_dec: forall (th : thread_state_variable), dec_sumbool (Enabled th).
  Proof.
    unfold dec_sumbool.
    unfold Enabled.
    intros.
    destruct (dispatch_protocol th).
    auto.
    apply Periodic_Enabled_dec.
    apply Sporadic_Enabled_dec.
    apply Aperiodic_Enabled_dec.
    apply Background_Enabled_dec.
    apply Timed_Enabled_dec.
    apply Hybrid_Enabled_dec.
  Defined.

  (** [Enabled_oracle] return a [bool] as a witness, useful only for debugging purposes. *)
  Definition Enabled_oracle (th : thread_state_variable) :=
    if Enabled_dec th then true else false.

(* begin hide *)
End AADL_Dispatching.
(* end hide *)

(** ** Ports Queue Processing *)

(**  The following is a first cut at formalizing ports from %\S 8.3%. We capture the definition of [Frozen] for ports. *)

(** [Activated_Triggering_Features] returns the list of Activated Triggering Features. *)

Fixpoint Activated_Triggering_Features' (l : list port_variable) (d : list feature) :=
  match l with
  | nil => nil
  | h :: t => match Is_Activated_Triggering_Feature_dec h d with
                  | left _=> h :: (Activated_Triggering_Features' t d)
                  | right _ => Activated_Triggering_Features' t d
              end
  end.

Definition Activated_Triggering_Features (th : thread_state_variable) :=
  Activated_Triggering_Features' th.(input_ports) th.(dispatch_trigger).

(** [Get_Port_Variable_With_Max_Urgency] returns the port variable with the maximum urgency, see %\S 8.3 (32) \change{We should also address the FIFO for ports with same urgency .. }% *)

Fixpoint Get_Port_Variable_With_Max_Urgency
  (p : port_variable) (l : list port_variable) : port_variable :=
  match l with
  | nil => p
  | h :: t => if p.(urgency) <=? h.(urgency) then
      Get_Port_Variable_With_Max_Urgency h t else
      Get_Port_Variable_With_Max_Urgency p t
    (* note we take h in all cases, this is to address the case where the
       first argument is [Invalid_Feature] *)
  end.

(** Then, we can define the [Get_Elected_Triggering_Feature] that returns the elected features among Activated Triggering Features. XXX must define this concept in the standard. *)

Definition Get_Elected_Triggering_Feature (th : thread_state_variable) : port_variable :=
  Get_Port_Variable_With_Max_Urgency Invalid_Port_Variable
      (Activated_Triggering_Features th).

(** [Current_Valid_IO_Time_Spec] returns the current IO_Time_Spec for the considered port variable. A port variable can be associated with a list of IO_Time_Spec. The current IO_Time_Spec denotes the IO_Time_Spec that is current to the thread state. %\change{This version is highly simplified. We should define this in the standard first}% *)

Definition Current_Valid_IO_Time_Spec (p : port_variable) (th : thread_state_variable) :=
  hd Default_IO_Time_Spec (projectionIO_Time_Spec p.(port_input_times)).

(** The definition of the [Frozen] predicate relies on the previous definitions. A port variable is frozen based on the current thread state, the port IO_Time_Spec, etc.*)

Definition Dispatch_Frozen (p : port_variable) (th : thread_state_variable) : Prop :=
   (p = Get_Elected_Triggering_Feature  th) \/
       ~ (Feature_In_Dispatch_Trigger p th.(dispatch_trigger)).

Definition Dispatch_Frozen_dec: forall p th, { Dispatch_Frozen p th } + { ~ Dispatch_Frozen p th }.
Proof.
  intros.
  unfold Dispatch_Frozen.
  apply dec_sumbool_or.
  apply port_variable_eq_dec.
  apply dec_sumbool_not.
  apply Feature_In_Dispatch_Trigger_dec.
Defined.

Definition Frozen (p : port_variable) (th : thread_state_variable) : Prop :=
  match Current_Valid_IO_Time_Spec p th with
  | Dispatch => Dispatch_Frozen p th
  | NoIo => False
  | Start _ => False
  | Completion _ => False
  end.

Definition Frozen_Ports' (th : thread_state_variable): list port_variable :=
  filter_dec port_variable_wf port_variable_wf_dec th.(input_ports).

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

  Definition Store_In_ (p : port_variable) (name : identifier) (value : bool) :=
    if identifier_beq (projectionFeatureIdentifier p.(port)) name then
      Update_Variable p (ListQueue.enq p.(variable) value)
    else
      p.

  Fixpoint Store_In (l : list port_variable) (name : identifier) (value : bool) :=
    match l with
    | nil => l
    | h :: t => Store_In_ h name value :: Store_In t name value
    end.

  Definition store_in (t : thread_state_variable) (name : identifier) (value : bool) : thread_state_variable := {|
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

Definition A_Periodic_Thread_State := mk_thread_state_variable (A_Periodic_Thread).

(** At t = 0, the periodic thread is enabled *)
Compute Enabled_oracle (A_Periodic_Thread_State).
(*
	 = true
     : bool
*)

Definition A_Periodic_Thread_State' := advance_time A_Periodic_Thread_State 4.

(** At t = 4, the periodic thread is not enabled *)
Compute Enabled_oracle (A_Periodic_Thread_State').

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

(** We can continue ant build a sporadic thread, add an event, avancd time and check if it is enabled *)

Definition A_Sporadic_Thread_State := mk_thread_state_variable (A_Sporadic_Thread).

(** initially, the sporadic thread is not enabled *)
Eval vm_compute in Enabled_oracle (A_Sporadic_Thread_State).

(** inject en event *)
Definition A_Sporadic_Thread_State' := store_in A_Sporadic_Thread_State (Ident "a_feature") true.

(** the thread is not enabled yet *)
Compute Enabled_oracle (A_Sporadic_Thread_State').

(** we advance time *)
Definition th := advance_time A_Sporadic_Thread_State' 32.

(** the thread is enabled, and we can check frozen port *)
Compute Enabled_oracle th.
Compute Get_Elected_Triggering_Feature (th).
Compute Frozen_Ports' (th).

(*
Record Request : Type := {
  received_time : AADL_Time;
  payload : hlist;
}.

Definition mkRequest (t : AADL_Time) (T : Type) := {|
  received_time := t;
  payload := T;
|}.

*)