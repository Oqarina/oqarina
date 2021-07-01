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
Require Import Coq.ZArith.ZArith.

(** Oqarina library *)
Require Import Oqarina.coq_utils.utils.

Require Import Oqarina.core.identifiers.
Require Import Oqarina.core.time.
Require Import Oqarina.core.queue.
Require Import Oqarina.properties.properties.

Require Import Oqarina.aadl_categories.
Require Import Oqarina.aadl.
Require Import Oqarina.aadl_declarative.

Require Import Oqarina.property_sets.all.

Require Import Oqarina.aadl_port_variable.
Require Import Oqarina.aadl_feature_helper.

Open Scope Z_scope.
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
    deadline : AADL_Time;
   (* wcet : AADL_Time; *)
    priority : Z;
    clock : AADL_Time;
    input_ports : list port_variable;
    output_ports : list port_variable;

    dispatch_trigger : list feature;
  }.

  Definition mk_thread_state_variable (t : component) : thread_state_variable := {|
    dispatch_protocol := Map_Scheduling_Protocol (t->properties);
    period := Map_Period (t->properties);
    priority := Map_Priority (t->properties);
    deadline := Map_Deadline (t->properties);
    clock := 0;

    input_ports := Build_Input_Port_Variables (t->features);
    output_ports := Build_Output_Port_Variables (t->features);

    dispatch_trigger := Build_Dispatch_Trigger (t->features);
  |}.

(* begin hide *)
End Thread_State_Variable.
(* end hide*)

(** ** Thread Dispatching

This section captures the content of %\S 5.4.2 of \cite{as2-cArchitectureAnalysisDesign2017}%. Ultimately, we want to provide a definition of the [Enabled] function that controls the dispatch of a thread. The definition of this function relies on the state of some of its triggering features. In the following, we use directly the concept of thread state variable and port variables to define the [Enabled] function. *)

(* begin hide *)
Section AADL_Dispatching.
(* end hide *)

(** *** Intermediate Predicates

All AADL dispatch protocols review the state of triggering features and the current clock. We build the [Thread_Has_Activated_Triggering_Feature] predicate as a conjunction of more basic predicates, in [Prop], and demonstrate their decidability.

First, we check whether the feature is activated, [Is_Feature_Activated], then whether it is in the dispatch trigger, in [Feature_In_Dispatch_Trigger]. *)

  Definition Is_Feature_Activated (p : port_variable) :=
    ~ PortQueue.Is_Empty p.(outer_variable).

  (* begin hide *)
  Lemma Is_Feature_Activated_dec :
    forall (p : port_variable), dec_sumbool (Is_Feature_Activated p).
  Proof.
    intros.
    unfold dec_sumbool.
    unfold Is_Feature_Activated.
    apply dec_sumbool_not.
    apply PortQueue.Is_Empty_dec.
  Defined.
  (* end hide *)

  Definition Feature_In_Dispatch_Trigger (p : port_variable) (d : list feature) :=
    In p.(port) d.

  (* begin hide *)
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
  (* end hide *)

  (** From that point, we can build [Thread_Has_Activated_Triggering_Feature] that is true iff. the thread has at least one activated triggering feature that is also in the dispatch trigger. *)

  Definition Is_Activated_Triggering_Feature (p : port_variable)  (d : list feature) :=
    Is_Feature_Activated p /\ Feature_In_Dispatch_Trigger p d.

  (* begin hide *)
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
  (* end hide *)

  Definition Has_Activated_Triggering_Feature (l : list port_variable) (d : list feature) :=
    All_Or (fun x => (Is_Activated_Triggering_Feature x d)) l.

  (* begin hide *)
  Lemma Has_Activated_Triggering_Feature_dec :
    forall (l : list port_variable) (d : list feature),
      dec_sumbool (Has_Activated_Triggering_Feature l d).
  Proof.
    intros.
    unfold dec_sumbool.
    unfold Has_Activated_Triggering_Feature.
    induction l.
    - auto.
    - unfold All_Or. apply dec_sumbool_or.
      * apply Is_Activated_Triggering_Feature_dec.
      * apply IHl.
  Defined.
  (* end hide *)

  Definition Thread_Has_Activated_Triggering_Feature (th : thread_state_variable) :=
    Has_Activated_Triggering_Feature
      th.(input_ports) th.(dispatch_trigger).

  (* begin hide *)
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
(* end hide *)

(** *** Definition of [Enabled]

From the previous definitions, we can now define the [Enabled] function that returns [true] when a thread is dispatched. First, we define basic predicates for each dispatch protocol.*)

  Definition Periodic_Enabled (th : thread_state_variable) :=
    th.(clock) mod th.(period) = 0.

  (* begin hide *)
  Lemma Periodic_Enabled_dec:
    forall (th : thread_state_variable), dec_sumbool (Periodic_Enabled th).
  Proof.
    unfold dec_sumbool.
    unfold Periodic_Enabled.
    intros.
    apply Z.eq_dec.
  Defined.
  (* end hide *)

  Definition Aperiodic_Enabled (th : thread_state_variable) :=
    Thread_Has_Activated_Triggering_Feature th.

  (* begin hide *)
  Lemma Aperiodic_Enabled_dec:
    forall (th : thread_state_variable), dec_sumbool (Aperiodic_Enabled th).
  Proof.
    unfold dec_sumbool.
    unfold Aperiodic_Enabled.
    intros.
    apply Thread_Has_Activated_Triggering_Feature_dec.
  Defined.
  (* end hide *)

  Definition Sporadic_Enabled (th : thread_state_variable) :=
    th.(period) <= th.(clock) /\
     Thread_Has_Activated_Triggering_Feature th.

  (* begin hide *)
  Lemma Sporadic_Enabled_dec:
    forall (th : thread_state_variable), dec_sumbool (Sporadic_Enabled th).
  Proof.
    unfold dec_sumbool.
    unfold Sporadic_Enabled.
    intros.
    apply dec_sumbool_and.
    apply Z_le_dec. (* {period th <= clock th} + {~ period th <= clock th} *)
    apply Thread_Has_Activated_Triggering_Feature_dec.
  Defined.
  (* end hide *)

  Definition Timed_Enabled (th : thread_state_variable) :=
    (th.(period) = th.(clock)) \/
    Thread_Has_Activated_Triggering_Feature th.

  (* begin hide *)
  Lemma Timed_Enabled_dec:
    forall (th : thread_state_variable), dec_sumbool (Timed_Enabled th).
  Proof.
    unfold dec_sumbool.
    unfold Timed_Enabled.
    intros.
    apply dec_sumbool_or.
    apply Z.eq_dec.
    apply Thread_Has_Activated_Triggering_Feature_dec.
  Defined.
  (* end hide *)

  Definition Hybrid_Enabled (th : thread_state_variable) :=
    (th.(period) = th.(clock)) /\
    Thread_Has_Activated_Triggering_Feature th.

  (* begin hide *)
  Lemma Hybrid_Enabled_dec:
    forall (th : thread_state_variable), dec_sumbool (Hybrid_Enabled th).
  Proof.
    unfold dec_sumbool.
    unfold Hybrid_Enabled.
    intros.
    apply dec_sumbool_and.
    apply Z.eq_dec.
    apply Thread_Has_Activated_Triggering_Feature_dec.
  Defined.
  (* end hide *)

  Definition Background_Enabled (th : thread_state_variable) :=
    True.

  (* begin hide *)
  Lemma Background_Enabled_dec:
    forall (th : thread_state_variable), dec_sumbool (Background_Enabled th).
  Proof.
    unfold dec_sumbool.
    unfold Background_Enabled.
    auto.
  Defined.
  (* end hide *)

  (** Then we define the [Enabled] predicate *)

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

  (* begin hide *)
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
  (* end hide *)

  (** [Enabled_oracle] return a [bool] as a witness, for debugging purposes. *)

  Definition Enabled_oracle (th : thread_state_variable) :=
    Oracle (Enabled_dec th).

(* begin hide *)
End AADL_Dispatching.
(* end hide *)

(** ** Ports Queue Processing *)

(**  The following is a first cut at formalizing ports from %\S 8.3%. We capture the definition of [Frozen] for ports. First, we build ATF, the list of Activated Triggering Features. *)

(** [Activated_Triggering_Features] returns the list of Activated Triggering Features. *)

Definition Activated_Triggering_Features'  (l : list port_variable) (d : list feature) :=
  filter (fun x => Oracle (Is_Activated_Triggering_Feature_dec x d) ) l.

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
        first argument is [Invalid_Port_Variable] *)
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

(* begin hide *)
Definition Dispatch_Frozen_dec:
  forall p th, { Dispatch_Frozen p th } + { ~ Dispatch_Frozen p th }.
Proof.
  intros.
  unfold Dispatch_Frozen.
  apply dec_sumbool_or.
  apply port_variable_eq_dec.
  apply dec_sumbool_not.
  apply Feature_In_Dispatch_Trigger_dec.
Defined.
(* end hide *)

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

(** %\define{advance\_time (Coq)}{advance\_time (Coq)}
{$advance\_time(th, t)$ increments the clock of the thread state variable:\\
  $$\infer[advance\_time(th, t)]{th() \rightarrow th (clock \leftarrow clock + t)}{th, t \geq 0}$$
}
   %*)

  Definition advance_time (th : thread_state_variable) (t : AADL_Time) := {|
      (* Generic part *)
      dispatch_protocol := th.(dispatch_protocol);
      period := th.(period);
      deadline := th.(deadline);
      priority := th.(priority);

      input_ports := th.(input_ports);
      output_ports := th.(output_ports);
      dispatch_trigger := th.(dispatch_trigger);

      (* advance_time *)
      clock := th.(clock) + t;
    |}.

(** %\begin{definition}[store\_in (Coq)]
This private API function stores a value in an outer\_port of an AADL thread.
  \end{definition} %*)

  Definition store_in (t : thread_state_variable) (name : identifier) (value : bool) := {|
    (* Generic part *)
    dispatch_protocol := t.(dispatch_protocol);
    period := t.(period);
    deadline := t.(deadline);
    priority := t.(priority);
    clock := t.(clock);
    output_ports := t.(output_ports);
    dispatch_trigger := t.(dispatch_trigger);

    (* store_in *)
    input_ports := Store t.(input_ports) name (t.(clock), value);

  |}.

(** %\begin{definition}[Get\_Count (Coq)]
    subprogram Get\_Count
    features
      Portvariable: requires data access; -- reference to port variable
      CountValue: out parameter Base\_Types::Integer; -- content count of port variable
    end Get\_Count;

  \end{definition} %*)

  Definition get_count (t : thread_state_variable) (name : identifier) :=
    Get_Count t.(input_ports) name.

(** %\begin{definition}[Put\_Value (Coq)]
    subprogram Put\_Value
    features
      Portvariable: requires data access; -- reference to port variable
      DataValue: in parameter; -- value to be stored
      DataSize: in parameter;  - size in bytes (optional)
    end Put\_Value;
  \end{definition} %*)

  Definition put_value (t : thread_state_variable) (name : identifier) (value : bool) := {|
    (* Generic part *)
    dispatch_protocol := t.(dispatch_protocol);
    period := t.(period);
    deadline := t.(deadline);
    priority := t.(priority);
    clock := t.(clock);
    input_ports := t.(input_ports);
    dispatch_trigger := t.(dispatch_trigger);

    (* put_value *)
    output_ports := Store t.(output_ports) name (t.(clock), value);

  |}.

(** %\begin{definition}[Get\_Value (Coq)]
  subprogram Get\_Value
  features
    Portvariable: requires data access; -- reference to port variable
    DataValue: out parameter; -- value being retrieved
       -- Error code
      ErrorCode: out parameter <implementation-defined error code>;
  end Get\_Value;
  \end{definition} %*)

  Definition get_value (t : thread_state_variable) (name : identifier) :=
    Get_Value t.(input_ports) name.

  (** %\begin{definition}[Next\_Value (Coq)]
  subprogram Next\_Value
  features
    Portvariable: requires data access; -- reference to port variable
       -- Error code
      ErrorCode: out parameter <implementation-defined error code>;
  end Next\_Value;
  \end{definition} %*)

  Definition next_value (t : thread_state_variable) (name : identifier) (value : bool) := {|
    (* Generic part *)
    dispatch_protocol := t.(dispatch_protocol);
    period := t.(period);
    deadline := t.(deadline);
    priority := t.(priority);
    clock := t.(clock);
    output_ports := t.(output_ports);
    dispatch_trigger := t.(dispatch_trigger);

    (* next_value *)
    input_ports := Next_Value t.(input_ports) name;

  |}.

  Definition receive_input (t : thread_state_variable) (name : identifier) := {|
    (* Generic part *)
    dispatch_protocol := t.(dispatch_protocol);
    period := t.(period);
    deadline := t.(deadline);
    priority := t.(priority);
    clock := t.(clock);
    output_ports := t.(output_ports);
    dispatch_trigger := t.(dispatch_trigger);

    (* next_value *)
    input_ports := Receive_Input t.(input_ports) name;

  |}.

(* begin hide *)
End Thread_RTS.
(* end hide *)

(** ** Examples *)

(** *** A Periodic Thread *)

Definition Periodic_Dispatch := {|
  PT := PT_TypeRef (Dispatch_Protocol_Name);
  PV := PV_Enum (Id "periodic");
|}.

Definition A_Priority_Value := {|
  PT := PT_TypeRef (Priority_Name);
  PV := PV_Int 42;
|}.

Definition A_Period := {|
  PT := PT_TypeRef (Period_Name);
  PV := PV_IntU 3 (PV_Unit (Id "ms"));
|}.

Definition A_Periodic_Thread := Component
  (Id "a_periodic_thread")
  (thread)
  (Id "a_periodic_thread_classifier")
  nil
  nil
  [A_Priority_Value ; Periodic_Dispatch ; A_Period ] nil.

Definition A_Periodic_Thread_State := mk_thread_state_variable (A_Periodic_Thread).

(** At t = 0, the periodic thread is enabled *)
Lemma Periodic_t0_enabled : Enabled_oracle (A_Periodic_Thread_State) = true.
Proof.
  trivial.
Qed.

Definition A_Periodic_Thread_State' := advance_time A_Periodic_Thread_State 4.

(** At t = 4, the periodic thread is not enabled *)
Lemma Periodic_t4_not_enabled : Enabled_oracle (A_Periodic_Thread_State') = false.
Proof.
  trivial.
Qed.

(** *** A Sporadic Thread*)

Definition Sporadic_Dispatch  := {|
  PT := PT_TypeRef (Dispatch_Protocol_Name);
  PV := PV_Enum (Id "sporadic");
|}.

Definition An_Input_Feature :=
  Feature (Id "a_feature") inF eventPort nil_component nil.

Definition A_Sporadic_Thread := Component
  (Id "a_sporadic_thread")
  (thread)
  (Id "a_sporadic_thread_classifier")
  [ An_Input_Feature ]
  nil
  [A_Priority_Value ; Sporadic_Dispatch ; A_Period ]
  nil.

(** We can continue ant build a sporadic thread, add an event, avancd time and check if it is enabled *)

Definition A_Sporadic_Thread_State := mk_thread_state_variable (A_Sporadic_Thread).

(** initially, the sporadic thread is not enabled *)
Lemma Sporatic_tO_not_enabled : Enabled_oracle (A_Sporadic_Thread_State) = false.
Proof.
  trivial.
Qed.

(** inject en event *)
Definition A_Sporadic_Thread_State_ := store_in A_Sporadic_Thread_State (Id "a_feature") false.
Definition A_Sporadic_Thread_State' := store_in A_Sporadic_Thread_State_ (Id "a_feature") true.

Compute A_Sporadic_Thread_State_.
Compute A_Sporadic_Thread_State'.

(** the thread is not enabled yet *)
Lemma Sporatic_tO_not_enabled' : Enabled_oracle (A_Sporadic_Thread_State') = false.
Proof.
  trivial.
Qed.

(** we advance time *)
Definition th := advance_time A_Sporadic_Thread_State' 32.

(** the thread is enabled, and we can check frozen port *)
Lemma Sporadic_t42_enabled : Enabled_oracle th = true.
Proof.
  trivial.
Qed.

Lemma ETF: Get_Port_Variable_Name (Get_Elected_Triggering_Feature (th)) = Id "a_feature".
Proof.
  trivial.
Qed.

Compute Frozen_Ports' (th).

(* at this stage, we have not called receive_input, no event available *)
Lemma get_count_1 : get_count th (Id "a_feature") = 0%nat.
Proof.
  trivial.
Qed.

(* calling receive input *)
Definition th_rec := receive_input th (Id "a_feature").

Lemma get_count_2 : get_count th_rec (Id "a_feature") = 1%nat.
Proof.
  trivial.
Qed.

Lemma get_value_1 : get_value th_rec (Id "a_feature") = (0,true).
Proof.
  trivial.
Qed.
