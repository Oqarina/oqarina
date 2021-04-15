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
(* end hide *)

(** % \subsection{Thread Dispatching}

The litterature on real-time scheduling proposes one canonical task model \cite{XXX}. The AADL core language supports this task model through a collection of properties. The dispatch of a thread is configured by several core properties:  \texttt{Dispatch\_Protocol}, \texttt{Priority}, \texttt{Period}, .
%

*)

(** *** Canonical task model as AADL model elements



*)
(* begin hide *)
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

(* end hide *)





Definition Thread_Time : Type := NaturalTime.Time.

(* begin hide *)
Section AADL_Dispatching.
(* end hide *)

Definition Port_Queue : Type := ListQueue.queue.

(** ** Mapping of ports *)

Definition Is_Input_Port (f : feature) :=
  (DirectionType_beq (projectionFeatureDirection f) inF) ||
  (DirectionType_beq (projectionFeatureDirection f) inoutF).

Definition Is_Triggerable_Port (f : feature) :=
  (FeatureCategory_beq (projectionFeatureCategory f) eventPort) ||
  (FeatureCategory_beq (projectionFeatureCategory f) eventDataPort) ||
  (FeatureCategory_beq (projectionFeatureCategory f) subprogramAccess) ||
  (FeatureCategory_beq (projectionFeatureCategory f) subprogramGroupAccess).

Definition Is_Triggerable_Port_p (f : feature) :=
  In (projectionFeatureCategory f) [ eventPort ; eventDataPort ;
                                     subprogramAccess ; subprogramGroupAccess].

Definition Is_Data_Port (f : feature) :=
  (projectionFeatureCategory f) = dataPort.

Definition Get_Input_Features (l : list feature) :=
  filter Is_Input_Port l.

(** ** Port variable *)

Inductive Dispatch_Time :=
| Dispatch
| Start : Thread_Time -> Dispatch_Time
| Completion : Thread_Time -> Dispatch_Time
| NoIo.

Scheme Equality for Dispatch_Time.

Definition Invalid_Feature :=
  Feature (Ident "invalid" ) inF invalid nil_component nil.

Record port_variable : Type := {
  port : feature;
  variable : Port_Queue;
  dispatch_time : Dispatch_Time;
  urgency : nat;
}.

Lemma port_variable_eq_dec : forall x y : port_variable, {x=y}+{x<>y}.
Proof.
  decide equality.
  apply PeanoNat.Nat.eq_dec.
  apply Dispatch_Time_eq_dec.
  apply list_eq_dec; apply PeanoNat.Nat.eq_dec.
  apply feature_eq_dec.
Qed.

Definition mkPortVariable (f : feature) := {|
  port := f;
  variable := [];
  dispatch_time := Dispatch;
  urgency := 0;
|}.

Definition Invalid_Port_Variable := mkPortVariable Invalid_Feature.

Definition Update_Variable (p : port_variable) (v : Port_Queue): port_variable := {|
  port := p.(port);
  variable := v;
  dispatch_time := p.(dispatch_time);
  urgency := p.(urgency);
|}.

Definition Build_Input_Port_Variables (l : list feature) :=
  map mkPortVariable (Get_Input_Features l).

Definition Is_Output_Port (f : feature) :=
  DirectionType_beq (projectionFeatureDirection f) outF ||
  DirectionType_beq (projectionFeatureDirection f) inoutF.

Definition Get_Output_Features (l : list feature) :=
  filter Is_Output_Port l.

Definition Build_Output_Port_Variables (l : list feature) :=
  map mkPortVariable (Get_Output_Features l).

(** %\begin{definition}[Enabled set] (AADLv2.2 \S 5.4.2 37, 38)\\

For threads whose dispatch protocol is aperiodic, sporadic, timed, or hybrid, a dispatch request is the result of an event or event data arriving at an event or event data port of the thread, or a remote subprogram call arriving at a provides subprogram access feature of the thread.  This dispatch trigger condition is determined as follows:
\begin{itemize}
\item Arrival of an event or event data on any incoming event, or event data port, or arrival of any subprogram call request on a provides subprogram access feature. In other words, it is a disjunction of all incoming features.
\item By arrival on a subset of incoming features (port, subprogram access).  This subset can be specified through the \texttt{Dispatch\_Trigger} value of the thread.
\item By a user-defined logical condition on the incoming features that can trigger the dispatch expressed through an annex subclause expressed in the Behavior Annex  sublanguage notation (see Annex Document D).
\end{itemize}

Let us note $E$ the set of features that can trigger a dispatch with a non-empty queue.
\end{definition}%*)

Definition Build_Dispatch_Trigger (l : list feature) :=
  filter Is_Triggerable_Port l. (* XXX should use also property Dispatch_Trigger *)

Definition Pending_Request_On (p : port_variable) :=
  negb (ListQueue.is_empty p.(variable)).

Definition Has_Pending_Request (l : list port_variable) (d : list feature) : Prop :=
  exists p, In p l -> p.(variable) <> nil /\ In p.(port) d.

Definition In_Dispatch_Trigger (p : port_variable) (d : list feature) :=
  In p.(port) d.

Fixpoint In_Dispatch_Trigger_b (p : port_variable) (d : list feature) :=
match d with
| nil => false
| h :: t => (eqb feature_eq_dec (p.(port)) h) || In_Dispatch_Trigger_b p t
end.

Fixpoint Has_Pending_Request' (l : list port_variable) (d : list feature) :=
  match l with
  | nil => false
  | h :: t => (Pending_Request_On h && In_Dispatch_Trigger_b h d ) ||
              (Has_Pending_Request' t d)
  end.

Definition Port_Variables_With_Pending_Request
  (l : list port_variable) (d : list feature) : list port_variable :=
  filter Pending_Request_On l.

Check Port_Variables_With_Pending_Request.

(** ** Thread state *)

(** %\begin{definition}[Thread State (Coq)]
TBD
  \end{definition} %*)

Record thread_state : Type := {
  dispatch_protocol : Dispatch_Protocol;
  period : Thread_Time;
(*  deadline : Thread_Time;
  wcet : Thread_Time; *)
  priority : nat;
  clock : Thread_Time;
  input_ports : list port_variable;
  output_ports : list port_variable;
  dispatch_trigger : list feature;
}.

Definition mk_thread_state (t : component) : thread_state := {|
  dispatch_protocol := Map_Scheduling_Protocol (t->properties);
  period := Map_Period (t->properties);
  priority := Map_Priority (t->properties);
  clock := 0;
  input_ports := Build_Input_Port_Variables (t->features);
  output_ports := Build_Output_Port_Variables (t->features);
  dispatch_trigger := Build_Dispatch_Trigger (t->features);
|}.

Eval compute in mk_thread_state (A_Periodic_Thread).
Eval compute in mk_thread_state (A_Sporadic_Thread).

(** %\begin{definition}[Advance time (Coq)]
TBD
  \end{definition} %*)

(** Coq has no syntax to update records, but a plugin that I prefer not to use. This provides a sufficient alternative *)

Definition advance_time (t : thread_state) (tt : Thread_Time): thread_state := {|
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

Definition store_in (t : thread_state) (name : identifier) (value : nat) : thread_state := {|
  dispatch_protocol := t.(dispatch_protocol);
  period := t.(period);
  priority := t.(priority);
  clock := t.(clock);
  input_ports := Store_In t.(input_ports) name value;
  output_ports := t.(output_ports);
  dispatch_trigger := t.(dispatch_trigger);
|}.

(** * Thread Dispatching *)

(** This section defines the predicates for a thread to be dispatched. In particular, we define the [Enabled] function that returns [true] when a thread is ready for dispatch. %\paragraph{}% *)

(** %\begin{definition}[\texttt{Enabled} (periodic thread)]
  (AADLv2.2 \S 5.4.2 35)\\	For a thread whose dispatch protocol is \textbf{periodic}, a dispatch request is issued at time intervals of the specified Period property value.  The Enabled function is $t = Period$.
  \end{definition} %*)

Definition Periodic_Enabled (th : thread_state) :=
  (th.(clock) mod th.(period)) =? 0.

Definition A_Periodic_Thread_State := mk_thread_state (A_Periodic_Thread).

Eval compute in Periodic_Enabled (A_Periodic_Thread_State).

Definition A_Periodic_Thread_State' := advance_time A_Periodic_Thread_State 4.

Eval compute in Periodic_Enabled (A_Periodic_Thread_State').

(** % \begin{definition}[\texttt{Enabled} (sporadic thread)]
  (AADLv2.2 \S 5.4.2 40)\\ For a thread whose dispatch protocol is \textbf{sporadic}, a dispatch request is the result of an event or event data arriving at an event or event data port of the thread, or a remote subprogram call arriving at a provides subprogram access feature of the thread.  The time interval between successive dispatch requests will never be less than the associated Period property value. The Enabled function is $t \ge Period \land \exists p \in E: p \neq \emptyset$.
  \end{definition} %*)

Definition Sporadic_Enabled (th : thread_state) :=
  (th.(period) <=? th.(clock)) &&
  Has_Pending_Request' th.(input_ports) th.(dispatch_trigger).

(** We can continue a build a sporadic thread, add an event, avancd time and check it is enabled *)

Definition A_Sporadic_Thread_State := mk_thread_state (A_Sporadic_Thread).

Eval compute in Sporadic_Enabled (A_Sporadic_Thread_State).

Definition A_Sporadic_Thread_State' := store_in A_Sporadic_Thread_State (Ident "a_feature") 42.
Compute A_Sporadic_Thread_State'.

Eval compute in Sporadic_Enabled (A_Sporadic_Thread_State').

Eval compute in Sporadic_Enabled (advance_time A_Sporadic_Thread_State' 32).

(** Port Input and Output Timing *)

Fixpoint Dispatch_Port' (p : port_variable) (l : list port_variable) :=
  match l with
  | nil => Invalid_Port_Variable
  | h :: t => if p.(urgency) <=? h.(urgency)
      then Dispatch_Port' h t else Dispatch_Port' p t
    (* note we take h in all cases, this is to address the case where the
       first argument is [Invalid_Feature] *)
  end.

Definition Dispatching_Port (th : thread_state) : port_variable :=
  Dispatch_Port' Invalid_Port_Variable
      (Port_Variables_With_Pending_Request th.(input_ports) th.(dispatch_trigger)).

Definition Frozen (p : port_variable) (th : thread_state) :=
match p.(dispatch_time) with
| Dispatch => (p = Dispatching_Port th) \/ ~ (In_Dispatch_Trigger p th.(dispatch_trigger))
| NoIo => False
| Start _ => False
| Completion _ => False
end.

Print Frozen.

(* begin hide *)
End AADL_Dispatching.
(* end hide *)
