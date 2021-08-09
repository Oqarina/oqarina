(* begin hide *)
(** Coq Library *)

Require Import List.
Import ListNotations. (* from List *)

(** Oqarina library *)
Require Import Oqarina.core.all.
Require Import Oqarina.AADL.Kernel.all.
Require Import Oqarina.AADL.declarative.all.
(* end hide *)

(**
%
\section{Software Categories}

\subsection{Threads}\label{sec::aadl_thread}

\N An AADL thread models a flow of execution. A thread forms a schedulable unit that can execute concurrently with other threads. For a definition of threads, see \S 5.4 of \cite{as2-cArchitectureAnalysisDesign2017}.

\N \wfrule{Thead component category well-formedness}{}
        {An AADL thread respects the following constraints on its elements:}

\threadconstraints

From these rules, we deduce the two following lemmas and their decidability results\change{Actually wrong, we miss the direction of the feature !}:
% *)

Definition Well_Formed_Thead_Component_Type (c: component) :=
  Well_Formed_Component_Type c
      [ dataPort ; eventPort ; eventDataPort ; dataAccess ;
        subprogramAccess ; subprogramGroupAccess ; featureGroup ; abstractFeature ].

Lemma Well_Formed_Thead_Component_Type_dec :
  forall c:component,
    {Well_Formed_Thead_Component_Type c} +
    {~ Well_Formed_Thead_Component_Type c}.
Proof.
  intros.
  unfold Well_Formed_Thead_Component_Type.
  apply Well_Formed_Component_Type_dec.
Qed.

Definition Well_Formed_Thead_Component_Implementation (c: component) :=
  Well_Formed_Component_Implementation c
    [ data ; subprogram ; subprogramGroup ; abstract ].

Lemma Well_Formed_Thead_Component_Implementation_dec :
  forall c:component, {Well_Formed_Thead_Component_Implementation c} +
                      {~ Well_Formed_Thead_Component_Implementation c}.
Proof.
  intros.
  unfold Well_Formed_Thead_Component_Implementation.
  apply Well_Formed_Component_Implementation_dec.
Qed.

(**
%\subsection{Data}\label{sec::aadl_data}

\N \wfrule{Data component category well-formedness}{}
        {An AADL data respects the following constraints on its elements:}

\dataconstraints
*)

Definition Well_Formed_Data_Component_Type (c: component) :=
  Well_Formed_Component_Type c
    [ featureGroup ; subprogramAccess ; subprogramGroupAccess ;
      dataAccess ; abstractFeature
    ].

Lemma Well_Formed_Data_Component_Type_dec :
  forall c:component,
    {Well_Formed_Data_Component_Type c} +
    {~ Well_Formed_Data_Component_Type c}.
Proof.
  intros.
  unfold Well_Formed_Data_Component_Type.
  apply Well_Formed_Component_Type_dec.
Qed.

Definition Well_Formed_Data_Component_Implementation (c:component) :=
  Well_Formed_Component_Implementation c
    [ data ; subprogram ; abstract ].

Lemma Well_Formed_Data_Component_Implementation_dec :
  forall c:component,
    {Well_Formed_Data_Component_Implementation c} +
    {~ Well_Formed_Data_Component_Implementation c}.
Proof.
  intros.
  unfold Well_Formed_Data_Component_Implementation.
  apply Well_Formed_Component_Implementation_dec.
Qed.

(**
%\subsection{Subprogram}\label{sec::aadl_subprogram}

\N \wfrule{Subprogram component category well-formedness}{}
        {An AADL subprogram respects the following constraints on its elements:}

\subprogramconstraints
*)

Definition Well_Formed_Subprogram_Component_Type (c: component) :=
    Well_Formed_Component_Type c
    [ eventPort ; featureGroup ; dataAccess ; subprogramAccess ;
      subprogramGroupAccess ; parameter ; abstractFeature
    ].

Lemma Well_Formed_Subprogram_Component_Type_dec :
  forall c:component,
  {Well_Formed_Subprogram_Component_Type c} +
  {~ Well_Formed_Subprogram_Component_Type c}.
Proof.
  intros.
  unfold Well_Formed_Subprogram_Component_Type.
  apply Well_Formed_Component_Type_dec.
Qed.

Definition Well_Formed_Subprogram_Component_Implementation (c: component) :=
  Well_Formed_Component_Implementation c
  [ data ; abstract; subprogram ].

Lemma Well_Formed_Subprogram_Component_Implementation_dec :
  forall c:component,
  {Well_Formed_Subprogram_Component_Implementation c} +
  {~ Well_Formed_Subprogram_Component_Implementation c}.
Proof.
  intros.
  unfold Well_Formed_Subprogram_Component_Implementation.
  apply Well_Formed_Component_Implementation_dec.
Qed.

(**
%\subsection{Subprogram Group}\label{sec::aadl_subprogram_group}

\N \wfrule{Subprogram Group component category well-formedness}{}
        {An AADL subprogram group espects the following constraints on its elements:}

\subprogramgroupconstraints
*)

Definition Well_Formed_SubprogramGroup_Component_Type (c: component) :=
    Well_Formed_Component_Type c
    [ featureGroup ; subprogramAccess ; subprogramGroupAccess ;
      abstractFeature ].

Lemma Well_Formed_SubprogramGroup_Component_Type_dec :
  forall c:component,
  {Well_Formed_SubprogramGroup_Component_Type c} +
  {~ Well_Formed_SubprogramGroup_Component_Type c}.
Proof.
  intros.
  unfold Well_Formed_SubprogramGroup_Component_Type.
  apply Well_Formed_Component_Type_dec.
Qed.

Definition Well_Formed_SubprogramGroup_Component_Implementation (c: component) :=
  Well_Formed_Component_Implementation c
  [ data ; abstract; subprogram ].

Lemma Well_Formed_SubprogramGroup_Component_Implementation_dec :
  forall c:component,
  {Well_Formed_SubprogramGroup_Component_Implementation c} +
  {~ Well_Formed_SubprogramGroup_Component_Implementation c}.
Proof.
  intros.
  unfold Well_Formed_SubprogramGroup_Component_Implementation.
  apply Well_Formed_Component_Implementation_dec.
Qed.

(**
%\subsection{Thread Group}\label{sec::aadl_thread_group}

\N \wfrule{Thread Group component category well-formedness}{}
        {An AADL thread group espects the following constraints on its elements:}

\threadgroupconstraints
*)

Definition Well_Formed_ThreadGroup_Component_Type (c: component) :=
    Well_Formed_Component_Type c
    [ dataPort ; eventPort ; eventDataPort ; featureGroup ; dataAccess ;
      subprogramAccess ; subprogramGroupAccess ; abstractFeature ].

Lemma Well_Formed_ThreadGroup_Component_Type_dec :
  forall c:component,
  {Well_Formed_ThreadGroup_Component_Type c} +
  {~ Well_Formed_ThreadGroup_Component_Type c}.
Proof.
  intros.
  unfold Well_Formed_ThreadGroup_Component_Type.
  apply Well_Formed_Component_Type_dec.
Qed.

Definition Well_Formed_ThreadGroup_Component_Implementation (c: component) :=
  Well_Formed_Component_Implementation c
  [ data ; subprogram ; subprogramGroup ; thread ; threadGroup ; abstract ].

Lemma Well_Formed_ThreadGroup_Component_Implementation_dec :
  forall c:component,
  {Well_Formed_ThreadGroup_Component_Implementation c} +
  {~ Well_Formed_ThreadGroup_Component_Implementation c}.
Proof.
  intros.
  unfold Well_Formed_ThreadGroup_Component_Implementation.
  apply Well_Formed_Component_Implementation_dec.
Qed.


(**
%\subsection{Process}\label{sec::aadl_process}

\N \wfrule{Process component category well-formedness}{}
        {An AADL process espects the following constraints on its elements:}

\processconstraints
*)
Definition Well_Formed_Process_Component_Type (c: component) :=
    Well_Formed_Component_Type c
    [ dataPort ; eventPort ; eventDataPort ; featureGroup ; dataAccess ;
      subprogramAccess ; subprogramGroupAccess ; abstractFeature ].

Lemma Well_Formed_Process_Component_Type_dec :
  forall c:component,
  {Well_Formed_Process_Component_Type c} +
  {~ Well_Formed_Process_Component_Type c}.
Proof.
  intros.
  unfold Well_Formed_Process_Component_Type.
  apply Well_Formed_Component_Type_dec.
Qed.

Definition Well_Formed_Process_Component_Implementation (c: component) :=
  Well_Formed_Component_Implementation c
  [ data ; subprogram ; subprogramGroup ; thread ; threadGroup ; abstract ].

Lemma Well_Formed_Process_Component_Implementation_dec :
  forall c:component,
  {Well_Formed_Process_Component_Implementation c} +
  {~ Well_Formed_Process_Component_Implementation c}.
Proof.
  intros.
  unfold Well_Formed_Process_Component_Implementation.
  apply Well_Formed_Component_Implementation_dec.
Qed.

(**
%
\section{Execution platform category}

\subsection{Processor}\label{sec::aadl_processor}

\N \wfrule{Processor component category well-formedness}{}
        {An AADL processor espects the following constraints on its elements:}

\processorconstraints
*)

Definition Well_Formed_Processor_Component_Type (c: component) :=
    Well_Formed_Component_Type c
    [ subprogramAccess ; subprogramGroupAccess ;
      dataPort ; eventPort ; eventDataPort ;
      featureGroup ; busAccess ; virtualBusAccess;
      abstractFeature ].

Lemma Well_Formed_Processor_Component_Type_dec :
  forall c:component,
  {Well_Formed_Processor_Component_Type c} +
  {~ Well_Formed_Processor_Component_Type c}.
Proof.
  intros.
  unfold Well_Formed_Processor_Component_Type.
  apply Well_Formed_Component_Type_dec.
Qed.

Definition Well_Formed_Processor_Component_Implementation (c: component) :=
  Well_Formed_Component_Implementation c
  [ memory ; bus ; virtualProcessor ; virtualBus ; abstract ].

Lemma Well_Formed_Processor_Component_Implementation_dec :
  forall c:component,
  {Well_Formed_Processor_Component_Implementation c} +
  {~ Well_Formed_Processor_Component_Implementation c}.
Proof.
  intros.
  unfold Well_Formed_Processor_Component_Implementation.
  apply Well_Formed_Component_Implementation_dec.
Qed.

(**
%\subsection{Virtual Processor}\label{sec::aadl_virtualprocessor}

\N \wfrule{Virtual Processor component category well-formedness}{}
        {An AADL virtual processor espects the following constraints on its elements:}

\virtualprocessorconstraints
*)

Definition Well_Formed_VirtualProcessor_Component_Type (c: component) :=
    Well_Formed_Component_Type c
    [ subprogramAccess ; subprogramGroupAccess ;
      dataPort ; eventPort ; eventDataPort ;
      virtualBusAccess;
      featureGroup ; abstractFeature ].

Lemma Well_Formed_VirtualProcessor_Component_Type_dec :
  forall c:component,
  {Well_Formed_VirtualProcessor_Component_Type c} +
  {~ Well_Formed_VirtualProcessor_Component_Type c}.
Proof.
  intros.
  unfold Well_Formed_VirtualProcessor_Component_Type.
  apply Well_Formed_Component_Type_dec.
Qed.

Definition Well_Formed_VirtualProcessor_Component_Implementation (c: component) :=
  Well_Formed_Component_Implementation c
  [ virtualProcessor ; virtualBus ; abstract ].

Lemma Well_Formed_VirtualProcessor_Component_Implementation_dec :
  forall c:component,
  {Well_Formed_VirtualProcessor_Component_Implementation c} +
  {~ Well_Formed_VirtualProcessor_Component_Implementation c}.
Proof.
  intros.
  unfold Well_Formed_VirtualProcessor_Component_Implementation.
  apply Well_Formed_Component_Implementation_dec.
Qed.

(**
%\subsection{Memory}\label{sec::aadl_memory}

\N \wfrule{Memory component category well-formedness}{}
        {An AADL memory espects the following constraints on its elements:}

\memoryconstraints
*)

Definition Well_Formed_Memory_Component_Type (c: component) :=
    Well_Formed_Component_Type c
    [ busAccess ; (* virtualBusAccess ; *)
      featureGroup ; abstractFeature ;
      dataPort ; eventPort ; eventDataPort ].

Lemma Well_Formed_Memory_Component_Type_dec :
  forall c:component,
  {Well_Formed_Memory_Component_Type c} +
  {~ Well_Formed_Memory_Component_Type c}.
Proof.
  intros.
  unfold Well_Formed_Memory_Component_Type.
  apply Well_Formed_Component_Type_dec.
Qed.

Definition Well_Formed_Memory_Component_Implementation (c: component) :=
  Well_Formed_Component_Implementation c
  [ memory ; bus ; abstract ].

Lemma Well_Formed_Memory_Component_Implementation_dec :
  forall c:component,
  {Well_Formed_Memory_Component_Implementation c} +
  {~ Well_Formed_Memory_Component_Implementation c}.
Proof.
  intros.
  unfold Well_Formed_Memory_Component_Implementation.
  apply Well_Formed_Component_Implementation_dec.
Qed.

(**
%\subsection{Bus}\label{sec::aadl_bus}

\N \wfrule{Bus component category well-formedness}{}
        {An AADL bus espects the following constraints on its elements:}

\busconstraints
*)

Definition Well_Formed_Bus_Component_Type (c: component) :=
    Well_Formed_Component_Type c
    [ busAccess ; (* virtualBusAccess ; *)
      featureGroup ; abstractFeature ;
      dataPort ; eventPort ; eventDataPort ].

Lemma Well_Formed_Bus_Component_Type_dec :
  forall c:component,
  {Well_Formed_Bus_Component_Type c} +
  {~ Well_Formed_Bus_Component_Type c}.
Proof.
  intros.
  unfold Well_Formed_Bus_Component_Type.
  apply Well_Formed_Component_Type_dec.
Qed.

Definition Well_Formed_Bus_Component_Implementation (c: component) :=
  Well_Formed_Component_Implementation c
  [ virtualBus ; abstract ].

Lemma Well_Formed_Bus_Component_Implementation_dec :
  forall c:component,
  {Well_Formed_Bus_Component_Implementation c} +
  {~ Well_Formed_Bus_Component_Implementation c}.
Proof.
  intros.
  unfold Well_Formed_Bus_Component_Implementation.
  apply Well_Formed_Component_Implementation_dec.
Qed.

(**
%\subsection{Virtual Bus}\label{sec::aadl_virtualbus}

\N \wfrule{Virtual Bus component category well-formedness}{}
        {An AADL virtual bus espects the following constraints on its elements:}

\virtualbusconstraints
*)

Definition Well_Formed_VirtualBus_Component_Type (c: component) :=
    Well_Formed_Component_Type c
    [ dataPort ; eventPort ; eventDataPort ;
      (* virtualBusAccess ; *)
      featureGroup ; abstractFeature ].

Lemma Well_Formed_VirtualBus_Component_Type_dec :
  forall c:component,
  {Well_Formed_VirtualBus_Component_Type c} +
  {~ Well_Formed_VirtualBus_Component_Type c}.
Proof.
  intros.
  unfold Well_Formed_VirtualBus_Component_Type.
  apply Well_Formed_Component_Type_dec.
Qed.

Definition Well_Formed_VirtualBus_Component_Implementation (c: component) :=
  Well_Formed_Component_Implementation c
  [ virtualBus ; abstract ].

Lemma Well_Formed_VirtualBus_Component_Implementation_dec :
  forall c:component,
  {Well_Formed_VirtualBus_Component_Implementation c} +
  {~ Well_Formed_VirtualBus_Component_Implementation c}.
Proof.
  intros.
  unfold Well_Formed_VirtualBus_Component_Implementation.
  apply Well_Formed_Component_Implementation_dec.
Qed.

(**
%\subsection{Device}\label{sec::aadl_device}

\N \wfrule{Device component category well-formedness}{}
        {An AADL device espects the following constraints on its elements:}

\deviceconstraints
*)

Definition Well_Formed_Device_Component_Type (c: component) :=
    Well_Formed_Component_Type c
    [ dataPort ; eventPort ; eventDataPort ; featureGroup ;
      subprogramAccess ; subprogramGroupAccess ;
      busAccess ; (* virtualBusAccess ; *)
      abstractFeature ].

Lemma Well_Formed_Device_Component_Type_dec :
  forall c:component,
  {Well_Formed_Device_Component_Type c} +
  {~ Well_Formed_Device_Component_Type c}.
Proof.
  intros.
  unfold Well_Formed_Device_Component_Type.
  apply Well_Formed_Component_Type_dec.
Qed.

Definition Well_Formed_Device_Component_Implementation (c: component) :=
  Well_Formed_Component_Implementation c
  [ bus ; virtualBus ; data ; abstract ].

Lemma Well_Formed_Device_Component_Implementation_dec :
  forall c:component,
  {Well_Formed_Device_Component_Implementation c} +
  {~ Well_Formed_Device_Component_Implementation c}.
Proof.
  intros.
  unfold Well_Formed_Device_Component_Implementation.
  apply Well_Formed_Component_Implementation_dec.
Qed.


(**
%
\section{Generic category}
\subsection{Abstract}\label{sec::aadl_abstract}

\N \wfrule{Abstract component category well-formedness}{}
        {An AADL abstract respects the following constraints on its elements:}

\abstractconstraints
*)

Definition Well_Formed_Abstract_Component_Type (c: component) :=
  Well_Formed_Component_Type c
      [ dataPort ; eventPort ; eventDataPort ; featureGroup ; dataAccess ;
        subprogramAccess ; subprogramGroupAccess ; busAccess ;
        virtualBusAccess ; abstractFeature
      ].

Lemma Well_Formed_Abstract_Component_Type_dec :
  forall c:component,
    {Well_Formed_Abstract_Component_Type c} +
    {~ Well_Formed_Abstract_Component_Type c}.
Proof.
  intros.
  unfold Well_Formed_Abstract_Component_Type.
  apply Well_Formed_Component_Type_dec.
Qed.

Definition Well_Formed_Abstract_Component_Implementation (c: component) :=
  Well_Formed_Component_Implementation c
      [ data ; subprogram ; subprogramGroup ; thread ; threadGroup ; process ;
        processor ; virtualProcessor ; memory ; bus ; virtualBus ; device ;
        system ; abstract
      ].

Lemma Well_Formed_Abstract_Component_Implementation_dec :
  forall c:component,
    {Well_Formed_Abstract_Component_Implementation c} +
    {~ Well_Formed_Abstract_Component_Implementation c}.
Proof.
  intros.
  unfold Well_Formed_Abstract_Component_Implementation.
  apply Well_Formed_Component_Implementation_dec.
Qed.

(**
%
\section{Composite category}
\subsection{System}\label{sec::aadl_system}

\N \wfrule{System component category well-formedness}{}
        {An AADL system espects the following constraints on its elements:}

\systemconstraints
*)

Definition Well_Formed_System_Component_Type (c: component) :=
    Well_Formed_Component_Type c
    [ dataPort ; eventPort ; eventDataPort ;
      featureGroup ; subprogramAccess ; subprogramGroupAccess ;
      busAccess ; (* virtualBusAccess ; *)
      dataAccess ; abstractFeature ].

Lemma Well_Formed_System_Component_Type_dec :
  forall c:component,
  {Well_Formed_System_Component_Type c} +
  {~ Well_Formed_System_Component_Type c}.
Proof.
  intros.
  unfold Well_Formed_System_Component_Type.
  apply Well_Formed_Component_Type_dec.
Qed.

Definition Well_Formed_System_Component_Implementation (c: component) :=
  Well_Formed_Component_Implementation c
  [ data ; subprogram ; subprogramGroup ; process ; processor ;
    virtualProcessor ; memory ; bus ; virtualBus ; device ; system ;
    abstract ].

Lemma Well_Formed_System_Component_Implementation_dec :
  forall c:component,
  {Well_Formed_System_Component_Implementation c} +
  {~ Well_Formed_System_Component_Implementation c}.
Proof.
  intros.
  unfold Well_Formed_System_Component_Implementation.
  apply Well_Formed_Component_Implementation_dec.
Qed.

(* begin hide *)
Global Hint Resolve
  Well_Formed_Thead_Component_Type_dec
  Well_Formed_Thead_Component_Implementation_dec    Well_Formed_Data_Component_Type_dec
  Well_Formed_Data_Component_Implementation_dec
  Well_Formed_Subprogram_Component_Type_dec
  Well_Formed_Subprogram_Component_Implementation_dec
  Well_Formed_SubprogramGroup_Component_Type_dec
  Well_Formed_SubprogramGroup_Component_Implementation_dec
  Well_Formed_ThreadGroup_Component_Type_dec
  Well_Formed_ThreadGroup_Component_Implementation_dec
  Well_Formed_Process_Component_Type_dec
  Well_Formed_Process_Component_Implementation_dec
  Well_Formed_Processor_Component_Type_dec
  Well_Formed_Processor_Component_Implementation_dec
  Well_Formed_VirtualProcessor_Component_Type_dec
  Well_Formed_VirtualProcessor_Component_Implementation_dec
  Well_Formed_Memory_Component_Type_dec
  Well_Formed_Memory_Component_Implementation_dec
  Well_Formed_Bus_Component_Type_dec
  Well_Formed_Bus_Component_Implementation_dec
  Well_Formed_VirtualBus_Component_Type_dec
  Well_Formed_VirtualBus_Component_Implementation_dec
  Well_Formed_Device_Component_Type_dec
  Well_Formed_Device_Component_Implementation_dec
  Well_Formed_Abstract_Component_Type_dec
  Well_Formed_Abstract_Component_Implementation_dec
  Well_Formed_System_Component_Type_dec
  Well_Formed_System_Component_Implementation_dec :core.
(* end hide *)

(**
%
\section{Master theorem}


Here, we define two master theorems that assess wether a component type has a valid interface and a component implementation valid subcomponents.

%*)

Definition Well_Formed_Component_Type_Interface (c : component) :=
  match (c->category) with
  | thread => Well_Formed_Thead_Component_Type c
  | threadGroup => Well_Formed_ThreadGroup_Component_Type c
  | data =>  Well_Formed_Data_Component_Type c
  | subprogram =>  Well_Formed_Subprogram_Component_Type c
  | subprogramGroup =>  Well_Formed_SubprogramGroup_Component_Type c
  | process =>  Well_Formed_Process_Component_Type c

  | system =>  Well_Formed_System_Component_Type c
  | abstract =>  Well_Formed_Abstract_Component_Type c

  | processor =>  Well_Formed_Processor_Component_Type c
  | virtualProcessor =>  Well_Formed_VirtualProcessor_Component_Type c
  | memory =>  Well_Formed_Memory_Component_Type c

  | device =>  Well_Formed_Device_Component_Type c
  | bus =>  Well_Formed_Bus_Component_Type c
  | virtualBus =>  Well_Formed_VirtualBus_Component_Type c
  | null => False
  end.

Lemma Well_Formed_Component_Type_Interface_dec :
  forall c:component,
  {Well_Formed_Component_Type_Interface c} +
  {~ Well_Formed_Component_Type_Interface c}.
Proof.
  intros.
  unfold Well_Formed_Component_Type_Interface.
  destruct (c ->category); auto.
Qed.

Definition Well_Formed_Component_Implementation_Subcomponents (c : component) :=
  match (c->category) with
  | thread => Well_Formed_Thead_Component_Type c
  | threadGroup => Well_Formed_ThreadGroup_Component_Type c
  | data =>  Well_Formed_Data_Component_Type c
  | subprogram =>  Well_Formed_Subprogram_Component_Type c
  | subprogramGroup =>  Well_Formed_SubprogramGroup_Component_Type c
  | process =>  Well_Formed_Process_Component_Type c

  | system =>  Well_Formed_System_Component_Type c
  | abstract =>  Well_Formed_Abstract_Component_Type c

  | processor =>  Well_Formed_Processor_Component_Type c
  | virtualProcessor =>  Well_Formed_VirtualProcessor_Component_Type c
  | memory =>  Well_Formed_Memory_Component_Type c

  | device =>  Well_Formed_Device_Component_Type c
  | bus =>  Well_Formed_Bus_Component_Type c
  | virtualBus =>  Well_Formed_VirtualBus_Component_Type c
  | null => False
  end.

Lemma Well_Formed_Component_Implementation_Subcomponents_dec :
  forall c:component,
  {Well_Formed_Component_Implementation_Subcomponents c} +
  {~ Well_Formed_Component_Implementation_Subcomponents c}.
Proof.
  intros.
  unfold Well_Formed_Component_Implementation_Subcomponents.
  destruct (c ->category); auto.
Qed.
