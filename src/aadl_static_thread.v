(**
%\subsection{Threads}\label{sec::aadl_thread}%

*)

(* begin hide *)
(** Coq Library *)

Require Import List.
Import ListNotations. (* from List *)

(** Oqarina library *)
Require Import Oqarina.core.all.
Require Import Oqarina.AADL.Kernel.all.
Require Import Oqarina.AADL.declarative.all.
(* end hide *)

(** %

\N An AADL thread models a flow of execution. A thread forms a schedulable unit that can execute concurrently with other threads. For a definition of threads, see \S 5.4 of \cite{as2-cArchitectureAnalysisDesign2017}.

\N \wfrule{Thead component category well-formedness}{}
        {An AADL thread respects the following constraints on its elements:}

\threadconstraints

From these rules, we deduce the two following lemmas and their decidability results\change{Actually wrong, we miss the direction of the feature !}:
% *)

(* N.B.: plain 'feature' in the AADL document is represented by 'abstractFeature' here in Coq. *)

(**************************************************)
(* Page 80 *)

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

(********************************************************************)
(* TODO: Move the below to an appropriate new file *)

(* page 54 *)
Definition Well_Formed_Abstract_Component_Type (c: component) :=
  Well_Formed_Component_Type c
      [ dataPort ; eventPort ; eventDataPort ; featureGroup ; dataAccess ;
        subprogramAccess ; subprogramGroupAccess ; busAccess ;
        (* virtualBusAccess FIXME *)
        abstractFeature
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

(**************************************************)
(* Page 65 *)

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

(**************************************************)
(* Page 72 *)

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

(**************************************************)
(* Page 78 *)

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

(**************************************************)
(* Page 99 *)

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


(**************************************************)
(* Page 101 *)

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

(**************************************************)
(* Page 106 *)

Definition Well_Formed_Processor_Component_Type (c: component) :=
    Well_Formed_Component_Type c
    [ subprogramAccess ; subprogramGroupAccess ; 
      dataPort ; eventPort ; eventDataPort ;
      featureGroup ; busAccess ; (* virtualBusAccess; *) (* FIXME *) 
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


(**************************************************)
(* Page 110 *)

Definition Well_Formed_VirtualProcessor_Component_Type (c: component) :=
    Well_Formed_Component_Type c
    [ subprogramAccess ; subprogramGroupAccess ; 
      dataPort ; eventPort ; eventDataPort ;
      (* virtualBusAccess; *) (* FIXME *) 
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



(**************************************************)
(* Page 113 *)

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


(**************************************************)
(* Page 115 *)

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


(**************************************************)
(* Page 118 *)

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


(**************************************************)
(* Page 121 *)

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


(**************************************************)
(* Page 126 *)

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

