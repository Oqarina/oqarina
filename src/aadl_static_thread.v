(**
%\subsection{Threads}\label{sec::aadl_thread}%

*)

(* begin hide *)
(** Coq Library *)

Require Import List.
Import ListNotations. (* from List *)

(** Oqarina library *)
Require Import Oqarina.core.identifiers.
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

Definition Well_Formed_Thead_Component_Type (c: component) :=
  Well_Formed_Component_Type c
      [ dataPort ; eventPort ; eventDataPort ; dataAccess ;
        subprogramAccess ; subprogramGroupAccess ;featureGroup ; abstractFeature ].

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
        (* virtualBusAccess *)
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

Lemma Well_Formed_Abstract_Component_Implementation_dec (c : component) :
  forall c:component,
    {Well_Formed_Abstract_Component_Implementation c} +
    {~ Well_Formed_Abstract_Component_Implementation c}.
Proof. 
  intros.
  unfold Well_Formed_Abstract_Component_Implementation.
  apply Well_Formed_Component_Implementation_dec.
Qed.


