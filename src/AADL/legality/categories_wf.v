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

(*| .. coq:: none |*)
Require Import List.
Import ListNotations. (* from List *)

(** Oqarina library *)
Require Import Oqarina.core.all.
Require Import Oqarina.AADL.Kernel.all.
Require Import Oqarina.AADL.legality.features_wf.
(*| .. coq:: |*)

(*|

Component categories
--------------------

XXX add feature direction


Thread
``````
|*)

Local Hint Resolve
  Well_Formed_Component_Subcomponents_dec
  Well_Formed_Component_Interface_dec : core.

Definition Well_Formed_Thead_Component_Type (c: component) :=
  Well_Formed_Component_Interface c
      [ dataPort ; eventPort ; eventDataPort ; dataAccess ;
        subprogramAccess ; subprogramGroupAccess ; featureGroup ; abstractFeature ].

Lemma Well_Formed_Thead_Component_Type_dec :
  forall c:component,
    {Well_Formed_Thead_Component_Type c} +
    {~ Well_Formed_Thead_Component_Type c}.
Proof.
  prove_dec.
Qed.

Definition Well_Formed_Thead_Component_Implementation (c: component) :=
  Well_Formed_Component_Subcomponents c
    [ data ; subprogram ; subprogramGroup ; abstract ].

Lemma Well_Formed_Thead_Component_Implementation_dec :
  forall c:component, {Well_Formed_Thead_Component_Implementation c} +
                      {~ Well_Formed_Thead_Component_Implementation c}.
Proof.
  prove_dec.
Qed.

(*|
Data
````
|*)

Definition Well_Formed_Data_Component_Type (c: component) :=
  Well_Formed_Component_Interface c
    [ featureGroup ; subprogramAccess ; subprogramGroupAccess ;
      dataAccess ; abstractFeature
    ].

Lemma Well_Formed_Data_Component_Type_dec :
  forall c:component,
    {Well_Formed_Data_Component_Type c} +
    {~ Well_Formed_Data_Component_Type c}.
Proof.
  prove_dec.
Qed.

Definition Well_Formed_Data_Component_Implementation (c:component) :=
  Well_Formed_Component_Subcomponents c
    [ data ; subprogram ; abstract ].

Lemma Well_Formed_Data_Component_Implementation_dec :
  forall c:component,
    {Well_Formed_Data_Component_Implementation c} +
    {~ Well_Formed_Data_Component_Implementation c}.
Proof.
  prove_dec.
Qed.

(*|
Subprogram
``````````
|*)

Definition Well_Formed_Subprogram_Component_Type (c: component) :=
    Well_Formed_Component_Interface c
    [ eventPort ; featureGroup ; dataAccess ; subprogramAccess ;
      subprogramGroupAccess ; parameter ; abstractFeature
    ].

Lemma Well_Formed_Subprogram_Component_Type_dec :
  forall c:component,
  {Well_Formed_Subprogram_Component_Type c} +
  {~ Well_Formed_Subprogram_Component_Type c}.
Proof.
  prove_dec.
Qed.

Definition Well_Formed_Subprogram_Component_Implementation (c: component) :=
  Well_Formed_Component_Subcomponents c
  [ data ; abstract; subprogram ].

Lemma Well_Formed_Subprogram_Component_Implementation_dec :
  forall c:component,
  {Well_Formed_Subprogram_Component_Implementation c} +
  {~ Well_Formed_Subprogram_Component_Implementation c}.
Proof.
  prove_dec.
Qed.

(*|
Subprogram Group
````````````````
|*)

Definition Well_Formed_SubprogramGroup_Component_Type (c: component) :=
    Well_Formed_Component_Interface c
    [ featureGroup ; subprogramAccess ; subprogramGroupAccess ;
      abstractFeature ].

Lemma Well_Formed_SubprogramGroup_Component_Type_dec :
  forall c:component,
  {Well_Formed_SubprogramGroup_Component_Type c} +
  {~ Well_Formed_SubprogramGroup_Component_Type c}.
Proof.
  prove_dec.
Qed.

Definition Well_Formed_SubprogramGroup_Component_Implementation (c: component) :=
  Well_Formed_Component_Subcomponents c
  [ data ; abstract; subprogram ].

Lemma Well_Formed_SubprogramGroup_Component_Implementation_dec :
  forall c:component,
  {Well_Formed_SubprogramGroup_Component_Implementation c} +
  {~ Well_Formed_SubprogramGroup_Component_Implementation c}.
Proof.
  prove_dec.
Qed.

(*|
Thread Group
````````````
|*)

Definition Well_Formed_ThreadGroup_Component_Type (c: component) :=
    Well_Formed_Component_Interface c
    [ dataPort ; eventPort ; eventDataPort ; featureGroup ; dataAccess ;
      subprogramAccess ; subprogramGroupAccess ; abstractFeature ].

Lemma Well_Formed_ThreadGroup_Component_Type_dec :
  forall c:component,
  {Well_Formed_ThreadGroup_Component_Type c} +
  {~ Well_Formed_ThreadGroup_Component_Type c}.
Proof.
  prove_dec.
Qed.

Definition Well_Formed_ThreadGroup_Component_Implementation (c: component) :=
  Well_Formed_Component_Subcomponents c
  [ data ; subprogram ; subprogramGroup ; thread ; threadGroup ; abstract ].

Lemma Well_Formed_ThreadGroup_Component_Implementation_dec :
  forall c:component,
  {Well_Formed_ThreadGroup_Component_Implementation c} +
  {~ Well_Formed_ThreadGroup_Component_Implementation c}.
Proof.
  prove_dec.
Qed.

(*|
Process
```````
|*)

Definition Well_Formed_Process_Component_Type (c: component) :=
    Well_Formed_Component_Interface c
    [ dataPort ; eventPort ; eventDataPort ; featureGroup ; dataAccess ;
      subprogramAccess ; subprogramGroupAccess ; abstractFeature ].

Lemma Well_Formed_Process_Component_Type_dec :
  forall c:component,
  {Well_Formed_Process_Component_Type c} +
  {~ Well_Formed_Process_Component_Type c}.
Proof.
  prove_dec.
Qed.

Definition Well_Formed_Process_Component_Implementation (c: component) :=
  Well_Formed_Component_Subcomponents c
  [ data ; subprogram ; subprogramGroup ; thread ; threadGroup ; abstract ].

Lemma Well_Formed_Process_Component_Implementation_dec :
  forall c:component,
  {Well_Formed_Process_Component_Implementation c} +
  {~ Well_Formed_Process_Component_Implementation c}.
Proof.
  prove_dec.
Qed.

(*|
Processor
`````````
|*)

Definition Well_Formed_Processor_Component_Type (c: component) :=
    Well_Formed_Component_Interface c
    [ subprogramAccess ; subprogramGroupAccess ;
      dataPort ; eventPort ; eventDataPort ;
      featureGroup ; busAccess ; virtualBusAccess;
      abstractFeature ].

Lemma Well_Formed_Processor_Component_Type_dec :
  forall c:component,
  {Well_Formed_Processor_Component_Type c} +
  {~ Well_Formed_Processor_Component_Type c}.
Proof.
  prove_dec.
Qed.

Definition Well_Formed_Processor_Component_Implementation (c: component) :=
  Well_Formed_Component_Subcomponents c
  [ memory ; bus ; virtualProcessor ; virtualBus ; abstract ].

Lemma Well_Formed_Processor_Component_Implementation_dec :
  forall c:component,
  {Well_Formed_Processor_Component_Implementation c} +
  {~ Well_Formed_Processor_Component_Implementation c}.
Proof.
  prove_dec.
Qed.

(*|
Virtual Processor
`````````````````
|*)

Definition Well_Formed_VirtualProcessor_Component_Type (c: component) :=
    Well_Formed_Component_Interface c
    [ subprogramAccess ; subprogramGroupAccess ;
      dataPort ; eventPort ; eventDataPort ;
      virtualBusAccess;
      featureGroup ; abstractFeature ].

Lemma Well_Formed_VirtualProcessor_Component_Type_dec :
  forall c:component,
  {Well_Formed_VirtualProcessor_Component_Type c} +
  {~ Well_Formed_VirtualProcessor_Component_Type c}.
Proof.
  prove_dec.
Qed.

Definition Well_Formed_VirtualProcessor_Component_Implementation (c: component) :=
  Well_Formed_Component_Subcomponents c
  [ virtualProcessor ; virtualBus ; abstract ].

Lemma Well_Formed_VirtualProcessor_Component_Implementation_dec :
  forall c:component,
  {Well_Formed_VirtualProcessor_Component_Implementation c} +
  {~ Well_Formed_VirtualProcessor_Component_Implementation c}.
Proof.
  prove_dec.
Qed.

(*|
Memory
```````
|*)

Definition Well_Formed_Memory_Component_Type (c: component) :=
    Well_Formed_Component_Interface c
    [ busAccess ; (* virtualBusAccess ; *)
      featureGroup ; abstractFeature ;
      dataPort ; eventPort ; eventDataPort ].

Lemma Well_Formed_Memory_Component_Type_dec :
  forall c:component,
  {Well_Formed_Memory_Component_Type c} +
  {~ Well_Formed_Memory_Component_Type c}.
Proof.
  prove_dec.
Qed.

Definition Well_Formed_Memory_Component_Implementation (c: component) :=
  Well_Formed_Component_Subcomponents c
  [ memory ; bus ; abstract ].

Lemma Well_Formed_Memory_Component_Implementation_dec :
  forall c:component,
  {Well_Formed_Memory_Component_Implementation c} +
  {~ Well_Formed_Memory_Component_Implementation c}.
Proof.
  prove_dec.
Qed.

(*|
Bus
```
|*)

Definition Well_Formed_Bus_Component_Type (c: component) :=
    Well_Formed_Component_Interface c
    [ busAccess ; (* virtualBusAccess ; *)
      featureGroup ; abstractFeature ;
      dataPort ; eventPort ; eventDataPort ].

Lemma Well_Formed_Bus_Component_Type_dec :
  forall c:component,
  {Well_Formed_Bus_Component_Type c} +
  {~ Well_Formed_Bus_Component_Type c}.
Proof.
  prove_dec.
Qed.

Definition Well_Formed_Bus_Component_Implementation (c: component) :=
  Well_Formed_Component_Subcomponents c
  [ virtualBus ; abstract ].

Lemma Well_Formed_Bus_Component_Implementation_dec :
  forall c:component,
  {Well_Formed_Bus_Component_Implementation c} +
  {~ Well_Formed_Bus_Component_Implementation c}.
Proof.
  prove_dec.
Qed.

(*|
Virtual Bus
```````````
|*)

Definition Well_Formed_VirtualBus_Component_Type (c: component) :=
    Well_Formed_Component_Interface c
    [ dataPort ; eventPort ; eventDataPort ;
      (* virtualBusAccess ; *)
      featureGroup ; abstractFeature ].

Lemma Well_Formed_VirtualBus_Component_Type_dec :
  forall c:component,
  {Well_Formed_VirtualBus_Component_Type c} +
  {~ Well_Formed_VirtualBus_Component_Type c}.
Proof.
  prove_dec.
Qed.

Definition Well_Formed_VirtualBus_Component_Implementation (c: component) :=
  Well_Formed_Component_Subcomponents c
  [ virtualBus ; abstract ].

Lemma Well_Formed_VirtualBus_Component_Implementation_dec :
  forall c:component,
  {Well_Formed_VirtualBus_Component_Implementation c} +
  {~ Well_Formed_VirtualBus_Component_Implementation c}.
Proof.
  prove_dec.
Qed.

(*|
Device
``````
|*)

Definition Well_Formed_Device_Component_Type (c: component) :=
    Well_Formed_Component_Interface c
    [ dataPort ; eventPort ; eventDataPort ; featureGroup ;
      subprogramAccess ; subprogramGroupAccess ;
      busAccess ; (* virtualBusAccess ; *)
      abstractFeature ].

Lemma Well_Formed_Device_Component_Type_dec :
  forall c:component,
  {Well_Formed_Device_Component_Type c} +
  {~ Well_Formed_Device_Component_Type c}.
Proof.
  prove_dec.
Qed.

Definition Well_Formed_Device_Component_Implementation (c: component) :=
  Well_Formed_Component_Subcomponents c
  [ bus ; virtualBus ; data ; abstract ].

Lemma Well_Formed_Device_Component_Implementation_dec :
  forall c:component,
  {Well_Formed_Device_Component_Implementation c} +
  {~ Well_Formed_Device_Component_Implementation c}.
Proof.
  prove_dec.
Qed.

(*|
Abstract
````````
|*)

Definition Well_Formed_Abstract_Component_Type (c: component) :=
  Well_Formed_Component_Interface c
      [ dataPort ; eventPort ; eventDataPort ; featureGroup ; dataAccess ;
        subprogramAccess ; subprogramGroupAccess ; busAccess ;
        virtualBusAccess ; abstractFeature
      ].

Lemma Well_Formed_Abstract_Component_Type_dec :
  forall c:component,
    {Well_Formed_Abstract_Component_Type c} +
    {~ Well_Formed_Abstract_Component_Type c}.
Proof.
  prove_dec.
Qed.

Definition Well_Formed_Abstract_Component_Implementation (c: component) :=
  Well_Formed_Component_Subcomponents c
      [ data ; subprogram ; subprogramGroup ; thread ; threadGroup ; process ;
        processor ; virtualProcessor ; memory ; bus ; virtualBus ; device ;
        system ; abstract
      ].

Lemma Well_Formed_Abstract_Component_Implementation_dec :
  forall c:component,
    {Well_Formed_Abstract_Component_Implementation c} +
    {~ Well_Formed_Abstract_Component_Implementation c}.
Proof.
  prove_dec.
Qed.

(*|
System
```````
|*)

Definition Well_Formed_System_Component_Type (c: component) :=
    Well_Formed_Component_Interface c
    [ dataPort ; eventPort ; eventDataPort ;
      featureGroup ; subprogramAccess ; subprogramGroupAccess ;
      busAccess ; (* virtualBusAccess ; *)
      dataAccess ; abstractFeature ].

Lemma Well_Formed_System_Component_Type_dec :
  forall c:component,
  {Well_Formed_System_Component_Type c} +
  {~ Well_Formed_System_Component_Type c}.
Proof.
  prove_dec.
Qed.

Definition Well_Formed_System_Component_Implementation (c: component) :=
  Well_Formed_Component_Subcomponents c
  [ data ; subprogram ; subprogramGroup ; process ; processor ;
    virtualProcessor ; memory ; bus ; virtualBus ; device ; system ;
    abstract ].

Lemma Well_Formed_System_Component_Implementation_dec :
  forall c:component,
  {Well_Formed_System_Component_Implementation c} +
  {~ Well_Formed_System_Component_Implementation c}.
Proof.
  prove_dec.
Qed.

(*| .. coq:: none |*)
Local Hint Resolve
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
(*| .. coq:: |*)

(*|

General component category well-formedness
``````````````````````````````````````````

Here, we define two master theorems that assess wether a component type has a valid interface and a component implementation valid subcomponents.

|*)

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
  prove_dec.
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
  prove_dec.
Qed.
