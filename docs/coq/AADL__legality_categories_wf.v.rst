.. coq::


.. coq:: none

   Require Import List.
   Import ListNotations. (* from List *)

   (** Oqarina library *)
   Require Import Oqarina.core.all.
   Require Import Oqarina.AADL.Kernel.all.
   Require Import Oqarina.AADL.legality.features_wf.

Component categories
--------------------

XXX add feature direction


Thread
``````

.. coq::

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

Data
````

.. coq::

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

Subprogram
``````````

.. coq::

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

Subprogram Group
````````````````

.. coq::

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

Thread Group
````````````

.. coq::

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

Process
```````

.. coq::

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

Processor
`````````

.. coq::

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

Virtual Processor
`````````````````

.. coq::

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

Memory
```````

.. coq::

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

Bus
```

.. coq::

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

Virtual Bus
```````````

.. coq::

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

Device
``````

.. coq::

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

Abstract
````````

.. coq::

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

System
```````

.. coq::

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

.. coq:: none

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

General component category well-formedness
``````````````````````````````````````````

Here, we define two master theorems that assess wether a component type has a valid interface and a component implementation valid subcomponents.

.. coq::

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
