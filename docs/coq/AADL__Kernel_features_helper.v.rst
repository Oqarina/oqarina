.. coq::


.. coq:: none

   (** Coq Library *)
   Require Import List.
   Import ListNotations. (* from List *)
   Require Import Coq.Bool.Bool.

   (** Oqarina library *)
   Require Import Oqarina.AADL.Kernel.categories.
   Require Import Oqarina.AADL.Kernel.component.
   Require Import Oqarina.coq_utils.all.
   Require Import Oqarina.core.all.

Features Helper Library
========================

The following defines helper functions to manipulate feature of a component

.. coq::

   Definition Is_Input_Port (f : feature) :=
     (DirectionType_beq (projectionFeatureDirection f) inF) ||
     (DirectionType_beq (projectionFeatureDirection f) inoutF).

   Definition Is_Output_Port (f : feature) :=
       DirectionType_beq (projectionFeatureDirection f) outF ||
       DirectionType_beq (projectionFeatureDirection f) inoutF.

   Definition Is_Triggering_Feature (f : feature) :=
     (FeatureCategory_beq (projectionFeatureCategory f) eventPort) ||
     (FeatureCategory_beq (projectionFeatureCategory f) eventDataPort) ||
     (FeatureCategory_beq (projectionFeatureCategory f) subprogramAccess) ||
     (FeatureCategory_beq (projectionFeatureCategory f) subprogramGroupAccess).

   Definition Is_Portb (f : feature) :=
       (FeatureCategory_beq (projectionFeatureCategory f) eventPort) ||
       (FeatureCategory_beq (projectionFeatureCategory f) eventDataPort) ||
       (FeatureCategory_beq (projectionFeatureCategory f) dataPort).

   Definition Is_Port (f: feature) :=
     match f->category with
     | eventPort | eventDataPort | dataPort => True
     | _ => False
     end.

   Definition Is_Triggering_Feature_p (f : feature) :=
     In (projectionFeatureCategory f) [ eventPort ; eventDataPort ;
                                        subprogramAccess ; subprogramGroupAccess].

   Definition Is_Data_Port (f : feature) :=
     (projectionFeatureCategory f) = dataPort.

   Definition Is_Data_Portb (f : feature) : bool :=
     FeatureCategory_beq (projectionFeatureCategory f) dataPort.

   Definition Get_Input_Features (l : list feature) :=
     filter Is_Input_Port l.

   Definition Get_Output_Features (l : list feature) :=
     filter Is_Output_Port l.

   Definition Feature_Classifier (f : feature) :=
     projectionComponentClassifier (projectionFeatureComponent f).
