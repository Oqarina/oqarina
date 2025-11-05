.. coq::


.. coq:: none

   Require Export Oqarina.AADL.legality.categories_wf.
   Require Export Oqarina.AADL.legality.component_wf.
   Require Export Oqarina.AADL.legality.connections_wf.
   Require Export Oqarina.AADL.legality.features_wf.
   Require Export Oqarina.AADL.legality.properties_wf.
   Require Import Oqarina.core.tactics.

   Global Hint Resolve
       Well_Formed_Component_Type_Interface_dec
       Well_Formed_Component_dec
       Well_Formed_Component_Id_dec
       Well_Formed_Component_Classifier_dec
       Well_Formed_Component_Features_dec
       Well_Formed_Property_Associations_dec
       Rule_4_5_N1_dec
   : well_know_wf_dec.

Legality rules
===============

In this chapter, we define AADL legality rules as a collection of decidable propositions.

.. toctree::
    :maxdepth: 2

    AADL__legality_component_wf.v.rst
    AADL__legality_features_wf.v.rst
    AADL__legality_categories_wf.v.rst
    AADL__legality_connections_wf.v.rst
    AADL__legality_properties_wf.v.rst
