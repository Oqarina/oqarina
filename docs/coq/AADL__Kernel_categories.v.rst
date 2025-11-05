.. coq::


.. coq:: none

   Section AADL_Categories.

Categories
==========

* The :coq:`ComponentCategory` type denotes AADL component categories.

*Note*: we need to diverge from the AADL standard and add an explicit null component category for the rare situations where we need to define the absence of a component attach to a model element such as an event port.

.. coq::

   Inductive ComponentCategory : Type :=
     (* Hybrid categories *)
     | system | abstract

     (* Software categories *)
     | process | thread | threadGroup | subprogram | subprogramGroup | data

     (* Hardware categories *)
     | processor| virtualProcessor | memory | device | bus | virtualBus

     (* Mechanization addition -- not part of AADL standard *)
     | null (* denote an explicitely null or invalid component *).

* The :coq:`FeatureCategory` type denotes AADL feature categories.

*Note:* The :coq:`invalid` category is an addition used to denote an invalid feature.

.. coq::

   Inductive FeatureCategory : Type :=
     | dataPort | eventPort | eventDataPort | parameter
     | busAccess | virtualBusAccess | dataAccess| subprogramAccess
     | subprogramGroupAccess | featureGroup | abstractFeature

      (* Mechanization addition -- not part of AADL standard *)
     | invalid (* denote an explicitely null or invalid feature *).

   Inductive MetaModelCategory : Type :=
     | connection.

* The :coq:`AppliesToCategory` type is an aggreagate type used in [applies to] clauses in AADL. AADL properties may apply to different categories: components, features, meta model elements, etc. Hence the need for such an aggregate.

.. coq::

   Inductive AppliesToCategory : Type :=
     | CompCat : ComponentCategory -> AppliesToCategory
     | FeatureCat : FeatureCategory -> AppliesToCategory
     | MetaCat : MetaModelCategory -> AppliesToCategory
     | all.

* The :coq:`DirectionType` type denotes AADL feature direction.

*Note:* we had to use the 'F' suffix to avoid conflict with Coq concept :coq:`in`.

.. coq::

   Inductive DirectionType : Type :=
     inF | outF | inoutF | nullDirection.

.. coq:: none

   Scheme Equality for ComponentCategory.
   Scheme Equality for FeatureCategory.
   Scheme Equality for AppliesToCategory.
   Scheme Equality for DirectionType.

   End AADL_Categories.
