.. coq::


.. coq:: none

   Require Export Oqarina.formalisms.lts.

==========
Formalisms
==========

Oqarina builds on a couple of well-known formalisms to provide analysis or simulation capabilities.

* :doc:`formalisms__DEVS_classic_all.v` is a mechanization of the DEVS simulation formalism in Coq.

* :doc:`formalisms__DEVS_parallel_all.v` is a mechanization of the P-DEVS simulation formalism in Coq.

* :doc:`formalisms__FaultTrees_all.v` introduces a representation for both static and dynamic Fault Trees, with reduction lemmas and computations.

They rely on the following libraries for internal computations and manipulations:

* :doc:`formalisms__Expressions_Propositions.v` is a representation of propositions, translation to negative and disjunctive normal forms, and computation of minimum cutsets.

* :doc:`formalisms__lts.v` is a basic library for representing and executing Labelled Transition Systems.

* :doc:`formalisms__FaultTrees_Merle_Algebra.v` mechanizes Merle's algebra used in Dynamic Fault Trees manipulation.

* :doc:`formalisms__Contracts_all.v` formalizes contracts meta-theory and some of its instances.

* :doc:`formalisms__Expressions_BoolExpr.v` is a WiP for boolean expressions

Here is the detailed list of contents:

.. toctree::
   :maxdepth: 2

   formalisms__DEVS_classic_all.v.rst
   formalisms__DEVS_parallel_all.v.rst
   formalisms__FaultTrees_all.v.rst
   formalisms__Expressions_Propositions.v.rst
   formalisms__Expressions_BoolExpr.v.rst
   formalisms__lts.v.rst
   formalisms__FaultTrees_Merle_Algebra.v.rst
   formalisms__Contracts_all.v.rst
