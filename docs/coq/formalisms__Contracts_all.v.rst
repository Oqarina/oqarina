.. coq::


.. coq:: none

   Require Export Oqarina.formalisms.Contracts.Specification.
   Require Export Oqarina.formalisms.Contracts.MetaTheory.
   Require Export Oqarina.formalisms.Contracts.AG_Contracts.

===============
Contract theory
===============

In this chapter, we mechanize the meta-theory of contracts, along with in Assume/Guarantee instantiation.

In :cite:`DBLP:journals/corr/abs-2108-13647`, the authors propose a mechanization of these contracts using a set-theoretical approach. In our formalization, we opted for the Coq :coq:`Prop` type instead. Ultimately, they are equivalent in that the authors use decidable set appartenance.

In the following, we introduce the following results:

* :doc:`formalisms__Contracts_Specification.v` mechanizes the Specification theory as a collection of typeclasses. We also provide one instance based on :coq:`PropF`.

* :doc:`formalisms__Contracts_MetaTheory.v` provides the core definition of the contract meta-theory from :cite:`benvenisteContractsSystemsDesign`.

* :doc:`formalisms__Contracts_AG_Contracts.v` mechanizes Assume/Guarantee contracts.

Here is the detailed list of contents:

.. toctree::
    :maxdepth: 2

    formalisms__Contracts_Specification.v.rst
    formalisms__Contracts_MetaTheory.v.rst
    formalisms__Contracts_AG_Contracts.v.rst
    formalisms__Contracts_Extended_AG_Contracts.v.rst
