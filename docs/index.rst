Oqarina User Guide and Reference Manual
=======================================

This is the documentation for Oqarina, a mechanization of AADL and other
supporting formalisms using the Coq theorem prover :cite:`the_coq_development_team_2022_5846982`.

The following documentation provides a high-level presentation of
Oqarina, along with some details of the Coq code:

* :doc:`examples` is a collection of usage examples of Oqarina

* :doc:`coq/AADL__all.v` provides the core definitions used to represent AADL models

* :doc:`coq/formalisms__all.v` provides the mechanization of additional formalisms used to either analyze or simulate AADL models: DEVS and Fault Trees

*Note*: Oqarina uses a litterate programming approach for documentation. Each chapter is an actual Coq source file. We use Alectryon to produce the documentation :cite:`Alectryon+SLE2020`.

Table of Contents
-----------------

.. toctree::
   :maxdepth: 3
   :name: mastertoc
   :numbered:

   examples.rst
   coq/Categories__all.v.rst
   coq/AADL__all.v.rst
   coq/formalisms__all.v.rst
   coq/MoC__ravenscar.v.rst
   coq/CoqExt__all.v.rst
   references.rst
   genindex.rst