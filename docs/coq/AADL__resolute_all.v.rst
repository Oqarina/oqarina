.. coq::


.. coq:: none

   Require Export Oqarina.AADL.resolute.resolute.

   Global Hint Resolve has_property_c_dec is_thread_dec: well_know_wf_dec.

Resolute Annex
===============

In this chapter, we show how to implement most of Resolute API in Coq.

.. toctree::
    :maxdepth: 2

    AADL__resolute_resolute.v.rst
