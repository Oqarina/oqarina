.. coq::


.. coq:: none

   Require Export Oqarina.AADL.Kernel.all.
   Require Export Oqarina.AADL.legality.all.
   Require Export Oqarina.AADL.declarative.all.
   Require Export Oqarina.AADL.instance.all.
   Require Export Oqarina.AADL.property_sets.all.
   Require Export Oqarina.AADL.resolute.all.

****
AADL
****

In this chapter, we introduce the key elements of the formalization of AADL in Coq.

* In :doc:`AADL__Kernel_all.v` we mechanize the basic AADL component model.

* In :doc:`AADL__legality_all.v`

* In :doc:`AADL__declarative_all.v`

* In :doc:`AADL__instance_all.v`

* In :doc:`AADL__resolute_all.v`

* In :doc:`AADL__behavior_all.v` we provide a behavioral semantics of AADL component categoeis.

*Note:* some elements are not presented, most notably decidability results since those are trivial.

Here is the detailed list of contents:

.. toctree::
   :maxdepth: 2

   AADL__Kernel_all.v.rst
   AADL__legality_all.v.rst
   AADL__declarative_all.v.rst
   AADL__instance_all.v.rst
   AADL__resolute_all.v.rst
   AADL__behavior_all.v.rst
