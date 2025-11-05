.. coq::


.. coq:: none

   Require Import Coq.Strings.String.
   Require Import Oqarina.core.all.
   Require Import Oqarina.CoqExt.all.

   Require Export Oqarina.AADL.Kernel.categories.
   Require Export Oqarina.AADL.Kernel.component.
   Require Export Oqarina.AADL.Kernel.components_helper.
   Require Export Oqarina.AADL.Kernel.properties.
   Require Export Oqarina.AADL.Kernel.typecheck.
   Require Export Oqarina.AADL.Kernel.properties_helper.
   Require Export Oqarina.AADL.Kernel.features_helper.
   Require Export Oqarina.AADL.Kernel.package.
   Require Export Oqarina.AADL.Kernel.notations.

   Definition Time := nat.

AADL Kernel
===========

In this section, we first introduce the kernel of AADL, capturing the static semantics of the AADL language.

* In :doc:`AADL__Kernel_categories.v` we define the main component categories;

* In :doc:`AADL__Kernel_component.v`

* In :doc:`AADL__Kernel_package.v`

* :doc:`AADL__Kernel_properties.v`

* :doc:`AADL__Kernel_components_helper.v`

* :doc:`AADL__Kernel_features_helper.v`

* :doc:`AADL__Kernel_properties_helper.v`

* :doc:`AADL__Kernel_notations.v`

Here is the detailed list of contents:

.. toctree::
    :maxdepth: 2

    AADL__Kernel_categories.v.rst
    AADL__Kernel_component.v.rst
    AADL__Kernel_package.v.rst
    AADL__Kernel_properties.v.rst
    AADL__Kernel_components_helper.v.rst
    AADL__Kernel_features_helper.v.rst
    AADL__Kernel_properties_helper.v.rst
    AADL__Kernel_notations.v.rst
