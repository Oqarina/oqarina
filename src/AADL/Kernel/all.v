(***
 * Oqarina
 * Copyright 2021 Carnegie Mellon University.
 *
 * NO WARRANTY. THIS CARNEGIE MELLON UNIVERSITY AND SOFTWARE ENGINEERING
 * INSTITUTE MATERIAL IS FURNISHED ON AN "AS-IS" BASIS. CARNEGIE MELLON
 * UNIVERSITY MAKES NO WARRANTIES OF ANY KIND, EITHER EXPRESSED OR
 * IMPLIED, AS TO ANY MATTER INCLUDING, BUT NOT LIMITED TO, WARRANTY OF
 * FITNESS FOR PURPOSE OR MERCHANTABILITY, EXCLUSIVITY, OR RESULTS
 * OBTAINED FROM USE OF THE MATERIAL. CARNEGIE MELLON UNIVERSITY DOES NOT
 * MAKE ANY WARRANTY OF ANY KIND WITH RESPECT TO FREEDOM FROM PATENT,
 * TRADEMARK, OR COPYRIGHT INFRINGEMENT.
 *
 * Released under a BSD (SEI)-style license, please see license.txt or
 * contact permission@sei.cmu.edu for full terms.
 *
 * [DISTRIBUTION STATEMENT A] This material has been approved for public
 * release and unlimited distribution.  Please see Copyright notice for
 * non-US Government use and distribution.
 *
 * This Software includes and/or makes use of the following Third-Party
 * Software subject to its own license:
 *
 * 1. Coq theorem prover (https://github.com/coq/coq/blob/master/LICENSE)
 * Copyright 2021 INRIA.
 *
 * 2. Coq JSON (https://github.com/liyishuai/coq-json/blob/comrade/LICENSE)
 * Copyright 2021 Yishuai Li.
 *
 * DM21-0762
***)

(*| .. coq:: none |*)
Require Import Coq.Strings.String.
Require Import Oqarina.core.all.

Require Export Oqarina.AADL.Kernel.categories.
Require Export Oqarina.AADL.Kernel.component.
Require Export Oqarina.AADL.Kernel.components_helper.
Require Export Oqarina.AADL.Kernel.properties.
Require Export Oqarina.AADL.Kernel.typecheck.
Require Export Oqarina.AADL.Kernel.properties_helper.
Require Export Oqarina.AADL.Kernel.features_helper.
Require Export Oqarina.AADL.Kernel.notations.

(*| .. coq:: |*)

(*|
AADL Kernel
===========

In this section, we first introduce the kernel of AADL, capturing the static semantics of the AADL language.

* In :doc:`AADL__Kernel_categories.v` we define the main component categories;

* In :doc:`AADL__Kernel_component.v`

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
    AADL__Kernel_properties.v.rst
    AADL__Kernel_components_helper.v.rst
    AADL__Kernel_features_helper.v.rst
    AADL__Kernel_properties_helper.v.rst
    AADL__Kernel_notations.v.rst
|*)
