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
Require Export Oqarina.AADL.Kernel.all.
Require Export Oqarina.AADL.legality.all.
Require Export Oqarina.AADL.declarative.all.
Require Export Oqarina.AADL.instance.all.
Require Export Oqarina.AADL.property_sets.all.
Require Export Oqarina.AADL.resolute.all.
(*| .. coq:: |*)

(*|

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

|*)