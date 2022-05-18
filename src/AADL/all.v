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

*********
AADL Core
*********

In this chapter, we introduce the key elements of the formalization of AADL in Coq.

*Note:* some elements are not presented, most notably decidability results since those are trivial.

.. include::  AADL__Kernel_categories.v.rst
.. include::  AADL__Kernel_component.v.rst
.. include::  AADL__resolute_resolute.v.rst

*************************
AADL Behavioral semantics
*************************

In this chapter, we leverage the previous definitions of AADL concepts and provide a description of the behavioral semantics of AADL. This description starts with the description of AADL port variables, representing features, then present AADL runtime services to finally present the semantics of each components category.

.. include::  AADL__behavior_port_variable.v.rst
.. include::  AADL__behavior_thread.v.rst
.. include::  AADL__behavior_system.v.rst

|*)