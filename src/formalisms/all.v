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
Require Export Oqarina.formalisms.lts.
(*| .. coq:: |*)

(*|

==========
Formalisms
==========

Oqarina builds on a couple of well-known formalisms to provide analysis or simulation capabilities.

* :doc:`formalisms__DEVS_classic_all.v` is a mechanization of the DEVS simulation formalism in Coq.

* :doc:`formalisms__FaultTrees_all.v` introduces a representation for both static and dynamic Fault Trees, with reduction lemmas and computations.

They rely on the following libraries for internal computations and manipulations:

* :doc:`formalisms__Expressions_Propositions.v` is a representation of propositions, translation to negative and disjunctive normal forms, and computation of minimum cutsets.

* :doc:`formalisms__lts.v` is a basic library for representing and executing Labelled Transition Systems.

* :doc:`formalisms__FaultTrees_Merle_Algebra.v` mechanizes Merle's algebra used in Dynamic Fault Trees manipulation.

* :doc:`formalisms__Contracts_Contracts.v` formalizes contracts meta-theory and some of its instances.

* :doc:`formalisms__Expressions_BoolExpr.v` is a WiP for boolean expressions

Here is the detailed list of contents:

.. toctree::
   :maxdepth: 2

   formalisms__DEVS_classic_all.v.rst
   formalisms__FaultTrees_all.v.rst
   formalisms__Expressions_Propositions.v.rst
   formalisms__Expressions_BoolExpr.v.rst
   formalisms__lts.v.rst
   formalisms__FaultTrees_Merle_Algebra.v.rst
   formalisms__Contracts_Contracts.v.rst

|*)