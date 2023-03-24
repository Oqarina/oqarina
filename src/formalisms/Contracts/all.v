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
Require Export Oqarina.formalisms.Contracts.Specification.
Require Export Oqarina.formalisms.Contracts.MetaTheory.
Require Export Oqarina.formalisms.Contracts.AG_Contracts.
(*| .. coq:: |*)

(*|
===============
Contract theory
===============

In this chapter, we mechanize the meta-theory of contracts, along with in Assume/Guarantee instantiation.

In :cite:`DBLP:journals/corr/abs-2108-13647`, the authors propose a mechanization of these contracts using a set-theoretical approach. In our formalization, we opted for the Coq :coq:`Prop` type instead. Ultimately, they are equivalent in that the authors use decidable set appartenance.

In the following, we introduce the following results:

* :doc:`formalisms__Contracts_Specification.v` mechanizes the Specification theory as a collection of typeclasses. We also provide one instance based on :coq:`PropF`.

* :doc:`formalisms__Contracts_MetaTheory.v` provides the core definition of the contract meta-theory from :cite:`benvenisteContractsSystemsDesign`.

* :doc:`formalisms__Contracts_AG_Contracts.v` mechanizes Assume/Guarantee contracts.

|*)