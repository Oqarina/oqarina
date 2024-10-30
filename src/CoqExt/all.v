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
Require Export Oqarina.CoqExt.Classes.
Require Export Oqarina.CoqExt.PeanoNat_Ext.
Require Export Oqarina.CoqExt.Reflexive_Transitive_Closure_Ext.
Require Export Oqarina.CoqExt.strong_ind.
(*| .. coq::  |*)

(*|

**************************************
Extensions to the Coq standard library
**************************************

In the following, we list additional lemmas and definitions that extend the Coq standard library.

Here is the detailed list of contents:

.. toctree::
   :maxdepth: 2

   CoqExt__Classes.v.rst
   CoqExt__PeanoNat_Ext.v.rst
   CoqExt__Reflexive_Transitive_Closure_Ext.v.rst
   CoqExt__strong_ind.v.rst

**********************
Extensions to MathComp
**********************

.. toctree::
   :maxdepth: 2

   CoqExt__finset_Ext.v.rst

*****************************
Extensions to Category-Theory
*****************************

.. toctree::
   :maxdepth: 2

   CoqExt__Category_Ext.v.rst


|*)
