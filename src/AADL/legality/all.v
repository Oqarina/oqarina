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
Require Export Oqarina.AADL.legality.categories_wf.
Require Export Oqarina.AADL.legality.component_wf.
Require Export Oqarina.AADL.legality.connections_wf.
Require Export Oqarina.AADL.legality.features_wf.
Require Export Oqarina.AADL.legality.properties_wf.
Require Import Oqarina.core.tactics.

Global Hint Resolve
    Well_Formed_Component_Type_Interface_dec
    Well_Formed_Component_dec
    Well_Formed_Component_Id_dec
    Well_Formed_Component_Classifier_dec
    Well_Formed_Component_Features_dec
    Well_Formed_Property_Associations_dec
    Rule_4_5_N1_dec
: well_know_wf_dec.
(*| .. coq:: |*)

(*|

Legality rules
===============

In this chapter, we define AADL legality rules as a collection of decidable propositions.

.. toctree::
    :maxdepth: 2

    AADL__legality_component_wf.v.rst
    AADL__legality_features_wf.v.rst
    AADL__legality_categories_wf.v.rst
    AADL__legality_connections_wf.v.rst
    AADL__legality_properties_wf.v.rst

|*)
