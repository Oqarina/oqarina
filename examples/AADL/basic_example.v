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

(* Coq library *)
Require Import List.
Import ListNotations. (* from List *)

Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

(* Oqarina *)
Require Import Oqarina.core.all.
Require Import Oqarina.coq_utils.all.
Require Import Oqarina.AADL.all.
Import AADL_Notations.
Open Scope aadl_scope.

Example A_Component_2 :=
    abstract: "a_component" ->| "pack1::foo_classifier"
        features: [
            feature: in_event "a_feature"   ;
            feature: out_event "a_feature2"
        ]
        subcomponents: [
            thread: "a_thread" ->| "pack2::thread_t"
                features: nil
                subcomponents: nil
                connections: nil
                properties: nil
        ]
        connections: [
            connection: "c1" # "a_feature" --> "a_feature_2"
        ]
        properties: nil.

Definition A_Sporadic_Thread' :=
    thread: "a_sporadic_thread" ->| "pack::a_sporadic_thread_classifier.impl"
        features: [
            feature: in_event "a_feature"
        ]
        subcomponents: nil
        connections: nil
        properties: [
            property: Priority_Name ==>| PV_Int 42 ;
            property: Dispatch_Protocol_Name ==>| PV_Enum (Id "Sporadic") ;
            property: Period_Name ==>| PV_IntU 3 (PV_Unit (Id "ms"))
        ].

Lemma a_sporadic_thread_wf :
    Well_Formed_Component_Instance A_Sporadic_Thread'.
Proof.
    prove_Well_Formed_Component_Instance.
Qed.
