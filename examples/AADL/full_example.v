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

(* In this second example, we show how to leverage Coq language to build
modular models. First, we define an isolated components a periodic thread. *)

Definition A_Periodic_Thread :=
    thread: "a_periodic_thread" ->| "pack::a_thread_classifier"
        features: nil
        subcomponents: nil
        connections: nil
        properties: [
            property: Priority_Name ==> PV_Int 42 ;
            property: Dispatch_Protocol_Name ==> PV_Enum (Id "Periodic") ;
            property: Period_Name ==> PV_IntU 3 (PV_Unit (Id "ms"))
        ].

(* Using Coq variables, one can then combine model elements to build a full hierarchy. *)

Definition A_Process :=
    process: "a_process" ->| "pack::a_process_classifier"
    features: nil
    subcomponents: [ A_Periodic_Thread ]
    connections: nil
    properties: [
        property: Actual_Processor_Binding_Name ==>
            PV_ModelRef [ Id "a_processor" ]
    ].

Definition A_Processor :=
    processor: "a_processor" ->| "pack::a_processor_classifier"
    features: nil
    subcomponents: nil
    connections: nil
    properties: nil.

Definition A_System :=
    system: "a_system" ->| "pack::a_system_classifier"
    features: nil
    subcomponents: [ A_Process ; A_Processor ]
    connections: nil
    properties: nil.

(* We show that the resulting system is well-formed *)

Lemma a_system_wf :
    Well_Formed_Component_Instance A_System.
Proof.
    prove_Well_Formed_Component_Instance.
Qed.

(* Some subcomponent resolution *)

Lemma Resolva_A_Processor:
    Resolve_Subcomponent A_System (FQN [] (Id "a_processor") None) = Some A_Processor.
Proof.
    trivial.
Qed.

Lemma Resolve_A_Periodic_Thread:
    Resolve_Subcomponent A_System (FQN [ Id "a_process" ] (Id "a_periodic_thread") None) = Some A_Periodic_Thread.
Proof. trivial. Qed.
