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

Require Import Coq.Lists.List.
Import ListNotations. (* from List *)
Require Import Lia.
Require Import Oqarina.core.all.
Require Import Oqarina.AADL.Kernel.all.
Require Import Oqarina.AADL.behavior.all.
Import AADL_Notations.
Require Import Oqarina.formalisms.DEVS.parallel.all.
Require Import Oqarina.formalisms.all.
Open Scope bool_scope.
(* Test #1: Translate DEVS to a LTS *)

Definition System_LTS := system_DEVS_LTS.

Example System_LTS_1 :=
    step_lts (Init System_LTS) (i X_system Y_system 0).

Lemma System_LTS_1_OK :
    Print_DEVS_Simulator System_LTS_1 = dbg 0 1 system_offline [].
Proof. trivial. Qed.

Example System_LTS_2 :=
    step_lts System_LTS_1 (xs Y_system Parent Parent 1 [ start_system ]).

Lemma System_LTS_2_OK :
    Print_DEVS_Simulator System_LTS_2 = dbg 1 2 system_starting [].
Proof. trivial. Qed.

(* Test#2: Map An_AADL_System to an LTS *)

Example An_AADL_System :=
    system: "a_system" ->| "pack::a_system_classifier"
    extends: None
    features: nil
    subcomponents: [
        system: "a_subsystem" ->| "pack::a_system_classifier"
            extends: None
            features: nil
            subcomponents: nil
            connections: nil
            properties: nil ;
        system: "a_subsystem2" ->| "pack::a_system_classifier"
            extends: None
            features: nil
            subcomponents: nil
            connections: nil
            properties: nil
    ]
    connections: nil
    properties: nil.

Definition An_AADL_System_Coupled_Model :=
    Map_AADL_Root_System_to_Coupled_DEVS An_AADL_System.
(* Keep for debugging purposes *)

Example An_AADL_System_LTS :=
    LTS_Of_DEVS (Map_AADL_Root_to_DEVS An_AADL_System).

Example An_AADL_System_LTS_1 :=
    step_lts (Init An_AADL_System_LTS) (i X_system Y_system 0).

(* After initialization, both system are offline *)
Fact An_AADL_System_LTS_1_OK :
    Print_DEVS_Simulator An_AADL_System_LTS_1 =
    dbg 0 1
         [{| st := system_offline; e := 0 |};
         {| st := system_offline; e := 0 |};
         {| st := system_offline; e := 0 |}] [].
Proof. trivial. Qed.

Example An_AADL_System_LTS_2 :=
    step_lts An_AADL_System_LTS_1 (xs Y_system Parent Parent 1 [start_system]).

(* After the first step, the first system is starting *)
Fact Am_AADL_System_LTS_2_OK :
    Print_DEVS_Simulator An_AADL_System_LTS_2 =
    dbg 1 2
         [{| st := system_starting; e := 0 |};
         {| st := system_offline; e := 0 |};
         {| st := system_offline; e := 0 |}] [].
Proof. trivial. Qed.

Example An_AADL_System_LTS_3 :=
    step_lts An_AADL_System_LTS_2 (step X_system Y_system 2).

(* After the second step, both systems are in the starting state *)
Fact Am_AADL_System_LTS_3_OK :
    Print_DEVS_Simulator An_AADL_System_LTS_3 =
    dbg 1 2
         [{| st := system_starting; e := 0 |};
         {| st := system_offline; e := 0 |};
         {| st := system_offline; e := 0 |}] [].
Proof. trivial. Qed.

Example An_AADL_System_LTS_4 :=
    step_lts An_AADL_System_LTS_3 (xs Y_system Parent Parent 2 []).

Fact Am_AADL_System_LTS_4_OK :
    Print_DEVS_Simulator An_AADL_System_LTS_4 =
    dbg 2 3
         [{| st := system_starting; e := 0 |};
         {| st := system_starting; e := 0 |};
         {| st := system_starting; e := 0 |}]
         [].
Proof. trivial. Qed.

Example An_AADL_System_LTS_5 :=
    step_lts An_AADL_System_LTS_4 (xs Y_system Parent Parent 3 [ started_system ]).

Fact Am_AADL_System_LTS_5_OK :
    Print_DEVS_Simulator An_AADL_System_LTS_5 =
    dbg 3 4
         [{| st := system_operational; e := 0 |};
         {| st := system_starting; e := 0 |};
         {| st := system_starting; e := 0 |}]
         [].
Proof. trivial. Qed.

Example An_AADL_System_LTS_6 :=
    step_lts An_AADL_System_LTS_5 (xs Y_system Parent Parent 4 []).

Fact Am_AADL_System_LTS_6_OK :
    Print_DEVS_Simulator An_AADL_System_LTS_6 =
    dbg 4 5
         [{| st := system_operational; e := 0 |};
         {| st := system_operational; e := 0 |};
         {| st := system_operational; e := 0 |}]
         [].
Proof. trivial. Qed.

(** Recursive example *)

Example An_AADL_System2 :=
    system: "a_system" ->| "pack::a_system_classifier"
    extends: None
    features: nil
    subcomponents: [
        system: "a_subsystem" ->| "pack::a_system_classifier"
            extends: None
            features: nil
            subcomponents: [
                system: "a_subsubsystem" ->| "pack::a_system_classifier"
                    extends: None
                    features: nil
                    subcomponents: nil
                    connections: nil
                    properties: nil
            ]
            connections: nil
            properties: nil ;
        system: "a_subsystem2" ->| "pack::a_system_classifier"
            extends: None
            features: nil
            subcomponents: nil
            connections: nil
            properties: nil
    ]
    connections: nil
    properties: nil.

Definition An_AADL_System_Coupled_Model_2 :=
    Map_AADL_Root_System_to_Coupled_DEVS An_AADL_System2.
(* Keep for debugging purposes *)

Example An_AADL_System_LTS' :=
    LTS_Of_DEVS (Map_AADL_Root_to_DEVS An_AADL_System2).

Example An_AADL_System_LTS_1' :=
    step_lts (Init An_AADL_System_LTS') (i X_system Y_system 0).

(* After initialization, all systems are offline *)
Fact Am_AADL_System_LTS_1_OK' :
    Print_DEVS_Simulator An_AADL_System_LTS_1' =
    dbg 0 1
         [{| st := system_offline; e := 0 |};
         {| st := system_offline; e := 0 |};
         {| st := system_offline; e := 0 |};
         {| st := system_offline; e := 0 |}] [].
Proof. trivial. Qed.

Example An_AADL_System_LTS_2' :=
    step_lts An_AADL_System_LTS_1' (xs Y_system Parent Parent 1 [start_system]).

(* After the first step, the first system is starting *)
Fact Am_AADL_System_LTS_2_OK' :
    Print_DEVS_Simulator An_AADL_System_LTS_2' =
    dbg 1 2
         [{| st := system_starting; e := 0 |};
         {| st := system_offline; e := 0 |};
         {| st := system_offline; e := 0 |};
         {| st := system_offline; e := 0 |}] [].
Proof. trivial. Qed.

Example An_AADL_System_LTS_3' :=
    step_lts An_AADL_System_LTS_2' (xs Y_system Parent Parent 2 []).

(* After the second step, both systems are in the starting state *)
Fact Am_AADL_System_LTS_3_OK' :
    Print_DEVS_Simulator An_AADL_System_LTS_3' =
    dbg 2 3
         [{| st := system_starting; e := 0 |};
         {| st := system_starting; e := 0 |};
         {| st := system_offline; e := 0 |};
         {| st := system_starting; e := 0 |}]
         [].
Proof. trivial. Qed.

Example An_AADL_System_LTS_4' :=
    step_lts An_AADL_System_LTS_3' (xs Y_system Parent Parent 3 []).

Fact Am_AADL_System_LTS_4_OK' :
    Print_DEVS_Simulator An_AADL_System_LTS_4' =
    dbg 3 4
         [{| st := system_starting; e := 0 |};
         {| st := system_starting; e := 0 |};
         {| st := system_starting; e := 0 |};
         {| st := system_starting; e := 0 |}] [].
Proof. trivial. Qed.
