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

Require Import Oqarina.coq_utils.all.
Require Import Oqarina.core.all.
Import NaturalTime.
Require Import Oqarina.formalisms.devs_classic.
Require Import Oqarina.formalisms.devs_coupled.
Require Import Oqarina.formalisms.lts.

Section Traffic_Light.

(*

Traffic Light example
=====================

In this section, we model the traffic light example from
:math:`\cite{vantendelooIntroductionClassicDEVS2018}`. This example is a direct transcription in Coq of the various types and functions definitions and yield no complexity. It is kept for testing and documentation purposes.

*)

Inductive X_tl :=
    | toAuto | toManual.

Inductive Y_tl :=
    | show_green | show_yellow | show_red | turn_off.

Inductive S_tl :=
    | GREEN | YELLOW | RED | GOING_MANUAL | GOING_AUTO | MANUAL.

Definition Q_tl : Type := Q S_tl.

Definition Q_init_tl : Q_tl := {| st := GREEN ; e := 0 |}.

Definition δint_tl (s : S_tl) : S_tl :=
    match s with
        | GREEN => YELLOW
        | YELLOW => RED
        | RED => GREEN
        | GOING_MANUAL => MANUAL
        | GOING_AUTO => RED
        | _ => s
    end.

Definition δext_tl (q : Q_tl) (x : X_tl) : S_tl :=
    match q.(st), x  with
        | GREEN,toManual => GOING_MANUAL
        | YELLOW, toManual => GOING_MANUAL
        | RED,toManual => GOING_MANUAL
        | MANUAL, toAuto => GOING_AUTO
        |  _, _ => q.(st)
    end.

Definition Y_output_tl : Type := Y_output Y_tl.

Definition λ_tl (s : S_tl) : Y_output_tl :=
    match s with
        | GREEN  => y show_yellow
        | YELLOW  => y show_red
        | RED  => y show_green
        | GOING_MANUAL  => y turn_off
        | GOING_AUTO  => y show_red
        | _ => no_output Y_tl
    end.

Definition ta_tl (s : S_tl) : Time :=
    match s with
        | GREEN  => 1
        | YELLOW  => 2
        | RED  => 3
        | GOING_MANUAL  => 0
        | GOING_AUTO  => 0
        | MANUAL => 10 (* infinity *)
    end.

(* From these specifications, we define the corresponding Coq data types.
First, a type representing the interface of a TrafficLight_Devs
(:coq:`TrafficLight_DEVS_Type`), then the DEVS atomic model itself.
*)

Definition TrafficLight_DEVS_type : Type := DEVS_Atomic_Model S_tl X_tl Y_tl.

Definition TrafficLight_DEVS : TrafficLight_DEVS_type := {|
    devs_atomic_id := (Id "TrafficLight");

    Q_init := Q_init_tl;

    ta := ta_tl;
    δint := δint_tl;
    λ := λ_tl ;
    δext := δext_tl;
|}.

(* Then, we instantiate the DEVS model to build on instance, or simulator. *)

Definition TrafficLight_DEVS_Simulator_type : Type :=
    DEVS_Simulator S_tl X_tl Y_tl.

Definition TL_Initial := Instantiate_DEVS_Simulator
    (Id "TrafficLighti") TrafficLight_DEVS.

(* From that point, we can simulate the Traffic Light. *)

Definition TL_Coordinator := Iniitialize_DEVS_Root_Coordinator TL_Initial.

Definition TLC_Step1 := DEVS_Simulation_Step TL_Coordinator.
Lemma TLC_Step1_OK :
    (Print_DEVS_State TLC_Step1) = dbg 0 1 GREEN [].
Proof.
    trivial.
Qed.

Definition TLC_Step2 := DEVS_Simulation_Step TLC_Step1.
Lemma TLC_Step2_OK :
    (Print_DEVS_State TLC_Step2) = dbg 1 3 YELLOW [].
Proof.
    trivial.
Qed.

Definition TLC_Step3 := DEVS_Simulation_Step TLC_Step2.
Lemma TLC_Step3_OK :
    (Print_DEVS_State TLC_Step3) = dbg 3 6 RED [].
Proof.
    trivial.
Qed.

Definition TLC_Step4 := DEVS_Simulation_Step TLC_Step3.
Lemma TLC_Step4_OK :
    (Print_DEVS_State TLC_Step4) = dbg 6 7 GREEN [].
Proof.
    trivial.
Qed.

(* LTS variant of the Traffic LIght DEVS. We introduce a variant of the step
function that drops the output to compare the states with the previous
simulation run.*)

Definition TL_LTS := LTS_Of_DEVS TL_Initial.

Definition step_TL_LTS
    (m : Synchronization_Message_Type X_tl Y_tl)
    (s : States TL_LTS) : States TL_LTS
:=
    let s := step_lts TL_LTS s m in
    DEVS_Reset_Outputs s.

Example TL_LTS_1 := iterate (step_TL_LTS (i X_tl Y_tl 0)) 1 (Init TL_LTS).
Compute Print_DEVS_Simulator TL_LTS_1.

Lemma TL_LTS_1_OK :
    Print_DEVS_Simulator TL_LTS_1 = Print_DEVS_Simulator TLC_Step1.(astate).
Proof.
    trivial.
Qed.

End Traffic_Light.
(*| .. coq:: |*)

Section Traffic_Light_Coupled.
(*

Traffic Light example
=====================

In this section, we build a naive coupled DEVS model out of the Traffic Light example. The coupled model is made of a single node. We use this as a first verification step that the coupled DEVS model made of one atonmic model has the same behavior.

*)

Definition Traffic_Light_Coupled := {|
    devs_coupled_model_id := Id "traffic_light_coupled" ;
    D := [ TL_Initial ] ;
    Select := @Default_Select_Function S_tl X_tl Y_tl ;
    Z_f :=  (fun (i : identifier) (y : Y_output_tl) => toManual) ;
    I := Default_I_Function;
|}.

Definition TL_coupled_atomic := Map_DEVS_Coupled_Model Traffic_Light_Coupled.

Definition TL_coupled_initial :=
    Instantiate_DEVS_Simulator (Id "traffic_light_coupled_instance")
    TL_coupled_atomic.

Definition TL_Coordinator_coupled := Iniitialize_DEVS_Root_Coordinator TL_coupled_initial.

Definition TLCC_Step1 := DEVS_Simulation_Step TL_Coordinator_coupled.
Lemma TLCC_Step1_OK :
    (Print_DEVS_Simulator TLCC_Step1.(astate)) =
        dbg 0 1 [{| st := GREEN; e := 0 |}] [].
Proof.
    trivial.
Qed.

Definition TLCC_Step2 := DEVS_Simulation_Step TLCC_Step1.
Lemma TLCC_Step2_OK :
    (Print_DEVS_Simulator TLCC_Step2.(astate)) =
    dbg 1 3 [{| st := YELLOW; e := 0 |}] [].
Proof.
    trivial.
Qed.

Definition TLCC_Step3 := DEVS_Simulation_Step TLCC_Step2.
Lemma TLCC_Step3_OK :
    (Print_DEVS_Simulator TLCC_Step3.(astate)) =
    dbg 3 6 [{| st := RED; e := 0 |}] [].
Proof.
    trivial.
Qed.

Definition TLCC_Step4 := DEVS_Simulation_Step TLCC_Step3.
Lemma TLCC_Step4_OK :
    (Print_DEVS_Simulator TLCC_Step4.(astate)) =
    dbg 6 7 [{| st := GREEN; e := 0 |}] [].
Proof.
    trivial.
Qed.

End Traffic_Light_Coupled.
(*| .. coq:: |*)
