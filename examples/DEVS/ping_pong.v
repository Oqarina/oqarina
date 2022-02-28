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

Section Ping_Pong.

(*

Ping pong example
==================

In this example, we build a ping pong game simulation. We first define a
DEVS for a player, then a coupled model made of two players.

*)

Inductive X_pp := receive.
Inductive Y_pp := send.
Inductive S_pp' := Wait | Send.

Scheme Equality for S_pp'.

Record S_pp := { s_pp : S_pp'; sigma : Time }.

Definition Q_pp : Type := Q S_pp.

Definition Q_init_pp : Q_pp :=
     {| st:= {| s_pp := Wait ; sigma := 1 |} ;
        e := 0 |}.

Definition δint_pp (s : S_pp) : S_pp :=
    match s with
        | Build_S_pp Send 1 => Build_S_pp Wait 1000 (* XXX should be infinity*)
        | Build_S_pp Wait 1 => Build_S_pp Send 1
        | Build_S_pp s0 sig0 => Build_S_pp s0 sig0
    end.

Definition δext_pp (q : Q_pp) (x : X_pp) : S_pp :=
    match q.(st), x  with
    | Build_S_pp Wait _, receive => Build_S_pp Send 1
    | _, _ => q.(st)
    end.

Definition Y_output_pp : Type := Y_output Y_pp.

Definition λ_pp (s : S_pp) : Y_output_pp :=
    match s with
    | Build_S_pp Send _ => y send
    | _ => no_output Y_pp
    end.

Definition ta_pp (s : S_pp) : Time := 1.

Definition PingPoing_DEVS_type : Type := DEVS_Atomic_Model S_pp X_pp Y_pp.

Definition PingPong_DEVS : PingPoing_DEVS_type := {|
    devs_atomic_id := Id "ping_pong_player" ;
    Q_init := Q_init_pp;

    ta := ta_pp;
    δint := δint_pp;
    λ  := λ_pp;
    δext := δext_pp;
|}.

Definition PingPong_DEVS_Simulator_type : Type :=
    DEVS_Simulator S_pp X_pp Y_pp.

(* Player A is serving, it stars in the Send state. Player B is receiving, and starts int he default Wait state. *)

Definition Player_A_Q_Init :=
    {| st:= {| s_pp := Send ; sigma := 1 |} ;
       e := 0 |}.

Definition Player_A := Instantiate_DEVS_Simulator
    (Id "playerA") (Set_Q_Init PingPong_DEVS Player_A_Q_Init).

Definition Player_B := Instantiate_DEVS_Simulator
    (Id "playerB") PingPong_DEVS.

Definition Ready_To_Send (p : S_pp) :=
    S_pp'_beq p.(s_pp) Send.

Definition Select_Function_pp : Select_Function S_pp X_pp Y_pp :=
    fun (l : list (PingPong_DEVS_Simulator_type * (Q S_pp))) =>
    let l' := filter
            (fun (x : (PingPong_DEVS_Simulator_type * (Q S_pp))) =>
                Ready_To_Send (snd x).(st)) l in
        hd_error l'.

Definition Z_Function_pp : Z_Function X_pp Y_pp :=
    fun ( id : identifier) ( y : Y_output Y_pp)  =>
    match y with
    | y send  => receive
    | _ => receive (* stupid XXX *)
    end.

(* Player A is sending to Player B and vice versa. *)

Definition I_pp : I_Function :=
    fun (x : identifier) =>
    match x with
        | (Id "playerA"%string) => [ Id "playerB"%string ]
        | (Id "playerB"%string) => [ Id "playerA"%string ]
        | _ => [empty_identifier]
    end.

(* Definition of the coupled DEVS, derivation of the corresponding
atomic DEVS. *)

Definition Ping_Pong_Coupled := {|
    devs_coupled_model_id := Id "ping_pong_coupled" ;
    D := [ Player_A ; Player_B ] ;
    Select := Select_Function_pp ;
    Z_f := Z_Function_pp ;
    I := I_pp;
|}.

Definition PP_coupled_atomic := Map_DEVS_Coupled_Model Ping_Pong_Coupled.

(* From this point, we can check that the behavior is the one we expect, that is an alternance of Player A and B sending the ball. *)

Definition PP_coupled_initial :=
    Instantiate_DEVS_Simulator (Id "ping_pong_coupled_instance")
    PP_coupled_atomic.

Definition PPCC_Step0 :=
    Iniitialize_DEVS_Root_Coordinator PP_coupled_initial.
Lemma PPCC_Step0_OK :
    Print_DEVS_Simulator PPCC_Step0.(astate) =
    dbg 0 0
            [{| st := {| s_pp := Send; sigma := 1 |}; e := 0 |};
            {| st := {| s_pp := Wait; sigma := 1 |}; e := 0 |}] [].
Proof.
    trivial.
Qed.

Definition PPCC_Step1 := DEVS_Simulation_Step PPCC_Step0.
Lemma PPCC_Step1_OK :
    Print_DEVS_Simulator PPCC_Step1.(astate) =
    dbg 0 1
         [{| st := {| s_pp := Send; sigma := 1 |}; e := 0 |};
         {| st := {| s_pp := Wait; sigma := 1 |}; e := 0 |}] [].
Proof.
    trivial.
Qed.

Definition PPCC_Step2 := DEVS_Simulation_Step PPCC_Step1.
Lemma PPCC_Step2_OK :
    Print_DEVS_Simulator PPCC_Step2.(astate) =
    dbg 1 2
         [{| st := {| s_pp := Wait; sigma := 1000 |}; e := 0 |};
         {| st := {| s_pp := Send; sigma := 1 |}; e := 0 |}] [].
Proof.
    trivial.
Qed.

Definition PPCC_Step3 := DEVS_Simulation_Step PPCC_Step2.
Lemma PPCC_Step3_OK :
    Print_DEVS_Simulator PPCC_Step3.(astate) =
    dbg 2 3
         [{| st := {| s_pp := Send; sigma := 1 |}; e := 0 |};
         {| st := {| s_pp := Wait; sigma := 1000 |}; e := 0 |}] [].
Proof.
    trivial.
Qed.

Definition PPCC_Step4 := DEVS_Simulation_Step PPCC_Step3.
Lemma PPCC_Step4_OK :
    Print_DEVS_Simulator PPCC_Step4.(astate) =
    dbg 3 4
         [{| st := {| s_pp := Wait; sigma := 1000 |}; e := 0 |};
         {| st := {| s_pp := Send; sigma := 1 |}; e := 0 |}] [].
Proof.
    trivial.
Qed.

Definition PPCC_Step5 := DEVS_Simulation_Step PPCC_Step4.
Lemma PPCC_Step5_OK :
    Print_DEVS_Simulator PPCC_Step5.(astate) =
    dbg 4 5
         [{| st := {| s_pp := Send; sigma := 1 |}; e := 0 |};
         {| st := {| s_pp := Wait; sigma := 1000 |}; e := 0 |}] [].
Proof.
    trivial.
Qed.

End Ping_Pong.