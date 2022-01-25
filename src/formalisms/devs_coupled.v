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
Require Import Coq.Init.Datatypes.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations. (* from List *)
Import IfNotations.
Require Import Coq.Lists.ListSet.

Require Import Oqarina.core.all.
Import NaturalTime.
Require Import Oqarina.AADL.property_sets.all.
Require Import Oqarina.coq_utils.all.
Require Import Oqarina.formalisms.lts.
Require Import Oqarina.formalisms.devs_classic.
#[local] Open Scope bool_scope.
Set Implicit Arguments.

Section DEVS_Coupled.
(*| .. coq:: |*)

(*|

Coupled models
--------------

Coupled models represent a hierarchy of DEVS model.

A coupled DEVS model is an 8-tuple :math:`$M=<X,Y,D,\{M_{i}\},Z_{{i, self}},Select>$` where

    * X is the set of input events;
    * Y is the set of output events;
    * D is the name set of sub-components;
    * :math:`\{M_{i}\}` is the set of sub-components where for each i ∈ D,  :math:`i\in D,M_{i}` is an atomic DEVS model.
    * :math:`Select:2^{D}\rightarrow D` is the tie-breaking function which defines how to select the event from the set of simultaneous events;
    * I = model influencees

|*)

(*| .. coq:: none |*)
Variable S : Type.                  (* State Set (S) *)
Variable X : Type.                  (* Input Set (X) *)
Variable Y : Type.                  (* Output Set (Y) *)

(*| .. coq:: |*)

(*| The state of the resulting DEVS is the combination of the states of all DEVS. From these considerations, one could derive the various functions of the DEVS.|*)

Definition S_Combined : Type := list (Q S).

Definition Q_Combined : Type := Q S_Combined.

Definition Select_Function :=
    list ((DEVS_Simulator S X Y) * (Q S)) ->
        option ((DEVS_Simulator S X Y) * (Q S)).

Definition Default_Select_Function : Select_Function :=
    fun l => hd_error l.

Definition Z_Function := identifier -> Y_output Y -> X. (* XXX simplified here *)

Definition I_Function := identifier -> list identifier.

Definition Default_I_Function : I_Function :=
    fun x => [ (*empty_identifier*) ].

Record DEVS_Coupled_Model := {
    devs_coupled_model_id : identifier ;
    D : list (DEVS_Simulator S X Y);
    Select : Select_Function ;
    Z_f : Z_Function ;
    I : I_Function;
}.

(*|
Closure under coupling
----------------------

From a coupled model, one can build the corresponding atomic model using the "closure under coupling" approach.

|*)



Definition e_init (l : list (DEVS_Simulator S X Y)) :=
    let e_init_l := map (fun x =>  x.(d).(Q_init).(e)) l in
        list_min e_init_l.

Definition Build_Q_init_Combined
    (l : list (DEVS_Simulator S X Y)) : Q_Combined :=
    let e_init_v := e_init l in
    let sc := map (fun x =>
            Build_Q x.(d).(Q_init).(st) (x.(d).(Q_init).(e) - e_init_v)) l in
            Build_Q sc e_init_v.

Definition ta_combined
    (l : list (DEVS_Simulator S X Y)) (sc : S_Combined) : Time :=
    let ta_combined_v :=
        map2 (fun a b => (a.(d).(ta) b.(st) - a.(d).(Q_init).(e))) l sc in
        list_min ta_combined_v.

Definition IMM (l : list (DEVS_Simulator S X Y)) (sc : S_Combined) :=
    let ta_v := ta_combined l sc in
        filter2 (fun a b => (sigma a.(d) b) =? ta_v) l sc.

Check IMM.

Definition λ_combined
    (l : list (DEVS_Simulator S X Y))
    (select : Select_Function)
    (sc : S_Combined)
:=
    let imm := IMM l sc in
    let i_star := select imm in
    match i_star with
        | None => no_output Y
        | Some i_star' => (fst i_star').(d).(λ) (snd i_star').(st)
    end.

Definition δint_combined
    (l : list (DEVS_Simulator S X Y))
    (select : Select_Function)
    (I : I_Function)
    (Z_f : Z_Function)
    (sc : S_Combined) : S_Combined
:=
    let imm := IMM l sc in
    let i_star := select imm in

    match i_star with
    | None => sc (* should not happen *)
    | Some i_star' =>

        let i_star_id := (fst i_star').(devs_simulator_id) (* XXX use get_id*) in
        let I_star := I i_star_id in

        let dispatch :=
            (fun (s : Q S) (x : DEVS_Simulator S X Y)  =>
                if (identifier_beq x.(devs_simulator_id) i_star_id)
                    then Build_Q (x.(d).(δint) s.(st)) 0

                else if existsb (fun y => (identifier_beq x.(devs_simulator_id) y)) I_star
                    then Build_Q
                        (x.(d).(δext) (Build_Q s.(st) (s.(e) + ta_combined l sc))             (Z_f i_star_id ((fst i_star').(d).(λ) (snd i_star').(st))))
                    0

                else Build_Q s.(st) (s.(e) + ta_combined l sc)

            )
        in

    (* Main processing of δint_combined *)
    map2 dispatch sc l
    end.

Definition δext_combined
    (l : list (DEVS_Simulator S X Y))
    (select : Select_Function)
    (I : I_Function)
    (Z_f : Z_Function)
    (qc : Q_Combined) (x : X): S_Combined
:=
    let imm := IMM l qc.(st) in
    let i_star := select imm in

    match i_star with
    | None => qc.(st) (* should not happen *)
    | Some i_star' =>
        let i_star_id := (fst i_star').(devs_simulator_id) (* XXX use get_id*) in
        let I_star := I i_star_id in

        let dispatch :=
            (fun (s : Q S) (x : DEVS_Simulator S X Y)  =>
                if existsb (fun y => (identifier_beq x.(devs_simulator_id) y)) I_star
                    then Build_Q
                        (x.(d).(δext) (Build_Q s.(st) (s.(e) + qc.(e)))             (Z_f i_star_id ((fst i_star').(d).(λ) (snd i_star').(st))))
                    0

                else Build_Q s.(st) (s.(e) + qc.(e))

            ) in

        (* Main processing of δint_combined *)
        map2 dispatch qc.(st) l

    end.

(*| Hence, one can now build an atomic DEVS from a coupled DEVS using
:coq:`Maps_DEVS_Coupled_Model`. |*)

Definition Map_DEVS_Coupled_Model (dc : DEVS_Coupled_Model) : DEVS_Atomic_Model S_Combined X Y :=
    {|
        devs_atomic_id := dc.(devs_coupled_model_id);
        Q_init := Build_Q_init_Combined dc.(D);
        ta := ta_combined dc.(D);
        δint := δint_combined dc.(D) dc.(Select) dc.(I) dc.(Z_f) ;
        λ := λ_combined dc.(D) dc.(Select) ;
        δext := δext_combined  dc.(D) dc.(Select) dc.(I) dc.(Z_f) ;
    |}.

(*| .. coq:: none |*)
End DEVS_Coupled.

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
Lemma TLC_Step2_OK :
    (Print_DEVS_Simulator TLCC_Step2.(astate)) =
    dbg 1 3 [{| st := YELLOW; e := 0 |}] [].
Proof.
    trivial.
Qed.

Definition TLCC_Step3 := DEVS_Simulation_Step TLCC_Step2.
Lemma TLC_Step3_OK :
    (Print_DEVS_Simulator TLCC_Step3.(astate)) =
    dbg 3 6 [{| st := RED; e := 0 |}] [].
Proof.
    trivial.
Qed.

Definition TLCC_Step4 := DEVS_Simulation_Step TLCC_Step3.
Lemma TLC_Step4_OK :
    (Print_DEVS_Simulator TLCC_Step4.(astate)) =
    dbg 6 7 [{| st := GREEN; e := 0 |}] [].
Proof.
    trivial.
Qed.

End Traffic_Light_Coupled.
(*| .. coq:: |*)

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

(* From this point, we cannow check that the behavior is the one we expect, that is an alternance of Player A and B sending. *)

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