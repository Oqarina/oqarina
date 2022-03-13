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
Require Import Oqarina.core.all.

Require Import Oqarina.coq_utils.all.
Require Import Oqarina.formalisms.lts.
Require Import Oqarina.formalisms.DEVS.parallel.devs.
#[local] Open Scope bool_scope.
Set Implicit Arguments.

Section DEVS_Coupled.
(*| .. coq:: |*)

(*|

Coupled models
--------------

Coupled models represent a hierarchy of DEVS model.

A coupled DEVS model is an 8-tuple :math:`M=<X,Y,D,\{M_{i}\},Z_{{i, self}},Select>` where

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

Definition Z_Function_internal := identifier -> identifier -> Y_output Y -> list X.

(*| By construction, we do not consider this |*)
Definition Z_Function_in := identifier -> list X -> list X.

Definition Z_Function_out := identifier -> Y_output Y -> Y_output Y.

Definition I_Function := identifier -> list identifier.

Definition Default_I_Function : I_Function :=
    fun x => [ (*empty_identifier*) ].

Record DEVS_Coupled_Model := {
    devs_coupled_model_id : identifier ;
    D : list (DEVS_Simulator S X Y);
    Z_f : Z_Function_internal ;
    Z_in : Z_Function_in;
    Z_out : Z_Function_out ;
    I : I_Function;
}.

(*|
Closure under coupling
----------------------

From a coupled model, one can build the corresponding atomic model using the
 "closure under coupling" approach. See chapter 7.2 of Theory of Modeling and Simulation

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
    map2 (fun a b => (a.(d).(ta) b.(st) - b.(e))) l sc in
    list_min ta_combined_v.


(*||
   Imminent models :math:`\displaystyle IMM(s)`

   :math:`IMM(s)=\{d|\sigma _{d}=ta(s)\}}`

*)

Definition IMM (l : list (DEVS_Simulator S X Y)) (sc : S_Combined) :=
    let ta_v := ta_combined l sc in
        filter2 (fun a b => (sigma a.(d) b) =? ta_v) l sc.

(*|

:math:`INF(s)=\{d|i\in I_{d},i\in IMM(s)\wedge x_{d}^{b}\notin \emptyset \}` with :math:`x_{d}^{b}=\{I{d}(\lambda _{i}(s_{i}))|i\in IMM(s)\cap I_{d}\}`

INF is defined as a set of elements meeting some predicates. Yet, this definition is not natural. INF is the set of DEVS models that are (a) influenced by DEVS components that belongs to the IMM set and (b) receive events from thes elements. We can provide a more direct definition using functions instead of sets.

let :math:`INF_m (s)` the set of DEVS components that may be influenced while at state s: i.e. elements that are influenced by immediate components at state s

|*)

Definition INF_m
    (l : list (DEVS_Simulator S X Y))
    (sc : S_Combined)
    (I : I_Function)
:=
    (* extract the set of immediate DEVS componentns *)
    let IMM' := map (fun x => fst x) (IMM l sc) in

    (* buld all influencees, it is the image of IMM' by I *)
    let INF_m1 := flat_map (fun x => I x) (get_devs_simulator_ids IMM') in

    (* filter out duplicate values *)
    nodup identifier_eq_dec INF_m1.

Definition x_d
    (l : list (DEVS_Simulator S X Y))
    (sc : S_Combined)
    (I : I_Function)
    : list (Y_output Y)
:=
    (*    let INF_m' := INF_m l sc I in *)
    let INF_m' := get_devs_simulator_ids (map (fun x => fst x) (IMM l sc)) in
    let dispatch :=
        (fun (s : Q S) (ds : DEVS_Simulator S X Y)  =>
            if id_in ds.(devs_simulator_id) INF_m' then
                ds.(d).(λ) s.(st)
            else
           [ no_output Y ]
        ) in
    flat_map id (map2 dispatch sc l).

Definition x_d_i
    (l : list (DEVS_Simulator S X Y))
    (sc : S_Combined)
    (I : I_Function)
    (Z_internal : Z_Function_internal)
    (i : identifier)
    : list X
:=
   (* let INF_m' := INF_m l sc I in *)
   let INF_m' := get_devs_simulator_ids (map (fun x => fst x) (IMM l sc)) in

    let dispatch :=
        (fun (s : Q S) (ds : DEVS_Simulator S X Y)  =>
            if ((id_in ds.(devs_simulator_id) INF_m') &&
                id_in i (I ds.(devs_simulator_id))
            ) then
                map (fun x => Z_internal ds.(devs_simulator_id) i x) (ds.(d).(λ) s.(st))
            else
                []
        ) in
    flat_map id (flat_map id (map2 dispatch sc l)).

Definition INF_id
    (l : list (DEVS_Simulator S X Y))
    (sc : S_Combined)
    (I : I_Function)
:=
    let INF_m' := INF_m l sc I in
    filter (fun x => negb (is_nil (x_d l sc I))) INF_m'.

Definition λ_combined
    (l : list (DEVS_Simulator S X Y))
    (I : I_Function)
    (Z_out : Z_Function_out)
    (sc : S_Combined)
:=
    (* Compute IMM (s) *)
    let imm := IMM l sc in

    (* *)
    let imm' := filter
        (fun x => id_in (Id "_self") (I (fst x).(devs_simulator_id))) imm in

    (* Compute the messages for elements in IMM*)
    let messages := map
        (fun x : DEVS_Simulator S X Y * Q S =>
            map (fun x' => Z_out (fst x).(devs_simulator_id) x')
                    ((fst x).(d).(λ) (snd x).(st))) imm' in

    (* Flatten the list of messages *)
    let messages' := flat_map id messages in

    (* and the resulting messages to be sent. Note we filter the no output as
       well, since these are produced anyway. *)

    filter (fun x => match x with | (no_output _) => false
                                    | _ => true end) messages'.

Definition δint_combined
    (l : list (DEVS_Simulator S X Y))
    (I : I_Function)
    (Z_internal : Z_Function_internal)
    (Z_out : Z_Function_out)
    (sc : S_Combined)
    : S_Combined
:=
    let IMM_ids := get_devs_simulator_ids (map (fun x => fst x) (IMM l sc)) in
    let INF_ids' := INF_id l sc I in

    let ext_ids := set_diff identifier_eq_dec INF_ids' IMM_ids in
    let int_ids := set_diff identifier_eq_dec IMM_ids INF_ids' in
    let conf_ids :=  set_inter identifier_eq_dec IMM_ids INF_ids' in

    let x_i_b :=
        (fun (ds : DEVS_Simulator S X Y) =>
            x_d_i l sc I Z_internal ds.(devs_simulator_id)
        ) in

    let dispatch :=
        (fun (s : Q S) (ds : DEVS_Simulator S X Y)  =>

            (* INT case *)
            if (id_in ds.(devs_simulator_id) int_ids) then
                Build_Q (ds.(d).(δint) s.(st)) 0

            (* EXT case *)
            else if (id_in ds.(devs_simulator_id) ext_ids) then
                Build_Q
                    (ds.(d).(δext)
                        (Build_Q s.(st) (s.(e) + ta_combined l sc))
                        (x_i_b ds))
                    0

            (* CONF case *)
            else if (id_in ds.(devs_simulator_id) conf_ids) then
                Build_Q (ds.(d).(δcon) s.(st) (x_i_b ds)) 0

            (* Default *)
            else Build_Q s.(st) (s.(e) + ta_combined l sc))
    in
        (* Main processing of δint_combined *)
        map2 dispatch sc l.

Definition δext_combined
    (l : list (DEVS_Simulator S X Y))
    (I : I_Function)
    (Z_in : Z_Function_in)
    (qc : Q_Combined)
    (x : list X)
    : S_Combined
:=
    let imm := IMM l qc.(st) in

    let dispatch :=
        (fun (s : Q S) (ds : DEVS_Simulator S X Y)  =>
            if id_in ds.(devs_simulator_id) (I (Id "_self"))
                then Build_Q (
                    ds.(d).(δext)
                        (Build_Q s.(st) (s.(e) + qc.(e)))
                        (Z_in ds.(devs_simulator_id) x))
                0

            else Build_Q s.(st) (s.(e) + qc.(e)))
    in
        (* Main processing of δext_combined *)
        map2 dispatch qc.(st) l.

Definition δcon_combined
    (l : list (DEVS_Simulator S X Y))
    (I : I_Function)
    (Z_in : Z_Function_in)
    (Z_internal : Z_Function_internal)
    (Z_out : Z_Function_out)
    (sc : S_Combined)
    (x : list X)
    : S_Combined
:=
    let IMM_ids := get_devs_simulator_ids (map (fun x => fst x) (IMM l sc)) in
    let INF_ids' := set_union identifier_eq_dec (INF_id l sc I) (I (Id "_self")) in

    let ext_ids := set_diff identifier_eq_dec INF_ids' IMM_ids in
    let int_ids := set_diff identifier_eq_dec IMM_ids INF_ids' in
    let conf_ids := set_inter identifier_eq_dec IMM_ids INF_ids' in
    let x_i_b :=
        (fun (ds : DEVS_Simulator S X Y) =>
            (x_d_i l sc I Z_internal ds.(devs_simulator_id)) ++
            if id_in ds.(devs_simulator_id) (I (Id "_self")) then x else []
            ) in

    let dispatch :=
        (fun (s : Q S) (ds : DEVS_Simulator S X Y)  =>

            (* INT case *)
            if (id_in ds.(devs_simulator_id) int_ids) then
                Build_Q (ds.(d).(δint) s.(st)) 0

            (* EXT case *)
            else if (id_in ds.(devs_simulator_id) ext_ids) then
                Build_Q
                    (ds.(d).(δext)
                        (Build_Q s.(st) (s.(e) + ta_combined l sc))
                         (x_i_b ds))
                    0

            (* CONF case *)
            else if (id_in ds.(devs_simulator_id) conf_ids) then
                Build_Q
                    (ds.(d).(δcon) s.(st) (x_i_b ds)) 0

            (* Default *)
            else Build_Q s.(st) (s.(e) + ta_combined l sc))
    in
        (* Main processing of δint_combined *)
        map2 dispatch sc l.

(*| Hence, one can now build an atomic DEVS from a coupled DEVS using
:coq:`Maps_DEVS_Coupled_Model`. |*)

Definition Map_DEVS_Coupled_Model
    (dc : DEVS_Coupled_Model) : DEVS_Atomic_Model S_Combined X Y :=
    {|
        devs_atomic_id := dc.(devs_coupled_model_id);
        Q_init := Build_Q_init_Combined dc.(D);
        ta := ta_combined dc.(D);
        δint := δint_combined dc.(D) dc.(I) dc.(Z_f) dc.(Z_out);
        λ := λ_combined dc.(D) dc.(I) dc.(Z_out) ;
        δext := δext_combined dc.(D) dc.(I) dc.(Z_in);
        δcon := δcon_combined dc.(D) dc.(I) dc.(Z_in) dc.(Z_f) dc.(Z_out);
    |}.

Inductive DEVS_Coupled_Debug : Type :=
    dbg_coupled  : identifier ->  Q S -> DEVS_Coupled_Debug.

Definition Print_DEVS_Coupled_Debug
    (dc : DEVS_Coupled_Model )
    (dc_sim : DEVS_Simulator S_Combined X Y )
:=
    let devs_names := map (fun x => x.(devs_simulator_id)) dc.(D) in
    let devs_dbg : list (Q S) := dc_sim.(cs).(st) in
    map2 (fun x y =>  dbg_coupled x y) devs_names devs_dbg.

Definition sigma_combined (* debugging *)
    (l : list (DEVS_Simulator S X Y))
    (sc : S_Combined)
:=
    map2 (fun a b => (sigma a.(d) b)) l sc.

Record DEVS_Decision_Sets := {
    IMM_ids : list identifier;
    INF_ids : list identifier;
    EXT_ids : list identifier;
    INT_ids : list identifier;
    CONF_ids : list identifier;
}.

Definition Compute_DEVS_Decision_Sets
    (l : list (DEVS_Simulator S X Y))
    (I : I_Function)
    (sc : S_Combined)
:=
    let IMM_ids' :=  get_devs_simulator_ids
        (map (fun x => fst x) (IMM l sc)) in
    let INF_ids' := set_union identifier_eq_dec
        (INF_id l sc I) (I (Id "_self")) in
    {|
        IMM_ids := IMM_ids';
        INF_ids := INF_ids';
        EXT_ids := set_diff identifier_eq_dec INF_ids' IMM_ids' ;
        INT_ids := set_diff identifier_eq_dec IMM_ids' INF_ids' ;
        CONF_ids :=  set_inter identifier_eq_dec IMM_ids' INF_ids'
    |}.

(*| .. coq:: none |*)
End DEVS_Coupled.
