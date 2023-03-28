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
(** Coq Library *)
Require Import List.
Import ListNotations. (* from List *)
Require Import Coq.Lists.ListDec.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.

(** Oqarina library *)
Require Import Oqarina.AADL.Kernel.all.
Require Import Oqarina.AADL.legality.all.
Require Import Oqarina.AADL.property_sets.all.
Require Import Oqarina.core.all.
Require Import Oqarina.coq_utils.all.
Require Import Oqarina.AADL.declarative.declarative_model.
Import AADL_Notations.
Open Scope aadl_scope.
(*| .. coq::  |*)

(*| .. coq:: none |*)
Section Implementation_Of.
(*| .. coq:: |*)

(*|
Implenentation
--------------

In this section, we define the predicate :coq:`Is_Implemented_By` to evaluate that a component is implemented by another.

A component c2 implements component c1 iff.

* c1 is a component type
* c2 is a component implementation type
* c2 identifier matches c1 identifier (see :coq:`Is_Implementation_Of_id`)
* c1 and c2 have the same features
* c1's properties identifiers are a sublist of c2's properties identifiers. The rationale is that a component implementation may either add new property associations, or change property values.

We first define intermediate helper functions, then implement this predicate.

|*)

Definition Is_Implementation_Of_classifier (c1 c2:component) : Prop :=
    let (l1, i1, _) := c1->classifier in
    let (l2, i2, _) := c2->classifier in
        l1 = l2 /\ i1 = i2.

Definition Extract_Identifiers_From_Component_Properties (c : component) :=
    let props := c->properties in
    map (fun x => x.(P)) props.

Definition Is_Implementation_Of_properties (c1 c2:component) : Prop :=
    let c1_props_psqn:= Extract_Identifiers_From_Component_Properties c1 in
    let c2_props_psqn:= Extract_Identifiers_From_Component_Properties c2 in
        Is_true (inclb ps_qname_beq c1_props_psqn c2_props_psqn).

(*| :coq:`Is_Implemented_By` returns :coq:`True` if :coq:`c1` is implenented by :coq:`c2`. It is a decidable proposition. We provide a tactic to expedite this verification. |*)

Definition Is_Implemented_By (c1 c2: component) : Prop :=
    Is_AADL_Component_Type c1 /\
    Is_AADL_Component_Implementation c2 /\
    Is_Implementation_Of_classifier c1 c2 /\
    (c1->features) = (c2->features) /\
    Is_Implementation_Of_properties c1 c2.

Lemma Is_Implemented_By_dec : forall c1 c2,
    { Is_Implemented_By c1 c2 } + { ~ Is_Implemented_By c1 c2 }.
Proof.
    generalize list_eq_dec, identifier_eq_dec, feature_eq_dec.
    generalize incl_dec, ps_qname_eq_dec.
    prove_dec.
Qed.

Ltac prove_Is_Implemented_By :=
    repeat match goal with
        | |- Is_Implemented_By _ _ => compute; repeat split; auto
        | |- (_ =  EmptyString -> False) => intuition; inversion H
        | |- NoDup nil => apply NoDup_nil
        | |- NoDup  _  => apply NoDup_cons
        | |- ~ In _ _ => apply not_in_car
        | |- Id _ <> Id _ => apply identifier_string_neq; easy
        | |- ~ In _ [] => apply in_nil
    end.

(*| .. coq:: none |*)
Section Test.

Example C1 : component :=
    thread: "a_periodic_thread" ->| "pack::a_thread_classifier"
    features: nil
    subcomponents: nil
    connections: nil
    properties: [
        property: Priority_Name ==>| PV_Int 42%Z;
        property: Dispatch_Protocol_Name ==>| PV_Enum (Id "Periodic");
        property: Period_Name ==>| PV_IntU 3 (PV_Unit (Id "ms"))
    ].

Example C2 : component :=
    thread: "a_periodic_thread2" ->| "pack::a_thread_classifier.impl"
    features: nil
    subcomponents: nil
    connections: nil
    properties: [
        property: Priority_Name ==>| PV_Int 42%Z;
        property: Dispatch_Protocol_Name ==>| PV_Enum (Id "Periodic");
        property: Period_Name ==>| PV_IntU 3 (PV_Unit (Id "ms"))
    ].

Lemma Test_1 : Is_Implemented_By C1 C2.
Proof.
    prove_Is_Implemented_By.
Qed.

Lemma Test_2 : ~ Is_Implemented_By C2 C1.
Proof.
    unfold Is_Implemented_By.
    intuition.
    assert (~ Is_AADL_Component_Type C2).
    - unfold Is_AADL_Component_Type. intuition.
    - contradiction.
Qed.

End Test.
(*| .. coq:: |*)

(*| .. coq:: none |*)
End Implementation_Of.
(*| .. coq:: |*)
