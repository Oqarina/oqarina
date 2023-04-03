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
Set Implicit Arguments.
Set Strict Implicit.

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

(*|
Refinements
===========

In this section, we provide the definition of various notion of refinement present in AADL: feature refinement. property refinement, component type extension, component implementaton, classifier matching rule, etc.

_This part is not linear because these definitions are interleaved. We propose an order that avoid forward declarations, forbidden in Cqo._
|*)

(*| .. coq:: none |*)
Section Helper_Functions.
(*| .. coq:: |*)

(*| * :coq:`Is_Same_Component_Type_classifier` returns True iff. :coq:`c1` and :coq:`c2` have the same component type classifier. |*)

Definition Is_Same_Component_Type_classifier (c1 c2: component) : Prop :=
    let (l1, i1, _) := c1->classifier in
    let (l2, i2, _) := c2->classifier in
        l1 = l2 /\ i1 = i2.

(*| .. coq:: none |*)
End Helper_Functions.
(*| .. coq:: |*)


(*| .. coq:: none |*)
Section Property_Refinement.
(*| .. coq:: |*)
(*|

Property refinement
-------------------

An element (e.g. a component or a feature) may refine the properties
of another. In this case, we simply check that the list of identifiers
of the extended element is a subset of the list of identifiers of the
other. |*)

Definition Extract_Property_Identifiers_From_Element
    {A : Type } {gpa : Get_Properties A}
    (e : A)
:=
    map (fun x => x.(P)) (e->properties).

Definition Is_Refined_Properties
    {A : Type } {gpa : Get_Properties A}
    (e1 e2 : A)
    : Prop
:=
    let e1_props_psqn := Extract_Property_Identifiers_From_Element e1 in
    let e2_props_psqn := Extract_Property_Identifiers_From_Element e2 in
        Is_true (inclb ps_qname_beq e1_props_psqn e2_props_psqn).

(*| .. coq:: none |*)
End Property_Refinement.
(*| .. coq:: |*)

(*| .. coq:: none |*)
Section Implementation_Of.
(*| .. coq:: |*)

(*|
Component Implementation
------------------------

In this section, we define the predicate :coq:`Is_Implemented_By` to evaluate whether a component is implemented by another (Section 4.4 of AADL standard). A component c2 implements component c1 iff.

* c1 is a component type
* c2 is a component implementation type
* c2 identifier matches c1 identifier (see :coq:`Is_Implementation_Of_id`)
* c1 and c2 have the same features
* c1's properties identifiers are a sublist of c2's properties identifiers. The rationale is that a component implementation may either add new property associations, or change property values.

|*)

(*| :coq:`Is_Implemented_By` returns :coq:`True` if :coq:`c1` is implenented by :coq:`c2`. It is a decidable proposition. We provide a tactic to expedite this verification. |*)

Definition Is_Implemented_By (c1 c2: component) : Prop :=
    Is_AADL_Component_Type c1 /\
    Is_AADL_Component_Implementation c2 /\
    ((c1 ->category) = (c2->category)) /\
    Is_Same_Component_Type_classifier c1 c2 /\
    (c1->features) = (c2->features) /\
    Is_Refined_Properties c1 c2.

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
    extends: None
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
    extends: None
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

(*| .. coq:: none |*)
Section Feature_Refinement.
(*| .. coq:: |*)

(*|
Feature refinement
------------------

The AADL standards define rules for each feature category

* Port refinement is discussed in section 8.3 rules (L2) to (L5) |*)

Definition Port_Refinement_properties (f1 f2: feature) : Prop :=
    let f1_props_psqn:= Extract_Property_Identifiers_From_Element f1 in
    let f2_props_psqn:= Extract_Property_Identifiers_From_Element f2 in
        Is_true (inclb ps_qname_beq f1_props_psqn f2_props_psqn).

Definition Port_Refinement (f1 f2: feature) :=
    (* L2 *) (((f2->category) = dataPort \/
                (f2->category) = eventDataPort) \/
              (projectionFeatureComponent f2 = nil_component)) /\

    (* L3 *) (Port_Refinement_properties f1 f2) /\

    (* L4 *) ((f1->category) = (f2->category)
                \/ (f2->category = abstractFeature)) /\

    (* L5 *) ((projectionFeatureDirection f1) =
                (projectionFeatureDirection f2)
            \/ (f2->category) = abstractFeature).

Lemma Port_Refinement_dec: forall f1 f2,
    { Port_Refinement f1 f2 } + { ~ Port_Refinement f1 f2 }.
Proof.
    prove_dec.
Qed.

Definition Feature_Refinement (f1 f2 : feature) :=
    match f1->category with
        | eventPort | eventDataPort | dataPort => Port_Refinement f1 f2
        | _ => False
    end.

Definition Feature_Refinements' (f : feature) (l : list feature) :=
    let Some_f2 := Get_Feature_By_Name l (f->id) in
        match Some_f2 with
        | None => False
        | Some f2 => Feature_Refinement f f2
        end.

Definition Feature_Refinements (l1 l2: list feature) :=
    All (fun x => Feature_Refinements' x l2) l1.

(*| .. coq:: none |*)
End Feature_Refinement.
(*| .. coq:: |*)

(*| .. coq:: none |*)
Section Type_Extension.
(*| .. coq:: |*)

(*|

Type Extension
--------------

|*)

Definition Check_Type_Extension_Classifier (c1 c2: component) :=
    let c1_extends := projectionComponentExtends c1 in
    match c1_extends with
    | None => False
    | Some c => c = (c2->classifier)
    end.

Definition Type_Extension (c1 c2: component) :=
    Is_AADL_Component_Type c1 /\
    Is_AADL_Component_Type c2 /\
    ((c1 ->category) = (c2->category)) /\
    (Check_Type_Extension_Classifier c1 c2) /\
    Feature_Refinements (c1->features) (c2->features) /\
    Is_Refined_Properties c1 c2.

Lemma Type_Extension_dec: forall c1 c2,
    { Type_Extension c1 c2 } + { ~ Type_Extension c1 c2 }.
Proof.
    prove_dec.
    repeat decide equality.
Qed.

(*| .. coq:: none |*)
End Type_Extension.
(*| .. coq:: |*)

(*| .. coq:: none |*)
Section Classifier_Substitution_Rule.
(*| .. coq:: |*)

(*|
Classifier_Substitution_Rule
----------------------------

The AADL standard defines in section 4.5 (L4) the rules for subcomponent refinement. It is configured by the :code:`Classifier_Substitution_Rule` property that specifies the rule to be applied when a refinement supplies a classifier and the original subcomponent declaration already has a component classifier.

We define a predicate for each rule.

* :coq:`Classifier_Match`: The component type of the refinement must be identical to the component type of the classifier being refined. If the original declaration specifies a component type, then any implementation of that type can replace this original implementation. This is the default rule.

XXX this wording is weird. It means a couple of things
- a component implementation cannot be refined
- how do you evaluate component type equality?
|*)

Definition Component_Refined_To_Classifier_Match (c1 c2: component) :=
    (Is_Same_Component_Type_classifier c1 c2) \/
    Is_Implemented_By c1 c2.

Lemma Component_Refined_To_Classifier_Match_dec: forall c1 c2,
    { Component_Refined_To_Classifier_Match c1 c2 } +
    { ~ Component_Refined_To_Classifier_Match c1 c2 }.
Proof.
    generalize fq_name_eq_dec, list_eq_dec.
    prove_dec.
Qed.

(*|

* :coq:`Type_Extension`: Any component classifier whose component type is an extension of the component type of the classifier in the subcomponent being refined is an acceptable substitute.

|*)

(*|

*	Signature_Match: The component type of the refinement must match the signature of the component type of the classifier being refined.

|*)

(*| .. coq:: none |*)
End Classifier_Substitution_Rule.
(*| .. coq:: |*)


Import AADL_Notations.
Open Scope aadl_scope.

Example package_1 :=
    package: "package1" ->| [

    system: "s1" ->| "s1_classifier"
        extends: None
        features: nil
        subcomponents: nil
        connections: nil
        properties: nil
;
    system: "s2" ->| "s2_classifier"
        extends: Some (parse_fq_name "s1_classifier")
        features: nil
        subcomponents: nil
        connections: nil
        properties: nil
;
    system: "s3" ->| "s1_classifier.i"
        extends: None
        features: nil
        subcomponents: [
            system: "s4" ->| "s4_classifier.i"
            extends: None
            features: nil
            subcomponents: nil
            connections: nil
            properties: nil
        ]
        connections: nil
        properties: nil
    ] .

Lemma wf_package_1: Well_Formed_Package package_1.
Proof.
   prove_Well_Formed_Package.
Qed.
