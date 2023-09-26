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
Require Import Coq.Relations.Relation_Definitions.
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

*This part is not linear because these definitions are interleaved. We propose an order that avoid forward declarations, forbidden in Coq.*

|*)

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

Context {A : Type } `{gpa : Get_Properties A}.

Definition Extract_Property_Identifiers_From_Element
    (e : A)
:=
    map (fun x => x.(P)) (e->properties).

Definition Is_Refined_Properties
    (e1 e2 : A)
    : Prop
:=
    let e1_props_psqn := Extract_Property_Identifiers_From_Element e1 in
    let e2_props_psqn := Extract_Property_Identifiers_From_Element e2 in
       incl e1_props_psqn e2_props_psqn.

Lemma Is_Refined_Properties_dec: forall f1 f2,
    { Is_Refined_Properties f1 f2 } + { ~ Is_Refined_Properties f1 f2 }.
Proof.
    intros.
    unfold Is_Refined_Properties.
    apply incl_dec.
    apply ps_qname_eq_dec.
Qed.

Lemma Is_Refined_Properties_reflexive:
    reflexive A Is_Refined_Properties.
Proof.
    unfold reflexive.
    unfold Is_Refined_Properties.
    intros. apply incl_refl.
Qed.

Lemma Is_Refined_Properties_transitive:
    transitive A Is_Refined_Properties.
Proof.
    unfold transitive.
    unfold Is_Refined_Properties.
    intros.
    eapply incl_tran. apply H. apply H0.
Qed.

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

Definition Port_Refinement (f1 f2: feature) :=
    (* L2 *) (((f2->category) = dataPort \/
                (f2->category) = eventDataPort) \/
              (projectionFeatureComponent f2 = nil_component)) /\

    (* L3 *) (Is_Refined_Properties f1 f2) /\

    (* L4 *) ((f1->category) = (f2->category)
                \/ (f2->category = abstractFeature)) /\

    (* L5 *) ((projectionFeatureDirection f1) =
                (projectionFeatureDirection f2)
            \/ (f2->category) = abstractFeature).

Lemma Port_Refinement_dec: forall f1 f2,
    { Port_Refinement f1 f2 } + { ~ Port_Refinement f1 f2 }.
Proof.
    generalize Is_Refined_Properties_dec.
    prove_dec.
Qed.

Lemma Port_Refinement_transitive: transitive _ Port_Refinement.
Proof.
    unfold transitive.
    generalize Is_Refined_Properties_transitive.
    unfold Port_Refinement.
    intros.
    repeat split.
    - intuition.
    - specialize (H x y z). intuition.
    - intuition ;
        try (rewrite H0; left; apply H7);
        try (rewrite H0 in H8; inversion H8) ;
        try (rewrite H0 in H7; rewrite H8 in H7; inversion H7);
        try (rewrite H0 in H7; right; intuition).
    - intuition ;
        try (rewrite H5 in H4; left ; apply H4) ;
        try (rewrite H4 in H7; right; intuition).
Qed.

(*|

We merge all these definition to define :coq:`Feature_Refinement`. We show this relation is reflexive and transitive.
|*)

Definition Feature_Refinement (f1 f2 : feature) :=
    f1 = f2 \/ (
    (f1 ->id) = (f2->id) /\
    match f1->category with
        | eventPort | eventDataPort | dataPort => Port_Refinement f1 f2
        | _ => False
    end).

Lemma Feature_Refinement_reflexive: reflexive _ Feature_Refinement.
Proof.
    unfold Feature_Refinement.
    auto with *.
Qed.

Lemma Feature_Refinement_transitive: transitive _ Feature_Refinement.
Proof.
    intros f1 f2 f3.
    unfold Feature_Refinement.
    intros.
    destruct H ; destruct H0.
    - rewrite H in *. intuition.
    - rewrite H in *. intuition.
    - rewrite H0 in *. intuition.
    - destruct (f1 ->category ) ; destruct (f2 ->category) ; right ;
        try (apply Port_Refinement_transitive with (y:= f2) ;
        try apply H ; try apply H0) ;
        try (inversion H0) ;
        try (intuition) ;
        try (rewrite H3 ; apply H) ;
        try (apply Port_Refinement_transitive with (y := f2) ;
            intuition).
Qed.

(*| In the following, we extend the concept of feature refinement to a list of features. |*)

Definition Feature_Refinements' (f : feature) (l : list feature) :=
    let Some_f2 := Get_Element_By_Name _ l (f->id) in
        match Some_f2 with
        | None => False
        | Some f2 => Feature_Refinement f f2
        end.

Definition Feature_Refinements (l1 l2: list feature) :=
    All (fun x => Feature_Refinements' x l2) l1.

(*| Proving the :coq:`Feature_Refinements` is a preorder has some technicalities. We introduce several helper lemmas. |*)

Lemma Feature_Refinements'_destruct: forall a l,
    Feature_Refinements' a l ->
        exists f, In f l /\ Feature_Refinement a f.
Proof.
    unfold Feature_Refinements'.
    intros.
    destruct (Get_Element_By_Name _ l (a ->id)) eqn:al.
    - assert (In f l /\ (identifier_beq (f->id) (a->id) = true)).
      apply Get_Element_By_Name_destruct ; intuition.
      exists f. intuition.
    - inversion H.
Qed.

Lemma Feature_Refinement_same_id: forall f1 f2,
    Feature_Refinement f1 f2 -> (f1->id) = (f2->id).
Proof.
    intros.
    unfold Feature_Refinement in H.
    destruct H.
    - inversion H ; intuition.
    - intuition.
Qed.

Lemma Feature_Refinements'_elt:
    forall (a x: feature) (l : list feature),
    Feature_Refinement a x
        -> Feature_Refinements' x l
        -> Feature_Refinements' a l.
Proof.
    intros.

    assert (exists f : feature, In f l /\ Feature_Refinement x f).
    apply Feature_Refinements'_destruct, H0.
    destruct H1. destruct H1.

    assert (Feature_Refinement a x0).
    apply Feature_Refinement_transitive with (y:=x) ; intuition.

    assert (Hid: (a->id) = (x0->id)).
    apply Feature_Refinement_same_id , H3.

    assert (Hid': (x->id) = (x0->id)).
    apply Feature_Refinement_same_id , H2.

    unfold Feature_Refinements' in *.
    rewrite Hid. rewrite Hid' in *.
    destruct (Get_Element_By_Name _ l (x0 ->id) ).
    - eapply Feature_Refinement_transitive. apply H. intuition.
    - inversion H0.
Qed.

Lemma Feature_Refinements_elt: forall (a: feature) (l1 l2: list feature),
    Feature_Refinements' a l1
        -> Feature_Refinements l1 l2
        -> Feature_Refinements' a l2.
Proof.
    intros.
    apply Feature_Refinements'_destruct in H.
    destruct H. destruct H.
    unfold Feature_Refinements in H0.

    apply All_In with (x := x) in H0.
    eapply Feature_Refinements'_elt.
    apply H1. apply H0. apply H.
Qed.

Lemma Feature_Refinements'_app: forall f l,
    Feature_Refinements' f (f::l).
Proof.
    intros.
    unfold Feature_Refinements'.
    assert (Get_Element_By_Name _ (f :: l) (f ->id) = Some f).
    - simpl.
      assert (identifier_beq (projectionFeatureIdentifier f)
                             (projectionFeatureIdentifier f) = true).
      apply identifier_eqb_refl.
      rewrite H. reflexivity.

    - rewrite H. apply Feature_Refinement_reflexive.
Qed.

Lemma Feature_Refinements_destruct: forall l1 l2,
    Feature_Refinements l1 l2 ->
        forall f, In f l1 -> Feature_Refinements' f l2.
Proof.
    intros.
    unfold Feature_Refinements in H.

    assert (forall x, In x l1 -> Feature_Refinements' x l2).

    apply Forall_forall. apply All_Forall. apply H.
    specialize (H1 f). intuition.
Qed.

(*| We can now prove that :coq:`Feature_Refinements` is both transitive and reflextive. Note that reflexivitiy requires the list of features to be well-formed, this is expected: features identifiers should be unique to ascertain feature refinement. |*)

Lemma Feature_Refinements_transitive:
    transitive _ Feature_Refinements.
Proof.
    unfold transitive.
    intros.
    induction x.
    - trivial.
    - simpl in H. destruct H.
      simpl. split.
      + eapply Feature_Refinements_elt. apply H. apply H0.
      + apply IHx. apply H1.
Qed.

Lemma Feature_Refinements_reflexive: forall l,
    Well_Formed_Features l -> Feature_Refinements l l.
Proof.
    intros.
    unfold Feature_Refinements.
    apply All_Forall. apply Forall_forall.
    intros.

    unfold Feature_Refinements'.
    rewrite Well_Formed_Features_in_resolve.
    apply Feature_Refinement_reflexive.
    apply H.
    apply H0.
Qed.

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
    Feature_Refinements (c1->features) (c2->features) /\
    Is_Refined_Properties c1 c2.

Lemma Type_Extension_dec: forall c1 c2,
    { Type_Extension c1 c2 } + { ~ Type_Extension c1 c2 }.
Proof.
    generalize fq_name_eq_dec, ps_qname_eq_dec, identifier_eq_dec, In_dec.
    generalize Is_Refined_Properties_dec, incl_dec.
    prove_dec.
Qed.

Lemma Type_Extension_reflexive: forall c,
    Is_AADL_Component_Type c -> Type_Extension c c.
Proof.
    unfold reflexive.
    unfold Type_Extension.
    intuition.
    - apply Feature_Refinements_reflexive.
      apply AADL_Component_Has_Well_Formed_Features. intuition.
    - apply Is_Refined_Properties_reflexive.
Qed.

Lemma Type_Extension_transitive: transitive _ Type_Extension.
Proof.
    unfold transitive.
    unfold Type_Extension.
    intuition.
    - rewrite H4 in H3. intuition.
    - eapply Feature_Refinements_transitive. apply H5. apply H6.
    - eapply Is_Refined_Properties_transitive. apply H8. apply H9.
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
    Is_Same_Component_Type_classifier c1 c2 \/
    Is_Implemented_By c1 c2.

Lemma Component_Refined_To_Classifier_Match_dec: forall c1 c2,
    { Component_Refined_To_Classifier_Match c1 c2 } +
    { ~ Component_Refined_To_Classifier_Match c1 c2 }.
Proof.
    generalize fq_name_eq_dec, list_eq_dec, incl_dec, ps_qname_eq_dec.
    prove_dec.
Qed.

Lemma Component_Refined_To_Classifier_Match_transitive :
    transitive _ Component_Refined_To_Classifier_Match.
Proof.
    unfold transitive.
    intros c1 c2 c3.
    unfold Component_Refined_To_Classifier_Match.
    intros.
    unfold Is_Implemented_By in *.
    intuition.
    - left. eapply Is_Same_Component_Type_classifier_transitive.
      apply H1. apply H.
    - left. eapply Is_Same_Component_Type_classifier_transitive.
      apply H1. apply H3.
    - left. eapply Is_Same_Component_Type_classifier_transitive.
      apply H3. apply H5.
    - left. eapply Is_Same_Component_Type_classifier_transitive.
      apply H3. apply H8.
Qed.

(*|

* :coq:`Type_Extension`: Any component classifier whose component type is an extension of the component type of the classifier in the subcomponent being refined is an acceptable substitute.

|*)

(*|

*	Signature_Match: The component type of the refinement must match the signature of the component type of the classifier being refined.

|*)

(*|

Component Refinement
--------------------

|*)

Definition Component_Refinement (c1 c2 : component) :=
    c1 = c2 \/ (
    (c1 ->id) = (c2->id) /\
    Component_Refined_To_Classifier_Match c1 c2).

Lemma Component_Refinement_transitive: transitive _ Component_Refinement.
Proof.
    intros c1 c2 c3.
    unfold Component_Refinement.
    intros.
    destruct H ; destruct H0.
    - rewrite H in *. intuition.
    - rewrite H in *. intuition.
    - rewrite H0 in *. intuition.
    - destruct H. destruct H0. right. split.
      + rewrite H in *. intuition.
      + eapply Component_Refined_To_Classifier_Match_transitive.
      apply H1. apply H2.
Qed.

Lemma Component_Refinement_reflexive: reflexive _ Component_Refinement.
Proof.
    unfold Component_Refinement.
    auto with *.
Qed.

(*| In the following, we extend the concept of component refinement to a list of conponent. |*)

Definition Component_Refinements' (c : component) (l : list component) :=
    let Some_c2 := Get_Element_By_Name _ l (c->id) in
        match Some_c2 with
        | None => False
        | Some c2 => Component_Refinement c c2
        end.

Definition Component_Refinements (l1 l2: list component) :=
    All (fun x => Component_Refinements' x l2) l1.

(*| Proving the :coq:`Component_Refinements` is a preorder has some technicalities. We introduce several helper lemmas. |*)

Lemma Component_Refinements'_destruct: forall a l,
    Component_Refinements' a l ->
        exists c, In c l /\ Component_Refinement a c.
Proof.
    unfold Component_Refinements'.
    intros.
    destruct (Get_Element_By_Name _ l (a ->id)) eqn:al.
    - assert (In c l /\ (identifier_beq (c->id) (a->id) = true)).
      apply Get_Element_By_Name_destruct ; intuition.
      exists c. intuition.
    - inversion H.
Qed.

Lemma Component_Refinement_same_id: forall c1 c2,
    Component_Refinement c1 c2 -> (c1->id) = (c2->id).
Proof.
    intros.
    unfold Component_Refinement in H.
    destruct H.
    - inversion H ; intuition.
    - intuition.
Qed.

Lemma Component_Refinements'_elt:
    forall (a x: component) (l : list component),
    Component_Refinement a x
        -> Component_Refinements' x l
        -> Component_Refinements' a l.
Proof.
    intros.

    assert (exists c : component, In c l /\ Component_Refinement x c).
    apply Component_Refinements'_destruct, H0.
    destruct H1. destruct H1.

    assert (Component_Refinement a x0).
    apply Component_Refinement_transitive with (y:=x) ; intuition.

    assert (Hid: (a->id) = (x0->id)).
    apply Component_Refinement_same_id , H3.

    assert (Hid': (x->id) = (x0->id)).
    apply Component_Refinement_same_id , H2.

    unfold Component_Refinements' in *.
    rewrite Hid. rewrite Hid' in *.
    destruct (Get_Element_By_Name _ l (x0 ->id) ).
    - eapply Component_Refinement_transitive. apply H. intuition.
    - inversion H0.
Qed.

Lemma Component_Refinements_elt:
    forall (a: component) (l1 l2: list component),
    Component_Refinements' a l1
        -> Component_Refinements l1 l2
        -> Component_Refinements' a l2.
Proof.
    intros.
    apply Component_Refinements'_destruct in H.
    destruct H. destruct H.
    unfold Component_Refinements in H0.

    apply All_In with (x := x) in H0.
    eapply Component_Refinements'_elt.
    apply H1. apply H0. apply H.
Qed.

Lemma Component_Refinements'_app: forall f l,
    Component_Refinements' f (f::l).
Proof.
    intros.
    unfold Component_Refinements'.
    assert (Get_Element_By_Name _ (f :: l) (f ->id) = Some f).
    - simpl.
      assert (identifier_beq (f->id)
                             (f->id) = true).
      apply identifier_eqb_refl.
      simpl in H.
      rewrite H. reflexivity.

    - rewrite H. apply Component_Refinement_reflexive.
Qed.

Lemma Component_Refinements_destruct: forall l1 l2,
    Component_Refinements l1 l2 ->
        forall f, In f l1 -> Component_Refinements' f l2.
Proof.
    intros.
    unfold Component_Refinements in H.

    assert (forall x, In x l1 -> Component_Refinements' x l2).

    apply Forall_forall. apply All_Forall. apply H.
    specialize (H1 f). intuition.
Qed.

(*| We can now prove that :coq:`Component_Refinements` is both transitive and reflextive. Note that reflexivitiy requires the list of features to be well-formed, this is expected: features identifiers should be unique to ascertain feature refinement. |*)

Lemma Component_Refinements_transitive:
    transitive _ Component_Refinements.
Proof.
    unfold transitive.
    intros.
    induction x.
    - trivial.
    - simpl in H. destruct H.
      simpl. split.
      + eapply Component_Refinements_elt. apply H. apply H0.
      + apply IHx. apply H1.
Qed.

Lemma Component_Refinements_reflexive: forall l,
    Well_Formed_Subcomponents l -> Component_Refinements l l.
Proof.
    intros.
    unfold Component_Refinements.
    apply All_Forall. apply Forall_forall.
    intros.

    unfold Component_Refinements'.
    rewrite Well_Formed_Subcomponents_in_resolve.
    apply Component_Refinement_reflexive.
    apply H.
    apply H0.
Qed.

Definition valid_list_component := { x : list component | Well_Formed_Subcomponents x}.

Definition cast (l: valid_list_component) : list component.
Proof.
    unfold valid_list_component in *.
    destruct l.
    exact x.
Defined.

Definition Valid_Component_Refinements (l1 l2 : valid_list_component ) :=
    Component_Refinements (cast l1) (cast l2).

Lemma Valid_Component_Refinements_reflexive: reflexive _
Valid_Component_Refinements.
Proof.
    unfold reflexive.
    intros.
    unfold valid_list_component in *.
    destruct x.
    unfold Valid_Component_Refinements; simpl.
    now apply Component_Refinements_reflexive.
Qed.

Lemma Valid_Component_Refinements_transitive:
    transitive _ Valid_Component_Refinements.
Proof.
    unfold transitive.
    intros.
    unfold Valid_Component_Refinements in *.

    destruct x, y, z.
    simpl in *.

    induction x.
    - trivial.
    - simpl in H. destruct H.
      simpl. split.
      + eapply Component_Refinements_elt. apply H. apply H0.
      + apply Well_Formed_Subcomponents_cons in w. destruct w. apply IHx ; auto.
Qed.

#[global] Instance Valid_Component_Refinements_Preorder
    : PreOrder Valid_Component_Refinements := {
        PreOrder_Reflexive := Valid_Component_Refinements_reflexive ;
        PreOrder_Transitive := Valid_Component_Refinements_transitive ;
    }.

(*|

Implementation Extension
------------------------

|*)

Definition Implementation_Extension (c1 c2: component) :=
    Is_AADL_Component_Implementation c1 /\
    Is_AADL_Component_Implementation c2 /\
    ((c1 ->category) = (c2->category)) /\
    Feature_Refinements (c1->features) (c2->features) /\
    Component_Refinements (c1->subcomps) (c2->subcomps) /\
    Is_Refined_Properties c1 c2.

Lemma Implementation_Extension_reflexive: forall c,
    Well_Formed_Component_Implementation c ->
        Implementation_Extension c c.
Proof.
    unfold reflexive.
    unfold Implementation_Extension.
    intros.
    unfold Well_Formed_Component_Implementation in H.
    destruct c. unfold Unfold_Apply in H.
    simpl in H. destruct H.
    unfold Well_Formed_Component_Implementation' in H.

    intuition.

    - apply Feature_Refinements_reflexive.
      apply AADL_Component_Has_Well_Formed_Features.
      intuition.

    - apply Component_Refinements_reflexive.
      unfold Well_Formed_Component in *. intuition.

    - apply Is_Refined_Properties_reflexive.
Qed.

Lemma Implementation_Extension_transitive:
    transitive _ Implementation_Extension.
Proof.
    unfold transitive.
    unfold Implementation_Extension.
    intuition.
    - rewrite H4 in H3. intuition.
    - eapply Feature_Refinements_transitive. apply H5. apply H6.
    - eapply Component_Refinements_transitive. apply H7. apply H8.
    - eapply Is_Refined_Properties_transitive. apply H10. apply H11.
Qed.

(*| .. coq:: none |*)
End Classifier_Substitution_Rule.
(*| .. coq:: |*)

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
