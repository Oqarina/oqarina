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
Require Import Coq.Relations.Relation_Definitions.
Require Export Coq.Classes.RelationClasses.
Require Export Coq.Classes.Morphisms.
Require Import Coq.Classes.DecidableClass.
Require Import Coq.Lists.List.
Import ListNotations. (* from List *)

Require Import Coq.Bool.Bool.
Require Import Coq.Classes.SetoidClass.
Open Scope equiv_scope.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Logic.Decidable.
Set Implicit Arguments.
Set Strict Implicit.

Require Import Oqarina.formalisms.Expressions.Propositions.
Require Import Oqarina.CoqExt.all.
(*| .. coq:: |*)

(*| .. coq:: none |*)
Section Specifications.
(*| .. coq:: |*)

(*|
Specification
=============

In the following, we provide a definition of a specification theory adapted from :cite:`10.1007/978-3-642-28872-2_3`,

Informally, given a class S of specifications, a specification theory includes a composition operator :coq:`×` to combine specifications to larger ones. Additionally, a specification theory has a refinement relation :coq:`≤` to relate “concrete” and “abstract” specifications. This relation defines a preorder, i.e., it is transitive and reflexive.
To obtain a specification theory, refinement must be compositional in the sense that it must be preserved by the composition operator.

|*)

(*| For a given type :coq:`T`, we define the concept of a model. A
model is equipped with a :coq:`valid` function that asserts model
validity, it is a decidable proposition. |*)

Class Model (T : Type) := {
    valid : T -> Prop;
    valid_decidable : forall (t : T), Decision (valid t);
}.

(*| For a given type :coq:`T`, we define the concept of a refinement. A
refinement is a relation that is also a preorder, that is reflexive and transitive. |*)

Class Refinement (T : Type) := {
    refinement : relation T ;
    refinement_preorder : PreOrder refinement
}.
Notation "s1 ≼ s2" := (refinement s1 s2)
    (at level 70, no associativity).

(*| For a given type :coq:`T`, we define the notion of composition.
The :coq:`compose` operator is commutative and associative.
Composition is connected to the notion of refinment through a
compatibility relation. |*)

Class Composition (T : Type) `{Refinement T} `{Setoid T} := {
    compose: T -> T -> T;

    compose_comm :: Setoid_Commutative compose;
    compose_assoc :: Setoid_SemiGroup compose;
    compose_compatible : forall S1 S2 T1 T2,
        S1 ≼ S2 -> T1 ≼ T2 -> (compose S1 T1) ≼ (compose S2 T2);
}.

(*| From these considerations, we can now define the :coq`Specification`
typeclass, equipped with a refinement and a composition operation. |*)

Class Specification (T : Type) `{s : Setoid T} := {
    m :: Model T;
    refinement_op :: Refinement T;
    compose_op :: Composition;
}.

(*| In :cite:`10.1007/978-3-642-28872-2_3`, the authors only consider composition operator as total function. We acknowledge that this is a strong hypothesis: semantic or syntactic rules may forbid some compositions to happem, or they might be incomplete. A typical example being two AADL components being composed: composition can be done in multiple ways, e.g. variations in connections, as subcomponents of different components, etc. Instead, we define a composition operation as a partial function. Partial composition is commutative and compatible with the notion of refinement. |*)

Class Partial_Composition (T : Type)  `{Refinement T} := {
    partial_compose: list T -> T -> Prop ;

    partial_compose_comm : forall (l l': list T) S,
        partial_compose l S
            -> Permutation l l'
            -> partial_compose l' S;

    partial_compose_compatible: forall S1 S2 T1 T2 R,
        S1 ≼ S2 -> T1 ≼ T2
            -> partial_compose [S2 ;T2] R
            -> partial_compose [S1 ;T1] R;
}.

(*| From these considerations, we can now define the :coq:`Rich_Specification` typeclass, equipped with a refinement and a partial composition operation. We call this "rich" as a partial composition is a natural consequence of rich modeling languages. |*)

Class Rich_Specification (T : Type) `{s : Setoid T} := {
    r :: Model T;
    r_refinement_op :: Refinement T;
    r_compose_op :: Partial_Composition;
}.

(*| .. coq:: none |*)
End Specifications.
(*| .. coq:: |*)

(*| We encapsulate the following notations to ease model
manipulation. |*)

Module Specifications_Notations.

Notation "s1 '×' s2" := (compose s1 s2)
    (at level 70, right associativity).

Notation "s3 |=c s1 '×' s2" := (partial_compose [s1 ;s2 ] s3)
    (at level 70, right associativity).

Notation "s1 ≼ s2" := (refinement s1 s2)
    (at level 70, no associativity).

End Specifications_Notations.

(*| .. coq:: none |*)
Section Specifications_PropF.

Import Specifications_Notations.
(*| .. coq:: |*)

(*|
Specification -- PropF
======================

In this section, we provide an instantiation of the previous
classes for propositions (see :coq:`PropF`). We build incrementally the notion of model (i.e. a PropF), of a refinement, and of a composition. |*)

Variable PropVars : Set.

(* A PropF is always valid, per construction of the Coq syntax. *)
Definition Valid_PropF (P : PropF PropVars) := True.

Lemma Valid_PropF_decidable: forall t : PropF PropVars,
    Decision (Valid_PropF t).
Proof.
    intros. compute. intuition.
Qed.

Instance Models_PropF : Model (PropF PropVars) := {
    valid := Valid_PropF;
    valid_decidable := Valid_PropF_decidable;
}.

Definition PropF_equiv (p1 p2: PropF PropVars) :=
    forall v, Eval_PropF v p1 = Eval_PropF v p2.

Lemma PropF_equiv_Reflexive : Reflexive PropF_equiv.
Proof.
    unfold Reflexive, PropF_equiv.
    intuition.
Qed.

Lemma PropF_equiv_Symetric: Symmetric PropF_equiv.
Proof.
    unfold Symmetric, PropF_equiv.
    intuition.
Qed.

Lemma PropF_equiv_Transitive: Transitive PropF_equiv.
Proof.
    unfold Transitive, PropF_equiv.
    intros.
    specialize (H v).
    specialize (H0 v).
    rewrite H.
    intuition.
Qed.

Instance Setoid_PropF : Setoid (PropF PropVars) := {
    equiv := PropF_equiv;
    setoid_equiv :=
        Build_Equivalence _ PropF_equiv_Reflexive
            PropF_equiv_Symetric PropF_equiv_Transitive ;
}.

(* P1 refines P2 iff P2 => P1. *)

Definition Refinement_PropF' (P1 P2: PropF PropVars) :=
    forall v, sat_PropF v P2 -> sat_PropF v P1.

Lemma Refinement_PropF_Reflexive : forall P1,
    Refinement_PropF' P1 P1.
Proof.
    unfold Refinement_PropF'. intuition.
Qed.

Lemma Refinement_PropF_Transitive : forall P1 P2 P3,
    Refinement_PropF' P1 P2
        -> Refinement_PropF' P2 P3
        -> Refinement_PropF' P1 P3.
Proof.
    unfold Refinement_PropF'. intuition.
Qed.

Instance Refinement_PropF : Refinement (PropF PropVars) := {
    refinement := Refinement_PropF';
    refinement_preorder :=
        Build_PreOrder _ Refinement_PropF_Reflexive Refinement_PropF_Transitive;
}.

(* The composition of two PropF is their conjunction. *)

Definition compose_PropF (p1 p2: PropF PropVars) :=
    (Conj p1 p2).

Lemma compose_PropF_comm: forall (p1 p2: PropF PropVars),
    (compose_PropF p1 p2) == (compose_PropF p2 p1).
Proof.
    unfold compose_PropF. simpl.
    unfold PropF_equiv. simpl.
    intros.
    rewrite andb_comm. intuition.
Qed.

Instance compose_PropF_Setoid_Commutative :
    Setoid_Commutative compose_PropF  := {
    commute_proof := compose_PropF_comm;
}.

Lemma compose_PropF_assoc: forall (p1 p2 p3: PropF PropVars),
    compose_PropF p1 (compose_PropF p2 p3) ==
        compose_PropF (compose_PropF p1 p2) p3.
Proof.
    unfold compose_PropF. simpl.
    unfold PropF_equiv. simpl.
    intros.
    rewrite andb_assoc. intuition.
Qed.

Instance compose_PropF_Setoid_SemiGroup :
    Setoid_SemiGroup compose_PropF := {
    assoc_f := compose_PropF_assoc;
}.

Lemma compose_PropF_compatible : forall (S1 S2 T1 T2 : PropF PropVars),
    S1 ≼ S2 -> T1 ≼ T2 ->
        (compose_PropF S1 T1) ≼ (compose_PropF S2 T2).
Proof.
    unfold compose_PropF. unfold refinement. simpl.
    unfold Refinement_PropF'.
    intros.
    rewrite sat_PropF_and_rewrite in *.
    split.
    - apply H. intuition.
    - apply H0. intuition.
Qed.

Instance Composition_PropF : Composition := {
    compose := compose_PropF ;
    compose_compatible := compose_PropF_compatible ;
    compose_assoc := compose_PropF_Setoid_SemiGroup ;
    compose_comm := compose_PropF_Setoid_Commutative ;
}.

(*| Finally, we can combine all results and build a valid instance of
a specification from PropF.|*)

Instance Specification_PropF : Specification := {
    m := Models_PropF;
    refinement_op := Refinement_PropF ;
    compose_op := Composition_PropF;
}.

(*| .. coq:: none |*)
End Specifications_PropF.
