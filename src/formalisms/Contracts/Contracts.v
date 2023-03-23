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
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Set Implicit Arguments.
Set Strict Implicit.

Require Import Oqarina.formalisms.Expressions.Propositions.
Require Import Oqarina.CoqExt.all.
(*| .. coq:: |*)

(*|
===============
Contract theory
===============

In this chapter, we mechanize the meta-theory of contracts, along with in Assume/Guarantee instantiation. Definitions follow :cite:`benvenisteContractsSystemsDesign`.

In :cite:`DBLP:journals/corr/abs-2108-13647`, the authors propose a mechanization of these contracts using a set-theoretical approach. In our formalization, we opted for the Coq :coq:`Prop` type instead. Ultimately, they are equivalent in that the authors use decidable set appartenance.

|*)


(*| .. coq:: none |*)
Section Models.
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

    compose_comm :> Setoid_Commutative compose;
    compose_assoc :> Setoid_SemiGroup compose;
    compose_compatible : forall S1 S2 T1 T2,
        S1 ≼ S2 -> T1 ≼ T2 -> (compose S1 T1) ≼ (compose S2 T2);
}.

(*| From these considerations, we can now define the Specification
typeclass, equipped with a refinement and a composition operation. |*)

Class Specification (T : Type) `{s : Setoid T} := {
    m :> Model T;
    refinement_op :> Refinement T;
    compose_op :> Composition;
}.

(*| In :cite:`10.1007/978-3-642-28872-2_3`, the authors only consider total composition operator. We acknowledge that this is a strong hypothesis: semantic or syntactic rules may forbid some compositions to happem, or they might be incomplete. A typical example being two AADL components being composed: composition can be done in multiple ways, e.g. variations in connections, as subcomponents of different components, etc. Instead, we define a partial composition operation that is commutative. Partial composition is also compatible with the notion of refinement. |*)

(*
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
*)
(*| .. coq:: none |*)
End Models.
(*| .. coq:: |*)

(*| We encapsulate the following notations to ease model
manipulation. |*)

Module Models_Notations.

Notation "s1 '×' s2" := (compose s1 s2)
    (at level 70, right associativity).

    (*
Notation "s3 |= s1 '×' s2" := (partial_compose [s1 ;s2 ] s3)
    (at level 70, right associativity).
*)
Notation "s1 ≼ s2" := (refinement s1 s2)
    (at level 70, no associativity).

End Models_Notations.

(*| .. coq:: none |*)
Section Models_PropF.

Import Models_Notations.
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
End Models_PropF.

Section Contracts_Meta_Theory.

Import Models_Notations.

(*| .. coq:: |*)

(*|
Contract meta-theory
====================

|*)

(*| Let us consider a model, that implements the :coq:`Specification` typeclass, extended with a partial composition operator. |*)

Variable model : Type.
Context `{spec : Specification model}.


(*| We define a contract as a pair of two functions that computes, for a model, the sets of models that implement the contract (:coq:`Mc`) and the set of models that are compatible with the contract (:coq:`Ec`) as per :cite:`benvenisteContractsSystemsDesign`, section 3.2.

Rationale: the original paper provides little fundations for the definition of contracts. In the following, we define a contract by a function :coq:`Model -> Prop`. A model validates C iff :coq:`Mc C` and :coq:`Ec C` are True.

*Note: we impose the contracts to be decidable. This is a strong hypothesis, but necessary to compose models as one needs a contract to be either true or false. Requesting decidability makes it possible to reason and compute on contracts easily.*

|*)

Record Contract := {
    Ec : model -> Prop;
    Mc : model -> Prop;
}.

Hypothesis Decidable_Contract_c:
    forall (m: model) (c: Contract), decidable (c.(Mc) m).

Hypothesis Decidable_Contract_e:
    forall (m: model) (c: Contract), decidable (c.(Ec) m).

(* A :coq:`Contract` is always valid, per construction of the Coq
syntax. *)
Definition Valid_Contract (P : Contract) := True.

Lemma Valid_Contract_decidable: forall t : Contract,
    Decision (Valid_Contract t).
Proof.
    intros. compute. intuition.
Qed.

#[global] Instance Model_Contract : Model (Contract) := {
    valid := Valid_Contract;
    valid_decidable := Valid_Contract_decidable;
}.

(*| A contract having no implementation is called inconsistent. A contract having no environment is called incompatible. |*)

Definition Inconsistent_Contract (C : Contract) :=
    forall m: model, ~ C.(Mc) m.

Definition Incompatible_Contract (C : Contract) :=
    forall m: model, C.(Ec) m = False.

(*| We define notations for a model that implements a contract, and an environment that is compatible with a contract. |*)

Definition Implements_Contract m c := c.(Mc) m.

Notation "m ⊢m c" := (Implements_Contract m c)
    (at level 70, no associativity).

Definition Is_Compatible_Contract e c := c.(Ec) e.

Definition Compatible_Contract c :=
    exists e, Is_Compatible_Contract e c.

Notation "e ⊢e c" := (Is_Compatible_Contract e c)
    (at level 70, no associativity).

(*|

Contract refinement
-------------------

A contract refines another if it follows Liskow-like principles on :coq:`Mc` and :coq:`Ec`. |*)

Definition refines c' c :=
    forall m, (m ⊢m c' -> m ⊢m c) /\ (m ⊢e c -> m ⊢e c' ).

(*| :coq:`refines` is a pre-order, it implements the :coq:`Refinement` typeclass. |*)

Theorem refines_refl : reflexive Contract refines.
Proof. firstorder. Qed.

Theorem refines_trans : transitive Contract refines.
Proof.
    unfold refines.
    intros c1 c2 c3 H0 H1 m.
    specialize (H0 m) ; destruct H0.
    specialize (H1 m) ; destruct H1.
    split ; auto.
Qed.

#[global] Instance refines_PreOrder : PreOrder (refines) := {|
    PreOrder_Reflexive := refines_refl ;
    PreOrder_Transitive := refines_trans;
|}.

#[global] Instance Refinement_Contract : Refinement (Contract):= {|
    refinement := refines ;
    refinement_preorder := refines_PreOrder ;
|}.

(*| Additional results. |*)

Lemma refines_implements: forall c' c m,
    c' ≼ c -> m ⊢m c' -> m ⊢m c.
Proof.
    simpl.
    unfold refines.
    intros.
    specialize (H m0).
    intuition.
Qed.

Lemma refines_compatible: forall c' c m,
    c' ≼ c -> m ⊢e c -> m ⊢e c'.
Proof.
    simpl.
    unfold refines.
    intros.
    specialize (H m0).
    intuition.
Qed.

(*|

Contract equivalence
--------------------

Two contracts are equivalent iff. they refine each other. :coq:`equiv`
is an equivalence relation. |*)

Definition contract_equiv : relation Contract
 := fun (c1 c2 : Contract) => (c1 ≼ c2) /\ (c2 ≼ c1).

Lemma contract_equiv_refl: reflexive _ contract_equiv.
Proof. firstorder. Qed.

Theorem contract_equiv_trans: transitive _ contract_equiv.
Proof. firstorder. Qed.

Theorem contract_equiv_sym: symmetric _ contract_equiv.
Proof. firstorder. Qed.

#[global] Instance Equivalence_contract_equiv
    : Equivalence (contract_equiv) := {|
    Equivalence_Reflexive := contract_equiv_refl ;
    Equivalence_Symmetric := contract_equiv_sym ;
    Equivalence_Transitive := contract_equiv_trans;
|}.

#[global] Instance Setoid_contract_equiv : Setoid (Contract) := {|
    equiv := contract_equiv;
    setoid_equiv := Equivalence_contract_equiv;
|}.

(*| A contract refinement can be extended to a partial order thanks
to the equivalence relation on contracts.|*)

#[global] Instance PartialOrder_refines:
    PartialOrder equiv refines.
Proof.
    split.
    - (* Equivalence implies inclusion *)
        firstorder.
    - (* Inclusion implies equivalence *)
        firstorder.
Defined.

Theorem refines_antisym : forall c1 c2,
    c1 ≼ c2 -> c2 ≼ c1 -> (c1 == c2).
Proof.
    simpl.
    unfold contract_equiv ; auto.
Qed.

(*|

Contract composition
--------------------

|*)

Definition contract_compose c1 c2 := {|
    Mc := fun m : model => m ⊢m c1 /\ m ⊢m c2  \/
                            (~ m ⊢e c1 \/ ~ m ⊢e c2);
    Ec := fun m : model => m ⊢e c1 /\ m ⊢e c2;
|}.

Lemma contract_compose_assoc: forall c1 c2 c3,
    (contract_compose c1 (contract_compose c2 c3)) ==
    (contract_compose (contract_compose c1 c2) c3).
Proof.
    simpl.
    intros.
    unfold contract_compose, equiv, refines.
    simpl ; firstorder.
Qed.

Lemma contract_compose_comm : forall c1 c2,
    (contract_compose c1 c2) == (contract_compose c2 c1).
Proof.
    simpl.
    intros.
    unfold contract_compose, equiv, refines.
    simpl ; firstorder.
Qed.

#[global] Instance compose_contract_Setoid_Commutative :
    Setoid_Commutative contract_compose  := {
    commute_proof := contract_compose_comm;
}.

#[global] Instance compose_contract_Setoid_SemiGroup :
    Setoid_SemiGroup contract_compose:= {
    assoc_f := contract_compose_assoc;
}.

Lemma Property_3a: forall S1 S2 T1 T2,
    S1 ≼ S2 -> T1 ≼ T2 ->
        (contract_compose S1 T1) ≼ (contract_compose S2 T2).
Proof.
    simpl.
    unfold refines.
    intros.
    specialize (H0 m0).
    specialize (H m0).

    split ;
        unfold contract_compose ; simpl ; intuition.
Qed.

#[global] Instance Composition_Contract : Composition := {
    compose := contract_compose ;
    compose_compatible := Property_3a ;
    compose_assoc := compose_contract_Setoid_SemiGroup ;
    compose_comm := compose_contract_Setoid_Commutative ;
}.

(*| A consequence of the above results is that :coq:`Contract` is a :coq:`Specification`|*)

#[global] Instance Specification_Contract : Specification := {
    m := Model_Contract;
    refinement_op := Refinement_Contract ;
    compose_op := Composition_Contract;
}.

(*|

Contract compatibility
----------------------

From table 2, "Say that (C1, C2) is a compatible pair if C1 × C2 is compatible". XXX this |*)

Definition contract_composition_well_defined
    (c1 c2: Contract)
    : Prop
:=
    forall (m1 m2 e: model),
        (m1 ⊢m c1) /\ (m2 ⊢m c2) -> (valid (m1 × m2)).

Definition contracts_compatible c1 c2 :=
    Compatible_Contract (c1 × c2).

(*|
Contract conjunction
--------------------

The authors define the Greatest Lower Bound of contract refinement (:cite:`benvenisteContractsSystemsDesign`, section 3.3). Because of our encoding, we provide a more direct definition based on conjunction and disjunction of propositions. |*)

Definition contract_conjunction c1 c2 := {|
    Mc := fun m : model => c1.(Mc) m /\ c2.(Mc) m ;
    Ec := fun m : model => c1.(Ec) m \/ c2.(Ec) m;
|}.

Notation "c1 ⊓ c2" := (contract_conjunction c1 c2)
    (at level 40, left associativity).

Lemma contract_conjunction_comm: forall c1 c2,
    c1 ⊓ c2 == c2 ⊓ c1.
Proof.
    intros.
    unfold contract_conjunction.
    firstorder.
Qed.

Theorem shared_refinement: forall c c1 c2,
    c ≼ (c1 ⊓ c2) -> c ≼ c1.
Proof.
    simpl.

    intros.
    unfold refines in *.
    unfold contract_conjunction in H.
    intros.
    specialize (H m0).
    split ; firstorder.
Qed.

(*|

Additional results
------------------

|*)

(* Lemma 1 p25 *)

Lemma Lemma_1: forall c1 c2 c1' c2',
    c1' ≼ c1 -> c2' ≼ c2
        -> (contract_composition_well_defined c1 c2)
            -> (contract_composition_well_defined c1' c2').
Proof.
    intros.
    unfold contract_composition_well_defined in *.
    intros.

    specialize (H1 m1 m2 e).

    intuition.

    assert (m1 ⊢m c1).
    apply refines_implements with (c':=c1'). auto. auto.

    assert (m2 ⊢m c2).
    apply refines_implements with (c':=c2'). auto. auto.

    intuition.
Qed.

Lemma Property_3b: forall c1 c2 c1' c2',
    c1' ≼ c1 -> c2' ≼ c2
        -> contracts_compatible c1 c2
        -> contracts_compatible c1' c2'.
Proof.
    unfold contracts_compatible.
    unfold Compatible_Contract.
    intros.
    destruct H1.
    assert ((c1' × c2') ≼ (c1 × c2)).
    apply Property_3a ; auto.

    assert ((x ⊢e (c1' × c2'))).
    apply refines_compatible with (c:=c1 × c2) ; auto.
    exists x ; auto.
Qed.

Lemma Property_4: forall c1 c2 c3 c4,
    ((c1 × c2) × (c3 × c4)) == ((c1 × c3) × (c2 × c4)).
Proof.
    (* We admit this proof, firstorder is too slow to discharge it.
    It is assumed it could be proved by using the lemmas below. *)
Admitted.

(*| Corrollary 2 states that compose is associate and commutative. |*)

(*| .. coq:: none |*)
End Contracts_Meta_Theory.

Module Contract_Notations.

    Notation "m ⊢m c" := (Implements_Contract m c)
        (at level 70, no associativity).

    Notation "e ⊢e c" := (Is_Compatible_Contract e c)
        (at level 70, no associativity).

End Contract_Notations.

Section Assume_Guarantee_Contracts.
(*| .. coq:: |*)

(*|

A/G Contracts
=============

In this section, we define the notion of Assume/Guarantee contracts (or A/G contract). A :coq:`AG_Contract` refines the notion of contract from the meta-theory to components.

Without loss of generality, we define a component as a set of variables (:coq:`V`) that validates a specific assertion, i.e. a function whose signature is :coq:`list V -> Prop`. For instance, the set of static configuration parameters of a component, or a trace generated by some behavioral description.

For an A/G contract, an assumption (A) states assumptions made on the environment by a model and a guarantee (G) states guarantees offered by a model. They are both assertions on the same set of variables.

A/G contracts trivially meet all the meta-theory lemmas proved above.
We only prove a subset of them. Proofs follow the same schema: we map
an A/G contract to a general contract and conclude.

|*)

Import Contract_Notations.

Variable V : Type.
Context `{spec : Specification V}.

Definition Assertion: Type := V -> Prop.
Definition Component := Assertion.
Definition Environment := Assertion.

Record AG_Contract := {
    A: Assertion ;
    G: Assertion ;
}.

Definition AG_Contract_to_Contract (AG : AG_Contract) := {|
    Ec := AG.(A) ;
    Mc := AG.(G) ;
|}.

Notation "@ c" := (AG_Contract_to_Contract c)
    (at level 70 , no associativity).

(*| A saturated contract is an A/G contract defines by the following rule predicate. It is an idemptotent function. |*)

Definition Saturate (AG : AG_Contract) := {|
    A := AG.(A);
    G := fun x => (AG.(A) x -> AG.(G) x);
|}.

Print Instances Setoid.

Lemma Saturate_idempotent: forall ag,
    (@Saturate ag) == (@ Saturate (Saturate ag)).
Proof.
    intros.
    unfold AG_Contract_to_Contract.
    simpl.

    assert (
        (fun x => A ag x -> G ag x) =
        (fun x => A ag x -> A ag x -> G ag x)
    ).
    apply functional_extensionality. intros.
    apply propositional_extensionality.
    firstorder.

    rewrite H. reflexivity.
Qed.

(*| A saturated contract is equivalent to the original contract if
the environment is compatible with the contract.

Note: :cite:`benvenisteContractsSystemsDesign`, p36 introduces this lemma without proof. It misses the hypothesis on the environment. |*)

Lemma Saturate_equiv: forall ag,
    (forall v, v ⊢e (@ ag)) ->
        (@ Saturate ag) == (@ ag).
Proof.
    intros. unfold Saturate.
    unfold AG_Contract_to_Contract.
    simpl. firstorder.
Qed.

(*| The notion of contract refinement and composition is directly inherited from the meta-theory.

We demonstrate that a saturated contract preserves some initial properties, e.g. equivalence, compatibility, etc. |*)

Theorem contract_extensionality : forall (c1 c2 : AG_Contract),
    (@c1) == (@c2) -> Saturate c1 = Saturate c2.
Proof.
    simpl.
    intros. firstorder.
    unfold refines in *.
    simpl in *.
    unfold Saturate.

    assert (
        (fun x : V => A c1 x -> G c1 x) =
        (fun x : V => A c2 x -> G c2 x)
    ).
    apply functional_extensionality. intros.
    specialize (H x).
    specialize (H0 x).
    apply propositional_extensionality. firstorder.

    assert (forall m, A c1 m = A c2 m).
    intros.
    specialize (H m0).
    specialize (H0 m0).
    apply propositional_extensionality. firstorder.

    assert (A c1 = A c2).
    apply functional_extensionality. apply H2.

    rewrite H1. rewrite H3. reflexivity.
Qed.

Lemma implements_implements_saturate: forall c v,
    v ⊢m (@c) -> v ⊢m (@(Saturate c)).
Proof.
    simpl. firstorder.
Qed.

Lemma implements_saturate_implements: forall c v,
    (forall v, v ⊢e (@ c)) ->
        v ⊢m (@(Saturate c)) -> v ⊢m (@c).
Proof.
    simpl. firstorder.
Qed.

(*| .. coq:: none |*)
End Assume_Guarantee_Contracts.
(*| .. coq:: |*)
